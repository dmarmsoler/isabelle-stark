(*  Title:      Stark/Soundness_FRI_Trace_Residuals.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Residuals
  imports
    Soundness_FRI_Value_Aligned_Events
    Soundness_FRI_Final_Step_Replay
    Soundness_FRI_Recorded_Chunk_Replay
begin

text \<open>
  Narrow residual refinements for the header-tied trace FRI route.  These
  predicates name the remaining replay gaps for non-base FRI branches without
  changing the protocol or exporting broad selected-step replay lemmas.
\<close>

context soundness
begin

definition trace_fri_reachable_header_tie_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_reachable_header_tie_gap s out \<longleftrightarrow>
    trace_fri_bad_with_reachable_partial_candidate s out \<and>
    \<not> trace_fri_bad_with_header_tied_partial_candidate s out"

definition trace_fri_header_tied_candidate_transfer_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_candidate_transfer_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table.
      trace_fri_bad_with_reachable_partial_candidate s out \<and>
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

definition trace_fri_header_tied_candidate_available_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_candidate_available_gap s out \<longleftrightarrow>
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
      partial_trace_table_candidate trace_table trace_openings)"

lemma trace_fri_zero_round_final_obstruction_imp_header_tied_or_gap:
  assumes "trace_fri_zero_round_final_obstruction s out"
  shows
    "trace_fri_bad_with_header_tied_partial_candidate s out \<or>
     trace_fri_reachable_header_tie_gap s out"
proof -
  have reachable:
    "trace_fri_bad_with_reachable_partial_candidate s out"
  proof -
    from assms obtain trace_roots trace_bs trace_final dg
        composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers fr candidate_query_idxs
        trace_openings trace_table
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
      unfolding trace_fri_zero_round_final_obstruction_def by blast
    have partial:
      "trace_fri_partial_candidate_evidence s out fr candidate_query_idxs
        trace_openings trace_table"
      using trace_fri_partial_candidate_opening_evidenceD(2)[OF evidence] .
    show ?thesis
      unfolding trace_fri_bad_with_reachable_partial_candidate_def
      by (intro exI conjI)
        (rule trace_fri_partial_candidate_evidenceD(1)[OF partial],
         rule trace_fri_partial_candidate_evidenceD(2)[OF partial],
         rule trace_fri_partial_candidate_evidenceD(3)[OF partial])
  qed
  show ?thesis
  proof (cases "trace_fri_bad_with_header_tied_partial_candidate s out")
    case True
    then show ?thesis by simp
  next
    case False
    then have "trace_fri_reachable_header_tie_gap s out"
      unfolding trace_fri_reachable_header_tie_gap_def
      using reachable by simp
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_zero_round_final_obstruction_bound_from_header_tied_and_gap:
  fixes H G :: prob
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> H"
    and gap_bound:
    "wp_event verify_monad
      (trace_fri_reachable_header_tie_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction s) s \<le> H + G"
proof -
  have "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction s) s \<le>
    wp_event verify_monad
      (\<lambda>out.
        trace_fri_bad_with_header_tied_partial_candidate s out \<or>
        trace_fri_reachable_header_tie_gap s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_zero_round_final_obstruction_imp_header_tied_or_gap)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s +
      wp_event verify_monad (trace_fri_reachable_header_tie_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> H + G"
    by (rule add_mono[OF header_bound gap_bound])
  finally show ?thesis .
qed

definition trace_fri_header_tied_reduction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "trace_fri_header_tied_reduction s \<longleftrightarrow>
    wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
      trace_fri_error"

lemma trace_fri_header_tied_reductionD:
  assumes "trace_fri_header_tied_reduction s"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
      trace_fri_error"
  using assms unfolding trace_fri_header_tied_reduction_def by simp

lemma trace_fri_header_tied_reduction_staged_bound:
  assumes reductions:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_header_tied_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> trace_fri_error"
  by (rule trace_fri_bad_with_header_tied_partial_candidates_staged_bound)
    (rule trace_fri_header_tied_reductionD[OF reductions])

lemma trace_fri_header_tied_reduction_from_reachable_reduction:
  assumes "trace_fri_reachable_partial_candidate_reduction_assumption s"
  shows "trace_fri_header_tied_reduction s"
proof -
  have reachable:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le>
      trace_fri_error"
    using assms
    unfolding trace_fri_reachable_partial_candidate_reduction_assumption_def
    by simp
  have verifier_tied:
    "wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_partial_candidate s) s \<le>
      trace_fri_error"
    by (rule order_trans[OF _ reachable])
      (rule wp_event_mono,
        rule trace_fri_bad_with_verifier_tied_imp_reachable_partial_candidate)
  show ?thesis
    unfolding trace_fri_header_tied_reduction_def
    by (rule order_trans[OF _ verifier_tied])
      (rule wp_event_mono,
        rule trace_fri_bad_with_header_tied_imp_verifier_tied)
qed

lemma trace_fri_header_candidate_non_low_contradicts_header_tie_gap:
  assumes gap: "trace_fri_reachable_header_tie_gap s out"
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
    and not_low: "\<not> trace_table_low_degree trace_table"
  shows False
proof -
  have "trace_fri_bad_with_header_tied_partial_candidate s out"
    unfolding trace_fri_bad_with_header_tied_partial_candidate_def
    by (intro exI conjI)
      (rule fri_openings, rule header, rule partial, rule candidate,
        rule not_low)
  then show False
    using gap unfolding trace_fri_reachable_header_tie_gap_def by simp
qed

lemma trace_fri_header_candidate_low_imp_transfer_gap:
  assumes gap: "trace_fri_reachable_header_tie_gap s out"
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
  shows "trace_fri_header_tied_candidate_transfer_gap s out"
proof -
  have raw: "trace_fri_bad_with_reachable_partial_candidate s out"
    using gap unfolding trace_fri_reachable_header_tie_gap_def by simp
  show ?thesis
    unfolding trace_fri_header_tied_candidate_transfer_gap_def
    by (intro exI conjI)
      (rule raw, rule fri_openings, rule header, rule partial,
        rule candidate, rule low)
qed

lemma trace_fri_header_tied_candidate_available_gap_imp_transfer_gap:
  assumes "trace_fri_header_tied_candidate_available_gap s out"
  shows "trace_fri_header_tied_candidate_transfer_gap s out"
proof -
  obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
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
    using assms
    unfolding trace_fri_header_tied_candidate_available_gap_def by blast
  show ?thesis
  proof (cases "trace_table_low_degree trace_table")
    case True
    show ?thesis
      by (rule trace_fri_header_candidate_low_imp_transfer_gap
          [OF gap fri_openings header partial candidate True])
  next
    case False
    have False
      by (rule trace_fri_header_candidate_non_low_contradicts_header_tie_gap
          [OF gap fri_openings header partial candidate False])
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_header_tied_candidate_available_gap_bound_from_transfer_gap:
  assumes transfer_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_candidate_transfer_gap s) s \<le> T"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_candidate_available_gap s) s \<le> T"
  by (rule order_trans[OF _ transfer_bound])
    (rule wp_event_mono,
      rule trace_fri_header_tied_candidate_available_gap_imp_transfer_gap)

lemma trace_fri_reachable_imp_header_tied_or_gap:
  assumes "trace_fri_bad_with_reachable_partial_candidate s out"
  shows
    "trace_fri_bad_with_header_tied_partial_candidate s out \<or>
     trace_fri_reachable_header_tie_gap s out"
  using assms
  unfolding trace_fri_reachable_header_tie_gap_def
  by blast

lemma wp_trace_fri_reachable_bound_from_header_tied_and_gap:
  fixes H G :: prob
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> H"
    and gap_bound:
      "wp_event verify_monad
        (trace_fri_reachable_header_tie_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le> H + G"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_bad_with_header_tied_partial_candidate s out \<or>
          trace_fri_reachable_header_tie_gap s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_reachable_imp_header_tied_or_gap)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s +
      wp_event verify_monad
        (trace_fri_reachable_header_tie_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> H + G"
    by (rule add_mono[OF header_bound gap_bound])
  finally show ?thesis .
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_header_tied_and_gap:
  fixes H G :: prob
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> H"
    and gap_bound:
      "wp_event verify_monad
        (trace_fri_reachable_header_tie_gap s) s \<le> G"
    and total_bound: "H + G \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have old_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le> H + G"
    by (rule wp_trace_fri_reachable_bound_from_header_tied_and_gap
        [OF header_bound gap_bound])
  show ?thesis
    unfolding trace_fri_reachable_partial_candidate_reduction_assumption_def
    by (rule order_trans[OF old_bound total_bound])
qed

definition trace_fri_header_tied_recorded_base_chunk_auth_missing
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_recorded_base_chunk_auth_missing s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        round_idx xp xp_path xn xn_path result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      round_idx < length fri_query_idxs \<and>
      0 < length trace_bs \<and>
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
      \<not> fri_opening_matches_table
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        trace_table xp xn \<and>
      \<not> fri_layer_chunk_authenticated (trace_roots ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        (trace_round_layers ! round_idx ! 0) final_state)"

lemma trace_fri_header_tied_recorded_base_chunk_auth_missing_false:
  assumes
    "trace_fri_header_tied_recorded_base_chunk_auth_missing s out"
  shows False
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      round_idx xp xp_path xn xn_path result final_state
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and round_bound: "round_idx < length fri_query_idxs"
    and trace_bs_nonempty: "0 < length trace_bs"
    and missing:
      "\<not> fri_layer_chunk_authenticated (trace_roots ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        (trace_round_layers ! round_idx ! 0) final_state"
    unfolding
      trace_fri_header_tied_recorded_base_chunk_auth_missing_def
    by blast
  have len_trace_bs:
    "length trace_bs = length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings] .
  have trace_nonempty: "0 < length trace_roots"
    using trace_bs_nonempty len_trace_bs by simp
  have len_query: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes(7)[OF fri_openings] .
  have round_bound_rounds: "round_idx < rounds"
    using round_bound len_query by simp
  have auth:
    "fri_layer_chunk_authenticated (trace_roots ! 0) (clength * scale)
      (fri_query_idxs ! round_idx)
      (trace_round_layers ! round_idx ! 0) final_state"
    by (rule
        accepted_fri_opening_transcript_trace_base_recorded_chunk_authenticated_at
          [OF fri_openings out_eq round_bound_rounds trace_nonempty])
  have len0:
    "fri_evidence_layer_len trace_roots 0 = clength * scale"
    using trace_nonempty
    unfolding fri_evidence_layer_len_def
    by (cases trace_roots) simp_all
  have idx0:
    "fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 =
      fri_query_idxs ! round_idx"
    using trace_nonempty
    unfolding fri_evidence_layer_idx_def
    by (cases trace_roots) simp_all
  show False
    using missing auth unfolding len0 idx0 by contradiction
qed

lemma wp_trace_fri_header_tied_recorded_base_chunk_auth_missing_zero:
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_recorded_base_chunk_auth_missing s) s \<le> 0"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_recorded_base_chunk_auth_missing s) s
    \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_recorded_base_chunk_auth_missing_false)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis .
qed

definition trace_fri_header_tied_next_value_replay_checked_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_next_value_replay_checked_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table
        round_idx round_idx' layer_idx v v'.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      fr = hd trace_roots \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      round_idx < length fri_query_idxs \<and>
      round_idx' < length fri_query_idxs \<and>
      layer_idx < length trace_bs \<and>
      fri_evidence_next_idx trace_roots fri_query_idxs round_idx layer_idx =
      fri_evidence_next_idx trace_roots fri_query_idxs round_idx'
        layer_idx \<and>
      generic_fri_round_forced_next_value trace_roots trace_bs
        fri_query_idxs trace_round_layers round_idx layer_idx v \<and>
      generic_fri_round_forced_next_value trace_roots trace_bs
        fri_query_idxs trace_round_layers round_idx' layer_idx v' \<and>
      v \<noteq> v' \<and>
      v = v')"

definition trace_fri_header_tied_next_value_replay_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_next_value_replay_gap s out \<longleftrightarrow>
    trace_fri_header_tied_sampled_next_value_conflict s out \<and>
    \<not> trace_fri_header_tied_next_value_replay_checked_conflict s out"

lemma trace_fri_header_tied_next_value_replay_checked_conflict_false:
  "\<not> trace_fri_header_tied_next_value_replay_checked_conflict s out"
  unfolding trace_fri_header_tied_next_value_replay_checked_conflict_def
  by blast

lemma trace_fri_header_tied_sampled_next_value_imp_replay_gap:
  assumes "trace_fri_header_tied_sampled_next_value_conflict s out"
  shows "trace_fri_header_tied_next_value_replay_gap s out"
  using assms trace_fri_header_tied_next_value_replay_checked_conflict_false
  unfolding trace_fri_header_tied_next_value_replay_gap_def
  by simp

lemma wp_trace_fri_header_tied_sampled_next_value_bound_from_replay_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_next_value_conflict s) s \<le> G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sampled_next_value_conflict s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_sampled_next_value_imp_replay_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

definition trace_fri_header_tied_successor_replay_checked_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_successor_replay_checked_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table
        source_round target_round layer_idx v xp xp_path xn xn_path.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      fr = hd trace_roots \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      source_round < length fri_query_idxs \<and>
      target_round < length fri_query_idxs \<and>
      Suc layer_idx < length trace_bs \<and>
      generic_fri_round_forced_next_value trace_roots trace_bs
        fri_query_idxs trace_round_layers source_round layer_idx v \<and>
      fri_layer_step_evidence
        (trace_roots ! Suc layer_idx)
        (trace_bs ! Suc layer_idx)
        (fri_evidence_layer_len trace_roots (Suc layer_idx))
        (fri_evidence_layer_idx trace_roots fri_query_idxs target_round
          (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len trace_roots (Suc layer_idx))
          (fri_evidence_layer_idx trace_roots fri_query_idxs
            target_round (Suc layer_idx)))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs target_round
          (Suc layer_idx))
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          target_round (Suc layer_idx) xp xn)
        (trace_round_layers ! target_round ! Suc layer_idx) \<and>
      ((fri_evidence_next_idx trace_roots fri_query_idxs source_round
          layer_idx =
        fri_evidence_layer_idx trace_roots fri_query_idxs target_round
          (Suc layer_idx) \<and>
        v \<noteq> xp \<and> v = xp) \<or>
       (fri_evidence_next_idx trace_roots fri_query_idxs source_round
          layer_idx =
        fri_sibling_index
          (fri_evidence_layer_len trace_roots (Suc layer_idx))
          (fri_evidence_layer_idx trace_roots fri_query_idxs target_round
            (Suc layer_idx)) \<and>
        v \<noteq> xn \<and> v = xn)))"

definition trace_fri_header_tied_successor_replay_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_successor_replay_gap s out \<longleftrightarrow>
    trace_fri_header_tied_sampled_successor_opening_conflict s out \<and>
    \<not> trace_fri_header_tied_successor_replay_checked_conflict s out"

lemma trace_fri_header_tied_successor_replay_checked_conflict_false:
  "\<not> trace_fri_header_tied_successor_replay_checked_conflict s out"
  unfolding trace_fri_header_tied_successor_replay_checked_conflict_def
  by blast

lemma trace_fri_header_tied_sampled_successor_imp_replay_gap:
  assumes "trace_fri_header_tied_sampled_successor_opening_conflict s out"
  shows "trace_fri_header_tied_successor_replay_gap s out"
  using assms trace_fri_header_tied_successor_replay_checked_conflict_false
  unfolding trace_fri_header_tied_successor_replay_gap_def
  by simp

lemma wp_trace_fri_header_tied_sampled_successor_bound_from_replay_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_successor_opening_conflict s) s \<le> G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sampled_successor_opening_conflict s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_sampled_successor_imp_replay_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

definition trace_fri_header_tied_final_value_replay_checked_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_final_value_replay_checked_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table round_idx v.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      fr = hd trace_roots \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      0 < length trace_bs \<and>
      round_idx < length fri_query_idxs \<and>
      generic_fri_round_forced_next_value trace_roots trace_bs
        fri_query_idxs trace_round_layers round_idx (length trace_bs - 1)
        v \<and>
      v \<noteq> trace_final \<and>
      v = trace_final)"

definition trace_fri_header_tied_final_value_replay_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_final_value_replay_gap s out \<longleftrightarrow>
    trace_fri_header_tied_sampled_final_value_conflict s out \<and>
    \<not> trace_fri_header_tied_final_value_replay_checked_conflict s out"

lemma trace_fri_header_tied_sampled_final_value_conflictE:
  assumes "trace_fri_header_tied_sampled_final_value_conflict s out"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      round_idx v
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "verifier_header_transcript s fr trace_roots trace_final as fri_dg
      composition_roots composition_final rest"
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "\<not> trace_table_low_degree trace_table"
    "0 < length trace_bs"
    "round_idx < length fri_query_idxs"
    "generic_fri_round_forced_next_value trace_roots trace_bs
      fri_query_idxs trace_round_layers round_idx (length trace_bs - 1) v"
    "v \<noteq> trace_final"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table where
    fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and nonlow: "\<not> trace_table_low_degree trace_table"
    and final_conflict:
      "generic_fri_sampled_final_value_conflict trace_roots trace_bs
        trace_final fri_query_idxs trace_round_layers"
    unfolding trace_fri_header_tied_sampled_final_value_conflict_def
    by blast
  from generic_fri_sampled_final_value_conflictE[OF final_conflict]
  obtain round_idx v where
    nonempty: "0 < length trace_bs"
    and round_bound: "round_idx < length fri_query_idxs"
    and forced:
      "generic_fri_round_forced_next_value trace_roots trace_bs
        fri_query_idxs trace_round_layers round_idx (length trace_bs - 1) v"
    and neq: "v \<noteq> trace_final"
    by blast
  show ?thesis
    by (rule that[OF fri_openings header partial candidate nonlow nonempty
          round_bound forced neq])
qed

lemma trace_fri_header_tied_final_value_replay_checked_conflict_false:
  "\<not> trace_fri_header_tied_final_value_replay_checked_conflict s out"
  unfolding trace_fri_header_tied_final_value_replay_checked_conflict_def
  by blast

lemma trace_fri_header_tied_sampled_final_value_imp_replay_gap:
  assumes "trace_fri_header_tied_sampled_final_value_conflict s out"
  shows "trace_fri_header_tied_final_value_replay_gap s out"
  using assms trace_fri_header_tied_final_value_replay_checked_conflict_false
  unfolding trace_fri_header_tied_final_value_replay_gap_def
  by simp

lemma wp_trace_fri_header_tied_sampled_final_value_bound_from_replay_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_final_value_conflict s) s \<le> G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sampled_final_value_conflict s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_sampled_final_value_imp_replay_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

lemma wp_trace_fri_header_tied_without_same_bound_from_replay_gaps:
  fixes B N S F :: prob
  assumes base_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_base_opening_conflict s) s \<le> B"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> B + N + S + F"
  by (rule wp_trace_fri_header_tied_without_same_bound_from_branches)
    (rule base_bound,
     rule wp_trace_fri_header_tied_sampled_next_value_bound_from_replay_gap
       [OF next_gap_bound],
     rule wp_trace_fri_header_tied_sampled_successor_bound_from_replay_gap
       [OF successor_gap_bound],
     rule wp_trace_fri_header_tied_sampled_final_value_bound_from_replay_gap
       [OF final_gap_bound])

lemma wp_trace_fri_header_tied_without_same_bound_from_value_alignment_and_replay_gaps:
  fixes M G N S F :: prob
  assumes mismatch_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_value_aligned_sibling_mismatch s) s \<le> M"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> (M + G) + N + S + F"
  by (rule wp_trace_fri_header_tied_without_same_bound_from_replay_gaps)
    (rule
      wp_trace_fri_header_tied_sampled_base_bound_from_sibling_mismatch_and_gap
        [OF mismatch_bound alignment_gap_bound],
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_trace_fri_header_tied_without_same_bound_from_partial_merkle_structural_and_replay_gaps:
  fixes P H G N S F :: prob
  assumes partial_merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> ((P + H) + G) + N + S + F"
  by (rule
      wp_trace_fri_header_tied_without_same_bound_from_value_alignment_and_replay_gaps)
    (rule
      wp_trace_fri_header_tied_value_aligned_sibling_mismatch_bound_from_partial_merkle_and_structural_gap
        [OF partial_merkle_bound structural_gap_bound],
     rule alignment_gap_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_trace_fri_header_tied_authenticated_conflict_bound_from_partial_merkle_structural_and_replay_gaps:
  fixes P H G N S F :: prob
  assumes partial_merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> (((P + H) + G) + N + S + F) + P"
proof -
  have without_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> ((P + H) + G) + N + S + F"
    by (rule
        wp_trace_fri_header_tied_without_same_bound_from_partial_merkle_structural_and_replay_gaps)
      (rule partial_merkle_bound,
       rule structural_gap_bound,
       rule alignment_gap_bound,
       rule next_gap_bound,
       rule successor_gap_bound,
       rule final_gap_bound)
  show ?thesis
    by (rule
        wp_trace_fri_header_tied_authenticated_conflict_bound_from_without_same_and_merkle)
      (rule without_bound, rule partial_merkle_bound)
qed

definition trace_fri_header_tied_assignment_auth_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_assignment_auth_gap s out \<longleftrightarrow>
    trace_fri_header_tied_sampled_assignment_conflict s out \<and>
    \<not> trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"

definition trace_fri_header_tied_same_layer_auth_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_same_layer_auth_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_same_layer_opening_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers \<and>
      \<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state)"

definition trace_fri_header_tied_same_layer_recorded_auth_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_same_layer_recorded_auth_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_same_layer_recorded_auth_gap trace_roots trace_bs
        fri_query_idxs trace_round_layers final_state)"

definition trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_same_layer_authenticated_recorded_auth_gap
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state)"

definition trace_fri_header_tied_authenticated_slot_recorded_chunk_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_authenticated_slot_recorded_chunk_gap trace_roots
        fri_query_idxs trace_round_layers final_state)"

definition trace_fri_header_tied_final_value_authenticated_replay_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_final_value_authenticated_replay_gap s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        result final_state round_idx v.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      0 < length trace_bs \<and>
      round_idx < length fri_query_idxs \<and>
      generic_fri_round_forced_next_value trace_roots trace_bs
        fri_query_idxs trace_round_layers round_idx (length trace_bs - 1)
        v \<and>
      v \<noteq> trace_final \<and>
      \<not> partial_merkle_inconsistency_bad s out \<and>
      generic_fri_recorded_layer_chunk_authenticated trace_roots
        fri_query_idxs trace_round_layers final_state round_idx
        (length trace_bs - 1))"

lemma trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_false:
  assumes
    "trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s out"
  shows False
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      result final_state
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and gap:
      "generic_fri_authenticated_slot_recorded_chunk_gap trace_roots
        fri_query_idxs trace_round_layers final_state"
    unfolding trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_def
    by blast
  from gap obtain round_idx layer_idx auth_chunk where
    round_bound: "round_idx < length fri_query_idxs"
    and layer_bound: "layer_idx < length trace_roots"
    and missing:
      "\<not> generic_fri_recorded_layer_chunk_authenticated trace_roots
        fri_query_idxs trace_round_layers final_state round_idx layer_idx"
    unfolding generic_fri_authenticated_slot_recorded_chunk_gap_def
    by blast
  have round_bound_rounds: "round_idx < rounds"
    using round_bound accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
    by simp
  have all_layer_bounds:
    "\<And>raw k. k < length trace_roots \<Longrightarrow>
      0 < fri_layer_lengths (length trace_roots) (clength * scale) ! k \<and>
      fri_layer_indices (length trace_roots) (index (to_nat raw))
        (clength * scale) ! k <
      fri_layer_lengths (length trace_roots) (clength * scale) ! k"
    by (rule accepted_fri_opening_transcript_trace_raw_layer_bound
        [OF fri_openings])
  have recorded:
    "generic_fri_recorded_layer_chunk_authenticated trace_roots
      fri_query_idxs trace_round_layers final_state round_idx layer_idx"
    by (rule
        accepted_fri_opening_transcript_trace_recorded_layer_chunk_authenticated_at
        [OF fri_openings out_eq round_bound_rounds layer_bound
          all_layer_bounds])
  show False
    using missing recorded by simp
qed

lemma wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero:
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s
      \<le> (0::prob)"
proof -
  have
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s
      \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_false)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis by simp
qed

definition trace_fri_header_tied_final_value_selected_step_missing_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_final_value_selected_step_missing_gap s out
    \<longleftrightarrow>
    trace_fri_header_tied_final_value_authenticated_replay_gap s out \<and>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers result final_state round_idx v.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      0 < length trace_bs \<and>
      round_idx < length fri_query_idxs \<and>
      generic_fri_round_forced_next_value trace_roots trace_bs
        fri_query_idxs trace_round_layers round_idx (length trace_bs - 1)
        v \<and>
      v \<noteq> trace_final \<and>
      \<not> partial_merkle_inconsistency_bad s out \<and>
      generic_fri_recorded_layer_chunk_authenticated trace_roots
        fri_query_idxs trace_round_layers final_state round_idx
        (length trace_bs - 1) \<and>
      (\<forall>actual_chunk axp axp_path axn axn_path.
        \<not> (fri_layer_chunk_authenticated
          (trace_roots ! (length trace_bs - 1))
          (fri_evidence_layer_len trace_roots (length trace_bs - 1))
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          actual_chunk final_state \<and>
        fri_layer_step_evidence
          (trace_roots ! (length trace_bs - 1))
          (trace_bs ! (length trace_bs - 1))
          (fri_evidence_layer_len trace_roots (length trace_bs - 1))
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          (2 ^ (length trace_bs - 1))
          (fri_sibling_index
            (fri_evidence_layer_len trace_roots (length trace_bs - 1))
            (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
              (length trace_bs - 1)))
          axp axp_path axn axn_path
          (fri_evidence_next_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          trace_final actual_chunk)))"

lemma trace_fri_header_tied_final_value_selected_step_missing_gap_false:
  assumes gap:
    "trace_fri_header_tied_final_value_selected_step_missing_gap s out"
  shows False
proof -
  from gap obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers result final_state round_idx v
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and nonempty_bs: "0 < length trace_bs"
    and round_bound: "round_idx < length fri_query_idxs"
    and missing:
      "\<And>actual_chunk axp axp_path axn axn_path.
        \<not> (fri_layer_chunk_authenticated
          (trace_roots ! (length trace_bs - 1))
          (fri_evidence_layer_len trace_roots (length trace_bs - 1))
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          actual_chunk final_state \<and>
        fri_layer_step_evidence
          (trace_roots ! (length trace_bs - 1))
          (trace_bs ! (length trace_bs - 1))
          (fri_evidence_layer_len trace_roots (length trace_bs - 1))
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          (2 ^ (length trace_bs - 1))
          (fri_sibling_index
            (fri_evidence_layer_len trace_roots (length trace_bs - 1))
            (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
              (length trace_bs - 1)))
          axp axp_path axn axn_path
          (fri_evidence_next_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          trace_final actual_chunk)"
    unfolding trace_fri_header_tied_final_value_selected_step_missing_gap_def
    by blast
  have len_bs_roots: "length trace_bs = length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings] .
  have nonempty_roots: "0 < length trace_roots"
    using nonempty_bs len_bs_roots by simp
  have round_bound_rounds: "round_idx < rounds"
    using round_bound
      accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
    by simp
  have raw_layer:
    "\<And>raw.
      0 < fri_layer_lengths (length trace_roots) (clength * scale) !
        (length trace_roots - 1) \<and>
      fri_layer_indices (length trace_roots) (index (to_nat raw))
        (clength * scale) ! (length trace_roots - 1) <
      fri_layer_lengths (length trace_roots) (clength * scale) !
        (length trace_roots - 1)"
    by (rule accepted_fri_opening_transcript_trace_raw_layer_bound
        [OF fri_openings])
      (use nonempty_roots in simp)
  from accepted_fri_opening_transcript_trace_final_step_evidence_at
      [OF fri_openings out_eq round_bound_rounds nonempty_roots raw_layer]
  obtain actual_chunk axp axp_path axn axn_path where
    auth:
      "fri_layer_chunk_authenticated
        (trace_roots ! (length trace_roots - 1))
        (fri_evidence_layer_len trace_roots (length trace_roots - 1))
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
          (length trace_roots - 1))
        actual_chunk final_state"
    and step:
      "fri_layer_step_evidence
        (trace_roots ! (length trace_roots - 1))
        (trace_bs ! (length trace_roots - 1))
        (fri_evidence_layer_len trace_roots (length trace_roots - 1))
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
          (length trace_roots - 1))
        (2 ^ (length trace_roots - 1))
        (fri_sibling_index
          (fri_evidence_layer_len trace_roots (length trace_roots - 1))
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
            (length trace_roots - 1)))
        axp axp_path axn axn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx
          (length trace_roots - 1))
        trace_final actual_chunk"
    by blast
  show False
    using missing[of actual_chunk axp axp_path axn axn_path]
      auth step len_bs_roots
    by simp
qed

lemma wp_trace_fri_header_tied_final_value_selected_step_missing_gap_zero:
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_selected_step_missing_gap s) s
      \<le> (0::prob)"
proof -
  have
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_selected_step_missing_gap s) s \<le>
      wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_final_value_selected_step_missing_gap_false)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis by simp
qed

lemma trace_fri_header_tied_final_value_authenticated_replay_gap_imp_selected_step_missing:
  assumes
    "trace_fri_header_tied_final_value_authenticated_replay_gap s out"
  shows
    "trace_fri_header_tied_final_value_selected_step_missing_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      result final_state round_idx v
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and nonempty: "0 < length trace_bs"
    and round_bound: "round_idx < length fri_query_idxs"
    and forced:
      "generic_fri_round_forced_next_value trace_roots trace_bs
        fri_query_idxs trace_round_layers round_idx (length trace_bs - 1) v"
    and neq: "v \<noteq> trace_final"
    and no_merkle: "\<not> partial_merkle_inconsistency_bad s out"
    and recorded_auth:
      "generic_fri_recorded_layer_chunk_authenticated trace_roots
        fri_query_idxs trace_round_layers final_state round_idx
        (length trace_bs - 1)"
    unfolding trace_fri_header_tied_final_value_authenticated_replay_gap_def
    by blast
  have no_step:
    "\<And>actual_chunk axp axp_path axn axn_path.
      \<not> (fri_layer_chunk_authenticated
          (trace_roots ! (length trace_bs - 1))
          (fri_evidence_layer_len trace_roots (length trace_bs - 1))
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          actual_chunk final_state \<and>
        fri_layer_step_evidence
          (trace_roots ! (length trace_bs - 1))
          (trace_bs ! (length trace_bs - 1))
          (fri_evidence_layer_len trace_roots (length trace_bs - 1))
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          (2 ^ (length trace_bs - 1))
          (fri_sibling_index
            (fri_evidence_layer_len trace_roots (length trace_bs - 1))
            (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
              (length trace_bs - 1)))
          axp axp_path axn axn_path
          (fri_evidence_next_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          trace_final actual_chunk)"
  proof
    fix actual_chunk axp axp_path axn axn_path
    assume step_auth:
      "fri_layer_chunk_authenticated
          (trace_roots ! (length trace_bs - 1))
          (fri_evidence_layer_len trace_roots (length trace_bs - 1))
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          actual_chunk final_state \<and>
        fri_layer_step_evidence
          (trace_roots ! (length trace_bs - 1))
          (trace_bs ! (length trace_bs - 1))
          (fri_evidence_layer_len trace_roots (length trace_bs - 1))
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          (2 ^ (length trace_bs - 1))
          (fri_sibling_index
            (fri_evidence_layer_len trace_roots (length trace_bs - 1))
            (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
              (length trace_bs - 1)))
          axp axp_path axn axn_path
          (fri_evidence_next_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          trace_final actual_chunk"
    have False
      by (rule generic_fri_final_conflict_false_from_authenticated_step
          [OF forced recorded_auth conjunct1[OF step_auth]
            conjunct2[OF step_auth] no_merkle[unfolded out_eq] neq])
    then show False .
  qed
  have witness:
    "\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers result final_state round_idx v.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      0 < length trace_bs \<and>
      round_idx < length fri_query_idxs \<and>
      generic_fri_round_forced_next_value trace_roots trace_bs
        fri_query_idxs trace_round_layers round_idx (length trace_bs - 1)
        v \<and>
      v \<noteq> trace_final \<and>
      \<not> partial_merkle_inconsistency_bad s out \<and>
      generic_fri_recorded_layer_chunk_authenticated trace_roots
        fri_query_idxs trace_round_layers final_state round_idx
        (length trace_bs - 1) \<and>
      (\<forall>actual_chunk axp axp_path axn axn_path.
        \<not> (fri_layer_chunk_authenticated
          (trace_roots ! (length trace_bs - 1))
          (fri_evidence_layer_len trace_roots (length trace_bs - 1))
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          actual_chunk final_state \<and>
        fri_layer_step_evidence
          (trace_roots ! (length trace_bs - 1))
          (trace_bs ! (length trace_bs - 1))
          (fri_evidence_layer_len trace_roots (length trace_bs - 1))
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          (2 ^ (length trace_bs - 1))
          (fri_sibling_index
            (fri_evidence_layer_len trace_roots (length trace_bs - 1))
            (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx
              (length trace_bs - 1)))
          axp axp_path axn axn_path
          (fri_evidence_next_idx trace_roots fri_query_idxs round_idx
            (length trace_bs - 1))
          trace_final actual_chunk))"
    using out_eq fri_openings nonempty round_bound forced neq no_merkle
      recorded_auth no_step
    by blast
  show ?thesis
    unfolding trace_fri_header_tied_final_value_selected_step_missing_gap_def
    using assms witness by blast
qed

lemma wp_trace_fri_header_tied_final_value_authenticated_replay_gap_bound_from_selected_step_missing:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_selected_step_missing_gap s) s
      \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_authenticated_replay_gap s) s
      \<le> G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_final_value_authenticated_replay_gap s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_final_value_selected_step_missing_gap s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_final_value_authenticated_replay_gap_imp_selected_step_missing)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

lemma trace_fri_header_tied_final_value_replay_gap_imp_merkle_or_slot_or_authenticated:
  assumes "trace_fri_header_tied_final_value_replay_gap s out"
  shows
    "partial_merkle_inconsistency_bad s out \<or>
     trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s out \<or>
     trace_fri_header_tied_final_value_authenticated_replay_gap s out"
proof -
  from assms have sampled:
    "trace_fri_header_tied_sampled_final_value_conflict s out"
    unfolding trace_fri_header_tied_final_value_replay_gap_def by simp
  from trace_fri_header_tied_sampled_final_value_conflictE[OF sampled]
  obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      round_idx v
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
    and nonempty: "0 < length trace_bs"
    and round_bound: "round_idx < length fri_query_idxs"
    and forced:
      "generic_fri_round_forced_next_value trace_roots trace_bs
        fri_query_idxs trace_round_layers round_idx (length trace_bs - 1) v"
    and neq: "v \<noteq> trace_final"
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
    let ?j = "length trace_bs - 1"
    have len_trace_bs: "length trace_bs = length trace_roots"
      using accepted_fri_opening_transcript_shapes(2)[OF fri_openings] .
    have layer_bound: "?j < length trace_roots"
      using nonempty len_trace_bs by simp
    show ?thesis
    proof (cases "generic_fri_recorded_layer_chunk_authenticated trace_roots
        fri_query_idxs trace_round_layers final_state round_idx ?j")
      case True
      have authenticated_gap:
        "trace_fri_header_tied_final_value_authenticated_replay_gap s out"
        unfolding
          trace_fri_header_tied_final_value_authenticated_replay_gap_def
        by (intro exI conjI)
          (rule out_eq, rule fri_openings, rule header, rule partial,
            rule cand, rule not_low, rule nonempty, rule round_bound,
            rule forced, rule neq, use no_merkle True in simp_all)
      then show ?thesis by simp
    next
      case missing_recorded: False
      have round_bound_rounds: "round_idx < rounds"
        using round_bound
          accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
        by simp
      have raw_layer:
        "\<And>raw.
          0 < fri_layer_lengths (length trace_roots) (clength * scale) !
              ?j \<and>
          fri_layer_indices (length trace_roots) (index (to_nat raw))
            (clength * scale) ! ?j <
          fri_layer_lengths (length trace_roots) (clength * scale) ! ?j"
        by (rule accepted_fri_opening_transcript_trace_raw_layer_bound
            [OF fri_openings layer_bound])
      from accepted_fri_opening_transcript_trace_selected_chunk_authenticated_at
          [OF fri_openings out_eq round_bound_rounds layer_bound raw_layer]
      obtain auth_chunk where auth:
        "fri_layer_chunk_authenticated (trace_roots ! ?j)
          (fri_layer_lengths (length trace_roots) (clength * scale) ! ?j)
          (fri_layer_indices (length trace_roots) (fri_query_idxs ! round_idx)
            (clength * scale) ! ?j)
          auth_chunk final_state"
        by blast
      have step:
        "fri_round_layer_evidence trace_roots trace_bs fri_query_idxs
          round_idx ?j trace_round_layers"
        by (rule accepted_fri_opening_transcript_trace_round_layer_evidence
            [OF fri_openings round_bound_rounds layer_bound])
      have generic_step:
        "generic_fri_transcript_step_with_authenticated_chunk trace_roots
          trace_bs fri_query_idxs trace_round_layers final_state
          round_idx ?j"
        by (rule generic_fri_transcript_step_with_authenticated_chunkI
            [OF step])
          (use auth in
            \<open>simp add: fri_evidence_layer_len_def
              fri_evidence_layer_idx_def\<close>)
      have slot_gap:
        "generic_fri_authenticated_slot_recorded_chunk_gap trace_roots
          fri_query_idxs trace_round_layers final_state"
        by (rule
            generic_fri_transcript_step_auth_missing_imp_authenticated_slot_recorded_chunk_gap
            [OF generic_step missing_recorded])
      have route_slot_gap:
        "trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s out"
        unfolding trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_def
        by (intro exI conjI)
          (rule out_eq, rule fri_openings, rule header, rule partial,
            rule cand, rule not_low, rule slot_gap)
      then show ?thesis by simp
    qed
  qed
qed

lemma wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_authenticated:
  fixes M A R :: prob
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and slot_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s \<le> A"
    and replay_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_authenticated_replay_gap s) s \<le> R"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap s) s \<le> M + A + R"
proof -
  let ?P = "partial_merkle_inconsistency_bad s"
  let ?Q = "trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s"
  let ?R =
    "trace_fri_header_tied_final_value_authenticated_replay_gap s"
  have event_le:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap s) s \<le>
     wp_event verify_monad (\<lambda>out. ?P out \<or> ?Q out \<or> ?R out) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_final_value_replay_gap_imp_merkle_or_slot_or_authenticated)
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

lemma wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step:
  fixes M A R :: prob
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and slot_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s \<le> A"
    and selected_step_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_selected_step_missing_gap s) s
      \<le> R"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap s) s \<le> M + A + R"
proof -
  have authenticated_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_authenticated_replay_gap s) s
      \<le> R"
    by (rule
        wp_trace_fri_header_tied_final_value_authenticated_replay_gap_bound_from_selected_step_missing
      [OF selected_step_bound])
  show ?thesis
    by (rule
        wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_authenticated)
      (rule merkle_bound, rule slot_bound, rule authenticated_bound)
qed

definition trace_fri_header_tied_base_head_value_mismatch_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_base_head_value_mismatch_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        round_idx xp xp_path xn xn_path result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      round_idx < length fri_query_idxs \<and>
      0 < length trace_bs \<and>
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
      \<not> fri_opening_matches_table
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        trace_table xp xn \<and>
      \<not> (trace_openings ! round_idx \<noteq> [] \<and>
        opening_index (hd (trace_openings ! round_idx)) =
          fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 \<and>
        opening_value (hd (trace_openings ! round_idx)) = xp))"

lemma trace_fri_header_tied_base_value_alignment_gap_imp_head_value_mismatch_gap:
  assumes "trace_fri_header_tied_base_value_alignment_gap s out"
  shows "trace_fri_header_tied_base_head_value_mismatch_gap s out"
proof -
  from assms have sampled:
    "trace_fri_header_tied_sampled_base_opening_conflict s out"
    and no_aligned:
      "\<not> trace_fri_header_tied_value_aligned_base_opening_conflict s out"
    unfolding trace_fri_header_tied_base_value_alignment_gap_def by simp_all
  from sampled obtain trace_roots trace_bs trace_final dg composition_roots
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
    and generic:
      "generic_fri_sampled_base_opening_conflict trace_table trace_roots
        trace_bs fri_query_idxs trace_round_layers"
    unfolding trace_fri_header_tied_sampled_base_opening_conflict_def
    by blast
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  from generic obtain round_idx xp xp_path xn xn_path where
    trace_bs_nonempty: "0 < length trace_bs"
    and round_bound: "round_idx < length fri_query_idxs"
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
    and no_match:
      "\<not> fri_opening_matches_table
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        trace_table xp xn"
    unfolding generic_fri_sampled_base_opening_conflict_def
    by blast
  have no_head:
    "\<not> (trace_openings ! round_idx \<noteq> [] \<and>
      opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 \<and>
      opening_value (hd (trace_openings ! round_idx)) = xp)"
  proof
    assume head:
      "trace_openings ! round_idx \<noteq> [] \<and>
       opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 \<and>
       opening_value (hd (trace_openings ! round_idx)) = xp"
    have aligned:
      "trace_fri_header_tied_value_aligned_base_opening_conflict s out"
      unfolding trace_fri_header_tied_value_aligned_base_opening_conflict_def
      by (intro exI conjI)
        (rule out_eq, rule fri_openings, rule header, rule partial, rule cand,
          rule not_low, rule round_bound, rule trace_bs_nonempty,
          use head step no_match in simp_all)
    then show False
      using no_aligned by contradiction
  qed
  show ?thesis
    unfolding trace_fri_header_tied_base_head_value_mismatch_gap_def
    by (intro exI conjI)
      (rule out_eq, rule fri_openings, rule header, rule partial, rule cand,
        rule not_low, rule round_bound, rule trace_bs_nonempty, rule step,
        rule no_match, rule no_head)
qed

lemma wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap:
  fixes G :: prob
  assumes mismatch_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_mismatch_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_base_head_value_mismatch_gap s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_base_value_alignment_gap_imp_head_value_mismatch_gap)
  then show ?thesis
    by (rule order_trans[OF _ mismatch_bound])
qed

definition trace_fri_header_tied_base_head_value_neq_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_base_head_value_neq_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        round_idx xp xp_path xn xn_path result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      round_idx < length fri_query_idxs \<and>
      0 < length trace_bs \<and>
      trace_openings ! round_idx \<noteq> [] \<and>
      opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 \<and>
      opening_value (hd (trace_openings ! round_idx)) \<noteq> xp \<and>
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
      \<not> fri_opening_matches_table
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        trace_table xp xn)"

lemma trace_fri_header_tied_base_head_value_mismatch_gap_imp_neq_gap:
  assumes "trace_fri_header_tied_base_head_value_mismatch_gap s out"
  shows "trace_fri_header_tied_base_head_value_neq_gap s out"
proof -
  from assms show ?thesis
    unfolding trace_fri_header_tied_base_head_value_mismatch_gap_def
  proof (elim exE conjE)
    fix trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      round_idx xp xp_path xn xn_path result final_state
    assume out_eq: "out = Some (result, final_state)"
    assume fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    assume header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    assume partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    assume cand: "partial_trace_table_candidate trace_table trace_openings"
    assume not_low: "\<not> trace_table_low_degree trace_table"
    assume round_bound: "round_idx < length fri_query_idxs"
    assume trace_bs_nonempty: "0 < length trace_bs"
    assume step:
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
    assume no_match:
      "\<not> fri_opening_matches_table
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        trace_table xp xn"
    assume no_head:
      "\<not> (trace_openings ! round_idx \<noteq> [] \<and>
        opening_index (hd (trace_openings ! round_idx)) =
          fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 \<and>
        opening_value (hd (trace_openings ! round_idx)) = xp)"
    have round_bound_rounds: "round_idx < rounds"
      using round_bound
        accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
      by simp
    have roots_nonempty: "0 < length trace_roots"
      using accepted_fri_opening_transcript_shapes(2)[OF fri_openings]
        trace_bs_nonempty by simp
    have idxs:
      "map opening_index (trace_openings ! round_idx) =
        powers_scaled (fri_query_idxs ! round_idx)"
      by (rule accepted_with_partial_trace_openings_shapes(3)
          [OF partial round_bound_rounds])
    have openings_nonempty: "trace_openings ! round_idx \<noteq> []"
      using idxs powers_pos unfolding powers_scaled_def by auto
    have hd_idx:
      "opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0"
    proof -
      have "opening_index (hd (trace_openings ! round_idx)) =
          fri_query_idxs ! round_idx"
      proof -
        have "opening_index (hd (trace_openings ! round_idx)) =
            hd (map opening_index (trace_openings ! round_idx))"
          using openings_nonempty by (cases "trace_openings ! round_idx") auto
        also have "... = hd (powers_scaled (fri_query_idxs ! round_idx))"
          using idxs by simp
        also have "... = fri_query_idxs ! round_idx"
          by (rule powers_scaled_hd)
        finally show ?thesis .
      qed
      moreover have
        "fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 =
          fri_query_idxs ! round_idx"
        using roots_nonempty
        unfolding fri_evidence_layer_idx_def
        by (cases trace_roots) simp_all
      ultimately show ?thesis by simp
    qed
    have hd_neq:
      "opening_value (hd (trace_openings ! round_idx)) \<noteq> xp"
      using no_head openings_nonempty hd_idx by blast
    show "trace_fri_header_tied_base_head_value_neq_gap s out"
      unfolding trace_fri_header_tied_base_head_value_neq_gap_def
      by (intro exI conjI)
        (rule out_eq, rule fri_openings, rule header, rule partial, rule cand,
          rule not_low, rule round_bound, rule trace_bs_nonempty,
          rule openings_nonempty, rule hd_idx, rule hd_neq, rule step,
          rule no_match)
  qed
qed

lemma wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap:
  fixes G :: prob
  assumes neq_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_mismatch_gap s) s \<le> G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_mismatch_gap s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_base_head_value_neq_gap s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_base_head_value_mismatch_gap_imp_neq_gap)
  then show ?thesis
    by (rule order_trans[OF _ neq_bound])
qed

lemma trace_fri_header_tied_assignment_imp_authenticated_or_auth_gap:
  assumes "trace_fri_header_tied_sampled_assignment_conflict s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out \<or>
     trace_fri_header_tied_assignment_auth_gap s out"
  using assms
  unfolding trace_fri_header_tied_assignment_auth_gap_def
  by blast

lemma trace_fri_header_tied_assignment_auth_gap_imp_same_layer_auth_gap:
  assumes "trace_fri_header_tied_assignment_auth_gap s out"
  shows "trace_fri_header_tied_same_layer_auth_gap s out"
proof -
  from assms have conflict:
    "trace_fri_header_tied_sampled_assignment_conflict s out"
    and no_auth:
    "\<not> trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
    unfolding trace_fri_header_tied_assignment_auth_gap_def
    by simp_all
  from conflict obtain trace_roots trace_bs trace_final dg composition_roots
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
    and sampled:
      "generic_fri_sampled_assignment_conflict trace_table trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers"
    unfolding trace_fri_header_tied_sampled_assignment_conflict_def
    by blast
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  have split:
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      trace_table trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers final_state \<or>
     (generic_fri_sampled_same_layer_opening_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers \<and>
      \<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state)"
    by (rule
        generic_fri_sampled_assignment_conflict_imp_authenticated_or_same_layer_auth_gap
        [OF sampled])
  then show ?thesis
  proof
    assume auth:
      "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers final_state"
    have
      "trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
        s out"
      unfolding
        trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
      by (intro exI conjI)
        (rule fri_openings, rule out_eq, rule header, rule partial, rule cand,
          rule not_low, rule auth)
    then show ?thesis
      using no_auth by contradiction
  next
    assume gap:
      "generic_fri_sampled_same_layer_opening_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers \<and>
       \<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    show ?thesis
      unfolding trace_fri_header_tied_same_layer_auth_gap_def
      by (intro exI conjI)
        (rule out_eq, rule fri_openings, rule header, rule partial, rule cand,
          rule not_low, use gap in simp_all)
  qed
qed

lemma trace_fri_header_tied_same_layer_auth_gap_imp_recorded_auth_gap:
  assumes "trace_fri_header_tied_same_layer_auth_gap s out"
  shows "trace_fri_header_tied_same_layer_recorded_auth_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      result final_state
    where out_eq: "out = Some (result, final_state)"
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
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and same:
      "generic_fri_sampled_same_layer_opening_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers"
    and no_auth:
      "\<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    unfolding trace_fri_header_tied_same_layer_auth_gap_def
    by blast
  have recorded_gap:
    "generic_fri_sampled_same_layer_recorded_auth_gap trace_roots trace_bs
      fri_query_idxs trace_round_layers final_state"
    by (rule generic_fri_sampled_same_layer_auth_gap_imp_recorded_auth_gap
        [OF same no_auth])
  show ?thesis
    unfolding trace_fri_header_tied_same_layer_recorded_auth_gap_def
    by (intro exI conjI)
      (rule out_eq, rule fri_openings, rule header, rule partial, rule cand,
        rule not_low, rule recorded_gap)
qed

lemma trace_fri_header_tied_same_layer_recorded_auth_gap_imp_authenticated_recorded_auth_gap:
  assumes "trace_fri_header_tied_same_layer_recorded_auth_gap s out"
  shows
    "trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      result final_state
    where out_eq: "out = Some (result, final_state)"
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
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and recorded_gap:
      "generic_fri_sampled_same_layer_recorded_auth_gap trace_roots
        trace_bs fri_query_idxs trace_round_layers final_state"
    unfolding trace_fri_header_tied_same_layer_recorded_auth_gap_def
    by blast
  have len_trace_bs: "length trace_bs = length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings] .
  have len_query: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes(7)[OF fri_openings] .
  have auth_step:
    "\<And>round_idx layer_idx.
      round_idx < length fri_query_idxs \<Longrightarrow>
      layer_idx < length trace_bs \<Longrightarrow>
      generic_fri_transcript_step_with_authenticated_chunk trace_roots
        trace_bs fri_query_idxs trace_round_layers final_state round_idx
        layer_idx"
  proof -
    fix round_idx layer_idx
    assume round_bound: "round_idx < length fri_query_idxs"
      and layer_bound_bs: "layer_idx < length trace_bs"
    have round_bound_rounds: "round_idx < rounds"
      using round_bound len_query by simp
    have layer_bound_roots: "layer_idx < length trace_roots"
      using layer_bound_bs len_trace_bs by simp
    show
      "generic_fri_transcript_step_with_authenticated_chunk trace_roots
        trace_bs fri_query_idxs trace_round_layers final_state round_idx
        layer_idx"
      by (rule
          accepted_fri_opening_transcript_trace_step_with_authenticated_chunk_at_raw
          [OF fri_openings out_eq round_bound_rounds layer_bound_roots])
  qed
  have authenticated_recorded_gap:
    "generic_fri_sampled_same_layer_authenticated_recorded_auth_gap
      trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    by (rule
        generic_fri_recorded_auth_gap_imp_authenticated_recorded_auth_gap
        [OF recorded_gap auth_step])
  show ?thesis
    unfolding
      trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap_def
    by (intro exI conjI)
      (rule out_eq, rule fri_openings, rule header, rule partial, rule cand,
        rule not_low, rule authenticated_recorded_gap)
qed

lemma trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap_imp_slot_recorded_chunk_gap:
  assumes
    "trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap s out"
  shows "trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      result final_state
    where out_eq: "out = Some (result, final_state)"
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
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and gap:
      "generic_fri_sampled_same_layer_authenticated_recorded_auth_gap
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    unfolding
      trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap_def
    by blast
  have slot_gap:
    "generic_fri_authenticated_slot_recorded_chunk_gap trace_roots
      fri_query_idxs trace_round_layers final_state"
    by (rule
        generic_fri_authenticated_recorded_auth_gap_imp_slot_recorded_chunk_gap
        [OF gap])
  show ?thesis
    unfolding trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_def
    by (intro exI conjI)
      (rule out_eq, rule fri_openings, rule header, rule partial, rule cand,
        rule not_low, rule slot_gap)
qed

lemma wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_authenticated_and_auth_gap:
  fixes C G :: prob
  assumes authenticated_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> C"
    and auth_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_assignment_auth_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s \<le> C + G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
            s out \<or>
          trace_fri_header_tied_assignment_auth_gap s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_assignment_imp_authenticated_or_auth_gap)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
        s +
      wp_event verify_monad
        (trace_fri_header_tied_assignment_auth_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> C + G"
    by (intro add_mono authenticated_bound auth_gap_bound)
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_assignment_auth_gap_bound_from_same_layer_auth_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_auth_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_assignment_auth_gap s) s \<le> G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_assignment_auth_gap s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_same_layer_auth_gap s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_assignment_auth_gap_imp_same_layer_auth_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

lemma wp_trace_fri_header_tied_same_layer_auth_gap_bound_from_recorded_auth_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_recorded_auth_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_auth_gap s) s \<le> G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_same_layer_auth_gap s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_same_layer_recorded_auth_gap s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_same_layer_auth_gap_imp_recorded_auth_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

lemma wp_trace_fri_header_tied_same_layer_recorded_auth_gap_bound_from_authenticated_recorded_auth_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap s)
      s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_recorded_auth_gap s) s \<le> G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_same_layer_recorded_auth_gap s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap s)
        s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_same_layer_recorded_auth_gap_imp_authenticated_recorded_auth_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

lemma wp_trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap_bound_from_slot_recorded_chunk_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s
      \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap s)
      s \<le> G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap s)
      s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap_imp_slot_recorded_chunk_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

lemma wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_auth_gap_and_residuals:
  fixes A P H G N S F :: prob
  assumes auth_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_assignment_auth_gap s) s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s
      \<le> ((((P + H) + G) + N + S + F) + P) + A"
  by (rule
      wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_authenticated_and_auth_gap)
    (rule
      wp_trace_fri_header_tied_authenticated_conflict_bound_from_partial_merkle_structural_and_replay_gaps
        [OF partial_merkle_bound structural_gap_bound alignment_gap_bound
          next_gap_bound successor_gap_bound final_gap_bound],
     rule auth_gap_bound)

lemma wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_same_layer_auth_gap_and_residuals:
  fixes A P H G N S F :: prob
  assumes same_layer_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_auth_gap s) s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s
      \<le> ((((P + H) + G) + N + S + F) + P) + A"
  by (rule
      wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_auth_gap_and_residuals)
    (rule
      wp_trace_fri_header_tied_assignment_auth_gap_bound_from_same_layer_auth_gap
        [OF same_layer_gap_bound],
     rule partial_merkle_bound,
     rule structural_gap_bound,
     rule alignment_gap_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_recorded_auth_gap_and_residuals:
  fixes A P H G N S F :: prob
  assumes recorded_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_recorded_auth_gap s) s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s
      \<le> ((((P + H) + G) + N + S + F) + P) + A"
  by (rule
      wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_same_layer_auth_gap_and_residuals)
    (rule
      wp_trace_fri_header_tied_same_layer_auth_gap_bound_from_recorded_auth_gap
        [OF recorded_gap_bound],
     rule partial_merkle_bound,
     rule structural_gap_bound,
     rule alignment_gap_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_authenticated_recorded_auth_gap_and_residuals:
  fixes A P H G N S F :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap s)
      s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s
      \<le> ((((P + H) + G) + N + S + F) + P) + A"
  by (rule
      wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_recorded_auth_gap_and_residuals)
    (rule
      wp_trace_fri_header_tied_same_layer_recorded_auth_gap_bound_from_authenticated_recorded_auth_gap
        [OF gap_bound],
     rule partial_merkle_bound,
     rule structural_gap_bound,
     rule alignment_gap_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_slot_recorded_chunk_gap_and_residuals:
  fixes A P H G N S F :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s
      \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s
      \<le> ((((P + H) + G) + N + S + F) + P) + A"
  by (rule
      wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_authenticated_recorded_auth_gap_and_residuals)
    (rule
      wp_trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap_bound_from_slot_recorded_chunk_gap
        [OF gap_bound],
     rule partial_merkle_bound,
     rule structural_gap_bound,
     rule alignment_gap_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_trace_fri_header_tied_bound_from_sampled_zero_auth_gap_and_residuals:
  fixes R Z A P H G N S F :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and auth_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_assignment_auth_gap s) s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> R + (((((P + H) + G) + N + S + F) + P) + A + Z)"
proof -
  have conflict_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s
      \<le> ((((P + H) + G) + N + S + F) + P) + A"
    by (rule
        wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_auth_gap_and_residuals)
      (rule auth_gap_bound,
       rule partial_merkle_bound,
       rule structural_gap_bound,
       rule alignment_gap_bound,
       rule next_gap_bound,
       rule successor_gap_bound,
       rule final_gap_bound)
  have "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> R + (((((P + H) + G) + N + S + F) + P) + A + Z)"
    by (rule order_trans[
        OF wp_trace_fri_header_tied_bound_from_sampled_conflict_and_zero
          [OF sampled_bound conflict_bound zero_bound]])
      (simp add: algebra_simps)
  then show ?thesis .
qed

lemma wp_trace_fri_header_tied_bound_from_sampled_zero_same_layer_auth_gap_and_residuals:
  fixes R Z A P H G N S F :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and same_layer_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_auth_gap s) s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> R + (((((P + H) + G) + N + S + F) + P) + A + Z)"
  by (rule
      wp_trace_fri_header_tied_bound_from_sampled_zero_auth_gap_and_residuals)
    (rule sampled_bound,
     rule zero_bound,
     rule
       wp_trace_fri_header_tied_assignment_auth_gap_bound_from_same_layer_auth_gap
        [OF same_layer_gap_bound],
     rule partial_merkle_bound,
     rule structural_gap_bound,
     rule alignment_gap_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_trace_fri_header_tied_bound_from_sampled_zero_recorded_auth_gap_and_residuals:
  fixes R Z A P H G N S F :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and recorded_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_recorded_auth_gap s) s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> R + (((((P + H) + G) + N + S + F) + P) + A + Z)"
  by (rule
      wp_trace_fri_header_tied_bound_from_sampled_zero_same_layer_auth_gap_and_residuals)
    (rule sampled_bound,
     rule zero_bound,
     rule
       wp_trace_fri_header_tied_same_layer_auth_gap_bound_from_recorded_auth_gap
        [OF recorded_gap_bound],
     rule partial_merkle_bound,
     rule structural_gap_bound,
     rule alignment_gap_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_trace_fri_header_tied_bound_from_sampled_zero_authenticated_recorded_auth_gap_and_residuals:
  fixes R Z A P H G N S F :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap s)
        s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> R + (((((P + H) + G) + N + S + F) + P) + A + Z)"
  by (rule
      wp_trace_fri_header_tied_bound_from_sampled_zero_recorded_auth_gap_and_residuals)
    (rule sampled_bound,
     rule zero_bound,
     rule
       wp_trace_fri_header_tied_same_layer_recorded_auth_gap_bound_from_authenticated_recorded_auth_gap
        [OF gap_bound],
     rule partial_merkle_bound,
     rule structural_gap_bound,
     rule alignment_gap_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_trace_fri_header_tied_bound_from_sampled_zero_slot_recorded_chunk_gap_and_residuals:
  fixes R Z A P H G N S F :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s)
        s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> R + (((((P + H) + G) + N + S + F) + P) + A + Z)"
  by (rule
      wp_trace_fri_header_tied_bound_from_sampled_zero_authenticated_recorded_auth_gap_and_residuals)
    (rule sampled_bound,
     rule zero_bound,
     rule
       wp_trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap_bound_from_slot_recorded_chunk_gap
        [OF gap_bound],
     rule partial_merkle_bound,
     rule structural_gap_bound,
     rule alignment_gap_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_trace_fri_header_tied_bound_from_sampled_zero_slot_and_authenticated_final_residuals:
  fixes R Z A P H G N S F :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and slot_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s)
        s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and authenticated_final_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_authenticated_replay_gap s) s
        \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> R + (((((P + H) + G) + N + S + (P + A + F)) + P) + A + Z)"
proof -
  have final_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap s) s \<le> P + A + F"
    by (rule
        wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_authenticated)
      (rule partial_merkle_bound, rule slot_gap_bound,
        rule authenticated_final_bound)
  have old_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> R + (((((P + H) + G) + N + S + (P + A + F)) + P) + A + Z)"
    by (rule
        wp_trace_fri_header_tied_bound_from_sampled_zero_slot_recorded_chunk_gap_and_residuals)
      (rule sampled_bound,
       rule zero_bound,
       rule slot_gap_bound,
       rule partial_merkle_bound,
       rule structural_gap_bound,
       rule alignment_gap_bound,
       rule next_gap_bound,
       rule successor_gap_bound,
       rule final_gap_bound)
  then show ?thesis .
qed

lemma wp_trace_fri_header_tied_bound_from_sampled_zero_slot_and_selected_step_final_residuals:
  fixes R Z A P H G N S F :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and zero_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and slot_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> A"
    and partial_merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and selected_step_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_selected_step_missing_gap s) s
      \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> R + (((((P + H) + G) + N + S + (P + A + F)) + P) + A + Z)"
proof -
  have final_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap s) s \<le> P + A + F"
    by (rule
        wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
      (rule partial_merkle_bound, rule slot_gap_bound,
        rule selected_step_bound)
  show ?thesis
    by (rule
        wp_trace_fri_header_tied_bound_from_sampled_zero_slot_recorded_chunk_gap_and_residuals)
      (rule sampled_bound,
       rule zero_bound,
       rule slot_gap_bound,
       rule partial_merkle_bound,
       rule structural_gap_bound,
       rule alignment_gap_bound,
       rule next_gap_bound,
       rule successor_gap_bound,
       rule final_gap_bound)
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_header_tied_residual_bounds:
  fixes R Z A P H G N S F T :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and slot_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s)
        s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
    and header_gap_bound:
      "wp_event verify_monad
        (trace_fri_reachable_header_tie_gap s) s \<le> T"
    and total_bound:
      "R + (((((P + H) + G) + N + S + F) + P) + A + Z) + T
        \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> R + (((((P + H) + G) + N + S + F) + P) + A + Z)"
    by (rule
        wp_trace_fri_header_tied_bound_from_sampled_zero_slot_recorded_chunk_gap_and_residuals
        [OF sampled_bound zero_bound slot_gap_bound partial_merkle_bound
          structural_gap_bound alignment_gap_bound next_gap_bound
          successor_gap_bound final_gap_bound])
  show ?thesis
    by (rule
        trace_fri_reachable_partial_candidate_reduction_from_header_tied_and_gap
        [OF header_bound header_gap_bound total_bound])
qed

lemma trace_fri_header_tied_reduction_from_residual_bounds:
  fixes R Z A P H G N S F :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and slot_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s)
        s \<le> A"
    and partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and alignment_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
    and next_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap s) s \<le> F"
    and total_bound:
      "R + (((((P + H) + G) + N + S + F) + P) + A + Z)
        \<le> trace_fri_error"
  shows "trace_fri_header_tied_reduction s"
  unfolding trace_fri_header_tied_reduction_def
  by (rule order_trans[
      OF wp_trace_fri_header_tied_bound_from_sampled_zero_slot_recorded_chunk_gap_and_residuals
        [OF sampled_bound zero_bound slot_gap_bound partial_merkle_bound
          structural_gap_bound alignment_gap_bound next_gap_bound
          successor_gap_bound final_gap_bound] total_bound])

end

end
