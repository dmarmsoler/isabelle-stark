(*  Title:      Stark/Soundness_FRI_Trace_Empty_Sampled_Assignment_Split.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Empty_Sampled_Assignment_Split
  imports
    Soundness_Public_Route_Concrete_FRI_Sharpened
    Soundness_FRI_Canonical_Full_Cover_Failure
    Soundness_FRI_Trace_Transcript_Consistent
    Soundness_Conceptual_Query_Empty_Current
begin

text \<open>
  First split for the remaining plain trace empty-branch sampled-assignment
  conflict.  The plain event is intentionally broader than the low-degree
  sampled-query bad-candidate event: it does not require the conflicting
  candidate table to be non-low-degree.  This layer separates the aligned
  verifier-tied part from the residual that still needs a Merkle/replay
  explanation.
\<close>

context soundness
begin

lemma prob_le_refl: "(x::prob) \<le> x"
  by transfer simp

definition trace_fri_sampled_assignment_verifier_untied_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_assignment_verifier_untied_gap s out \<longleftrightarrow>
    trace_fri_sampled_assignment_conflict s out \<and>
    \<not> trace_fri_verifier_tied_sampled_assignment_conflict s out"

lemma trace_fri_sampled_assignment_conflict_imp_verifier_tied_or_untied:
  assumes "trace_fri_sampled_assignment_conflict s out"
  shows
    "trace_fri_verifier_tied_sampled_assignment_conflict s out \<or>
     trace_fri_sampled_assignment_verifier_untied_gap s out"
  using assms
  unfolding trace_fri_sampled_assignment_verifier_untied_gap_def by blast

lemma wp_trace_fri_sampled_assignment_conflict_bound_from_verifier_tied_and_untied:
  assumes verifier_tied_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict s) s \<le> V"
    and untied_bound:
    "wp_event verify_monad
      (trace_fri_sampled_assignment_verifier_untied_gap s) s \<le> U"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_assignment_conflict s) s \<le> V + U"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_assignment_conflict s) s \<le>
    wp_event verify_monad
      (\<lambda>out.
        trace_fri_verifier_tied_sampled_assignment_conflict s out \<or>
        trace_fri_sampled_assignment_verifier_untied_gap s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_assignment_conflict_imp_verifier_tied_or_untied)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_verifier_tied_sampled_assignment_conflict s) s +
      wp_event verify_monad
        (trace_fri_sampled_assignment_verifier_untied_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> V + U"
    by (rule add_mono[OF verifier_tied_bound untied_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_sampled_assignment_conflict_bound_from_verifier_tied_and_untied:
  assumes verifier_tied_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_sampled_assignment_conflict)
      adversary_initial_state \<le> V"
    and untied_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_assignment_verifier_untied_gap)
      adversary_initial_state \<le> U"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_assignment_conflict)
      adversary_initial_state \<le> V + U"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?plain =
    "staged_security_with_data_state_verifier_event
      trace_fri_sampled_assignment_conflict"
  let ?tied =
    "staged_security_with_data_state_verifier_event
      trace_fri_verifier_tied_sampled_assignment_conflict"
  let ?untied =
    "staged_security_with_data_state_verifier_event
      trace_fri_sampled_assignment_verifier_untied_gap"
  have "wp_event ?M ?plain adversary_initial_state \<le>
    wp_event ?M (\<lambda>out. ?tied out \<or> ?untied out)
      adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono)
      (auto dest:
        trace_fri_sampled_assignment_conflict_imp_verifier_tied_or_untied
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?tied adversary_initial_state +
      wp_event ?M ?untied adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> V + U"
    by (rule add_mono[OF verifier_tied_bound untied_bound])
  finally show ?thesis .
qed

definition trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_assignment_conflict_without_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers)"

definition trace_fri_verifier_tied_same_layer_auth_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_verifier_tied_same_layer_auth_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table result
        final_state.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      out = Some (result, final_state) \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_same_layer_opening_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers \<and>
      \<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state)"

lemma trace_fri_verifier_tied_conflict_imp_authenticated_or_auth_gap:
  assumes "trace_fri_verifier_tied_sampled_assignment_conflict s out"
  shows
    "trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out \<or>
     trace_fri_verifier_tied_same_layer_auth_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and conflict:
      "generic_fri_sampled_assignment_conflict trace_table trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers"
    unfolding trace_fri_verifier_tied_sampled_assignment_conflict_def
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
        [OF conflict])
  then show ?thesis
  proof
    assume auth:
      "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers final_state"
    have "trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
      unfolding
        trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
      by (intro exI conjI)
        (rule fri_openings, rule out_eq, rule partial, rule cand,
          rule not_low, rule auth)
    then show ?thesis by simp
  next
    assume gap:
      "generic_fri_sampled_same_layer_opening_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers \<and>
      \<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    have "trace_fri_verifier_tied_same_layer_auth_gap s out"
      unfolding trace_fri_verifier_tied_same_layer_auth_gap_def
      by (intro exI conjI)
        (rule fri_openings, rule out_eq, rule partial, rule cand,
          rule not_low, use gap in simp_all)
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_verifier_tied_conflict_bound_from_authenticated_and_auth_gap:
  fixes A G :: prob
  assumes auth_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> A"
    and gap_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_same_layer_auth_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict s) s \<le> A + G"
proof -
  have "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict s) s \<le>
    wp_event verify_monad
      (\<lambda>out.
        trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
          s out \<or>
        trace_fri_verifier_tied_same_layer_auth_gap s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_verifier_tied_conflict_imp_authenticated_or_auth_gap)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
        s +
      wp_event verify_monad (trace_fri_verifier_tied_same_layer_auth_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> A + G"
    by (rule add_mono[OF auth_bound gap_bound])
  finally show ?thesis .
qed

lemma trace_fri_verifier_tied_authenticated_conflict_imp_without_same_or_same_layer:
  assumes
    "trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
  shows
    "trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out \<or>
     trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
      s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table result
      final_state
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and conflict:
      "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers final_state"
    unfolding
      trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
    by blast
  have split:
    "generic_fri_sampled_assignment_conflict_without_same_layer
      trace_table trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers \<or>
     generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    by (rule
        generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_split
        [OF conflict])
  then show ?thesis
  proof
    assume without:
      "generic_fri_sampled_assignment_conflict_without_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers"
    have "trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out"
      unfolding
        trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer_def
      by (intro exI conjI)
        (rule fri_openings, rule partial, rule cand, rule not_low,
          rule without)
    then show ?thesis by simp
  next
    assume same:
      "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    have "trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
      s out"
      unfolding
        trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_def
      by (intro exI conjI)
        (rule fri_openings, rule out_eq, rule partial, rule cand,
          rule not_low, rule same)
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_verifier_tied_authenticated_conflict_bound_from_without_same_and_merkle:
  assumes without_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> W"
    and merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> W + M"
proof -
  have "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
            s out \<or>
          trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
            s out) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_verifier_tied_authenticated_conflict_imp_without_same_or_same_layer)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer s)
        s +
      wp_event verify_monad
        (trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks s)
        s"
    by (rule wp_event_union_bound)
  also have "... \<le> W + M"
    by (rule add_mono[OF without_bound
          wp_trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_bound_from_partial_merkle
            [OF merkle_bound]])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_verifier_tied_conflict_bound_from_authenticated_and_auth_gap:
  assumes auth_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer)
      adversary_initial_state \<le> Auth"
    and gap_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_same_layer_auth_gap)
      adversary_initial_state \<le> Gap"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_sampled_assignment_conflict)
      adversary_initial_state \<le> Auth + Gap"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?conflict =
    "staged_security_with_data_state_verifier_event
      trace_fri_verifier_tied_sampled_assignment_conflict"
  let ?auth =
    "staged_security_with_data_state_verifier_event
      trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer"
  let ?gap =
    "staged_security_with_data_state_verifier_event
      trace_fri_verifier_tied_same_layer_auth_gap"
  have "wp_event ?M ?conflict adversary_initial_state \<le>
    wp_event ?M (\<lambda>out. ?auth out \<or> ?gap out) adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono)
      (auto dest:
        trace_fri_verifier_tied_conflict_imp_authenticated_or_auth_gap
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?auth adversary_initial_state +
      wp_event ?M ?gap adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> Auth + Gap"
    by (rule add_mono[OF auth_bound gap_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_verifier_tied_authenticated_conflict_bound_from_without_same_and_merkle:
  assumes without_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer)
      adversary_initial_state \<le> W"
    and merkle_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer)
      adversary_initial_state \<le> W + M"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?auth =
    "staged_security_with_data_state_verifier_event
      trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer"
  let ?without =
    "staged_security_with_data_state_verifier_event
      trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer"
  let ?merkle =
    "staged_security_with_data_state_verifier_event
      partial_merkle_inconsistency_bad"
  have "wp_event ?M ?auth adversary_initial_state \<le>
    wp_event ?M (\<lambda>out. ?without out \<or> ?merkle out)
      adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume auth: "?auth out"
    show "?without out \<or> ?merkle out"
    proof (cases out)
      case None
      then show ?thesis
        using auth
        unfolding staged_security_with_data_state_verifier_event_def
          trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      have local_auth:
        "trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
          ?s (Some (result, final_state))"
        using auth
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
      have split:
        "trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
          ?s (Some (result, final_state)) \<or>
         trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
          ?s (Some (result, final_state))"
        by (rule
            trace_fri_verifier_tied_authenticated_conflict_imp_without_same_or_same_layer
            [OF local_auth])
      then show ?thesis
      proof
        assume without:
          "trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
            ?s (Some (result, final_state))"
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          by simp
      next
        assume same:
          "trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
            ?s (Some (result, final_state))"
        have "partial_merkle_inconsistency_bad ?s
          (Some (result, final_state))"
          by (rule
              trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_imp_partial_merkle
              [OF same])
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          by simp
      qed
    qed
  qed
  also have "... \<le>
      wp_event ?M ?without adversary_initial_state +
      wp_event ?M ?merkle adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> W + M"
    by (rule add_mono[OF without_bound merkle_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_verifier_tied_conflict_bound_from_without_same_merkle_and_auth_gap:
  fixes W M G :: prob
  assumes without_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer)
      adversary_initial_state \<le> W"
    and merkle_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le> M"
    and gap_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_same_layer_auth_gap)
      adversary_initial_state \<le> G"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_sampled_assignment_conflict)
      adversary_initial_state \<le> (W + M) + G"
proof (rule
    checked_staged_security_trace_fri_verifier_tied_conflict_bound_from_authenticated_and_auth_gap)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer)
      adversary_initial_state \<le> W + M"
    by (rule
        checked_staged_security_trace_fri_verifier_tied_authenticated_conflict_bound_from_without_same_and_merkle
        [OF without_bound merkle_bound])
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_same_layer_auth_gap)
      adversary_initial_state \<le> G"
    by (rule gap_bound)
qed

definition trace_fri_empty_sampled_assignment_structural_error_for
where
  "trace_fri_empty_sampled_assignment_structural_error_for budgets A =
    ((reachable_verifier_event_bound_for A
        trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer +
      trace_fri_controlled_merkle_error_for budgets) +
     reachable_verifier_event_bound_for A
        trace_fri_verifier_tied_same_layer_auth_gap) +
    reachable_verifier_event_bound_for A
      trace_fri_sampled_assignment_verifier_untied_gap"

definition trace_empty_header_openings_zero_error_for
where
  "trace_empty_header_openings_zero_error_for budgets A empty_bad =
    (trace_fri_zero_round_agreement_set_target_error_for budgets +
     trace_fri_controlled_merkle_error_for budgets +
     (trace_header_one_step_error_for budgets A empty_bad +
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_openings_gap) +
     trace_header_one_step_error_for budgets A empty_bad)"

definition trace_fri_header_tied_low_candidate_nonconsumed_openings_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_nonconsumed_openings_gap s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final (fri_query_idxs :: nat list)
        trace_round_layers composition_round_layers (fr :: 'f) as
        trace_openings trace_table (fr0 :: 'f) (query_idxs0 :: nat list)
        trace_openings0 trace_table0.
      trace_fri_reachable_header_tie_gap s out \<and>
      accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      trace_table_low_degree trace_table \<and>
      trace_fri_partial_candidate_evidence s out fr0 query_idxs0
        trace_openings0 trace_table0 \<and>
      (fr0 \<noteq> fr \<or> query_idxs0 \<noteq> fri_query_idxs) \<and>
      trace_openings0 \<noteq> trace_openings)"

definition trace_fri_header_tied_low_candidate_nonconsumed_root_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_nonconsumed_root_gap s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final (fri_query_idxs :: nat list)
        trace_round_layers composition_round_layers (fr :: 'f) as
        trace_openings trace_table (fr0 :: 'f) (query_idxs0 :: nat list)
        trace_openings0 trace_table0.
      trace_fri_reachable_header_tie_gap s out \<and>
      accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      trace_table_low_degree trace_table \<and>
      trace_fri_partial_candidate_evidence s out fr0 query_idxs0
        trace_openings0 trace_table0 \<and>
      fr0 \<noteq> fr \<and>
      trace_openings0 \<noteq> trace_openings)"

definition trace_fri_header_tied_low_candidate_nonconsumed_query_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_nonconsumed_query_gap s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final (fri_query_idxs :: nat list)
        trace_round_layers composition_round_layers (fr :: 'f) as
        trace_openings trace_table (fr0 :: 'f) (query_idxs0 :: nat list)
        trace_openings0 trace_table0.
      trace_fri_reachable_header_tie_gap s out \<and>
      accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      trace_table_low_degree trace_table \<and>
      trace_fri_partial_candidate_evidence s out fr0 query_idxs0
        trace_openings0 trace_table0 \<and>
      query_idxs0 \<noteq> fri_query_idxs \<and>
      trace_openings0 \<noteq> trace_openings)"

definition trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final (fri_query_idxs :: nat list)
        trace_round_layers composition_round_layers (fr :: 'f) as
        trace_openings trace_table (fr0 :: 'f) (query_idxs0 :: nat list)
        trace_openings0 trace_table0.
      trace_fri_reachable_header_tie_gap s out \<and>
      accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      trace_table_low_degree trace_table \<and>
      trace_fri_partial_candidate_evidence s out fr0 query_idxs0
        trace_openings0 trace_table0 \<and>
      fr0 \<noteq> fr \<and>
      query_idxs0 = fri_query_idxs \<and>
      trace_openings0 \<noteq> trace_openings)"

definition trace_empty_header_nonnormalized_zero_error_for
where
  "trace_empty_header_nonnormalized_zero_error_for budgets A empty_bad =
    (trace_fri_zero_round_agreement_set_target_error_for budgets +
     trace_fri_controlled_merkle_error_for budgets +
      (trace_fri_controlled_merkle_error_for budgets +
       ((reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
         reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap) +
        reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_query_gap)) +
     trace_header_one_step_error_for budgets A empty_bad)"

definition trace_fri_zero_round_verifier_consumed_low_candidate_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_zero_round_verifier_consumed_low_candidate_gap s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings trace_table.
      trace_fri_zero_round_final_obstruction s out \<and>
      trace_fri_reachable_header_tie_gap s out \<and>
      accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings \<and>
      length trace_bs = 0 \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      trace_table_low_degree trace_table)"

lemma trace_fri_header_tied_low_candidate_nonconsumed_root_gapE:
  assumes "trace_fri_header_tied_low_candidate_nonconsumed_root_gap s out"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings trace_table
      fr0 query_idxs0 trace_openings0 trace_table0 where
    "trace_fri_reachable_header_tie_gap s out"
    "accepted_with_partial_trace_openings_verifier_consumed s out
      trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "trace_table_low_degree trace_table"
    "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
      trace_openings0 trace_table0"
    "fr0 \<noteq> fr"
    "trace_openings0 \<noteq> trace_openings"
  using assms
  unfolding trace_fri_header_tied_low_candidate_nonconsumed_root_gap_def
  by blast

lemma trace_fri_header_tied_low_candidate_nonconsumed_query_gapE:
  assumes "trace_fri_header_tied_low_candidate_nonconsumed_query_gap s out"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings trace_table
      fr0 query_idxs0 trace_openings0 trace_table0 where
    "trace_fri_reachable_header_tie_gap s out"
    "accepted_with_partial_trace_openings_verifier_consumed s out
      trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "trace_table_low_degree trace_table"
    "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
      trace_openings0 trace_table0"
    "query_idxs0 \<noteq> fri_query_idxs"
    "trace_openings0 \<noteq> trace_openings"
  using assms
  unfolding trace_fri_header_tied_low_candidate_nonconsumed_query_gap_def
  by blast

lemma trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gapE:
  assumes
    "trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap s out"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings trace_table
      fr0 query_idxs0 trace_openings0 trace_table0 where
    "trace_fri_reachable_header_tie_gap s out"
    "accepted_with_partial_trace_openings_verifier_consumed s out
      trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "trace_table_low_degree trace_table"
    "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
      trace_openings0 trace_table0"
    "fr0 \<noteq> fr"
    "query_idxs0 = fri_query_idxs"
    "trace_openings0 \<noteq> trace_openings"
  using assms
  unfolding
    trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap_def
  by blast

lemma trace_fri_zero_round_verifier_consumed_low_candidate_gapE:
  assumes
    "trace_fri_zero_round_verifier_consumed_low_candidate_gap s out"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings trace_table where
    "trace_fri_zero_round_final_obstruction s out"
    "trace_fri_reachable_header_tie_gap s out"
    "accepted_with_partial_trace_openings_verifier_consumed s out
      trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings"
    "length trace_bs = 0"
    "partial_trace_table_candidate trace_table trace_openings"
    "trace_table_low_degree trace_table"
  using assms
  unfolding trace_fri_zero_round_verifier_consumed_low_candidate_gap_def
  by blast

lemma trace_fri_zero_round_verifier_consumed_low_candidate_gap_imp_candidate_available:
  assumes
    "trace_fri_zero_round_verifier_consumed_low_candidate_gap s out"
  shows "trace_fri_header_tied_candidate_available_gap s out"
proof (rule trace_fri_zero_round_verifier_consumed_low_candidate_gapE
    [OF assms])
  fix trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings trace_table
  assume gap: "trace_fri_reachable_header_tie_gap s out"
    and consumed:
      "accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    by (rule accepted_with_partial_trace_openings_verifier_consumedD(1)
        [OF consumed])
  from accepted_with_partial_trace_openings_verifier_consumedD(2)
      [OF consumed]
  obtain rest where header:
    "verifier_header_transcript s fr trace_roots trace_final as fri_dg
      composition_roots composition_final rest"
    by blast
  have partial:
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    by (rule accepted_with_partial_trace_openings_verifier_consumedD(3)
        [OF consumed])
  show "trace_fri_header_tied_candidate_available_gap s out"
    unfolding trace_fri_header_tied_candidate_available_gap_def
    by (intro exI conjI)
      (rule gap, rule fri_openings, rule header, rule partial,
       rule candidate)
qed

lemma trace_fri_zero_round_verifier_consumed_low_candidate_gap_imp_untied_openings:
  assumes
    "trace_fri_zero_round_verifier_consumed_low_candidate_gap s out"
  shows "trace_fri_header_tied_low_candidate_untied_openings_gap s out"
proof (rule trace_fri_zero_round_verifier_consumed_low_candidate_gapE
    [OF assms])
  fix trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings trace_table
  assume gap: "trace_fri_reachable_header_tie_gap s out"
    and consumed:
    "accepted_with_partial_trace_openings_verifier_consumed s out
      trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and low: "trace_table_low_degree trace_table"
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      fri_dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    by (rule accepted_with_partial_trace_openings_verifier_consumedD(1)
        [OF consumed])
  from accepted_with_partial_trace_openings_verifier_consumedD(2)
      [OF consumed]
  obtain rest where header:
    "verifier_header_transcript s fr trace_roots trace_final as fri_dg
      composition_roots composition_final rest"
    by blast
  have partial:
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    by (rule accepted_with_partial_trace_openings_verifier_consumedD(3)
        [OF consumed])
  have low_gap: "trace_fri_header_tied_low_candidate_gap s out"
    unfolding trace_fri_header_tied_low_candidate_gap_def
    by (intro exI conjI)
      (rule gap, rule fri_openings, rule header, rule partial,
        rule candidate, rule low)
  have untied:
    "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
    by (rule trace_fri_header_tied_low_candidate_gap_imp_untied_reachable_witness
        [OF low_gap])
  show "trace_fri_header_tied_low_candidate_untied_openings_gap s out"
    by (rule trace_fri_header_tied_low_candidate_untied_gap_imp_openings
        [OF untied])
qed

lemma accepted_with_partial_trace_openings_query_index_list_space:
  assumes partial:
    "accepted_with_partial_trace_openings s out fr query_idxs trace_openings"
  shows "query_idxs \<in> fri_query_index_list_space"
proof -
  have len: "length query_idxs = rounds"
    by (rule accepted_with_partial_trace_openings_shapes(1)[OF partial])
  have subset: "set query_idxs \<subseteq> query_sample_space"
  proof
    fix idx
    assume idx_in: "idx \<in> set query_idxs"
    then obtain i where i_bound: "i < length query_idxs"
      and idx_eq: "query_idxs ! i = idx"
      unfolding in_set_conv_nth by blast
    have i_round: "i < rounds"
      using i_bound len by simp
    obtain result final_state where out_eq: "out = Some (result, final_state)"
      and auth:
        "\<And>j. j < rounds \<Longrightarrow>
          partial_authenticated_table fr (scale * clength)
            (trace_openings ! j) final_state"
      using partial unfolding accepted_with_partial_trace_openings_def by blast
    have indices:
      "map opening_index (trace_openings ! i) = powers_scaled idx"
      using accepted_with_partial_trace_openings_shapes(3)[OF partial i_round]
        idx_eq by simp
    show "idx \<in> query_sample_space"
      by (rule partial_authenticated_trace_openings_query_index_in_sample_space
          [OF indices auth[OF i_round]])
  qed
  show ?thesis
    unfolding fri_query_index_list_space_def
    using len subset by simp
qed

lemma trace_fri_header_tied_low_candidate_nonconsumed_root_gap_shapes:
  assumes "trace_fri_header_tied_low_candidate_nonconsumed_root_gap s out"
  obtains fri_query_idxs query_idxs0 where
    "fri_query_idxs \<in> fri_query_index_list_space"
    "query_idxs0 \<in> fri_query_index_list_space"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings trace_table
      fr0 query_idxs0 trace_openings0 trace_table0 where
    consumed:
      "accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings"
    and evidence0:
      "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
        trace_openings0 trace_table0"
    and mismatch: "fr0 \<noteq> fr"
    by (rule trace_fri_header_tied_low_candidate_nonconsumed_root_gapE)
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      fri_dg composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers"
    by (rule accepted_with_partial_trace_openings_verifier_consumedD(1)
        [OF consumed])
  have verifier_space:
    "fri_query_idxs \<in> fri_query_index_list_space"
    by (rule accepted_fri_opening_transcript_query_index_list_space
        [OF fri_openings])
  have alternate_space: "query_idxs0 \<in> fri_query_index_list_space"
    by (rule accepted_with_partial_trace_openings_query_index_list_space)
      (rule trace_fri_partial_candidate_evidenceD(1)[OF evidence0])
	  show ?thesis
	    by (rule that[OF verifier_space alternate_space])
qed

lemma trace_fri_header_tied_low_candidate_nonconsumed_query_gap_shapes:
  assumes "trace_fri_header_tied_low_candidate_nonconsumed_query_gap s out"
  obtains fri_query_idxs query_idxs0 where
    "fri_query_idxs \<in> fri_query_index_list_space"
    "query_idxs0 \<in> fri_query_index_list_space"
    "query_idxs0 \<noteq> fri_query_idxs"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings trace_table
      fr0 query_idxs0 trace_openings0 trace_table0 where
    consumed:
      "accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings"
    and evidence0:
      "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
        trace_openings0 trace_table0"
    and mismatch: "query_idxs0 \<noteq> fri_query_idxs"
    by (rule trace_fri_header_tied_low_candidate_nonconsumed_query_gapE)
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      fri_dg composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers"
    by (rule accepted_with_partial_trace_openings_verifier_consumedD(1)
        [OF consumed])
  have verifier_space:
    "fri_query_idxs \<in> fri_query_index_list_space"
    by (rule accepted_fri_opening_transcript_query_index_list_space
        [OF fri_openings])
  have alternate_space: "query_idxs0 \<in> fri_query_index_list_space"
    by (rule accepted_with_partial_trace_openings_query_index_list_space)
      (rule trace_fri_partial_candidate_evidenceD(1)[OF evidence0])
  show ?thesis
    by (rule that[of fri_query_idxs query_idxs0,
          OF verifier_space alternate_space mismatch])
qed

lemma trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap_shapes:
  assumes
    "trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap s out"
  obtains fri_query_idxs query_idxs0 where
    "fri_query_idxs \<in> fri_query_index_list_space"
    "query_idxs0 \<in> fri_query_index_list_space"
    "query_idxs0 = fri_query_idxs"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings trace_table
      fr0 query_idxs0 trace_openings0 trace_table0 where
    consumed:
      "accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings"
    and evidence0:
      "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
        trace_openings0 trace_table0"
    and mismatch: "fr0 \<noteq> fr"
    and query_eq: "query_idxs0 = fri_query_idxs"
    by (rule trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gapE)
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      fri_dg composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers"
    by (rule accepted_with_partial_trace_openings_verifier_consumedD(1)
        [OF consumed])
  have verifier_space:
    "fri_query_idxs \<in> fri_query_index_list_space"
    by (rule accepted_fri_opening_transcript_query_index_list_space
        [OF fri_openings])
  have alternate_space: "query_idxs0 \<in> fri_query_index_list_space"
    by (rule accepted_with_partial_trace_openings_query_index_list_space)
      (rule trace_fri_partial_candidate_evidenceD(1)[OF evidence0])
	  show ?thesis
	    by (rule that[OF verifier_space alternate_space query_eq])
qed

lemma trace_fri_header_tied_low_candidate_nonconsumed_root_gap_imp_query_or_irrelevant_root:
  assumes "trace_fri_header_tied_low_candidate_nonconsumed_root_gap s out"
  shows
    "trace_fri_header_tied_low_candidate_nonconsumed_query_gap s out \<or>
     trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap
      s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings trace_table
      fr0 query_idxs0 trace_openings0 trace_table0 where
    gap: "trace_fri_reachable_header_tie_gap s out"
    and consumed:
      "accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings"
    and candidate: "partial_trace_table_candidate trace_table trace_openings"
    and low: "trace_table_low_degree trace_table"
    and evidence0:
      "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
        trace_openings0 trace_table0"
    and root_mismatch: "fr0 \<noteq> fr"
    and openings_mismatch: "trace_openings0 \<noteq> trace_openings"
    by (rule trace_fri_header_tied_low_candidate_nonconsumed_root_gapE)
  show ?thesis
  proof (cases "query_idxs0 \<noteq> fri_query_idxs")
    case True
    have "trace_fri_header_tied_low_candidate_nonconsumed_query_gap s out"
      unfolding trace_fri_header_tied_low_candidate_nonconsumed_query_gap_def
      by (intro exI conjI)
        (rule gap, rule consumed, rule candidate, rule low, rule evidence0,
          rule True, rule openings_mismatch)
    then show ?thesis by simp
  next
    case False
    then have query_eq: "query_idxs0 = fri_query_idxs"
      by simp
    have "trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap
        s out"
      unfolding
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap_def
      by (intro exI conjI)
        (rule gap, rule consumed, rule candidate, rule low, rule evidence0,
          rule root_mismatch, rule query_eq, rule openings_mismatch)
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_trace_fri_header_tied_low_candidate_nonconsumed_root_gap_bound_from_query_and_irrelevant_root:
  assumes query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap)
      adversary_initial_state \<le> Q"
    and irrelevant_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap)
      adversary_initial_state \<le> I"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_nonconsumed_root_gap)
      adversary_initial_state \<le> Q + I"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?root =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_nonconsumed_root_gap"
  let ?query =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_nonconsumed_query_gap"
  let ?irrelevant =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap"
  have "wp_event ?M ?root adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?query out \<or> ?irrelevant out)
        adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto dest:
        trace_fri_header_tied_low_candidate_nonconsumed_root_gap_imp_query_or_irrelevant_root
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?query adversary_initial_state +
      wp_event ?M ?irrelevant adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> Q + I"
    by (rule add_mono[OF query_bound irrelevant_bound])
  finally show ?thesis .
qed

lemma trace_fri_header_tied_low_candidate_nonconsumed_openings_gap_imp_root_or_query:
  assumes "trace_fri_header_tied_low_candidate_nonconsumed_openings_gap s out"
  shows
    "trace_fri_header_tied_low_candidate_nonconsumed_root_gap s out \<or>
     trace_fri_header_tied_low_candidate_nonconsumed_query_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as
      trace_openings trace_table fr0 query_idxs0 trace_openings0 trace_table0
    where
    gap: "trace_fri_reachable_header_tie_gap s out"
    and consumed:
      "accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings"
    and candidate: "partial_trace_table_candidate trace_table trace_openings"
    and low: "trace_table_low_degree trace_table"
    and evidence0:
      "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
        trace_openings0 trace_table0"
    and mismatch: "fr0 \<noteq> fr \<or> query_idxs0 \<noteq> fri_query_idxs"
    and openings_mismatch: "trace_openings0 \<noteq> trace_openings"
    unfolding trace_fri_header_tied_low_candidate_nonconsumed_openings_gap_def
    by blast
  from mismatch show ?thesis
  proof
    assume root_mismatch: "fr0 \<noteq> fr"
    have "trace_fri_header_tied_low_candidate_nonconsumed_root_gap s out"
      unfolding trace_fri_header_tied_low_candidate_nonconsumed_root_gap_def
      apply (rule exI[where x=trace_roots])
      apply (rule exI[where x=trace_bs])
      apply (rule exI[where x=trace_final])
      apply (rule exI[where x=fri_dg])
      apply (rule exI[where x=composition_roots])
      apply (rule exI[where x=composition_bs])
      apply (rule exI[where x=composition_final])
      apply (rule exI[where x=fri_query_idxs])
      apply (rule exI[where x=trace_round_layers])
      apply (rule exI[where x=composition_round_layers])
      apply (rule exI[where x=fr])
      apply (rule exI[where x=as])
      apply (rule exI[where x=trace_openings])
      apply (rule exI[where x=trace_table])
      apply (rule exI[where x=fr0])
      apply (rule exI[where x=query_idxs0])
      apply (rule exI[where x=trace_openings0])
      apply (rule exI[where x=trace_table0])
      using gap consumed candidate low evidence0 root_mismatch openings_mismatch
      by blast
    then show ?thesis by simp
  next
    assume query_mismatch: "query_idxs0 \<noteq> fri_query_idxs"
    have "trace_fri_header_tied_low_candidate_nonconsumed_query_gap s out"
      unfolding trace_fri_header_tied_low_candidate_nonconsumed_query_gap_def
      apply (rule exI[where x=trace_roots])
      apply (rule exI[where x=trace_bs])
      apply (rule exI[where x=trace_final])
      apply (rule exI[where x=fri_dg])
      apply (rule exI[where x=composition_roots])
      apply (rule exI[where x=composition_bs])
      apply (rule exI[where x=composition_final])
      apply (rule exI[where x=fri_query_idxs])
      apply (rule exI[where x=trace_round_layers])
      apply (rule exI[where x=composition_round_layers])
      apply (rule exI[where x=fr])
      apply (rule exI[where x=as])
      apply (rule exI[where x=trace_openings])
      apply (rule exI[where x=trace_table])
      apply (rule exI[where x=fr0])
      apply (rule exI[where x=query_idxs0])
      apply (rule exI[where x=trace_openings0])
      apply (rule exI[where x=trace_table0])
      using gap consumed candidate low evidence0 query_mismatch openings_mismatch
      by blast
    then show ?thesis by simp
  qed
qed

lemma trace_fri_header_tied_low_candidate_nonconsumed_root_gap_imp_untied_root_gap:
  assumes "trace_fri_header_tied_low_candidate_nonconsumed_root_gap s out"
  shows "trace_fri_header_tied_low_candidate_untied_root_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      trace_table fr0 query_idxs0 trace_openings0 trace_table0
    where gap: "trace_fri_reachable_header_tie_gap s out"
      and consumed:
        "accepted_with_partial_trace_openings_verifier_consumed s out
          trace_roots trace_bs trace_final fri_dg composition_roots
          composition_bs composition_final fri_query_idxs trace_round_layers
          composition_round_layers fr as trace_openings"
      and candidate: "partial_trace_table_candidate trace_table trace_openings"
      and low: "trace_table_low_degree trace_table"
      and evidence0:
        "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
          trace_openings0 trace_table0"
      and root_mismatch: "fr0 \<noteq> fr"
    by (rule trace_fri_header_tied_low_candidate_nonconsumed_root_gapE)
  have transcript:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    and header_ex:
      "\<exists>rest. verifier_header_transcript s fr trace_roots trace_final as
        fri_dg composition_roots composition_final rest"
    and accepted:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    by (rule accepted_with_partial_trace_openings_verifier_consumedD
        [OF consumed])+
  from header_ex obtain rest where header:
    "verifier_header_transcript s fr trace_roots trace_final as fri_dg
      composition_roots composition_final rest"
    by blast
  have accepted0:
    "accepted_with_partial_trace_openings s out fr0 query_idxs0
      trace_openings0"
    and candidate0: "partial_trace_table_candidate trace_table0 trace_openings0"
    and not_low0: "\<not> trace_table_low_degree trace_table0"
    by (rule trace_fri_partial_candidate_evidenceD[OF evidence0])+
  show ?thesis
    unfolding trace_fri_header_tied_low_candidate_untied_root_gap_def
    by (rule trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI
        [OF gap transcript header accepted candidate low accepted0 candidate0
          not_low0])
      (simp add: root_mismatch)
qed

lemma trace_fri_header_tied_low_candidate_nonconsumed_query_gap_imp_untied_query_gap:
  assumes "trace_fri_header_tied_low_candidate_nonconsumed_query_gap s out"
  shows "trace_fri_header_tied_low_candidate_untied_query_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      trace_table fr0 query_idxs0 trace_openings0 trace_table0
    where gap: "trace_fri_reachable_header_tie_gap s out"
      and consumed:
        "accepted_with_partial_trace_openings_verifier_consumed s out
          trace_roots trace_bs trace_final fri_dg composition_roots
          composition_bs composition_final fri_query_idxs trace_round_layers
          composition_round_layers fr as trace_openings"
      and candidate: "partial_trace_table_candidate trace_table trace_openings"
      and low: "trace_table_low_degree trace_table"
      and evidence0:
        "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
          trace_openings0 trace_table0"
      and query_mismatch: "query_idxs0 \<noteq> fri_query_idxs"
    by (rule trace_fri_header_tied_low_candidate_nonconsumed_query_gapE)
  have transcript:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    and header_ex:
      "\<exists>rest. verifier_header_transcript s fr trace_roots trace_final as
        fri_dg composition_roots composition_final rest"
    and accepted:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    by (rule accepted_with_partial_trace_openings_verifier_consumedD
        [OF consumed])+
  from header_ex obtain rest where header:
    "verifier_header_transcript s fr trace_roots trace_final as fri_dg
      composition_roots composition_final rest"
    by blast
  have accepted0:
    "accepted_with_partial_trace_openings s out fr0 query_idxs0
      trace_openings0"
    and candidate0: "partial_trace_table_candidate trace_table0 trace_openings0"
    and not_low0: "\<not> trace_table_low_degree trace_table0"
    by (rule trace_fri_partial_candidate_evidenceD[OF evidence0])+
  show ?thesis
    unfolding trace_fri_header_tied_low_candidate_untied_query_gap_def
    by (rule trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI
        [OF gap transcript header accepted candidate low accepted0 candidate0
          not_low0])
      (simp add: query_mismatch)
qed

lemma checked_staged_security_trace_fri_header_tied_low_candidate_nonconsumed_openings_gap_bound_from_root_query:
  assumes root_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_nonconsumed_root_gap)
      adversary_initial_state \<le> R"
    and query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap)
      adversary_initial_state \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_nonconsumed_openings_gap)
      adversary_initial_state \<le> R + Q"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?nonconsumed =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_nonconsumed_openings_gap"
  let ?root =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_nonconsumed_root_gap"
  let ?query =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_nonconsumed_query_gap"
  have split:
    "wp_event ?M ?nonconsumed adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?root out \<or> ?query out) adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto dest:
        trace_fri_header_tied_low_candidate_nonconsumed_openings_gap_imp_root_or_query
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?root adversary_initial_state +
      wp_event ?M ?query adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> R + Q"
    by (rule add_mono[OF root_bound query_bound])
  finally show ?thesis .
qed

lemma trace_fri_zero_round_final_obstruction_imp_checked_merkle_low_consumed_or_header:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and obstruction: "trace_fri_zero_round_final_obstruction s out"
  shows
    "trace_fri_zero_round_checked_final_obstruction s out \<or>
     partial_merkle_inconsistency_bad s out \<or>
     trace_fri_zero_round_verifier_consumed_low_candidate_gap s out \<or>
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
    by (rule trace_fri_zero_round_final_obstructionE[OF obstruction])
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
        have consumed:
          "accepted_with_partial_trace_openings_verifier_consumed s out
            trace_roots trace_bs trace_final dg composition_roots
            composition_bs composition_final fri_query_idxs
            trace_round_layers composition_round_layers fr as
            trace_openings"
          unfolding accepted_with_partial_trace_openings_verifier_consumed_def
          by (intro conjI exI)
            (rule fri_openings, rule header, rule partial)
        have low_gap:
          "trace_fri_zero_round_verifier_consumed_low_candidate_gap s out"
          unfolding
            trace_fri_zero_round_verifier_consumed_low_candidate_gap_def
          by (intro exI conjI)
            (rule obstruction, rule gap, rule consumed, rule rounds_empty,
              rule candidate, rule True)
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

lemma checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_staged_checked_merkle_low_consumed_header:
  fixes Q M L H :: prob
  assumes checked_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le> Q"
    and merkle_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state \<le> M"
    and low_consumed_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_zero_round_verifier_consumed_low_candidate_gap)
        adversary_initial_state \<le> L"
    and header_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_partial_candidate)
        adversary_initial_state \<le> H"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state \<le> Q + M + L + H"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?zero =
    "staged_security_with_data_state_verifier_event
      trace_fri_zero_round_final_obstruction"
  let ?checked =
    "staged_security_with_data_state_verifier_event
      trace_fri_zero_round_checked_final_obstruction"
  let ?merkle =
    "staged_security_with_data_state_verifier_event
      partial_merkle_inconsistency_bad"
  let ?low =
    "staged_security_with_data_state_verifier_event
      trace_fri_zero_round_verifier_consumed_low_candidate_gap"
  let ?header =
    "staged_security_with_data_state_verifier_event
      trace_fri_bad_with_header_tied_partial_candidate"
		  have "wp_event ?M ?zero adversary_initial_state \<le>
		      wp_event ?M
		        (\<lambda>out. ?checked out \<or> ?merkle out \<or> ?low out \<or>
		          ?header out)
		        adversary_initial_state"
		  proof (rule wp_event_mono_on_support)
	    fix out
	    assume support:
	      "out \<in> set_dist (execute ?M adversary_initial_state)"
	      and zero: "?zero out"
	    show "?checked out \<or> ?merkle out \<or> ?low out \<or> ?header out"
	    proof (cases out)
	      case None
	      then show ?thesis
	        using zero unfolding staged_security_with_data_state_verifier_event_def
	        by simp
	    next
	      case (Some out_data)
	      then obtain data attacker_state result final_state where out_eq:
	        "out = Some (((data, attacker_state), result), final_state)"
	        by (cases out_data, auto split: prod.splits)
	      let ?s =
	        "verifier_state_from_adversary attacker_state
	          (staged_proof_transcript data)"
	      from checked_staged_security_experiment_with_data_state_outcomeE
	          [OF support[unfolded out_eq]]
	      have verify_support:
	        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
	        by blast
	      have zero_local:
	        "trace_fri_zero_round_final_obstruction ?s
	          (Some (result, final_state))"
	        using zero unfolding out_eq
	          staged_security_with_data_state_verifier_event_def
	        by simp
	      have
	        "trace_fri_zero_round_checked_final_obstruction ?s
	          (Some (result, final_state)) \<or>
	         partial_merkle_inconsistency_bad ?s
	          (Some (result, final_state)) \<or>
	         trace_fri_zero_round_verifier_consumed_low_candidate_gap ?s
	          (Some (result, final_state)) \<or>
	         trace_fri_bad_with_header_tied_partial_candidate ?s
	          (Some (result, final_state))"
	        by (rule
	            trace_fri_zero_round_final_obstruction_imp_checked_merkle_low_consumed_or_header
	            [OF verify_support zero_local])
	      then show ?thesis
	        unfolding out_eq staged_security_with_data_state_verifier_event_def
	        by simp
	    qed
	  qed
  also have "... \<le>
      wp_event ?M ?checked adversary_initial_state +
      wp_event ?M ?merkle adversary_initial_state +
      wp_event ?M ?low adversary_initial_state +
      wp_event ?M ?header adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le> Q + M + L + H"
    by (intro add_mono checked_bound merkle_bound low_consumed_bound
        header_bound)
  finally show ?thesis .
qed

lemma trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_imp_nonconsumed:
  assumes
    "trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap
      s out"
  shows
    "trace_fri_header_tied_low_candidate_nonconsumed_openings_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table fr0 query_idxs0 trace_openings0 trace_table0 where
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
    and partial0:
      "accepted_with_partial_trace_openings s out fr0 query_idxs0
        trace_openings0"
    and candidate0:
      "partial_trace_table_candidate trace_table0 trace_openings0"
    and not_low0: "\<not> trace_table_low_degree trace_table0"
    and mismatch:
      "fr0 \<noteq> fr \<or> query_idxs0 \<noteq> fri_query_idxs"
    and openings_mismatch:
      "trace_openings0 \<noteq> trace_openings"
    unfolding
      trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_def
      trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
    by blast
  have consumed:
    "accepted_with_partial_trace_openings_verifier_consumed s out
      trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings"
    unfolding accepted_with_partial_trace_openings_verifier_consumed_def
    by (intro conjI exI)
      (rule fri_openings, rule header, rule partial)
  have evidence0:
    "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
      trace_openings0 trace_table0"
    unfolding trace_fri_partial_candidate_evidence_def
    by (intro conjI)
      (rule partial0, rule candidate0, rule not_low0)
  show ?thesis
    unfolding trace_fri_header_tied_low_candidate_nonconsumed_openings_gap_def
    by (intro exI conjI)
      (rule gap, rule consumed, rule candidate, rule low, rule evidence0,
        rule mismatch, rule openings_mismatch)
qed

lemma checked_staged_security_trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_bound_from_nonconsumed:
  assumes nonconsumed_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_nonconsumed_openings_gap)
      adversary_initial_state \<le> N"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap)
      adversary_initial_state \<le> N"
proof (rule order_trans[OF _ nonconsumed_bound])
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_nonconsumed_openings_gap)
      adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto dest:
        trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_imp_nonconsumed
        split: option.splits prod.splits)
qed

lemma checked_staged_security_trace_fri_sampled_assignment_conflict_bound_structural:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_assignment_conflict)
      adversary_initial_state \<le>
      trace_fri_empty_sampled_assignment_structural_error_for budgets A"
proof -
  have without:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer)
      adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer"
	    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
	      (simp add:
	        trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer_def
	        accepted_fri_opening_transcript_def,
	       rule reachable_verifier_event_bound_for_ge)
  have merkle:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets"
    unfolding trace_fri_controlled_merkle_error_for_def
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
  have gap:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_same_layer_auth_gap)
      adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_verifier_tied_same_layer_auth_gap"
	    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
	      (simp add: trace_fri_verifier_tied_same_layer_auth_gap_def
	        accepted_fri_opening_transcript_def,
	       rule reachable_verifier_event_bound_for_ge)
  have tied:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_verifier_tied_sampled_assignment_conflict)
      adversary_initial_state \<le>
      (reachable_verifier_event_bound_for A
        trace_fri_verifier_tied_sampled_assignment_conflict_without_same_layer +
       trace_fri_controlled_merkle_error_for budgets) +
      reachable_verifier_event_bound_for A
        trace_fri_verifier_tied_same_layer_auth_gap"
    by (rule
        checked_staged_security_trace_fri_verifier_tied_conflict_bound_from_without_same_merkle_and_auth_gap
        [OF without merkle gap])
  have untied:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_assignment_verifier_untied_gap)
      adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_sampled_assignment_verifier_untied_gap"
	    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
	      (simp add: trace_fri_sampled_assignment_verifier_untied_gap_def
	        trace_fri_sampled_assignment_conflict_def
	        trace_fri_partial_candidate_opening_evidence_def
	        accepted_fri_opening_transcript_def,
	       rule reachable_verifier_event_bound_for_ge)
  show ?thesis
    unfolding trace_fri_empty_sampled_assignment_structural_error_for_def
    by (rule
        checked_staged_security_trace_fri_sampled_assignment_conflict_bound_from_verifier_tied_and_untied
        [OF tied untied])
qed

lemma checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_agreement_sets_header_and_openings:
  fixes H :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and header_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_partial_candidate)
        adversary_initial_state \<le> H"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets +
      trace_fri_controlled_merkle_error_for budgets +
      (H +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_openings_gap) +
      H"
proof -
  have checked:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets"
    by (rule
        checked_staged_security_trace_fri_zero_round_checked_final_obstruction_bound_from_agreement_sets
        [OF wf controlled])
  have merkle:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets"
    unfolding trace_fri_controlled_merkle_error_for_def
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
	  have openings:
	    "wp_event (checked_staged_security_experiment_with_data_state A)
	      (staged_security_with_data_state_verifier_event
	        trace_fri_header_tied_low_candidate_untied_openings_gap)
	      adversary_initial_state \<le>
	      reachable_verifier_event_bound_for A
	        trace_fri_header_tied_low_candidate_untied_openings_gap"
	  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
	    show "\<And>s. \<not>
	      trace_fri_header_tied_low_candidate_untied_openings_gap s None"
	      by (simp add: trace_fri_header_tied_low_candidate_untied_openings_gap_def
	        trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
	        accepted_fri_opening_transcript_def)
	  next
	    fix data attacker_state
	    assume support:
	      "Some (data, attacker_state) \<in>
	        set_dist
	          (execute (checked_staged_transcript_program A)
	            adversary_initial_state)"
	    show "wp_event verify_monad
	      (trace_fri_header_tied_low_candidate_untied_openings_gap
	        (verifier_state_from_adversary attacker_state
	          (staged_proof_transcript data)))
	      (verifier_state_from_adversary attacker_state
	        (staged_proof_transcript data))
	      \<le> reachable_verifier_event_bound_for A
	        trace_fri_header_tied_low_candidate_untied_openings_gap"
	      by (rule reachable_verifier_event_bound_for_ge[OF support])
	  qed
  have untied:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_reachable_witness_gap)
      adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_openings_gap"
  proof -
    have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_reachable_witness_gap)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_header_tied_low_candidate_untied_openings_gap)
        adversary_initial_state"
      unfolding staged_security_with_data_state_verifier_event_def
      by (rule wp_event_mono_on_support)
        (auto dest: trace_fri_header_tied_low_candidate_untied_gap_imp_openings
          split: option.splits prod.splits)
    also have "... \<le>
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_openings_gap"
      by (rule openings)
    finally show ?thesis .
  qed
  have transfer:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_candidate_transfer_gap)
      adversary_initial_state \<le>
      H +
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_openings_gap"
    by (rule
        checked_staged_security_trace_fri_header_tied_candidate_transfer_gap_bound_from_staged_header_and_untied
        [OF header_bound untied])
  show ?thesis
    by (rule
        checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_staged_checked_merkle_transfer_header
        [OF checked merkle transfer header_bound])
qed

lemma checked_staged_security_trace_fri_header_tied_low_candidate_untied_openings_gap_bound_from_hash_and_nonnormalized:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_openings_gap)
      adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets +
      ((reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap) +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap)"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?openings =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_untied_openings_gap"
  let ?hash =
    "staged_security_with_data_state_verifier_event
      hash_map_output_collision_bad"
  let ?nonnormal =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap"
  let ?nonconsumed =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_nonconsumed_openings_gap"
  let ?root =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_nonconsumed_root_gap"
  let ?query =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_nonconsumed_query_gap"
  let ?irrelevant =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap"
  have hash:
    "wp_event ?M ?hash adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets"
    unfolding trace_fri_controlled_merkle_error_for_def
    by (rule
        checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  have root:
    "wp_event ?M ?root adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_root_gap"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (simp add: trace_fri_header_tied_low_candidate_nonconsumed_root_gap_def
        accepted_with_partial_trace_openings_verifier_consumed_def
        trace_fri_partial_candidate_evidence_def
        accepted_fri_opening_transcript_def,
       rule reachable_verifier_event_bound_for_ge)
  have query:
    "wp_event ?M ?query adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (simp add: trace_fri_header_tied_low_candidate_nonconsumed_query_gap_def
        accepted_with_partial_trace_openings_verifier_consumed_def
        trace_fri_partial_candidate_evidence_def
        accepted_fri_opening_transcript_def,
       rule reachable_verifier_event_bound_for_ge)
  have irrelevant:
    "wp_event ?M ?irrelevant adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (simp add:
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap_def
        accepted_with_partial_trace_openings_verifier_consumed_def
        trace_fri_partial_candidate_evidence_def
        accepted_fri_opening_transcript_def,
       rule reachable_verifier_event_bound_for_ge)
  have root_refined:
    "wp_event ?M ?root adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap"
    by (rule
        checked_staged_security_trace_fri_header_tied_low_candidate_nonconsumed_root_gap_bound_from_query_and_irrelevant_root
        [OF query irrelevant])
  have nonconsumed_root_query:
    "wp_event ?M ?nonconsumed adversary_initial_state \<le>
      (reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap) +
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap"
    by (rule
        checked_staged_security_trace_fri_header_tied_low_candidate_nonconsumed_openings_gap_bound_from_root_query
        [OF root_refined query])
  have nonnormal_root_query:
    "wp_event ?M ?nonnormal adversary_initial_state \<le>
      (reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap) +
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap"
    by (rule
        checked_staged_security_trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_bound_from_nonconsumed
        [OF nonconsumed_root_query])
  have "wp_event ?M ?openings adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?hash out \<or> ?nonnormal out)
        adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto
        dest:
          trace_fri_header_tied_low_candidate_untied_openings_gap_imp_normalized_or_nonnormalized
          trace_fri_header_tied_low_candidate_untied_normalized_openings_gap_imp_hash_collision
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?hash adversary_initial_state +
      wp_event ?M ?nonnormal adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      trace_fri_controlled_merkle_error_for budgets +
      ((reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap) +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap)"
    by (rule add_mono[OF hash nonnormal_root_query])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_zero_round_verifier_consumed_low_candidate_gap_bound_from_hash_and_nonnormalized:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_verifier_consumed_low_candidate_gap)
      adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets +
      ((reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap) +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_verifier_consumed_low_candidate_gap)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_header_tied_low_candidate_untied_openings_gap)
        adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto
        dest:
          trace_fri_zero_round_verifier_consumed_low_candidate_gap_imp_untied_openings
        split: option.splits prod.splits)
  also have "... \<le>
      trace_fri_controlled_merkle_error_for budgets +
      ((reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap) +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap)"
    by (rule
        checked_staged_security_trace_fri_header_tied_low_candidate_untied_openings_gap_bound_from_hash_and_nonnormalized
        [OF wf controlled])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_agreement_sets_header_and_nonnormalized:
  fixes H :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and header_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_partial_candidate)
        adversary_initial_state \<le> H"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets +
      trace_fri_controlled_merkle_error_for budgets +
      (trace_fri_controlled_merkle_error_for budgets +
       ((reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
         reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap) +
        reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_query_gap)) +
      H"
proof -
  have checked:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets"
    by (rule
        checked_staged_security_trace_fri_zero_round_checked_final_obstruction_bound_from_agreement_sets
        [OF wf controlled])
  have merkle:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets"
    unfolding trace_fri_controlled_merkle_error_for_def
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
  have openings:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_verifier_consumed_low_candidate_gap)
      adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets +
      ((reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap) +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_nonconsumed_query_gap)"
    by (rule
        checked_staged_security_trace_fri_zero_round_verifier_consumed_low_candidate_gap_bound_from_hash_and_nonnormalized
        [OF wf controlled])
  have zero:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets +
      trace_fri_controlled_merkle_error_for budgets +
      (trace_fri_controlled_merkle_error_for budgets +
       ((reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
         reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap) +
        reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_query_gap)) +
      H"
    by (rule
        checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_staged_checked_merkle_low_consumed_header
        [OF checked merkle openings header_bound])
  show ?thesis
    by (rule zero)
qed

definition trace_empty_header_sampled_split_one_step_error_for
where
  "trace_empty_header_sampled_split_one_step_error_for budgets A empty_bad =
    trace_one_step_sampled_error_for budgets empty_bad +
      (trace_fri_empty_sampled_assignment_structural_error_for budgets A +
       trace_empty_header_openings_zero_error_for budgets A empty_bad)"

definition concrete_trace_empty_header_sampled_split_one_step_error_for
where
  "concrete_trace_empty_header_sampled_split_one_step_error_for budgets A =
    trace_empty_header_sampled_split_one_step_error_for budgets A
      trace_one_step_split_bad"

lemma trace_empty_header_sampled_split_one_step_error_for_bound:
  fixes empty_bad :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and empty_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        empty_bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (trace_fri_canonical_layer_len i) (empty_pw i)
            (empty_layer i prefix) (empty_claimed i prefix)
            (empty_dom i prefix)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state
    \<le> trace_empty_header_sampled_split_one_step_error_for budgets A empty_bad"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> trace_one_step_sampled_error_for budgets empty_bad"
    by (rule trace_one_step_sampled_error_for_bound
        [OF wf controlled empty_subset])
  have conflict_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_assignment_conflict)
      adversary_initial_state
    \<le> trace_fri_empty_sampled_assignment_structural_error_for budgets A"
    by (rule
        checked_staged_security_trace_fri_sampled_assignment_conflict_bound_structural
        [OF wf controlled])
  have header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state
    \<le> trace_header_one_step_error_for budgets A empty_bad"
    by (rule trace_header_one_step_error_for_bound
        [OF wf controlled empty_subset])
  have zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state
    \<le> trace_empty_header_openings_zero_error_for budgets A empty_bad"
    unfolding trace_empty_header_openings_zero_error_for_def
    by (rule
        checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_agreement_sets_header_and_openings
        [OF wf controlled header_bound])
  have branch:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state
      \<le> trace_one_step_sampled_error_for budgets empty_bad +
        (trace_fri_empty_sampled_assignment_structural_error_for budgets A +
         trace_empty_header_openings_zero_error_for budgets A empty_bad)"
    by (rule
        checked_staged_security_trace_fri_empty_header_bound_from_staged_sampled_conflict_and_zero
        [OF sampled conflict_bound zero_bound])
  show ?thesis
    using branch
    by (simp add: trace_empty_header_sampled_split_one_step_error_for_def)
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_sampled_split_one_step_fri_components:
  fixes trace_bad empty_bad :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
    and comp_bad :: "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        trace_bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (trace_fri_canonical_layer_len i) (empty_pw i)
            (empty_layer i prefix) (empty_claimed i prefix)
            (empty_dom i prefix)"
    and comp_subset:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        comp_bad dg i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (composition_fri_canonical_layer_len dg i) (comp_pw dg i)
            (comp_layer dg i prefix) (comp_claimed dg i prefix)
            (comp_dom dg i prefix)"
    and empty_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        empty_bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (trace_fri_canonical_layer_len i) (empty_pw i)
            (empty_layer i prefix) (empty_claimed i prefix)
            (empty_dom i prefix)"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        active_route_current_prefix_authenticated_error_for A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
    trace_header_one_step_error_for budgets A trace_bad +
      composition_one_step_verifier_tied_controlled_error_for budgets
        comp_bad +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound) +
      trace_empty_header_sampled_split_one_step_error_for budgets A empty_bad +
      active_route_current_empty_query_error_for A)"
proof -
  have trace_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state
    \<le> trace_header_one_step_error_for budgets A trace_bad"
    by (rule trace_header_one_step_error_for_bound
        [OF wf controlled trace_subset])
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state
    \<le> composition_one_step_verifier_tied_controlled_error_for budgets
        comp_bad"
    by (rule composition_one_step_verifier_tied_controlled_error_for_bound
        [OF wf controlled comp_subset])
  have empty_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state
    \<le> trace_empty_header_sampled_split_one_step_error_for budgets A empty_bad"
    by (rule trace_empty_header_sampled_split_one_step_error_for_bound
        [OF wf controlled empty_subset])
  show ?thesis
    by (rule
        stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_bounds
        [OF false_statement wf controlled trace_bound comp_bound empty_bound])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_sampled_split_endpoint:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        active_route_current_prefix_authenticated_error_for A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
    concrete_trace_header_one_step_error_for budgets A +
      concrete_composition_one_step_error_for budgets A +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound) +
      concrete_trace_empty_header_sampled_split_one_step_error_for budgets A +
      active_route_current_empty_query_error_for A)"
  unfolding concrete_trace_header_one_step_error_for_def
    concrete_composition_one_step_error_for_def
    concrete_trace_empty_header_sampled_split_one_step_error_for_def
  by (rule
      stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_sampled_split_one_step_fri_components
      [where trace_bad = trace_one_step_split_bad
        and comp_bad = composition_one_step_split_bad
        and empty_bad = trace_one_step_split_bad
        and empty_pw = trace_one_step_split_pw
        and empty_layer = trace_one_step_split_layer
        and empty_claimed = trace_one_step_split_claimed
        and empty_dom = trace_one_step_split_domain
        and comp_pw = composition_one_step_split_pw
        and comp_layer = composition_one_step_split_layer
        and comp_claimed = composition_one_step_split_claimed
        and comp_dom = composition_one_step_split_domain,
        OF false_statement wf controlled])
    (simp_all add:
      trace_one_step_split_bad_def
      composition_one_step_split_bad_def
      trace_one_step_disagreement_bad_for_def
      composition_one_step_disagreement_bad_for_def)

definition active_route_current_prefix_conceptual_residual_error_for
where
  "active_route_current_prefix_conceptual_residual_error_for
      (A :: 'f staged_adversary) (i :: nat) =
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      checked_staged_security_with_query_prefix_conceptual_context_residual_at
      adversary_initial_state"

definition active_route_current_prefix_conceptual_hit_residual_error_for
where
  "active_route_current_prefix_conceptual_hit_residual_error_for
      (A :: 'f staged_adversary) (i :: nat) =
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out.
        checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
          i out \<and>
        checked_staged_security_with_query_prefix_conceptual_context_residual_at
          out)
      adversary_initial_state"

definition active_route_current_prefix_conceptual_bound_for
where
  "active_route_current_prefix_conceptual_bound_for
      (budgets :: staged_budgets) (A :: 'f staged_adversary)
      (i :: nat) =
    staged_phase_relation_error size
      (staged_query_search_queries budgets i + 1) +
    query_error_bound +
    active_route_current_prefix_conceptual_hit_residual_error_for A i"

lemma active_route_current_prefix_authenticated_error_for_le_conceptual_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "active_route_current_prefix_authenticated_error_for A i \<le>
      active_route_current_prefix_conceptual_bound_for budgets A i"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Hit =
    "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
      i"
  let ?Conceptual =
    "checked_staged_security_with_query_prefix_conceptual_target_hit"
  let ?Residual =
    "\<lambda>out. ?Hit out \<and>
      checked_staged_security_with_query_prefix_conceptual_context_residual_at
        out"
  have event_le:
    "wp_event ?M ?Hit adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Conceptual out \<or> ?Residual out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit: "?Hit out"
    from checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_imp_conceptual_or_residual_on_support
        [OF wf controlled i_bound support hit]
    show "?Conceptual out \<or> ?Residual out"
      using hit by blast
  qed
  have conceptual_bound:
    "wp_event ?M ?Conceptual adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_target_hit_bound
        [OF wf controlled i_bound])
  have union_bound:
    "wp_event ?M (\<lambda>out. ?Conceptual out \<or> ?Residual out)
      adversary_initial_state \<le>
     wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state"
    by (rule wp_event_union_bound)
  have residual_bound:
    "wp_event ?M ?Residual adversary_initial_state \<le>
      active_route_current_prefix_conceptual_hit_residual_error_for A i"
    by (simp add:
        active_route_current_prefix_conceptual_hit_residual_error_for_def)
  have sum_bound:
    "wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      active_route_current_prefix_conceptual_hit_residual_error_for A i"
    by (intro add_mono conceptual_bound residual_bound)
  show ?thesis
    unfolding active_route_current_prefix_authenticated_error_for_def
      active_route_current_prefix_conceptual_bound_for_def
    by (rule order_trans[OF event_le])
      (rule order_trans[OF union_bound sum_bound])
qed

definition active_route_current_empty_conceptual_residual_error_for
  :: "'f itself \<Rightarrow> 'f staged_adversary \<Rightarrow> prob"
where
  "active_route_current_empty_conceptual_residual_error_for
      (_ :: 'f itself)
      (A :: 'f staged_adversary) =
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A 0)
      (checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
        (0 :: nat))
      adversary_initial_state"

definition active_route_current_empty_conceptual_bound_for
where
  "active_route_current_empty_conceptual_bound_for
      (budgets :: staged_budgets) (A :: 'f staged_adversary) =
    staged_phase_relation_error size
      (staged_query_search_queries budgets 0 + 1) +
    query_error_bound +
      active_route_current_empty_conceptual_residual_error_for TYPE('f) A +
      (active_route_transcript_pre_error_for A +
      staged_concrete_transcript_target_error_bound)"

lemma active_route_current_empty_query_error_for_le_conceptual_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "active_route_current_empty_query_error_for A \<le>
      active_route_current_empty_conceptual_bound_for budgets A"
proof -
  have i_bound: "0 < rounds"
    using rounds_positive by simp
  have residual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A 0)
      (checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
        (0 :: nat))
      adversary_initial_state \<le>
      active_route_current_empty_conceptual_residual_error_for TYPE('f) A"
    unfolding active_route_current_empty_conceptual_residual_error_for_def
    by (rule wp_event_mono) simp
  have pre_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_pre_hit
      adversary_initial_state \<le> active_route_transcript_pre_error_for A"
    by (simp add: active_route_transcript_pre_error_for_def)
  have new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  show ?thesis
    unfolding active_route_current_empty_query_error_for_def
      active_route_current_empty_conceptual_bound_for_def
    by (rule
        checked_staged_security_with_data_state_current_empty_query_opening_hit_at_bound_from_conceptual_empty_residual_and_transcript
        [OF wf controlled i_bound residual_bound pre_bound new_bound])
qed

definition trace_no_full_cover_sampled_query_error_for
where
  "trace_no_full_cover_sampled_query_error_for budgets bad =
    (\<Sum>challenges \<in> fri_challenge_space (ceil_log clength).
      (1 / nnreal (CARD('f) ^ ceil_log clength)) *
        (nnreal
          (card
            (trace_fri_sampled_query_no_full_cover_failure_query_fiber
              bad challenges)) *
          (1 / nnreal (card query_sample_space)) ^ rounds)) +
    hash_relation_budget_value
      (query_index_raw_list_relation_fiber_bound
        (\<Union>challenges \<in> fri_challenge_space (ceil_log clength).
          trace_fri_sampled_query_no_full_cover_failure_query_fiber
            bad challenges))
      (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
    hash_relation_budget_value
      (card (fri_challenge_space (ceil_log clength)) * ceil_log clength)
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)"

definition trace_canonical_full_cover_shape_failure_error_for
where
  "trace_canonical_full_cover_shape_failure_error_for A bad =
    reachable_verifier_event_bound_for A
      (\<lambda>s. trace_fri_sampled_full_cover_proximity_failure s bad) +
    reachable_verifier_event_bound_for A
      trace_fri_sampled_full_cover_index_failure +
    reachable_verifier_event_bound_for A
      trace_fri_sampled_full_cover_shape_failure"

definition trace_restricted_sampled_query_error_for
where
  "trace_restricted_sampled_query_error_for budgets A bad =
    trace_no_full_cover_sampled_query_error_for budgets bad +
    trace_canonical_full_cover_shape_failure_error_for A bad"

lemma trace_restricted_sampled_query_error_for_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> trace_restricted_sampled_query_error_for budgets A bad"
proof -
  have no_full:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_query_no_full_cover_failure_candidate s bad))
      adversary_initial_state
    \<le> trace_no_full_cover_sampled_query_error_for budgets bad"
    unfolding trace_no_full_cover_sampled_query_error_for_def
    by (rule
        checked_staged_security_trace_fri_sampled_query_no_full_cover_failure_candidate_bound_from_restricted_pairs
        [OF wf controlled])
  have failure:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_canonical_full_cover_failure s bad))
      adversary_initial_state
    \<le> trace_canonical_full_cover_shape_failure_error_for A bad"
    unfolding trace_canonical_full_cover_shape_failure_error_for_def
  proof (rule
      checked_staged_security_trace_fri_sampled_canonical_full_cover_failure_bound_from_shape_subcases)
    fix data attacker_state
    assume support:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        (\<lambda>s. trace_fri_sampled_full_cover_proximity_failure s bad)"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  next
    fix data attacker_state
    assume support:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        trace_fri_sampled_full_cover_index_failure"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  next
    fix data attacker_state
    assume support:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
        (trace_fri_sampled_full_cover_shape_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        trace_fri_sampled_full_cover_shape_failure"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  qed
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> trace_no_full_cover_sampled_query_error_for budgets bad +
      trace_canonical_full_cover_shape_failure_error_for A bad"
    by (rule
        checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_canonical_failure
        [OF no_full failure])
  show ?thesis
    using sampled
    by (simp add: trace_restricted_sampled_query_error_for_def)
qed

definition concrete_sampled_split_stark_soundness_bound_for
where
  "concrete_sampled_split_stark_soundness_bound_for budgets A =
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        active_route_current_prefix_conceptual_bound_for budgets A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
    concrete_trace_header_one_step_error_for budgets A +
      concrete_composition_one_step_error_for budgets A +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound) +
      concrete_trace_empty_header_sampled_split_one_step_error_for budgets A +
      active_route_current_empty_conceptual_bound_for budgets A)"

theorem stark_soundness_trace_empty_sampled_split_endpoint:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    concrete_sampled_split_stark_soundness_bound_for budgets A"
proof -
  have old_bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
        (\<Sum>i<rounds.
          active_route_current_prefix_authenticated_error_for A i +
          (active_route_transcript_pre_error_for A +
            staged_concrete_transcript_target_error_bound) +
          (active_route_transcript_pre_error_for A +
            staged_concrete_transcript_target_error_bound)) +
      concrete_trace_header_one_step_error_for budgets A +
        concrete_composition_one_step_error_for budgets A +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        concrete_trace_empty_header_sampled_split_one_step_error_for budgets A +
        active_route_current_empty_query_error_for A)"
    by (rule
        stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_sampled_split_endpoint
        [OF false_statement wf controlled])
  have prefix_terms:
    "(\<Sum>i<rounds.
        active_route_current_prefix_authenticated_error_for A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound))
      \<le>
     (\<Sum>i<rounds.
        active_route_current_prefix_conceptual_bound_for budgets A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound))"
    by (intro sum_mono add_mono order_refl
        active_route_current_prefix_authenticated_error_for_le_conceptual_bound
        [OF wf controlled])
      simp
  have empty_term:
    "active_route_current_empty_query_error_for A \<le>
      active_route_current_empty_conceptual_bound_for budgets A"
    by (rule active_route_current_empty_query_error_for_le_conceptual_bound
        [OF wf controlled])
  have old_le_new:
    "hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
        (\<Sum>i<rounds.
          active_route_current_prefix_authenticated_error_for A i +
          (active_route_transcript_pre_error_for A +
            staged_concrete_transcript_target_error_bound) +
          (active_route_transcript_pre_error_for A +
            staged_concrete_transcript_target_error_bound)) +
      concrete_trace_header_one_step_error_for budgets A +
        concrete_composition_one_step_error_for budgets A +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        concrete_trace_empty_header_sampled_split_one_step_error_for budgets A +
        active_route_current_empty_query_error_for A)
      \<le> concrete_sampled_split_stark_soundness_bound_for budgets A"
    unfolding concrete_sampled_split_stark_soundness_bound_for_def
    by (intro add_mono order_refl prefix_terms empty_term)
  show ?thesis
    by (rule order_trans[OF old_bound old_le_new])
qed

end

hide_fact
  soundness.stark_soundness_trace_empty_sampled_split_endpoint
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_sampled_split_endpoint

end
