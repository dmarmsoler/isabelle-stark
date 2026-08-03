(*  Title:      Stark/Soundness_FRI_Staged_Replay_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Staged_Replay_Bounds
  imports
    Soundness_FRI_Staged_Active_Bounds
    Soundness_FRI_Replay_Gap_Assignment
    Soundness_FRI_Composition_Replay_Gaps
    Soundness_FRI_Trace_Replay_Gaps
    Soundness_FRI_Trace_Sibling_Evidence
begin

text \<open>
  Staged active FRI bounds that additionally use the replay-gap assignment
  adapters.  This theory is deliberately downstream of both the staged
  prequery-accounting layer and the replay-gap layer.
\<close>

context soundness
begin

lemma wp_trace_fri_header_tied_without_same_without_recorded_missing_bound_from_partial_merkle_and_replay_gaps:
  fixes P G N S F :: prob
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
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
      (\<lambda>out.
        trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
          s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> (P + G) + N + S + F"
proof -
  have base_bound:
    "wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_sampled_base_opening_conflict s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> P + G"
    by (rule
        wp_trace_fri_header_tied_sampled_base_without_recorded_missing_bound_from_partial_merkle_and_gap
        [OF merkle_bound alignment_gap_bound])
  have "wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
          s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> wp_event verify_monad
        (\<lambda>out.
          (trace_fri_header_tied_sampled_base_opening_conflict s out \<and>
            \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) \<or>
          trace_fri_header_tied_sampled_next_value_conflict s out \<or>
          trace_fri_header_tied_sampled_successor_opening_conflict s out \<or>
          trace_fri_header_tied_sampled_final_value_conflict s out) s"
    by (rule wp_event_mono)
      (auto dest: trace_fri_header_tied_without_same_imp_branch)
  also have "... \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_sampled_base_opening_conflict s out \<and>
          \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s +
      wp_event verify_monad
        (trace_fri_header_tied_sampled_next_value_conflict s) s +
      wp_event verify_monad
        (trace_fri_header_tied_sampled_successor_opening_conflict s) s +
      wp_event verify_monad
        (trace_fri_header_tied_sampled_final_value_conflict s) s"
    by (rule wp_event_union_bound4)
  also have "... \<le> (P + G) + N + S + F"
    by (intro add_mono base_bound
        wp_trace_fri_header_tied_sampled_next_value_bound_from_replay_gap
        [OF next_gap_bound]
        wp_trace_fri_header_tied_sampled_successor_bound_from_replay_gap
        [OF successor_gap_bound]
        wp_trace_fri_header_tied_sampled_final_value_bound_from_replay_gap
        [OF final_gap_bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_authenticated_conflict_without_recorded_missing_bound_from_partial_merkle_and_replay_gaps:
  fixes P G N S F :: prob
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
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
      (\<lambda>out.
        trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
          s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> ((P + G) + N + S + F) + P"
proof -
  have without_bound:
    "wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
          s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> (P + G) + N + S + F"
    by (rule
        wp_trace_fri_header_tied_without_same_without_recorded_missing_bound_from_partial_merkle_and_replay_gaps
        [OF merkle_bound alignment_gap_bound next_gap_bound successor_gap_bound
          final_gap_bound])
  have "wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
          s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> wp_event verify_monad
        (\<lambda>out.
          (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
            s out \<and>
            \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) \<or>
          trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks
            s out) s"
    by (rule wp_event_mono)
      (auto dest:
        trace_fri_header_tied_authenticated_conflict_imp_without_same_or_same_layer)
  also have "... \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
            s out \<and>
          \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s +
      wp_event verify_monad
        (trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks s)
        s"
    by (rule wp_event_union_bound)
  also have "... \<le> ((P + G) + N + S + F) + P"
    by (intro add_mono without_bound
        wp_trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks_bound_from_partial_merkle
        [OF merkle_bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_sampled_assignment_conflict_without_recorded_missing_bound_from_auth_gap_and_replay_gaps:
  fixes A P G N S F :: prob
  assumes auth_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_assignment_auth_gap s) s \<le> A"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
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
      (\<lambda>out.
        trace_fri_header_tied_sampled_assignment_conflict s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> (((P + G) + N + S + F) + P) + A"
proof -
  have auth_bound:
    "wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
          s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> ((P + G) + N + S + F) + P"
    by (rule
        wp_trace_fri_header_tied_authenticated_conflict_without_recorded_missing_bound_from_partial_merkle_and_replay_gaps
        [OF merkle_bound alignment_gap_bound next_gap_bound successor_gap_bound
          final_gap_bound])
  have "wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_sampled_assignment_conflict s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> wp_event verify_monad
        (\<lambda>out.
          (trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
            s out \<and>
            \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) \<or>
          trace_fri_header_tied_assignment_auth_gap s out) s"
    by (rule wp_event_mono)
      (auto dest: trace_fri_header_tied_assignment_imp_authenticated_or_auth_gap)
  also have "... \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
            s out \<and>
          \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s +
      wp_event verify_monad
        (trace_fri_header_tied_assignment_auth_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> (((P + G) + N + S + F) + P) + A"
    by (intro add_mono auth_bound auth_gap_bound)
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_recorded_missing_and_complement:
  fixes Missing Complement :: prob
  assumes missing_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_recorded_sibling_candidate_missing s) s
      \<le> Missing"
    and complement_bound:
      "wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_sampled_assignment_conflict s out \<and>
          \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
        \<le> Complement"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s
      \<le> Missing + Complement"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_recorded_sibling_candidate_missing s out \<or>
          (trace_fri_header_tied_sampled_assignment_conflict s out \<and>
            \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out)) s"
    by (rule wp_event_mono) blast
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing s) s +
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_sampled_assignment_conflict s out \<and>
          \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s"
    by (rule wp_event_union_bound)
  also have "... \<le> Missing + Complement"
    by (intro add_mono missing_bound complement_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_header_tied_augmented_sampled_layer_chain_bound_from_fresh_and_prequery:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_augmented_sampled_layer_chain)
      adversary_initial_state \<le>
      Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_header_tied_sampled_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B cover envelope fresh_bound])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_augmented_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_sampled_layer_chain)
        adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono)
      (auto dest:
        trace_fri_bad_with_header_tied_augmented_sampled_layer_chain_imp_plain
        split: option.splits prod.splits)
  then show ?thesis
    by (rule order_trans[OF _ sampled])
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_augmented_and_unaugmented:
  assumes augmented_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_augmented_partial_candidate)
      adversary_initial_state \<le> Augmented"
    and unaugmented_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_unaugmented_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Unaugmented"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> Augmented + Unaugmented"
proof -
  have unaugmented_staged:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_unaugmented_partial_candidate)
      adversary_initial_state \<le> Unaugmented"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (auto simp: trace_fri_header_tied_unaugmented_partial_candidate_def
        unaugmented_bound)
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            trace_fri_bad_with_header_tied_augmented_partial_candidate out \<or>
          staged_security_with_data_state_verifier_event
            trace_fri_header_tied_unaugmented_partial_candidate out)
        adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto dest:
        trace_fri_bad_with_header_tied_partial_candidate_imp_augmented_or_unaugmented
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_augmented_partial_candidate)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_header_tied_unaugmented_partial_candidate)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> Augmented + Unaugmented"
    by (rule add_mono[OF augmented_bound unaugmented_staged])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_header_tied_unaugmented_partial_candidate_bound_from_recorded_missing_and_merkle:
  assumes merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Missing"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_unaugmented_partial_candidate)
      adversary_initial_state \<le> Missing + Merkle"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have head_neq:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap ?s) ?s \<le> Merkle"
    by (rule
        wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle)
      (rule merkle_bound[OF support])
  have head_mismatch:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_mismatch_gap ?s) ?s \<le> Merkle"
    by (rule
        wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap
        [OF head_neq])
  have alignment:
    "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap ?s) ?s \<le> Merkle"
    by (rule
        wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap
        [OF head_mismatch])
  show
    "wp_event verify_monad
      (trace_fri_header_tied_unaugmented_partial_candidate ?s) ?s
      \<le> Missing + Merkle"
    by (rule
        wp_trace_fri_header_tied_unaugmented_partial_candidate_bound_from_recorded_missing_and_base_gap)
      (rule missing_bound[OF support], rule alignment)
next
  fix s
  show "\<not> trace_fri_header_tied_unaugmented_partial_candidate s None"
    unfolding trace_fri_header_tied_unaugmented_partial_candidate_def
      trace_fri_bad_with_header_tied_partial_candidate_def
      accepted_fri_opening_transcript_def
    by simp
qed

lemma trace_fri_header_tied_reduction_from_augmented_and_recorded_missing_bounds:
  fixes Augmented Missing Merkle :: prob
  assumes augmented_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_partial_candidate s) s
      \<le> Augmented"
    and missing_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing s) s
      \<le> Missing"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s
      \<le> Merkle"
    and total_bound:
      "Augmented + (Missing + Merkle) \<le> trace_fri_error"
  shows "trace_fri_header_tied_reduction s"
proof -
  have head_neq:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap s) s \<le> Merkle"
    by (rule
        wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle)
      (rule merkle_bound)
  have head_mismatch:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_mismatch_gap s) s
      \<le> Merkle"
    by (rule
        wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap
        [OF head_neq])
  have alignment:
    "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap s) s \<le> Merkle"
    by (rule
        wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap
        [OF head_mismatch])
  have unaugmented:
    "wp_event verify_monad
      (trace_fri_header_tied_unaugmented_partial_candidate s) s
      \<le> Missing + Merkle"
    by (rule
        wp_trace_fri_header_tied_unaugmented_partial_candidate_bound_from_recorded_missing_and_base_gap)
      (rule missing_bound, rule alignment)
  have partial:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> Augmented + (Missing + Merkle)"
    by (rule
        wp_trace_fri_header_tied_partial_candidate_bound_from_augmented_and_unaugmented)
      (rule augmented_bound, rule unaugmented)
  show ?thesis
    unfolding trace_fri_header_tied_reduction_def
    by (rule order_trans[OF partial total_bound])
qed

lemma active_trace_fri_header_tied_reductions_from_augmented_and_recorded_missing_bounds:
  fixes Augmented Missing Merkle ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes augmented_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_augmented_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Augmented data attacker_state"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Missing data attacker_state"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle data attacker_state"
    and total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Augmented data attacker_state +
        (Missing data attacker_state + Merkle data attacker_state)
      \<le> trace_fri_error"
    and support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  shows
    "trace_fri_header_tied_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
  by (rule
      trace_fri_header_tied_reduction_from_augmented_and_recorded_missing_bounds)
    (rule augmented_bound[OF support], rule missing_bound[OF support],
      rule merkle_bound[OF support], rule total_bound[OF support])

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_without_same_residuals:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and structural_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Structural"
    and zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Zero"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      (Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (((((Merkle + Structural) + Merkle) + (Merkle + 0) + (Merkle + 0) +
        (Merkle + 0 + 0)) + Merkle) + 0 + Zero)"
proof (rule
    checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_and_residual_gaps
    [OF wf controlled finite_B cover envelope fresh_bound])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap ?s) ?s
      \<le> 0"
    by (rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
  show "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> Merkle"
    by (rule merkle_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap ?s) ?s
      \<le> Structural"
    by (rule structural_bound[OF support])
  have head_neq:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap ?s) ?s \<le> Merkle"
    by (rule
        wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle)
      (rule merkle_bound[OF support])
  have head_mismatch:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_mismatch_gap ?s) ?s
      \<le> Merkle"
    by (rule
        wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap
        [OF head_neq])
  show "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap ?s) ?s \<le> Merkle"
    by (rule
        wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap
        [OF head_mismatch])
  show "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap ?s) ?s \<le> Merkle + 0"
    by (rule
        wp_trace_fri_header_tied_next_value_replay_gap_bound_from_merkle_and_slot)
      (rule merkle_bound[OF support],
       rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
  show "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap ?s) ?s \<le> Merkle + 0"
    by (rule
        wp_trace_fri_header_tied_successor_replay_gap_bound_from_merkle_and_slot)
      (rule merkle_bound[OF support],
       rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
  show "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap ?s) ?s
      \<le> Merkle + 0 + 0"
    by (rule
        wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
      (rule merkle_bound[OF support],
       rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero,
       rule wp_trace_fri_header_tied_final_value_selected_step_missing_gap_zero)
  show "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction ?s) ?s \<le> Zero"
    by (rule zero_bound[OF support])
qed

lemma checked_staged_security_trace_fri_header_tied_zero_round_bound_from_staged_checked_and_merkle:
  assumes checked_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le> CheckedZero"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> CheckedZero + Merkle"
proof -
  have merkle_staged:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le> Merkle"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (auto simp: partial_merkle_inconsistency_bad_def merkle_bound)
  have split:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_verifier_event
          trace_fri_zero_round_checked_final_obstruction out \<or>
        staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad out)
      adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto dest:
        trace_fri_header_tied_zero_round_final_obstruction_imp_checked_or_merkle
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_zero_round_checked_final_obstruction)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> CheckedZero + Merkle"
    by (intro add_mono checked_bound merkle_staged)
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_staged_checked_zero_and_without_same_residuals:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and structural_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Structural"
    and checked_zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le> CheckedZero"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      (Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (((((Merkle + Structural) + Merkle) + (Merkle + 0) + (Merkle + 0) +
        (Merkle + 0 + 0)) + Merkle) + 0 + (CheckedZero + Merkle))"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_header_tied_sampled_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B cover envelope fresh_bound])
  have conflict:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_sampled_assignment_conflict)
      adversary_initial_state \<le>
      (((((Merkle + Structural) + Merkle) + (Merkle + 0) +
        (Merkle + 0) + (Merkle + 0 + 0)) + Merkle) + 0)"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    fix data attacker_state
    assume support:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    have head_neq:
      "wp_event verify_monad
        (trace_fri_header_tied_base_head_value_neq_gap ?s) ?s \<le> Merkle"
      by (rule
          wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle)
        (rule merkle_bound[OF support])
    have head_mismatch:
      "wp_event verify_monad
        (trace_fri_header_tied_base_head_value_mismatch_gap ?s) ?s
        \<le> Merkle"
      by (rule
          wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap
          [OF head_neq])
    have alignment:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap ?s) ?s \<le> Merkle"
      by (rule
          wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap
          [OF head_mismatch])
    have next_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap ?s) ?s \<le> Merkle + 0"
      by (rule
          wp_trace_fri_header_tied_next_value_replay_gap_bound_from_merkle_and_slot)
        (rule merkle_bound[OF support],
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
    have successor:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap ?s) ?s \<le> Merkle + 0"
      by (rule
          wp_trace_fri_header_tied_successor_replay_gap_bound_from_merkle_and_slot)
        (rule merkle_bound[OF support],
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
    have final:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap ?s) ?s
        \<le> Merkle + 0 + 0"
      by (rule
          wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
        (rule merkle_bound[OF support],
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero,
         rule wp_trace_fri_header_tied_final_value_selected_step_missing_gap_zero)
    show "wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict ?s) ?s
        \<le> (((((Merkle + Structural) + Merkle) + (Merkle + 0) +
          (Merkle + 0) + (Merkle + 0 + 0)) + Merkle) + 0)"
      by (rule
          wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_slot_recorded_chunk_gap_and_residuals)
        (rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero,
         rule merkle_bound[OF support],
         rule structural_bound[OF support],
         rule alignment, rule next_bound, rule successor, rule final)
  next
    fix s
    show "\<not> trace_fri_header_tied_sampled_assignment_conflict s None"
      unfolding trace_fri_header_tied_sampled_assignment_conflict_def
        accepted_fri_opening_transcript_def
      by simp
  qed
  have zero:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> CheckedZero + Merkle"
    by (rule
        checked_staged_security_trace_fri_header_tied_zero_round_bound_from_staged_checked_and_merkle)
      (rule checked_zero_bound, rule merkle_bound)
  show ?thesis
    by (rule
        checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_sampled_conflict_and_staged_zero
        [OF sampled conflict zero])
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_staged_checked_zero_and_recorded_sibling_missing:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Missing"
    and checked_zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le> CheckedZero"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      (Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (((((Merkle + Missing) + Merkle) + (Merkle + 0) + (Merkle + 0) +
        (Merkle + 0 + 0)) + Merkle) + 0 + (CheckedZero + Merkle))"
proof (rule
    checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_staged_checked_zero_and_without_same_residuals
    [OF wf controlled finite_B cover envelope fresh_bound merkle_bound _ checked_zero_bound])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap ?s) ?s
      \<le> Missing"
    by (rule
        wp_trace_fri_header_tied_sibling_structural_gap_bound_from_recorded_sibling_missing)
      (rule missing_bound[OF support])
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_staged_checked_zero_and_recorded_sibling_missing_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Missing"
    and checked_zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le> CheckedZero"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      (Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      ((Missing +
        ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
          (Merkle + 0 + 0)) + Merkle) + 0)) +
        (CheckedZero + Merkle))"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_header_tied_sampled_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B cover envelope fresh_bound])
  have conflict:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_sampled_assignment_conflict)
      adversary_initial_state \<le>
      Missing +
        ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
          (Merkle + 0 + 0)) + Merkle) + 0)"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    fix data attacker_state
    assume support:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    have head_neq:
      "wp_event verify_monad
        (trace_fri_header_tied_base_head_value_neq_gap ?s) ?s \<le> Merkle"
      by (rule
          wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle)
        (rule merkle_bound[OF support])
    have head_mismatch:
      "wp_event verify_monad
        (trace_fri_header_tied_base_head_value_mismatch_gap ?s) ?s
        \<le> Merkle"
      by (rule
          wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap
          [OF head_neq])
    have alignment:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap ?s) ?s \<le> Merkle"
      by (rule
          wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap
          [OF head_mismatch])
    have next_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap ?s) ?s \<le> Merkle + 0"
      by (rule
          wp_trace_fri_header_tied_next_value_replay_gap_bound_from_merkle_and_slot)
        (rule merkle_bound[OF support],
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
    have successor:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap ?s) ?s \<le> Merkle + 0"
      by (rule
          wp_trace_fri_header_tied_successor_replay_gap_bound_from_merkle_and_slot)
        (rule merkle_bound[OF support],
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
    have final:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap ?s) ?s
        \<le> Merkle + 0 + 0"
      by (rule
          wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
        (rule merkle_bound[OF support],
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero,
         rule wp_trace_fri_header_tied_final_value_selected_step_missing_gap_zero)
    have slot:
      "wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap ?s) ?s
        \<le> 0"
      by (rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
    have authenticated_recorded_auth:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap ?s)
        ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap_bound_from_slot_recorded_chunk_gap
          [OF slot])
    have recorded_auth:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_recorded_auth_gap ?s) ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_same_layer_recorded_auth_gap_bound_from_authenticated_recorded_auth_gap
          [OF authenticated_recorded_auth])
    have same_auth:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_auth_gap ?s) ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_same_layer_auth_gap_bound_from_recorded_auth_gap
          [OF recorded_auth])
    have auth_gap:
      "wp_event verify_monad
        (trace_fri_header_tied_assignment_auth_gap ?s) ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_assignment_auth_gap_bound_from_same_layer_auth_gap
          [OF same_auth])
    have complement:
      "wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_sampled_assignment_conflict ?s out \<and>
          \<not> trace_fri_header_tied_recorded_sibling_candidate_missing ?s out)
        ?s \<le>
        ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
          (Merkle + 0 + 0)) + Merkle) + 0)"
      by (rule
          wp_trace_fri_header_tied_sampled_assignment_conflict_without_recorded_missing_bound_from_auth_gap_and_replay_gaps)
        (rule auth_gap, rule merkle_bound[OF support], rule alignment,
         rule next_bound, rule successor, rule final)
    show "wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict ?s) ?s
        \<le> Missing +
          ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
            (Merkle + 0 + 0)) + Merkle) + 0)"
      by (rule
          wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_recorded_missing_and_complement)
        (rule missing_bound[OF support], rule complement)
  next
    fix s
    show "\<not> trace_fri_header_tied_sampled_assignment_conflict s None"
      unfolding trace_fri_header_tied_sampled_assignment_conflict_def
        accepted_fri_opening_transcript_def
      by simp
  qed
  have zero:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> CheckedZero + Merkle"
    by (rule
        checked_staged_security_trace_fri_header_tied_zero_round_bound_from_staged_checked_and_merkle)
      (rule checked_zero_bound, rule merkle_bound)
  show ?thesis
    by (rule
        checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_sampled_conflict_and_staged_zero
        [OF sampled conflict zero])
qed

lemma checked_staged_security_trace_fri_header_tied_augmented_partial_candidate_bound_from_fresh_prequery_staged_checked_zero_and_recorded_sibling_missing_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Missing"
    and checked_zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le> CheckedZero"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_augmented_partial_candidate)
      adversary_initial_state \<le>
      (Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      ((Missing +
        ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
          (Merkle + 0 + 0)) + Merkle) + 0)) +
        (CheckedZero + Merkle))"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_augmented_sampled_layer_chain)
      adversary_initial_state \<le>
      Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_header_tied_augmented_sampled_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B cover envelope fresh_bound])
  have conflict:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_sampled_assignment_conflict)
      adversary_initial_state \<le>
      Missing +
        ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
          (Merkle + 0 + 0)) + Merkle) + 0)"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    fix data attacker_state
    assume support:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    have head_neq:
      "wp_event verify_monad
        (trace_fri_header_tied_base_head_value_neq_gap ?s) ?s \<le> Merkle"
      by (rule
          wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle)
        (rule merkle_bound[OF support])
    have head_mismatch:
      "wp_event verify_monad
        (trace_fri_header_tied_base_head_value_mismatch_gap ?s) ?s
        \<le> Merkle"
      by (rule
          wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap
          [OF head_neq])
    have alignment:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap ?s) ?s \<le> Merkle"
      by (rule
          wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap
          [OF head_mismatch])
    have next_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap ?s) ?s \<le> Merkle + 0"
      by (rule
          wp_trace_fri_header_tied_next_value_replay_gap_bound_from_merkle_and_slot)
        (rule merkle_bound[OF support],
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
    have successor:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap ?s) ?s \<le> Merkle + 0"
      by (rule
          wp_trace_fri_header_tied_successor_replay_gap_bound_from_merkle_and_slot)
        (rule merkle_bound[OF support],
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
    have final:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap ?s) ?s
        \<le> Merkle + 0 + 0"
      by (rule
          wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
        (rule merkle_bound[OF support],
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero,
         rule wp_trace_fri_header_tied_final_value_selected_step_missing_gap_zero)
    have slot:
      "wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap ?s) ?s
        \<le> 0"
      by (rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
    have authenticated_recorded_auth:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap ?s)
        ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap_bound_from_slot_recorded_chunk_gap
          [OF slot])
    have recorded_auth:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_recorded_auth_gap ?s) ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_same_layer_recorded_auth_gap_bound_from_authenticated_recorded_auth_gap
          [OF authenticated_recorded_auth])
    have same_auth:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_auth_gap ?s) ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_same_layer_auth_gap_bound_from_recorded_auth_gap
          [OF recorded_auth])
    have auth_gap:
      "wp_event verify_monad
        (trace_fri_header_tied_assignment_auth_gap ?s) ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_assignment_auth_gap_bound_from_same_layer_auth_gap
          [OF same_auth])
    have complement:
      "wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_sampled_assignment_conflict ?s out \<and>
          \<not> trace_fri_header_tied_recorded_sibling_candidate_missing ?s out)
        ?s \<le>
        ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
          (Merkle + 0 + 0)) + Merkle) + 0)"
      by (rule
          wp_trace_fri_header_tied_sampled_assignment_conflict_without_recorded_missing_bound_from_auth_gap_and_replay_gaps)
        (rule auth_gap, rule merkle_bound[OF support], rule alignment,
         rule next_bound, rule successor, rule final)
    show "wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict ?s) ?s
        \<le> Missing +
          ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
            (Merkle + 0 + 0)) + Merkle) + 0)"
      by (rule
          wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_recorded_missing_and_complement)
        (rule missing_bound[OF support], rule complement)
  next
    fix s
    show "\<not> trace_fri_header_tied_sampled_assignment_conflict s None"
      unfolding trace_fri_header_tied_sampled_assignment_conflict_def
        accepted_fri_opening_transcript_def
      by simp
  qed
  have zero:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> CheckedZero + Merkle"
    by (rule
        checked_staged_security_trace_fri_header_tied_zero_round_bound_from_staged_checked_and_merkle)
      (rule checked_zero_bound, rule merkle_bound)
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_augmented_partial_candidate)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            trace_fri_bad_with_header_tied_augmented_sampled_layer_chain out \<or>
          staged_security_with_data_state_verifier_event
            trace_fri_header_tied_sampled_assignment_conflict out \<or>
          staged_security_with_data_state_verifier_event
            trace_fri_header_tied_zero_round_final_obstruction out)
        adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto dest:
        trace_fri_header_tied_augmented_partial_candidate_imp_sampled_conflict_or_zero
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_augmented_sampled_layer_chain)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            trace_fri_header_tied_sampled_assignment_conflict out \<or>
          staged_security_with_data_state_verifier_event
            trace_fri_header_tied_zero_round_final_obstruction out)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_augmented_sampled_layer_chain)
        adversary_initial_state +
      (wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_header_tied_sampled_assignment_conflict)
        adversary_initial_state +
       wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_header_tied_zero_round_final_obstruction)
        adversary_initial_state)"
    by (intro add_mono order_refl wp_event_union_bound)
  also have "... \<le>
      (Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      ((Missing +
        ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
          (Merkle + 0 + 0)) + Merkle) + 0)) +
        (CheckedZero + Merkle))"
    by (intro add_mono sampled conflict zero)
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_augmented_route_and_unaugmented_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Missing"
    and checked_zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le> CheckedZero"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      ((Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      ((Missing +
        ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
          (Merkle + 0 + 0)) + Merkle) + 0)) +
        (CheckedZero + Merkle))) +
      (Missing + Merkle)"
proof -
  have augmented:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_augmented_partial_candidate)
      adversary_initial_state \<le>
      (Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      ((Missing +
        ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
          (Merkle + 0 + 0)) + Merkle) + 0)) +
        (CheckedZero + Merkle))"
    by (rule
        checked_staged_security_trace_fri_header_tied_augmented_partial_candidate_bound_from_fresh_prequery_staged_checked_zero_and_recorded_sibling_missing_split
        [OF wf controlled finite_B cover envelope fresh_bound merkle_bound
          missing_bound checked_zero_bound])
  have unaugmented:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_unaugmented_partial_candidate)
      adversary_initial_state \<le> Missing + Merkle"
    by (rule
        checked_staged_security_trace_fri_header_tied_unaugmented_partial_candidate_bound_from_recorded_missing_and_merkle)
      (erule merkle_bound, erule missing_bound)
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            trace_fri_bad_with_header_tied_augmented_partial_candidate out \<or>
          staged_security_with_data_state_verifier_event
            trace_fri_header_tied_unaugmented_partial_candidate out)
        adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto dest:
        trace_fri_bad_with_header_tied_partial_candidate_imp_augmented_or_unaugmented
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_augmented_partial_candidate)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_header_tied_unaugmented_partial_candidate)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      ((Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      ((Missing +
        ((((Merkle + Merkle) + (Merkle + 0) + (Merkle + 0) +
          (Merkle + 0 + 0)) + Merkle) + 0)) +
        (CheckedZero + Merkle))) +
      (Missing + Merkle)"
    by (rule add_mono[OF augmented unaugmented])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_checked_zero_and_without_same_residuals:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and structural_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Structural"
    and checked_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_checked_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> CheckedZero"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      (Fresh +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (((((Merkle + Structural) + Merkle) + (Merkle + 0) + (Merkle + 0) +
        (Merkle + 0 + 0)) + Merkle) + 0 + (CheckedZero + Merkle))"
proof (rule
    checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_without_same_residuals
    [OF wf controlled finite_B cover envelope fresh_bound merkle_bound
      structural_bound])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le> CheckedZero + Merkle"
    by (rule wp_trace_fri_header_tied_zero_round_bound_from_checked_and_merkle)
      (rule checked_zero_bound[OF support],
       rule merkle_bound[OF support])
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_without_same_residuals:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets bad dg composition_table
        \<subseteq> B dg"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_recorded_base_chunk_auth_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Missing"
    and without_same_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> WithoutSame"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      (Fresh +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (((Merkle + Missing) + (Merkle + 0) + (Merkle + 0) + WithoutSame +
        Merkle) + 0 + 0)"
proof (rule
    checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_and_residual_gaps
    [OF wf controlled finite_B cover envelope fresh_bound])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap ?s)
      ?s \<le> 0"
    by (rule
        wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
  show "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> Merkle"
    by (rule merkle_bound[OF support])
  show "wp_event verify_monad
      (composition_fri_verifier_tied_recorded_base_chunk_auth_missing ?s) ?s
      \<le> Missing"
    by (rule missing_bound[OF support])
  show "wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap ?s) ?s
      \<le> Merkle + 0"
    by (rule
        wp_composition_fri_verifier_tied_next_value_replay_gap_bound_from_merkle_and_slot)
      (rule merkle_bound[OF support],
       rule
        wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
  show "wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap ?s) ?s
      \<le> Merkle + 0"
    by (rule
        wp_composition_fri_verifier_tied_successor_replay_gap_bound_from_merkle_and_slot)
      (rule merkle_bound[OF support],
       rule
        wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
  show "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap ?s) ?s
      \<le> WithoutSame"
    by (rule
        wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_without_same)
      (rule without_same_bound[OF support])
  show "wp_event verify_monad
      (composition_fri_verifier_tied_zero_round_final_obstruction ?s) ?s
      \<le> 0"
    by (subst wp_composition_fri_verifier_tied_zero_round_final_obstruction_zero)
      simp
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_without_missing_or_same_residuals:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets bad dg composition_table
        \<subseteq> B dg"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and without_same_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> WithoutSame"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      (Fresh +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (((Merkle + 0) + (Merkle + 0) + (Merkle + 0) + WithoutSame +
        Merkle) + 0 + 0)"
proof (rule
    checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_without_same_residuals
    [where Missing = 0])
  show "staged_budget_wellformed budgets"
    by (rule wf)
  show "staged_adversary_controlled budgets A"
    by (rule controlled)
  show "\<And>dg. finite (B dg)"
    by (rule finite_B)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      composition_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    by (rule cover)
  show "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets bad dg composition_table
      \<subseteq> B dg"
    by (rule envelope)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    by (rule fresh_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    by (rule merkle_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_recorded_base_chunk_auth_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> 0"
    by (subst wp_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_zero)
      simp
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> WithoutSame"
    by (rule without_same_bound)
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_zero_slot_missing_and_replay_gaps:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets bad dg composition_table
        \<subseteq> B dg"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Next"
    and successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Successor"
    and final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Final"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      (Fresh +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (((Merkle + 0) + Next + Successor + Final + Merkle) + 0 + 0)"
proof (rule
    checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_and_residual_gaps
    [where Slot = 0 and Missing = 0 and Zero = 0])
  show "staged_budget_wellformed budgets"
    by (rule wf)
  show "staged_adversary_controlled budgets A"
    by (rule controlled)
  show "\<And>dg. finite (B dg)"
    by (rule finite_B)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      composition_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    by (rule cover)
  show "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets bad dg composition_table
      \<subseteq> B dg"
    by (rule envelope)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    by (rule fresh_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> 0"
    by (rule
        wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    by (rule merkle_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_recorded_base_chunk_auth_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> 0"
    by (subst wp_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_zero)
      simp
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Next"
    by (rule next_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Successor"
    by (rule successor_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Final"
    by (rule final_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> 0"
    by (subst wp_composition_fri_verifier_tied_zero_round_final_obstruction_zero)
      simp
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_zero_slot_missing_selected_final_and_replay_gaps:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets bad dg composition_table
        \<subseteq> B dg"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      (Fresh +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (((Merkle + 0) + (Merkle + 0) + (Merkle + 0) + (Merkle + 0 + 0) +
        Merkle) + 0 + 0)"
proof (rule
    checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_zero_slot_missing_and_replay_gaps)
  show "staged_budget_wellformed budgets"
    by (rule wf)
  show "staged_adversary_controlled budgets A"
    by (rule controlled)
  show "\<And>dg. finite (B dg)"
    by (rule finite_B)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      composition_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    by (rule cover)
  show "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets bad dg composition_table
      \<subseteq> B dg"
    by (rule envelope)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> Fresh"
    by (rule fresh_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    by (rule merkle_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle + 0"
  proof -
    fix data attacker_state
    assume support:
      "Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    show "wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap ?s) ?s
        \<le> Merkle + 0"
      by (rule
          wp_composition_fri_verifier_tied_next_value_replay_gap_bound_from_merkle_and_slot)
        (rule merkle_bound[OF support],
         rule
          wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
  qed
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle + 0"
  proof -
    fix data attacker_state
    assume support:
      "Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    show "wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap ?s) ?s
        \<le> Merkle + 0"
      by (rule
          wp_composition_fri_verifier_tied_successor_replay_gap_bound_from_merkle_and_slot)
        (rule merkle_bound[OF support],
         rule
          wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
  qed
  show "\<And>data attacker_state.
      Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle + 0 + 0"
  proof -
    fix data attacker_state
    assume support:
      "Some (data, attacker_state)
      \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    show "wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap ?s) ?s
        \<le> Merkle + 0 + 0"
      by (rule
          wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
        (rule merkle_bound[OF support],
         rule
          wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero,
         rule
          wp_composition_fri_verifier_tied_final_value_selected_step_missing_gap_zero)
  qed
qed

lemma active_composition_fri_verifier_tied_reductions_from_sampled_and_merkle_bounds:
  fixes Sampled Merkle ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_bad_with_verifier_tied_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Sampled data attacker_state"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle data attacker_state"
    and total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Sampled data attacker_state +
        (((Merkle data attacker_state + 0) +
          (Merkle data attacker_state + 0) +
          (Merkle data attacker_state + 0) +
          (Merkle data attacker_state + 0 + 0) +
          Merkle data attacker_state) + 0)
      \<le> composition_fri_error"
    and support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  shows
    "composition_fri_verifier_tied_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have slot:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
        ?s) ?s \<le> 0"
    by (rule
        wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
  have next_gap:
    "wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap ?s) ?s
      \<le> Merkle data attacker_state + 0"
    by (rule
        wp_composition_fri_verifier_tied_next_value_replay_gap_bound_from_merkle_and_slot)
      (rule merkle_bound[OF support], rule slot)
  have successor:
    "wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap ?s) ?s
      \<le> Merkle data attacker_state + 0"
    by (rule
        wp_composition_fri_verifier_tied_successor_replay_gap_bound_from_merkle_and_slot)
      (rule merkle_bound[OF support], rule slot)
  have final:
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap ?s) ?s
      \<le> Merkle data attacker_state + 0 + 0"
    by (rule
        wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
      (rule merkle_bound[OF support], rule slot,
       rule
        wp_composition_fri_verifier_tied_final_value_selected_step_missing_gap_zero)
  show ?thesis
    by (rule
        composition_fri_verifier_tied_reduction_from_residual_bounds_with_recorded_missing_zero
        [OF sampled_bound[OF support] slot merkle_bound[OF support]
          next_gap successor final total_bound[OF support]])
qed

end

end
