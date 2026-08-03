(*  Title:      Stark/Soundness_FRI_Staged_Active_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Staged_Active_Bounds
  imports Soundness_FRI_Prequery_Composition_Sampled_Bounds
begin

text \<open>
  Staged integration lemmas for the active FRI route.

  The prequery accounting layer proves whole checked-security-experiment
  bounds for sampled FRI layer-chain events.  The active route still reasons
  about partial-candidate FRI events.  This layer bridges those levels by
  splitting a partial-candidate FRI bad event into the sampled layer-chain case
  and the remaining missing-sampled-chain residual.
\<close>

context soundness
begin

lemma trace_fri_header_tied_partial_candidate_imp_sampled_conflict_or_zero:
  assumes bad: "trace_fri_bad_with_header_tied_partial_candidate s out"
  shows
    "trace_fri_bad_with_header_tied_sampled_layer_chain s out \<or>
     trace_fri_header_tied_sampled_assignment_conflict s out \<or>
     trace_fri_header_tied_zero_round_final_obstruction s out"
proof (cases "trace_fri_bad_with_header_tied_sampled_layer_chain s out")
  case True
  then show ?thesis by blast
next
  case False
  have missing: "trace_fri_header_tied_missing_sampled_layer_chain s out"
    unfolding trace_fri_header_tied_missing_sampled_layer_chain_def
    using bad False by blast
  have obstruction:
    "trace_fri_header_tied_sampled_layer_assignment_obstruction s out"
    by (rule trace_fri_header_tied_missing_sampled_imp_assignment_obstruction
        [OF missing])
  then show ?thesis
    using trace_fri_header_tied_assignment_obstruction_imp_conflict_or_zero
    by blast
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_sampled_and_missing:
  assumes sampled_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state \<le> R"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> R + M"
proof -
  have missing_staged:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_missing_sampled_layer_chain)
      adversary_initial_state \<le> M"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (auto simp: trace_fri_header_tied_missing_sampled_layer_chain_def
        missing_bound)
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            trace_fri_bad_with_header_tied_sampled_layer_chain out \<or>
          staged_security_with_data_state_verifier_event
            trace_fri_header_tied_missing_sampled_layer_chain out)
        adversary_initial_state"
    unfolding trace_fri_header_tied_missing_sampled_layer_chain_def
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_sampled_layer_chain)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_header_tied_missing_sampled_layer_chain)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (rule add_mono[OF sampled_bound missing_staged])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_sampled_conflict_and_staged_zero:
  assumes sampled_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state \<le> R"
    and conflict_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_sampled_assignment_conflict)
      adversary_initial_state \<le> C"
    and zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> R + (C + Z)"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?sampled =
    "staged_security_with_data_state_verifier_event
      trace_fri_bad_with_header_tied_sampled_layer_chain"
  let ?conflict =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_sampled_assignment_conflict"
  let ?zero =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_zero_round_final_obstruction"
  have split:
    "wp_event ?M
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?sampled out \<or> ?conflict out \<or> ?zero out)
      adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto dest:
        trace_fri_header_tied_partial_candidate_imp_sampled_conflict_or_zero
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?sampled adversary_initial_state +
      wp_event ?M (\<lambda>out. ?conflict out \<or> ?zero out)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      wp_event ?M ?sampled adversary_initial_state +
      (wp_event ?M ?conflict adversary_initial_state +
       wp_event ?M ?zero adversary_initial_state)"
    by (intro add_mono order_refl wp_event_union_bound)
  also have "... \<le> R + (C + Z)"
    by (intro add_mono sampled_bound conflict_bound zero_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_and_missing:
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
      adversary_initial_state \<le> F"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) + M"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_header_tied_sampled_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B cover envelope fresh_bound])
  show ?thesis
    by (rule
        checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_sampled_and_missing
        [OF sampled missing_bound])
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_and_assignment_obstruction:
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
      adversary_initial_state \<le> F"
    and assignment_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_layer_assignment_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) + M"
proof (rule
    checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_and_missing
    [OF wf controlled finite_B cover envelope fresh_bound])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
    (trace_fri_header_tied_missing_sampled_layer_chain
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)))
    (verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)) \<le> M"
    by (rule wp_trace_fri_header_tied_missing_sampled_bound_from_assignment_obstruction)
      (rule assignment_bound[OF support])
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_conflict_and_staged_zero:
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
      adversary_initial_state \<le> F"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
    and zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) + (C + Z)"
proof (rule
    checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_sampled_conflict_and_staged_zero)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_header_tied_sampled_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B cover envelope fresh_bound])
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_sampled_assignment_conflict)
      adversary_initial_state \<le> C"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (simp_all add: conflict_bound
        trace_fri_header_tied_sampled_assignment_conflict_def
        accepted_fri_opening_transcript_def)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> Z"
    by (rule zero_bound)
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_conflict_and_zero:
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
      adversary_initial_state \<le> F"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
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
          (staged_proof_transcript data)) \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) + (C + Z)"
proof (rule
    checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_and_assignment_obstruction
    [OF wf controlled finite_B cover envelope fresh_bound])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
    (trace_fri_header_tied_sampled_layer_assignment_obstruction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)))
    (verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)) \<le> C + Z"
    by (rule
        wp_trace_fri_header_tied_assignment_obstruction_bound_from_conflict_and_zero)
      (rule conflict_bound[OF support], rule zero_bound[OF support])
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_and_residual_gaps:
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
    and slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Slot"
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
    and alignment_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Align"
    and next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap
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
        (trace_fri_header_tied_successor_replay_gap
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
        (trace_fri_header_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Final"
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
      (((((Merkle + Structural) + Align) + Next + Successor + Final) +
        Merkle) + Slot + Zero)"
proof (rule
    checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_fresh_prequery_conflict_and_zero
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
    (trace_fri_header_tied_sampled_assignment_conflict ?s) ?s
    \<le> (((((Merkle + Structural) + Align) + Next + Successor + Final) +
        Merkle) + Slot)"
    by (rule
        wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_slot_recorded_chunk_gap_and_residuals)
      (rule slot_bound[OF support],
       rule merkle_bound[OF support],
       rule structural_bound[OF support],
       rule alignment_bound[OF support],
       rule next_bound[OF support],
       rule successor_bound[OF support],
       rule final_bound[OF support])
  show "wp_event verify_monad
    (trace_fri_header_tied_zero_round_final_obstruction ?s) ?s \<le> Zero"
    by (rule zero_bound[OF support])
qed

lemma checked_staged_security_trace_fri_empty_header_bound_from_sampled_and_missing:
  assumes sampled_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state \<le> R"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_reachable_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> R + M"
proof -
  have missing_staged:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_reachable_missing_sampled_layer_chain)
      adversary_initial_state \<le> M"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (simp add: trace_fri_reachable_missing_sampled_layer_chain_def
        trace_fri_bad_with_reachable_partial_candidate_def
        accepted_with_partial_trace_openings_def,
       rule missing_bound)
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            trace_fri_bad_with_sampled_layer_chain out \<or>
          staged_security_with_data_state_verifier_event
            trace_fri_reachable_missing_sampled_layer_chain out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest:
          trace_fri_bad_with_empty_composition_header_candidates_imp_reachable_partial_candidate
          trace_fri_reachable_imp_sampled_or_missing_layer_chain
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_sampled_layer_chain)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_reachable_missing_sampled_layer_chain)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (rule add_mono[OF sampled_bound missing_staged])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_empty_header_bound_from_fresh_prequery_and_missing:
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
      adversary_initial_state \<le> F"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_reachable_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) + M"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state \<le>
      F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_sampled_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B cover envelope fresh_bound])
  show ?thesis
    by (rule
        checked_staged_security_trace_fri_empty_header_bound_from_sampled_and_missing
        [OF sampled missing_bound])
qed

lemma checked_staged_security_trace_fri_empty_header_bound_from_fresh_prequery_and_assignment_obstruction:
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
      adversary_initial_state \<le> F"
    and assignment_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_layer_assignment_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) + M"
proof (rule
    checked_staged_security_trace_fri_empty_header_bound_from_fresh_prequery_and_missing
    [OF wf controlled finite_B cover envelope fresh_bound])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
    (trace_fri_reachable_missing_sampled_layer_chain
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)))
    (verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)) \<le> M"
    by (rule wp_trace_fri_reachable_missing_sampled_bound_from_assignment_obstruction)
      (rule assignment_bound[OF support])
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_sampled_and_missing:
  assumes sampled_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state \<le> R"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> R + M"
proof -
  have missing_staged:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_missing_sampled_layer_chain)
      adversary_initial_state \<le> M"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (auto simp: composition_fri_verifier_tied_missing_sampled_layer_chain_def
        missing_bound)
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            composition_fri_bad_with_verifier_tied_sampled_layer_chain out \<or>
          staged_security_with_data_state_verifier_event
            composition_fri_verifier_tied_missing_sampled_layer_chain out)
        adversary_initial_state"
    unfolding composition_fri_verifier_tied_missing_sampled_layer_chain_def
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_verifier_tied_sampled_layer_chain)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_verifier_tied_missing_sampled_layer_chain)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (rule add_mono[OF sampled_bound missing_staged])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_and_missing:
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
      adversary_initial_state \<le> F"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) + M"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_verifier_tied_sampled_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B cover envelope fresh_bound])
  show ?thesis
    by (rule
        checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_sampled_and_missing
        [OF sampled missing_bound])
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_and_assignment_obstruction:
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
      adversary_initial_state \<le> F"
    and assignment_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_layer_assignment_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) + M"
proof (rule
    checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_and_missing
    [OF wf controlled finite_B cover envelope fresh_bound])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
    (composition_fri_verifier_tied_missing_sampled_layer_chain
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)))
    (verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)) \<le> M"
    by (rule
        wp_composition_fri_verifier_tied_missing_sampled_bound_from_assignment_obstruction)
      (rule assignment_bound[OF support])
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_conflict_and_zero:
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
      adversary_initial_state \<le> F"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
    and zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) + (C + Z)"
proof (rule
    checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_and_assignment_obstruction
    [OF wf controlled finite_B cover envelope fresh_bound])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
    (composition_fri_verifier_tied_sampled_layer_assignment_obstruction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)))
    (verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)) \<le> C + Z"
    by (rule
        wp_composition_fri_verifier_tied_assignment_obstruction_bound_from_conflict_and_zero)
      (rule conflict_bound[OF support], rule zero_bound[OF support])
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_and_residual_gaps:
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
    and slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Slot"
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
    and zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Zero"
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
      (((Merkle + Missing) + Next + Successor + Final + Merkle) +
        Slot + Zero)"
proof (rule
    checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_conflict_and_zero
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
    (composition_fri_verifier_tied_sampled_assignment_conflict ?s) ?s
    \<le> ((Merkle + Missing) + Next + Successor + Final + Merkle) + Slot"
    by (rule
        wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_slot_recorded_chunk_gap_and_residuals)
      (rule slot_bound[OF support],
       rule merkle_bound[OF support],
       rule missing_bound[OF support],
       rule next_bound[OF support],
       rule successor_bound[OF support],
       rule final_bound[OF support])
  show "wp_event verify_monad
    (composition_fri_verifier_tied_zero_round_final_obstruction ?s) ?s \<le> Zero"
    by (rule zero_bound[OF support])
qed

end

end
