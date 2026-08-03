(*  Title:      Stark/Soundness_Relevant_Drift_Transcript_Public.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Relevant_Drift_Transcript_Public
  imports Soundness_Relevant_Drift_Transcript_Empty
begin

text \<open>
  Public-facing transcript-indexed packaging for the current relevant-drift
  proof route.  This layer keeps new wrappers out of the larger
  transcript-empty theory and avoids the diagnostic broad witnessed
  cross/Merkle route for the nonempty partial-candidate branch.
\<close>

context soundness
begin

lemma accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_or_empty_header_transcript:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  shows
    "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle
        s out \<or>
     soundness_bad_event_partial_candidate_empty_header_transcript s out"
proof (cases "composition_fri_roots = []")
  case False
  then have comp_nonempty: "composition_fri_roots \<noteq> []"
    by simp
  have
    "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle
      s out"
    by (rule
        accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_if_header_nonempty
        [OF false_statement supp acc header comp_nonempty])
  then show ?thesis by simp
next
  case True
  note comp_empty = True
  from acc obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  have header_empty:
    "verifier_header_transcript s fr f_fri_roots f_final as dg []
      final rest"
    using header comp_empty by simp
  from verify_monad_supplied_empty_header_partial_trace_openings
      [OF supp[unfolded out_eq] header_empty]
  obtain query_idxs trace_openings where shape:
      "accepted_transcript_shape s (Some (result, final_state)) as
        query_idxs"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    by blast
  show ?thesis
  proof (cases
      "partial_merkle_inconsistency_bad s (Some (result, final_state))")
    case True
    then have
      "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle
        s out"
      unfolding out_eq
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_def
      by simp
    then show ?thesis by simp
  next
    case False
    obtain trace_table where trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
      using accepted_with_partial_trace_openings_candidate_if_no_partial_merkle_bad
        [OF trace_partial False]
      by blast
    have accepted_out: "accepted (Some (result, final_state))"
      by (rule accepted_with_partial_trace_openings_imp_accepted
          [OF trace_partial])
    let ?composition_table = "replicate (scale * clength) final"
    have empty_partial:
      "accepted_with_empty_composition_header_candidates s
        (Some (result, final_state)) fr f_fri_roots f_final as dg final
        query_idxs trace_openings trace_table ?composition_table"
      unfolding accepted_with_empty_composition_header_candidates_def
      by (intro conjI exI[of _ rest])
        (use accepted_out header_empty trace_partial trace_candidate
          in simp_all)
    have "soundness_bad_event_partial_candidate_empty_header_transcript s
        (Some (result, final_state))"
      by (rule accepted_empty_composition_header_candidate_partition_transcript
          [OF false_statement empty_partial shape])
    then show ?thesis
      unfolding out_eq by simp
  qed
qed

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_and_empty_header_transcript_bounds:
  fixes partial_candidate_error empty_header_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and partial_candidate_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle)
        adversary_initial_state \<le> partial_candidate_error"
    and empty_header_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_partial_candidate_empty_header_transcript)
        adversary_initial_state \<le> empty_header_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    partial_candidate_error + empty_header_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?partial =
    "?E soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle"
  let ?empty = "?E soundness_bad_event_partial_candidate_empty_header_transcript"
  let ?bad = "\<lambda>out. ?partial out \<or> ?empty out"
  have accepted_bad:
    "wp_event ?M accepted adversary_initial_state \<le>
      wp_event ?M ?bad adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?M adversary_initial_state)"
      and acc: "accepted out"
    show "?bad out"
    proof (cases out)
      case None
      then show ?thesis
        using acc unfolding accepted_def by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      have verifier:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        using checked_staged_security_experiment_with_data_state_outcomeE
          [OF support[unfolded out_eq]]
        by blast
      have verifier_acc: "accepted (Some (result, final_state))"
        unfolding accepted_def by simp
      from verify_monad_accepted_transcript_shape[OF verifier]
      obtain alphas query_idxs where shape:
        "accepted_transcript_shape ?s (Some (result, final_state))
          alphas query_idxs"
        by blast
      from shape obtain result' final_state' fr f_fri_roots f_final dg
          composition_fri_roots final rest where
        header:
          "verifier_header_transcript ?s fr f_fri_roots f_final alphas dg
            composition_fri_roots final rest"
        by (elim accepted_transcript_shape_header_query_extraction)
      have local_bad:
        "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle
            ?s (Some (result, final_state)) \<or>
         soundness_bad_event_partial_candidate_empty_header_transcript ?s
            (Some (result, final_state))"
        by (rule
            accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_or_empty_header_transcript
            [OF false_statement verifier verifier_acc header])
      then show ?thesis
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
    qed
  qed
  have bad_bound:
    "wp_event ?M ?bad adversary_initial_state \<le>
      partial_candidate_error + empty_header_error"
  proof -
    have "wp_event ?M ?bad adversary_initial_state \<le>
        wp_event ?M ?partial adversary_initial_state +
        wp_event ?M ?empty adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le> partial_candidate_error + empty_header_error"
      by (intro add_mono partial_candidate_bound empty_header_bound)
    finally show ?thesis .
  qed
  have staged_bound:
    "wp_event (checked_staged_security_experiment A) accepted
      adversary_initial_state \<le>
      partial_candidate_error + empty_header_error"
    unfolding checked_staged_security_experiment_acceptance_with_data_state
    by (rule order_trans[OF accepted_bad bad_bound])
  show ?thesis
  proof -
    have
      "wp_event (checked_staged_security_experiment A)
        (\<lambda>out. \<not> Option.is_none out) adversary_initial_state =
       wp_event (checked_staged_security_experiment A) accepted
        adversary_initial_state"
      unfolding wp_event_def accepted_def
      by (rule arg_cong[where
        f="\<lambda>Q. wp (checked_staged_security_experiment A) Q
          adversary_initial_state"])
        (rule ext, simp)
    then show ?thesis
      unfolding checked_staged_adversary_acceptance_probability_def
      using staged_bound by simp
  qed
qed

theorem stark_soundness_from_transcript_indexed_partial_opening_route:
  fixes F empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and fixed_empty_alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (F + (trace_fri_error +
        low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  have merkle_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_aligned_partial_candidate_randomization_bound_from_query_prefix_current_rounds
        [OF wf controlled round_bound])
  have trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_partial_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have comp_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> composition_fri_error"
    by (rule
        composition_fri_bad_with_partial_candidates_bound_from_reachable_reduction
        [OF composition_fri_reduction])
  have current_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds
        [OF round_bound wf controlled])
  have query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_current_partial_opening_hit
          current_query_bound])
      (use wf controlled in simp_all)
  have partial_candidate_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds. C i) + trace_fri_error + composition_fri_error +
      (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_partial_candidate_aligned_randomization_with_merkle_union_bound
        [OF merkle_bound comp_bound trace_fri_bound comp_fri_bound
          query_bound])
  have empty_drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      adversary_initial_state \<le>
      F + (trace_fri_error + low_degree_trace_pair_agreement_error budgets)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_bound_from_reachable_trace_fri_and_pair_union
        [OF wf controlled trace_fri_reduction fixed_empty_alpha_bound])
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have empty_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> empty_query_error"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_empty_query_bad_le_current_empty_opening_hit_at_zero[
          OF wf controlled] current_empty_bound])
  have empty_header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header_transcript)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (F + (trace_fri_error +
        low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_transcript_bound_from_empty_relevant_drift_transcript_trace_fri_and_query
        [OF false_statement wf controlled empty_drift_bound
          empty_trace_fri_bound empty_query_bound])
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      (hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds. C i) + trace_fri_error + composition_fri_error +
      (\<Sum>i<rounds. C i)) +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (F + (trace_fri_error +
          low_degree_trace_pair_agreement_error budgets)) +
        trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_and_empty_header_transcript_bounds
        [OF false_statement partial_candidate_bound empty_header_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

theorem stark_soundness_from_transcript_indexed_partial_opening_route_single_query_charge:
  fixes F empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and fixed_empty_alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (F + (trace_fri_error +
        low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  have merkle_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
  have trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_partial_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have comp_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> composition_fri_error"
    by (rule
        composition_fri_bad_with_partial_candidates_bound_from_reachable_reduction
        [OF composition_fri_reduction])
  have current_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds
        [OF round_bound wf controlled])
  have partial_candidate_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds. C i) + trace_fri_error + composition_fri_error"
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_partial_candidate_aligned_randomization_with_merkle_current_query_union_bound
        [OF wf controlled merkle_bound current_query_bound trace_fri_bound
          comp_fri_bound])
  have empty_drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      adversary_initial_state \<le>
      F + (trace_fri_error + low_degree_trace_pair_agreement_error budgets)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_bound_from_reachable_trace_fri_and_pair_union
        [OF wf controlled trace_fri_reduction fixed_empty_alpha_bound])
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have empty_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> empty_query_error"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_empty_query_bad_le_current_empty_opening_hit_at_zero[
          OF wf controlled] current_empty_bound])
  have empty_header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header_transcript)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (F + (trace_fri_error +
        low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_transcript_bound_from_empty_relevant_drift_transcript_trace_fri_and_query
        [OF false_statement wf controlled empty_drift_bound
          empty_trace_fri_bound empty_query_bound])
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      (hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds. C i) + trace_fri_error + composition_fri_error) +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (F + (trace_fri_error +
          low_degree_trace_pair_agreement_error budgets)) +
        trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_and_empty_header_transcript_bounds
        [OF false_statement partial_candidate_bound empty_header_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

theorem stark_soundness_from_transcript_indexed_partial_opening_route_from_not_prefix:
  fixes N empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> N"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      ((composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) + N) +
        (trace_fri_error +
          low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?P =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  have transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets
        [OF wf controlled])
  have prefix_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have fixed_empty_alpha_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
      adversary_initial_state \<le> ?P + N"
  proof (rule order_trans)
    show "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      wp_event ?M
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state +
      wp_event ?M
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_fixed_empty_alpha_hit_le_prefix_or_not_prefix
          [OF wf controlled])
    show "... \<le> ?P + N"
      by (intro add_mono prefix_bound not_prefix_bound)
  qed
  show ?thesis
    by (rule
        stark_soundness_from_transcript_indexed_partial_opening_route
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound fixed_empty_alpha_bound
          current_empty_bound])
qed

theorem stark_soundness_from_transcript_indexed_partial_opening_route_from_not_prefix_single_query_charge:
  fixes N empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> N"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      ((composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) + N) +
        (trace_fri_error +
          low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?P =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  have transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets
        [OF wf controlled])
  have prefix_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have fixed_empty_alpha_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
      adversary_initial_state \<le> ?P + N"
  proof (rule order_trans)
    show "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      wp_event ?M
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state +
      wp_event ?M
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_fixed_empty_alpha_hit_le_prefix_or_not_prefix
          [OF wf controlled])
    show "... \<le> ?P + N"
      by (intro add_mono prefix_bound not_prefix_bound)
  qed
  show ?thesis
    by (rule
        stark_soundness_from_transcript_indexed_partial_opening_route_single_query_charge
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound fixed_empty_alpha_bound
          current_empty_bound])
qed

theorem stark_soundness_from_transcript_indexed_partial_opening_route_from_uncovered_and_transcript:
  fixes U P empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and uncovered_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
        adversary_initial_state \<le> U"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      ((composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        (hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) + U +
          (P + staged_concrete_transcript_target_error_bound) +
          (P + staged_concrete_transcript_target_error_bound))) +
        (trace_fri_error +
          low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  have transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have no_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_bound_from_sampled_transcript
        [OF data_pre_bound transcript_new_bound])
  have path_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_bound_from_sampled_transcript
        [OF data_pre_bound transcript_new_bound])
  have collision_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision_bound
        [OF wf controlled])
  have not_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (staged_alpha_search_queries budgets 0) +
      U + (P + staged_concrete_transcript_target_error_bound) +
      (P + staged_concrete_transcript_target_error_bound)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_bound])
  show ?thesis
    by (rule
        stark_soundness_from_transcript_indexed_partial_opening_route_from_not_prefix
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound not_prefix_bound
          current_empty_bound])
qed

theorem stark_soundness_from_transcript_indexed_partial_opening_route_from_uncovered_and_transcript_single_query_charge:
  fixes U P empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and uncovered_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
        adversary_initial_state \<le> U"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      ((composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        (hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) + U +
          (P + staged_concrete_transcript_target_error_bound) +
          (P + staged_concrete_transcript_target_error_bound))) +
        (trace_fri_error +
          low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  have transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have no_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_bound_from_sampled_transcript
        [OF data_pre_bound transcript_new_bound])
  have path_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_bound_from_sampled_transcript
        [OF data_pre_bound transcript_new_bound])
  have collision_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision_bound
        [OF wf controlled])
  have not_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (staged_alpha_search_queries budgets 0) +
      U + (P + staged_concrete_transcript_target_error_bound) +
      (P + staged_concrete_transcript_target_error_bound)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_bound])
  show ?thesis
    by (rule
        stark_soundness_from_transcript_indexed_partial_opening_route_from_not_prefix_single_query_charge
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound not_prefix_bound
          current_empty_bound])
qed

end

end
