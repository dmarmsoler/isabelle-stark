(*  Title:      Stark/Soundness_FRI_Query_Fiber_Exact_Staged_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_Fiber_Exact_Staged_Bounds
  imports
    Soundness_FRI_Query_Fiber_Staged_Bounds
    Soundness_FRI_Query_List_Exact_Product
begin

text \<open>
  Exact query-list staged bounds for the outside-query-cover branch of sampled
  FRI query events.

  This layer keeps the challenge-cover split and uses exact product
  query-list accounting for the outside branch.
\<close>

context soundness
begin

lemma checked_staged_security_trace_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_list_exact:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and projection:
      "fst ` (P \<inter> (UNIV \<times> (- B))) \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      (nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
       hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget))"
proof -
  let ?Outside = "P \<inter> (UNIV \<times> (- B))"
  have split:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_set_hit s B) out \<or>
        staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_query_challenge_pair_set_hit s ?Outside) out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P) out"
    then show
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_set_hit s B) out \<or>
       staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s ?Outside) out"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some full)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases full) (auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      have pair_hit:
        "trace_fri_query_challenge_pair_set_hit ?s P
          (Some (result, final_state))"
        using hit out_eq
        unfolding staged_security_with_data_state_verifier_event_def by simp
      from pair_hit obtain trace_roots trace_bs trace_final dg
          composition_roots composition_bs composition_final fri_query_idxs
          trace_round_layers composition_round_layers
        where openings:
          "accepted_fri_opening_transcript ?s (Some (result, final_state))
            trace_roots trace_bs trace_final dg composition_roots
            composition_bs composition_final fri_query_idxs
            trace_round_layers composition_round_layers"
        and pair: "(fri_query_idxs, trace_bs) \<in> P"
        unfolding trace_fri_query_challenge_pair_set_hit_def by blast
      show ?thesis
      proof (cases "trace_bs \<in> B")
        case True
        have challenges:
          "accepted_fri_challenges ?s (Some (result, final_state))
            trace_bs dg composition_bs"
          by (rule accepted_fri_opening_transcript_challenges[OF openings])
        have "trace_fri_challenge_list_set_hit ?s B
            (Some (result, final_state))"
          unfolding trace_fri_challenge_list_set_hit_def
          using challenges True by blast
        then show ?thesis
          using out_eq unfolding staged_security_with_data_state_verifier_event_def
          by simp
      next
        case False
        have outside_pair: "(fri_query_idxs, trace_bs) \<in> ?Outside"
          using pair False by simp
        have "trace_fri_query_challenge_pair_set_hit ?s ?Outside
            (Some (result, final_state))"
          unfolding trace_fri_query_challenge_pair_set_hit_def
          using openings outside_pair by blast
        then show ?thesis
          using out_eq unfolding staged_security_with_data_state_verifier_event_def
          by simp
      qed
    qed
  qed
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_set_hit s B))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_query_challenge_pair_set_hit s ?Outside))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
       hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget))"
  proof (rule add_mono)
    show "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_set_hit s B))
        adversary_initial_state
        \<le> F +
          hash_relation_budget_value (card B * ceil_log clength)
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget)"
      by (rule checked_staged_security_trace_fri_challenge_list_set_hit_bound
          [OF wf controlled finite_B fresh_bound])
    show "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_query_challenge_pair_set_hit s ?Outside))
        adversary_initial_state
        \<le> nnreal (card Q) *
            (1 / nnreal (card query_sample_space)) ^ rounds +
          hash_relation_budget_value
            (query_index_raw_list_relation_fiber_bound Q)
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget)"
      by (rule
          checked_staged_security_trace_fri_query_challenge_pair_set_hit_exact_product_bound
          [OF wf controlled projection subset])
  qed
  finally show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_composition_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_list_exact:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and projection:
      "\<And>dg. fst ` (P dg \<inter> (UNIV \<times> (- B dg))) \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      (nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
       hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget))"
proof -
  let ?Outside = "\<lambda>dg. P dg \<inter> (UNIV \<times> (- B dg))"
  have split:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_challenge_list_set_hit s B) out \<or>
        staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_query_challenge_pair_set_hit s ?Outside) out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P) out"
    then show
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_set_hit s B) out \<or>
       staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s ?Outside) out"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some full)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases full) (auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      have pair_hit:
        "composition_fri_query_challenge_pair_set_hit ?s P
          (Some (result, final_state))"
        using hit out_eq
        unfolding staged_security_with_data_state_verifier_event_def by simp
      from pair_hit obtain trace_roots trace_bs trace_final fri_dg
          composition_roots composition_bs composition_final fri_query_idxs
          trace_round_layers composition_round_layers
        where openings:
          "accepted_fri_opening_transcript ?s (Some (result, final_state))
            trace_roots trace_bs trace_final fri_dg composition_roots
            composition_bs composition_final fri_query_idxs
            trace_round_layers composition_round_layers"
        and pair: "(fri_query_idxs, composition_bs) \<in> P fri_dg"
        unfolding composition_fri_query_challenge_pair_set_hit_def by blast
      show ?thesis
      proof (cases "composition_bs \<in> B fri_dg")
        case True
        have challenges:
          "accepted_fri_challenges ?s (Some (result, final_state))
            trace_bs fri_dg composition_bs"
          by (rule accepted_fri_opening_transcript_challenges[OF openings])
        have "composition_fri_challenge_list_set_hit ?s B
            (Some (result, final_state))"
          unfolding composition_fri_challenge_list_set_hit_def
          using challenges True by blast
        then show ?thesis
          using out_eq unfolding staged_security_with_data_state_verifier_event_def
          by simp
      next
        case False
        have outside_pair:
          "(fri_query_idxs, composition_bs) \<in> ?Outside fri_dg"
          using pair False by simp
        have "composition_fri_query_challenge_pair_set_hit ?s ?Outside
            (Some (result, final_state))"
          unfolding composition_fri_query_challenge_pair_set_hit_def
          using openings outside_pair by blast
        then show ?thesis
          using out_eq unfolding staged_security_with_data_state_verifier_event_def
          by simp
      qed
    qed
  qed
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_challenge_list_set_hit s B))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_query_challenge_pair_set_hit s ?Outside))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
       hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget))"
  proof (rule add_mono)
    show "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_challenge_list_set_hit s B))
        adversary_initial_state
        \<le> F +
          hash_relation_budget_value
            (\<Sum>dg \<in> (UNIV :: 'f set).
              card (B dg) * ceil_log (maxDegree + 1))
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget)"
      by (rule
          checked_staged_security_composition_fri_challenge_list_set_hit_bound
          [OF wf controlled finite_B fresh_bound])
    show "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_query_challenge_pair_set_hit s ?Outside))
        adversary_initial_state
        \<le> nnreal (card Q) *
            (1 / nnreal (card query_sample_space)) ^ rounds +
          hash_relation_budget_value
            (query_index_raw_list_relation_fiber_bound Q)
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget)"
      by (rule
          checked_staged_security_composition_fri_query_challenge_pair_set_hit_exact_product_bound
          [OF wf controlled projection subset])
  qed
  finally show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_query_cover_exact:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      (nnreal
        (card
          (generic_fri_sampled_query_outside_query_cover
            trace_table_low_degree (Not \<circ> trace_table_low_degree)
            (clength - 1) B)) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
       hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (generic_fri_sampled_query_outside_query_cover
            trace_table_low_degree (Not \<circ> trace_table_low_degree)
            (clength - 1) B))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget))"
proof -
  let ?P =
    "trace_fri_sampled_query_bad_pair_union \<inter>
      (fri_query_index_list_space \<times> UNIV)"
  let ?Q =
    "generic_fri_sampled_query_outside_query_cover trace_table_low_degree
      (Not \<circ> trace_table_low_degree) (clength - 1) B"
  have sampled_to_pair:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s ?P))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          trace_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit
        split: option.splits prod.splits)
  also have "... \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      (nnreal (card ?Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
       hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound ?Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget))"
    by (rule
        checked_staged_security_trace_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_list_exact
        [OF wf controlled finite_B fresh_bound
          trace_fri_sampled_query_outside_projection_subset
          generic_fri_sampled_query_outside_query_cover_subset])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_query_cover_exact:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      (nnreal (card (composition_fri_sampled_query_outside_query_cover B)) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
       hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (composition_fri_sampled_query_outside_query_cover B))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget))"
proof -
  let ?P =
    "\<lambda>dg. composition_fri_sampled_query_bad_pair_union dg \<inter>
      (fri_query_index_list_space \<times> UNIV)"
  let ?Q = "composition_fri_sampled_query_outside_query_cover B"
  have sampled_to_pair:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s ?P))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit
        split: option.splits prod.splits)
  also have "... \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      (nnreal (card ?Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
       hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound ?Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget))"
    by (rule
        checked_staged_security_composition_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_list_exact
        [OF wf controlled finite_B fresh_bound
          composition_fri_sampled_query_outside_projection_subset
          composition_fri_sampled_query_outside_query_cover_subset])
  finally show ?thesis .
qed

end

end
