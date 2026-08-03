(*  Title:      Stark/Soundness_FRI_Prequery_Trace_Sampled_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Prequery_Trace_Sampled_Bounds
  imports Soundness_FRI_Prequery_Challenge_Bounds
begin

text \<open>
  Staged bounds for trace FRI sampled-layer events.  The lemmas combine the
  fresh-challenge case with prequery accounting from the shared random oracle.
\<close>

context soundness
begin

lemma checked_staged_security_trace_fri_sampled_layer_chain_bound_from_fresh_and_prequery:
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
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_set_hit s B))
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
      "staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain out"
    from hit obtain data attacker_state result final_state where
      out_eq: "out = Some (((data, attacker_state), result), final_state)"
      unfolding staged_security_with_data_state_verifier_event_def
      by (cases out) (auto split: option.splits prod.splits)
    have builder:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
      using checked_staged_security_experiment_with_data_state_outcomeE
        [OF support[unfolded out_eq]]
      by blast
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    have sampled:
      "trace_fri_bad_with_sampled_layer_chain ?s
        (Some (result, final_state))"
      using hit unfolding staged_security_with_data_state_verifier_event_def
        out_eq by simp
    have list_hit:
      "trace_fri_challenge_list_set_hit ?s B (Some (result, final_state))"
      by (rule trace_fri_bad_with_sampled_layer_chain_imp_list_hit
          [OF sampled cover[OF builder]])
        (rule envelope[OF builder])
    show
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_set_hit s B) out"
      unfolding staged_security_with_data_state_verifier_event_def out_eq
      using list_hit by simp
  qed
  also have "... \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule checked_staged_security_trace_fri_challenge_list_set_hit_bound
        [OF wf controlled finite_B fresh_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_header_tied_sampled_layer_chain_bound_from_fresh_and_prequery:
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
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_sampled_layer_chain)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro: trace_fri_header_tied_sampled_layer_chain_imp_sampled_layer_chain
        split: option.splits prod.splits)
  also have "... \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_sampled_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B cover envelope fresh_bound])
  finally show ?thesis .
qed

end

end
