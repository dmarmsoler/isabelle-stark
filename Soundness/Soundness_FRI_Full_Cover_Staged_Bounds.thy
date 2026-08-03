(*  Title:      Stark/Soundness_FRI_Full_Cover_Staged_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Full_Cover_Staged_Bounds
  imports
    Soundness_FRI_Prequery_Composition_Sampled_Bounds
    Soundness_FRI_Full_Cover_Active_Bounds
begin

text \<open>
  Staged bounds for the full-cover FRI split.

  Unlike the verifier-local full-cover envelope lemmas, these results work in
  the staged adversary experiment where future FRI keys may have been queried
  by the attacker.  The full-cover part is therefore routed through the
  existing staged fresh/prequery accounting for FRI challenge-list hits.
\<close>

context soundness
begin

lemma trace_fri_bad_with_sampled_layer_chain_not_None:
  "\<not> trace_fri_bad_with_sampled_layer_chain s None"
  unfolding trace_fri_bad_with_sampled_layer_chain_def
    trace_fri_partial_candidate_opening_evidence_def
    accepted_fri_opening_transcript_def
  by blast

lemma composition_fri_bad_with_sampled_layer_chain_not_None:
  "\<not> composition_fri_bad_with_sampled_layer_chain s None"
  unfolding composition_fri_bad_with_sampled_layer_chain_def
    composition_fri_partial_candidate_opening_evidence_def
    accepted_fri_opening_transcript_def
  by blast

lemma trace_fri_sampled_missing_full_cover_not_None:
  "\<not> trace_fri_sampled_missing_full_cover s bad None"
  unfolding trace_fri_sampled_missing_full_cover_def
  using trace_fri_bad_with_sampled_layer_chain_not_None by blast

lemma composition_fri_sampled_missing_full_cover_not_None:
  "\<not> composition_fri_sampled_missing_full_cover s bad None"
  unfolding composition_fri_sampled_missing_full_cover_def
  using composition_fri_bad_with_sampled_layer_chain_not_None by blast

lemma checked_staged_security_trace_fri_full_cover_layer_chain_bound_from_fresh_and_prequery:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
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
        (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad))
      adversary_initial_state
      \<le> F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad))
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
        (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad) out"
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
    have full:
      "trace_fri_bad_with_full_cover_layer_chain ?s bad
        (Some (result, final_state))"
      using hit unfolding staged_security_with_data_state_verifier_event_def
        out_eq by simp
    have list_hit:
      "trace_fri_challenge_list_set_hit ?s B
        (Some (result, final_state))"
      by (rule trace_fri_bad_with_full_cover_layer_chain_imp_list_hit
          [OF full])
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
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule checked_staged_security_trace_fri_challenge_list_set_hit_bound
        [OF wf controlled finite_B fresh_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_full_cover_layer_chain_bound_from_fresh_and_prequery:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
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
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad))
      adversary_initial_state
      \<le> F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad))
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_challenge_list_set_hit s B))
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
        (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad) out"
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
    have full:
      "composition_fri_bad_with_full_cover_layer_chain ?s bad
        (Some (result, final_state))"
      using hit unfolding staged_security_with_data_state_verifier_event_def
        out_eq by simp
    have list_hit:
      "composition_fri_challenge_list_set_hit ?s B
        (Some (result, final_state))"
      by (rule composition_fri_bad_with_full_cover_layer_chain_imp_list_hit
          [OF full])
        (rule envelope[OF builder])
    show
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_set_hit s B) out"
      unfolding staged_security_with_data_state_verifier_event_def out_eq
      using list_hit by simp
  qed
  also have "... \<le>
      F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_challenge_list_set_hit_bound
        [OF wf controlled finite_B fresh_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_sampled_missing_full_cover_bound_from_domain_split:
  assumes proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and domain_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> DL"
    and sampled_domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> SD"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_missing_full_cover s bad))
      adversary_initial_state \<le> P + I + (I + DL) + (I + SD)"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> trace_fri_sampled_missing_full_cover s bad None"
    by (rule trace_fri_sampled_missing_full_cover_not_None)
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover ?s bad) ?s
      \<le> P + I + (I + DL) + (I + SD)"
    by (rule wp_trace_fri_sampled_missing_full_cover_bound_from_domain_split)
      (rule proximity[OF support], rule index[OF support],
       rule domain_length[OF support], rule sampled_domain[OF support])
qed

lemma checked_staged_security_trace_fri_sampled_layer_chain_bound_from_full_cover_fresh_and_domain_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
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
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and domain_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> DL"
    and sampled_domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> SD"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
proof -
  have full_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad))
      adversary_initial_state
      \<le>
      F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_full_cover_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B envelope fresh_bound])
  have missing_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_missing_full_cover s bad))
      adversary_initial_state \<le> P + I + (I + DL) + (I + SD)"
    by (rule
        checked_staged_security_trace_fri_sampled_missing_full_cover_bound_from_domain_split
        [OF proximity index domain_length sampled_domain])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad) out \<or>
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_sampled_missing_full_cover s bad) out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest: trace_fri_sampled_imp_full_cover_or_missing
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_sampled_missing_full_cover s bad))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
    by (rule add_mono[OF full_bound missing_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_canonical_sampled_layer_chain_bound_from_full_cover_fresh_and_domain_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
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
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and domain_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> DL"
    and sampled_domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> SD"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_canonical_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_canonical_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_sampled_layer_chain)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro: trace_fri_bad_with_canonical_sampled_layer_chain_imp_sampled
        split: option.splits prod.splits)
  also have "... \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
    by (rule
        checked_staged_security_trace_fri_sampled_layer_chain_bound_from_full_cover_fresh_and_domain_split
        [OF wf controlled finite_B envelope fresh_bound proximity index
          domain_length sampled_domain])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_sampled_missing_full_cover_bound_from_domain_split:
  assumes proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and domain_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> DL"
    and sampled_domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> SD"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_missing_full_cover s bad))
      adversary_initial_state \<le> P + I + (I + DL) + (I + SD)"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> composition_fri_sampled_missing_full_cover s bad None"
    by (rule composition_fri_sampled_missing_full_cover_not_None)
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover ?s bad) ?s
      \<le> P + I + (I + DL) + (I + SD)"
    by (rule
        wp_composition_fri_sampled_missing_full_cover_bound_from_domain_split)
      (rule proximity[OF support], rule index[OF support],
       rule domain_length[OF support], rule sampled_domain[OF support])
qed

lemma checked_staged_security_composition_fri_sampled_layer_chain_bound_from_full_cover_fresh_and_domain_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
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
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and domain_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> DL"
    and sampled_domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> SD"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
proof -
  have full_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad))
      adversary_initial_state
      \<le>
      F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_full_cover_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B envelope fresh_bound])
  have missing_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_missing_full_cover s bad))
      adversary_initial_state \<le> P + I + (I + DL) + (I + SD)"
    by (rule
        checked_staged_security_composition_fri_sampled_missing_full_cover_bound_from_domain_split
        [OF proximity index domain_length sampled_domain])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad)
            out \<or>
          staged_security_with_data_state_verifier_event
            (\<lambda>s. composition_fri_sampled_missing_full_cover s bad) out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest: composition_fri_sampled_imp_full_cover_or_missing
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_sampled_missing_full_cover s bad))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
    by (rule add_mono[OF full_bound missing_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_canonical_sampled_layer_chain_bound_from_full_cover_fresh_and_domain_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
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
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and domain_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> DL"
    and sampled_domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> SD"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_canonical_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_canonical_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_sampled_layer_chain)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro: composition_fri_bad_with_canonical_sampled_layer_chain_imp_sampled
        split: option.splits prod.splits)
  also have "... \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
    by (rule
        checked_staged_security_composition_fri_sampled_layer_chain_bound_from_full_cover_fresh_and_domain_split
        [OF wf controlled finite_B envelope fresh_bound proximity index
          domain_length sampled_domain])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_header_tied_sampled_layer_chain_bound_from_full_cover_fresh_and_domain_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
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
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and domain_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> DL"
    and sampled_domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> SD"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
proof -
  have full_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad))
      adversary_initial_state
      \<le>
      F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_full_cover_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B envelope fresh_bound])
  have missing_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_missing_full_cover s bad))
      adversary_initial_state \<le> P + I + (I + DL) + (I + SD)"
    by (rule
        checked_staged_security_trace_fri_sampled_missing_full_cover_bound_from_domain_split
        [OF proximity index domain_length sampled_domain])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad) out \<or>
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_sampled_missing_full_cover s bad) out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest!: trace_fri_header_tied_sampled_layer_chain_imp_sampled_layer_chain
        dest: trace_fri_sampled_imp_full_cover_or_missing
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_sampled_missing_full_cover s bad))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
    by (rule add_mono[OF full_bound missing_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_verifier_tied_sampled_layer_chain_bound_from_full_cover_fresh_and_domain_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
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
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and domain_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> DL"
    and sampled_domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> SD"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
proof -
  have full_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad))
      adversary_initial_state
      \<le>
      F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_full_cover_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B envelope fresh_bound])
  have missing_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_missing_full_cover s bad))
      adversary_initial_state \<le> P + I + (I + DL) + (I + SD)"
    by (rule
        checked_staged_security_composition_fri_sampled_missing_full_cover_bound_from_domain_split
        [OF proximity index domain_length sampled_domain])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad)
            out \<or>
          staged_security_with_data_state_verifier_event
            (\<lambda>s. composition_fri_sampled_missing_full_cover s bad)
            out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest!: composition_fri_verifier_tied_sampled_layer_chain_imp_sampled_layer_chain
        dest: composition_fri_sampled_imp_full_cover_or_missing
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_sampled_missing_full_cover s bad))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
    by (rule add_mono[OF full_bound missing_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_sampled_missing_full_cover_bound_from_witness_domain:
  assumes proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and witness_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_witness_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> W"
    and domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_missing_full_cover s bad))
      adversary_initial_state \<le> P + I + W + D"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> trace_fri_sampled_missing_full_cover s bad None"
    by (rule trace_fri_sampled_missing_full_cover_not_None)
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover ?s bad) ?s \<le>
      P + I + W + D"
    by (rule
        wp_trace_fri_sampled_missing_full_cover_bound_from_witness_length_subcases)
      (rule proximity[OF support], rule index[OF support],
       rule witness_length[OF support], rule domain[OF support])
qed

lemma checked_staged_security_composition_fri_sampled_missing_full_cover_bound_from_witness_domain:
  assumes proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and witness_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_witness_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> W"
    and domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_missing_full_cover s bad))
      adversary_initial_state \<le> P + I + W + D"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> composition_fri_sampled_missing_full_cover s bad None"
    by (rule composition_fri_sampled_missing_full_cover_not_None)
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover ?s bad) ?s \<le>
      P + I + W + D"
    by (rule
        wp_composition_fri_sampled_missing_full_cover_bound_from_witness_length_subcases)
      (rule proximity[OF support], rule index[OF support],
       rule witness_length[OF support], rule domain[OF support])
qed

lemma checked_staged_security_trace_fri_header_tied_sampled_layer_chain_bound_from_full_cover_fresh_and_witness_domain:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
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
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and witness_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_witness_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> W"
    and domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + W + D)"
proof -
  have full_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad))
      adversary_initial_state
      \<le>
      F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_full_cover_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B envelope fresh_bound])
  have missing_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_missing_full_cover s bad))
      adversary_initial_state \<le> P + I + W + D"
    by (rule
        checked_staged_security_trace_fri_sampled_missing_full_cover_bound_from_witness_domain
        [OF proximity index witness_length domain])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad) out \<or>
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_sampled_missing_full_cover s bad) out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest!: trace_fri_header_tied_sampled_layer_chain_imp_sampled_layer_chain
        dest: trace_fri_sampled_imp_full_cover_or_missing
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_sampled_missing_full_cover s bad))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + W + D)"
    by (rule add_mono[OF full_bound missing_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_sampled_layer_chain_bound_from_full_cover_fresh_and_witness_domain:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
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
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and witness_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_witness_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> W"
    and domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + W + D)"
proof -
  have full_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad))
      adversary_initial_state
      \<le>
      F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_full_cover_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B envelope fresh_bound])
  have missing_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_missing_full_cover s bad))
      adversary_initial_state \<le> P + I + W + D"
    by (rule
        checked_staged_security_trace_fri_sampled_missing_full_cover_bound_from_witness_domain
        [OF proximity index witness_length domain])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad) out \<or>
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_sampled_missing_full_cover s bad) out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest: trace_fri_sampled_imp_full_cover_or_missing
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_bad_with_full_cover_layer_chain s bad))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_sampled_missing_full_cover s bad))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + W + D)"
    by (rule add_mono[OF full_bound missing_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_verifier_tied_sampled_layer_chain_bound_from_full_cover_fresh_and_witness_domain:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
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
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and witness_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_witness_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> W"
    and domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + W + D)"
proof -
  have full_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad))
      adversary_initial_state
      \<le>
      F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_full_cover_layer_chain_bound_from_fresh_and_prequery
        [OF wf controlled finite_B envelope fresh_bound])
  have missing_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_missing_full_cover s bad))
      adversary_initial_state \<le> P + I + W + D"
    by (rule
        checked_staged_security_composition_fri_sampled_missing_full_cover_bound_from_witness_domain
        [OF proximity index witness_length domain])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad)
            out \<or>
          staged_security_with_data_state_verifier_event
            (\<lambda>s. composition_fri_sampled_missing_full_cover s bad)
            out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest!: composition_fri_verifier_tied_sampled_layer_chain_imp_sampled_layer_chain
        dest: composition_fri_sampled_imp_full_cover_or_missing
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_bad_with_full_cover_layer_chain s bad))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_sampled_missing_full_cover s bad))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + W + D)"
    by (rule add_mono[OF full_bound missing_bound])
  finally show ?thesis .
qed

end

end
