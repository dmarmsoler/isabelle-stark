(*  Title:      Stark/Soundness_Conceptual_Query_Current_Candidate.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Conceptual_Query_Current_Candidate
  imports Soundness_Conceptual_Query_Current_Path
begin

text \<open>
  Fixed-candidate projection for current-query openings.

  This layer keeps the trace/composition candidate tables as fixed parameters
  while projecting the data-state current-opening event to the corresponding
  query-prefix event.  It is the form needed by the conceptual/default query
  target bound: the target is fixed before the query-index challenge.
\<close>

context soundness
begin

definition staged_security_with_data_state_current_query_partial_candidate_hit_at
where
  "staged_security_with_data_state_current_query_partial_candidate_hit_at
      trace_table composition_table i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((data, attacker_state), result), final_state) \<Rightarrow>
        (let s =
          verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)
         in \<exists>raw trace_openings composition_openings rest.
          i < rounds \<and>
          fmlookup (HashMap final_state)
            (QueryIndexChallenge i
              (state_after_query_chunks
                (staged_query_start_hash data)
                (staged_query_chunks data) i)) =
            Some raw \<and>
          staged_composition_fri_roots data \<noteq> [] \<and>
          Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
          partial_authenticated_table (staged_trace_root data)
            (scale * clength) trace_openings final_state \<and>
          partial_authenticated_table
            (hd (staged_composition_fri_roots data)) (scale * clength)
            composition_openings final_state \<and>
          verifier_header_transcript s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)
            rest \<and>
          partial_query_openings_consistent trace_openings
            composition_openings (staged_alphas data) (index (to_nat raw)) \<and>
          partial_trace_table_candidate trace_table
            ((replicate rounds []) [i := trace_openings]) \<and>
          partial_composition_table_candidate composition_table
            ((replicate rounds []) [i := composition_openings])))"

definition staged_security_with_data_state_current_query_some_partial_candidate_hit
where
  "staged_security_with_data_state_current_query_some_partial_candidate_hit
      out \<longleftrightarrow>
    (\<exists>trace_table composition_table i.
      i < rounds \<and>
      staged_security_with_data_state_current_query_partial_candidate_hit_at
        trace_table composition_table i out)"

lemma staged_security_with_data_state_current_query_partial_candidate_hit_at_imp_query_prefix_authenticated_candidate_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "staged_security_with_data_state_current_query_partial_candidate_hit_at
        trace_table composition_table i
        (Some (((data, attacker_state), result), final_state))"
  shows
    "checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
      trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from hit obtain raw' trace_openings composition_openings rest where
    final_lookup':
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
       Some raw'"
    and comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and comp_auth:
      "partial_authenticated_table
        (hd (staged_composition_fri_roots data)) (scale * clength)
        composition_openings final_state"
    and consistent':
      "partial_query_openings_consistent trace_openings
        composition_openings (staged_alphas data) (index (to_nat raw'))"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    unfolding
      staged_security_with_data_state_current_query_partial_candidate_hit_at_def
      Let_def
    by auto
  have final_lookup:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_raw_final_lookup
        [OF wf controlled i_bound support])
  have raw_eq: "raw' = raw"
    using final_lookup' final_lookup by simp
  have opening_hit:
    "checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    unfolding checked_staged_security_with_query_prefix_authenticated_opening_hit_def
    using comp_nonempty trace_auth comp_auth consistent' raw_eq by simp
  show ?thesis
    unfolding checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_def
    by (intro exI[of _ trace_openings] exI[of _ composition_openings]
        conjI opening_hit trace_candidate comp_candidate)
qed

lemma staged_security_with_data_state_current_query_partial_candidate_hit_at_le_query_prefix_authenticated_candidate:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_query_partial_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state"
proof -
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow>
        staged_security_with_data_state_current_query_partial_candidate_hit_at
          trace_table composition_table i None
    | Some (packed, t) \<Rightarrow>
        staged_security_with_data_state_current_query_partial_candidate_hit_at
          trace_table composition_table i (Some (snd packed, t))"
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_query_partial_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      ?projected
      adversary_initial_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound])
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      ?projected
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state A i)
              adversary_initial_state)"
      and hit: "?projected out"
    show
      "checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          staged_security_with_data_state_current_query_partial_candidate_hit_at_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
          "out =
            Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      show ?thesis
        unfolding out_eq
        by (rule
            staged_security_with_data_state_current_query_partial_candidate_hit_at_imp_query_prefix_authenticated_candidate_on_support
            [OF wf controlled i_bound])
          (use support hit out_eq in simp_all)
    qed
  qed
  show ?thesis
    unfolding projection
    by (rule event_le)
qed

lemma staged_security_with_data_state_current_query_partial_candidate_hit_at_bound_from_conceptual_default:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and residual_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
          trace_table composition_table i)
        adversary_initial_state \<le> R"
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_query_partial_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R + T + C"
proof -
  have prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R + T + C"
    by (rule
        checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_bound_from_conceptual_default_residual_and_structured_paths
        [OF wf controlled i_bound residual_bound trace_path_bound
          composition_path_bound])
  show ?thesis
    by (rule order_trans
        [OF
          staged_security_with_data_state_current_query_partial_candidate_hit_at_le_query_prefix_authenticated_candidate
          prefix_bound])
      (use wf controlled i_bound in simp_all)
qed

lemma staged_security_with_data_state_current_query_partial_candidate_hit_at_bound_from_conceptual_default_context:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and default_context:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_table) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_table) \<and>
        \<not> all_queries_consistent
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_table)
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_table)
          (sqp_alphas prefix)"
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_query_partial_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
proof -
  have prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
    by (rule
        checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_bound_from_conceptual_default_context_and_structured_paths
        [OF wf controlled i_bound default_context trace_path_bound
          composition_path_bound])
  show ?thesis
    by (rule order_trans
        [OF
          staged_security_with_data_state_current_query_partial_candidate_hit_at_le_query_prefix_authenticated_candidate
          prefix_bound])
      (use wf controlled i_bound in simp_all)
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_data_state_current_partial_candidate_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
  obtains trace_table composition_table i where
    "i < rounds"
    "staged_security_with_data_state_current_query_partial_candidate_hit_at
      trace_table composition_table i
      (Some (((data, attacker_state), result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  have header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_current_openingsE
        [OF wf controlled support hit])
    fix s trace_table composition_table query_idxs f i raw trace_openings
        composition_openings trace_openingss composition_openingss
    assume s_def:
        "s = verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      and bad_context:
        "composition_bad_context s (Some (result, final_state))
          trace_table composition_table (staged_alphas data) query_idxs f"
      and i_bound: "i < rounds"
      and final_lookup:
        "fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some raw"
      and idx_eq: "index (to_nat raw) = query_idxs ! i"
      and comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
      and trace_auth:
        "partial_authenticated_table (staged_trace_root data)
          (scale * clength) trace_openings final_state"
      and comp_auth:
        "partial_authenticated_table
          (hd (staged_composition_fri_roots data)) (scale * clength)
          composition_openings final_state"
      and consistent:
        "partial_query_openings_consistent trace_openings
          composition_openings (staged_alphas data) (query_idxs ! i)"
      and trace_candidate_full:
        "partial_trace_table_candidate trace_table trace_openingss"
      and comp_candidate_full:
        "partial_composition_table_candidate composition_table
          composition_openingss"
      and trace_openings_eq: "trace_openings = trace_openingss ! i"
      and comp_openings_eq: "composition_openings = composition_openingss ! i"
      and all_queries:
        "all_queries_consistent trace_table composition_table
          (staged_alphas data)"
      and not_alpha_prefix:
        "\<not> staged_alphas data \<in>
          alpha_prefix_union_bad_sets alpha_prefix_state
            composition_trace_bad_alpha_space (fst alpha_prefix)"
    have consistent_raw:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
      using consistent idx_eq by simp
    have trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
      by (rule partial_trace_table_candidate_single_roundI)
        (use i_bound trace_candidate_full trace_openings_eq in
          \<open>auto simp: partial_trace_table_candidate_def\<close>)
    have comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
      by (rule partial_composition_table_candidate_single_roundI)
        (use i_bound comp_candidate_full comp_openings_eq in
          \<open>auto simp: partial_composition_table_candidate_def\<close>)
    have round_hit:
      "staged_security_with_data_state_current_query_partial_candidate_hit_at
        trace_table composition_table i
        (Some (((data, attacker_state), result), final_state))"
      unfolding
        staged_security_with_data_state_current_query_partial_candidate_hit_at_def
        Let_def
      apply simp
      by (intro exI[of _ raw] exI[of _ trace_openings]
          exI[of _ composition_openings]
          exI[of _ "List.concat (staged_query_chunks data)"] conjI)
        (use i_bound final_lookup comp_nonempty verifier trace_auth
          comp_auth header consistent_raw trace_candidate comp_candidate
          in simp_all)
    show ?thesis
      by (rule that[OF i_bound round_hit])
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_data_state_current_some_partial_candidate_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
  shows
    "staged_security_with_data_state_current_query_some_partial_candidate_hit
      (Some (((data, attacker_state), result), final_state))"
proof -
  from
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_data_state_current_partial_candidate_hit_on_support
      [OF wf controlled support hit]
  obtain trace_table composition_table i where
    i_bound: "i < rounds"
    and round_hit:
      "staged_security_with_data_state_current_query_partial_candidate_hit_at
        trace_table composition_table i
        (Some (((data, attacker_state), result), final_state))"
    by blast
  show ?thesis
    unfolding
      staged_security_with_data_state_current_query_some_partial_candidate_hit_def
    by (intro exI[of _ trace_table] exI[of _ composition_table]
        exI[of _ i] conjI i_bound round_hit)
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_data_state_current_some_partial_candidate_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_some_partial_candidate_hit
      adversary_initial_state"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (packed, t) \<Rightarrow>
        staged_security_with_data_state_current_query_some_partial_candidate_hit
          (Some (?project packed, t))"
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?projected adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
                A)
              adversary_initial_state)"
      and hit:
        "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
          out"
    show "?projected out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
          checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        by simp
    next
      case (Some packed)
      then obtain alpha_prefix alpha_prefix_state data attacker_state result
          final_state where out_eq:
          "out =
            Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      have candidate_hit:
        "staged_security_with_data_state_current_query_some_partial_candidate_hit
          (Some (((data, attacker_state), result), final_state))"
        by (rule
            checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_data_state_current_some_partial_candidate_hit_on_support
            [OF wf controlled])
          (use support hit out_eq in simp_all)
      show ?thesis
        unfolding out_eq
        using candidate_hit by simp
    qed
  qed
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?projected adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_some_partial_candidate_hit
      adversary_initial_state"
  proof -
    have
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_current_query_some_partial_candidate_hit
        adversary_initial_state =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
          \<bind> (\<lambda>x. return (?project x)))
        staged_security_with_data_state_current_query_some_partial_candidate_hit
        adversary_initial_state"
      using
        checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
        [of A]
      by simp
    also have "... =
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        ?projected adversary_initial_state"
      by (subst wp_event_bind_return_map)
        (simp add:
          staged_security_with_data_state_current_query_some_partial_candidate_hit_def
          staged_security_with_data_state_current_query_partial_candidate_hit_at_def)
    finally show ?thesis
      by simp
  qed
  show ?thesis
    by (rule order_trans[OF event_le])
      (simp add: projection)
qed

end

end
