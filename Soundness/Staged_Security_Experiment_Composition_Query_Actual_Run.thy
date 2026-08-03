(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Actual_Run.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Actual_Run
  imports Staged_Security_Experiment_Composition_Query_Single_Round
begin

text \<open>
  Same-run authenticated-opening split for the composition query branch.

  This layer keeps the verifier continuation from the staged experiment fixed,
  so partial-Merkle inconsistency is expressed as the actual verifier event for
  the sampled run.
\<close>

context soundness
begin

definition checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
where
  "checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
      out \<longleftrightarrow>
    checked_staged_security_with_actual_alpha_prefix_verifier_event
      partial_merkle_inconsistency_bad out"

lemma checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix_imp_actual_partial_merkle_or_candidate_pair_on_support:
  assumes support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
        A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    and trace_low:
      "\<And>i trace_openings composition_openings trace_table
          composition_table.
        i < rounds \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        trace_table_low_degree trace_table"
    and comp_low:
      "\<And>i trace_openings composition_openings trace_table
          composition_table.
        i < rounds \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>i trace_openings composition_openings trace_table
          composition_table prefix prefix_state.
        i < rounds \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     (\<exists>i trace_table composition_table.
      checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
        A trace_table composition_table i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)))"
proof -
  let ?out =
    "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
      result), final_state)"
  let ?vout = "Some (result, final_state)"
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
    verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  from hit obtain i trace_openings composition_openings where
    comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and comp_auth:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings final_state"
    and component:
      "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
        A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i ?out"
    unfolding
      checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix_def
    by auto
  have i_bound: "i < rounds"
    using component
    unfolding
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix_def
    by (simp split: option.splits prod.splits)
  show ?thesis
  proof (cases "partial_merkle_inconsistency_bad ?s ?vout")
    case True
    then show ?thesis
      unfolding
        checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad_def
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      by (simp add: Let_def)
  next
    case no_bad: False
    obtain trace_table where trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
      using
        partial_trace_table_candidate_single_witness_if_no_partial_merkle_bad
          [OF trace_auth verifier no_bad i_bound]
      by blast
    obtain composition_table where comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
      using
        partial_composition_table_candidate_single_witness_if_no_partial_merkle_bad
          [OF comp_auth verifier no_bad i_bound]
      by blast
    have pair_hit:
      "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
        A trace_table composition_table i ?out"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix_imp_candidate_pair_query_hit_from_prefix
          [OF component trace_candidate comp_candidate
            trace_low[OF i_bound trace_candidate comp_candidate]
            comp_low[OF i_bound trace_candidate comp_candidate]])
        (rule not_all[OF i_bound trace_candidate comp_candidate])
    then show ?thesis
      using i_bound by blast
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix_imp_actual_partial_merkle_or_single_round_components_on_support:
  assumes support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
        A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    and trace_low:
      "\<And>i trace_openings composition_openings trace_table
          composition_table.
        i < rounds \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        trace_table_low_degree trace_table"
    and comp_low:
      "\<And>i trace_openings composition_openings trace_table
          composition_table.
        i < rounds \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>i trace_openings composition_openings trace_table
          composition_table prefix prefix_state.
        i < rounds \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     (\<exists>i<rounds.
      checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)) \<or>
      checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)))"
proof -
  have split:
    "checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     (\<exists>i trace_table composition_table.
      checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
        A trace_table composition_table i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix_imp_actual_partial_merkle_or_candidate_pair_on_support
        [OF support hit trace_low comp_low not_all])
  then show ?thesis
  proof
    assume
      "checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    then show ?thesis by simp
  next
    assume
      "\<exists>i trace_table composition_table.
        checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
          A trace_table composition_table i
          (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
            result), final_state))"
    then obtain i trace_table composition_table where pair_hit:
      "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
        A trace_table composition_table i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
      by blast
    have i_bound: "i < rounds"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE
          [OF pair_hit])
    have
      "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)) \<or>
       checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_imp_single_round_header_target_or_gap
          [OF pair_hit])
    then show ?thesis
      using i_bound by blast
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix_bound_from_actual_single_round_components:
  fixes PM :: prob and T G :: "nat \<Rightarrow> prob"
  assumes split:
      "\<And>out.
        out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
                A)
              adversary_initial_state) \<Longrightarrow>
        checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
          A out \<Longrightarrow>
        checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
          out \<or>
        (\<exists>i<rounds.
          checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
            i A out \<or>
          checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
            i A out)"
    and partial_merkle_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
        adversary_initial_state \<le> PM"
    and target_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          (checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
            i A)
          adversary_initial_state \<le> T i"
    and gap_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          (checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
            i A)
          adversary_initial_state \<le> G i"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
        A)
      adversary_initial_state \<le>
      PM + (\<Sum>i<rounds. T i + G i)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?auth =
    "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
      A"
  let ?pm =
    "checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad"
  let ?round =
    "\<lambda>i out.
      checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
        i A out \<or>
      checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
        i A out"
  have event_le:
    "wp_event ?M ?auth adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?pm out \<or> (\<exists>i \<in> {..<rounds}. ?round i out))
       adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (use split in auto)
  have union_le:
    "wp_event ?M (\<lambda>out. ?pm out \<or> (\<exists>i \<in> {..<rounds}. ?round i out))
      adversary_initial_state \<le>
     wp_event ?M ?pm adversary_initial_state +
     wp_event ?M (\<lambda>out. \<exists>i \<in> {..<rounds}. ?round i out)
      adversary_initial_state"
    by (rule wp_event_union_bound)
  have round_bound:
    "\<And>i. i \<in> {..<rounds} \<Longrightarrow>
      wp_event ?M (?round i) adversary_initial_state \<le> T i + G i"
  proof -
    fix i
    assume i_bound: "i \<in> {..<rounds}"
    have
      "wp_event ?M (?round i) adversary_initial_state \<le>
       wp_event ?M
        (checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
          i A)
        adversary_initial_state +
       wp_event ?M
        (checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
          i A)
        adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le> T i + G i"
      by (intro add_mono target_bound gap_bound)
        (use i_bound in simp_all)
    finally show "wp_event ?M (?round i) adversary_initial_state \<le> T i + G i" .
  qed
  have rounds_bound:
    "wp_event ?M (\<lambda>out. \<exists>i \<in> {..<rounds}. ?round i out)
      adversary_initial_state \<le> (\<Sum>i<rounds. T i + G i)"
    by (rule wp_event_finite_union_bound)
      (simp_all add: round_bound)
  have
    "wp_event ?M (\<lambda>out. ?pm out \<or> (\<exists>i \<in> {..<rounds}. ?round i out))
      adversary_initial_state \<le> PM + (\<Sum>i<rounds. T i + G i)"
    by (rule order_trans[OF union_le])
      (intro add_mono partial_merkle_bound rounds_bound)
  then show ?thesis
    by (rule order_trans[OF event_le])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_actual_single_round_components_and_budgets:
  fixes PM :: prob and T G :: "nat \<Rightarrow> prob"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and split:
      "\<And>out.
        out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
                A)
              adversary_initial_state) \<Longrightarrow>
        checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
          A out \<Longrightarrow>
        checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
          out \<or>
        (\<exists>i<rounds.
          checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
            i A out \<or>
          checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
            i A out)"
    and partial_merkle_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
        adversary_initial_state \<le> PM"
    and target_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          (checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
            i A)
          adversary_initial_state \<le> T i"
    and gap_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          (checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
            i A)
          adversary_initial_state \<le> G i"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (PM + (\<Sum>i<rounds. T i + G i)) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have authenticated_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
        A)
      adversary_initial_state \<le> PM + (\<Sum>i<rounds. T i + G i)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix_bound_from_actual_single_round_components
        [OF split partial_merkle_bound target_bound gap_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_authenticated_query_from_prefix_and_budgets
        [OF wf controlled authenticated_bound])
qed

end

end
