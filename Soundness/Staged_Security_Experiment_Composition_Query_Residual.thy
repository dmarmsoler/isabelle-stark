(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Residual.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Residual
  imports
    Staged_Security_Experiment_Composition_Partial
    Soundness_Staged_Partial_Query_Branch
    Soundness_Staged_Candidate_Query
begin

text \<open>
  Composition-specific residual split after the alpha-prequery accounting.

  The broad branch-subtree witness event is not rare: honest verifier-side
  Merkle path recomputation can produce such witnesses.  This layer therefore
  splits the actual remaining composition drift event itself into a part
  covered by the sampled partial-opening query event and a residual part that
  is still to be discharged by the Merkle/candidate proof.
\<close>

context soundness
begin

text \<open>
  The existing committed query-prefix targets are based on
  \<^term>\<open>query_sampling_success_space\<close>.  They are suitable for ordinary query
  inconsistency, but not directly for composition randomization witnesses:
  \<^term>\<open>composition_bad_context\<close> already requires all sampled queries to be
  consistent.  Hence the query-sampling success space of the actual
  composition witness is empty, and the composition-drift query case needs a
  narrower candidate-indexed target rather than the global partial-opening
  fixed cover.
\<close>

lemma composition_bad_context_query_sampling_success_space_empty:
  assumes
    "composition_bad_context s out trace_table composition_table as query_idxs f"
  shows "query_sampling_success_space trace_table composition_table as = {}"
proof -
  have all_queries: "all_queries_consistent trace_table composition_table as"
    using assms unfolding composition_bad_context_def by blast
  then show ?thesis
    unfolding query_sampling_success_space_def by simp
qed

lemma composition_randomization_bad_witness_query_sampling_success_space_empty:
  assumes "composition_randomization_bad s out"
  obtains trace_table composition_table as query_idxs f where
    "composition_bad_context s out trace_table composition_table as query_idxs f"
    "common_denominator_degree_bounds f as"
    "random_combination_common_denominator_hides_violations f as"
    "query_sampling_success_space trace_table composition_table as = {}"
  using assms
  unfolding composition_randomization_bad_def
  by (metis composition_bad_context_query_sampling_success_space_empty)

lemma composition_trace_bad_alpha_spaceE:
  assumes bad: "as \<in> composition_trace_bad_alpha_space trace_table"
  obtains f where
    "f = low_degree_trace_witness trace_table"
    "degree f < clength"
    "trace_table = map (poly f) eval_domain"
    "violated_constraints f \<noteq> {}"
    "as \<in> common_denominator_hiding_alpha_space f"
    "common_denominator_degree_bounds f as"
    "trace_table_low_degree trace_table"
proof -
  let ?f = "low_degree_trace_witness trace_table"
  have deg: "degree ?f < clength"
    and trace_table: "trace_table = map (poly ?f) eval_domain"
    and violated: "violated_constraints ?f \<noteq> {}"
    and alpha: "as \<in> common_denominator_hiding_alpha_space ?f"
    and degree_bounds: "common_denominator_degree_bounds ?f as"
    using bad
    unfolding composition_trace_bad_alpha_space_def Let_def
    by (auto split: if_splits)
  have trace_low: "trace_table_low_degree trace_table"
    unfolding trace_table_low_degree_def
    using deg trace_table by blast
  show ?thesis
    by (rule that[OF refl deg trace_table violated alpha degree_bounds
          trace_low])
qed

lemma composition_trace_bad_alpha_space_trace_low_degree:
  assumes "as \<in> composition_trace_bad_alpha_space trace_table"
  shows "trace_table_low_degree trace_table"
  using assms by (elim composition_trace_bad_alpha_spaceE)

definition checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      out \<longleftrightarrow>
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      out \<and>
    checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      out"

definition checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      out \<longleftrightarrow>
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      out \<and>
    \<not> checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      out"

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_imp_drift:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_def
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_imp_not_query_hit:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      out"
  shows
    "\<not> checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_def
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_imp_randomization_bad:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_def
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_imp_partial_header_candidate_drift:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
      composition_trace_bad_alpha_space out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_def
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_imp_partial_header_fresh:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
      composition_trace_bad_alpha_space out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_def
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
    checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_def
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_imp_not_prefix_hit:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      out"
  shows
    "\<not> checked_staged_security_with_actual_alpha_prefix_bad_set_hit
      composition_trace_bad_alpha_space out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_def
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
    checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_def
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hitE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
  obtains
    "alpha_header_list_set_hit
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (alpha_header_supported_partial_union_bad_sets
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        composition_trace_bad_alpha_space)
      (Some (result, final_state))"
    "\<not> alpha_vector_prequeried_in_state prefix_state
      (staged_alphas data) (length spec)"
    "\<not> checked_staged_security_with_actual_alpha_prefix_bad_set_hit
      composition_trace_bad_alpha_space
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
    "\<not> checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
  using hit
  unfolding
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_def
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
    checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_def
    checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit_def
    checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_def
    Let_def
  by auto

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_imp_branch_tree_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      out"
  by (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_imp_branch_tree_on_support
      [OF wf controlled support])
    (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_imp_drift
      [OF hit])

lemma checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support:
  assumes support:
    "Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
  shows
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have projected:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A \<bind> (\<lambda>x. return (?project x)))
          adversary_initial_state)"
    apply (rule set_dist_bindI[OF support])
    apply simp
    done
  then show ?thesis
    using
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
      [of A]
    by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_imp_query_partial_opening_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and bad:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
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
  have staged_header:
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
  from bad obtain trace_table composition_table as query_idxs f where
    ctx:
      "composition_bad_context ?s (Some (result, final_state))
        trace_table composition_table as query_idxs f"
    unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      composition_randomization_bad_def Let_def
    by auto
  have bound:
    "accepted_with_bound_tables ?s (Some (result, final_state))
      trace_table composition_table as query_idxs"
    using ctx unfolding composition_bad_context_def by blast
  have all_queries:
    "all_queries_consistent trace_table composition_table as"
    using ctx unfolding composition_bad_context_def by blast
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as query_idxs"
    using bound
    unfolding accepted_with_bound_tables_def accepted_with_tables_def
    by simp
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled data_support shape]
  obtain raw_idxs where
    as_eq: "as = staged_alphas data"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    and idx_bound:
      "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by blast
  have bound_staged:
    "accepted_with_bound_tables ?s (Some (result, final_state))
      trace_table composition_table (staged_alphas data) query_idxs"
    using bound as_eq by simp
  have all_queries_staged:
    "all_queries_consistent trace_table composition_table
      (staged_alphas data)"
    using all_queries as_eq by simp
  have i_bound: "0 < rounds"
    by (rule rounds_positive)
  have idx_sample:
    "query_idxs ! 0 \<in> query_sample_space"
  proof -
    have len_query_idxs: "length query_idxs = rounds"
      by (rule accepted_with_bound_tables_shapes(4)[OF bound_staged])
    have "query_idxs ! 0 \<in> set query_idxs"
      by (rule nth_mem) (use i_bound len_query_idxs in simp)
    then show ?thesis
      by (rule accepted_with_bound_tables_query_sample_space
          [OF bound_staged])
  qed
  show ?thesis
  proof (rule accepted_with_bound_tables_partial_opening_witnesses_Some
      [OF bound_staged])
    fix fr f_fri_roots f_final dg composition_fri_roots final rest
        trace_openings composition_openings
    assume header:
      "verifier_header_transcript ?s fr f_fri_roots f_final
        (staged_alphas data) dg composition_fri_roots final rest"
      and comp_nonempty: "composition_fri_roots \<noteq> []"
      and trace_partial:
      "accepted_with_partial_trace_openings ?s
        (Some (result, final_state)) fr query_idxs trace_openings"
      and comp_partial:
      "accepted_with_partial_composition_openings ?s
        (Some (result, final_state)) (hd composition_fri_roots)
        query_idxs composition_openings"
      and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
      and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    have header_eq:
      "fr = staged_trace_root data \<and>
       f_fri_roots = staged_trace_fri_roots data \<and>
       f_final = staged_trace_final data \<and>
       dg = staged_degree data \<and>
       composition_fri_roots = staged_composition_fri_roots data \<and>
       final = staged_composition_final data \<and>
       rest = List.concat (staged_query_chunks data)"
      using verifier_header_transcript_unique[OF staged_header header]
      by simp
    have idx_in:
      "query_idxs ! 0 \<in>
        query_header_supported_partial_opening_success_indices_at ?s fr
          f_fri_roots f_final (staged_alphas data) dg
          composition_fri_roots final 0"
      by (rule
          query_header_supported_partial_opening_success_indices_atI_from_partials_consistent
          [OF verifier trace_partial comp_partial trace_candidate
            comp_candidate header comp_nonempty refl i_bound idx_sample
            all_queries_staged])
    have idx_in_staged:
      "query_idxs ! 0 \<in>
        query_header_supported_partial_opening_success_indices_at ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)
          0"
      using idx_in header_eq by simp
    have raw_idx:
      "index (to_nat (raw_idxs ! 0)) = query_idxs ! 0"
      using query_idxs_eq len_raw i_bound by simp
    have hit_at:
      "staged_security_with_data_state_query_partial_opening_hit_at 0
        (Some (((data, attacker_state), result), final_state))"
      unfolding staged_security_with_data_state_query_partial_opening_hit_at_def
      using i_bound lookup[OF i_bound] idx_in_staged raw_idx
      by (simp add: Let_def)
    have hit:
      "staged_security_with_data_state_query_partial_opening_hit
        (Some (((data, attacker_state), result), final_state))"
      by (rule staged_security_with_data_state_query_partial_opening_hitI
          [OF i_bound hit_at])
    show ?thesis
      unfolding
        checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit_def
      using hit by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_false_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
        out"
  shows False
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_def
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state data attacker_state result final_state where
    out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state)"
    by (cases packed, auto split: prod.splits)
  have support_some:
    "Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
    using support unfolding out_eq .
  have random_bad:
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
    using hit unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_def
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
    by simp
  have query_hit:
    "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_imp_query_partial_opening_hit_on_support
        [OF wf controlled support_some random_bad])
  have not_query:
    "\<not> checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
    using hit unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_def
    by simp
  show ?thesis
    using query_hit not_query by contradiction
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le> 0"
proof -
  have
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (\<lambda>_. False)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (use
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_false_on_support
        [OF wf controlled] in blast)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_imp_query_or_without_query:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      out \<or>
     checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_def
  by blast

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_query_hit:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_branch_tree_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      out"
proof -
  have drift:
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      out"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
    by simp
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_imp_branch_tree_on_support
        [OF wf controlled support drift])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_branch_tree:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and branch_tree_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
        adversary_initial_state \<le> T"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> T"
proof -
  have
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_branch_tree_on_support
        [OF wf controlled])
  then show ?thesis
    by (rule order_trans[OF _ branch_tree_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_driftE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
  obtains s where
    "s = verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
    "composition_randomization_bad s (Some (result, final_state))"
    "alpha_header_list_set_hit s
      (alpha_header_supported_partial_union_bad_sets s
        composition_trace_bad_alpha_space)
      (Some (result, final_state))"
    "\<not> staged_alphas data \<in>
      alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space (fst prefix)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have random_bad:
    "composition_randomization_bad ?s (Some (result, final_state))"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      Let_def
    by simp
  have header_hit:
    "alpha_header_list_set_hit ?s
      (alpha_header_supported_partial_union_bad_sets ?s
        composition_trace_bad_alpha_space)
      (Some (result, final_state))"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_def
      checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit_def
      checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_def
      Let_def
    by simp
  have not_prefix:
    "\<not> staged_alphas data \<in>
      alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space (fst prefix)"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_def
      checked_staged_security_with_actual_alpha_prefix_bad_set_hit_def
      Let_def
    by simp
  show ?thesis
    by (rule that[OF refl random_bad header_hit not_prefix])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hitE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
  obtains s where
    "s = verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
    "composition_randomization_bad s (Some (result, final_state))"
    "alpha_header_list_set_hit s
      (alpha_header_supported_partial_union_bad_sets s
        composition_trace_bad_alpha_space)
      (Some (result, final_state))"
    "\<not> staged_alphas data \<in>
      alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space (fst prefix)"
    "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
proof -
  have drift:
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
    by simp
  have query_hit:
    "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
    by simp
  from checked_staged_security_with_actual_alpha_prefix_composition_candidate_driftE
      [OF drift]
  obtain s where
    s_def:
      "s = verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    and random_bad:
      "composition_randomization_bad s (Some (result, final_state))"
    and header_hit:
      "alpha_header_list_set_hit s
        (alpha_header_supported_partial_union_bad_sets s
          composition_trace_bad_alpha_space)
        (Some (result, final_state))"
    and not_prefix:
      "\<not> staged_alphas data \<in>
        alpha_prefix_union_bad_sets prefix_state
          composition_trace_bad_alpha_space (fst prefix)"
    by blast
  show ?thesis
    by (rule that[OF s_def random_bad header_hit not_prefix query_hit])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_supportedE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  obtains s trace_table where
    "s = verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
    "composition_randomization_bad s (Some (result, final_state))"
    "staged_alphas data \<in>
      alpha_header_supported_partial_union_bad_sets s
        composition_trace_bad_alpha_space
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)"
    "trace_table \<in>
      alpha_header_supported_partial_trace_table_candidates s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)"
    "staged_alphas data \<in> composition_trace_bad_alpha_space trace_table"
    "\<not> staged_alphas data \<in>
      alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space (fst prefix)"
    "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hitE
      [OF hit]
  have random_bad:
      "composition_randomization_bad ?s (Some (result, final_state))"
    and header_list_hit:
      "alpha_header_list_set_hit ?s
        (alpha_header_supported_partial_union_bad_sets ?s
          composition_trace_bad_alpha_space)
        (Some (result, final_state))"
    and not_prefix:
      "\<not> staged_alphas data \<in>
        alpha_prefix_union_bad_sets prefix_state
          composition_trace_bad_alpha_space (fst prefix)"
    and query_hit:
      "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
    by blast+
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
  have staged_header:
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
  from header_list_hit obtain as query_idxs fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    shape: "accepted_transcript_shape ?s (Some (result, final_state))
        as query_idxs"
    and header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and as_bad:
      "as \<in> alpha_header_supported_partial_union_bad_sets ?s
        composition_trace_bad_alpha_space fr f_fri_roots f_final"
    unfolding alpha_header_list_set_hit_def by blast
  have header_eq:
    "fr = staged_trace_root data \<and>
     f_fri_roots = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     composition_fri_roots = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  have staged_bad:
    "staged_alphas data \<in>
      alpha_header_supported_partial_union_bad_sets ?s
        composition_trace_bad_alpha_space
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)"
    using as_bad header_eq by simp
  from staged_bad obtain trace_table where trace_candidate:
      "trace_table \<in>
        alpha_header_supported_partial_trace_table_candidates ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)"
    and trace_bad:
      "staged_alphas data \<in> composition_trace_bad_alpha_space trace_table"
    unfolding alpha_header_supported_partial_union_bad_sets_def by blast
  show ?thesis
    by (rule that[OF refl random_bad staged_bad trace_candidate trace_bad
          not_prefix query_hit])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_supported_openingsE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  obtains s trace_table i raw trace_openings composition_openings where
    "s = verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
    "composition_randomization_bad s (Some (result, final_state))"
    "trace_table \<in>
      alpha_header_supported_partial_trace_table_candidates s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)"
    "staged_alphas data \<in> composition_trace_bad_alpha_space trace_table"
    "\<not> staged_alphas data \<in>
      alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space (fst prefix)"
    "i < rounds"
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some raw"
    "index (to_nat raw) \<in> query_sample_space"
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    "partial_query_openings_consistent trace_openings composition_openings
      (staged_alphas data) (index (to_nat raw))"
proof -
  from checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_supportedE
      [OF wf controlled support hit]
  obtain s trace_table where
    s_def:
      "s = verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    and random_bad:
      "composition_randomization_bad s (Some (result, final_state))"
    and trace_candidate:
      "trace_table \<in>
        alpha_header_supported_partial_trace_table_candidates s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)"
    and trace_bad:
      "staged_alphas data \<in> composition_trace_bad_alpha_space trace_table"
    and not_prefix:
      "\<not> staged_alphas data \<in>
        alpha_prefix_union_bad_sets prefix_state
          composition_trace_bad_alpha_space (fst prefix)"
    and query_hit:
      "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
    by blast
  from checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hitE
      [OF query_hit]
  obtain i raw trace_openings composition_openings where
    i_bound: "i < rounds"
    and lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
        Some raw"
    and idx_sample: "index (to_nat raw) \<in> query_sample_space"
    and witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
    by blast
  have witness_s:
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    using witness s_def by simp
  show ?thesis
    by (rule that[OF s_def random_bad trace_candidate trace_bad not_prefix
          i_bound lookup idx_sample witness_s consistent])
qed

definition checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit
  :: "('f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool)"
where
  "checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit
      A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (\<exists>i trace_openings composition_openings.
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
            ((replicate rounds []) [i := trace_openings])
            ((replicate rounds []) [i := composition_openings])
            (staged_alphas data) i
            (Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state))))"

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hitI:
  assumes component:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      (staged_alphas data) i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
proof -
  have
    "\<exists>j trace_openings' composition_openings'.
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
        ((replicate rounds []) [j := trace_openings'])
        ((replicate rounds []) [j := composition_openings'])
        (staged_alphas data) j
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
          final_state))"
    by (intro exI[of _ i] exI[of _ trace_openings]
        exI[of _ composition_openings])
      (rule component)
  then show ?thesis
    unfolding
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit_def
    by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_hit:
  assumes query_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> Q"
  by (rule order.trans[OF _ query_bound])
    (rule wp_event_mono,
      rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_query_hit)

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_query_and_without_query:
  assumes query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        adversary_initial_state \<le> Q"
    and without_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
        adversary_initial_state \<le> W"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> Q + W"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Drift =
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift"
  let ?Query =
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit"
  let ?Without =
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit"
  have "wp_event ?M ?Drift adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?Query out \<or> ?Without out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_imp_query_or_without_query)
  also have "... \<le>
      wp_event ?M ?Query adversary_initial_state +
      wp_event ?M ?Without adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> Q + W"
    by (intro add_mono query_bound without_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_composition_candidate_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
        adversary_initial_state \<le> D"
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
      D +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Prefix =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  let ?Pre =
    "staged_phase_relation_error size
      (staged_alpha_search_queries budgets 0)"
  let ?Coll =
    "hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget)"
  have transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?Prefix"
    by (rule
        checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets
        [OF wf controlled])
  have prefix_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?Prefix"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have prequery_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?Pre"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_vector_alpha_prequery_accounting
        [OF wf controlled])
  have collision_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state \<le> ?Coll"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  let ?degree =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_degree_bad"
  let ?random =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad"
  let ?bad =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_bad"
  have projected:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state =
     wp_event ?M ?bad adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection)
  have event_eq: "?bad = (\<lambda>out. ?degree out \<or> ?random out)"
    by (rule ext)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        composition_bad_def split: option.splits prod.splits)
  have degree_false: "?degree = (\<lambda>out. False)"
    by (rule ext)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        composition_degree_bad_false[OF spec_degree_wellformed_from_spec_query_margin]
        split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    unfolding degree_false wp_event_def wp_def dist_expect_def by simp
  have random_bound:
    "wp_event ?M ?random adversary_initial_state \<le>
      ?Prefix + ?Pre + D + ?Coll"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_bound_from_prefix_prequery_drift_and_collision
        [OF prefix_bound prequery_bound drift_bound collision_bound])
  have "wp_event ?M ?bad adversary_initial_state \<le>
      wp_event ?M ?degree adversary_initial_state +
      wp_event ?M ?random adversary_initial_state"
    unfolding event_eq by (rule wp_event_union_bound)
  also have "... \<le> 0 + (?Prefix + ?Pre + D + ?Coll)"
    by (intro add_mono degree_bound random_bound)
  finally show ?thesis
    unfolding projected by (simp add: add.assoc)
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_partial_opening_hit_and_budgets:
  fixes query_error :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and partial_opening_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_opening_hit
        adversary_initial_state \<le> query_error"
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
      (query_error + 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  have query_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      adversary_initial_state \<le> query_error"
    unfolding
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit_projection
    by (rule partial_opening_bound)
  have drift_query_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> query_error"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_hit
        [OF query_bound])
  have without_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le> 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_bound
        [OF wf controlled])
  have drift_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> query_error + 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_query_and_without_query
        [OF drift_query_bound without_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_composition_candidate_drift_and_budgets
        [OF wf controlled drift_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_partial_query_residual_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
    "\<And>data attacker_state i.
      i < rounds \<Longrightarrow>
      query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<subseteq> B"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
    and residual_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
        adversary_initial_state \<le> R"
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
      (nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound + R) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?QueryCost =
    "nnreal
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget) * query_error_bound"
  have query_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      adversary_initial_state \<le> ?QueryCost"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit_bound_from_fixed_query_error_cover
        [OF wf controlled cover raw_bound subset frac])
  have drift_query_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> ?QueryCost"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_hit
        [OF query_bound])
  have drift_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> ?QueryCost + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_query_and_without_query
        [OF drift_query_bound residual_bound])
  have
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
      (?QueryCost + R) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_composition_candidate_drift_and_budgets
        [OF wf controlled drift_bound])
  then show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_partial_query_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
    "\<And>data attacker_state i.
      i < rounds \<Longrightarrow>
      query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<subseteq> B"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
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
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have residual_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le> 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_bound
        [OF wf controlled])
  have
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
      (nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound + 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_partial_query_residual_and_budgets
        [OF wf controlled cover raw_bound subset frac residual_bound])
  then show ?thesis
    by simp
qed

end

end
