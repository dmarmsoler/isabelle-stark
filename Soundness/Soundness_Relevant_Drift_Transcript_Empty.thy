(*  Title:      Stark/Soundness_Relevant_Drift_Transcript_Empty.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Relevant_Drift_Transcript_Empty
  imports
    Soundness_Relevant_Drift_Query_Agreement
    Soundness_Query_Transcript_Openings
begin

text \<open>
  Transcript-indexed empty-header packaging.

  This layer avoids the broad empty-header composition residual whose
  authenticated-opening witnesses carry existential query indices.  The
  composition branch instead carries the verifier transcript shape, so later
  query-agreement bounds can use verifier-derived query indices.
\<close>

context soundness
begin

definition soundness_bad_event_partial_candidate_empty_header_transcript
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "soundness_bad_event_partial_candidate_empty_header_transcript s out
    \<longleftrightarrow>
    composition_bad_with_empty_composition_header_candidates_transcript
      s out \<or>
    trace_fri_bad_with_empty_composition_header_candidates s out \<or>
    query_bad_with_empty_composition_header_candidates s out"

lemma accepted_empty_composition_header_candidate_partition_transcript:
  assumes false_statement: "\<not> exists_valid_trace"
    and partial:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and shape: "accepted_transcript_shape s out as trace_query_idxs"
  shows "soundness_bad_event_partial_candidate_empty_header_transcript s out"
proof (cases "trace_table_low_degree trace_table")
  case False
  have "trace_fri_bad_with_empty_composition_header_candidates s out"
    unfolding trace_fri_bad_with_empty_composition_header_candidates_def
    using partial False by blast
  then show ?thesis
    unfolding soundness_bad_event_partial_candidate_empty_header_transcript_def
    by blast
next
  case True
  note trace_low = True
  have composition_low:
    "composition_table_low_degree maxDegree composition_table"
  proof -
    have "composition_table = replicate (scale * clength) final"
      using partial
      unfolding accepted_with_empty_composition_header_candidates_def by simp
    then show ?thesis
      using constant_composition_table_low_degree by simp
  qed
  show ?thesis
  proof (cases "all_queries_consistent trace_table composition_table as")
    case False
    have "query_bad_with_empty_composition_header_candidates s out"
      unfolding query_bad_with_empty_composition_header_candidates_def
      using partial trace_low composition_low False by blast
    then show ?thesis
      unfolding soundness_bad_event_partial_candidate_empty_header_transcript_def
      by blast
  next
    case True
    note all_queries = True
    from trace_low obtain f where
      deg_f: "degree f < clength"
      and trace_table_eq: "trace_table = map (poly f) eval_domain"
      unfolding trace_table_low_degree_def by blast
    have violated: "violated_constraints f \<noteq> {}"
      by (rule false_statement_violated_constraints
          [OF false_statement deg_f])
    have "composition_bad_with_empty_composition_header_candidates_transcript
        s out"
      unfolding composition_bad_with_empty_composition_header_candidates_transcript_def
      using partial shape deg_f trace_table_eq violated composition_low
        all_queries
      by blast
    then show ?thesis
      unfolding soundness_bad_event_partial_candidate_empty_header_transcript_def
      by blast
  qed
qed

lemma accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_or_empty_header_transcript_from_partial_trace_openings:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
    and shape: "accepted_transcript_shape s out as query_idxs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and trace_partial_if_empty:
      "composition_fri_roots = [] \<Longrightarrow>
        accepted_with_partial_trace_openings s out fr query_idxs
          trace_openings"
  shows
    "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
        s out \<or>
     soundness_bad_event_partial_candidate_empty_header_transcript s out"
proof (cases "composition_fri_roots = []")
  case False
  then have comp_nonempty: "composition_fri_roots \<noteq> []"
    by simp
  have
    "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
      s out"
    by (rule
        accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_if_header_nonempty
        [OF false_statement supp acc header comp_nonempty])
  then show ?thesis by simp
next
  case True
  note comp_empty = True
  from acc obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  have trace_partial:
    "accepted_with_partial_trace_openings s (Some (result, final_state))
      fr query_idxs trace_openings"
    using trace_partial_if_empty[OF comp_empty] unfolding out_eq .
  show ?thesis
  proof (cases
      "partial_merkle_inconsistency_bad s (Some (result, final_state))")
    case True
    then have
      "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
        s out"
      unfolding out_eq
        soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_def
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
        (use accepted_out header comp_empty trace_partial trace_candidate
          in simp_all)
    have "soundness_bad_event_partial_candidate_empty_header_transcript s
        (Some (result, final_state))"
      by (rule accepted_empty_composition_header_candidate_partition_transcript
          [OF false_statement empty_partial shape[unfolded out_eq]])
    then show ?thesis
      unfolding out_eq by simp
  qed
qed

lemma accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_or_empty_header_transcript:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  shows
    "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
        s out \<or>
     soundness_bad_event_partial_candidate_empty_header_transcript s out"
proof (cases "composition_fri_roots = []")
  case False
  then have comp_nonempty: "composition_fri_roots \<noteq> []"
    by simp
  have
    "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
      s out"
    by (rule
        accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_if_header_nonempty
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
      "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
        s out"
      unfolding out_eq
        soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_def
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

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_transcript_imp_prefix_prequery_or_empty_relevant_drift_transcript_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header_transcript
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
        out"
proof -
  have broad_hit:
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header out"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
    by (auto split: option.splits prod.splits
        intro:
          composition_alpha_partial_opening_union_hit_with_empty_header_transcript_imp_union_hit)
  have partial:
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      composition_trace_bad_alpha_space out"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_partial_alpha_hit_imp_partial_header_bad_set_hit_on_support
        [OF support broad_hit])
  have fresh_or_prequery:
    "checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space out"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_imp_fresh_or_prequery
        [OF partial])
  then show ?thesis
  proof
    assume fresh:
      "checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
        composition_trace_bad_alpha_space out"
    have prefix_or_drift:
      "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space out \<or>
       checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space out"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit_imp_prefix_or_drift
          [OF fresh])
    then show ?thesis
    proof
      assume
        "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space out"
      then show ?thesis by simp
    next
      assume drift:
        "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space out"
      have
        "checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
          out"
        unfolding
          checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_def
        using drift hit by simp
      then show ?thesis by simp
    qed
  next
    assume
      "checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space out"
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_transcript_bound_from_empty_relevant_drift_transcript_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
        adversary_initial_state \<le> D"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header_transcript)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Prefix =
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
      composition_trace_bad_alpha_space"
  let ?Prequery =
    "checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
      composition_trace_bad_alpha_space"
  let ?Drift =
    "checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript"
  let ?Hit =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header_transcript"
  let ?P =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  let ?Q =
    "staged_phase_relation_error size
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
    "wp_event ?M ?Prefix adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have prequery_bound:
    "wp_event ?M ?Prequery adversary_initial_state \<le> ?Q"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_vector_alpha_prequery_accounting
        [OF wf controlled])
  have event_le:
    "wp_event ?M ?Hit adversary_initial_state \<le>
     wp_event ?M
      (\<lambda>out. ?Prefix out \<or> ?Prequery out \<or> ?Drift out \<or> False)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (use
        checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_transcript_imp_prefix_prequery_or_empty_relevant_drift_transcript_on_support
          [of _ A] in blast)
  also have "... \<le>
      wp_event ?M ?Prefix adversary_initial_state +
      wp_event ?M ?Prequery adversary_initial_state +
      wp_event ?M ?Drift adversary_initial_state +
      wp_event ?M (\<lambda>_. False) adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le> ?P + ?Q + D + 0"
    by (intro add_mono prefix_bound prequery_bound drift_bound)
      (simp add: wp_event_def wp_def dist_expect_def)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_data_state_empty_header_composition_randomization_transcript_bound_from_empty_relevant_drift_transcript_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
        adversary_initial_state \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_empty_composition_header_candidates_transcript)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?random =
    "staged_security_with_data_state_verifier_event
      composition_randomization_bad_with_empty_composition_header_candidates_transcript"
  let ?alpha =
    "staged_security_with_data_state_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header_transcript"
  have alpha_projected:
    "wp_event ?M ?alpha adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header_transcript)
      adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection)
  have alpha_bound:
    "wp_event ?M ?alpha adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D"
    unfolding alpha_projected
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_transcript_bound_from_empty_relevant_drift_transcript_and_budgets
        [OF wf controlled drift_bound])
  have "wp_event ?M ?random adversary_initial_state \<le>
      wp_event ?M ?alpha adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_randomization_bad_with_empty_composition_header_candidates_transcript_imp_alpha_union_hit
        split: option.splits prod.splits)
  also have "... \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D"
    by (rule alpha_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_empty_header_bad_event_transcript_bound_from_empty_relevant_drift_transcript_trace_fri_and_query:
  fixes empty_trace_fri_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
        adversary_initial_state \<le> D"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> empty_trace_fri_error"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> empty_query_error"
  shows
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
      D + empty_trace_fri_error + empty_query_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?degree =
    "?E composition_degree_bad_with_empty_composition_header_candidates_transcript"
  let ?random =
    "?E composition_randomization_bad_with_empty_composition_header_candidates_transcript"
  let ?trace =
    "?E trace_fri_bad_with_empty_composition_header_candidates"
  let ?query =
    "?E query_bad_with_empty_composition_header_candidates"
  let ?bad =
    "?E soundness_bad_event_partial_candidate_empty_header_transcript"
  have degree_false: "?degree = (\<lambda>out. False)"
    by (rule ext)
      (auto simp: staged_security_with_data_state_verifier_event_def
        composition_degree_bad_with_empty_composition_header_candidates_transcript_false
        split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    unfolding degree_false wp_event_def wp_def dist_expect_def by simp
  have random_bound:
    "wp_event ?M ?random adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D"
    by (rule
        checked_staged_security_with_data_state_empty_header_composition_randomization_transcript_bound_from_empty_relevant_drift_transcript_and_budgets
        [OF wf controlled drift_bound])
  have "wp_event ?M ?bad adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?degree out \<or> ?random out \<or> ?trace out \<or>
          ?query out)
        adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume bad: "?bad out"
    show "?degree out \<or> ?random out \<or> ?trace out \<or> ?query out"
    proof (cases out)
      case None
      then show ?thesis
        using bad
        unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      have local_bad:
        "soundness_bad_event_partial_candidate_empty_header_transcript ?s
          (Some (result, final_state))"
        using bad
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
      then consider
          (comp)
            "composition_bad_with_empty_composition_header_candidates_transcript ?s
              (Some (result, final_state))"
        | (trace)
            "trace_fri_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state))"
        | (query)
            "query_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state))"
        unfolding
          soundness_bad_event_partial_candidate_empty_header_transcript_def
        by blast
      then show ?thesis
      proof cases
        case comp
        then have comp_split:
          "composition_degree_bad_with_empty_composition_header_candidates_transcript
              ?s (Some (result, final_state)) \<or>
           composition_randomization_bad_with_empty_composition_header_candidates_transcript
              ?s (Some (result, final_state))"
          by (rule
              composition_bad_with_empty_composition_header_candidates_transcript_split
              [OF false_statement])
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          using comp_split by (auto split: option.splits prod.splits)
      next
        case trace
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          by simp
      next
        case query
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          by simp
      qed
    qed
  qed
  also have "... \<le>
      wp_event ?M ?degree adversary_initial_state +
      wp_event ?M ?random adversary_initial_state +
      wp_event ?M ?trace adversary_initial_state +
      wp_event ?M ?query adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le>
      0 +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        D) +
      empty_trace_fri_error + empty_query_error"
    by (intro add_mono degree_bound random_bound trace_fri_bound query_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_and_empty_header_transcript_bounds:
  fixes partial_candidate_error empty_header_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and partial_candidate_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle)
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
    "?E soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle"
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
        "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
            ?s (Some (result, final_state)) \<or>
         soundness_bad_event_partial_candidate_empty_header_transcript ?s
            (Some (result, final_state))"
        by (rule
            accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_or_empty_header_transcript
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

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_relevant_drift_transcript:
  fixes trace_fri_error' composition_fri_error' query_error D E
    empty_trace_fri_error
    empty_query_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_fri_error'"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_aligned_transcript_partial_candidates)
        adversary_initial_state \<le> query_error"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
    and empty_drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
        adversary_initial_state \<le> E"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> empty_trace_fri_error"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
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
      D) +
    trace_fri_error' + composition_fri_error' +
    query_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      E + empty_trace_fri_error + empty_query_error)"
proof -
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_bad_with_partial_candidates)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D"
    by (rule
        checked_staged_security_with_data_state_partial_candidate_composition_bad_bound_from_relevant_drift_and_budgets
        [OF false_statement wf controlled drift_bound])
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
      E + empty_trace_fri_error + empty_query_error"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_transcript_bound_from_empty_relevant_drift_transcript_trace_fri_and_query
        [OF false_statement wf controlled empty_drift_bound
          empty_trace_fri_bound empty_query_bound])
  have partial_candidate_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle)
      adversary_initial_state \<le>
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
        D) +
      trace_fri_error' + composition_fri_error' + query_error"
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_partial_candidate_with_partial_merkle_component_union_bound
        [OF merkle_bound comp_bound trace_fri_bound comp_fri_bound
          query_bound])
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      (hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        D) +
      trace_fri_error' + composition_fri_error' + query_error) +
      (composition_error_bound +
        staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      E + empty_trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_and_empty_header_transcript_bounds
        [OF false_statement partial_candidate_bound empty_header_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_relevant_drift_only:
  fixes trace_fri_error' composition_fri_error' query_error D
    empty_trace_fri_error empty_query_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_fri_error'"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_aligned_transcript_partial_candidates)
        adversary_initial_state \<le> query_error"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> empty_trace_fri_error"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
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
      D) +
    trace_fri_error' + composition_fri_error' +
    query_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + empty_trace_fri_error + empty_query_error)"
proof -
  have empty_drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      adversary_initial_state \<le> D"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_bound_from_relevant_drift
        [OF drift_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_relevant_drift_transcript
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound drift_bound empty_drift_bound empty_trace_fri_bound
          current_empty_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_bound_from_reachable_trace_fri_and_query_agreement:
  fixes F L :: prob
  assumes trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and fixed_empty_alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and low_degree_query_agreement_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit)
        adversary_initial_state \<le> L"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      adversary_initial_state \<le> F + (trace_fri_error + L)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?trace =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      trace_fri_bad_with_empty_composition_header_candidates"
  let ?low_degree_transcript =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit"
  let ?low_degree =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit"
  have trace_data_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have trace_bound:
    "wp_event ?M ?trace adversary_initial_state \<le> trace_fri_error"
    using trace_data_bound
      checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection
        [of A trace_fri_bad_with_empty_composition_header_candidates]
    by simp
  have low_degree_transcript_bound:
    "wp_event ?M ?low_degree_transcript adversary_initial_state \<le> L"
  proof (rule order_trans)
    show "wp_event ?M ?low_degree_transcript adversary_initial_state \<le>
      wp_event ?M ?low_degree adversary_initial_state"
      by (rule wp_event_mono)
        (auto simp: checked_staged_security_with_actual_alpha_prefix_verifier_event_def
          intro:
            empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_imp_query_agreement
          split: option.splits prod.splits)
    show "wp_event ?M ?low_degree adversary_initial_state \<le> L"
      by (rule low_degree_query_agreement_bound)
  qed
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_bound_from_fixed_trace_fri_and_low_degree_transcript
        [OF fixed_empty_alpha_bound trace_bound low_degree_transcript_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_bound_from_reachable_trace_fri_and_pair_union:
  fixes F :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and fixed_empty_alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      adversary_initial_state \<le>
      F + (trace_fri_error + low_degree_trace_pair_agreement_error budgets)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  have trace_data_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have trace_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    using trace_data_bound
      checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection
        [of A trace_fri_bad_with_empty_composition_header_candidates]
    by simp
  have low_degree_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit)
      adversary_initial_state \<le>
      low_degree_trace_pair_agreement_error budgets"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_low_degree_transcript_query_agreement_bound
        [OF wf controlled])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_bound_from_fixed_trace_fri_and_low_degree_transcript
        [OF fixed_empty_alpha_bound trace_bound low_degree_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_reachable_empty_drift_transcript:
  fixes trace_fri_error' composition_fri_error' query_error D F L
    empty_query_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_fri_error'"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_aligned_transcript_partial_candidates)
        adversary_initial_state \<le> query_error"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and fixed_empty_alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and low_degree_query_agreement_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit)
        adversary_initial_state \<le> L"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
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
      D) +
    trace_fri_error' + composition_fri_error' +
    query_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (F + (trace_fri_error + L)) + trace_fri_error +
      empty_query_error)"
proof -
  have empty_drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      adversary_initial_state \<le> F + (trace_fri_error + L)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_bound_from_reachable_trace_fri_and_query_agreement
        [OF trace_fri_reduction fixed_empty_alpha_bound
          low_degree_query_agreement_bound])
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_relevant_drift_transcript
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound drift_bound empty_drift_bound empty_trace_fri_bound
          current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_reachable_empty_drift_transcript_pair_union:
  fixes trace_fri_error' composition_fri_error' query_error D F
    empty_query_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_fri_error'"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_aligned_transcript_partial_candidates)
        adversary_initial_state \<le> query_error"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
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
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D) +
    trace_fri_error' + composition_fri_error' +
    query_error +
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
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_relevant_drift_transcript
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound drift_bound empty_drift_bound empty_trace_fri_bound
          current_empty_bound])
qed

theorem stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_query_agreement:
  fixes D F L empty_query_error :: prob
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
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
    and fixed_empty_alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and low_degree_query_agreement_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit)
        adversary_initial_state \<le> L"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
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
      D) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (F + (trace_fri_error + L)) + trace_fri_error +
      empty_query_error)"
proof -
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
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_reachable_empty_drift_transcript
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound drift_bound trace_fri_reduction fixed_empty_alpha_bound
          low_degree_query_agreement_bound current_empty_bound])
qed

theorem stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_pair_union:
  fixes D F empty_query_error :: prob
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
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
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
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D) +
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
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_reachable_empty_drift_transcript_pair_union
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound drift_bound trace_fri_reduction fixed_empty_alpha_bound
          current_empty_bound])
qed

theorem stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_relevant_drift_only:
  fixes D empty_query_error :: prob
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
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
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
      D) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error)"
proof -
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
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_relevant_drift_only
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound drift_bound empty_trace_fri_bound current_empty_bound])
qed

theorem stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_not_prefix_query_agreement:
  fixes D N L empty_query_error :: prob
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
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> N"
    and low_degree_query_agreement_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit)
        adversary_initial_state \<le> L"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
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
      D) +
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
        (trace_fri_error + L)) +
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
        stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_query_agreement
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound drift_bound
          fixed_empty_alpha_bound low_degree_query_agreement_bound
          current_empty_bound])
qed

theorem stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_not_prefix_pair_union:
  fixes D N empty_query_error :: prob
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
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
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
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D) +
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
        (trace_fri_error + low_degree_trace_pair_agreement_error budgets)) +
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
        stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_pair_union
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound drift_bound
          fixed_empty_alpha_bound current_empty_bound])
qed

theorem stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_from_not_prefix_relevant_drift_only:
  fixes D N empty_query_error :: prob
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
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
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
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error)"
  by (rule
      stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_relevant_drift_only
      [OF false_statement wf controlled trace_fri_reduction
        composition_fri_reduction round_bound drift_bound
        current_empty_bound])

theorem stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_cross_data_pre_witness_new_query_agreement:
  fixes X P R L empty_query_error :: prob
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
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and witness_new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> R"
    and low_degree_query_agreement_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit)
        adversary_initial_state \<le> L"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
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
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R))) +
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
          (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R))) +
        (trace_fri_error + L)) +
      trace_fri_error + empty_query_error)"
proof -
  let ?D =
    "hash_collision_budget_value 0
      (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R)"
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le> ?D"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_cross_data_pre_and_witness_new
        [OF wf controlled cross_bound data_pre_bound witness_new_bound])
  have transcript_pre_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      adversary_initial_state \<le> P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_bound_from_data_state_pre_hit
        [OF data_pre_bound])
  have witness_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new
        [OF transcript_pre_bound witness_new_bound])
  have no_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le> P + R"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_le_witness_transcript_hit
          witness_bound])
  have path_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le> P + R"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_le_witness_transcript_hit
          witness_bound])
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
  have uncovered_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      adversary_initial_state \<le> X"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_witnessed_cross_or_merkle_bad
          cross_bound])
  have not_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?D"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_bound])
  show ?thesis
    by (rule
        stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_not_prefix_query_agreement
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound drift_bound not_prefix_bound
          low_degree_query_agreement_bound current_empty_bound])
qed

theorem stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_cross_data_pre_witness_new_pair_union:
  fixes X P R empty_query_error :: prob
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
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and witness_new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> R"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
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
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R))) +
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
          (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R))) +
        (trace_fri_error + low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  let ?D =
    "hash_collision_budget_value 0
      (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R)"
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le> ?D"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_cross_data_pre_and_witness_new
        [OF wf controlled cross_bound data_pre_bound witness_new_bound])
  have transcript_pre_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      adversary_initial_state \<le> P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_bound_from_data_state_pre_hit
        [OF data_pre_bound])
  have witness_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new
        [OF transcript_pre_bound witness_new_bound])
  have no_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le> P + R"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_le_witness_transcript_hit
          witness_bound])
  have path_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le> P + R"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_le_witness_transcript_hit
          witness_bound])
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
  have uncovered_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      adversary_initial_state \<le> X"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_witnessed_cross_or_merkle_bad
          cross_bound])
  have not_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?D"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_bound])
  show ?thesis
    by (rule
        stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_not_prefix_pair_union
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound drift_bound not_prefix_bound
          current_empty_bound])
qed

(*
Unused scaffold: this wrapper attempted to replace the current-empty bound by an
empty-residual bound directly.  The validated public path below continues to use
the current-empty theorem family; the empty-residual infrastructure remains in
Soundness_Conceptual_Query_Empty_Current.
theorem stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_empty_residual_reachable_fri_split_empty_header_from_drift_cross_data_pre_sampled_transcript_pair_union:
  fixes D X P E :: prob
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
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and empty_residual0:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A 0)
        (checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
          0)
        adversary_initial_state \<le> E"
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
      D) +
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
          (staged_alpha_search_queries budgets 0) + X +
          (P + staged_concrete_transcript_target_error_bound) +
          (P + staged_concrete_transcript_target_error_bound))) +
        (trace_fri_error + low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error +
      (staged_phase_relation_error size
        (staged_query_search_queries budgets 0 + 1) +
       query_error_bound + E +
       (P + staged_concrete_transcript_target_error_bound)))"
proof -
  have transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have zero_lt: "0 < rounds"
    by (simp add: rounds_positive)
  have current_empty_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets 0 + 1) +
      query_error_bound + E +
      (P + staged_concrete_transcript_target_error_bound)"
  proof (rule
        checked_staged_security_with_data_state_current_empty_query_opening_hit_at_bound_from_conceptual_empty_residual_and_transcript
        [where budgets=budgets and A=A and i=0 and E=E and P=P
          and R=staged_concrete_transcript_target_error_bound])
    show "staged_budget_wellformed budgets"
      by (fact wf)
    show "staged_adversary_controlled budgets A"
      by (fact controlled)
    show "0 < rounds"
      by (fact zero_lt)
    show "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A 0)
      (checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
        0)
      adversary_initial_state \<le> E"
      by (fact empty_residual0)
    show "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_pre_hit
      adversary_initial_state \<le> P"
      by (fact data_pre_bound)
    show "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit adversary_initial_state
      \<le> staged_concrete_transcript_target_error_bound"
      by (fact transcript_new_bound)
  qed
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
  have uncovered_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      adversary_initial_state \<le> X"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_witnessed_cross_or_merkle_bad
          cross_bound])
  have not_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (staged_alpha_search_queries budgets 0) +
      X + (P + staged_concrete_transcript_target_error_bound) +
      (P + staged_concrete_transcript_target_error_bound)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_bound])
  show ?thesis
    by (rule
        stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_not_prefix_pair_union
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound drift_bound not_prefix_bound
          current_empty_bound])
qed
*)

end

text \<open>
  These transcript-empty wrappers expose the broad witnessed cross/Merkle
  diagnostic event directly.  They are retained only for internal comparison
  with the sampled-transcript route and are not part of the exported public
  path.
\<close>

hide_fact
  soundness.stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_query_agreement
  soundness.stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_pair_union
  soundness.stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_relevant_drift_only
  soundness.stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_not_prefix_query_agreement
  soundness.stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_not_prefix_pair_union
  soundness.stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_from_not_prefix_relevant_drift_only
  soundness.stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_cross_data_pre_witness_new_query_agreement
  soundness.stark_soundness_from_aligned_transcript_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_cross_data_pre_witness_new_pair_union

end
