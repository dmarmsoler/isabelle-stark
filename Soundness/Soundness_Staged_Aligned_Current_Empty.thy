(*  Title:      Stark/Soundness_Staged_Aligned_Current_Empty.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Aligned_Current_Empty
  imports
    Soundness_Conceptual_Query_Current_Alpha_Clean
    Soundness_Staged_Aligned_Partial_Merkle
begin

text \<open>
  Packaging for the aligned-transcript partial-candidate path with the
  current-empty query bound.  This combines the current-query non-empty branch
  with the empty-composition branch introduced in the current-empty query
  layer, using a refined empty-header query bound in this downstream route.
\<close>

context soundness
begin

definition checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
    out \<longleftrightarrow>
    checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
      composition_trace_bad_alpha_space out \<and>
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad_with_partial_candidates out \<or>
     checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header out)"

lemma checked_staged_security_with_actual_alpha_prefix_partial_candidate_randomization_imp_prefix_prequery_or_relevant_drift_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and bad:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_partial_candidates out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        out"
proof -
  have partial:
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      composition_trace_bad_alpha_space out"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_candidate_randomization_imp_partial_header_bad_set_hit_on_support
        [OF support bad])
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
        "checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
          out"
        unfolding
          checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_def
        using drift bad by simp
      then show ?thesis by simp
    qed
  next
    assume
      "checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space out"
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_imp_prefix_prequery_or_relevant_drift_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        out"
proof -
  have partial:
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      composition_trace_bad_alpha_space out"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_partial_alpha_hit_imp_partial_header_bad_set_hit_on_support
        [OF support hit])
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
        "checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
          out"
        unfolding
          checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_def
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

lemma checked_staged_security_with_actual_alpha_prefix_partial_candidate_randomization_bound_from_relevant_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_partial_candidates)
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
    "checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift"
  let ?Random =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad_with_partial_candidates"
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
  have "wp_event ?M ?Random adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?Prefix out \<or> ?Prequery out \<or> ?Drift out \<or> False)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (use
        checked_staged_security_with_actual_alpha_prefix_partial_candidate_randomization_imp_prefix_prequery_or_relevant_drift_on_support
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

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_bound_from_relevant_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
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
    "checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift"
  let ?Hit =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header"
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
  have "wp_event ?M ?Hit adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?Prefix out \<or> ?Prequery out \<or> ?Drift out \<or> False)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (use
        checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_imp_prefix_prequery_or_relevant_drift_on_support
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

lemma checked_staged_security_with_data_state_partial_candidate_composition_bad_bound_from_relevant_drift_and_budgets:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
  shows
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
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?degree = "?E composition_degree_bad_with_partial_candidates"
  let ?random = "?E composition_randomization_bad_with_partial_candidates"
  let ?bad = "?E composition_bad_with_partial_candidates"
  have degree_false: "?degree = (\<lambda>out. False)"
    by (rule ext)
      (auto simp: staged_security_with_data_state_verifier_event_def
        composition_degree_bad_with_partial_candidates_false
        split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    unfolding degree_false wp_event_def wp_def dist_expect_def by simp
  have projected:
    "wp_event ?M ?random adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_partial_candidates)
      adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection)
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
    unfolding projected
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_candidate_randomization_bound_from_relevant_drift_and_budgets
        [OF wf controlled drift_bound])
  have "wp_event ?M ?bad adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?degree out \<or> ?random out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest: composition_bad_with_partial_candidates_split
          [OF false_statement]
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?degree adversary_initial_state +
      wp_event ?M ?random adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      0 +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        D)"
    by (intro add_mono degree_bound random_bound)
  finally show ?thesis
    by simp
qed

lemma checked_staged_security_with_data_state_empty_header_composition_randomization_bound_from_relevant_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_empty_composition_header_candidates)
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
      composition_randomization_bad_with_empty_composition_header_candidates"
  let ?alpha =
    "staged_security_with_data_state_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header"
  have alpha_projected:
    "wp_event ?M ?alpha adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
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
        checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_bound_from_relevant_drift_and_budgets
        [OF wf controlled drift_bound])
  have "wp_event ?M ?random adversary_initial_state \<le>
      wp_event ?M ?alpha adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_alpha_bad_set_hit_with_empty_header_imp_partial_opening_union_hit
          composition_randomization_bad_with_empty_composition_header_candidates_imp_alpha_hit
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

lemma checked_staged_security_with_data_state_empty_header_bad_event_bound_from_relevant_drift_trace_fri_and_query:
  fixes trace_fri_error' :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error'"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> empty_query_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error' + empty_query_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?degree =
    "?E composition_degree_bad_with_empty_composition_header_candidates"
  let ?random =
    "?E composition_randomization_bad_with_empty_composition_header_candidates"
  let ?trace =
    "?E trace_fri_bad_with_empty_composition_header_candidates"
  let ?query =
    "?E query_bad_with_empty_composition_header_candidates"
  let ?bad = "?E soundness_bad_event_partial_candidate_empty_header"
  have degree_false: "?degree = (\<lambda>out. False)"
    by (rule ext)
      (auto simp: staged_security_with_data_state_verifier_event_def
        composition_degree_bad_with_empty_composition_header_candidates_false
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
        checked_staged_security_with_data_state_empty_header_composition_randomization_bound_from_relevant_drift_and_budgets
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
        "soundness_bad_event_partial_candidate_empty_header ?s
          (Some (result, final_state))"
        using bad
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
      then consider
          (comp)
            "composition_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state))"
        | (trace)
            "trace_fri_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state))"
        | (query)
            "query_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state))"
        unfolding soundness_bad_event_partial_candidate_empty_header_def
        by blast
      then show ?thesis
      proof cases
        case comp
        then have comp_split:
          "composition_degree_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state)) \<or>
           composition_randomization_bad_with_empty_composition_header_candidates
              ?s (Some (result, final_state))"
          by (rule
              composition_bad_with_empty_composition_header_candidates_split
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
      trace_fri_error' + empty_query_error"
    by (intro add_mono degree_bound random_bound trace_fri_bound query_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_soundness_from_aligned_partial_candidate_components_and_current_empty_query_from_relevant_drift:
  fixes trace_fri_error' composition_fri_error' query_error D
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
          query_bad_with_aligned_partial_candidates)
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
        adversary_initial_state \<le> trace_fri_error"
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
      D + trace_fri_error + empty_query_error)"
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
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_relevant_drift_trace_fri_and_query
        [OF false_statement wf controlled drift_bound empty_trace_fri_bound
          empty_query_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_partial_candidate_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query:
  fixes trace_fri_error' composition_fri_error' query_error P D
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
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    query_error +
    (P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_bad_with_partial_candidates)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_data_state_partial_candidate_composition_bad_bound_from_prefix_drift_and_budgets
        [OF false_statement wf controlled prefix_bound drift_bound])
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
  have empty_header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_prefix_drift_trace_fri_and_current_empty_query
        [OF false_statement wf controlled prefix_bound drift_bound
          empty_trace_fri_bound current_empty_bound])
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (P + D +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0)) +
      trace_fri_error' + composition_fri_error' +
      query_error +
      (P + D +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
  then show ?thesis .
qed

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_drift:
  fixes trace_fri_error' composition_fri_error' query_error D
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
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    query_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
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
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound prefix_bound drift_bound empty_trace_fri_bound
          current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_partial_candidate_components_and_current_empty_query_from_drift:
  fixes trace_fri_error' composition_fri_error' query_error D
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
          query_bad_with_aligned_partial_candidates)
        adversary_initial_state \<le> query_error"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    query_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
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
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_partial_candidate_components_and_current_empty_query
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound prefix_bound drift_bound empty_trace_fri_bound
          current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_current_partial_opening_hit_from_drift_current_empty:
  fixes trace_fri_error' composition_fri_error' query_error D
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
    and current_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_current_query_partial_opening_hit
        adversary_initial_state \<le> query_error"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    query_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> query_error"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_current_partial_opening_hit
          current_query_bound])
      (use wf controlled in simp_all)
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_drift
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound drift_bound empty_trace_fri_bound current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_current_partial_opening_hit_from_not_prefix_current_empty:
  fixes trace_fri_error' composition_fri_error' query_error N
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
    and current_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_current_query_partial_opening_hit
        adversary_initial_state \<le> query_error"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> N"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    query_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> query_error"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_current_partial_opening_hit
          current_query_bound])
      (use wf controlled in simp_all)
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      N"
  proof -
    have "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le>
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_le_not_prefix_bound
          [OF wf controlled])
    also have "... \<le> N"
      by (rule not_prefix_bound)
    finally show ?thesis .
  qed
  have prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  proof -
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
    show ?thesis
      by (rule
          checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
          [OF transcript_bound])
  qed
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound prefix_bound drift_bound empty_trace_fri_bound
          current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds_from_drift_current_empty:
  fixes trace_fri_error' composition_fri_error' D empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
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
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have current_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds
        [OF round_bound wf controlled])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_components_and_current_partial_opening_hit_from_drift_current_empty
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          current_query_bound drift_bound empty_trace_fri_bound
          current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds_from_not_prefix_current_empty:
  fixes trace_fri_error' composition_fri_error' N empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
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
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have current_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds
        [OF round_bound wf controlled])
  show ?thesis
    by (rule
    checked_staged_soundness_from_aligned_transcript_components_and_current_partial_opening_hit_from_not_prefix_current_empty
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          current_query_bound not_prefix_bound empty_trace_fri_bound
          current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_not_prefix_current_empty:
  fixes trace_fri_error' composition_fri_error' N empty_query_error :: prob
    and Q :: "nat \<Rightarrow> prob"
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
    and trace_frac:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (card
            (staged_query_prefix_prefix_authenticated_trace_indices prefix
              prefix_state)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
    and path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_path_output_hit_at i)
          adversary_initial_state \<le> Q i"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> N"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + Q i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have round_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + Q i"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have prefix_hit_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
        adversary_initial_state \<le>
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) + query_error_bound"
      by (rule
          checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_trace_indices
          [OF wf controlled i_bound])
        (use trace_frac[OF i_bound] in blast)
    show
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + Q i"
      by (rule
          checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_path
          [OF wf controlled i_bound prefix_hit_bound path_bound[OF i_bound]])
  qed
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds_from_not_prefix_current_empty
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound not_prefix_bound empty_trace_fri_bound
          current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_trace_index_structured_path_bounds_from_not_prefix_current_empty:
  fixes trace_fri_error' composition_fri_error' N empty_query_error :: prob
    and T C :: "nat \<Rightarrow> prob"
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
    and trace_frac:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (card
            (staged_query_prefix_prefix_authenticated_trace_indices prefix
              prefix_state)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
    and trace_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
          adversary_initial_state \<le> T i"
    and composition_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
          adversary_initial_state \<le> C i"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> N"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + T i + C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have round_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + T i + C i"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have prefix_hit_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
        adversary_initial_state \<le>
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) + query_error_bound"
      by (rule
          checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_trace_indices
          [OF wf controlled i_bound])
        (use trace_frac[OF i_bound] in blast)
    show
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + T i + C i"
      by (rule
          checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_structured_paths
          [OF wf controlled i_bound prefix_hit_bound trace_path_bound[OF i_bound]
            composition_path_bound[OF i_bound]])
  qed
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds_from_not_prefix_current_empty
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound not_prefix_bound empty_trace_fri_bound
          current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_conceptual_structured_paths_from_not_prefix_current_empty:
  fixes trace_fri_error' composition_fri_error' N empty_query_error :: prob
    and T C :: "nat \<Rightarrow> prob"
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
    and conceptual_context:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> hash_map_output_collision prefix_state \<and>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table prefix prefix_state) \<and>
        \<not> all_queries_consistent
          (query_prefix_trace_conceptual_table prefix prefix_state)
          (query_prefix_composition_conceptual_table prefix prefix_state)
          (sqp_alphas prefix)"
    and trace_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
          adversary_initial_state \<le> T i"
    and composition_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
          adversary_initial_state \<le> C i"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> N"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + T i + C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have round_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + T i + C i"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have prefix_target_bound:
      "wp_event (checked_staged_query_prefix_receive_with_state A i)
        (checked_staged_query_prefix_dynamic_index_hit
          staged_query_prefix_prefix_authenticated_opening_target)
        adversary_initial_state \<le>
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) + query_error_bound"
      by (rule
          checked_staged_query_prefix_prefix_authenticated_target_hit_bound_from_conceptual
          [OF wf controlled i_bound])
        (rule conceptual_context[OF i_bound])
    have prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
        adversary_initial_state \<le>
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) + query_error_bound"
      by (rule
          checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_dynamic_target
          [OF wf controlled i_bound prefix_target_bound])
    show
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + T i + C i"
      by (rule
          checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_structured_paths
          [OF wf controlled i_bound prefix_bound trace_path_bound[OF i_bound]
            composition_path_bound[OF i_bound]])
  qed
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds_from_not_prefix_current_empty
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound not_prefix_bound empty_trace_fri_bound
          current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_cross_data_pre_and_witness_new_components_current_empty:
  fixes trace_fri_error' composition_fri_error' X P R empty_query_error :: prob
    and Q :: "nat \<Rightarrow> prob"
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
    and trace_frac:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (card
            (staged_query_prefix_prefix_authenticated_trace_indices prefix
              prefix_state)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
    and path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_path_output_hit_at i)
          adversary_initial_state \<le> Q i"
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
    and transcript_new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> R"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + Q i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have transcript_pre_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      adversary_initial_state \<le> P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_bound_from_data_state_pre_hit
        [OF data_pre_bound])
  have witness_hit_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new
        [OF transcript_pre_bound transcript_new_bound])
  have no_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le> P + R"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_le_witness_transcript_hit
          witness_hit_bound])
  have path_output_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le> P + R"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_le_witness_transcript_hit
          witness_hit_bound])
  have uncovered_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      adversary_initial_state \<le> X"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_witnessed_cross_or_merkle_bad
          cross_bound])
  have collision_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
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
      X + (P + R) + (P + R)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_output_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_not_prefix_current_empty
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          trace_frac path_bound not_prefix_bound empty_trace_fri_bound
          current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_trace_index_structured_path_bounds_from_cross_data_pre_and_witness_new_components_current_empty:
  fixes trace_fri_error' composition_fri_error' X P R empty_query_error :: prob
    and T C :: "nat \<Rightarrow> prob"
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
    and trace_frac:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (card
            (staged_query_prefix_prefix_authenticated_trace_indices prefix
              prefix_state)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
    and trace_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
          adversary_initial_state \<le> T i"
    and composition_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
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
    and transcript_new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> R"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + T i + C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have transcript_pre_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      adversary_initial_state \<le> P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_bound_from_data_state_pre_hit
        [OF data_pre_bound])
  have witness_hit_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new
        [OF transcript_pre_bound transcript_new_bound])
  have no_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le> P + R"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_le_witness_transcript_hit
          witness_hit_bound])
  have path_output_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le> P + R"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_le_witness_transcript_hit
          witness_hit_bound])
  have uncovered_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      adversary_initial_state \<le> X"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_witnessed_cross_or_merkle_bad
          cross_bound])
  have collision_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
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
      X + (P + R) + (P + R)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_output_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_components_and_trace_index_structured_path_bounds_from_not_prefix_current_empty
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          trace_frac trace_path_bound composition_path_bound not_prefix_bound
          empty_trace_fri_bound current_empty_bound])
qed

theorem checked_staged_soundness_from_aligned_transcript_conceptual_default_alpha_prefix_union_clean_structured_paths_current_empty:
  fixes trace_fri_error' composition_fri_error' N empty_query_error :: prob
    and T C :: "nat \<Rightarrow> prob"
    and trace_default composition_default :: "'f list"
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
    and default_prefix_clean:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_default = trace_default \<and>
        query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default = composition_default \<and>
        trace_table_low_degree trace_default \<and>
        composition_table_low_degree maxDegree composition_default \<and>
        trace_default \<in>
          alpha_prefix_trace_table_candidates prefix_state
            (sqp_trace_root prefix) \<and>
        sqp_alphas prefix \<notin>
          alpha_prefix_union_bad_sets prefix_state
            composition_trace_bad_alpha_space (sqp_trace_root prefix)"
    and trace_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
          adversary_initial_state \<le> T i"
    and composition_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
          adversary_initial_state \<le> C i"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> N"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      T i + C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof (rule
    checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds_from_not_prefix_current_empty
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound _ not_prefix_bound
      empty_trace_fri_bound current_empty_bound])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_alpha_prefix_union_clean_and_structured_paths
        [OF false_statement wf controlled i_bound _ trace_path_bound[OF i_bound]
          composition_path_bound[OF i_bound]])
      (rule default_prefix_clean[OF i_bound])
qed

theorem checked_staged_soundness_from_aligned_transcript_conceptual_default_alpha_prefix_union_clean_structured_paths_from_drift_current_empty:
  fixes trace_fri_error' composition_fri_error' D empty_query_error :: prob
    and T C :: "nat \<Rightarrow> prob"
    and trace_default composition_default :: "'f list"
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
    and default_prefix_clean:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_default = trace_default \<and>
        query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default = composition_default \<and>
        trace_table_low_degree trace_default \<and>
        composition_table_low_degree maxDegree composition_default \<and>
        trace_default \<in>
          alpha_prefix_trace_table_candidates prefix_state
            (sqp_trace_root prefix) \<and>
        sqp_alphas prefix \<notin>
          alpha_prefix_union_bad_sets prefix_state
            composition_trace_bad_alpha_space (sqp_trace_root prefix)"
    and trace_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
          adversary_initial_state \<le> T i"
    and composition_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
          adversary_initial_state \<le> C i"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
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
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      T i + C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof (rule
    checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds_from_drift_current_empty
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound _ drift_bound
      empty_trace_fri_bound current_empty_bound])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_alpha_prefix_union_clean_and_structured_paths
        [OF false_statement wf controlled i_bound _ trace_path_bound[OF i_bound]
          composition_path_bound[OF i_bound]])
      (rule default_prefix_clean[OF i_bound])
qed

end

end
