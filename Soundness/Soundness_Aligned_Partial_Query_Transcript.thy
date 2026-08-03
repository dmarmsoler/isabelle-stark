(*  Title:      Stark/Soundness_Aligned_Partial_Query_Transcript.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Aligned_Partial_Query_Transcript
  imports
    Soundness_Aligned_Partial_Query
    Soundness_Staged_Partial_Query
begin

text \<open>
  Transcript-tied aligned partial-query events.

  The aligned partial-opening predicate records that trace and composition
  openings use the same sampled query indices.  For probabilistic query bounds
  we additionally need those indices to be the verifier-derived Fiat-Shamir
  query indices.  This layer adds that transcript replay fact without changing
  the protocol model.
\<close>

context soundness
begin

definition accepted_with_partial_initial_openings_aligned_transcript_consistent
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> bool"
where
  "accepted_with_partial_initial_openings_aligned_transcript_consistent s out
      fr f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings \<longleftrightarrow>
    accepted_with_partial_initial_openings_aligned_consistent s out fr
      f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings \<and>
    accepted_transcript_shape s out as query_idxs"

definition query_bad_with_aligned_transcript_partial_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "query_bad_with_aligned_transcript_partial_candidates s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
        query_idxs trace_openings composition_openings trace_table
        composition_table.
      accepted_with_partial_initial_openings_aligned_transcript_consistent s
        out fr f_fri_roots f_final as dg composition_fri_roots final
        query_idxs trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      \<not> all_queries_consistent trace_table composition_table as)"

definition soundness_bad_event_aligned_transcript_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "soundness_bad_event_aligned_transcript_partial_candidate s out \<longleftrightarrow>
    composition_bad_with_partial_candidates s out \<or>
    trace_fri_bad_with_partial_candidates s out \<or>
    composition_fri_bad_with_partial_candidates s out \<or>
    query_bad_with_aligned_transcript_partial_candidates s out"

definition soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
      s out \<longleftrightarrow>
    partial_merkle_inconsistency_bad s out \<or>
    soundness_bad_event_aligned_transcript_partial_candidate s out"

lemma accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned:
  assumes
    "accepted_with_partial_initial_openings_aligned_transcript_consistent s out
      fr f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings"
  shows
    "accepted_with_partial_initial_openings_aligned_consistent s out fr
      f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings"
  using assms
  unfolding
    accepted_with_partial_initial_openings_aligned_transcript_consistent_def
  by simp

lemma accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_shape:
  assumes
    "accepted_with_partial_initial_openings_aligned_transcript_consistent s out
      fr f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings"
  shows "accepted_transcript_shape s out as query_idxs"
  using assms
  unfolding
    accepted_with_partial_initial_openings_aligned_transcript_consistent_def
  by simp

lemma query_bad_with_aligned_transcript_partial_candidates_imp_aligned:
  assumes "query_bad_with_aligned_transcript_partial_candidates s out"
  shows "query_bad_with_aligned_partial_candidates s out"
proof -
  from assms obtain fr f_fri_roots f_final as dg composition_fri_roots
      final query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent s
        out fr f_fri_roots f_final as dg composition_fri_roots final
        query_idxs trace_openings composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
    unfolding query_bad_with_aligned_transcript_partial_candidates_def
    by blast
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent s out fr
      f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  show ?thesis
    unfolding query_bad_with_aligned_partial_candidates_def
    using aligned trace_candidate comp_candidate trace_low comp_low not_all
    by blast
qed

lemma query_bad_with_aligned_transcript_partial_candidates_miss_disagreements:
  assumes "query_bad_with_aligned_transcript_partial_candidates s out"
  shows "\<exists>trace_table composition_table as query_idxs.
    query_samples_miss_disagreements trace_table composition_table as
      query_idxs"
  by (rule query_bad_with_aligned_partial_candidates_miss_disagreements)
    (rule query_bad_with_aligned_transcript_partial_candidates_imp_aligned
      [OF assms])

lemma soundness_bad_event_aligned_transcript_partial_candidate_imp_aligned:
  assumes "soundness_bad_event_aligned_transcript_partial_candidate s out"
  shows "soundness_bad_event_aligned_partial_candidate s out"
  using assms query_bad_with_aligned_transcript_partial_candidates_imp_aligned
  unfolding soundness_bad_event_aligned_transcript_partial_candidate_def
    soundness_bad_event_aligned_partial_candidate_def
  by blast

lemma soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_imp_aligned:
  assumes
    "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
      s out"
  shows
    "soundness_bad_event_aligned_partial_candidate_with_partial_merkle s out"
  using assms soundness_bad_event_aligned_transcript_partial_candidate_imp_aligned
  unfolding
    soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_def
    soundness_bad_event_aligned_partial_candidate_with_partial_merkle_def
  by blast

lemma accepted_aligned_transcript_partial_candidate_partition:
  assumes false_statement: "\<not> exists_valid_trace"
    and partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent s
        out fr f_fri_roots f_final as dg composition_fri_roots final
        query_idxs trace_openings composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
  shows "soundness_bad_event_aligned_transcript_partial_candidate s out"
proof (cases "trace_table_low_degree trace_table")
  case False
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent s out fr
      f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  have "trace_fri_bad_with_partial_candidates s out"
    unfolding trace_fri_bad_with_partial_candidates_def
    using accepted_with_partial_initial_openings_aligned_consistent_imp_unaligned
        [OF aligned]
      trace_candidate False by blast
  then show ?thesis
    unfolding soundness_bad_event_aligned_transcript_partial_candidate_def
    by blast
next
  case True
  note trace_low = True
  show ?thesis
  proof (cases "composition_table_low_degree maxDegree composition_table")
    case False
    have aligned:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings"
      by (rule
          accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
          [OF partial])
    have "composition_fri_bad_with_partial_candidates s out"
      unfolding composition_fri_bad_with_partial_candidates_def
      using accepted_with_partial_initial_openings_aligned_consistent_imp_unaligned
          [OF aligned]
        trace_candidate composition_candidate trace_low False
      by blast
    then show ?thesis
      unfolding soundness_bad_event_aligned_transcript_partial_candidate_def
      by blast
  next
    case True
    note composition_low = True
    show ?thesis
    proof (cases "all_queries_consistent trace_table composition_table as")
      case False
      have "query_bad_with_aligned_transcript_partial_candidates s out"
        unfolding query_bad_with_aligned_transcript_partial_candidates_def
        using partial trace_candidate composition_candidate trace_low
          composition_low False
        by blast
      then show ?thesis
        unfolding soundness_bad_event_aligned_transcript_partial_candidate_def
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
      have aligned:
        "accepted_with_partial_initial_openings_aligned_consistent s out fr
          f_fri_roots f_final as dg composition_fri_roots final query_idxs
          trace_openings composition_openings"
        by (rule
            accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
            [OF partial])
      have "composition_bad_with_partial_candidates s out"
        unfolding composition_bad_with_partial_candidates_def
        using accepted_with_partial_initial_openings_aligned_consistent_imp_unaligned
            [OF aligned]
          trace_candidate composition_candidate deg_f trace_table_eq
          violated composition_low all_queries
        by blast
      then show ?thesis
        unfolding soundness_bad_event_aligned_transcript_partial_candidate_def
        by blast
    qed
  qed
qed

lemma soundness_bad_event_aligned_transcript_partial_candidate_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes comp_bound:
      "wp_event verify_monad
        (composition_bad_with_partial_candidates s) s \<le>
        composition_error"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_partial_candidates s) s \<le>
        trace_fri_error'"
    and comp_fri_bound:
      "wp_event verify_monad
        (composition_fri_bad_with_partial_candidates s) s \<le>
        composition_fri_error'"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_aligned_transcript_partial_candidates s) s \<le>
        query_error"
  shows
    "wp_event verify_monad
      (soundness_bad_event_aligned_transcript_partial_candidate s) s \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
proof -
  have "wp_event verify_monad
      (soundness_bad_event_aligned_transcript_partial_candidate s) s \<le>
      wp_event verify_monad
        (composition_bad_with_partial_candidates s) s +
      wp_event verify_monad
        (trace_fri_bad_with_partial_candidates s) s +
      wp_event verify_monad
        (composition_fri_bad_with_partial_candidates s) s +
      wp_event verify_monad
        (query_bad_with_aligned_transcript_partial_candidates s) s"
    unfolding soundness_bad_event_aligned_transcript_partial_candidate_def
    by (rule wp_event_union_bound4)
  also have "... \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
    by (intro add_mono comp_bound trace_fri_bound comp_fri_bound
        query_bound)
  finally show ?thesis .
qed

lemma soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le>
        merkle_error"
    and comp_bound:
      "wp_event verify_monad
        (composition_bad_with_partial_candidates s) s \<le>
        composition_error"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_partial_candidates s) s \<le>
        trace_fri_error'"
    and comp_fri_bound:
      "wp_event verify_monad
        (composition_fri_bad_with_partial_candidates s) s \<le>
        composition_fri_error'"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_aligned_transcript_partial_candidates s) s \<le>
        query_error"
  shows
    "wp_event verify_monad
      (soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle s) s
      \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
proof -
  have partial_bound:
    "wp_event verify_monad
      (soundness_bad_event_aligned_transcript_partial_candidate s) s \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
    by (rule
        soundness_bad_event_aligned_transcript_partial_candidate_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  have "wp_event verify_monad
      (soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle s) s
      \<le>
      wp_event verify_monad (partial_merkle_inconsistency_bad s) s +
      wp_event verify_monad
        (soundness_bad_event_aligned_transcript_partial_candidate s) s"
    unfolding
      soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_def
    by (rule wp_event_union_bound)
  also have "... \<le>
      merkle_error +
      (composition_error + trace_fri_error' + composition_fri_error' +
        query_error)"
    by (intro add_mono merkle_bound partial_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_data_state_aligned_transcript_partial_candidate_union_bound:
  fixes composition_error trace_fri_error' composition_fri_error'
    query_error :: prob
  assumes comp_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_error"
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
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate)
      adversary_initial_state \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?comp = "?E composition_bad_with_partial_candidates"
  let ?trace = "?E trace_fri_bad_with_partial_candidates"
  let ?comp_fri = "?E composition_fri_bad_with_partial_candidates"
  let ?query = "?E query_bad_with_aligned_transcript_partial_candidates"
  let ?partial = "?E soundness_bad_event_aligned_transcript_partial_candidate"
  have "wp_event ?M ?partial adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?comp out \<or> ?trace out \<or> ?comp_fri out \<or>
          ?query out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        soundness_bad_event_aligned_transcript_partial_candidate_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?comp adversary_initial_state +
      wp_event ?M ?trace adversary_initial_state +
      wp_event ?M ?comp_fri adversary_initial_state +
      wp_event ?M ?query adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
    by (intro add_mono comp_bound trace_fri_bound comp_fri_bound
        query_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_aligned_transcript_partial_candidate_with_partial_merkle_component_union_bound:
  fixes merkle_error composition_error trace_fri_error'
    composition_fri_error' query_error :: prob
  assumes merkle_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state \<le> merkle_error"
    and comp_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_error"
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
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle)
      adversary_initial_state \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
proof -
  have partial_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate)
      adversary_initial_state \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_partial_candidate_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?merkle = "?E partial_merkle_inconsistency_bad"
  let ?partial = "?E soundness_bad_event_aligned_transcript_partial_candidate"
  let ?with_merkle =
    "?E soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle"
  have "wp_event ?M ?with_merkle adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?merkle out \<or> ?partial out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?merkle adversary_initial_state +
      wp_event ?M ?partial adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      merkle_error +
      (composition_error + trace_fri_error' + composition_fri_error' +
        query_error)"
    by (intro add_mono merkle_bound partial_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_data_state_aligned_transcript_partial_candidate_with_partial_merkle_union_bound:
  fixes merkle_error composition_error trace_fri_error'
    composition_fri_error' query_error :: prob
  assumes merkle_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state \<le> merkle_error"
    and partial_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_aligned_transcript_partial_candidate)
        adversary_initial_state \<le>
        composition_error + trace_fri_error' + composition_fri_error' +
          query_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle)
      adversary_initial_state \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = "staged_security_with_data_state_verifier_event"
  let ?merkle = "?E partial_merkle_inconsistency_bad"
  let ?partial = "?E soundness_bad_event_aligned_transcript_partial_candidate"
  have "wp_event ?M
      (?E soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle)
      adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?merkle out \<or> ?partial out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?merkle adversary_initial_state +
      wp_event ?M ?partial adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      merkle_error +
      (composition_error + trace_fri_error' + composition_fri_error' +
        query_error)"
    by (intro add_mono merkle_bound partial_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_data_state_aligned_transcript_query_bad_imp_partial_opening_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates
        (Some (((data, attacker_state), result), final_state))"
  shows
    "staged_security_with_data_state_query_partial_opening_hit
      (Some (((data, attacker_state), result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support]
  obtain builder where builder:
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
  from bad obtain fr f_fri_roots f_final as dg composition_fri_roots
      final query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent ?s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
    unfolding staged_security_with_data_state_verifier_event_def
      query_bad_with_aligned_transcript_partial_candidates_def
    by simp blast
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as
      query_idxs"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_shape
        [OF partial])
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled support shape]
  obtain raw_idxs where
    as_eq: "as = staged_alphas data"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<forall>i<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    by blast
  have aligned0:
    "accepted_with_partial_initial_openings_aligned ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
        [OF aligned])
  from accepted_with_partial_initial_openings_aligned_shapes[OF aligned0]
  obtain rest where header:
    "verifier_header_transcript ?s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    by blast
  have comp_nonempty: "composition_fri_roots \<noteq> []"
    using accepted_with_partial_initial_openings_aligned_shapes(1)
      [OF aligned0] .
  have trace_partial:
    "accepted_with_partial_trace_openings ?s
      (Some (result, final_state)) fr query_idxs trace_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(3)
      [OF aligned0] .
  have comp_partial:
    "accepted_with_partial_composition_openings ?s
      (Some (result, final_state)) (hd composition_fri_roots) query_idxs
      composition_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(4)
      [OF aligned0] .
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
  let ?i = 0
  have i_bound: "?i < rounds"
    using rounds_positive by simp
  have round_consistent:
    "partial_query_round_consistent trace_openings composition_openings as
      ?i (query_idxs ! ?i)"
    using aligned i_bound
    unfolding accepted_with_partial_initial_openings_aligned_consistent_def
    by simp
  have opening_consistent:
    "partial_query_openings_consistent (trace_openings ! ?i)
      (composition_openings ! ?i) as (query_idxs ! ?i)"
    using round_consistent
    unfolding partial_query_round_consistent_def
      partial_query_openings_consistent_def
    by simp
  have idx_sample: "query_idxs ! ?i \<in> query_sample_space"
    using round_consistent
    unfolding partial_query_round_consistent_def by simp
  have trace_table:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! ?i) final_state"
    using trace_partial i_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  have comp_table:
    "partial_authenticated_table (hd composition_fri_roots)
      (scale * clength) (composition_openings ! ?i) final_state"
    using comp_partial i_bound
    unfolding accepted_with_partial_composition_openings_def by blast
  have witness:
    "(trace_openings ! ?i, composition_openings ! ?i) \<in>
      query_header_supported_partial_opening_witnesses ?s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_opening_witnesses_def
    using comp_nonempty verifier trace_table comp_table header by blast
  have idx_in_header_set:
    "query_idxs ! ?i \<in>
      query_header_supported_partial_opening_success_indices_at ?s fr
        f_fri_roots f_final as dg composition_fri_roots final ?i"
    unfolding query_header_supported_partial_opening_success_indices_at_def
    using idx_sample witness opening_consistent by blast
  have idx_in_staged_set:
    "query_idxs ! ?i \<in>
      query_header_supported_partial_opening_success_indices_at ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        ?i"
    using idx_in_header_set header_eq by simp
  have raw_idx:
    "index (to_nat (raw_idxs ! ?i)) = query_idxs ! ?i"
    using query_idxs_eq len_raw i_bound by simp
  have lookup_i:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge ?i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) ?i)) =
      Some (raw_idxs ! ?i)"
    using lookup i_bound by simp
  have hit_at:
    "staged_security_with_data_state_query_partial_opening_hit_at ?i
      (Some (((data, attacker_state), result), final_state))"
    unfolding staged_security_with_data_state_query_partial_opening_hit_at_def
    using i_bound lookup_i idx_in_staged_set raw_idx
    by (simp add: Let_def)
  show ?thesis
    by (rule staged_security_with_data_state_query_partial_opening_hitI
        [OF i_bound hit_at])
qed

lemma checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_partial_opening_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
    "out \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates out"
  show "staged_security_with_data_state_query_partial_opening_hit out"
  proof (cases out)
    case None
    then show ?thesis
      using bad
      unfolding staged_security_with_data_state_verifier_event_def by simp
  next
    case (Some packed)
    then obtain data attacker_state result final_state where out_eq:
      "out = Some (((data, attacker_state), result), final_state)"
      by (cases packed, auto split: prod.splits)
    show ?thesis
      unfolding out_eq
      by (rule
          checked_staged_security_with_data_state_aligned_transcript_query_bad_imp_partial_opening_hit_on_support
          [OF wf controlled])
        (use support bad out_eq in simp_all)
  qed
qed

lemma selected_query_openings_align_with_replayed_query_key:
  assumes i_bound: "i < rounds"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and selected_idx: "idx = index (to_nat raw)"
    and selected_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge k prefix_state) = Some raw"
    and replay_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge k prefix_state) = Some (raw_idxs ! i)"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and comp_indices:
      "map opening_index composition_openings =
        [idx, fri_sibling_index (scale * clength) idx]"
    and consistent:
      "partial_query_openings_consistent trace_openings
        composition_openings as idx"
  shows
    "idx = query_idxs ! i"
    "map opening_index trace_openings = powers_scaled (query_idxs ! i)"
    "map opening_index composition_openings =
      [query_idxs ! i,
       fri_sibling_index (scale * clength) (query_idxs ! i)]"
    "partial_query_openings_consistent trace_openings composition_openings
      as (query_idxs ! i)"
proof -
  have raw_eq: "raw = raw_idxs ! i"
    using selected_lookup replay_lookup by simp
  have idx_eq: "idx = query_idxs ! i"
    using selected_idx raw_eq query_idxs_eq len_raw i_bound by simp
  show "idx = query_idxs ! i"
    by (rule idx_eq)
  show "map opening_index trace_openings = powers_scaled (query_idxs ! i)"
    using trace_indices idx_eq by simp
  show "map opening_index composition_openings =
      [query_idxs ! i,
       fri_sibling_index (scale * clength) (query_idxs ! i)]"
    using comp_indices idx_eq by simp
  show "partial_query_openings_consistent trace_openings composition_openings
      as (query_idxs ! i)"
    using consistent idx_eq by simp
qed

lemma selected_query_openings_align_with_replayed_query_index:
  assumes i_bound: "i < rounds"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and selected_idx: "idx = index (to_nat raw)"
    and selected_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i prefix_state) = Some raw"
    and replay_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i prefix_state) = Some (raw_idxs ! i)"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and comp_indices:
      "map opening_index composition_openings =
        [idx, fri_sibling_index (scale * clength) idx]"
    and consistent:
      "partial_query_openings_consistent trace_openings
        composition_openings as idx"
  shows
    "idx = query_idxs ! i"
    "map opening_index trace_openings = powers_scaled (query_idxs ! i)"
    "map opening_index composition_openings =
      [query_idxs ! i,
       fri_sibling_index (scale * clength) (query_idxs ! i)]"
    "partial_query_openings_consistent trace_openings composition_openings
      as (query_idxs ! i)"
  by (rule selected_query_openings_align_with_replayed_query_key
      [OF i_bound len_raw query_idxs_eq selected_idx selected_lookup
        replay_lookup trace_indices comp_indices consistent])+

lemma ntimes_verifier_query_rounds_selected_authenticated_chunks_aligned_with_replay_at:
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    and i_bound: "i < rounds"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
  obtains trace_openings composition_openings where
    "map opening_index trace_openings = powers_scaled (query_idxs ! i)"
    "partial_authenticated_table fr (scale * clength) trace_openings
      final_state"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings final_state"
    "map opening_index composition_openings =
      [query_idxs ! i,
       fri_sibling_index (scale * clength) (query_idxs ! i)]"
    "partial_query_openings_consistent trace_openings composition_openings
      as (query_idxs ! i)"
proof (rule ntimes_verifier_query_rounds_selected_authenticated_chunks_at
    [OF fl_eq outcome i_bound])
  fix raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks trace_openings composition_openings
  assume selected_idx: "idx = index (to_nat raw)"
    and len_prefix_chunks: "length prefix_chunks = i"
    and len_suffix_chunks: "length suffix_chunks = rounds - Suc i"
    and chunk_shape:
      "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    and prefix_rounds:
      "\<And>j. j < i \<Longrightarrow>
        verifier_query_round_chunk (prefix_query_idxs ! j)
          (map snd f_fl) (map snd fl) (prefix_chunks ! j)"
    and suffix_rounds:
      "\<And>j. j < rounds - Suc i \<Longrightarrow>
        verifier_query_round_chunk (suffix_query_idxs ! j)
          (map snd f_fl) (map snd fl) (suffix_chunks ! j)"
    and selected_transcript:
      "PTranscript query_state =
        List.concat (prefix_chunks @ chunk # suffix_chunks) @
          PTranscript final_state"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and trace_table:
      "partial_authenticated_table fr (scale * clength) trace_openings
        final_state"
    and comp_table:
      "partial_authenticated_table composition_root (scale * clength)
        composition_openings final_state"
    and comp_indices:
      "map opening_index composition_openings =
        [idx, fri_sibling_index (scale * clength) idx]"
    and consistent:
      "partial_query_openings_consistent trace_openings
        composition_openings as idx"
    and selected_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) prefix_chunks i)) =
        Some raw"
  let ?selected_chunks = "prefix_chunks @ chunk # suffix_chunks"
  have len_selected_chunks: "length ?selected_chunks = rounds"
    using len_prefix_chunks len_suffix_chunks i_bound by simp
  have selected_chunk_lens:
    "\<And>j. j < rounds \<Longrightarrow>
      length (?selected_chunks ! j) =
        verifier_query_round_transcript_length (query_idxs ! j)
          (map snd f_fl) (map snd fl)"
  proof -
    fix j
    assume j_bound: "j < rounds"
    show
      "length (?selected_chunks ! j) =
        verifier_query_round_transcript_length (query_idxs ! j)
          (map snd f_fl) (map snd fl)"
    proof (cases "j < i")
      case True
      have nth_eq: "?selected_chunks ! j = prefix_chunks ! j"
        using True len_prefix_chunks by (simp add: nth_append)
      have
        "length (prefix_chunks ! j) =
          verifier_query_round_transcript_length
            (prefix_query_idxs ! j) (map snd f_fl) (map snd fl)"
        by (rule verifier_query_round_chunk_length[OF prefix_rounds[OF True]])
      then show ?thesis
        using nth_eq
        by (simp add: verifier_query_round_transcript_length_index_irrelevant)
    next
      case False
      show ?thesis
      proof (cases "j = i")
        case True
        have nth_eq: "?selected_chunks ! j = chunk"
          using True len_prefix_chunks by (simp add: nth_append)
        have
          "length chunk =
            verifier_query_round_transcript_length idx
              (map snd f_fl) (map snd fl)"
          by (rule verifier_query_round_chunk_length[OF chunk_shape])
        then show ?thesis
          using nth_eq
          by (simp add:
              verifier_query_round_transcript_length_index_irrelevant)
      next
        case False
        let ?k = "j - Suc i"
        have ge: "Suc i \<le> j"
          using \<open>\<not> j < i\<close> False by linarith
        have k_bound: "?k < rounds - Suc i"
          using ge j_bound by linarith
        have nth_eq: "?selected_chunks ! j = suffix_chunks ! ?k"
          using ge len_prefix_chunks by (simp add: nth_append)
        have
          "length (suffix_chunks ! ?k) =
            verifier_query_round_transcript_length
              (suffix_query_idxs ! ?k) (map snd f_fl) (map snd fl)"
          by (rule verifier_query_round_chunk_length
              [OF suffix_rounds[OF k_bound]])
        then show ?thesis
          using nth_eq
          by (simp add:
              verifier_query_round_transcript_length_index_irrelevant)
      qed
    qed
  qed
  have query_chunk_lens:
    "\<And>j. j < rounds \<Longrightarrow>
      length (query_chunks ! j) =
        verifier_query_round_transcript_length (query_idxs ! j)
          (map snd f_fl) (map snd fl)"
    using query_chunk verifier_query_round_chunk_length by blast
  have concat_eq: "List.concat ?selected_chunks = List.concat query_chunks"
    using selected_transcript transcript_query by simp
  have chunks_eq: "?selected_chunks = query_chunks"
  proof -
    have same_lens:
      "\<And>j. j < length ?selected_chunks \<Longrightarrow>
        length (?selected_chunks ! j) = length (query_chunks ! j)"
      using selected_chunk_lens query_chunk_lens len_selected_chunks by simp
    have concat_eq_empty:
      "List.concat ?selected_chunks @ [] = List.concat query_chunks"
      using concat_eq by simp
    have len_eq: "length ?selected_chunks = length query_chunks"
      using len_selected_chunks len_query_chunks by simp
    have "?selected_chunks = query_chunks \<and> ([] :: 'f list) = []"
      by (rule concat_append_eq_concat_same_chunk_lengths
          [OF len_eq same_lens concat_eq_empty])
    then show ?thesis
      by simp
  qed
  have prefix_state_eq:
    "state_after_query_chunks (PState query_state) prefix_chunks i =
      state_after_query_chunks (PState query_state) query_chunks i"
  proof -
    have
      "state_after_query_chunks (PState query_state) ?selected_chunks i =
        state_after_query_chunks (PState query_state) prefix_chunks i"
      by (rule state_after_query_chunks_append_prefix[OF len_prefix_chunks])
    then show ?thesis
      using chunks_eq by simp
  qed
  have selected_lookup_global:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge (PQueryCounter query_state + i)
        (state_after_query_chunks (PState query_state) query_chunks i)) =
      Some raw"
    using selected_lookup prefix_state_eq by simp
  have aligned:
    "idx = query_idxs ! i"
    "map opening_index trace_openings = powers_scaled (query_idxs ! i)"
    "map opening_index composition_openings =
      [query_idxs ! i,
       fri_sibling_index (scale * clength) (query_idxs ! i)]"
    "partial_query_openings_consistent trace_openings composition_openings
      as (query_idxs ! i)"
    by (rule selected_query_openings_align_with_replayed_query_key
        [OF i_bound len_raw query_idxs_eq selected_idx
          selected_lookup_global replay_lookup[OF i_bound] trace_indices
          comp_indices consistent])+
  show ?thesis
    by (rule that)
      (use aligned trace_table comp_table in simp_all)
qed

lemma ntimes_verifier_query_rounds_aligned_authenticated_openings_consistent_with_replay:
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
  obtains trace_openings composition_openings where
    "length trace_openings = rounds"
    "length composition_openings = rounds"
    "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    "\<And>i. i < rounds \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
    "\<And>i. i < rounds \<Longrightarrow>
      partial_authenticated_table composition_root (scale * clength)
        (composition_openings ! i) final_state"
    "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (composition_openings ! i) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)]"
    "\<And>i. i < rounds \<Longrightarrow>
      partial_query_round_consistent trace_openings composition_openings as i
        (query_idxs ! i)"
proof -
  let ?P =
    "\<lambda>i w.
      map opening_index (fst w) = powers_scaled (query_idxs ! i) \<and>
      partial_authenticated_table fr (scale * clength) (fst w)
        final_state \<and>
      partial_authenticated_table composition_root (scale * clength)
        (snd w) final_state \<and>
      map opening_index (snd w) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
      query_idxs ! i \<in> query_sample_space \<and>
      snd w \<noteq> [] \<and>
      opening_value (snd w ! 0) =
        cp_eval as (map opening_value (fst w))
          (h ^ query_idxs ! i * shift)"
  have ex_round: "\<And>i. i < rounds \<Longrightarrow> \<exists>w. ?P i w"
  proof -
    fix i
    assume i_bound: "i < rounds"
    show "\<exists>w. ?P i w"
    proof (rule
        ntimes_verifier_query_rounds_selected_authenticated_chunks_aligned_with_replay_at
        [OF fl_eq outcome i_bound len_raw query_idxs_eq len_query_chunks
          transcript_query query_chunk replay_lookup])
      fix trace_openings composition_openings
      assume trace_indices:
          "map opening_index trace_openings =
            powers_scaled (query_idxs ! i)"
        and trace_table:
          "partial_authenticated_table fr (scale * clength) trace_openings
            final_state"
        and comp_table:
          "partial_authenticated_table composition_root (scale * clength)
            composition_openings final_state"
        and comp_indices:
          "map opening_index composition_openings =
            [query_idxs ! i,
             fri_sibling_index (scale * clength) (query_idxs ! i)]"
        and consistent:
          "partial_query_openings_consistent trace_openings
            composition_openings as (query_idxs ! i)"
      have idx_sample: "query_idxs ! i \<in> query_sample_space"
        using consistent unfolding partial_query_openings_consistent_def
        by simp
      have comp_nonempty: "composition_openings \<noteq> []"
        using consistent unfolding partial_query_openings_consistent_def
        by simp
      have comp_value:
        "opening_value (composition_openings ! 0) =
          cp_eval as (map opening_value trace_openings)
            (h ^ query_idxs ! i * shift)"
        using consistent unfolding partial_query_openings_consistent_def
        by simp
      show ?thesis
        by (intro exI[of _ "(trace_openings, composition_openings)"]
            conjI)
          (use trace_indices trace_table comp_table comp_indices consistent
            idx_sample comp_nonempty comp_value in simp_all)
    qed
  qed
  let ?wit = "\<lambda>i. SOME w. ?P i w"
  let ?trace_openings = "map (\<lambda>i. fst (?wit i)) [0..<rounds]"
  let ?composition_openings = "map (\<lambda>i. snd (?wit i)) [0..<rounds]"
  have round_props: "\<And>i. i < rounds \<Longrightarrow> ?P i (?wit i)"
    by (rule someI_ex[OF ex_round])
  have consistent:
    "\<And>i. i < rounds \<Longrightarrow>
      partial_query_round_consistent ?trace_openings ?composition_openings as
        i (query_idxs ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have chosen: "?P i (?wit i)"
      by (rule round_props[OF i_bound])
    have nths:
      "?trace_openings ! i = fst (?wit i)"
      "?composition_openings ! i = snd (?wit i)"
      using i_bound by simp_all
    have lengths:
      "length ?trace_openings = rounds"
      "length ?composition_openings = rounds"
      by simp_all
    have idx_sample: "query_idxs ! i \<in> query_sample_space"
      using chosen by blast
    have trace_indices0:
      "map opening_index (fst (?wit i)) =
        powers_scaled (query_idxs ! i)"
      using chosen by blast
    have comp_indices0:
      "map opening_index (snd (?wit i)) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)]"
      using chosen by blast
    have comp_value0:
      "opening_value (snd (?wit i) ! 0) =
        cp_eval as (map opening_value (fst (?wit i)))
          (h ^ query_idxs ! i * shift)"
      using chosen by blast
    have trace_indices:
      "map opening_index (?trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
      using trace_indices0 nths by simp
    have comp_indices:
      "map opening_index (?composition_openings ! i) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)]"
      using comp_indices0 nths by simp
    have comp_value:
      "opening_value ((?composition_openings ! i) ! 0) =
        cp_eval as (map opening_value (?trace_openings ! i))
          (h ^ query_idxs ! i * shift)"
      using comp_value0 nths by simp
    show
      "partial_query_round_consistent ?trace_openings ?composition_openings as
        i (query_idxs ! i)"
      by (rule partial_query_round_consistentI
          [OF i_bound idx_sample lengths trace_indices comp_indices comp_value])
  qed
  show ?thesis
  proof (rule that[of ?trace_openings ?composition_openings])
    show "length ?trace_openings = rounds"
      by simp
    show "length ?composition_openings = rounds"
      by simp
    show "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (?trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    proof -
      fix i
      assume i_bound: "i < rounds"
      have chosen: "?P i (?wit i)"
        by (rule round_props[OF i_bound])
      have nth: "?trace_openings ! i = fst (?wit i)"
        using i_bound by simp
      have trace_indices0:
        "map opening_index (fst (?wit i)) =
          powers_scaled (query_idxs ! i)"
        using chosen by blast
      show "map opening_index (?trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
        using trace_indices0 nth by simp
    qed
    show "\<And>i. i < rounds \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (?trace_openings ! i) final_state"
    proof -
      fix i
      assume i_bound: "i < rounds"
      have chosen: "?P i (?wit i)"
        by (rule round_props[OF i_bound])
      have nth: "?trace_openings ! i = fst (?wit i)"
        using i_bound by simp
      have trace_table0:
        "partial_authenticated_table fr (scale * clength)
          (fst (?wit i)) final_state"
        using chosen by blast
      show "partial_authenticated_table fr (scale * clength)
        (?trace_openings ! i) final_state"
        using trace_table0 nth by simp
    qed
    show "\<And>i. i < rounds \<Longrightarrow>
      partial_authenticated_table composition_root (scale * clength)
        (?composition_openings ! i) final_state"
    proof -
      fix i
      assume i_bound: "i < rounds"
      have chosen: "?P i (?wit i)"
        by (rule round_props[OF i_bound])
      have nth: "?composition_openings ! i = snd (?wit i)"
        using i_bound by simp
      have comp_table0:
        "partial_authenticated_table composition_root (scale * clength)
          (snd (?wit i)) final_state"
        using chosen by blast
      show "partial_authenticated_table composition_root (scale * clength)
        (?composition_openings ! i) final_state"
        using comp_table0 nth by simp
    qed
    show "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (?composition_openings ! i) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)]"
    proof -
      fix i
      assume i_bound: "i < rounds"
      have chosen: "?P i (?wit i)"
        by (rule round_props[OF i_bound])
      have nth: "?composition_openings ! i = snd (?wit i)"
        using i_bound by simp
      have comp_indices0:
        "map opening_index (snd (?wit i)) =
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)]"
        using chosen by blast
      show "map opening_index (?composition_openings ! i) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)]"
        using comp_indices0 nth by simp
    qed
    show "\<And>i. i < rounds \<Longrightarrow>
      partial_query_round_consistent ?trace_openings ?composition_openings as
        i (query_idxs ! i)"
      by (rule consistent)
  qed
qed

lemma query_rounds_replay_accepted_with_partial_initial_openings_aligned_consistent:
  assumes header0:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and fl_eq: "fl = (b, composition_root) # fl_tail"
    and f_roots: "map snd f_fl = f_fri_roots"
    and comp_roots: "map snd fl = composition_fri_roots"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
  obtains trace_openings composition_openings where
    "accepted_with_partial_initial_openings_aligned_consistent s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
proof -
  have root_eq: "composition_root = hd composition_fri_roots"
  proof -
    have "composition_root # map snd fl_tail = composition_fri_roots"
      using comp_roots unfolding fl_eq by simp
    then have "hd composition_fri_roots = composition_root"
      by (metis list.sel(1))
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule
      ntimes_verifier_query_rounds_aligned_authenticated_openings_consistent_with_replay
        [OF fl_eq query_out len_raw query_idxs_eq len_query_chunks
          transcript_query query_chunk replay_lookup])
    fix trace_openings composition_openings
    assume len_trace: "length trace_openings = rounds"
      and len_comp: "length composition_openings = rounds"
      and trace_indices:
        "\<And>i. i < rounds \<Longrightarrow>
          map opening_index (trace_openings ! i) =
            powers_scaled (query_idxs ! i)"
      and trace_tables:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_authenticated_table fr (scale * clength)
            (trace_openings ! i) final_state"
      and comp_tables:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_authenticated_table composition_root (scale * clength)
            (composition_openings ! i) final_state"
      and comp_indices:
        "\<And>i. i < rounds \<Longrightarrow>
          map opening_index (composition_openings ! i) =
            [query_idxs ! i,
             fri_sibling_index (scale * clength) (query_idxs ! i)]"
      and consistent:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_query_round_consistent trace_openings composition_openings
            as i (query_idxs ! i)"
    have len_query_idxs: "length query_idxs = rounds"
      using len_raw query_idxs_eq by simp
    have trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    proof -
      have all_indices:
        "\<forall>i < rounds.
          map opening_index (trace_openings ! i) =
            powers_scaled (query_idxs ! i)"
        using trace_indices by blast
      have all_tables:
        "\<forall>i < rounds.
          partial_authenticated_table fr (scale * clength)
            (trace_openings ! i) final_state"
        using trace_tables by blast
      show ?thesis
        unfolding accepted_with_partial_trace_openings_def accepted_def
        by (intro conjI exI[of _ result] exI[of _ final_state])
          (use len_query_idxs len_trace all_indices all_tables in simp_all)
    qed
    have comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots) query_idxs
        composition_openings"
    proof -
      have all_indices:
        "\<forall>i < rounds.
          map opening_index (composition_openings ! i) =
            [query_idxs ! i,
             fri_sibling_index (scale * clength) (query_idxs ! i)]"
        using comp_indices by blast
      have all_tables:
        "\<forall>i < rounds.
          partial_authenticated_table (hd composition_fri_roots)
            (scale * clength) (composition_openings ! i) final_state"
        using comp_tables root_eq by simp
      show ?thesis
        unfolding accepted_with_partial_composition_openings_def accepted_def
        by (intro conjI exI[of _ result] exI[of _ final_state])
          (use len_query_idxs len_comp all_indices all_tables in simp_all)
    qed
    have aligned:
      "accepted_with_partial_initial_openings_aligned s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    proof -
      have accepted_out: "accepted (Some (result, final_state))"
        using trace_partial
        by (rule accepted_with_partial_trace_openings_imp_accepted)
      show ?thesis
        unfolding accepted_with_partial_initial_openings_aligned_def
        by (intro conjI exI[of _ rest])
          (use accepted_out comp_nonempty header0 trace_partial comp_partial
            in simp_all)
    qed
    have all_consistent:
      "\<forall>i < rounds.
        partial_query_round_consistent trace_openings composition_openings as i
          (query_idxs ! i)"
      using consistent by blast
    have aligned_consistent:
      "accepted_with_partial_initial_openings_aligned_consistent s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
      unfolding accepted_with_partial_initial_openings_aligned_consistent_def
      using aligned all_consistent by simp
    show ?thesis
      by (rule that[OF aligned_consistent])
  qed
qed

lemma query_rounds_replay_accepted_with_partial_initial_openings_aligned_transcript_consistent:
  assumes header0:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and fl_eq: "fl = (b, composition_root) # fl_tail"
    and f_roots: "map snd f_fl = f_fri_roots"
    and comp_roots: "map snd fl = composition_fri_roots"
    and query_state_transcript: "PTranscript query_state = rest"
    and query_state_state:
      "PState query_state =
        verifier_header_state s fr f_fri_roots f_final as dg
          composition_fri_roots final"
    and query_state_counter: "PQueryCounter query_state = PQueryCounter s"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
  obtains trace_openings composition_openings where
    "accepted_with_partial_initial_openings_aligned_transcript_consistent s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
proof -
  from query_rounds_replay_accepted_with_partial_initial_openings_aligned_consistent
      [OF header0 comp_nonempty fl_eq f_roots comp_roots query_out
        len_raw query_idxs_eq len_query_chunks transcript_query
        query_chunk replay_lookup]
  obtain trace_openings composition_openings where aligned:
    "accepted_with_partial_initial_openings_aligned_consistent s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by blast
  have transcript_rest:
    "List.concat query_chunks @ PTranscript final_state = rest"
    using transcript_query query_state_transcript by simp
  have chunks:
    "\<forall>i < rounds.
      verifier_query_round_chunk (query_idxs ! i)
        f_fri_roots composition_fri_roots (query_chunks ! i)"
    using query_chunk f_roots comp_roots by simp
  have lookups:
    "\<forall>i<rounds.
      fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks
            (verifier_header_state s fr f_fri_roots f_final as dg
              composition_fri_roots final)
            query_chunks i)) =
      Some (raw_idxs ! i)"
    using replay_lookup query_state_state query_state_counter by simp
  have idx_bounds:
    "\<forall>idx \<in> set query_idxs. idx < clength * scale"
  proof
    fix idx
    assume "idx \<in> set query_idxs"
    then obtain raw where raw: "raw \<in> set raw_idxs"
      and idx: "idx = index (to_nat raw)"
      unfolding query_idxs_eq by auto
    have "index (to_nat raw) < query_sample_space_size"
      by (rule index_less_query_sample_space)
    also have "... \<le> clength * scale"
      by (rule query_sample_space_size_le_domain)
    finally show "idx < clength * scale"
      using idx by simp
  qed
  have derived:
    "verifier_query_indices_derived s (Some (result, final_state))
      (verifier_header_state s fr f_fri_roots f_final as dg
        composition_fri_roots final)
      rest f_fri_roots composition_fri_roots query_idxs"
    unfolding verifier_query_indices_derived_def
    by (intro exI[of _ result] exI[of _ final_state]
        exI[of _ raw_idxs] exI[of _ query_chunks]
        exI[of _ "PTranscript final_state"] conjI)
      (use len_raw query_idxs_eq len_query_chunks transcript_rest chunks
        lookups idx_bounds in auto)
  have shape:
    "accepted_transcript_shape s (Some (result, final_state)) as query_idxs"
    unfolding accepted_transcript_shape_def
    by (intro exI[of _ result] exI[of _ final_state] exI[of _ fr]
        exI[of _ f_fri_roots] exI[of _ f_final] exI[of _ dg]
        exI[of _ composition_fri_roots] exI[of _ final]
        exI[of _ rest] conjI)
      (use header0 derived in simp_all)
  have tied:
    "accepted_with_partial_initial_openings_aligned_transcript_consistent s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    unfolding
      accepted_with_partial_initial_openings_aligned_transcript_consistent_def
    using aligned shape by simp
  show ?thesis
    by (rule that[OF tied])
qed

end

end
