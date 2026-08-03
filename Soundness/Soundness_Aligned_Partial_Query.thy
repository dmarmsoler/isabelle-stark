(*  Title:      Stark/Soundness_Aligned_Partial_Query.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Aligned_Partial_Query
  imports Soundness_Partial_Initial_Aligned
begin

text \<open>
  Aligned partial-candidate query events.

  This layer records the query-bad shape needed by the staged prefix-target
  proof: one shared verifier query-index list for trace and composition
  openings, together with the local composition equation checked in each query
  round.  It is downstream of the staged query-opening extraction layer to
  avoid import cycles with the core deterministic reductions.
\<close>

context soundness
begin

definition accepted_with_partial_initial_openings_aligned_consistent
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> bool"
where
  "accepted_with_partial_initial_openings_aligned_consistent s out fr
      f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings \<longleftrightarrow>
    accepted_with_partial_initial_openings_aligned s out fr f_fri_roots
      f_final as dg composition_fri_roots final query_idxs trace_openings
      composition_openings \<and>
    (\<forall>i < rounds.
      partial_query_round_consistent trace_openings composition_openings as i
        (query_idxs ! i))"

definition query_bad_with_aligned_partial_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "query_bad_with_aligned_partial_candidates s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
        query_idxs trace_openings composition_openings trace_table
        composition_table.
      accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      \<not> all_queries_consistent trace_table composition_table as)"

lemma verify_monad_accepted_with_partial_initial_openings_aligned_consistent:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header0:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
  obtains query_idxs trace_openings composition_openings where
    "accepted_with_partial_initial_openings_aligned_consistent s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
proof -
  from verify_monad_accepted_with_partial_initial_openings_aligned
      [OF outcome header0 comp_nonempty]
  obtain query_idxs trace_openings composition_openings where aligned:
    "accepted_with_partial_initial_openings_aligned s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    and consistent:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_query_round_consistent trace_openings composition_openings as i
          (query_idxs ! i)"
    by blast
  have all_consistent:
    "\<forall>i < rounds.
      partial_query_round_consistent trace_openings composition_openings as i
        (query_idxs ! i)"
    using consistent by blast
  have partial:
    "accepted_with_partial_initial_openings_aligned_consistent s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    unfolding accepted_with_partial_initial_openings_aligned_consistent_def
    using aligned all_consistent by simp
  show ?thesis
    by (rule that[OF partial])
qed

definition soundness_bad_event_aligned_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "soundness_bad_event_aligned_partial_candidate s out \<longleftrightarrow>
    composition_bad_with_partial_candidates s out \<or>
    trace_fri_bad_with_partial_candidates s out \<or>
    composition_fri_bad_with_partial_candidates s out \<or>
    query_bad_with_aligned_partial_candidates s out"

definition soundness_bad_event_aligned_partial_candidate_with_partial_merkle
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "soundness_bad_event_aligned_partial_candidate_with_partial_merkle s out \<longleftrightarrow>
    partial_merkle_inconsistency_bad s out \<or>
    soundness_bad_event_aligned_partial_candidate s out"

lemma accepted_with_partial_initial_openings_aligned_consistent_imp_aligned:
  assumes
    "accepted_with_partial_initial_openings_aligned_consistent s out fr
      f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings"
  shows
    "accepted_with_partial_initial_openings_aligned s out fr f_fri_roots
      f_final as dg composition_fri_roots final query_idxs trace_openings
      composition_openings"
  using assms
  unfolding accepted_with_partial_initial_openings_aligned_consistent_def
  by simp

lemma accepted_with_partial_initial_openings_aligned_consistent_imp_unaligned:
  assumes
    "accepted_with_partial_initial_openings_aligned_consistent s out fr
      f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings"
  shows
    "accepted_with_partial_initial_openings s out fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings query_idxs
      composition_openings"
  by (rule accepted_with_partial_initial_openings_aligned_imp_unaligned)
    (rule accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
      [OF assms])

lemma accepted_with_partial_initial_openings_aligned_consistent_success_index:
  assumes partial:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings"
    and i_bound: "i < rounds"
  shows
    "query_idxs ! i \<in>
      partial_query_success_indices_at trace_openings composition_openings
        as i"
  using partial i_bound
  unfolding accepted_with_partial_initial_openings_aligned_consistent_def
    partial_query_success_indices_at_def partial_query_round_consistent_def
  by simp

lemma query_bad_with_aligned_partial_candidates_imp_query_bad_with_partial_candidates:
  assumes "query_bad_with_aligned_partial_candidates s out"
  shows "query_bad_with_partial_candidates s out"
proof -
  from assms obtain fr f_fri_roots f_final as dg composition_fri_roots
      final query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings"
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
    unfolding query_bad_with_aligned_partial_candidates_def by blast
  have unaligned:
    "accepted_with_partial_initial_openings s out fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings query_idxs
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_consistent_imp_unaligned
        [OF partial])
  show ?thesis
    unfolding query_bad_with_partial_candidates_def
    using unaligned trace_candidate comp_candidate trace_low comp_low not_all
    by blast
qed

lemma soundness_bad_event_aligned_partial_candidate_imp_partial_candidate:
  assumes "soundness_bad_event_aligned_partial_candidate s out"
  shows "soundness_bad_event_partial_candidate s out"
  using assms query_bad_with_aligned_partial_candidates_imp_query_bad_with_partial_candidates
  unfolding soundness_bad_event_aligned_partial_candidate_def
    soundness_bad_event_partial_candidate_def
  by blast

lemma soundness_bad_event_aligned_partial_candidate_with_partial_merkle_imp_partial_candidate_with_partial_merkle:
  assumes
    "soundness_bad_event_aligned_partial_candidate_with_partial_merkle s out"
  shows "soundness_bad_event_partial_candidate_with_partial_merkle s out"
  using assms soundness_bad_event_aligned_partial_candidate_imp_partial_candidate
  unfolding soundness_bad_event_aligned_partial_candidate_with_partial_merkle_def
    soundness_bad_event_partial_candidate_with_partial_merkle_def
  by blast

lemma accepted_aligned_partial_candidate_partition:
  assumes false_statement: "\<not> exists_valid_trace"
    and partial:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
  shows "soundness_bad_event_aligned_partial_candidate s out"
proof (cases "trace_table_low_degree trace_table")
  case False
  have "trace_fri_bad_with_partial_candidates s out"
    unfolding trace_fri_bad_with_partial_candidates_def
    using accepted_with_partial_initial_openings_aligned_consistent_imp_unaligned
        [OF partial]
      trace_candidate False by blast
  then show ?thesis
    unfolding soundness_bad_event_aligned_partial_candidate_def by blast
next
  case True
  note trace_low = True
  show ?thesis
  proof (cases "composition_table_low_degree maxDegree composition_table")
    case False
    have "composition_fri_bad_with_partial_candidates s out"
      unfolding composition_fri_bad_with_partial_candidates_def
      using accepted_with_partial_initial_openings_aligned_consistent_imp_unaligned
          [OF partial]
        trace_candidate composition_candidate trace_low False
      by blast
    then show ?thesis
      unfolding soundness_bad_event_aligned_partial_candidate_def by blast
  next
    case True
    note composition_low = True
    show ?thesis
    proof (cases "all_queries_consistent trace_table composition_table as")
      case False
      have "query_bad_with_aligned_partial_candidates s out"
        unfolding query_bad_with_aligned_partial_candidates_def
        using partial trace_candidate composition_candidate trace_low
          composition_low False
        by blast
      then show ?thesis
        unfolding soundness_bad_event_aligned_partial_candidate_def by blast
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
      have "composition_bad_with_partial_candidates s out"
        unfolding composition_bad_with_partial_candidates_def
        using accepted_with_partial_initial_openings_aligned_consistent_imp_unaligned
            [OF partial]
          trace_candidate composition_candidate deg_f trace_table_eq
          violated composition_low all_queries
        by blast
      then show ?thesis
        unfolding soundness_bad_event_aligned_partial_candidate_def by blast
    qed
  qed
qed

lemma soundness_bad_event_aligned_partial_candidate_union_bound:
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
        (query_bad_with_aligned_partial_candidates s) s \<le>
        query_error"
  shows
    "wp_event verify_monad
      (soundness_bad_event_aligned_partial_candidate s) s \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
proof -
  have "wp_event verify_monad
      (soundness_bad_event_aligned_partial_candidate s) s \<le>
      wp_event verify_monad
        (composition_bad_with_partial_candidates s) s +
      wp_event verify_monad
        (trace_fri_bad_with_partial_candidates s) s +
      wp_event verify_monad
        (composition_fri_bad_with_partial_candidates s) s +
      wp_event verify_monad
        (query_bad_with_aligned_partial_candidates s) s"
    unfolding soundness_bad_event_aligned_partial_candidate_def
    by (rule wp_event_union_bound4)
  also have "... \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
    by (intro add_mono comp_bound trace_fri_bound comp_fri_bound
        query_bound)
  finally show ?thesis .
qed

lemma soundness_bad_event_aligned_partial_candidate_with_partial_merkle_union_bound:
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
        (query_bad_with_aligned_partial_candidates s) s \<le>
        query_error"
  shows
    "wp_event verify_monad
      (soundness_bad_event_aligned_partial_candidate_with_partial_merkle s) s
      \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
proof -
  have partial_bound:
    "wp_event verify_monad
      (soundness_bad_event_aligned_partial_candidate s) s \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
    by (rule soundness_bad_event_aligned_partial_candidate_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  have "wp_event verify_monad
      (soundness_bad_event_aligned_partial_candidate_with_partial_merkle s) s
      \<le>
      wp_event verify_monad (partial_merkle_inconsistency_bad s) s +
      wp_event verify_monad
        (soundness_bad_event_aligned_partial_candidate s) s"
    unfolding
      soundness_bad_event_aligned_partial_candidate_with_partial_merkle_def
    by (rule wp_event_union_bound)
  also have "... \<le>
      merkle_error +
      (composition_error + trace_fri_error' + composition_fri_error' +
        query_error)"
    by (intro add_mono merkle_bound partial_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_data_state_aligned_partial_candidate_with_partial_merkle_union_bound:
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
          query_bad_with_aligned_partial_candidates)
        adversary_initial_state \<le> query_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_partial_candidate_with_partial_merkle)
      adversary_initial_state \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?merkle = "?E partial_merkle_inconsistency_bad"
  let ?comp = "?E composition_bad_with_partial_candidates"
  let ?trace = "?E trace_fri_bad_with_partial_candidates"
  let ?comp_fri = "?E composition_fri_bad_with_partial_candidates"
  let ?query = "?E query_bad_with_aligned_partial_candidates"
  let ?partial = "?E soundness_bad_event_aligned_partial_candidate"
  let ?with_merkle =
    "?E soundness_bad_event_aligned_partial_candidate_with_partial_merkle"
  have partial_bound:
    "wp_event ?M ?partial adversary_initial_state \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
  proof -
    have "wp_event ?M ?partial adversary_initial_state \<le>
        wp_event ?M
          (\<lambda>out. ?comp out \<or> ?trace out \<or> ?comp_fri out \<or>
            ?query out)
          adversary_initial_state"
      by (rule wp_event_mono)
        (auto simp: staged_security_with_data_state_verifier_event_def
          soundness_bad_event_aligned_partial_candidate_def
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
  have "wp_event ?M ?with_merkle adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?merkle out \<or> ?partial out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        soundness_bad_event_aligned_partial_candidate_with_partial_merkle_def
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

lemma query_bad_with_aligned_partial_candidates_success_indexE:
  assumes bad: "query_bad_with_aligned_partial_candidates s out"
    and i_bound: "i < rounds"
  obtains fr f_fri_roots f_final as dg composition_fri_roots final
      query_idxs trace_openings composition_openings trace_table
      composition_table where
    "accepted_with_partial_initial_openings_aligned_consistent s out fr
      f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "trace_table_low_degree trace_table"
    "composition_table_low_degree maxDegree composition_table"
    "\<not> all_queries_consistent trace_table composition_table as"
    "query_idxs ! i \<in>
      partial_query_success_indices_at trace_openings composition_openings
        as i"
proof -
  from bad obtain fr f_fri_roots f_final as dg composition_fri_roots
      final query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings"
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
    unfolding query_bad_with_aligned_partial_candidates_def by blast
  have success:
    "query_idxs ! i \<in>
      partial_query_success_indices_at trace_openings composition_openings
        as i"
    by (rule
        accepted_with_partial_initial_openings_aligned_consistent_success_index
        [OF partial i_bound])
  show ?thesis
    by (rule that[OF partial trace_candidate comp_candidate trace_low comp_low
          not_all success])
qed

lemma query_bad_with_aligned_partial_candidates_target_fractionE:
  assumes bad: "query_bad_with_aligned_partial_candidates s out"
    and i_bound: "i < rounds"
  obtains fr f_fri_roots f_final as dg composition_fri_roots final
      query_idxs trace_openings composition_openings trace_table
      composition_table where
    "accepted_with_partial_initial_openings_aligned_consistent s out fr
      f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings"
    "query_idxs ! i \<in>
      partial_query_success_indices_at trace_openings composition_openings
        as i"
    "nnreal
      (card
        (partial_query_success_indices_at trace_openings composition_openings
          as i)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof -
  from query_bad_with_aligned_partial_candidates_success_indexE
      [OF bad i_bound]
  obtain fr f_fri_roots f_final as dg composition_fri_roots final
      query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings"
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
    and success:
      "query_idxs ! i \<in>
        partial_query_success_indices_at trace_openings composition_openings
          as i"
    by blast
  have fraction:
    "nnreal
      (card
        (partial_query_success_indices_at trace_openings composition_openings
          as i)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
    by (rule partial_query_success_indices_at_fraction_bound_if_candidate_low_degree
        [OF trace_candidate comp_candidate trace_low comp_low not_all])
  show ?thesis
    by (rule that[OF partial success fraction])
qed

lemma query_bad_with_aligned_partial_candidates_miss_disagreements:
  assumes bad: "query_bad_with_aligned_partial_candidates s out"
  shows "\<exists>trace_table composition_table as query_idxs.
    query_samples_miss_disagreements trace_table composition_table as
      query_idxs"
proof -
  from bad obtain fr f_fri_roots f_final as dg composition_fri_roots
      final query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings"
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
    unfolding query_bad_with_aligned_partial_candidates_def by blast
  have aligned:
    "accepted_with_partial_initial_openings_aligned s out fr f_fri_roots
      f_final as dg composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
        [OF partial])
  have trace_partial:
    "accepted_with_partial_trace_openings s out fr query_idxs
      trace_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(3)
        [OF aligned] .
  have len_query: "length query_idxs = rounds"
    using accepted_with_partial_trace_openings_shapes(1)[OF trace_partial] .
  have nonempty_disagreements:
    "query_disagreement_indices trace_table composition_table as \<noteq> {}"
    using not_all
    unfolding query_disagreement_indices_def bad_query_indices_def
      all_queries_consistent_def
    by auto
  have subset_agreement:
    "set query_idxs \<subseteq>
      query_agreement_indices trace_table composition_table as"
  proof
    fix idx
    assume idx_in: "idx \<in> set query_idxs"
    then obtain i where i_len: "i < length query_idxs"
      and idx_eq: "query_idxs ! i = idx"
      by (auto simp: in_set_conv_nth)
    have i_bound: "i < rounds"
      using i_len len_query by simp
    have success:
      "query_idxs ! i \<in>
        partial_query_success_indices_at trace_openings composition_openings
          as i"
      by (rule
          accepted_with_partial_initial_openings_aligned_consistent_success_index
          [OF partial i_bound])
    have success_space:
      "query_idxs ! i \<in>
        query_sampling_success_space trace_table composition_table as"
      using success
        partial_query_success_indices_at_subset_query_sampling_success_space
          [OF trace_candidate comp_candidate trace_low comp_low not_all,
            of i]
      by blast
    then show "idx \<in>
        query_agreement_indices trace_table composition_table as"
      using idx_eq trace_low comp_low not_all
      unfolding query_sampling_success_space_def by simp
  qed
  have
    "query_samples_miss_disagreements trace_table composition_table as
      query_idxs"
    unfolding query_samples_miss_disagreements_def
    using nonempty_disagreements subset_agreement by simp
  then show ?thesis by blast
qed

end

end
