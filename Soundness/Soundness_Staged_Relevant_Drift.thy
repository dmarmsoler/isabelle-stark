(*  Title:      Stark/Soundness_Staged_Relevant_Drift.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Relevant_Drift
  imports
    Soundness_Staged_Aligned_Current_Empty
    Staged_Security_Experiment_Composition_Query_Aligned_Witness_Bridge
begin

text \<open>
  Small downstream layer for the refined relevant-drift event.  The purpose is
  to keep diagnostic and bridge lemmas out of the already large current-empty
  packaging theory.
\<close>

context soundness
begin

definition composition_randomization_bad_with_aligned_transcript_partial_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_randomization_bad_with_aligned_transcript_partial_candidates
      s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
        query_idxs trace_openings composition_openings trace_table
        composition_table f.
      accepted_with_partial_initial_openings_aligned_transcript_consistent s
        out fr f_fri_roots f_final as dg composition_fri_roots final
        query_idxs trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      degree f < clength \<and>
      trace_table = map (poly f) eval_domain \<and>
      violated_constraints f \<noteq> {} \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as \<and>
      common_denominator_degree_bounds f as \<and>
      random_combination_common_denominator_hides_violations f as)"

definition soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization
      s out \<longleftrightarrow>
    composition_randomization_bad_with_aligned_transcript_partial_candidates
      s out \<or>
    trace_fri_bad_with_partial_candidates s out \<or>
    composition_fri_bad_with_partial_candidates s out \<or>
    query_bad_with_aligned_transcript_partial_candidates s out"

definition soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle
      s out \<longleftrightarrow>
    partial_merkle_inconsistency_bad s out \<or>
    soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization
      s out"

lemma accepted_aligned_transcript_partial_candidate_partition_aligned_randomization:
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
  shows
    "trace_fri_bad_with_partial_candidates s out \<or>
     composition_fri_bad_with_partial_candidates s out \<or>
     query_bad_with_aligned_transcript_partial_candidates s out \<or>
     composition_randomization_bad_with_aligned_transcript_partial_candidates
      s out"
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
  then show ?thesis by blast
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
    then show ?thesis by blast
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
      then show ?thesis by blast
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
      have unaligned:
        "accepted_with_partial_initial_openings s out fr f_fri_roots f_final
          as dg composition_fri_roots final query_idxs trace_openings
          query_idxs composition_openings"
        by (rule
            accepted_with_partial_initial_openings_aligned_consistent_imp_unaligned
            [OF aligned])
      have len_as: "length as = length spec"
        by (rule accepted_with_partial_initial_openings_alpha_length
            [OF unaligned])
      have bounds: "common_denominator_degree_bounds f as"
        by (rule common_denominator_degree_bounds_from_spec_degree_wellformed
            [OF spec_degree_wellformed_from_spec_query_margin deg_f])
      have hides:
        "random_combination_common_denominator_hides_violations f as"
        by (rule random_combination_common_denominator_hides_from_queries
            [OF len_as false_statement deg_f trace_table_eq composition_low
              all_queries bounds])
      have
        "composition_randomization_bad_with_aligned_transcript_partial_candidates
          s out"
        unfolding
          composition_randomization_bad_with_aligned_transcript_partial_candidates_def
        using partial trace_candidate composition_candidate deg_f
          trace_table_eq violated composition_low all_queries bounds hides
        by blast
      then show ?thesis by blast
    qed
  qed
qed

lemma accepted_aligned_transcript_partial_candidate_partition_with_aligned_randomization_event:
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
  shows
    "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization
      s out"
  using
    accepted_aligned_transcript_partial_candidate_partition_aligned_randomization
      [OF false_statement partial trace_candidate composition_candidate]
  unfolding
    soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_def
  by blast

lemma checked_staged_security_with_data_state_aligned_transcript_partial_candidate_aligned_randomization_union_bound:
  fixes composition_error trace_fri_error' composition_fri_error'
    query_error :: prob
  assumes comp_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_randomization_bad_with_aligned_transcript_partial_candidates)
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
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization)
      adversary_initial_state \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?comp =
    "?E composition_randomization_bad_with_aligned_transcript_partial_candidates"
  let ?trace = "?E trace_fri_bad_with_partial_candidates"
  let ?comp_fri = "?E composition_fri_bad_with_partial_candidates"
  let ?query = "?E query_bad_with_aligned_transcript_partial_candidates"
  let ?partial =
    "?E soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization"
  have "wp_event ?M ?partial adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?comp out \<or> ?trace out \<or> ?comp_fri out \<or>
          ?query out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_def
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

lemma checked_staged_security_with_data_state_aligned_transcript_partial_candidate_aligned_randomization_with_merkle_union_bound:
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
          composition_randomization_bad_with_aligned_transcript_partial_candidates)
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
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle)
      adversary_initial_state \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
proof -
  have partial_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization)
      adversary_initial_state \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_partial_candidate_aligned_randomization_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization)
        adversary_initial_state"
  proof -
    have event_le:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle)
        adversary_initial_state \<le>
        wp_event (checked_staged_security_experiment_with_data_state A)
          (\<lambda>out.
            staged_security_with_data_state_verifier_event
              partial_merkle_inconsistency_bad out \<or>
            staged_security_with_data_state_verifier_event
              soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization
              out)
          adversary_initial_state"
      by (rule wp_event_mono)
        (auto simp: staged_security_with_data_state_verifier_event_def
          soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_def
          split: option.splits prod.splits)
    also have "... \<le>
        wp_event (checked_staged_security_experiment_with_data_state A)
          (staged_security_with_data_state_verifier_event
            partial_merkle_inconsistency_bad)
          adversary_initial_state +
        wp_event (checked_staged_security_experiment_with_data_state A)
          (staged_security_with_data_state_verifier_event
            soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization)
          adversary_initial_state"
      by (rule wp_event_union_bound)
    finally show ?thesis .
  qed
  also have "... \<le>
      merkle_error +
      (composition_error + trace_fri_error' + composition_fri_error' +
        query_error)"
    by (intro add_mono merkle_bound partial_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_if_header_nonempty:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
  shows
    "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle
      s out"
proof -
  from acc obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  from verify_monad_supplied_header_transcript_shape
      [OF supp[unfolded out_eq] header]
  obtain query_idxs raw_idxs query_chunks where shape:
      "accepted_transcript_shape s (Some (result, final_state)) as query_idxs"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_rest:
      "List.concat query_chunks @ PTranscript final_state = rest"
    and query_chunk_header:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          f_fri_roots composition_fri_roots (query_chunks ! i)"
    and replay_lookup_header:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks
              (verifier_header_state s fr f_fri_roots f_final as dg
                composition_fri_roots final)
              query_chunks i)) =
        Some (raw_idxs ! i)"
    by blast
  from verify_monad_supplied_header_query_rounds
      [OF supp[unfolded out_eq] header]
  obtain f_fl fl query_state where f_roots:
      "map snd f_fl = f_fri_roots"
    and comp_roots: "map snd fl = composition_fri_roots"
    and query_transcript_state: "PTranscript query_state = rest"
    and query_hash_state:
      "PState query_state =
        verifier_header_state s fr f_fri_roots f_final as dg
          composition_fri_roots final"
    and query_counter: "PQueryCounter query_state = PQueryCounter s"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    by blast
  have fl_nonempty: "fl \<noteq> []"
    using comp_nonempty comp_roots by (cases fl) simp_all
  then obtain b composition_root fl_tail where fl_eq:
    "fl = (b, composition_root) # fl_tail"
    by (cases fl) auto
  have transcript_query:
    "PTranscript query_state =
      List.concat query_chunks @ PTranscript final_state"
    using query_transcript_state transcript_rest by simp
  have query_chunk:
    "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (query_idxs ! i)
        (map snd f_fl) (map snd fl) (query_chunks ! i)"
    using query_chunk_header f_roots comp_roots by simp
  have replay_lookup:
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) query_chunks i)) =
      Some (raw_idxs ! i)"
    using replay_lookup_header query_hash_state query_counter by simp
  from
    query_rounds_replay_accepted_with_partial_initial_openings_aligned_transcript_consistent
      [OF header comp_nonempty fl_eq f_roots comp_roots
        query_transcript_state query_hash_state query_counter query_out
        len_raw query_idxs_eq len_query_chunks transcript_query query_chunk
        replay_lookup]
  obtain trace_openings composition_openings where partial:
    "accepted_with_partial_initial_openings_aligned_transcript_consistent s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by blast
  show ?thesis
  proof (cases
      "partial_merkle_inconsistency_bad s (Some (result, final_state))")
    case True
    then show ?thesis
      unfolding out_eq
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_def
      by simp
  next
    case False
    have aligned0:
      "accepted_with_partial_initial_openings_aligned s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
      using partial
      by (blast dest:
          accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
          accepted_with_partial_initial_openings_aligned_consistent_imp_aligned)
    obtain trace_table composition_table where trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
      and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
      using
        accepted_with_partial_initial_openings_aligned_candidates_if_no_partial_merkle_bad
        [OF aligned0 False]
      by blast
    have bad:
      "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization
        s (Some (result, final_state))"
      by (rule
          accepted_aligned_transcript_partial_candidate_partition_with_aligned_randomization_event
          [OF false_statement partial trace_candidate composition_candidate])
    then show ?thesis
      unfolding out_eq
      by (simp add:
          soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_def)
  qed
qed

lemma accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_or_empty_header:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  shows
    "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle
        s out \<or>
     soundness_bad_event_partial_candidate_empty_header s out"
proof (cases "composition_fri_roots = []")
  case False
  then have comp_nonempty: "composition_fri_roots \<noteq> []"
    by simp
  have
    "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle
      s out"
    by (rule
        accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_if_header_nonempty
        [OF false_statement supp acc header comp_nonempty])
  then show ?thesis by simp
next
  case True
  note comp_empty = True
  from acc obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  show ?thesis
  proof (cases
      "partial_merkle_inconsistency_bad s (Some (result, final_state))")
    case True
    then have
      "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle
        s out"
      unfolding out_eq
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_def
      by simp
    then show ?thesis by simp
  next
    case False
    from verify_monad_accepted_with_partial_trace_openings_for_header
        [OF supp[unfolded out_eq] header]
    obtain trace_query_idxs trace_openings where trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
      by blast
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
        trace_query_idxs trace_openings trace_table ?composition_table"
      unfolding accepted_with_empty_composition_header_candidates_def
      by (intro conjI exI[of _ rest])
        (use accepted_out header comp_empty trace_partial trace_candidate
          in simp_all)
    have "soundness_bad_event_partial_candidate_empty_header s
        (Some (result, final_state))"
      by (rule accepted_empty_composition_header_candidate_partition
          [OF false_statement empty_partial])
    then show ?thesis
      unfolding out_eq by simp
  qed
qed

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_and_empty_header_bounds:
  fixes partial_candidate_error empty_header_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and partial_candidate_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle)
        adversary_initial_state \<le> partial_candidate_error"
    and empty_header_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_partial_candidate_empty_header)
        adversary_initial_state \<le> empty_header_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    partial_candidate_error + empty_header_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?partial =
    "?E soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle"
  let ?empty = "?E soundness_bad_event_partial_candidate_empty_header"
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
        "soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle
            ?s (Some (result, final_state)) \<or>
         soundness_bad_event_partial_candidate_empty_header ?s
            (Some (result, final_state))"
        by (rule
            accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_or_empty_header
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

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_components_and_empty_header_bound:
  fixes merkle_error composition_error trace_fri_error'
    composition_fri_error' query_error empty_header_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and merkle_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state \<le> merkle_error"
    and comp_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_randomization_bad_with_aligned_transcript_partial_candidates)
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
    and empty_header_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_partial_candidate_empty_header)
        adversary_initial_state \<le> empty_header_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    merkle_error + composition_error + trace_fri_error' +
    composition_fri_error' + query_error + empty_header_error"
proof -
  have partial_candidate_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle)
      adversary_initial_state \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_partial_candidate_aligned_randomization_with_merkle_union_bound
        [OF merkle_bound comp_bound trace_fri_bound comp_fri_bound
          query_bound])
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      (merkle_error + composition_error + trace_fri_error' +
        composition_fri_error' + query_error) + empty_header_error"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_and_empty_header_bounds
        [OF false_statement partial_candidate_bound empty_header_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_current_query_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
  shows
    "staged_security_with_data_state_current_query_partial_opening_hit
      (Some (((data, attacker_state), result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support]
  obtain builder verifier where builder:
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
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as
      query_idxs"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_shape
        [OF partial])
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled support shape]
  obtain raw_idxs where as_eq: "as = staged_alphas data"
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
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  have aligned0:
    "accepted_with_partial_initial_openings_aligned ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
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
  have trace_auth:
    "partial_authenticated_table (staged_trace_root data)
      (scale * clength) (trace_openings ! ?i) final_state"
    using trace_partial i_bound header_eq
    unfolding accepted_with_partial_trace_openings_def by blast
  have comp_auth:
    "partial_authenticated_table (hd (staged_composition_fri_roots data))
      (scale * clength) (composition_openings ! ?i) final_state"
    using comp_partial i_bound header_eq
    unfolding accepted_with_partial_composition_openings_def by blast
  have final_lookup:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge ?i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) ?i)) =
      Some (raw_idxs ! ?i)"
    using lookup i_bound by simp
  have idx_raw:
    "query_idxs ! ?i = index (to_nat (raw_idxs ! ?i))"
    using query_idxs_eq len_raw i_bound by simp
  have hit_at:
    "staged_security_with_data_state_current_query_partial_opening_hit_at ?i
      (Some (((data, attacker_state), result), final_state))"
    unfolding staged_security_with_data_state_current_query_partial_opening_hit_at_def
      Let_def
    apply simp
    by (intro exI[of _ "raw_idxs ! ?i"]
        exI[of _ "trace_openings ! ?i"]
        exI[of _ "composition_openings ! ?i"] exI[of _ rest] conjI)
      (use i_bound final_lookup comp_nonempty verifier trace_auth comp_auth
        staged_header opening_consistent idx_raw header_eq as_eq in simp_all)
  show ?thesis
    by (rule staged_security_with_data_state_current_query_partial_opening_hitI
        [OF i_bound hit_at])
qed

lemma checked_staged_security_with_data_state_aligned_partial_candidate_randomization_imp_current_query_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates
        out"
  shows "staged_security_with_data_state_current_query_partial_opening_hit out"
proof (cases out)
  case None
  then show ?thesis
    using bad
    unfolding staged_security_with_data_state_verifier_event_def
      composition_randomization_bad_with_aligned_transcript_partial_candidates_def
    by simp
next
  case (Some packed)
  then obtain data attacker_state result final_state where out_eq:
      "out = Some (((data, attacker_state), result), final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have bad_some:
    "composition_randomization_bad_with_aligned_transcript_partial_candidates
      ?s (Some (result, final_state))"
    using bad
    unfolding out_eq staged_security_with_data_state_verifier_event_def
      Let_def
    by simp
  obtain fr f_fri_roots f_final as dg composition_fri_roots final
      query_idxs trace_openings composition_openings trace_table
      composition_table f
    where partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent
        ?s (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    using bad_some
    unfolding
      composition_randomization_bad_with_aligned_transcript_partial_candidates_def
    by blast
  show ?thesis
    unfolding out_eq
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_current_query_on_support
        [OF wf controlled support[unfolded out_eq] partial])
qed

lemma checked_staged_security_with_data_state_aligned_partial_candidate_randomization_le_current_query:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state"
  by (rule wp_event_mono_on_support)
    (rule
      checked_staged_security_with_data_state_aligned_partial_candidate_randomization_imp_current_query_on_support
      [OF wf controlled])

lemma checked_staged_security_with_data_state_aligned_partial_candidate_randomization_bound_from_query_prefix_current_rounds:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
proof -
  have current_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds
        [OF round_bound wf controlled])
  show ?thesis
    by (rule order_trans[
        OF
          checked_staged_security_with_data_state_aligned_partial_candidate_randomization_le_current_query
          current_bound])
      (use wf controlled in simp_all)
qed

lemma checked_staged_security_with_data_state_aligned_randomization_or_query_bad_le_current_query:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_verifier_event
          composition_randomization_bad_with_aligned_transcript_partial_candidates
          out \<or>
        staged_security_with_data_state_verifier_event
          query_bad_with_aligned_transcript_partial_candidates out)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
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
        composition_randomization_bad_with_aligned_transcript_partial_candidates
        out \<or>
       staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates out"
  show
    "staged_security_with_data_state_current_query_partial_opening_hit out"
  proof (cases
      "staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates
        out")
    case True
    then show ?thesis
      by (rule
          checked_staged_security_with_data_state_aligned_partial_candidate_randomization_imp_current_query_on_support
          [OF wf controlled support])
  next
    case False
    then have query_bad:
      "staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates out"
      using bad by simp
    show ?thesis
    proof (cases out)
      case None
      then show ?thesis
        using query_bad
        unfolding staged_security_with_data_state_verifier_event_def
          query_bad_with_aligned_transcript_partial_candidates_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      show ?thesis
        unfolding out_eq
        by (rule
            checked_staged_security_with_data_state_aligned_transcript_query_bad_imp_current_partial_opening_hit_on_support
            [OF wf controlled support[unfolded out_eq]
              query_bad[unfolded out_eq]])
    qed
  qed
qed

lemma checked_staged_security_with_data_state_aligned_transcript_partial_candidate_aligned_randomization_with_merkle_current_query_union_bound:
  fixes merkle_error current_query_error trace_fri_error'
    composition_fri_error' :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and merkle_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state \<le> merkle_error"
    and current_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_current_query_partial_opening_hit
        adversary_initial_state \<le> current_query_error"
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
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle)
      adversary_initial_state \<le>
      merkle_error + current_query_error + trace_fri_error' +
      composition_fri_error'"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?merkle = "?E partial_merkle_inconsistency_bad"
  let ?comp =
    "?E composition_randomization_bad_with_aligned_transcript_partial_candidates"
  let ?trace = "?E trace_fri_bad_with_partial_candidates"
  let ?comp_fri = "?E composition_fri_bad_with_partial_candidates"
  let ?query = "?E query_bad_with_aligned_transcript_partial_candidates"
  let ?current =
    "staged_security_with_data_state_current_query_partial_opening_hit"
  let ?combined = "\<lambda>out. ?comp out \<or> ?query out"
  let ?partial =
    "?E soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle"
  have event_le:
    "wp_event ?M ?partial adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?merkle out \<or> ?combined out \<or> ?trace out \<or>
          ?comp_fri out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle_def
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_def
        split: option.splits prod.splits)
  have union_bound:
    "wp_event ?M
        (\<lambda>out. ?merkle out \<or> ?combined out \<or> ?trace out \<or>
          ?comp_fri out)
        adversary_initial_state \<le>
      wp_event ?M ?merkle adversary_initial_state +
      wp_event ?M ?combined adversary_initial_state +
      wp_event ?M ?trace adversary_initial_state +
      wp_event ?M ?comp_fri adversary_initial_state"
    by (rule wp_event_union_bound4)
  have combined_bound:
    "wp_event ?M ?combined adversary_initial_state \<le>
      wp_event ?M ?current adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_aligned_randomization_or_query_bad_le_current_query
        [OF wf controlled])
  have
    "wp_event ?M ?partial adversary_initial_state \<le>
      wp_event ?M ?merkle adversary_initial_state +
      wp_event ?M ?current adversary_initial_state +
      wp_event ?M ?trace adversary_initial_state +
      wp_event ?M ?comp_fri adversary_initial_state"
    by (rule order_trans[OF event_le])
      (rule order_trans[OF union_bound],
        intro add_mono order_refl combined_bound)
  also have "... \<le>
      merkle_error + current_query_error + trace_fri_error' +
      composition_fri_error'"
    by (intro add_mono merkle_bound current_query_bound trace_fri_bound
        comp_fri_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_aligned_partial_candidate_randomization_imp_current_query_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and bad:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates
        out"
  shows
    "(case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        staged_security_with_data_state_current_query_partial_opening_hit
          (Some (((data, attacker_state), result), final_state)))"
proof (cases out)
  case None
  then show ?thesis
    using bad
    unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      composition_randomization_bad_with_aligned_transcript_partial_candidates_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix alpha_prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have bad_some:
    "composition_randomization_bad_with_aligned_transcript_partial_candidates
      ?s (Some (result, final_state))"
    using bad
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      Let_def
    by simp
  obtain fr f_fri_roots f_final as dg composition_fri_roots final
      query_idxs trace_openings composition_openings trace_table
      composition_table f
    where partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent
        ?s (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    using bad_some
    unfolding
      composition_randomization_bad_with_aligned_transcript_partial_candidates_def
    by blast
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support[unfolded out_eq]])
  have data_hit:
    "staged_security_with_data_state_current_query_partial_opening_hit
      (Some (((data, attacker_state), result), final_state))"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_current_query_on_support
        [OF wf controlled data_support partial])
  then show ?thesis
    unfolding out_eq by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_aligned_partial_candidate_randomization_le_current_query:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (packed, t) \<Rightarrow>
        staged_security_with_data_state_current_query_partial_opening_hit
          (Some (?project packed, t))"
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates)
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
      and bad:
        "checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_randomization_bad_with_aligned_transcript_partial_candidates
          out"
    show "?projected out"
    proof (cases out)
      case None
      then show ?thesis
        using bad
        unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
          composition_randomization_bad_with_aligned_transcript_partial_candidates_def
        by simp
    next
      case (Some packed)
      then obtain alpha_prefix alpha_prefix_state data attacker_state result
          final_state where out_eq:
          "out =
            Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      have hit:
        "staged_security_with_data_state_current_query_partial_opening_hit
          (Some (((data, attacker_state), result), final_state))"
        using
          checked_staged_security_with_actual_alpha_prefix_aligned_partial_candidate_randomization_imp_current_query_on_support
            [OF wf controlled support bad]
        unfolding out_eq by simp
      show ?thesis
        unfolding out_eq using hit by simp
    qed
  qed
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?projected adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state"
  proof -
    have
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_current_query_partial_opening_hit
        adversary_initial_state =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
          \<bind> (\<lambda>x. return (?project x)))
        staged_security_with_data_state_current_query_partial_opening_hit
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
          staged_security_with_data_state_current_query_partial_opening_hit_def
          staged_security_with_data_state_current_query_partial_opening_hit_at_def)
    finally show ?thesis
      by simp
  qed
  show ?thesis
    by (rule order_trans[OF event_le])
      (simp add: projection)
qed

lemma checked_staged_security_with_actual_alpha_prefix_aligned_partial_candidate_randomization_bound_from_query_prefix_current_rounds:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
proof -
  have current_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds
        [OF round_bound wf controlled])
  show ?thesis
    by (rule order_trans[
        OF
          checked_staged_security_with_actual_alpha_prefix_aligned_partial_candidate_randomization_le_current_query
          current_bound])
      (use wf controlled in simp_all)
qed

lemma checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_driftE:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      out"
  obtains
    "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
      composition_trace_bad_alpha_space out"
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad_with_partial_candidates out"
  | "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
      composition_trace_bad_alpha_space out"
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_def
  by blast

lemma checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_le_branches:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad_with_partial_candidates)
    adversary_initial_state +
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header)
    adversary_initial_state"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out.
        checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_randomization_bad_with_partial_candidates out \<or>
        checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_partial_opening_union_hit_with_empty_header out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_def)
  have union_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out.
        checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_randomization_bad_with_partial_candidates out \<or>
        checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_partial_opening_union_hit_with_empty_header out)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_partial_candidates)
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
      adversary_initial_state"
    by (rule wp_event_union_bound)
  show ?thesis
    by (rule order_trans[OF event_le union_le])
qed

lemma checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_branch_bounds:
  assumes random_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_randomization_bad_with_partial_candidates)
        adversary_initial_state \<le> R"
    and empty_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_partial_opening_union_hit_with_empty_header)
        adversary_initial_state \<le> E"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le> R + E"
  by (rule order_trans[
      OF
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_le_branches])
    (intro add_mono random_bound empty_bound)

lemma checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_le_not_prefix_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
        composition_trace_bad_alpha_space)
      adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_def)
  have drift_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_le_not_prefix_bound
        [OF wf controlled])
  show ?thesis
    by (rule order_trans[OF event_le drift_le])
qed

lemma checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_not_prefix_components:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and collision_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
        adversary_initial_state \<le> C"
    and uncovered_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
        adversary_initial_state \<le> U"
    and no_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        adversary_initial_state \<le> N"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
        adversary_initial_state \<le> P"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le> C + U + N + P"
proof -
  have not_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> C + U + N + P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_bound])
  have relevant_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_le_not_prefix_bound
        [OF wf controlled])
  show ?thesis
    by (rule order_trans[OF relevant_le not_prefix_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_cross_and_witness:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and witness_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
        adversary_initial_state \<le> W"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + W + W"
proof -
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
  have no_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le> W"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_le_witness_transcript_hit
          witness_bound])
  have path_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le> W"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_le_witness_transcript_hit
          witness_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_not_prefix_components
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_cross_data_pre_and_witness_new:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R)"
proof -
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
        [OF transcript_pre_bound transcript_new_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_cross_and_witness
        [OF wf controlled cross_bound witness_bound])
qed

lemma checked_staged_soundness_from_aligned_partial_candidate_components_and_current_empty_query_from_cross_data_pre_and_witness_new:
  fixes trace_fri_error' composition_fri_error' query_error X P R
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
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R))) +
    trace_fri_error' + composition_fri_error' +
    query_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + (P + R) + (P + R)) +
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
        [OF wf controlled cross_bound data_pre_bound transcript_new_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_partial_candidate_components_and_current_empty_query_from_relevant_drift
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound drift_bound empty_trace_fri_bound current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_relevant_drift:
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
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds_from_relevant_drift_current_empty:
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
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_current_empty_query_from_relevant_drift
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound drift_bound empty_trace_fri_bound current_empty_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_current_query_prefix_rounds_from_relevant_drift_current_empty:
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
    (\<Sum>i<rounds. C i) +
    trace_fri_error' + composition_fri_error' +
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
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_aligned_partial_candidate_randomization_bound_from_query_prefix_current_rounds
        [OF wf controlled round_bound])
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
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds. C i) +
      trace_fri_error' + composition_fri_error' +
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
        checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
  then show ?thesis .
qed

lemma checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_structured_query_from_relevant_drift_current_empty:
  fixes trace_fri_error' composition_fri_error' D empty_query_error
      header_query_error :: prob
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
    and header_query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
          A)
        adversary_initial_state \<le> header_query_error"
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
    (\<Sum>i<rounds. C i) +
    trace_fri_error' + composition_fri_error' +
    header_query_error +
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
        composition_randomization_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_aligned_partial_candidate_randomization_bound_from_query_prefix_current_rounds
        [OF wf controlled round_bound])
  have query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> header_query_error"
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_header_authenticated_candidate_opening_query_hit_from_prefix
        [OF wf controlled header_query_bound])
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
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      (hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
        (\<Sum>i<rounds. C i) + trace_fri_error' +
        composition_fri_error' + header_query_error) +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        D + trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_current_query_prefix_rounds_from_relevant_drift_current_empty_single_query_charge:
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
    (\<Sum>i<rounds. C i) +
    trace_fri_error' + composition_fri_error' +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error)"
proof -
  have current_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds
        [OF round_bound wf controlled])
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
  have partial_candidate_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds. C i) + trace_fri_error' + composition_fri_error'"
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_partial_candidate_aligned_randomization_with_merkle_current_query_union_bound
        [OF wf controlled merkle_bound current_query_bound trace_fri_bound
          comp_fri_bound])
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
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      (hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
        (\<Sum>i<rounds. C i) + trace_fri_error' +
        composition_fri_error') +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        D + trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_and_empty_header_bounds
        [OF false_statement partial_candidate_bound empty_header_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_soundness_from_aligned_transcript_conceptual_default_alpha_prefix_union_clean_structured_paths_from_relevant_drift_current_empty:
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
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      T i + C i) +
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
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error)"
proof (rule
    checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_current_query_prefix_rounds_from_relevant_drift_current_empty
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound _
      drift_bound empty_trace_fri_bound current_empty_bound])
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
