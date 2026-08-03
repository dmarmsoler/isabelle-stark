(*  Title:      Stark/Soundness_Staged_Aligned_Partial_Merkle.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Aligned_Partial_Merkle
  imports
    Soundness_Staged_Partial_Merkle
    Soundness_Aligned_Partial_Query_Transcript
    Staged_Security_Experiment_Alpha_Header_Binding
    Staged_Security_Experiment_Composition_Query_Current_Alignment
    Soundness_Conceptual_Query_Empty_Current
begin

text \<open>
  Staged partial-Merkle packaging that uses aligned nonempty-header query
  evidence.  This downstream layer avoids importing verifier-query extraction
  machinery into the upstream deterministic reductions.
\<close>

context soundness
begin

lemma partial_merkle_inconsistency_bad_imp_aligned_partial_candidate_with_partial_merkle:
  assumes "partial_merkle_inconsistency_bad s out"
  shows
    "soundness_bad_event_aligned_partial_candidate_with_partial_merkle s out"
  using assms
  unfolding
    soundness_bad_event_aligned_partial_candidate_with_partial_merkle_def
  by simp

lemma soundness_bad_event_aligned_partial_candidate_imp_with_partial_merkle:
  assumes "soundness_bad_event_aligned_partial_candidate s out"
  shows
    "soundness_bad_event_aligned_partial_candidate_with_partial_merkle s out"
  using assms
  unfolding
    soundness_bad_event_aligned_partial_candidate_with_partial_merkle_def
  by simp

lemma accepted_partition_soundness_bad_event_aligned_partial_candidate_with_partial_merkle_if_header_nonempty:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
  shows
    "soundness_bad_event_aligned_partial_candidate_with_partial_merkle s out"
proof -
  from acc obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  from
    verify_monad_accepted_with_partial_initial_openings_aligned_consistent
      [OF supp[unfolded out_eq] header comp_nonempty]
  obtain query_idxs trace_openings composition_openings where partial:
    "accepted_with_partial_initial_openings_aligned_consistent s
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
      by (rule
          partial_merkle_inconsistency_bad_imp_aligned_partial_candidate_with_partial_merkle)
  next
    case False
    have aligned:
      "accepted_with_partial_initial_openings_aligned s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
      by (rule
          accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
          [OF partial])
    obtain trace_table composition_table where trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
      and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
      using
        accepted_with_partial_initial_openings_aligned_candidates_if_no_partial_merkle_bad
        [OF aligned False]
      by blast
    have bad:
      "soundness_bad_event_aligned_partial_candidate s
        (Some (result, final_state))"
      by (rule accepted_aligned_partial_candidate_partition
          [OF false_statement partial trace_candidate composition_candidate])
    then show ?thesis
      unfolding out_eq
      by (rule soundness_bad_event_aligned_partial_candidate_imp_with_partial_merkle)
	  qed
	qed

lemma accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_if_header_nonempty:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
  shows
    "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
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
        soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_def
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
      "soundness_bad_event_aligned_transcript_partial_candidate s
        (Some (result, final_state))"
      by (rule accepted_aligned_transcript_partial_candidate_partition
          [OF false_statement partial trace_candidate composition_candidate])
    then show ?thesis
      unfolding out_eq
      by (simp add:
          soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_def)
  qed
qed

lemma accepted_partition_soundness_bad_event_aligned_partial_candidate_with_partial_merkle_or_empty_header:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  shows
    "soundness_bad_event_aligned_partial_candidate_with_partial_merkle s out \<or>
     soundness_bad_event_partial_candidate_empty_header s out"
proof (cases "composition_fri_roots = []")
  case False
  then have comp_nonempty: "composition_fri_roots \<noteq> []"
    by simp
  have "soundness_bad_event_aligned_partial_candidate_with_partial_merkle s
      out"
    by (rule
        accepted_partition_soundness_bad_event_aligned_partial_candidate_with_partial_merkle_if_header_nonempty
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
      "soundness_bad_event_aligned_partial_candidate_with_partial_merkle s out"
      unfolding out_eq
      by (rule
          partial_merkle_inconsistency_bad_imp_aligned_partial_candidate_with_partial_merkle)
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

lemma accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_or_empty_header:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  shows
    "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
        s out \<or>
     soundness_bad_event_partial_candidate_empty_header s out"
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

lemma checked_staged_soundness_from_aligned_partial_candidate_and_empty_header_bounds:
  fixes partial_candidate_error empty_header_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and partial_candidate_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_aligned_partial_candidate_with_partial_merkle)
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
    "?E soundness_bad_event_aligned_partial_candidate_with_partial_merkle"
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
        "soundness_bad_event_aligned_partial_candidate_with_partial_merkle ?s
            (Some (result, final_state)) \<or>
         soundness_bad_event_partial_candidate_empty_header ?s
            (Some (result, final_state))"
        by (rule
            accepted_partition_soundness_bad_event_aligned_partial_candidate_with_partial_merkle_or_empty_header
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

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_and_empty_header_bounds:
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
          soundness_bad_event_partial_candidate_empty_header)
        adversary_initial_state \<le> empty_header_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    partial_candidate_error + empty_header_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?partial =
    "?E soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle"
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
        "soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle
            ?s (Some (result, final_state)) \<or>
         soundness_bad_event_partial_candidate_empty_header ?s
            (Some (result, final_state))"
        by (rule
            accepted_partition_soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle_or_empty_header
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

lemma checked_staged_soundness_from_aligned_partial_candidate_components_and_empty_header_bound:
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
        soundness_bad_event_aligned_partial_candidate_with_partial_merkle)
      adversary_initial_state \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
    by (rule
        checked_staged_security_with_data_state_aligned_partial_candidate_with_partial_merkle_union_bound
        [OF merkle_bound comp_bound trace_fri_bound comp_fri_bound
          query_bound])
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      (merkle_error + composition_error + trace_fri_error' +
        composition_fri_error' + query_error) + empty_header_error"
    by (rule
        checked_staged_soundness_from_aligned_partial_candidate_and_empty_header_bounds
        [OF false_statement partial_candidate_bound empty_header_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_empty_header_bound:
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
        soundness_bad_event_aligned_transcript_partial_candidate_with_partial_merkle)
      adversary_initial_state \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_partial_candidate_with_partial_merkle_component_union_bound
        [OF merkle_bound comp_bound trace_fri_bound comp_fri_bound
          query_bound])
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      (merkle_error + composition_error + trace_fri_error' +
        composition_fri_error' + query_error) + empty_header_error"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_and_empty_header_bounds
        [OF false_statement partial_candidate_bound empty_header_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_soundness_from_aligned_partial_candidate_components_and_empty_header_components:
  fixes trace_fri_error' composition_fri_error' query_error P D :: prob
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
      trace_fri_error + nnreal rounds * query_error_bound)"
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
      trace_fri_error + nnreal rounds * query_error_bound"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_prefix_drift_trace_fri_and_query
        [OF false_statement wf controlled prefix_bound drift_bound
          empty_trace_fri_bound empty_query_bound])
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
        trace_fri_error + nnreal rounds * query_error_bound)"
    by (rule
        checked_staged_soundness_from_aligned_partial_candidate_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
  then show ?thesis .
qed

lemma checked_staged_soundness_from_aligned_partial_candidate_components_and_current_empty_query:
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
          query_bad_with_aligned_partial_candidates)
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
        checked_staged_soundness_from_aligned_partial_candidate_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
  then show ?thesis .
qed

lemma checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_empty_header_components:
  fixes trace_fri_error' composition_fri_error' query_error P D :: prob
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
      trace_fri_error + nnreal rounds * query_error_bound)"
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
      trace_fri_error + nnreal rounds * query_error_bound"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_prefix_drift_trace_fri_and_query
        [OF false_statement wf controlled prefix_bound drift_bound
          empty_trace_fri_bound empty_query_bound])
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
        trace_fri_error + nnreal rounds * query_error_bound)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
  then show ?thesis .
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_partial_opening_hit:
  fixes trace_fri_error' composition_fri_error' query_error P D :: prob
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
    and partial_opening_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_opening_hit
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
      trace_fri_error + nnreal rounds * query_error_bound)"
proof -
  have query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> query_error"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_partial_opening_hit
          partial_opening_bound])
      (use wf controlled in simp_all)
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_empty_header_components
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound prefix_bound drift_bound empty_trace_fri_bound
          empty_query_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_current_partial_opening_hit:
  fixes trace_fri_error' composition_fri_error' query_error P D :: prob
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
      trace_fri_error + nnreal rounds * query_error_bound)"
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
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_empty_header_components
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          query_bound prefix_bound drift_bound empty_trace_fri_bound
          empty_query_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds:
  fixes trace_fri_error' composition_fri_error' P D :: prob
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds. C i) +
    (P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
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
        checked_staged_soundness_from_aligned_transcript_components_and_current_partial_opening_hit
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          current_query_bound prefix_bound drift_bound empty_trace_fri_bound
          empty_query_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_partial_opening_hit_from_drift:
  fixes trace_fri_error' composition_fri_error' query_error D :: prob
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
    and partial_opening_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_opening_hit
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
      trace_fri_error + nnreal rounds * query_error_bound)"
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
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_data_state_partial_candidate_composition_bad_bound_from_drift_and_budgets
        [OF false_statement wf controlled drift_bound])
  have query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> query_error"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_partial_opening_hit
          partial_opening_bound])
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
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_drift_trace_fri_and_query
        [OF false_statement wf controlled drift_bound empty_trace_fri_bound
          empty_query_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_current_partial_opening_hit_from_drift:
  fixes trace_fri_error' composition_fri_error' query_error D :: prob
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
      trace_fri_error + nnreal rounds * query_error_bound)"
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
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_data_state_partial_candidate_composition_bad_bound_from_drift_and_budgets
        [OF false_statement wf controlled drift_bound])
  have query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> query_error"
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
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_drift_trace_fri_and_query
        [OF false_statement wf controlled drift_bound empty_trace_fri_bound
          empty_query_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_partial_opening_hit_from_not_prefix:
  fixes trace_fri_error' composition_fri_error' query_error N :: prob
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
    and partial_opening_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_opening_hit
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
      trace_fri_error + nnreal rounds * query_error_bound)"
proof -
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> N"
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
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_components_and_partial_opening_hit_from_drift
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          partial_opening_bound drift_bound empty_trace_fri_bound
          empty_query_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_current_partial_opening_hit_from_not_prefix:
  fixes trace_fri_error' composition_fri_error' query_error N :: prob
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
      trace_fri_error + nnreal rounds * query_error_bound)"
proof -
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> N"
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
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_components_and_current_partial_opening_hit_from_drift
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          current_query_bound drift_bound empty_trace_fri_bound
          empty_query_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds_from_not_prefix:
  fixes trace_fri_error' composition_fri_error' N :: prob
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
      trace_fri_error + nnreal rounds * query_error_bound)"
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
        checked_staged_soundness_from_aligned_transcript_components_and_current_partial_opening_hit_from_not_prefix
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          current_query_bound not_prefix_bound empty_trace_fri_bound
          empty_query_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_prefix_target_path_bounds_from_not_prefix:
  fixes trace_fri_error' composition_fri_error' N :: prob
    and P Q :: "nat \<Rightarrow> prob"
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
    and prefix_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event (checked_staged_query_prefix_receive_with_state A i)
          (checked_staged_query_prefix_dynamic_index_hit
            staged_query_prefix_prefix_authenticated_opening_target)
          adversary_initial_state \<le> P i"
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
    (\<Sum>i<rounds. P i + Q i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
proof -
  have round_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le> P i + Q i"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have prefix_hit_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
        adversary_initial_state \<le> P i"
      by (rule
          checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_dynamic_target
          [OF wf controlled i_bound prefix_bound[OF i_bound]])
    show
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le> P i + Q i"
      by (rule
          checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_path
          [OF wf controlled i_bound prefix_hit_bound path_bound[OF i_bound]])
  qed
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds_from_not_prefix
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound not_prefix_bound empty_trace_fri_bound
          empty_query_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_not_prefix:
  fixes trace_fri_error' composition_fri_error' N :: prob
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
      trace_fri_error + nnreal rounds * query_error_bound)"
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
        checked_staged_soundness_from_aligned_transcript_components_and_current_query_prefix_rounds_from_not_prefix
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound not_prefix_bound empty_trace_fri_bound
          empty_query_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_not_prefix_components:
  fixes trace_fri_error' composition_fri_error' C U M R :: prob
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
        adversary_initial_state \<le> M"
    and not_prefix_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
        adversary_initial_state \<le> R"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
      trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (C + U + M + R) +
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
      (C + U + M + R) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
proof -
  have not_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> C + U + M + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          not_prefix_path_bound])
  show ?thesis
    by (rule
    checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_not_prefix
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          trace_frac path_bound not_prefix_bound empty_trace_fri_bound
          empty_query_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_not_prefix_noncollision_components:
  fixes trace_fri_error' composition_fri_error' U M R :: prob
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
        adversary_initial_state \<le> M"
    and not_prefix_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
        adversary_initial_state \<le> R"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
      trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
        (staged_alpha_search_queries budgets 0) + U + M + R) +
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
        (staged_alpha_search_queries budgets 0) + U + M + R) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
proof (rule
    checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_not_prefix_components
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound
      trace_frac path_bound _ uncovered_bound no_prefix_bound
      not_prefix_path_bound empty_trace_fri_bound empty_query_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision_bound
        [OF wf controlled])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_cross_no_prefix_path_components:
  fixes trace_fri_error' composition_fri_error' X M R :: prob
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
    and no_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        adversary_initial_state \<le> M"
    and not_prefix_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
        adversary_initial_state \<le> R"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
      trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
        (staged_alpha_search_queries budgets 0) + X + M + R) +
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
        (staged_alpha_search_queries budgets 0) + X + M + R) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
proof (rule
    checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_not_prefix_noncollision_components
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound
      trace_frac path_bound _ no_prefix_bound not_prefix_path_bound
      empty_trace_fri_bound empty_query_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      adversary_initial_state \<le> X"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_witnessed_cross_or_merkle_bad
          cross_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_cross_no_prefix_transcript_split_components:
  fixes trace_fri_error' composition_fri_error' X M P R :: prob
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
    and no_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        adversary_initial_state \<le> M"
    and transcript_pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
        (staged_alpha_search_queries budgets 0) + X + M + (P + R)) +
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
        (staged_alpha_search_queries budgets 0) + X + M + (P + R)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
proof (rule
    checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_cross_no_prefix_path_components
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound
      trace_frac path_bound cross_bound no_prefix_bound _ empty_trace_fri_bound
      empty_query_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le> P + R"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_le_witness_transcript_hit])
      (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new
        [OF transcript_pre_bound transcript_new_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_cross_no_prefix_data_pre_and_witness_new_components:
  fixes trace_fri_error' composition_fri_error' X M P R :: prob
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
    and no_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        adversary_initial_state \<le> M"
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
        (staged_alpha_search_queries budgets 0) + X + M + (P + R)) +
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
        (staged_alpha_search_queries budgets 0) + X + M + (P + R)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
proof (rule
    checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_cross_no_prefix_transcript_split_components
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound
      trace_frac path_bound cross_bound no_prefix_bound _ transcript_new_bound
      empty_trace_fri_bound empty_query_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      adversary_initial_state \<le> P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_bound_from_data_state_pre_hit
        [OF data_pre_bound])
qed

lemma checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_cross_data_pre_and_witness_new_components:
  fixes trace_fri_error' composition_fri_error' X P R :: prob
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
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
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
      trace_fri_error + nnreal rounds * query_error_bound)"
proof (rule
    checked_staged_soundness_from_aligned_transcript_components_and_trace_index_path_bounds_from_cross_no_prefix_data_pre_and_witness_new_components
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound
      trace_frac path_bound cross_bound _ data_pre_bound transcript_new_bound
      empty_trace_fri_bound empty_query_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le> P + R"
  proof (rule order_trans
      [OF
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_le_witness_transcript_hit])
    have pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
        adversary_initial_state \<le> P"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_bound_from_data_state_pre_hit
          [OF data_pre_bound])
    show
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
        adversary_initial_state \<le> P + R"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new
          [OF pre_bound transcript_new_bound])
  qed
qed

end

end
