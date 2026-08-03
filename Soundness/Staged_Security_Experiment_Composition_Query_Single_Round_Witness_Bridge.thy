(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Single_Round_Witness_Bridge.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Single_Round_Witness_Bridge
  imports
    Staged_Security_Experiment_Composition_Query_Single_Round
    Staged_Security_Experiment_Composition_Query_Current_Alignment
    Staged_Security_Experiment_Composition_Query_Current_Path
    Staged_Security_Experiment_Alpha_Header_Binding
begin

text \<open>
  Bridge from the broad actual-alpha diagnostic witness event to a fixed
  query-prefix candidate-pair witness event.

  The bridge is deterministic: it extracts the concrete prefix branch and
  candidate pair already present in the diagnostic event.  It does not bound
  the diagnostic event probabilistically; later proof layers must still avoid
  treating the broad existential diagnostic event as a final public-path event.
\<close>

context soundness
begin

definition checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
where
  "checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
      trace_openings composition_openings trace_table composition_table i A out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (\<exists>prefix prefix_state raw raw_state.
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
            set_dist
              (execute
                (checked_staged_security_experiment_with_query_prefix_data_state
                  A i)
                adversary_initial_state) \<and>
          checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
            trace_openings composition_openings trace_table composition_table i
              (Some (((((prefix, prefix_state), raw), raw_state),
                ((data, attacker_state), result)), final_state))))"

definition checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
where
  "checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
      i A out \<longleftrightarrow>
    (\<exists>trace_openings composition_openings trace_table composition_table.
      checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
        trace_openings composition_openings trace_table composition_table i A
        out)"

definition checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
where
  "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
      i out \<longleftrightarrow>
    (\<exists>trace_openings composition_openings trace_table composition_table.
      checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
        trace_openings composition_openings trace_table composition_table i
        out)"

definition staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
where
  "staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
      trace_openings composition_openings trace_table composition_table i A out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((data, attacker_state), result), final_state) \<Rightarrow>
        (\<exists>prefix prefix_state raw raw_state.
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
            set_dist
              (execute
                (checked_staged_security_experiment_with_query_prefix_data_state
                  A i)
                adversary_initial_state) \<and>
          checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
            trace_openings composition_openings trace_table composition_table i
            (Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state))))"

definition staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
where
  "staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
      i A out \<longleftrightarrow>
    (\<exists>trace_openings composition_openings trace_table composition_table.
      staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
        trace_openings composition_openings trace_table composition_table i A
        out)"

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_projection:
  "checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
      trace_openings composition_openings trace_table composition_table i A out
    \<longleftrightarrow>
   (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
          trace_openings composition_openings trace_table composition_table i A
          (Some (((data, attacker_state), result), final_state)))"
  unfolding
    checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_def
    staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_def
  by (auto split: option.splits prod.splits)

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_wp_projection:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
      trace_openings composition_openings trace_table composition_table i A)
    adversary_initial_state =
   wp_event
    (checked_staged_security_experiment_with_data_state A)
    (staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
      trace_openings composition_openings trace_table composition_table i A)
    adversary_initial_state"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
        trace_openings composition_openings trace_table composition_table i A)
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
        \<bind> (\<lambda>x. return (?project x)))
      (staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
        trace_openings composition_openings trace_table composition_table i A)
      adversary_initial_state"
    using
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
      [of A]
    by simp
  also have "... =
    wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
        trace_openings composition_openings trace_table composition_table i A)
      adversary_initial_state"
  proof -
    have pred_eq:
      "(\<lambda>out. case out of
        None \<Rightarrow>
          staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
            trace_openings composition_openings trace_table composition_table i A
            None
      | Some (x, t) \<Rightarrow>
          staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
            trace_openings composition_openings trace_table composition_table i A
            (Some (?project x, t))) =
      checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
        trace_openings composition_openings trace_table composition_table i A"
      by (rule ext)
        (simp add:
          checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_projection
          staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_def
          split: option.splits prod.splits)
    show ?thesis
      by (subst wp_event_bind_return_map) (simp add: pred_eq)
  qed
  finally show ?thesis
    by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_bound_from_data_state:
  assumes bound:
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
        trace_openings composition_openings trace_table composition_table i A)
      adversary_initial_state \<le> B"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
        trace_openings composition_openings trace_table composition_table i A)
      adversary_initial_state \<le> B"
  using bound
  unfolding
    checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_wp_projection
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_projection:
  "checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
      i A out
    \<longleftrightarrow>
   (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
          i A (Some (((data, attacker_state), result), final_state)))"
  unfolding
    checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_def
    staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_def
  by (auto simp:
      checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_projection
      split: option.splits prod.splits)

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_wp_projection:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
      i A)
    adversary_initial_state =
   wp_event
    (checked_staged_security_experiment_with_data_state A)
    (staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
      i A)
    adversary_initial_state"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
        i A)
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
        \<bind> (\<lambda>x. return (?project x)))
      (staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
        i A)
      adversary_initial_state"
    using
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
      [of A]
    by simp
  also have "... =
    wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
        i A)
      adversary_initial_state"
  proof -
    have pred_eq:
      "(\<lambda>out. case out of
        None \<Rightarrow>
          staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
            i A None
      | Some (x, t) \<Rightarrow>
          staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
            i A (Some (?project x, t))) =
      checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
        i A"
      by (rule ext)
        (simp add:
          checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_projection
          staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_def
          staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_def
          split: option.splits prod.splits)
    show ?thesis
      by (subst wp_event_bind_return_map) (simp add: pred_eq)
  qed
  finally show ?thesis
    by simp
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at_le_same_run_data_state_exists:
  assumes i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
        i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
        i A)
      adversary_initial_state"
proof -
  let ?M =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Gap =
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
      i"
  let ?DataGap =
    "staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
      i A"
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow> ?DataGap None
    | Some (packed, t) \<Rightarrow> ?DataGap (Some (snd packed, t))"
  have projection:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      ?DataGap adversary_initial_state =
     wp_event ?M ?projected adversary_initial_state"
    by (rule checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound])
  have event_le:
    "wp_event ?M ?Gap adversary_initial_state \<le>
     wp_event ?M ?projected adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?M adversary_initial_state)"
      and gap: "?Gap out"
    show "?projected out"
    proof (cases out)
      case None
      then show ?thesis
        using gap
        unfolding
          checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at_def
          checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_def
          checked_staged_security_with_query_prefix_dynamic_index_hit_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
        "out =
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      from gap obtain trace_openings composition_openings trace_table
          composition_table where fixed_gap:
        "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
          trace_openings composition_openings trace_table composition_table i
          out"
        unfolding
          checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at_def
        by blast
      have qsupport:
        "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
          set_dist (execute ?M adversary_initial_state)"
        using support out_eq by simp
      have fixed_gap_out:
        "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
          trace_openings composition_openings trace_table composition_table i
          (Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state))"
        using fixed_gap out_eq by simp
      have data_gap:
        "staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
          trace_openings composition_openings trace_table composition_table i A
          (Some (((data, attacker_state), result), final_state))"
        unfolding
          staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_def
        using qsupport fixed_gap_out by auto
      have projected_gap:
        "?DataGap (Some (((data, attacker_state), result), final_state))"
        unfolding
          staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_def
        using data_gap by blast
      show ?thesis
        unfolding out_eq
        using projected_gap by simp
    qed
  qed
  show ?thesis
    unfolding projection
    by (rule event_le)
qed

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_atE:
  assumes gap:
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
      trace_openings composition_openings trace_table composition_table i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains prefix prefix_state raw raw_state where
    "Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
  using gap
  unfolding
    checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_def
  by (auto split: prod.splits)

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_atI:
  assumes support:
    "Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    and gap:
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
      trace_openings composition_openings trace_table composition_table i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  unfolding
    checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_def
  using support gap by auto

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_atI:
  assumes gap:
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
      trace_openings composition_openings trace_table composition_table i A out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
      i A out"
  unfolding
    checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_def
  using gap by blast

lemma checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_atI:
  assumes gap:
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
      i out"
  unfolding
    checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at_def
  using gap by blast

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_imp_witness_transcript_hit:
  assumes gap:
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
      i A out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using gap
    unfolding
      checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_def
      checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix alpha_prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed, auto split: prod.splits)
  from gap obtain trace_openings composition_openings trace_table
      composition_table prefix prefix_state raw raw_state where support:
      "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state
              A i)
            adversary_initial_state)"
    and fixed_gap:
      "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_def
    by (auto elim!:
        checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_atE)
  have witness_side:
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    by (rule
        checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_imp_witness_side
        [OF fixed_gap])
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from witness_side have witness:
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    unfolding
      checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_def
    by simp
  from query_header_supported_partial_opening_witnessesE[OF witness]
  obtain witness_result witness_state rest where outcome:
      "Some (witness_result, witness_state) \<in>
        set_dist (execute verify_monad ?s)"
    by blast
  have tr_eq: "PTranscript ?s = staged_proof_transcript data"
    by simp
  have transcript_hit:
    "hash_map_output_values ?s \<inter> set (staged_proof_transcript data)
        \<noteq> {} \<or>
     hash_map_new_output_hit (set (staged_proof_transcript data))
        ?s witness_state"
    by (rule verify_monad_trace_root_target_preexisting_or_new
        [OF outcome tr_eq])
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_def
      Let_def
    using outcome transcript_hit
    by (auto split: prod.splits)
qed

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_le_witness_transcript_hit:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
      i A)
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
    adversary_initial_state"
  by (rule wp_event_mono)
    (rule
      checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_imp_witness_transcript_hit)

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_bound_from_pre_and_new:
  assumes pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
        i A)
      adversary_initial_state \<le> P + Q"
  by (rule order_trans
      [OF
        checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_le_witness_transcript_hit
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new
          [OF pre_bound new_bound]])

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_bound_from_data_pre_and_new:
  assumes data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
        i A)
      adversary_initial_state \<le> P + Q"
proof -
  have pre_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      adversary_initial_state \<le> P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_bound_from_data_state_pre_hit
        [OF data_pre_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_bound_from_pre_and_new
        [OF pre_bound new_bound])
qed

lemma staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_bound_from_data_pre_and_new:
  assumes data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at
        i A)
      adversary_initial_state \<le> P + Q"
  using
    checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_bound_from_data_pre_and_new
      [OF data_pre_bound new_bound, of i]
  unfolding
    checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_wp_projection
  by simp

lemma checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at_bound_from_data_pre_and_new:
  assumes i_bound: "i < rounds"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
        i)
      adversary_initial_state \<le> P + Q"
  by (rule order_trans[
        OF checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at_le_same_run_data_state_exists[
          OF i_bound]
        staged_security_with_data_state_query_prefix_fixed_candidate_pair_witness_gap_same_run_exists_at_bound_from_data_pre_and_new[
          OF data_pre_bound new_bound]])

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_with_witness_imp_single_round_header_target_or_same_run_fixed_witness_gap:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
      A trace_table composition_table i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
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
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and same_run_support:
      "\<And>prefix prefix_state raw raw_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<Longrightarrow>
        Some (((prefix, prefix_state), raw), raw_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_receive_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        checked_staged_query_prefix_dynamic_index_hit
          (staged_query_prefix_candidate_pair_query_target_from_prefix
            trace_table composition_table)
          (Some (((prefix, prefix_state), raw), raw_state)) \<Longrightarrow>
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state)"
  shows
    "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
      trace_openings composition_openings trace_table composition_table i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  from
    checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE
      [OF hit]
  obtain prefix prefix_state raw raw_state where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE
        [OF hit])
  have support:
    "Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state
            A i)
          adversary_initial_state)"
    by (rule same_run_support[OF builder prefix_receive target_hit])
  show ?thesis
  proof (cases
      "(trace_table, composition_table) \<in>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i")
    case True
    have single_round_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_single_round_header_supported_query_target i)
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_pair_hit_imp_single_round_header_target_hit
          [OF True target_hit])
    have
      "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    proof -
      have inner:
        "\<exists>prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_single_round_header_supported_query_target i)
            (Some (((prefix, prefix_state), raw), raw_state))"
        by (intro exI[of _ prefix] exI[of _ prefix_state]
            exI[of _ raw] exI[of _ raw_state])
          (use builder prefix_receive single_round_hit in simp)
      show ?thesis
        unfolding
          checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at_def
        using inner by simp
    qed
    then show ?thesis by simp
  next
    case False
    have success:
      "index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (sqp_alphas prefix)"
      using target_hit
      unfolding
        checked_staged_query_prefix_dynamic_index_hit_def
        staged_query_prefix_candidate_pair_query_target_from_prefix_def
      by simp
    have fixed_gap:
      "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
    proof -
      have dyn:
        "checked_staged_security_with_query_prefix_dynamic_index_hit
          (staged_query_prefix_candidate_pair_query_target_from_prefix
            trace_table composition_table)
          (Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state))"
        unfolding
          checked_staged_security_with_query_prefix_dynamic_index_hit_def
          checked_staged_query_prefix_dynamic_index_hit_def
          staged_query_prefix_candidate_pair_query_target_from_prefix_def
        using success by simp
      have side:
        "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
          trace_openings composition_openings trace_table composition_table i
          (Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state))"
        unfolding
          checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_def
          checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side_def
        using witness trace_candidate comp_candidate False by simp
      show ?thesis
        unfolding
          checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_def
        using dyn side by simp
    qed
    have
      "checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
        trace_openings composition_openings trace_table composition_table i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_atI
          [OF support fixed_gap])
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_success_with_witness_imp_single_round_header_target_or_same_run_fixed_witness_gap:
  assumes i_bound: "i < rounds"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and success:
      "\<And>prefix prefix_state raw raw_state.
        Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        sqp_alphas prefix = staged_alphas data \<Longrightarrow>
        index (to_nat raw) \<in>
          query_sampling_success_space trace_table composition_table
            (staged_alphas data)"
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
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
  shows
    "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
      trace_openings composition_openings trace_table composition_table i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_candidate_pair_success_query_prefix_hitE
    [OF i_bound support success])
  fix prefix prefix_state raw raw_state
  assume qsupport:
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    and qhit:
    "checked_staged_security_with_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_imp_data_state_support
        [OF i_bound qsupport])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    by blast
  have prefix_receive:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    using qsupport
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have raw_pair_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
    using qhit
    unfolding checked_staged_security_with_query_prefix_dynamic_index_hit_def
    by simp
  show ?thesis
  proof (cases
      "(trace_table, composition_table) \<in>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i")
    case True
    have single_round_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_single_round_header_supported_query_target i)
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_pair_hit_imp_single_round_header_target_hit
          [OF True raw_pair_hit])
    have
      "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    proof -
      have inner:
        "\<exists>prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_single_round_header_supported_query_target i)
            (Some (((prefix, prefix_state), raw), raw_state))"
        by (intro exI[of _ prefix] exI[of _ prefix_state]
            exI[of _ raw] exI[of _ raw_state])
          (use builder prefix_receive single_round_hit in simp)
      show ?thesis
        unfolding
          checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at_def
        using inner by simp
    qed
    then show ?thesis by simp
  next
    case False
    have side:
      "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_def
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side_def
      using witness trace_candidate comp_candidate False by simp
    have fixed_gap:
      "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_def
      using qhit side by simp
    have
      "checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_at
        trace_openings composition_openings trace_table composition_table i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_query_prefix_fixed_candidate_pair_witness_gap_same_run_atI
          [OF qsupport fixed_gap])
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_imp_single_round_header_target_or_witness_gap:
  assumes hit:
    "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table
        (sqp_alphas prefix)"
  shows
    "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  from hit obtain comp_nonempty witness opening_target
    where comp_nonempty:
      "staged_composition_fri_roots data \<noteq> []"
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
    and opening_target:
      "index (to_nat raw) \<in>
        staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i prefix prefix_state"
    by (rule
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hitE)
  have opening_subset:
    "staged_query_prefix_candidate_opening_query_target_from_prefix
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      i prefix prefix_state \<subseteq>
     staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
      composition_table prefix prefix_state"
    by (rule
        staged_query_prefix_candidate_opening_query_target_from_prefix_subset_candidate_pair_from_prefix
        [OF trace_candidate comp_candidate trace_low comp_low not_all])
  have pair_target_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
    using opening_target opening_subset
    unfolding checked_staged_query_prefix_dynamic_index_hit_def by auto
  show ?thesis
  proof (cases
      "(trace_table, composition_table) \<in>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i")
    case True
    have target:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_single_round_header_supported_query_target i)
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_pair_hit_imp_single_round_header_target_hit
          [OF True pair_target_hit])
    have
      "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
        i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at_def
      using target by simp
    then show ?thesis by simp
  next
    case False
    have gap:
      "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at_def
      using hit trace_candidate comp_candidate False by simp
    have side:
      "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_def
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side_def
      using witness trace_candidate comp_candidate False by simp
    have
      "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_def
      using gap side by simp
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_bound_from_target_and_fixed_witness_gap:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>prefix prefix_state raw raw_state data attacker_state result
          final_state.
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
    and target_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
          i)
        adversary_initial_state \<le> T"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      T +
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
       (1::prob) / nnreal (card query_sample_space))"
proof -
  let ?m =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?target =
    "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
      i"
  let ?gap =
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
      trace_openings composition_openings trace_table composition_table i"
  have event_le:
    "wp_event ?m
      (checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
     wp_event ?m (\<lambda>out. ?target out \<or> ?gap out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in> set_dist (execute ?m adversary_initial_state)"
      and hit:
        "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
          trace_openings composition_openings i out"
    show "?target out \<or> ?gap out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state
          result final_state where out_eq:
        "out =
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      have not_all':
        "\<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
        by (rule not_all)
          (use support out_eq in simp)
      show ?thesis
        unfolding out_eq
        by (rule
            checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_imp_single_round_header_target_or_witness_gap
            [OF _ trace_candidate comp_candidate trace_low comp_low not_all'])
          (use hit out_eq in simp)
    qed
  qed
  have union_le:
    "wp_event ?m (\<lambda>out. ?target out \<or> ?gap out)
      adversary_initial_state \<le>
     wp_event ?m ?target adversary_initial_state +
     wp_event ?m ?gap adversary_initial_state"
    by (rule wp_event_union_bound)
  have gap_bound:
    "wp_event ?m ?gap adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
    by (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_bound_from_budgets
        [OF wf controlled i_bound])
  have sum_bound:
    "wp_event ?m ?target adversary_initial_state +
      wp_event ?m ?gap adversary_initial_state \<le>
     T +
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
       (1::prob) / nnreal (card query_sample_space))"
    by (rule add_mono[OF target_bound gap_bound])
  show ?thesis
    by (rule order_trans[OF event_le order_trans[OF union_le sum_bound]])
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_atI:
  assumes success:
      "index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (sqp_alphas prefix)"
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
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and notin:
      "(trace_table, composition_table) \<notin>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i"
  shows
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  have dyn:
    "checked_staged_security_with_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    using success
    unfolding
      checked_staged_security_with_query_prefix_dynamic_index_hit_def
      checked_staged_query_prefix_dynamic_index_hit_def
      staged_query_prefix_candidate_pair_query_target_from_prefix_def
    by simp
  have side:
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    unfolding
      checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_def
      checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side_def
    using witness trace_candidate comp_candidate notin by simp
  show ?thesis
    unfolding
      checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_def
    using dyn side by simp
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table))
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_imp_dynamic_hit)
  have target_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_candidate_pair_target_from_prefix_hit_bound_from_budgets
        [OF wf controlled i_bound trace_low comp_low not_all])
  show ?thesis
    by (rule order_trans[OF event_le target_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witnessE_candidate_pair_witness:
  assumes gap:
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains trace_openings composition_openings trace_table composition_table
      prefix prefix_state raw raw_state where
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  from gap show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witnessE)
    fix trace_openings composition_openings trace_table composition_table
        prefix prefix_state raw raw_state
    assume builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    assume prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    assume witness:
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
    assume trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    assume comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    assume target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state))"
    assume notin:
      "(trace_table, composition_table) \<notin>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i"
    have dyn:
      "checked_staged_security_with_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding checked_staged_security_with_query_prefix_dynamic_index_hit_def
      using target_hit by simp
    have side:
      "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_def
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side_def
      using witness trace_candidate comp_candidate notin by simp
    have fixed_gap:
      "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_def
      using dyn side by simp
    show ?thesis
      by (rule that[OF builder prefix_receive fixed_gap])
  qed
qed

lemma checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_imp_single_round_header_target_or_fixed_witness_gap:
  assumes pair_hit:
    "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
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
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
  shows
    "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?out =
    "Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state)"
  have raw_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
    using pair_hit
    unfolding
      checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_def
      checked_staged_security_with_query_prefix_dynamic_index_hit_def
    by simp
  show ?thesis
  proof (cases
      "(trace_table, composition_table) \<in>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i")
    case True
    have target:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_single_round_header_supported_query_target i)
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_pair_hit_imp_single_round_header_target_hit
          [OF True raw_hit])
    have
      "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
        i ?out"
      unfolding
        checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at_def
      using target by simp
    then show ?thesis by simp
  next
    case False
    have success:
      "index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (sqp_alphas prefix)"
      using raw_hit
      unfolding
        checked_staged_query_prefix_dynamic_index_hit_def
        staged_query_prefix_candidate_pair_query_target_from_prefix_def
      by simp
    have
      "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
        trace_openings composition_openings trace_table composition_table i
        ?out"
      by (rule
          checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_atI
          [OF success witness trace_candidate comp_candidate False])
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_single_round_header_target_or_fixed_witness_gap_or_structured_path_on_support:
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
      "checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
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
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table
        (sqp_alphas prefix)"
  shows
    "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?out =
    "Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state)"
  have split:
    "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
      trace_table composition_table ?out \<or>
     checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
      i ?out \<or>
     checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
      i ?out"
    by (rule
        checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_candidate_pair_or_structured_path_on_support
        [OF wf controlled i_bound support hit trace_candidate
          comp_candidate trace_low comp_low not_all])
  then show ?thesis
  proof
    assume pair:
      "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
        trace_table composition_table ?out"
    from
      checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_imp_single_round_header_target_or_fixed_witness_gap
        [OF pair witness trace_candidate comp_candidate]
    show ?thesis
      by blast
  next
    assume
      "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i ?out \<or>
       checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i ?out"
    then show ?thesis by blast
  qed
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_bound_from_single_round_target_fixed_witness_gap_and_structured_paths:
  fixes H G T C :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and witness:
      "\<And>prefix prefix_state raw raw_state data attacker_state result
          final_state.
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        (trace_openings, composition_openings) \<in>
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
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>prefix prefix_state raw raw_state data attacker_state result
          final_state.
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
    and target_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
          i)
        adversary_initial_state \<le> H"
    and fixed_gap_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
          trace_openings composition_openings trace_table composition_table i)
        adversary_initial_state \<le> G"
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le> H + G + T + C"
proof -
  let ?M =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Target =
    "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
      i"
  let ?Gap =
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i"
  let ?Trace =
    "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
      i"
  let ?Comp =
    "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
      i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
     wp_event ?M
      (\<lambda>out. ?Target out \<or> ?Gap out \<or> ?Trace out \<or> ?Comp out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit:
      "checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i out"
    show "?Target out \<or> ?Gap out \<or> ?Trace out \<or> ?Comp out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_query_prefix_authenticated_opening_hit_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
        "out =
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      have support_some:
        "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
          set_dist (execute ?M adversary_initial_state)"
        using support out_eq by simp
      show ?thesis
        unfolding out_eq
        by (rule
            checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_single_round_header_target_or_fixed_witness_gap_or_structured_path_on_support
            [OF wf controlled i_bound support_some _ witness[OF support_some]
              trace_candidate comp_candidate trace_low comp_low
              not_all[OF support_some]])
          (use hit out_eq in simp)
    qed
  qed
  have union_bound:
    "wp_event ?M
      (\<lambda>out. ?Target out \<or> ?Gap out \<or> ?Trace out \<or> ?Comp out)
      adversary_initial_state \<le>
     wp_event ?M ?Target adversary_initial_state +
     wp_event ?M ?Gap adversary_initial_state +
     wp_event ?M ?Trace adversary_initial_state +
     wp_event ?M ?Comp adversary_initial_state"
    by (rule wp_event_union_bound4)
  have component_bound:
    "wp_event ?M ?Target adversary_initial_state +
     wp_event ?M ?Gap adversary_initial_state +
     wp_event ?M ?Trace adversary_initial_state +
     wp_event ?M ?Comp adversary_initial_state \<le>
      H + G + T + C"
    by (intro add_mono target_bound fixed_gap_bound trace_path_bound
        composition_path_bound)
  show ?thesis
    by (rule order_trans[OF event_le order_trans[OF union_bound
          component_bound]])
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_bound_from_single_round_target_budgets_and_structured_paths:
  fixes H T C :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and witness:
      "\<And>prefix prefix_state raw raw_state data attacker_state result
          final_state.
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        (trace_openings, composition_openings) \<in>
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
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
    and target_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
          i)
        adversary_initial_state \<le> H"
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      H +
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      T + C"
proof -
  have fixed_gap_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_bound_from_budgets
        [OF wf controlled i_bound trace_low comp_low])
      (use not_all in blast)
  have not_all_on_data_support:
    "\<And>prefix prefix_state raw raw_state data attacker_state result
        final_state.
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state
              A i)
            adversary_initial_state) \<Longrightarrow>
      \<not> all_queries_consistent trace_table composition_table
        (sqp_alphas prefix)"
  proof -
    fix prefix prefix_state raw raw_state data attacker_state result
        final_state
    assume support:
      "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state
              A i)
            adversary_initial_state)"
    have receive_support:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
      using support
      unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    have prefix_support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
      by (rule checked_staged_query_prefix_receive_with_state_prefix_support
          [OF receive_support])
    show "\<not> all_queries_consistent trace_table composition_table
        (sqp_alphas prefix)"
      by (rule not_all[OF prefix_support])
  qed
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_authenticated_opening_hit_bound_from_single_round_target_fixed_witness_gap_and_structured_paths
        [OF wf controlled i_bound witness trace_candidate comp_candidate
          trace_low comp_low not_all_on_data_support target_bound fixed_gap_bound
          trace_path_bound composition_path_bound])
qed

end

end
