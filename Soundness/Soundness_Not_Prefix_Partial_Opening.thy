(*  Title:      Stark/Soundness_Not_Prefix_Partial_Opening.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Not_Prefix_Partial_Opening
  imports Soundness_Relevant_Drift_Transcript_Public
begin

text \<open>
  Same-run partial-opening packaging for the remaining not-prefix residual.

  The residual is not a probability-small sparse-cover event by itself.
  Instead, it records the precise verifier evidence still carried by the
  current route: an accepting verifier run, authenticated partial trace
  openings from that same run, and a trace-domain index left unopened by those
  sampled openings.  This layer gives that evidence a non-diagnostic name and
  keeps the broad witnessed cross/Merkle classifier out of the checked wrapper.
\<close>

context soundness
begin

definition partial_trace_openings_leave_domain_gap
  :: "'f authenticated_opening list list \<Rightarrow> bool"
where
  "partial_trace_openings_leave_domain_gap trace_openings \<longleftrightarrow>
    (\<exists>j < scale * clength.
      \<forall>i opn. i < rounds \<longrightarrow>
        opn \<in> set (trace_openings ! i) \<longrightarrow>
        opening_index opn \<noteq> j)"

definition checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             prefix_state = snd (fst packed);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>fr f_fri_roots f_final trace_table witness_final_state
              trace_openings.
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table witness_final_state
                trace_openings \<and>
              trace_table \<notin>
                alpha_prefix_trace_table_candidates prefix_state fr \<and>
              prefix_state \<le> witness_final_state \<and>
              partial_trace_openings_leave_domain_gap trace_openings))"

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap_iff_uncovered_index:
  "checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
      out \<longleftrightarrow>
   checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      out"
  unfolding
    checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap_def
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_def
    partial_trace_openings_leave_domain_gap_def
  by (auto split: option.splits prod.splits)

definition checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             prefix_state = snd (fst packed);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>fr f_fri_roots f_final trace_table prefix_trace_table
              witness_final_state trace_openings result query_idxs i.
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table witness_final_state
                trace_openings \<and>
              trace_table \<notin>
                alpha_prefix_trace_table_candidates prefix_state fr \<and>
              prefix_trace_table \<in>
                alpha_prefix_trace_table_candidates prefix_state fr \<and>
              prefix_state \<le> witness_final_state \<and>
              accepted_with_partial_trace_openings s
                (Some (result, witness_final_state)) fr query_idxs
                trace_openings \<and>
              i < rounds \<and>
              query_idxs ! i \<in>
                trace_table_agreement_indices trace_table
                  prefix_trace_table))"

definition checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_sampled_agreement
  :: "'f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_sampled_agreement
      A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             prefix_state = snd (fst packed);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>fr f_fri_roots f_final trace_table prefix_trace_table
              witness_final_state trace_openings result query_idxs as i
              prefix prefix_state' raw raw_state.
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table witness_final_state
                trace_openings \<and>
              trace_table \<notin>
                alpha_prefix_trace_table_candidates prefix_state fr \<and>
              prefix_trace_table \<in>
                alpha_prefix_trace_table_candidates prefix_state fr \<and>
              trace_table_low_degree trace_table \<and>
              trace_table_low_degree prefix_trace_table \<and>
              trace_table \<noteq> prefix_trace_table \<and>
              accepted_with_partial_trace_openings s
                (Some (result, witness_final_state)) fr query_idxs
                trace_openings \<and>
              accepted_transcript_shape s (Some (result, witness_final_state))
                as query_idxs \<and>
              i < rounds \<and>
              Some (data, attacker_state) \<in>
                set_dist
                  (execute (checked_staged_transcript_program A)
                    adversary_initial_state) \<and>
              Some (((prefix, prefix_state'), raw), raw_state) \<in>
                set_dist
                  (execute (checked_staged_query_prefix_receive_with_state A i)
                    adversary_initial_state) \<and>
              index (to_nat raw) \<in>
                trace_table_agreement_indices trace_table
                  prefix_trace_table))"

definition checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_actual_sampled_agreement
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_actual_sampled_agreement
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (let s =
          verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)
         in \<exists>fr f_fri_roots f_final trace_table prefix_trace_table
              witness_final_state trace_openings as query_idxs i.
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table witness_final_state
                trace_openings \<and>
              trace_table \<notin>
                alpha_prefix_trace_table_candidates prefix_state fr \<and>
              prefix_trace_table \<in>
                alpha_prefix_trace_table_candidates prefix_state fr \<and>
              trace_table_low_degree trace_table \<and>
              trace_table_low_degree prefix_trace_table \<and>
              trace_table \<noteq> prefix_trace_table \<and>
              accepted_transcript_shape s (Some (result, final_state))
                as query_idxs \<and>
              i < rounds \<and>
              query_idxs ! i \<in>
                trace_table_agreement_indices trace_table
                  prefix_trace_table))"

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_same_run_partial_opening_gap:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
    adversary_initial_state"
  by (rule wp_event_mono)
    (simp add:
      checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap_iff_uncovered_index)

lemma checked_staged_security_with_actual_alpha_prefix_same_run_gap_imp_witness_transcript_hit:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using assms
    unfolding
      checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from assms obtain fr f_fri_roots f_final trace_table
      witness_final_state trace_openings where witness:
      "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
        f_fri_roots f_final trace_table witness_final_state trace_openings"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap_def
      Let_def
    by (auto split: prod.splits)
  from witness obtain result' query_idxs as dg composition_fri_roots final
      rest where outcome:
      "Some (result', witness_final_state) \<in>
        set_dist (execute verify_monad ?s)"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  have tr_eq: "PTranscript ?s = staged_proof_transcript data"
    by simp
  have transcript_hit:
    "hash_map_output_values ?s \<inter> set (staged_proof_transcript data)
        \<noteq> {} \<or>
     hash_map_new_output_hit (set (staged_proof_transcript data))
        ?s witness_final_state"
    by (rule verify_monad_trace_root_target_preexisting_or_new
        [OF outcome tr_eq])
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_def
      Let_def
    using outcome transcript_hit
    by (auto split: prod.splits)
qed

lemma checked_staged_security_with_actual_alpha_prefix_same_run_gap_le_witness_transcript_hit:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
    adversary_initial_state"
  by (rule wp_event_mono)
    (rule
      checked_staged_security_with_actual_alpha_prefix_same_run_gap_imp_witness_transcript_hit)

lemma checked_staged_security_with_actual_alpha_prefix_same_run_gap_bound_from_pre_and_new:
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
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
      adversary_initial_state \<le> P + Q"
  by (rule order_trans
      [OF
        checked_staged_security_with_actual_alpha_prefix_same_run_gap_le_witness_transcript_hit
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new
          [OF pre_bound new_bound]])

lemma checked_staged_security_with_actual_alpha_prefix_same_run_gap_bound_from_data_pre_and_new:
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
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
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
        checked_staged_security_with_actual_alpha_prefix_same_run_gap_bound_from_pre_and_new
        [OF pre_bound new_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit_bound_from_sampled_transcript:
  assumes pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
      adversary_initial_state \<le> P + R"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
              adversary_initial_state)"
      and hit:
        "checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
          out"
    show
      "checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
        out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state data attacker_state result final_state
        where out_eq:
          "out =
            Some (((((prefix, prefix_state), data), attacker_state), result),
              final_state)"
        by (cases packed) (auto split: prod.splits)
      show ?thesis
        unfolding out_eq
        by (rule
            checked_staged_security_with_actual_alpha_prefix_some_support_imp_sampled_transcript_hit)
          (rule support[unfolded out_eq])
    qed
  qed
  have sampled_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit_bound_from_data_state
        [OF pre_bound new_bound])
  show ?thesis
    by (rule order_trans[OF event_le sampled_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_same_run_gap_and_transcript:
  fixes G P R :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and gap_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
        adversary_initial_state \<le> G"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and transcript_new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + G + (P + R) + (P + R)"
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
      adversary_initial_state \<le> G"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_same_run_partial_opening_gap
          gap_bound])
  have no_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_bound_from_sampled_transcript
        [OF data_pre_bound transcript_new_bound])
  have path_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_bound_from_sampled_transcript
        [OF data_pre_bound transcript_new_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_not_prefix_components
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_same_run_data_pre_and_witness_new:
  fixes P Q R :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and witness_new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> Q"
    and transcript_new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + (P + Q) + (P + R) +
      (P + R)"
proof -
  have gap_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
      adversary_initial_state \<le> P + Q"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_same_run_gap_bound_from_data_pre_and_new
        [OF data_pre_bound witness_new_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_same_run_gap_and_transcript
        [OF wf controlled gap_bound data_pre_bound transcript_new_bound])
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_from_same_run_gap_and_transcript:
  fixes G P empty_query_error :: prob
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
    and gap_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
        adversary_initial_state \<le> G"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + G +
        (P + staged_concrete_transcript_target_error_bound) +
        (P + staged_concrete_transcript_target_error_bound)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
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
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + G +
      (P + staged_concrete_transcript_target_error_bound) +
      (P + staged_concrete_transcript_target_error_bound)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_same_run_gap_and_transcript
        [OF wf controlled gap_bound data_pre_bound transcript_new_bound])
  have base:
    "checked_staged_adversary_acceptance_probability A \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds. C i) +
      trace_fri_error + composition_fri_error +
      (\<Sum>i<rounds. C i) +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) + G +
          (P + staged_concrete_transcript_target_error_bound) +
          (P + staged_concrete_transcript_target_error_bound)) +
        trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_current_query_prefix_rounds_from_relevant_drift_current_empty
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound drift_bound empty_trace_fri_bound current_empty_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma powers_scaled_domain_bound_imp_query_sample_space:
  assumes bounded:
      "\<And>j. j \<in> set (powers_scaled idx) \<Longrightarrow> j < clength * scale"
  shows "idx \<in> query_sample_space"
proof -
  let ?m = "Max (set [0..<powers])"
  have m_in: "?m \<in> set [0..<powers]"
    using powers_pos by (intro Max_in) simp_all
  have m_eq: "?m = powers - 1"
    using powers_pos by (intro Max_eqI) auto
  have idx_m_bound: "idx + ?m * scale < clength * scale"
    by (rule bounded) (use m_in in \<open>auto simp: powers_scaled_def\<close>)
  have m_le: "?m * scale \<le> clength * scale"
  proof -
    have "?m < clength"
      using m_eq powers_le_clength powers_pos by simp
    then show ?thesis
      by (simp add: mult_le_mono)
  qed
  have "idx < clength * scale - ?m * scale"
    using idx_m_bound m_le by linarith
  then show ?thesis
    unfolding query_sample_space_def query_sample_space_size_def by simp
qed

lemma partial_authenticated_trace_openings_query_index_in_sample_space:
  assumes indices:
      "map opening_index openings = powers_scaled idx"
    and auth:
      "partial_authenticated_table fr (scale * clength) openings s"
  shows "idx \<in> query_sample_space"
proof (rule powers_scaled_domain_bound_imp_query_sample_space)
  fix j
  assume j_in: "j \<in> set (powers_scaled idx)"
  have "j \<in> opening_index ` set openings"
    by (metis indices j_in set_map)
  then obtain opn where opn_in: "opn \<in> set openings"
    and j_eq: "j = opening_index opn"
    by blast
  have "opening_index opn < opening_length opn"
    using auth opn_in unfolding partial_authenticated_table_def
      authenticated_opening_in_def by blast
  moreover have "opening_length opn = scale * clength"
    using auth opn_in unfolding partial_authenticated_table_def by blast
  ultimately show "j < clength * scale"
    using j_eq by (simp add: mult.commute)
qed

lemma accepted_partial_trace_openings_leave_domain_gap_if_sparse_queries:
  assumes partial:
      "accepted_with_partial_trace_openings s out fr query_idxs trace_openings"
    and sparse: "rounds * powers < scale * clength"
  shows "partial_trace_openings_leave_domain_gap trace_openings"
proof -
  have rounds_len: "length trace_openings = rounds"
    by (rule accepted_with_partial_trace_openings_shapes(2)[OF partial])
  have concat_sparse:
    "length (List.concat trace_openings) < scale * clength"
    using accepted_with_partial_trace_openings_concat_length[OF partial]
      sparse by simp
  obtain j where j_bound: "j < scale * clength"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow>
        opn \<in> set (trace_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
    using sparse_openings_obtain_unopened_index[OF rounds_len concat_sparse]
    by blast
  show ?thesis
    unfolding partial_trace_openings_leave_domain_gap_def
    using j_bound unopened by blast
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap_if_sparse_queries:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and sparse: "rounds * powers < scale * clength"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        bad_sets out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_not_prefix_collision out \<or>
     checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate out \<or>
     checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output out \<or>
     checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from hit obtain fr f_fri_roots f_final as where not_prefix:
      "alpha_header_partial_candidate_not_prefix_bound prefix_state ?s fr
        f_fri_roots f_final"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound_def
      Let_def
    by (auto split: option.splits prod.splits)
  from checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_obtain_witness_final_ext
      [OF wf controlled support[unfolded out_eq] not_prefix]
  obtain trace_table witness_final_state trace_openings where witness:
      "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
        f_fri_roots f_final trace_table witness_final_state trace_openings"
    and table_not_prefix:
      "trace_table \<notin> alpha_prefix_trace_table_candidates prefix_state fr"
    and prefix_ext: "prefix_state \<le> witness_final_state"
    by blast
  from witness obtain result' query_idxs as' dg composition_fri_roots final rest
    where partial:
      "accepted_with_partial_trace_openings ?s
        (Some (result', witness_final_state)) fr query_idxs trace_openings"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  have gap:
    "partial_trace_openings_leave_domain_gap trace_openings"
    by (rule accepted_partial_trace_openings_leave_domain_gap_if_sparse_queries
        [OF partial sparse])
  have
    "checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
      out"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap_def
      Let_def
    using witness table_not_prefix prefix_ext gap
    by (simp split: prod.splits, blast)
  then show ?thesis by simp
qed

lemma alpha_header_witness_prefix_candidate_values_agree_on_openings:
  assumes prefix_candidate:
      "prefix_trace_table \<in>
        alpha_prefix_trace_table_candidates prefix_state fr"
    and witness:
      "alpha_header_supported_partial_trace_table_candidate_witness s fr
        f_fri_roots f_final trace_table final_state trace_openings"
    and pullback:
      "partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) prefix_state"
    and clean_prefix: "\<not> hash_map_output_collision prefix_state"
    and i_bound: "i < rounds"
  shows
    "map ((!) trace_table) (map opening_index (trace_openings ! i)) =
     map ((!) prefix_trace_table) (map opening_index (trace_openings ! i))"
proof -
  have prefix_len:
    "length prefix_trace_table = clength * scale"
    using prefix_candidate
    unfolding alpha_prefix_trace_table_candidates_def by simp
  have prefix_bind:
    "merkle_root_binds_table fr prefix_trace_table prefix_state"
    using prefix_candidate
    unfolding alpha_prefix_trace_table_candidates_def by simp
  from witness obtain result query_idxs as dg composition_fri_roots final rest
    where trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  have trace_agrees:
    "table_agrees_with_authenticated_openings trace_table
      (scale * clength) (trace_openings ! i)"
    using trace_cand i_bound
    unfolding partial_trace_table_candidate_def by blast
  have point_eq:
    "\<And>opn. opn \<in> set (trace_openings ! i) \<Longrightarrow>
      trace_table ! opening_index opn =
      prefix_trace_table ! opening_index opn"
  proof -
    fix opn
    assume opn_in: "opn \<in> set (trace_openings ! i)"
    have trace_value:
      "trace_table ! opening_index opn = opening_value opn"
      using trace_agrees opn_in
      unfolding table_agrees_with_authenticated_openings_def by blast
    have root: "opening_root opn = fr"
      using pullback opn_in unfolding partial_authenticated_table_def
      by blast
    have len: "opening_length opn = length prefix_trace_table"
      using pullback opn_in prefix_len
      unfolding partial_authenticated_table_def by simp
    have auth: "authenticated_opening_in prefix_state opn"
      using pullback opn_in unfolding partial_authenticated_table_def
      by blast
    obtain n where len_pow: "clength * scale = 2 ^ n"
      using eval_domain_length_power by blast
    have table_pow: "length prefix_trace_table = 2 ^ n"
      using prefix_len len_pow by (simp add: mult.commute)
    have prefix_value:
      "prefix_trace_table ! opening_index opn = opening_value opn"
      using
        merkle_bound_table_agrees_with_authenticated_opening_if_clean
          [OF prefix_bind table_pow auth root len clean_prefix]
      by simp
    show
      "trace_table ! opening_index opn =
       prefix_trace_table ! opening_index opn"
      using trace_value prefix_value by simp
  qed
  show ?thesis
    by (rule nth_equalityI)
      (use point_eq in auto)
qed

lemma alpha_header_witness_prefix_candidate_trace_table_agreement_index:
  assumes prefix_candidate:
      "prefix_trace_table \<in>
        alpha_prefix_trace_table_candidates prefix_state fr"
    and witness:
      "alpha_header_supported_partial_trace_table_candidate_witness s fr
        f_fri_roots f_final trace_table final_state trace_openings"
    and pullback:
      "partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) prefix_state"
    and clean_prefix: "\<not> hash_map_output_collision prefix_state"
    and i_bound: "i < rounds"
    and idx_sample: "idx \<in> query_sample_space"
    and idx_openings:
      "map opening_index (trace_openings ! i) = powers_scaled idx"
  shows "idx \<in> trace_table_agreement_indices trace_table prefix_trace_table"
proof -
  have agree:
    "map ((!) trace_table) (map opening_index (trace_openings ! i)) =
     map ((!) prefix_trace_table) (map opening_index (trace_openings ! i))"
    by (rule alpha_header_witness_prefix_candidate_values_agree_on_openings
        [OF prefix_candidate witness pullback clean_prefix i_bound])
  show ?thesis
    unfolding trace_table_agreement_indices_def
    using idx_sample agree idx_openings by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_imp_sampled_agreement_on_support:
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
      "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        bad_sets out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_not_prefix_collision out \<or>
     checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate out \<or>
     checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output out \<or>
     checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from hit obtain fr f_fri_roots f_final as where not_prefix_bound:
      "alpha_header_partial_candidate_not_prefix_bound prefix_state ?s fr
        f_fri_roots f_final"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound_def
      Let_def
    by (auto split: option.splits prod.splits)
  from checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_obtain_witness_final_ext
      [OF wf controlled support[unfolded out_eq] not_prefix_bound]
  obtain trace_table witness_final_state trace_openings where witness:
      "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
        f_fri_roots f_final trace_table witness_final_state trace_openings"
    and table_not_prefix:
      "trace_table \<notin> alpha_prefix_trace_table_candidates prefix_state fr"
    and prefix_ext: "prefix_state \<le> witness_final_state"
    by blast
  show ?thesis
  proof (cases "hash_map_output_collision prefix_state")
    case True
    then show ?thesis
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision_def
      by simp
  next
    case clean_prefix: False
    show ?thesis
    proof (cases "alpha_prefix_trace_table_candidates prefix_state fr = {}")
      case True
      then have
        "checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
          out"
        unfolding out_eq
          checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_def
          Let_def
        using witness table_not_prefix prefix_ext by (simp, blast)
      then show ?thesis by simp
    next
      case nonempty: False
      then obtain prefix_trace_table where prefix_candidate:
          "prefix_trace_table \<in>
            alpha_prefix_trace_table_candidates prefix_state fr"
        by blast
      have pullback_or_new:
        "(\<forall>i < rounds.
            partial_authenticated_table fr (scale * clength)
              (trace_openings ! i) prefix_state) \<or>
         (\<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
            hash_map_new_output_hit
              (merkle_path_target_roots witness_final_state fr
                (scale * clength) (opening_index opn)
                (opening_value opn) (opening_path opn))
              prefix_state witness_final_state)"
        by (rule alpha_header_witness_openings_pullback_or_new_output_hit
            [OF prefix_ext witness])
      from pullback_or_new show ?thesis
      proof
        assume pullback_all:
          "\<forall>i < rounds.
            partial_authenticated_table fr (scale * clength)
              (trace_openings ! i) prefix_state"
        from witness obtain witness_result query_idxs as dg
            composition_fri_roots final rest where partial:
            "accepted_with_partial_trace_openings ?s
              (Some (witness_result, witness_final_state)) fr query_idxs
              trace_openings"
          unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
          by blast
        have i_bound: "0 < rounds"
          by (rule rounds_positive)
        have idx_openings:
          "map opening_index (trace_openings ! 0) =
            powers_scaled (query_idxs ! 0)"
          by (rule accepted_with_partial_trace_openings_shapes(3)
              [OF partial i_bound])
        have pullback0:
          "partial_authenticated_table fr (scale * clength)
            (trace_openings ! 0) prefix_state"
          using pullback_all i_bound by blast
        have idx_sample: "query_idxs ! 0 \<in> query_sample_space"
          by (rule partial_authenticated_trace_openings_query_index_in_sample_space
              [OF idx_openings pullback0])
        have agreement:
          "query_idxs ! 0 \<in>
            trace_table_agreement_indices trace_table prefix_trace_table"
          by (rule
              alpha_header_witness_prefix_candidate_trace_table_agreement_index
              [OF prefix_candidate witness pullback0 clean_prefix i_bound
                idx_sample idx_openings])
        have
          "checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement
            out"
          unfolding out_eq
            checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement_def
            Let_def
          using witness table_not_prefix prefix_candidate prefix_ext partial
            i_bound agreement
          by (simp split: prod.splits, blast)
        then show ?thesis by simp
      next
        assume new:
          "\<exists>i<rounds. \<exists>opn\<in>set (trace_openings ! i).
            hash_map_new_output_hit
              (merkle_path_target_roots witness_final_state fr
                (scale * clength) (opening_index opn)
                (opening_value opn) (opening_path opn))
              prefix_state witness_final_state"
        have
          "checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
            out"
          unfolding out_eq
            checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_def
            Let_def
          using witness table_not_prefix prefix_ext new
          by (simp split: prod.splits, blast)
        then show ?thesis by simp
      qed
    qed
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_sampled_agreement_union_bound:
  fixes C S N P :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and collision_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
        adversary_initial_state \<le> C"
    and sampled_agreement_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement
        adversary_initial_state \<le> S"
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
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        bad_sets)
      adversary_initial_state \<le> C + S + N + P"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?B =
    "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
      bad_sets"
  let ?C = checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
  let ?S =
    checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement
  let ?N =
    checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
  let ?P = checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
  have "wp_event ?M ?B adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?C out \<or> ?S out \<or> ?N out \<or> ?P out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit: "?B out"
    from checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_imp_sampled_agreement_on_support
        [OF wf controlled support hit]
    show "?C out \<or> ?S out \<or> ?N out \<or> ?P out"
      by blast
  qed
  also have "... \<le>
      wp_event ?M ?C adversary_initial_state +
      wp_event ?M ?S adversary_initial_state +
      wp_event ?M ?N adversary_initial_state +
      wp_event ?M ?P adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le> C + S + N + P"
    by (intro add_mono collision_bound sampled_agreement_bound
        no_prefix_bound path_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement_imp_witness_transcript_hit:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using assms
    unfolding
      checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from assms obtain fr f_fri_roots f_final trace_table prefix_trace_table
      witness_final_state trace_openings witness_result query_idxs i where
    witness:
      "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
        f_fri_roots f_final trace_table witness_final_state trace_openings"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement_def
      Let_def
    by (auto split: prod.splits)
  from witness obtain result' query_idxs' as dg composition_fri_roots final
      rest where outcome:
      "Some (result', witness_final_state) \<in>
        set_dist (execute verify_monad ?s)"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  have tr_eq: "PTranscript ?s = staged_proof_transcript data"
    by simp
  have transcript_hit:
    "hash_map_output_values ?s \<inter> set (staged_proof_transcript data)
        \<noteq> {} \<or>
     hash_map_new_output_hit (set (staged_proof_transcript data))
        ?s witness_final_state"
    by (rule verify_monad_trace_root_target_preexisting_or_new
        [OF outcome tr_eq])
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_def
      Let_def
    using outcome transcript_hit
    by (auto split: prod.splits)
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement_le_witness_transcript_hit:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
    adversary_initial_state"
  by (rule wp_event_mono)
    (rule
      checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement_imp_witness_transcript_hit)

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement_bound_from_pre_and_new:
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
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement
      adversary_initial_state \<le> P + Q"
  by (rule order_trans
      [OF
        checked_staged_security_with_actual_alpha_prefix_not_prefix_sampled_agreement_le_witness_transcript_hit
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new
          [OF pre_bound new_bound]])

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_imp_sampled_transcript_hit_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        bad_sets out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state)"
    by (cases packed, auto split: prod.splits)
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
        [OF support[unfolded out_eq]])
  have verifier:
    "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    using checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
    by blast
  have tr_eq: "PTranscript ?s = staged_proof_transcript data"
    by simp
  have split:
    "hash_map_output_values ?s \<inter> set (staged_proof_transcript data)
        \<noteq> {} \<or>
     hash_map_new_output_hit (set (staged_proof_transcript data))
        ?s final_state"
    by (rule verify_monad_trace_root_target_preexisting_or_new
        [OF verifier tr_eq])
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit_def
      staged_security_with_data_state_transcript_pre_hit_def
      staged_security_with_data_state_transcript_new_hit_def
    using split by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_le_sampled_transcript_hit:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
      bad_sets)
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
    adversary_initial_state"
  by (rule wp_event_mono_on_support)
    (rule
      checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_imp_sampled_transcript_hit_on_support)

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_from_sampled_transcript:
  assumes pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        bad_sets)
      adversary_initial_state \<le> P + R"
  by (rule order_trans
      [OF
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_le_sampled_transcript_hit
        checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit_bound_from_data_state
          [OF pre_bound new_bound]])

lemma checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_sampled_transcript:
  fixes P R :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and transcript_new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le> P + R"
proof -
  have not_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_from_sampled_transcript
        [OF data_pre_bound transcript_new_bound])
  show ?thesis
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_le_not_prefix_bound
          not_prefix_bound])
      (use wf controlled in simp_all)
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_from_sampled_transcript_relevant_drift:
  fixes P empty_query_error :: prob
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
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (P + staged_concrete_transcript_target_error_bound) +
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
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_sampled_transcript
        [OF wf controlled data_pre_bound transcript_new_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_current_query_prefix_rounds_from_relevant_drift_current_empty
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound drift_bound empty_trace_fri_bound current_empty_bound])
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_from_sampled_transcript_relevant_drift_single_query_charge:
  fixes P empty_query_error :: prob
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
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (P + staged_concrete_transcript_target_error_bound) +
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
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_sampled_transcript
        [OF wf controlled data_pre_bound transcript_new_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_current_query_prefix_rounds_from_relevant_drift_current_empty_single_query_charge
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound drift_bound empty_trace_fri_bound current_empty_bound])
qed

theorem stark_soundness_from_aligned_partial_components_structured_query_and_current_empty_query_from_sampled_transcript_relevant_drift:
  fixes P empty_query_error :: prob
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
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error + 1 +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (P + staged_concrete_transcript_target_error_bound) +
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
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_sampled_transcript
        [OF wf controlled data_pre_bound transcript_new_bound])
  have header_query_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
        A)
      adversary_initial_state \<le> (1::prob)"
    by (rule wp_event_le_1)
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_structured_query_from_relevant_drift_current_empty
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound header_query_bound drift_bound empty_trace_fri_bound
          current_empty_bound])
qed

theorem stark_soundness_from_transcript_indexed_partial_opening_route_from_sampled_transcript:
  fixes P empty_query_error :: prob
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
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
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
        (P + staged_concrete_transcript_target_error_bound)) +
        (trace_fri_error +
          low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  have sampled_transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have not_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_from_sampled_transcript
        [OF data_pre_bound sampled_transcript_new_bound])
  show ?thesis
    by (rule
        stark_soundness_from_transcript_indexed_partial_opening_route_from_not_prefix
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound not_prefix_bound
          current_empty_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_sampled_agreement_imp_prefix_pair_hit:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_sampled_agreement
      A out"
  shows
    "\<exists>pair \<in> low_degree_trace_pair_space.
      \<exists>i \<in> {..<rounds}.
        checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_from_prefix
          A (fst pair) (snd pair) i out"
proof (cases out)
  case None
  then show ?thesis
    using assms
    unfolding
      checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_sampled_agreement_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix alpha_prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed, auto split: prod.splits)
  from assms obtain fr f_fri_roots f_final trace_table prefix_trace_table
      witness_final_state trace_openings witness_result query_idxs as i
      prefix prefix_state' raw raw_state where
    trace_low: "trace_table_low_degree trace_table"
    and prefix_low: "trace_table_low_degree prefix_trace_table"
    and distinct: "trace_table \<noteq> prefix_trace_table"
    and i_bound: "i < rounds"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((prefix, prefix_state'), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and raw_agree:
      "index (to_nat raw) \<in>
        trace_table_agreement_indices trace_table prefix_trace_table"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_sampled_agreement_def
      Let_def
    by (auto split: prod.splits)
  have pair_in:
    "(trace_table, prefix_trace_table) \<in> low_degree_trace_pair_space"
    unfolding low_degree_trace_pair_space_def
    using trace_low prefix_low distinct by simp
  have prefix_hit:
    "checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_from_prefix
      A trace_table prefix_trace_table i out"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_from_prefix_def
      checked_staged_query_prefix_dynamic_index_hit_def
    apply (simp add: builder)
    using prefix_receive raw_agree by blast
  show ?thesis
    by (intro bexI[of _ "(trace_table, prefix_trace_table)"]
        bexI[of _ i])
      (use pair_in i_bound prefix_hit in simp_all)
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_actual_sampled_agreement_imp_pair_hit:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_actual_sampled_agreement
      out"
  shows
    "\<exists>pair \<in> low_degree_trace_pair_space.
      \<exists>i \<in> {..<rounds}.
        checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
          (fst pair) (snd pair) i out"
proof (cases out)
  case None
  then show ?thesis
    using assms
    unfolding
      checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_actual_sampled_agreement_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed, auto split: prod.splits)
  from assms obtain fr f_fri_roots f_final trace_table prefix_trace_table
      witness_final_state trace_openings as query_idxs i where
    trace_low: "trace_table_low_degree trace_table"
    and prefix_low: "trace_table_low_degree prefix_trace_table"
    and distinct: "trace_table \<noteq> prefix_trace_table"
    and shape:
      "accepted_transcript_shape
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) as query_idxs"
    and i_bound: "i < rounds"
    and idx_agree:
      "query_idxs ! i \<in>
        trace_table_agreement_indices trace_table prefix_trace_table"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_actual_sampled_agreement_def
      Let_def
    by auto
  have pair_in:
    "(trace_table, prefix_trace_table) \<in> low_degree_trace_pair_space"
    unfolding low_degree_trace_pair_space_def
    using trace_low prefix_low distinct by simp
  have pair_hit:
    "checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
      trace_table prefix_trace_table i out"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at_def
      staged_security_with_data_state_trace_pair_agreement_hit_at_def
    using shape i_bound idx_agree by auto
  show ?thesis
    by (intro bexI[of _ "(trace_table, prefix_trace_table)"]
        bexI[of _ i])
      (use pair_in i_bound pair_hit in simp_all)
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_actual_sampled_agreement_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_actual_sampled_agreement
      adversary_initial_state \<le>
      low_degree_trace_pair_agreement_error budgets"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?pair_hit =
    "\<lambda>(pair, i) out.
      checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
        (fst pair) (snd pair) i out"
  let ?A = "low_degree_trace_pair_space \<times> {..<rounds}"
  have event_le:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_actual_sampled_agreement
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. \<exists>x \<in> ?A. ?pair_hit x out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (auto dest:
        checked_staged_security_with_actual_alpha_prefix_not_prefix_low_degree_actual_sampled_agreement_imp_pair_hit)
  have finite_A: "finite ?A"
    by simp
  have union_bound:
    "wp_event ?M (\<lambda>out. \<exists>x \<in> ?A. ?pair_hit x out)
      adversary_initial_state \<le>
     (\<Sum>x\<in>?A.
        case x of (pair, i) \<Rightarrow>
          staged_phase_relation_error size
            (staged_query_search_queries budgets i + 1) +
          nnreal clength / nnreal (card query_sample_space))"
  proof (rule wp_event_finite_UN_bound[OF finite_A])
    fix x
    assume x_in: "x \<in> ?A"
    then obtain trace_table prefix_trace_table i where x_eq:
        "x = ((trace_table, prefix_trace_table), i)"
      and pair_in:
        "(trace_table, prefix_trace_table) \<in> low_degree_trace_pair_space"
      and i_bound: "i < rounds"
      by (cases x, auto)
    have trace_low: "trace_table_low_degree trace_table"
      using pair_in unfolding low_degree_trace_pair_space_def by auto
    have prefix_low: "trace_table_low_degree prefix_trace_table"
      using pair_in unfolding low_degree_trace_pair_space_def by auto
    have distinct: "trace_table \<noteq> prefix_trace_table"
      using pair_in unfolding low_degree_trace_pair_space_def by auto
    have bound:
      "wp_event ?M
        (checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
          trace_table prefix_trace_table i)
        adversary_initial_state \<le>
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        nnreal clength / nnreal (card query_sample_space)"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at_bound
          [OF wf controlled i_bound trace_low prefix_low distinct])
    show "wp_event ?M (?pair_hit x) adversary_initial_state
        \<le> (case x of (pair, i) \<Rightarrow>
          staged_phase_relation_error size
            (staged_query_search_queries budgets i + 1) +
          nnreal clength / nnreal (card query_sample_space))"
      unfolding x_eq
      using bound by simp
  qed
  have sum_eq:
    "(\<Sum>x\<in>?A.
        case x of (pair, i) \<Rightarrow>
          staged_phase_relation_error size
            (staged_query_search_queries budgets i + 1) +
          nnreal clength / nnreal (card query_sample_space)) =
      low_degree_trace_pair_agreement_error budgets"
    unfolding low_degree_trace_pair_agreement_error_def
      low_degree_trace_pair_agreement_round_error_def
    by (simp add: sum.cartesian_product case_prod_unfold)
  show ?thesis
  proof (rule order_trans[OF event_le])
    show "wp_event ?M (\<lambda>out. \<exists>x \<in> ?A. ?pair_hit x out)
        adversary_initial_state \<le>
      low_degree_trace_pair_agreement_error budgets"
      using union_bound sum_eq by simp
  qed
qed

theorem stark_soundness_from_transcript_indexed_partial_opening_route_from_sampled_transcript_not_prefix:
  fixes P empty_query_error :: prob
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
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
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
        (P + staged_concrete_transcript_target_error_bound)) +
        (trace_fri_error +
          low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  have transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le>
      staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have not_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_from_sampled_transcript
        [OF data_pre_bound transcript_new_bound])
  show ?thesis
    by (rule
        stark_soundness_from_transcript_indexed_partial_opening_route_from_not_prefix
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound not_prefix_bound
          current_empty_bound])
qed

theorem stark_soundness_from_transcript_indexed_partial_opening_route_from_residual_sampled_transcript_not_prefix:
  fixes P empty_query_error :: prob
    and R :: "nat \<Rightarrow> prob"
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
    and residual_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
            i)
          adversary_initial_state \<le> R i"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
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
      query_error_bound + R i +
      (P + staged_concrete_transcript_target_error_bound) +
      (P + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R i +
      (P + staged_concrete_transcript_target_error_bound) +
      (P + staged_concrete_transcript_target_error_bound)) +
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
        (P + staged_concrete_transcript_target_error_bound)) +
        (trace_fri_error +
          low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  have transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le>
      staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have trace_path_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i)
        adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_current_trace_path_output_hit_at_bound_from_transcript
        [OF _ data_pre_bound transcript_new_bound])
  have composition_path_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i)
        adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_current_composition_path_output_hit_at_bound_from_transcript
        [OF _ data_pre_bound transcript_new_bound])
  have round_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R i +
      (P + staged_concrete_transcript_target_error_bound) +
      (P + staged_concrete_transcript_target_error_bound)"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_residual_and_structured_paths
        [OF wf controlled _ residual_bound trace_path_bound
          composition_path_bound])
  show ?thesis
    by (rule
        stark_soundness_from_transcript_indexed_partial_opening_route_from_sampled_transcript_not_prefix
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound data_pre_bound
          current_empty_bound])
qed

theorem stark_soundness_from_transcript_indexed_partial_opening_route_from_residual_split_sampled_transcript_not_prefix:
  fixes P empty_query_error :: prob
    and LT LC Alpha :: "nat \<Rightarrow> prob"
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
    and trace_low_degree_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_conceptual_trace_low_degree_bad_at
            i)
          adversary_initial_state \<le> LT i"
    and composition_low_degree_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_conceptual_composition_low_degree_bad_at
            i)
          adversary_initial_state \<le> LC i"
    and alpha_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_conceptual_alpha_bad_set_hit_at
            i)
          adversary_initial_state \<le> Alpha i"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
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
      (LT i + LC i + Alpha i) +
      (P + staged_concrete_transcript_target_error_bound) +
      (P + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      (LT i + LC i + Alpha i) +
      (P + staged_concrete_transcript_target_error_bound) +
      (P + staged_concrete_transcript_target_error_bound)) +
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
        (P + staged_concrete_transcript_target_error_bound)) +
        (trace_fri_error +
          low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  have residual_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
          i)
        adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      (LT i + LC i + Alpha i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have algebraic_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
          i)
        adversary_initial_state \<le> LT i + LC i + Alpha i"
      by (rule
          checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at_bound_from_split
          [OF false_statement trace_low_degree_bound[OF i_bound]
            composition_low_degree_bound[OF i_bound]
            alpha_bound[OF i_bound]])
    show
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
          i)
        adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      (LT i + LC i + Alpha i)"
      by (rule
          checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_bound_from_split
          [OF wf controlled i_bound algebraic_bound])
  qed
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound +
        (hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1) +
          (LT i + LC i + Alpha i)) +
        (P + staged_concrete_transcript_target_error_bound) +
        (P + staged_concrete_transcript_target_error_bound)) +
      trace_fri_error + composition_fri_error +
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound +
        (hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1) +
          (LT i + LC i + Alpha i)) +
        (P + staged_concrete_transcript_target_error_bound) +
        (P + staged_concrete_transcript_target_error_bound)) +
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
          (P + staged_concrete_transcript_target_error_bound)) +
          (trace_fri_error +
            low_degree_trace_pair_agreement_error budgets)) +
        trace_fri_error + empty_query_error)"
    by (rule
        stark_soundness_from_transcript_indexed_partial_opening_route_from_residual_sampled_transcript_not_prefix
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction residual_bound data_pre_bound
          current_empty_bound])
  show ?thesis
    using bound by (simp add: algebra_simps)
qed

theorem stark_soundness_from_transcript_indexed_partial_opening_route_from_same_run_partial_opening_gap_and_transcript:
  fixes G P empty_query_error :: prob
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
    and gap_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_same_run_partial_opening_gap
        adversary_initial_state \<le> G"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
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
          (staged_alpha_search_queries budgets 0) + G +
          (P + staged_concrete_transcript_target_error_bound) +
          (P + staged_concrete_transcript_target_error_bound))) +
        (trace_fri_error +
          low_degree_trace_pair_agreement_error budgets)) +
      trace_fri_error + empty_query_error)"
proof -
  have uncovered_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      adversary_initial_state \<le> G"
    by (rule order_trans
        [OF checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_same_run_partial_opening_gap
          gap_bound])
  show ?thesis
    by (rule
        stark_soundness_from_transcript_indexed_partial_opening_route_from_uncovered_and_transcript
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound uncovered_bound data_pre_bound
          current_empty_bound])
qed

end

end
