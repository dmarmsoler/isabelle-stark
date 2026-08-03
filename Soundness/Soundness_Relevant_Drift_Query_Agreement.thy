(*  Title:      Stark/Soundness_Relevant_Drift_Query_Agreement.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Relevant_Drift_Query_Agreement
  imports Soundness_Relevant_Drift_Reachable_FRI
begin

text \<open>
  Fixed trace-pair query-agreement bounds for the empty-header relevant-drift
  residual.  This layer keeps the candidate pair fixed before the query
  challenge is sampled.  It therefore avoids the invalid broad fixed-cover
  route where partial openings selected after the query determine the target.
\<close>

context soundness
begin

definition staged_security_with_data_state_trace_pair_agreement_hit_at
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "staged_security_with_data_state_trace_pair_agreement_hit_at
      trace_table trace_table' i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((data, attacker_state), result), final_state) \<Rightarrow>
        (\<exists>as query_idxs.
          accepted_transcript_shape
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (Some (result, final_state)) as query_idxs \<and>
          i < rounds \<and>
          query_idxs ! i \<in>
            trace_table_agreement_indices trace_table trace_table'))"

definition checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
      trace_table trace_table' i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        staged_security_with_data_state_trace_pair_agreement_hit_at
          trace_table trace_table' i
          (Some (((data, attacker_state), result), final_state)))"

definition checked_staged_security_with_query_prefix_trace_pair_agreement_hit_at
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      (((((('f staged_query_prefix_data \<times> 'f protocol_channel) \<times>
          'f) \<times> 'f protocol_channel) \<times>
        (('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list)) \<times>
        'f protocol_channel) option) \<Rightarrow> bool"
where
  "checked_staged_security_with_query_prefix_trace_pair_agreement_hit_at
      trace_table trace_table' i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_dynamic_index_hit
      (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table') out"

lemma checked_staged_query_prefix_trace_pair_agreement_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table'))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table'))
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled less_imp_le[OF i_bound]])
      (rule checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_trace_pair_agreement_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table'))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal clength / nnreal (card query_sample_space)"
proof -
  have hit:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table'))
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table'))
      adversary_initial_state +
     nnreal clength / nnreal (card query_sample_space)"
    by (rule checked_staged_query_prefix_trace_pair_agreement_hit_bound_by_prehit
        [OF trace_low trace'_low distinct])
  have pre:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table'))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
    by (rule checked_staged_query_prefix_trace_pair_agreement_prehit_bound
        [OF wf controlled i_bound])
  show ?thesis
    by (rule order_trans[OF hit]) (intro add_mono pre order_refl)
qed

lemma checked_staged_security_with_query_prefix_trace_pair_agreement_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_trace_pair_agreement_hit_at
        trace_table trace_table' i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal clength / nnreal (card query_sample_space)"
  unfolding checked_staged_security_with_query_prefix_trace_pair_agreement_hit_at_def
  by (rule checked_staged_security_with_query_prefix_dynamic_index_hit_bound)
    (rule checked_staged_query_prefix_trace_pair_agreement_hit_bound
      [OF wf controlled i_bound trace_low trace'_low distinct])

lemma staged_security_with_data_state_trace_pair_agreement_hit_at_le_query_prefix:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_trace_pair_agreement_hit_at
        trace_table trace_table' i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_trace_pair_agreement_hit_at
        trace_table trace_table' i)
      adversary_initial_state"
proof -
  let ?E =
    "staged_security_with_data_state_trace_pair_agreement_hit_at
      trace_table trace_table' i"
  let ?Q =
    "checked_staged_security_with_query_prefix_trace_pair_agreement_hit_at
      trace_table trace_table' i"
  have proj:
    "wp_event (checked_staged_security_experiment_with_data_state A) ?E
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out. case out of
        None \<Rightarrow> ?E None
      | Some (packed, t) \<Rightarrow> ?E (Some (snd packed, t)))
      adversary_initial_state"
    by (rule checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound])
  show ?thesis
    unfolding proj
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state
              A i)
            adversary_initial_state)"
      and hit:
        "(case out of None \<Rightarrow> ?E None
        | Some (packed, t) \<Rightarrow> ?E (Some (snd packed, t)))"
    show "?Q out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding staged_security_with_data_state_trace_pair_agreement_hit_at_def
          checked_staged_security_with_query_prefix_trace_pair_agreement_hit_at_def
          checked_staged_security_with_query_prefix_dynamic_index_hit_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state
          result final_state where out_eq:
          "out =
            Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state)"
        by (cases packed, auto split: prod.splits)
      have support':
        "Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)
          \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state)"
        using support unfolding out_eq .
      have data_support:
        "Some (((data, attacker_state), result), final_state) \<in>
          set_dist
            (execute (checked_staged_security_experiment_with_data_state A)
              adversary_initial_state)"
        by (rule
            checked_staged_security_experiment_with_query_prefix_data_state_imp_data_state_support
            [OF i_bound support'])
      have data_hit:
        "staged_security_with_data_state_trace_pair_agreement_hit_at
          trace_table trace_table' i
          (Some (((data, attacker_state), result), final_state))"
        using hit unfolding out_eq by simp
      obtain as query_idxs where shape:
          "accepted_transcript_shape
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (Some (result, final_state)) as query_idxs"
        and idx_agree:
          "query_idxs ! i \<in>
            trace_table_agreement_indices trace_table trace_table'"
        using data_hit unfolding
          staged_security_with_data_state_trace_pair_agreement_hit_at_def
        by auto
      from checked_staged_security_with_data_state_accepted_shape_query_keys
          [OF wf controlled data_support shape]
      obtain raw_idxs where len_raw: "length raw_idxs = rounds"
        and query_idxs_eq:
          "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
        and lookup_final:
          "\<And>j. j < rounds \<Longrightarrow>
            fmlookup (HashMap final_state)
              (QueryIndexChallenge j
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) j)) =
            Some (raw_idxs ! j)"
        by blast
      have final_lookup:
        "fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data) (staged_query_chunks data) i)) =
          Some raw"
        by (rule
            checked_staged_security_experiment_with_query_prefix_data_state_raw_final_lookup
            [OF wf controlled i_bound support'])
      have raw_eq: "raw_idxs ! i = raw"
        using lookup_final[OF i_bound] final_lookup by simp
      have raw_agree:
        "index (to_nat raw) \<in>
          trace_table_agreement_indices trace_table trace_table'"
        using idx_agree query_idxs_eq len_raw i_bound raw_eq by simp
      show ?thesis
        unfolding out_eq
          checked_staged_security_with_query_prefix_trace_pair_agreement_hit_at_def
          checked_staged_security_with_query_prefix_dynamic_index_hit_def
          checked_staged_query_prefix_dynamic_index_hit_def
        using raw_agree by simp
    qed
  qed
qed

lemma staged_security_with_data_state_trace_pair_agreement_hit_at_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_trace_pair_agreement_hit_at
        trace_table trace_table' i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal clength / nnreal (card query_sample_space)"
  by (rule order_trans[
      OF staged_security_with_data_state_trace_pair_agreement_hit_at_le_query_prefix
        checked_staged_security_with_query_prefix_trace_pair_agreement_hit_bound])
    (use assms in simp_all)

lemma checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at_projection:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
      trace_table trace_table' i)
    adversary_initial_state =
   wp_event (checked_staged_security_experiment_with_data_state A)
    (staged_security_with_data_state_trace_pair_agreement_hit_at
      trace_table trace_table' i)
    adversary_initial_state"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_trace_pair_agreement_hit_at
        trace_table trace_table' i)
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
        \<bind> (\<lambda>x. return (?project x)))
      (staged_security_with_data_state_trace_pair_agreement_hit_at
        trace_table trace_table' i)
      adversary_initial_state"
    using
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
      [of A]
    by simp
  also have "... =
    wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
        trace_table trace_table' i)
      adversary_initial_state"
  proof -
    have pred_eq:
      "(\<lambda>out. case out of
        None \<Rightarrow>
          staged_security_with_data_state_trace_pair_agreement_hit_at
            trace_table trace_table' i None
      | Some (x, t) \<Rightarrow>
          staged_security_with_data_state_trace_pair_agreement_hit_at
            trace_table trace_table' i (Some (?project x, t))) =
      checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
        trace_table trace_table' i"
      by (rule ext)
        (auto simp:
          staged_security_with_data_state_trace_pair_agreement_hit_at_def
          checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at_def
          split: option.splits prod.splits)
    show ?thesis
      by (subst wp_event_bind_return_map) (simp add: pred_eq)
  qed
  finally show ?thesis
    by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
        trace_table trace_table' i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal clength / nnreal (card query_sample_space)"
  unfolding
    checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at_projection
  by (rule staged_security_with_data_state_trace_pair_agreement_hit_at_bound
      [OF wf controlled i_bound trace_low trace'_low distinct])

definition low_degree_trace_pair_space :: "('f list \<times> 'f list) set"
where
  "low_degree_trace_pair_space =
    {(trace_table, trace_table').
      trace_table_low_degree trace_table \<and>
      trace_table_low_degree trace_table' \<and>
      trace_table \<noteq> trace_table'}"

lemma trace_table_low_degree_length:
  assumes "trace_table_low_degree trace_table"
  shows "length trace_table = clength * scale"
  using assms unfolding trace_table_low_degree_def
  by (auto simp: eval_domain_length)

lemma finite_low_degree_trace_pair_space[simp]:
  "finite low_degree_trace_pair_space"
proof -
  have subset:
    "low_degree_trace_pair_space \<subseteq>
      {xs. length xs = clength * scale} \<times>
      {xs. length xs = clength * scale}"
    unfolding low_degree_trace_pair_space_def
    by (auto dest: trace_table_low_degree_length)
  show ?thesis
    by (rule finite_subset[OF subset])
      (simp add: finite_length_lists_UNIV)
qed

definition low_degree_trace_pair_agreement_round_error
where
  "low_degree_trace_pair_agreement_round_error budgets i =
    (\<Sum>(trace_table, trace_table') \<in> low_degree_trace_pair_space.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal clength / nnreal (card query_sample_space))"

definition low_degree_trace_pair_agreement_error
where
  "low_degree_trace_pair_agreement_error budgets =
    (\<Sum>x \<in> low_degree_trace_pair_space \<times> {..<rounds}.
      case x of (pair, i) \<Rightarrow>
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        nnreal clength / nnreal (card query_sample_space))"

lemma empty_header_low_degree_transcript_query_agreement_imp_pair_hit:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit
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
    unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
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
  have hit:
    "empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit
      ?s (Some (result, final_state))"
    using assms
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
    by simp
  then obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table trace_table' i where
    shape:
      "accepted_transcript_shape ?s (Some (result, final_state)) as
        trace_query_idxs"
    and distinct: "trace_table \<noteq> trace_table'"
    and trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and i_bound: "i < rounds"
    and idx_agree:
      "trace_query_idxs ! i \<in>
        trace_table_agreement_indices trace_table trace_table'"
    by (rule
        empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreementE)
  have pair_in:
    "(trace_table, trace_table') \<in> low_degree_trace_pair_space"
    unfolding low_degree_trace_pair_space_def
    using trace_low trace'_low distinct by simp
  have pair_hit:
    "checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
      trace_table trace_table' i out"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at_def
      staged_security_with_data_state_trace_pair_agreement_hit_at_def
    using shape i_bound idx_agree by auto
  show ?thesis
    by (intro bexI[of _ "(trace_table, trace_table')"]
        bexI[of _ i])
      (use pair_in i_bound pair_hit in simp_all)
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_low_degree_transcript_query_agreement_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit)
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
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit)
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. \<exists>x \<in> ?A. ?pair_hit x out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (auto dest:
        empty_header_low_degree_transcript_query_agreement_imp_pair_hit)
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
    then obtain trace_table trace_table' i where x_eq:
        "x = ((trace_table, trace_table'), i)"
      and pair_in:
        "(trace_table, trace_table') \<in> low_degree_trace_pair_space"
      and i_bound: "i < rounds"
      by (cases x, auto)
    have trace_low: "trace_table_low_degree trace_table"
      using pair_in unfolding low_degree_trace_pair_space_def by auto
    have trace'_low: "trace_table_low_degree trace_table'"
      using pair_in unfolding low_degree_trace_pair_space_def by auto
    have distinct: "trace_table \<noteq> trace_table'"
      using pair_in unfolding low_degree_trace_pair_space_def by auto
    have bound:
      "wp_event ?M
        (checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at
          trace_table trace_table' i)
        adversary_initial_state \<le>
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        nnreal clength / nnreal (card query_sample_space)"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_at_bound
          [OF wf controlled i_bound trace_low trace'_low distinct])
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
    show "wp_event ?M (\<lambda>out. \<exists>x\<in>?A. ?pair_hit x out)
        adversary_initial_state \<le>
      low_degree_trace_pair_agreement_error budgets"
      using union_bound sum_eq by simp
  qed
qed

end

end
