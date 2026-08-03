(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Header_Rounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Header_Rounds
  imports
    Staged_Security_Experiment_Composition_Query_Prefix_Witness
    Soundness_Query_Header_Cross_Candidate
begin

text \<open>
  Per-round decomposition for the header-authenticated composition query event.

  The global event existentially ranges over the query round and authenticated
  opening witnesses.  This layer peels off the finite round existential.  The
  remaining witness selection problem is deliberately left explicit: later
  proofs must either choose prefix-fixed witnesses before the query challenge or
  charge failures to Merkle/collision side events.
\<close>

context soundness
begin

definition staged_query_prefix_header_supported_query_target
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_header_supported_query_target prefix prefix_state =
    query_header_supported_partial_union_good_sets prefix_state
      query_sampling_success_space
      (sqp_trace_root prefix)
      (sqp_trace_fri_roots prefix)
      (sqp_trace_final prefix)
      (sqp_alphas prefix)
      (sqp_degree prefix)
      (sqp_composition_fri_roots prefix)
      (sqp_composition_final prefix)"

lemma staged_query_prefix_header_supported_query_target_subset:
  "staged_query_prefix_header_supported_query_target prefix prefix_state
    \<subseteq> query_sample_space"
  unfolding staged_query_prefix_header_supported_query_target_def
  by (rule query_header_supported_partial_union_good_sets_subset)

lemma staged_query_prefix_header_supported_query_target_fraction_bound_if_no_cross_or_merkle_bad:
  assumes no_bad:
      "\<not> query_supported_partial_pairwise_cross_or_merkle_bad prefix_state"
  shows
    "nnreal
      (card
        (staged_query_prefix_header_supported_query_target prefix
          prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
  unfolding staged_query_prefix_header_supported_query_target_def
  by (rule
      query_header_supported_partial_union_good_sets_fraction_bound_if_no_global_cross_or_merkle_bad
      [OF no_bad query_sampling_success_space_subset
        query_sampling_success_space_fraction_bound_query_sample_space])

lemma checked_staged_query_prefix_header_supported_query_target_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_header_supported_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        staged_query_prefix_header_supported_query_target)
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_header_supported_query_target_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and no_bad:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> query_supported_partial_pairwise_cross_or_merkle_bad
          prefix_state"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_header_supported_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_header_supported_query_target)
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_header_supported_query_target)
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    show
      "staged_query_prefix_header_supported_query_target prefix prefix_state
        \<subseteq> query_sample_space \<and>
       nnreal
        (card
          (staged_query_prefix_header_supported_query_target prefix
            prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      using
        staged_query_prefix_header_supported_query_target_subset
          [of prefix prefix_state]
        staged_query_prefix_header_supported_query_target_fraction_bound_if_no_cross_or_merkle_bad
          [of prefix_state prefix, OF no_bad[OF support]]
      by blast
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_header_supported_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_query_prefix_header_supported_query_target_prehit_bound
        [OF wf controlled])
      (use i_bound in simp)
  show ?thesis
    by (rule order_trans[OF hit_bound])
      (intro add_mono prehit_bound order_refl)
qed

definition checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
  :: "nat \<Rightarrow> 'f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
      i A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (let s =
          verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)
         in \<exists>trace_openings composition_openings.
          (trace_openings, composition_openings) \<in>
            query_header_supported_partial_opening_witnesses s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              (staged_alphas data)
              (staged_degree data)
              (staged_composition_fri_roots data)
              (staged_composition_final data) \<and>
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
            A
            ((replicate rounds []) [i := trace_openings])
            ((replicate rounds []) [i := composition_openings])
            i
            (Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state))))"

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_atI:
  assumes witness:
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
    and component:
      "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  unfolding
    checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_def
    Let_def
  using witness component
  by (auto split: option.splits prod.splits)

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_imp_round:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
      A out"
  shows
    "\<exists>i < rounds.
      checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
        i A out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix alpha_prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed) (auto split: prod.splits)
  from checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefixE
      [OF hit[unfolded out_eq]]
  obtain i trace_openings composition_openings where witness:
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
    and component:
      "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    by blast
  have i_bound: "i < rounds"
    using component
    unfolding
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix_def
    by (simp split: option.splits prod.splits)
  have round_hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
      i A out"
    unfolding out_eq
    by (rule
        checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_atI
        [OF witness component])
  show ?thesis
    using i_bound round_hit by blast
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_atE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains trace_openings composition_openings where
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
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  using hit
  unfolding
    checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_def
    Let_def
  by (auto split: option.splits prod.splits)

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_candidates_or_partial_merkle_bad:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    and i_bound: "i < rounds"
  shows
    "(\<exists>result' final_state'.
      partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result', final_state'))) \<or>
    (\<exists>trace_openings composition_openings trace_table composition_table.
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
          (staged_composition_final data) \<and>
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
        A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)) \<and>
      partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings]) \<and>
      partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings]))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from
    checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_atE
      [OF hit]
  obtain trace_openings composition_openings where witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
    and component:
      "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
        A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    by blast
  from query_header_supported_partial_opening_witness_single_round_candidates_or_partial_merkle_bad
      [OF witness i_bound]
  show ?thesis
    using witness component by blast
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_imp_partial_merkle_or_candidate_pair:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    and i_bound: "i < rounds"
    and trace_low:
      "\<And>trace_openings composition_openings trace_table
          composition_table.
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
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        trace_table_low_degree trace_table"
    and comp_low:
      "\<And>trace_openings composition_openings trace_table
          composition_table.
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
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>trace_openings composition_openings trace_table
          composition_table prefix prefix_state.
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
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "(\<exists>result' final_state'.
      partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result', final_state'))) \<or>
    (\<exists>trace_table composition_table.
      checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
        A trace_table composition_table i
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state)))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from
    checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_candidates_or_partial_merkle_bad
      [OF hit i_bound]
  show ?thesis
  proof
    assume
      "\<exists>result' final_state'.
        partial_merkle_inconsistency_bad ?s (Some (result', final_state'))"
    then show ?thesis by simp
  next
    assume candidates:
      "\<exists>trace_openings composition_openings trace_table
          composition_table.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses ?s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<and>
        checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
          A
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i
          (Some (((((alpha_prefix, alpha_prefix_state), data),
            attacker_state), result), final_state)) \<and>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<and>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings])"
    then obtain trace_openings composition_openings trace_table
        composition_table where witness:
        "(trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses ?s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)"
      and opening_hit:
        "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
          A
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i
          (Some (((((alpha_prefix, alpha_prefix_state), data),
            attacker_state), result), final_state))"
      and trace_candidate:
        "partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings])"
      and comp_candidate:
        "partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings])"
      by blast
    have pair_hit:
      "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
        A trace_table composition_table i
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix_imp_candidate_pair_query_hit_from_prefix
          [OF opening_hit trace_candidate comp_candidate
            trace_low[OF witness trace_candidate comp_candidate]
            comp_low[OF witness trace_candidate comp_candidate]])
        (rule not_all[OF witness trace_candidate comp_candidate])
    then show ?thesis by blast
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_round_union_bound:
  fixes Q :: "nat \<Rightarrow> prob"
  assumes round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
          (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
            i A)
          adversary_initial_state \<le> Q i"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
        A)
      adversary_initial_state \<le> (\<Sum>i<rounds. Q i)"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
        A)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. \<exists>i \<in> {..<rounds}.
        checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
          i A out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (use
        checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_imp_round
        in blast)
  have union_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. \<exists>i \<in> {..<rounds}.
        checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
          i A out)
      adversary_initial_state \<le>
      (\<Sum>i<rounds. Q i)"
    by (rule wp_event_finite_UN_bound) (simp_all add: round_bound)
  show ?thesis
    by (rule order_trans[OF event_le union_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_header_authenticated_query_from_prefix_rounds_and_budgets:
  fixes Q :: "nat \<Rightarrow> prob"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
            i A)
          adversary_initial_state \<le> Q i"
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
      (\<Sum>i<rounds. Q i) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have header_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
        A)
      adversary_initial_state \<le> (\<Sum>i<rounds. Q i)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_round_union_bound
        [OF round_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_header_authenticated_query_from_prefix_and_budgets
        [OF wf controlled header_bound])
qed

end

end
