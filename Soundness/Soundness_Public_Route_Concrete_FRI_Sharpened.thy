(*  Title:      Stark/Soundness_Public_Route_Concrete_FRI_Sharpened.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Public_Route_Concrete_FRI_Sharpened
  imports
    Soundness_Public_Route_Concrete_FRI_Endpoint
    Soundness_FRI_Query_Fiber_Staged_Bounds
    Soundness_FRI_Prequery_Challenge_Bounds
    Soundness_FRI_Sampled_Challenge_Cover
    Soundness_FRI_Staged_Replay_Bounds
    Soundness_FRI_Zero_Round_Agreement_Set_Bounds
    Soundness_FRI_Trace_Empty_Verifier_Tied
begin

text \<open>
  First-stage API for sharpening the concrete FRI endpoint.

  The public endpoint already removed the FRI soundness assumptions by using
  explicit staged verifier-event error definitions.  This theory factors those
  definitions into named challenge, full-cover/domain, conflict, and
  zero-round components.  At this stage the components are definitionally equal
  to the endpoint terms; later proof layers can replace individual components
  by sharper product/fiber or residual sums without touching the public
  theorem interface.
\<close>

context soundness
begin

definition trace_fri_challenge_prequery_error_for
where
  "trace_fri_challenge_prequery_error_for budgets A =
    (wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          trace_fri_challenge_list_fresh_hit s
            (fri_challenge_space (ceil_log clength))))
      adversary_initial_state +
    hash_relation_budget_value
      (card (fri_challenge_space (ceil_log clength)) * ceil_log clength)
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget))"

definition trace_fri_full_cover_domain_residual_error_for
where
  "trace_fri_full_cover_domain_residual_error_for A =
    (reachable_verifier_event_bound_for A
      (\<lambda>s.
        trace_fri_sampled_full_cover_proximity_failure s
          trace_fri_full_challenge_bad) +
     reachable_verifier_event_bound_for A
      trace_fri_sampled_full_cover_index_failure +
     (reachable_verifier_event_bound_for A
        trace_fri_sampled_full_cover_index_failure +
      reachable_verifier_event_bound_for A
        trace_fri_sampled_full_cover_domain_length_failure) +
     (reachable_verifier_event_bound_for A
        trace_fri_sampled_full_cover_index_failure +
      reachable_verifier_event_bound_for A
        trace_fri_sampled_full_cover_sampled_domain_failure))"

definition sharpened_trace_fri_full_cover_domain_error_for
where
  "sharpened_trace_fri_full_cover_domain_error_for budgets A =
    trace_fri_challenge_prequery_error_for budgets A +
      trace_fri_full_cover_domain_residual_error_for A"

definition trace_fri_header_conflict_zero_error_for
where
  "trace_fri_header_conflict_zero_error_for A =
    (reachable_verifier_event_bound_for A
      trace_fri_header_tied_sampled_assignment_conflict +
     reachable_verifier_event_bound_for A
      trace_fri_header_tied_zero_round_final_obstruction)"

definition trace_fri_header_replay_conflict_error_for
where
  "trace_fri_header_replay_conflict_error_for A =
    (let M = reachable_verifier_event_bound_for A
          partial_merkle_inconsistency_bad;
         H = reachable_verifier_event_bound_for A
          trace_fri_header_tied_recorded_sibling_candidate_missing
     in H + ((((M + M) + (M + 0) + (M + 0) + (M + 0 + 0)) + M) + 0))"

definition trace_fri_controlled_merkle_error_for
where
  "trace_fri_controlled_merkle_error_for budgets =
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget)"

definition trace_fri_header_replay_conflict_zero_error_for
where
  "trace_fri_header_replay_conflict_zero_error_for budgets A =
    trace_fri_header_replay_conflict_error_for A +
      (trace_fri_zero_round_agreement_set_target_error_for budgets +
       trace_fri_controlled_merkle_error_for budgets)"

definition sharpened_trace_fri_header_error_for
where
  "sharpened_trace_fri_header_error_for budgets A =
    sharpened_trace_fri_full_cover_domain_error_for budgets A +
      trace_fri_header_conflict_zero_error_for A"

definition trace_fri_empty_conflict_zero_error_for
where
  "trace_fri_empty_conflict_zero_error_for A =
    (reachable_verifier_event_bound_for A
      trace_fri_sampled_assignment_conflict +
     reachable_verifier_event_bound_for A
      trace_fri_zero_round_final_obstruction)"

definition trace_fri_empty_small_conflict_zero_error_for
where
  "trace_fri_empty_small_conflict_zero_error_for budgets A =
    (reachable_verifier_event_bound_for A
      trace_fri_sampled_assignment_conflict +
     trace_fri_zero_round_agreement_set_target_error_for budgets +
     trace_fri_controlled_merkle_error_for budgets +
     reachable_verifier_event_bound_for A
      trace_fri_bad_with_header_tied_partial_candidate +
     (trace_fri_controlled_merkle_error_for budgets +
      (reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_root_gap +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_query_gap)) +
     reachable_verifier_event_bound_for A
      trace_fri_bad_with_header_tied_partial_candidate)"

definition sharpened_trace_fri_empty_error_for
where
  "sharpened_trace_fri_empty_error_for budgets A =
    sharpened_trace_fri_full_cover_domain_error_for budgets A +
      trace_fri_empty_conflict_zero_error_for A"

definition composition_fri_challenge_prequery_error_for
where
  "composition_fri_challenge_prequery_error_for budgets A =
    (wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          composition_fri_challenge_list_fresh_hit s
            (\<lambda>dg. fri_challenge_space (ceil_log (to_nat dg + 1)))))
      adversary_initial_state +
    hash_relation_budget_value
      (\<Sum>dg \<in> (UNIV :: 'f set).
        card (fri_challenge_space (ceil_log (to_nat dg + 1))) *
          ceil_log (maxDegree + 1))
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget))"

definition composition_fri_full_cover_domain_residual_error_for
where
  "composition_fri_full_cover_domain_residual_error_for A =
    (reachable_verifier_event_bound_for A
      (\<lambda>s.
        composition_fri_sampled_full_cover_proximity_failure s
          composition_fri_full_challenge_bad) +
     reachable_verifier_event_bound_for A
      composition_fri_sampled_full_cover_index_failure +
     (reachable_verifier_event_bound_for A
        composition_fri_sampled_full_cover_index_failure +
      reachable_verifier_event_bound_for A
        composition_fri_sampled_full_cover_domain_length_failure) +
     (reachable_verifier_event_bound_for A
        composition_fri_sampled_full_cover_index_failure +
      reachable_verifier_event_bound_for A
        composition_fri_sampled_full_cover_sampled_domain_failure))"

definition sharpened_composition_fri_full_cover_domain_error_for
where
  "sharpened_composition_fri_full_cover_domain_error_for budgets A =
    composition_fri_challenge_prequery_error_for budgets A +
      composition_fri_full_cover_domain_residual_error_for A"

definition composition_fri_conflict_zero_error_for
where
  "composition_fri_conflict_zero_error_for A =
    (reachable_verifier_event_bound_for A
      composition_fri_verifier_tied_sampled_assignment_conflict +
     reachable_verifier_event_bound_for A
      composition_fri_verifier_tied_zero_round_final_obstruction)"

definition sharpened_composition_fri_error_for
where
  "sharpened_composition_fri_error_for budgets A =
    sharpened_composition_fri_full_cover_domain_error_for budgets A +
      composition_fri_conflict_zero_error_for A"

definition composition_one_step_query_fraction_for
  :: "('f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> prob"
where
  "composition_one_step_query_fraction_for comp_bad =
    nnreal
      ((\<Sum>dg \<in> (UNIV :: 'f set).
        \<Sum>challenges \<in>
          fri_challenge_space (fri_round_count_for_degree_bound (to_nat dg)) -
            generic_fri_bad_challenge_lists
              (fri_round_count_for_degree_bound (to_nat dg))
              (comp_bad dg).
          card
            (generic_fri_sampled_query_query_fiber
              (composition_table_low_degree (to_nat dg))
              (Not \<circ> composition_table_low_degree maxDegree)
              (to_nat dg) challenges)) * rounds) /
      nnreal (card query_sample_space)"

definition composition_one_step_challenge_hash_count :: nat
where
  "composition_one_step_challenge_hash_count =
    (\<Sum>dg \<in> (UNIV :: 'f set).
      fri_one_step_disagreement_round_mass
        (fri_round_count_for_degree_bound (to_nat dg))
        (composition_fri_canonical_layer_len dg) *
      ceil_log (maxDegree + 1))"

definition composition_one_step_sampled_error_for
where
  "composition_one_step_sampled_error_for budgets comp_bad =
    concrete_composition_fri_bad_challenge_fraction +
      hash_relation_budget_value
        composition_one_step_challenge_hash_count
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      nnreal (staged_attacker_query_budget budgets +
        staged_challenge_query_budget) *
        composition_one_step_query_fraction_for comp_bad"

definition composition_one_step_reachable_merkle_error_for
where
  "composition_one_step_reachable_merkle_error_for A =
    reachable_verifier_event_bound_for A partial_merkle_inconsistency_bad"

definition composition_one_step_controlled_merkle_error_for
where
  "composition_one_step_controlled_merkle_error_for budgets =
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget)"

definition composition_one_step_verifier_tied_error_for
where
  "composition_one_step_verifier_tied_error_for budgets A comp_bad =
    composition_one_step_sampled_error_for budgets comp_bad +
      (((composition_one_step_reachable_merkle_error_for A + 0) +
        (composition_one_step_reachable_merkle_error_for A + 0) +
        (composition_one_step_reachable_merkle_error_for A + 0) +
        (composition_one_step_reachable_merkle_error_for A + 0 + 0) +
        composition_one_step_reachable_merkle_error_for A) + 0 + 0)"

definition composition_one_step_verifier_tied_controlled_error_for
where
  "composition_one_step_verifier_tied_controlled_error_for budgets comp_bad =
    composition_one_step_sampled_error_for budgets comp_bad +
      (((composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0 + 0) +
        composition_one_step_controlled_merkle_error_for budgets) + 0 + 0)"

definition trace_one_step_query_fraction_for
  :: "(nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> prob"
where
  "trace_one_step_query_fraction_for empty_bad =
    nnreal
      ((\<Sum>challenges \<in>
        fri_challenge_space (fri_round_count_for_degree_bound (clength - 1)) -
          generic_fri_bad_challenge_lists
            (fri_round_count_for_degree_bound (clength - 1)) empty_bad.
        card
          (generic_fri_sampled_query_query_fiber trace_table_low_degree
            (Not \<circ> trace_table_low_degree) (clength - 1) challenges)) *
        rounds) /
      nnreal (card query_sample_space)"

definition trace_one_step_challenge_hash_count :: nat
where
  "trace_one_step_challenge_hash_count =
    fri_one_step_disagreement_round_mass
      (fri_round_count_for_degree_bound (clength - 1))
      trace_fri_canonical_layer_len *
    ceil_log clength"

definition trace_one_step_disagreement_bad_for
  :: "(nat \<Rightarrow> nat) \<Rightarrow>
      (nat \<Rightarrow> 'f list \<Rightarrow> 'f list) \<Rightarrow>
      (nat \<Rightarrow> 'f list \<Rightarrow> 'f list) \<Rightarrow>
      (nat \<Rightarrow> 'f list \<Rightarrow> 'f list) \<Rightarrow>
      nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
where
  "trace_one_step_disagreement_bad_for pw layer claimed doms i prefix =
    fri_one_step_disagreement_challenges
      (trace_fri_canonical_layer_len i) (pw i)
      (layer i prefix) (claimed i prefix) (doms i prefix)"

definition composition_one_step_disagreement_bad_for
  :: "('f \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
      ('f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list) \<Rightarrow>
      ('f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list) \<Rightarrow>
      ('f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list) \<Rightarrow>
      'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
where
  "composition_one_step_disagreement_bad_for pw layer claimed doms dg i prefix =
    fri_one_step_disagreement_challenges
      (composition_fri_canonical_layer_len dg i) (pw dg i)
      (layer dg i prefix) (claimed dg i prefix) (doms dg i prefix)"

definition trace_one_step_sampled_error_for
where
  "trace_one_step_sampled_error_for budgets empty_bad =
    concrete_trace_fri_bad_challenge_fraction +
      hash_relation_budget_value
        trace_one_step_challenge_hash_count
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      nnreal (staged_attacker_query_budget budgets +
        staged_challenge_query_budget) *
        trace_one_step_query_fraction_for empty_bad"

definition trace_empty_one_step_error_for
where
  "trace_empty_one_step_error_for budgets A empty_bad =
    trace_one_step_sampled_error_for budgets empty_bad +
      trace_fri_empty_small_conflict_zero_error_for budgets A"

definition trace_header_one_step_error_for
where
  "trace_header_one_step_error_for budgets A trace_bad =
    trace_one_step_sampled_error_for budgets trace_bad +
      trace_fri_header_replay_conflict_zero_error_for budgets A"

definition trace_one_step_split_pw :: "nat \<Rightarrow> nat"
where
  "trace_one_step_split_pw _ = 0"

definition trace_one_step_split_layer
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list"
where
  "trace_one_step_split_layer i _ =
    replicate (trace_fri_canonical_layer_len i) 0"

definition trace_one_step_split_claimed
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list"
where
  "trace_one_step_split_claimed i _ =
    replicate (trace_fri_canonical_layer_len i) 1"

definition trace_one_step_split_domain
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list"
where
  "trace_one_step_split_domain i _ =
    replicate (trace_fri_canonical_layer_len i) 1"

definition trace_one_step_split_bad
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
where
  "trace_one_step_split_bad =
    trace_one_step_disagreement_bad_for
      trace_one_step_split_pw trace_one_step_split_layer
      trace_one_step_split_claimed trace_one_step_split_domain"

definition composition_one_step_split_pw
  :: "'f \<Rightarrow> nat \<Rightarrow> nat"
where
  "composition_one_step_split_pw _ _ = 0"

definition composition_one_step_split_layer
  :: "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list"
where
  "composition_one_step_split_layer dg i _ =
    replicate (composition_fri_canonical_layer_len dg i) 0"

definition composition_one_step_split_claimed
  :: "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list"
where
  "composition_one_step_split_claimed dg i _ =
    replicate (composition_fri_canonical_layer_len dg i) 1"

definition composition_one_step_split_domain
  :: "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list"
where
  "composition_one_step_split_domain dg i _ =
    replicate (composition_fri_canonical_layer_len dg i) 1"

definition composition_one_step_split_bad
  :: "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
where
  "composition_one_step_split_bad =
    composition_one_step_disagreement_bad_for
      composition_one_step_split_pw composition_one_step_split_layer
      composition_one_step_split_claimed composition_one_step_split_domain"

definition concrete_trace_header_one_step_error_for
where
  "concrete_trace_header_one_step_error_for budgets A =
    trace_header_one_step_error_for budgets A
      trace_one_step_split_bad"

definition concrete_composition_one_step_error_for
where
  "concrete_composition_one_step_error_for budgets A =
    composition_one_step_verifier_tied_controlled_error_for budgets
      composition_one_step_split_bad"

definition concrete_trace_empty_one_step_error_for
where
  "concrete_trace_empty_one_step_error_for budgets A =
    trace_empty_one_step_error_for budgets A
      trace_one_step_split_bad"

lemma sharpened_trace_fri_full_cover_domain_error_for_eq:
  "sharpened_trace_fri_full_cover_domain_error_for budgets A =
    concrete_trace_fri_full_cover_domain_error_for budgets A"
  by (simp add:
      sharpened_trace_fri_full_cover_domain_error_for_def
      trace_fri_challenge_prequery_error_for_def
      trace_fri_full_cover_domain_residual_error_for_def
      concrete_trace_fri_full_cover_domain_error_for_def)

lemma sharpened_trace_fri_header_error_for_eq:
  "sharpened_trace_fri_header_error_for budgets A =
    concrete_trace_fri_header_error_for' budgets A"
  by (simp add:
      sharpened_trace_fri_header_error_for_def
      sharpened_trace_fri_full_cover_domain_error_for_eq
      trace_fri_header_conflict_zero_error_for_def
      concrete_trace_fri_header_error_for'_def)

lemma sharpened_trace_fri_empty_error_for_eq:
  "sharpened_trace_fri_empty_error_for budgets A =
    concrete_trace_fri_empty_error_for' budgets A"
  by (simp add:
      sharpened_trace_fri_empty_error_for_def
      sharpened_trace_fri_full_cover_domain_error_for_eq
      trace_fri_empty_conflict_zero_error_for_def
      concrete_trace_fri_empty_error_for'_def)

lemma sharpened_composition_fri_full_cover_domain_error_for_eq:
  "sharpened_composition_fri_full_cover_domain_error_for budgets A =
    concrete_composition_fri_full_cover_domain_error_for budgets A"
  by (simp add:
      sharpened_composition_fri_full_cover_domain_error_for_def
      composition_fri_challenge_prequery_error_for_def
      composition_fri_full_cover_domain_residual_error_for_def
      concrete_composition_fri_full_cover_domain_error_for_def)

lemma sharpened_composition_fri_error_for_eq:
  "sharpened_composition_fri_error_for budgets A =
    concrete_composition_fri_error_for' budgets A"
  by (simp add:
      sharpened_composition_fri_error_for_def
      sharpened_composition_fri_full_cover_domain_error_for_eq
      composition_fri_conflict_zero_error_for_def
      concrete_composition_fri_error_for'_def)

lemma sharpened_trace_fri_header_error_for_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> sharpened_trace_fri_header_error_for budgets A"
  using concrete_trace_fri_header_error_for'_bound[OF wf controlled]
  by (simp add: sharpened_trace_fri_header_error_for_eq)

lemma sharpened_trace_fri_empty_error_for_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> sharpened_trace_fri_empty_error_for budgets A"
  using concrete_trace_fri_empty_error_for'_bound[OF wf controlled]
  by (simp add: sharpened_trace_fri_empty_error_for_eq)

lemma sharpened_composition_fri_error_for_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> sharpened_composition_fri_error_for budgets A"
  using concrete_composition_fri_error_for'_bound[OF wf controlled]
  by (simp add: sharpened_composition_fri_error_for_eq)

lemma composition_one_step_sampled_error_for_bound:
  fixes comp_bad :: "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and comp_subset:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        comp_bad dg i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (composition_fri_canonical_layer_len dg i) (comp_pw dg i)
            (comp_layer dg i prefix) (comp_claimed dg i prefix)
            (comp_dom dg i prefix)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> composition_one_step_sampled_error_for budgets comp_bad"
proof -
  let ?B =
    "\<lambda>dg. generic_fri_bad_challenge_lists
      (fri_round_count_for_degree_bound (to_nat dg)) (comp_bad dg)"
  let ?Q = "composition_one_step_query_fraction_for comp_bad"
  have round_bound:
    "\<And>dg i prefix.
      i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
      length prefix = i \<Longrightarrow>
      card (comp_bad dg i prefix)
        \<le> composition_fri_canonical_layer_len dg i div 2"
  proof -
    fix dg i and prefix :: "'f list"
    assume i: "i < fri_round_count_for_degree_bound (to_nat dg)"
      and prefix_len: "length prefix = i"
    have "card (comp_bad dg i prefix) \<le>
        card
          (fri_one_step_disagreement_challenges
            (composition_fri_canonical_layer_len dg i) (comp_pw dg i)
            (comp_layer dg i prefix) (comp_claimed dg i prefix)
            (comp_dom dg i prefix))"
      by (rule card_mono) (simp_all add: comp_subset[OF i prefix_len])
    also have "... \<le> composition_fri_canonical_layer_len dg i div 2"
      by (rule fri_one_step_disagreement_challenges_card_bound_local)
    finally show "card (comp_bad dg i prefix)
      \<le> composition_fri_canonical_layer_len dg i div 2" .
  qed
  have fraction_bound:
    "\<And>dg. nnreal
        (\<Sum>i\<in>{..<fri_round_count_for_degree_bound (to_nat dg)}.
          CARD('f) ^ i *
            (composition_fri_canonical_layer_len dg i div 2) *
            CARD('f) ^
              (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
      \<le> concrete_composition_fri_bad_challenge_fraction"
  proof -
    fix dg
    show "nnreal
        (\<Sum>i\<in>{..<fri_round_count_for_degree_bound (to_nat dg)}.
          CARD('f) ^ i *
            (composition_fri_canonical_layer_len dg i div 2) *
            CARD('f) ^
              (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
      \<le> concrete_composition_fri_bad_challenge_fraction"
      using concrete_composition_fri_bad_challenge_fraction_ge[of dg]
      by (simp add: fri_one_step_disagreement_round_fraction_def
        fri_bad_challenge_round_fraction_def
        fri_one_step_disagreement_round_mass_def
        fri_bad_challenge_round_mass_def)
  qed
  have fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s ?B))
      adversary_initial_state
      \<le> concrete_composition_fri_bad_challenge_fraction"
    by (rule
        checked_staged_security_composition_fri_bad_challenge_list_fresh_hit_bound_from_round_bounds
        [OF round_bound fraction_bound])
  have fiber_fraction:
    "nnreal
      ((\<Sum>dg\<in>UNIV.
        \<Sum>challenges\<in>
          fri_challenge_space (fri_round_count_for_degree_bound (to_nat dg)) -
            ?B dg.
          card
            (generic_fri_sampled_query_query_fiber
              (composition_table_low_degree (to_nat dg))
              (Not \<circ> composition_table_low_degree maxDegree)
              (to_nat dg) challenges)) *
        rounds) /
      nnreal (card query_sample_space) \<le> ?Q"
    by (simp add: composition_one_step_query_fraction_for_def)
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state
      \<le>
      concrete_composition_fri_bad_challenge_fraction +
      hash_relation_budget_value
        (\<Sum>dg\<in>UNIV. card (?B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * ?Q"
    by (rule
        checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fiber_card
        [OF wf controlled finite_generic_fri_bad_challenge_lists
          fresh_bound fiber_fraction])
  have card_le:
    "(\<Sum>dg\<in>UNIV. card (?B dg) * ceil_log (maxDegree + 1))
      \<le> composition_one_step_challenge_hash_count"
  proof (unfold composition_one_step_challenge_hash_count_def, rule sum_mono)
    fix dg :: 'f
    have raw:
      "card (?B dg) \<le>
        (\<Sum>i\<in>{..<fri_round_count_for_degree_bound (to_nat dg)}.
          CARD('f) ^ i *
            (composition_fri_canonical_layer_len dg i div 2) *
            CARD('f) ^
              (fri_round_count_for_degree_bound (to_nat dg) - Suc i))"
    proof (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds)
      fix i :: nat and prefix :: "'f list"
      assume i: "i < fri_round_count_for_degree_bound (to_nat dg)"
        and prefix_len: "length prefix = i"
      show "card (comp_bad dg i prefix)
        \<le> composition_fri_canonical_layer_len dg i div 2"
        by (rule round_bound[OF i prefix_len])
    qed
    have "card (?B dg) \<le>
        fri_one_step_disagreement_round_mass
          (fri_round_count_for_degree_bound (to_nat dg))
          (composition_fri_canonical_layer_len dg)"
      using raw
      by (simp add: fri_one_step_disagreement_round_mass_def
        fri_bad_challenge_round_mass_def)
    then show "card (?B dg) * ceil_log (maxDegree + 1)
      \<le> fri_one_step_disagreement_round_mass
          (fri_round_count_for_degree_bound (to_nat dg))
          (composition_fri_canonical_layer_len dg) *
        ceil_log (maxDegree + 1)"
      by (rule mult_right_mono) simp
  qed
  have budget_le:
    "hash_relation_budget_value
      (\<Sum>dg\<in>UNIV. card (?B dg) * ceil_log (maxDegree + 1))
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget)
      \<le>
      hash_relation_budget_value
        composition_one_step_challenge_hash_count
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule hash_relation_budget_value_mono_left[OF card_le])
  show ?thesis
    by (rule order_trans[OF sampled])
      (use budget_le in
        \<open>simp add: composition_one_step_sampled_error_for_def\<close>)
qed

lemma trace_one_step_sampled_error_for_bound:
  fixes empty_bad :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and empty_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        empty_bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (trace_fri_canonical_layer_len i) (empty_pw i)
            (empty_layer i prefix) (empty_claimed i prefix)
            (empty_dom i prefix)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> trace_one_step_sampled_error_for budgets empty_bad"
proof -
  let ?B =
    "generic_fri_bad_challenge_lists
      (fri_round_count_for_degree_bound (clength - 1)) empty_bad"
  let ?Q = "trace_one_step_query_fraction_for empty_bad"
  have round_bound:
    "\<And>i prefix.
      i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
      length prefix = i \<Longrightarrow>
      card (empty_bad i prefix) \<le> trace_fri_canonical_layer_len i div 2"
  proof -
    fix i :: nat and prefix :: "'f list"
    assume i: "i < fri_round_count_for_degree_bound (clength - 1)"
      and prefix_len: "length prefix = i"
    have "card (empty_bad i prefix) \<le>
        card
          (fri_one_step_disagreement_challenges
            (trace_fri_canonical_layer_len i) (empty_pw i)
            (empty_layer i prefix) (empty_claimed i prefix)
            (empty_dom i prefix))"
      by (rule card_mono) (simp_all add: empty_subset[OF i prefix_len])
    also have "... \<le> trace_fri_canonical_layer_len i div 2"
      by (rule fri_one_step_disagreement_challenges_card_bound_local)
    finally show "card (empty_bad i prefix)
      \<le> trace_fri_canonical_layer_len i div 2" .
  qed
  have fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s ?B))
      adversary_initial_state
      \<le> concrete_trace_fri_bad_challenge_fraction"
  proof -
    have base:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_fresh_hit s ?B))
        adversary_initial_state
        \<le> nnreal
          (\<Sum>i\<in>{..<fri_round_count_for_degree_bound (clength - 1)}.
            CARD('f) ^ i * (trace_fri_canonical_layer_len i div 2) *
              CARD('f) ^
                (fri_round_count_for_degree_bound (clength - 1) - Suc i)) /
          nnreal (CARD('f) ^ fri_round_count_for_degree_bound (clength - 1))"
      by (rule
          checked_staged_security_trace_fri_bad_challenge_list_fresh_hit_bound_from_round_bounds
          [OF round_bound])
    show ?thesis
      by (rule order_trans[OF base])
        (simp add: concrete_trace_fri_bad_challenge_fraction_def
          fri_one_step_disagreement_round_fraction_def
          fri_bad_challenge_round_fraction_def
          fri_one_step_disagreement_round_mass_def
          fri_bad_challenge_round_mass_def)
  qed
  have fiber_fraction:
    "nnreal
      ((\<Sum>challenges\<in>
        fri_challenge_space (fri_round_count_for_degree_bound (clength - 1)) -
          ?B.
        card
          (generic_fri_sampled_query_query_fiber trace_table_low_degree
            (Not \<circ> trace_table_low_degree) (clength - 1) challenges)) *
        rounds) /
      nnreal (card query_sample_space) \<le> ?Q"
    by (simp add: trace_one_step_query_fraction_for_def)
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state
      \<le>
      concrete_trace_fri_bad_challenge_fraction +
      hash_relation_budget_value (card ?B * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * ?Q"
    by (rule
        checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fiber_card
        [OF wf controlled finite_generic_fri_bad_challenge_lists
          fresh_bound fiber_fraction])
  have card_le:
    "card ?B * ceil_log clength \<le> trace_one_step_challenge_hash_count"
  proof -
    have raw:
      "card ?B \<le>
        (\<Sum>i\<in>{..<fri_round_count_for_degree_bound (clength - 1)}.
          CARD('f) ^ i * (trace_fri_canonical_layer_len i div 2) *
            CARD('f) ^
              (fri_round_count_for_degree_bound (clength - 1) - Suc i))"
    proof (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds)
      fix i :: nat and prefix :: "'f list"
      assume i: "i < fri_round_count_for_degree_bound (clength - 1)"
        and prefix_len: "length prefix = i"
      show "card (empty_bad i prefix)
        \<le> trace_fri_canonical_layer_len i div 2"
        by (rule round_bound[OF i prefix_len])
    qed
    have "card ?B \<le>
        fri_one_step_disagreement_round_mass
          (fri_round_count_for_degree_bound (clength - 1))
          trace_fri_canonical_layer_len"
      using raw
      by (simp add: fri_one_step_disagreement_round_mass_def
        fri_bad_challenge_round_mass_def)
    then show ?thesis
      unfolding trace_one_step_challenge_hash_count_def
      by (rule mult_right_mono) simp
  qed
  have budget_le:
    "hash_relation_budget_value (card ?B * ceil_log clength)
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget)
      \<le>
      hash_relation_budget_value trace_one_step_challenge_hash_count
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule hash_relation_budget_value_mono_left[OF card_le])
  show ?thesis
    by (rule order_trans[OF sampled])
      (use budget_le in \<open>simp add: trace_one_step_sampled_error_for_def\<close>)
qed

lemma checked_staged_security_trace_fri_empty_header_bound_from_staged_sampled_conflict_and_zero:
  assumes sampled_query:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> R"
    and conflict_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_assignment_conflict)
      adversary_initial_state \<le> C"
    and zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> R + (C + Z)"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?sampled =
    "staged_security_with_data_state_verifier_event
      trace_fri_bad_with_sampled_layer_chain"
  let ?missing =
    "staged_security_with_data_state_verifier_event
      trace_fri_reachable_missing_sampled_layer_chain"
  let ?conflict =
    "staged_security_with_data_state_verifier_event
      trace_fri_sampled_assignment_conflict"
  let ?zero =
    "staged_security_with_data_state_verifier_event
      trace_fri_zero_round_final_obstruction"
  have sampled:
    "wp_event ?M ?sampled adversary_initial_state \<le> R"
    by (rule
        checked_staged_security_trace_fri_sampled_layer_chain_bound_from_sampled_query
        [OF sampled_query])
  have missing_split:
    "wp_event ?M ?missing adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?conflict out \<or> ?zero out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and missing: "?missing out"
    show "?conflict out \<or> ?zero out"
    proof (cases out)
      case None
      then show ?thesis
        using missing unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some out_data)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases out_data, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from checked_staged_security_experiment_with_data_state_outcomeE
          [OF support[unfolded out_eq]]
      have verify_support:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        by blast
      have missing_local:
        "trace_fri_reachable_missing_sampled_layer_chain ?s
          (Some (result, final_state))"
        using missing unfolding out_eq
          staged_security_with_data_state_verifier_event_def
        by simp
      have obstruction:
        "trace_fri_sampled_layer_assignment_obstruction ?s
          (Some (result, final_state))"
        by (rule
            trace_fri_reachable_missing_sampled_imp_assignment_obstruction_on_support
            [OF verify_support missing_local])
      then have
        "trace_fri_sampled_assignment_conflict ?s
          (Some (result, final_state)) \<or>
         trace_fri_zero_round_final_obstruction ?s
          (Some (result, final_state))"
        by (rule
            trace_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final)
      then show ?thesis
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
    qed
  qed
  have missing_bound:
    "wp_event ?M ?missing adversary_initial_state \<le> C + Z"
  proof -
    have "wp_event ?M ?missing adversary_initial_state \<le>
        wp_event ?M (\<lambda>out. ?conflict out \<or> ?zero out)
          adversary_initial_state"
      by (rule missing_split)
    also have "... \<le>
        wp_event ?M ?conflict adversary_initial_state +
        wp_event ?M ?zero adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le> C + Z"
      by (rule add_mono[OF conflict_bound zero_bound])
    finally show ?thesis .
  qed
  have split:
    "wp_event ?M
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?sampled out \<or> ?missing out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest:
          trace_fri_bad_with_empty_composition_header_candidates_imp_reachable_partial_candidate
          trace_fri_reachable_imp_sampled_or_missing_layer_chain
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?sampled adversary_initial_state +
      wp_event ?M ?missing adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> R + (C + Z)"
    by (rule add_mono[OF sampled missing_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_header_tied_candidate_transfer_gap_bound_from_staged_header_and_untied:
  fixes H U :: prob
  assumes header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> H"
    and untied_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_reachable_witness_gap)
      adversary_initial_state \<le> U"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_candidate_transfer_gap)
      adversary_initial_state \<le> H + U"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?header =
    "staged_security_with_data_state_verifier_event
      trace_fri_bad_with_header_tied_partial_candidate"
  let ?untied =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_untied_reachable_witness_gap"
  have "wp_event ?M
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_candidate_transfer_gap)
      adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?header out \<or> ?untied out)
        adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto dest:
        trace_fri_header_tied_candidate_transfer_gap_imp_header_or_untied
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?header adversary_initial_state +
      wp_event ?M ?untied adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> H + U"
    by (rule add_mono[OF header_bound untied_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_staged_checked_merkle_transfer_header:
  fixes H M Q T :: prob
  assumes checked_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le> Q"
    and merkle_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le> M"
    and transfer_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_candidate_transfer_gap)
      adversary_initial_state \<le> T"
    and header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> H"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state \<le> Q + M + T + H"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?checked =
    "staged_security_with_data_state_verifier_event
      trace_fri_zero_round_checked_final_obstruction"
  let ?merkle =
    "staged_security_with_data_state_verifier_event
      partial_merkle_inconsistency_bad"
  let ?transfer =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_candidate_transfer_gap"
  let ?header =
    "staged_security_with_data_state_verifier_event
      trace_fri_bad_with_header_tied_partial_candidate"
  have "wp_event ?M
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out.
          ?checked out \<or> ?merkle out \<or> ?transfer out \<or> ?header out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and obstruction:
      "staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction out"
    show "?checked out \<or> ?merkle out \<or> ?transfer out \<or> ?header out"
    proof (cases out)
      case None
      then show ?thesis
        using obstruction
        unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some out_data)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases out_data, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from checked_staged_security_experiment_with_data_state_outcomeE
          [OF support[unfolded out_eq]]
      have verify_support:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        by blast
      have obstruction_local:
        "trace_fri_zero_round_final_obstruction ?s
          (Some (result, final_state))"
        using obstruction
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
      have
        "trace_fri_zero_round_checked_final_obstruction ?s
          (Some (result, final_state)) \<or>
         partial_merkle_inconsistency_bad ?s
          (Some (result, final_state)) \<or>
         trace_fri_header_tied_candidate_transfer_gap ?s
          (Some (result, final_state)) \<or>
         trace_fri_bad_with_header_tied_partial_candidate ?s
          (Some (result, final_state))"
        by (rule
            trace_fri_zero_round_final_obstruction_imp_checked_merkle_transfer_or_header
            [OF verify_support obstruction_local])
      then show ?thesis
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
    qed
  qed
  also have "... \<le>
      wp_event ?M ?checked adversary_initial_state +
      wp_event ?M ?merkle adversary_initial_state +
      wp_event ?M ?transfer adversary_initial_state +
      wp_event ?M ?header adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le> Q + M + T + H"
    by (intro add_mono checked_bound merkle_bound transfer_bound
        header_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_zero_round_checked_final_obstruction_bound_from_agreement_sets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets"
proof -
  have event_le:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_query_list_target_hit)
      adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto
        intro:
          trace_fri_zero_round_checked_first_query_target_hit_imp_query_list_target
        dest:
          trace_fri_zero_round_checked_final_obstruction_imp_first_query_target_hit
        split: option.splits prod.splits)
  show ?thesis
    by (rule order_trans[OF event_le])
      (rule checked_staged_security_trace_fri_zero_round_query_list_target_bound_from_agreement_sets
        [OF wf controlled])
qed

lemma checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_agreement_sets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets +
      trace_fri_controlled_merkle_error_for budgets +
      reachable_verifier_event_bound_for A
        trace_fri_bad_with_header_tied_partial_candidate +
      (trace_fri_controlled_merkle_error_for budgets +
       (reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_root_gap +
        reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_query_gap)) +
      reachable_verifier_event_bound_for A
        trace_fri_bad_with_header_tied_partial_candidate"
proof -
  have checked:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets"
    by (rule checked_staged_security_trace_fri_zero_round_checked_final_obstruction_bound_from_agreement_sets
        [OF wf controlled])
  have merkle:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets"
    unfolding trace_fri_controlled_merkle_error_for_def
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
  have header:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_bad_with_header_tied_partial_candidate"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    show "\<And>s. \<not> trace_fri_bad_with_header_tied_partial_candidate s None"
      unfolding trace_fri_bad_with_header_tied_partial_candidate_def
        accepted_fri_opening_transcript_def
      by simp
  next
    fix data attacker_state
    assume support: "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        trace_fri_bad_with_header_tied_partial_candidate"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  qed
  have hash:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets"
    unfolding trace_fri_controlled_merkle_error_for_def
    by (rule
        checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  have root:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_root_gap)
      adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_root_gap"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    show "\<And>s. \<not> trace_fri_header_tied_low_candidate_untied_root_gap s None"
      unfolding trace_fri_header_tied_low_candidate_untied_root_gap_def
        trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
        accepted_fri_opening_transcript_def
      by simp
  next
    fix data attacker_state
    assume support: "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_root_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_root_gap"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  qed
  have query:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_query_gap)
      adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_query_gap"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    show "\<And>s. \<not> trace_fri_header_tied_low_candidate_untied_query_gap s None"
      unfolding trace_fri_header_tied_low_candidate_untied_query_gap_def
        trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
        accepted_fri_opening_transcript_def
      by simp
  next
    fix data attacker_state
    assume support: "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_query_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_query_gap"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  qed
  have untied:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_reachable_witness_gap)
      adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets +
      (reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_root_gap +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_query_gap)"
  proof -
    let ?M = "checked_staged_security_experiment_with_data_state A"
    let ?untied =
      "staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_reachable_witness_gap"
    let ?hash =
      "staged_security_with_data_state_verifier_event
        hash_map_output_collision_bad"
    let ?root =
      "staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_root_gap"
    let ?query =
      "staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_query_gap"
    have split:
      "wp_event ?M ?untied adversary_initial_state \<le>
        wp_event ?M (\<lambda>out. ?hash out \<or> ?root out \<or> ?query out)
          adversary_initial_state"
      unfolding staged_security_with_data_state_verifier_event_def
      by (rule wp_event_mono_on_support)
        (auto
          dest:
            trace_fri_header_tied_low_candidate_untied_gap_imp_hash_root_or_query
          split: option.splits prod.splits)
    also have "... \<le>
        wp_event ?M ?hash adversary_initial_state +
        wp_event ?M (\<lambda>out. ?root out \<or> ?query out)
          adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?hash adversary_initial_state +
        (wp_event ?M ?root adversary_initial_state +
         wp_event ?M ?query adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        trace_fri_controlled_merkle_error_for budgets +
        (reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_root_gap +
         reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_query_gap)"
      by (intro add_mono hash root query)
    finally show ?thesis .
  qed
  have transfer:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_candidate_transfer_gap)
      adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_bad_with_header_tied_partial_candidate +
      (trace_fri_controlled_merkle_error_for budgets +
       (reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_root_gap +
        reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_query_gap))"
    by (rule
        checked_staged_security_trace_fri_header_tied_candidate_transfer_gap_bound_from_staged_header_and_untied
        [OF header untied])
  have raw:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets +
      trace_fri_controlled_merkle_error_for budgets +
      (reachable_verifier_event_bound_for A
        trace_fri_bad_with_header_tied_partial_candidate +
       (trace_fri_controlled_merkle_error_for budgets +
        (reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_root_gap +
         reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_query_gap))) +
      reachable_verifier_event_bound_for A
        trace_fri_bad_with_header_tied_partial_candidate"
    by (rule
        checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_staged_checked_merkle_transfer_header
        [OF checked merkle transfer header])
  show ?thesis
    by (rule order_trans[OF raw]) (simp add: algebra_simps)
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_staged_sampled_conflict_and_zero:
  assumes sampled_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state \<le> R"
    and conflict_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_sampled_assignment_conflict)
      adversary_initial_state \<le> C"
    and zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> R + (C + Z)"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?sampled =
    "staged_security_with_data_state_verifier_event
      composition_fri_bad_with_verifier_tied_sampled_layer_chain"
  let ?missing =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_missing_sampled_layer_chain"
  let ?conflict =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_sampled_assignment_conflict"
  let ?zero =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_zero_round_final_obstruction"
  have missing_split:
    "wp_event ?M ?missing adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?conflict out \<or> ?zero out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and missing: "?missing out"
    show "?conflict out \<or> ?zero out"
    proof (cases out)
      case None
      then show ?thesis
        using missing unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some out_data)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases out_data, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from checked_staged_security_experiment_with_data_state_outcomeE
          [OF support[unfolded out_eq]]
      have verify_support:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        by blast
      have missing_local:
        "composition_fri_verifier_tied_missing_sampled_layer_chain ?s
          (Some (result, final_state))"
        using missing unfolding out_eq
          staged_security_with_data_state_verifier_event_def
        by simp
      have obstruction:
        "composition_fri_verifier_tied_sampled_layer_assignment_obstruction
          ?s (Some (result, final_state))"
        by (rule
            composition_fri_verifier_tied_missing_sampled_imp_assignment_obstruction
            [OF missing_local])
      then have
        "composition_fri_verifier_tied_sampled_assignment_conflict ?s
          (Some (result, final_state)) \<or>
         composition_fri_verifier_tied_zero_round_final_obstruction ?s
          (Some (result, final_state))"
        by (rule
            composition_fri_verifier_tied_assignment_obstruction_imp_conflict_or_zero_on_support
            [OF verify_support])
      then show ?thesis
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
    qed
  qed
  have missing_bound:
    "wp_event ?M ?missing adversary_initial_state \<le> C + Z"
  proof -
    have "wp_event ?M ?missing adversary_initial_state \<le>
        wp_event ?M (\<lambda>out. ?conflict out \<or> ?zero out)
          adversary_initial_state"
      by (rule missing_split)
    also have "... \<le>
        wp_event ?M ?conflict adversary_initial_state +
        wp_event ?M ?zero adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le> C + Z"
      by (rule add_mono[OF conflict_bound zero_bound])
    finally show ?thesis .
  qed
  have split:
    "wp_event ?M
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?sampled out \<or> ?missing out)
        adversary_initial_state"
    unfolding composition_fri_verifier_tied_missing_sampled_layer_chain_def
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?sampled adversary_initial_state +
      wp_event ?M ?missing adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> R + (C + Z)"
    by (rule add_mono[OF sampled_bound missing_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_partial_merkle_inconsistency_bad_bound_by_composition_one_step_controlled_merkle_error:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      composition_one_step_controlled_merkle_error_for budgets"
  unfolding composition_one_step_controlled_merkle_error_for_def
  by (rule
      checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
      [OF wf controlled])

lemma checked_staged_security_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero:
  "wp_event (checked_staged_security_experiment_with_data_state A)
    (staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap)
    adversary_initial_state \<le> (0::prob)"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not>
    composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s None"
    unfolding
      composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_def
    by simp
next
  fix data attacker_state
  assume "Some (data, attacker_state) \<in>
    set_dist
      (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
    (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)))
    (verifier_state_from_adversary attacker_state
      (staged_proof_transcript data))
    \<le> 0"
    by (rule
        wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
qed

lemma checked_staged_security_composition_fri_verifier_tied_next_value_replay_gap_bound_by_controlled_merkle:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_next_value_replay_gap)
      adversary_initial_state \<le>
      composition_one_step_controlled_merkle_error_for budgets + 0"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?merkle =
    "staged_security_with_data_state_verifier_event
      partial_merkle_inconsistency_bad"
  let ?slot =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap"
  have split:
    "wp_event ?M
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_next_value_replay_gap)
      adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?merkle out \<or> ?slot out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and gap:
      "staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_next_value_replay_gap out"
    show "?merkle out \<or> ?slot out"
    proof (cases out)
      case None
      then show ?thesis
        using gap unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some out_data)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases out_data, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from checked_staged_security_experiment_with_data_state_outcomeE
          [OF support[unfolded out_eq]]
      have verify_support:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        by blast
      have gap_local:
        "composition_fri_verifier_tied_next_value_replay_gap ?s
          (Some (result, final_state))"
        using gap unfolding out_eq
          staged_security_with_data_state_verifier_event_def
        by simp
      have
        "partial_merkle_inconsistency_bad ?s
          (Some (result, final_state)) \<or>
         composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          ?s (Some (result, final_state))"
        by (rule
            composition_fri_verifier_tied_next_value_replay_gap_imp_merkle_or_slot_on_support
            [OF verify_support gap_local])
      then show ?thesis
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
    qed
  qed
  also have "... \<le>
      wp_event ?M ?merkle adversary_initial_state +
      wp_event ?M ?slot adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      composition_one_step_controlled_merkle_error_for budgets + 0"
    by (intro add_mono
        checked_staged_security_partial_merkle_inconsistency_bad_bound_by_composition_one_step_controlled_merkle_error
        [OF wf controlled]
        checked_staged_security_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_verifier_tied_successor_replay_gap_bound_by_controlled_merkle:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_successor_replay_gap)
      adversary_initial_state \<le>
      composition_one_step_controlled_merkle_error_for budgets + 0"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?merkle =
    "staged_security_with_data_state_verifier_event
      partial_merkle_inconsistency_bad"
  let ?slot =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap"
  have split:
    "wp_event ?M
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_successor_replay_gap)
      adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?merkle out \<or> ?slot out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and gap:
      "staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_successor_replay_gap out"
    show "?merkle out \<or> ?slot out"
    proof (cases out)
      case None
      then show ?thesis
        using gap unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some out_data)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases out_data, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from checked_staged_security_experiment_with_data_state_outcomeE
          [OF support[unfolded out_eq]]
      have verify_support:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        by blast
      have gap_local:
        "composition_fri_verifier_tied_successor_replay_gap ?s
          (Some (result, final_state))"
        using gap unfolding out_eq
          staged_security_with_data_state_verifier_event_def
        by simp
      have
        "partial_merkle_inconsistency_bad ?s
          (Some (result, final_state)) \<or>
         composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          ?s (Some (result, final_state))"
        by (rule
            composition_fri_verifier_tied_successor_replay_gap_imp_merkle_or_slot_on_support
            [OF verify_support gap_local])
      then show ?thesis
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
    qed
  qed
  also have "... \<le>
      wp_event ?M ?merkle adversary_initial_state +
      wp_event ?M ?slot adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      composition_one_step_controlled_merkle_error_for budgets + 0"
    by (intro add_mono
        checked_staged_security_partial_merkle_inconsistency_bad_bound_by_composition_one_step_controlled_merkle_error
        [OF wf controlled]
        checked_staged_security_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_verifier_tied_final_value_selected_step_missing_gap_zero:
  "wp_event (checked_staged_security_experiment_with_data_state A)
    (staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_final_value_selected_step_missing_gap)
    adversary_initial_state \<le> (0::prob)"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not>
    composition_fri_verifier_tied_final_value_selected_step_missing_gap s None"
    unfolding
      composition_fri_verifier_tied_final_value_selected_step_missing_gap_def
      composition_fri_verifier_tied_final_value_authenticated_replay_gap_def
      accepted_fri_opening_transcript_def
    by simp
next
  fix data attacker_state
  assume "Some (data, attacker_state) \<in>
    set_dist
      (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
    (composition_fri_verifier_tied_final_value_selected_step_missing_gap
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)))
    (verifier_state_from_adversary attacker_state
      (staged_proof_transcript data))
    \<le> 0"
    by (rule
        wp_composition_fri_verifier_tied_final_value_selected_step_missing_gap_zero)
qed

lemma checked_staged_security_composition_fri_verifier_tied_final_value_replay_gap_bound_by_controlled_merkle:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_final_value_replay_gap)
      adversary_initial_state \<le>
      composition_one_step_controlled_merkle_error_for budgets + 0 + 0"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?merkle =
    "staged_security_with_data_state_verifier_event
      partial_merkle_inconsistency_bad"
  let ?slot =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap"
  let ?selected =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_final_value_selected_step_missing_gap"
  have split:
    "wp_event ?M
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_final_value_replay_gap)
      adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?merkle out \<or> ?slot out \<or> ?selected out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and gap:
      "staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_final_value_replay_gap out"
    show "?merkle out \<or> ?slot out \<or> ?selected out"
    proof (cases out)
      case None
      then show ?thesis
        using gap unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some out_data)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases out_data, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from checked_staged_security_experiment_with_data_state_outcomeE
          [OF support[unfolded out_eq]]
      have verify_support:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        by blast
      have gap_local:
        "composition_fri_verifier_tied_final_value_replay_gap ?s
          (Some (result, final_state))"
        using gap unfolding out_eq
          staged_security_with_data_state_verifier_event_def
        by simp
      have
        "partial_merkle_inconsistency_bad ?s
          (Some (result, final_state)) \<or>
         composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          ?s (Some (result, final_state)) \<or>
         composition_fri_verifier_tied_final_value_authenticated_replay_gap
          ?s (Some (result, final_state))"
        by (rule
            composition_fri_verifier_tied_final_value_replay_gap_imp_merkle_or_slot_or_authenticated_on_support
            [OF verify_support gap_local])
      then show ?thesis
      proof
        assume "partial_merkle_inconsistency_bad ?s
          (Some (result, final_state))"
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          by simp
      next
        assume tail:
          "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
            ?s (Some (result, final_state)) \<or>
           composition_fri_verifier_tied_final_value_authenticated_replay_gap
            ?s (Some (result, final_state))"
        then show ?thesis
        proof
          assume
            "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
              ?s (Some (result, final_state))"
          then show ?thesis
            unfolding out_eq staged_security_with_data_state_verifier_event_def
            by simp
        next
          assume auth:
            "composition_fri_verifier_tied_final_value_authenticated_replay_gap
              ?s (Some (result, final_state))"
          have selected:
            "composition_fri_verifier_tied_final_value_selected_step_missing_gap
              ?s (Some (result, final_state))"
            by (rule
                composition_fri_verifier_tied_final_value_authenticated_replay_gap_imp_selected_step_missing
                [OF auth])
          then show ?thesis
            unfolding out_eq staged_security_with_data_state_verifier_event_def
            by simp
        qed
      qed
    qed
  qed
  also have "... \<le>
      wp_event ?M ?merkle adversary_initial_state +
      wp_event ?M ?slot adversary_initial_state +
      wp_event ?M ?selected adversary_initial_state"
  proof -
    have "wp_event ?M
        (\<lambda>out. ?merkle out \<or> ?slot out \<or> ?selected out)
        adversary_initial_state \<le>
        wp_event ?M ?merkle adversary_initial_state +
        wp_event ?M (\<lambda>out. ?slot out \<or> ?selected out)
          adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?merkle adversary_initial_state +
        (wp_event ?M ?slot adversary_initial_state +
         wp_event ?M ?selected adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  also have "... \<le>
      composition_one_step_controlled_merkle_error_for budgets + 0 + 0"
    by (intro add_mono
        checked_staged_security_partial_merkle_inconsistency_bad_bound_by_composition_one_step_controlled_merkle_error
        [OF wf controlled]
        checked_staged_security_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero
        checked_staged_security_composition_fri_verifier_tied_final_value_selected_step_missing_gap_zero)
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_zero:
  "wp_event (checked_staged_security_experiment_with_data_state A)
    (staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_recorded_base_chunk_auth_missing)
    adversary_initial_state \<le> (0::prob)"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not>
    composition_fri_verifier_tied_recorded_base_chunk_auth_missing s None"
    unfolding
      composition_fri_verifier_tied_recorded_base_chunk_auth_missing_def
      accepted_fri_opening_transcript_def
    by simp
next
  fix data attacker_state
  assume "Some (data, attacker_state) \<in>
    set_dist
      (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
    (composition_fri_verifier_tied_recorded_base_chunk_auth_missing
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)))
    (verifier_state_from_adversary attacker_state
      (staged_proof_transcript data))
    \<le> 0"
    by (rule
        wp_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_zero)
qed

lemma checked_staged_security_composition_fri_verifier_tied_sampled_assignment_conflict_bound_by_controlled_merkle:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_sampled_assignment_conflict)
      adversary_initial_state \<le>
      (((composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0 + 0) +
        composition_one_step_controlled_merkle_error_for budgets) + 0)"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?conflict =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_sampled_assignment_conflict"
  let ?merkle =
    "staged_security_with_data_state_verifier_event
      partial_merkle_inconsistency_bad"
  let ?slot =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap"
  let ?next =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_next_value_replay_gap"
  let ?successor =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_successor_replay_gap"
  let ?final =
    "staged_security_with_data_state_verifier_event
      composition_fri_verifier_tied_final_value_replay_gap"
	  have split:
	    "wp_event ?M ?conflict adversary_initial_state \<le>
	      wp_event ?M
	        (\<lambda>out.
	          ?merkle out \<or> ?slot out \<or> ?next out \<or>
          ?successor out \<or> ?final out \<or> ?merkle out \<or> ?slot out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and conflict: "?conflict out"
    show "?merkle out \<or> ?slot out \<or> ?next out \<or>
        ?successor out \<or> ?final out \<or> ?merkle out \<or> ?slot out"
    proof (cases out)
      case None
      then show ?thesis
        using conflict unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some out_data)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases out_data, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from checked_staged_security_experiment_with_data_state_outcomeE
          [OF support[unfolded out_eq]]
      have verify_support:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        by blast
      have conflict_local:
        "composition_fri_verifier_tied_sampled_assignment_conflict ?s
          (Some (result, final_state))"
        using conflict unfolding out_eq
          staged_security_with_data_state_verifier_event_def
        by simp
      have local_split:
        "partial_merkle_inconsistency_bad ?s
            (Some (result, final_state)) \<or>
         composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
            ?s (Some (result, final_state)) \<or>
         composition_fri_verifier_tied_next_value_replay_gap
            ?s (Some (result, final_state)) \<or>
         composition_fri_verifier_tied_successor_replay_gap
            ?s (Some (result, final_state)) \<or>
         composition_fri_verifier_tied_final_value_replay_gap
            ?s (Some (result, final_state)) \<or>
         partial_merkle_inconsistency_bad ?s
            (Some (result, final_state)) \<or>
         composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
            ?s (Some (result, final_state))"
      proof -
        have auth_or_gap:
          "composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
            ?s (Some (result, final_state)) \<or>
           composition_fri_verifier_tied_assignment_auth_gap
            ?s (Some (result, final_state))"
          by (rule
              composition_fri_verifier_tied_assignment_imp_authenticated_or_auth_gap
              [OF conflict_local])
        then show ?thesis
        proof
          assume auth:
            "composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
              ?s (Some (result, final_state))"
          have without_or_same:
            "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
              ?s (Some (result, final_state)) \<or>
             composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
              ?s (Some (result, final_state))"
            by (rule
                composition_fri_verifier_tied_authenticated_conflict_imp_without_same_or_same_layer
                [OF auth])
          then show ?thesis
          proof
            assume without:
              "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
                ?s (Some (result, final_state))"
            then have branches:
              "composition_fri_verifier_tied_sampled_base_opening_conflict
                  ?s (Some (result, final_state)) \<or>
               composition_fri_verifier_tied_sampled_next_value_conflict
                  ?s (Some (result, final_state)) \<or>
               composition_fri_verifier_tied_sampled_successor_opening_conflict
                  ?s (Some (result, final_state)) \<or>
               composition_fri_verifier_tied_sampled_final_value_conflict
                  ?s (Some (result, final_state))"
              using composition_fri_verifier_tied_without_same_iff_branches
              by blast
            then show ?thesis
            proof
              assume base:
                "composition_fri_verifier_tied_sampled_base_opening_conflict
                  ?s (Some (result, final_state))"
              have base_split:
                "composition_fri_verifier_tied_authenticated_base_opening_conflict
                  ?s (Some (result, final_state)) \<or>
                 composition_fri_verifier_tied_base_chunk_auth_gap
                  ?s (Some (result, final_state))"
                by (rule
                    composition_fri_verifier_tied_sampled_base_imp_authenticated_or_auth_gap
                    [OF base])
              then show ?thesis
              proof
                assume auth_base:
                  "composition_fri_verifier_tied_authenticated_base_opening_conflict
                    ?s (Some (result, final_state))"
                then have
                  "partial_merkle_inconsistency_bad ?s
                    (Some (result, final_state))"
                  by (rule
                      composition_fri_verifier_tied_authenticated_base_conflict_imp_partial_merkle)
                then show ?thesis by simp
              next
                assume gap:
                  "composition_fri_verifier_tied_base_chunk_auth_gap
                    ?s (Some (result, final_state))"
                then have missing:
                  "composition_fri_verifier_tied_recorded_base_chunk_auth_missing
                    ?s (Some (result, final_state))"
                  by (rule
                      composition_fri_verifier_tied_base_chunk_auth_gap_imp_recorded_missing)
                then have
                  "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
                    ?s (Some (result, final_state))"
                  by (rule
                      composition_fri_verifier_tied_recorded_base_chunk_auth_missing_imp_slot_recorded_chunk_gap)
                then show ?thesis by simp
              qed
            next
              assume rest:
                "composition_fri_verifier_tied_sampled_next_value_conflict
                    ?s (Some (result, final_state)) \<or>
                 composition_fri_verifier_tied_sampled_successor_opening_conflict
                    ?s (Some (result, final_state)) \<or>
                 composition_fri_verifier_tied_sampled_final_value_conflict
                    ?s (Some (result, final_state))"
              then show ?thesis
              proof
                assume next_conflict:
                  "composition_fri_verifier_tied_sampled_next_value_conflict
                    ?s (Some (result, final_state))"
                then have
                  "composition_fri_verifier_tied_next_value_replay_gap
                    ?s (Some (result, final_state))"
                  by (rule
                      composition_fri_verifier_tied_sampled_next_value_imp_replay_gap)
                then show ?thesis by simp
              next
                assume tail:
                  "composition_fri_verifier_tied_sampled_successor_opening_conflict
                      ?s (Some (result, final_state)) \<or>
                   composition_fri_verifier_tied_sampled_final_value_conflict
                      ?s (Some (result, final_state))"
                then show ?thesis
                proof
                  assume successor:
                    "composition_fri_verifier_tied_sampled_successor_opening_conflict
                      ?s (Some (result, final_state))"
                  then have
                    "composition_fri_verifier_tied_successor_replay_gap
                      ?s (Some (result, final_state))"
                    by (rule
                        composition_fri_verifier_tied_sampled_successor_imp_replay_gap)
                  then show ?thesis by simp
                next
                  assume final:
                    "composition_fri_verifier_tied_sampled_final_value_conflict
                      ?s (Some (result, final_state))"
                  then have
                    "composition_fri_verifier_tied_final_value_replay_gap
                      ?s (Some (result, final_state))"
                    by (rule
                        composition_fri_verifier_tied_sampled_final_value_imp_replay_gap)
                  then show ?thesis by simp
                qed
              qed
            qed
          next
            assume same:
              "composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
                ?s (Some (result, final_state))"
            then have
              "partial_merkle_inconsistency_bad ?s
                (Some (result, final_state))"
              by (rule
                  composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_imp_partial_merkle)
            then show ?thesis by simp
          qed
        next
          assume gap:
            "composition_fri_verifier_tied_assignment_auth_gap
              ?s (Some (result, final_state))"
          have same_gap:
            "composition_fri_verifier_tied_same_layer_auth_gap
              ?s (Some (result, final_state))"
            by (rule
                composition_fri_verifier_tied_assignment_auth_gap_imp_same_layer_auth_gap
                [OF gap])
          have recorded_gap:
            "composition_fri_verifier_tied_same_layer_recorded_auth_gap
              ?s (Some (result, final_state))"
            by (rule
                composition_fri_verifier_tied_same_layer_auth_gap_imp_recorded_auth_gap
                [OF same_gap])
          have authenticated_gap:
            "composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap
              ?s (Some (result, final_state))"
            by (rule
                composition_fri_verifier_tied_same_layer_recorded_auth_gap_imp_authenticated_recorded_auth_gap_on_support
                [OF verify_support recorded_gap])
          have
            "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
              ?s (Some (result, final_state))"
            by (rule
                composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap_imp_slot_recorded_chunk_gap
                [OF authenticated_gap])
          then show ?thesis by simp
        qed
      qed
      then show ?thesis
	        unfolding out_eq staged_security_with_data_state_verifier_event_def
	        by simp
	    qed
	  qed
	  have next_bound:
	    "wp_event ?M ?next adversary_initial_state \<le>
	      composition_one_step_controlled_merkle_error_for budgets"
	    using
	      checked_staged_security_composition_fri_verifier_tied_next_value_replay_gap_bound_by_controlled_merkle
	      [OF wf controlled]
	    by simp
	  have successor_bound:
	    "wp_event ?M ?successor adversary_initial_state \<le>
	      composition_one_step_controlled_merkle_error_for budgets"
	    using
	      checked_staged_security_composition_fri_verifier_tied_successor_replay_gap_bound_by_controlled_merkle
	      [OF wf controlled]
	    by simp
	  have final_bound:
	    "wp_event ?M ?final adversary_initial_state \<le>
	      composition_one_step_controlled_merkle_error_for budgets"
	    using
	      checked_staged_security_composition_fri_verifier_tied_final_value_replay_gap_bound_by_controlled_merkle
	      [OF wf controlled]
	    by simp
		  have split_bound:
		    "wp_event ?M
		      (\<lambda>out.
		        ?merkle out \<or> ?slot out \<or> ?next out \<or>
		        ?successor out \<or> ?final out \<or> ?merkle out \<or> ?slot out)
		      adversary_initial_state \<le>
		        wp_event ?M ?merkle adversary_initial_state +
		        (wp_event ?M ?slot adversary_initial_state +
		        (wp_event ?M ?next adversary_initial_state +
		        (wp_event ?M ?successor adversary_initial_state +
		        (wp_event ?M ?final adversary_initial_state +
		         wp_event ?M ?merkle adversary_initial_state))))"
		  proof -
		    let ?nodup =
		      "\<lambda>out.
		        ?merkle out \<or> ?slot out \<or> ?next out \<or>
		        ?successor out \<or> ?final out \<or> ?merkle out"
	    have dedup:
	      "wp_event ?M
	        (\<lambda>out.
	          ?merkle out \<or> ?slot out \<or> ?next out \<or>
	          ?successor out \<or> ?final out \<or> ?merkle out \<or> ?slot out)
	        adversary_initial_state \<le>
	        wp_event ?M ?nodup adversary_initial_state"
	      by (rule wp_event_mono) auto
		    have union_bound:
		      "wp_event ?M ?nodup adversary_initial_state \<le>
		        wp_event ?M ?merkle adversary_initial_state +
		        (wp_event ?M ?slot adversary_initial_state +
		        (wp_event ?M ?next adversary_initial_state +
		        (wp_event ?M ?successor adversary_initial_state +
		        (wp_event ?M ?final adversary_initial_state +
		         wp_event ?M ?merkle adversary_initial_state))))"
		    proof -
		      let ?tail_final = "\<lambda>out. ?final out \<or> ?merkle out"
		      let ?tail_successor = "\<lambda>out. ?successor out \<or> ?tail_final out"
		      let ?tail_next = "\<lambda>out. ?next out \<or> ?tail_successor out"
		      let ?tail_slot = "\<lambda>out. ?slot out \<or> ?tail_next out"
		      have final_bound':
		        "wp_event ?M ?tail_final adversary_initial_state \<le>
		          wp_event ?M ?final adversary_initial_state +
		          wp_event ?M ?merkle adversary_initial_state"
		        by (rule wp_event_union_bound)
		      have successor_bound':
		        "wp_event ?M ?tail_successor adversary_initial_state \<le>
		          wp_event ?M ?successor adversary_initial_state +
		          (wp_event ?M ?final adversary_initial_state +
		           wp_event ?M ?merkle adversary_initial_state)"
		      proof -
		        have "wp_event ?M ?tail_successor adversary_initial_state \<le>
		          wp_event ?M ?successor adversary_initial_state +
		          wp_event ?M ?tail_final adversary_initial_state"
		          by (rule wp_event_union_bound)
		        also have "... \<le>
		          wp_event ?M ?successor adversary_initial_state +
		          (wp_event ?M ?final adversary_initial_state +
		           wp_event ?M ?merkle adversary_initial_state)"
		          by (intro add_mono order_refl final_bound')
		        finally show ?thesis .
		      qed
		      have next_bound':
		        "wp_event ?M ?tail_next adversary_initial_state \<le>
		          wp_event ?M ?next adversary_initial_state +
		          (wp_event ?M ?successor adversary_initial_state +
		          (wp_event ?M ?final adversary_initial_state +
		           wp_event ?M ?merkle adversary_initial_state))"
		      proof -
		        have "wp_event ?M ?tail_next adversary_initial_state \<le>
		          wp_event ?M ?next adversary_initial_state +
		          wp_event ?M ?tail_successor adversary_initial_state"
		          by (rule wp_event_union_bound)
		        also have "... \<le>
		          wp_event ?M ?next adversary_initial_state +
		          (wp_event ?M ?successor adversary_initial_state +
		          (wp_event ?M ?final adversary_initial_state +
		           wp_event ?M ?merkle adversary_initial_state))"
		          by (intro add_mono order_refl successor_bound')
		        finally show ?thesis .
		      qed
		      have slot_bound':
		        "wp_event ?M ?tail_slot adversary_initial_state \<le>
		          wp_event ?M ?slot adversary_initial_state +
		          (wp_event ?M ?next adversary_initial_state +
		          (wp_event ?M ?successor adversary_initial_state +
		          (wp_event ?M ?final adversary_initial_state +
		           wp_event ?M ?merkle adversary_initial_state)))"
		      proof -
		        have "wp_event ?M ?tail_slot adversary_initial_state \<le>
		          wp_event ?M ?slot adversary_initial_state +
		          wp_event ?M ?tail_next adversary_initial_state"
		          by (rule wp_event_union_bound)
		        also have "... \<le>
		          wp_event ?M ?slot adversary_initial_state +
		          (wp_event ?M ?next adversary_initial_state +
		          (wp_event ?M ?successor adversary_initial_state +
		          (wp_event ?M ?final adversary_initial_state +
		           wp_event ?M ?merkle adversary_initial_state)))"
		          by (intro add_mono order_refl next_bound')
		        finally show ?thesis .
		      qed
		      have "wp_event ?M ?nodup adversary_initial_state \<le>
		        wp_event ?M ?merkle adversary_initial_state +
		        wp_event ?M ?tail_slot adversary_initial_state"
		        by (rule wp_event_union_bound)
		      also have "... \<le>
		        wp_event ?M ?merkle adversary_initial_state +
		        (wp_event ?M ?slot adversary_initial_state +
		        (wp_event ?M ?next adversary_initial_state +
		        (wp_event ?M ?successor adversary_initial_state +
		        (wp_event ?M ?final adversary_initial_state +
		         wp_event ?M ?merkle adversary_initial_state))))"
		        by (intro add_mono order_refl slot_bound')
		      finally show ?thesis .
		    qed
		    show ?thesis
		      by (rule order_trans[OF dedup union_bound])
		  qed
		  have split_sum_bound:
		    "wp_event ?M ?merkle adversary_initial_state +
		      (wp_event ?M ?slot adversary_initial_state +
		      (wp_event ?M ?next adversary_initial_state +
		      (wp_event ?M ?successor adversary_initial_state +
		      (wp_event ?M ?final adversary_initial_state +
		       wp_event ?M ?merkle adversary_initial_state)))) \<le>
		        composition_one_step_controlled_merkle_error_for budgets +
		        (0 +
		        (composition_one_step_controlled_merkle_error_for budgets +
		        (composition_one_step_controlled_merkle_error_for budgets +
		        (composition_one_step_controlled_merkle_error_for budgets +
		         composition_one_step_controlled_merkle_error_for budgets))))"
		    by (intro add_mono
		        checked_staged_security_partial_merkle_inconsistency_bad_bound_by_composition_one_step_controlled_merkle_error
		        [OF wf controlled]
		        checked_staged_security_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero
		        next_bound successor_bound final_bound)
		  have "wp_event ?M ?conflict adversary_initial_state \<le>
		    wp_event ?M
		      (\<lambda>out.
		        ?merkle out \<or> ?slot out \<or> ?next out \<or>
		        ?successor out \<or> ?final out \<or> ?merkle out \<or> ?slot out)
		      adversary_initial_state"
		    by (rule split)
		  also have "... \<le>
		    wp_event ?M ?merkle adversary_initial_state +
		      (wp_event ?M ?slot adversary_initial_state +
		      (wp_event ?M ?next adversary_initial_state +
		      (wp_event ?M ?successor adversary_initial_state +
		      (wp_event ?M ?final adversary_initial_state +
		       wp_event ?M ?merkle adversary_initial_state))))"
		    by (rule split_bound)
		  also have "... \<le>
		      composition_one_step_controlled_merkle_error_for budgets +
		      (0 +
		      (composition_one_step_controlled_merkle_error_for budgets +
		      (composition_one_step_controlled_merkle_error_for budgets +
		      (composition_one_step_controlled_merkle_error_for budgets +
		       composition_one_step_controlled_merkle_error_for budgets))))"
		    by (rule split_sum_bound)
		  finally show ?thesis
		    by (simp add: add.assoc)
qed

lemma composition_one_step_verifier_tied_controlled_error_for_bound:
  fixes comp_bad :: "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and comp_subset:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        comp_bad dg i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (composition_fri_canonical_layer_len dg i) (comp_pw dg i)
            (comp_layer dg i prefix) (comp_claimed dg i prefix)
            (comp_dom dg i prefix)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state
    \<le> composition_one_step_verifier_tied_controlled_error_for budgets
        comp_bad"
proof -
  have sampled_query:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> composition_one_step_sampled_error_for budgets comp_bad"
    by (rule composition_one_step_sampled_error_for_bound
        [OF wf controlled comp_subset])
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state
    \<le> composition_one_step_sampled_error_for budgets comp_bad"
    by (rule
        checked_staged_security_composition_fri_verifier_tied_sampled_layer_chain_bound_from_sampled_query
        [OF sampled_query])
  have conflict:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_sampled_assignment_conflict)
      adversary_initial_state \<le>
      (((composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0 + 0) +
        composition_one_step_controlled_merkle_error_for budgets) + 0)"
    by (rule
        checked_staged_security_composition_fri_verifier_tied_sampled_assignment_conflict_bound_by_controlled_merkle
        [OF wf controlled])
  have zero:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> (0::prob)"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    show "\<And>s. \<not>
      composition_fri_verifier_tied_zero_round_final_obstruction s None"
      unfolding composition_fri_verifier_tied_zero_round_final_obstruction_def
        accepted_fri_opening_transcript_def
      by simp
  next
    fix data attacker_state
    assume support: "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
      (composition_fri_verifier_tied_zero_round_final_obstruction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> 0"
      by (subst
          wp_composition_fri_verifier_tied_zero_round_final_obstruction_zero)
        simp
  qed
  have branch:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      composition_one_step_sampled_error_for budgets comp_bad +
        ((((composition_one_step_controlled_merkle_error_for budgets + 0) +
          (composition_one_step_controlled_merkle_error_for budgets + 0) +
          (composition_one_step_controlled_merkle_error_for budgets + 0) +
          (composition_one_step_controlled_merkle_error_for budgets + 0 + 0) +
          composition_one_step_controlled_merkle_error_for budgets) + 0) + 0)"
    by (rule
        checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_staged_sampled_conflict_and_zero
        [OF sampled conflict zero])
  show ?thesis
    using branch
    by (simp add: composition_one_step_verifier_tied_controlled_error_for_def)
qed

lemma composition_one_step_verifier_tied_error_for_bound:
  fixes comp_bad :: "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and comp_subset:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        comp_bad dg i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (composition_fri_canonical_layer_len dg i) (comp_pw dg i)
            (comp_layer dg i prefix) (comp_claimed dg i prefix)
            (comp_dom dg i prefix)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state
    \<le> composition_one_step_verifier_tied_error_for budgets A comp_bad"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> composition_one_step_sampled_error_for budgets comp_bad"
    by (rule composition_one_step_sampled_error_for_bound
        [OF wf controlled comp_subset])
  have merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
      \<le> composition_one_step_reachable_merkle_error_for A"
    unfolding composition_one_step_reachable_merkle_error_for_def
    by (rule reachable_verifier_event_bound_for_ge, assumption)
  have branch:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state
      \<le> composition_one_step_sampled_error_for budgets comp_bad +
        (((composition_one_step_reachable_merkle_error_for A + 0) +
          (composition_one_step_reachable_merkle_error_for A + 0) +
          (composition_one_step_reachable_merkle_error_for A + 0) +
          (composition_one_step_reachable_merkle_error_for A + 0 + 0) +
          composition_one_step_reachable_merkle_error_for A) + 0 + 0)"
    apply (rule
        checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_sampled_query_and_residual_gaps
        [OF sampled])
    apply (rule wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
    apply (rule merkle_bound)
    apply assumption
    apply (rule wp_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_zero)
    apply (rule wp_composition_fri_verifier_tied_next_value_replay_gap_bound_from_merkle_and_slot)
    apply (rule merkle_bound)
    apply assumption
    apply (rule wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
    apply (rule wp_composition_fri_verifier_tied_successor_replay_gap_bound_from_merkle_and_slot)
    apply (rule merkle_bound)
    apply assumption
    apply (rule wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
    apply (rule wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
    apply (rule merkle_bound)
    apply assumption
    apply (rule wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
    apply (rule wp_composition_fri_verifier_tied_final_value_selected_step_missing_gap_zero)
    apply (subst wp_composition_fri_verifier_tied_zero_round_final_obstruction_zero)
    apply simp
    done
  show ?thesis
    using branch
    by (simp add: composition_one_step_verifier_tied_error_for_def)
qed

lemma trace_empty_one_step_error_for_bound:
  fixes empty_bad :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and empty_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        empty_bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (trace_fri_canonical_layer_len i) (empty_pw i)
            (empty_layer i prefix) (empty_claimed i prefix)
            (empty_dom i prefix)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state
    \<le> trace_empty_one_step_error_for budgets A empty_bad"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> trace_one_step_sampled_error_for budgets empty_bad"
    by (rule trace_one_step_sampled_error_for_bound
        [OF wf controlled empty_subset])
  have conflict_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_assignment_conflict)
      adversary_initial_state
    \<le> reachable_verifier_event_bound_for A
        trace_fri_sampled_assignment_conflict"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    show "\<And>s. \<not> trace_fri_sampled_assignment_conflict s None"
      unfolding trace_fri_sampled_assignment_conflict_def
        trace_fri_partial_candidate_opening_evidence_def
        accepted_fri_opening_transcript_def
      by simp
  next
    fix data attacker_state
    assume support: "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
      (trace_fri_sampled_assignment_conflict
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        trace_fri_sampled_assignment_conflict"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  qed
  have zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state
    \<le> trace_fri_zero_round_agreement_set_target_error_for budgets +
        trace_fri_controlled_merkle_error_for budgets +
        reachable_verifier_event_bound_for A
        trace_fri_bad_with_header_tied_partial_candidate +
        (trace_fri_controlled_merkle_error_for budgets +
         (reachable_verifier_event_bound_for A
            trace_fri_header_tied_low_candidate_untied_root_gap +
          reachable_verifier_event_bound_for A
            trace_fri_header_tied_low_candidate_untied_query_gap)) +
        reachable_verifier_event_bound_for A
          trace_fri_bad_with_header_tied_partial_candidate"
    by (rule checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_agreement_sets
        [OF wf controlled])
  have branch:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state
      \<le> trace_one_step_sampled_error_for budgets empty_bad +
        (reachable_verifier_event_bound_for A
         trace_fri_sampled_assignment_conflict +
         trace_fri_zero_round_agreement_set_target_error_for budgets +
         trace_fri_controlled_merkle_error_for budgets +
         reachable_verifier_event_bound_for A
          trace_fri_bad_with_header_tied_partial_candidate +
         (trace_fri_controlled_merkle_error_for budgets +
          (reachable_verifier_event_bound_for A
            trace_fri_header_tied_low_candidate_untied_root_gap +
           reachable_verifier_event_bound_for A
         trace_fri_header_tied_low_candidate_untied_query_gap)) +
         reachable_verifier_event_bound_for A
          trace_fri_bad_with_header_tied_partial_candidate)"
  proof -
    have raw:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state
        \<le> trace_one_step_sampled_error_for budgets empty_bad +
          (reachable_verifier_event_bound_for A
            trace_fri_sampled_assignment_conflict +
           (trace_fri_zero_round_agreement_set_target_error_for budgets +
            trace_fri_controlled_merkle_error_for budgets +
            reachable_verifier_event_bound_for A
              trace_fri_bad_with_header_tied_partial_candidate +
            (trace_fri_controlled_merkle_error_for budgets +
             (reachable_verifier_event_bound_for A
                trace_fri_header_tied_low_candidate_untied_root_gap +
              reachable_verifier_event_bound_for A
                trace_fri_header_tied_low_candidate_untied_query_gap)) +
            reachable_verifier_event_bound_for A
              trace_fri_bad_with_header_tied_partial_candidate))"
      by (rule
          checked_staged_security_trace_fri_empty_header_bound_from_staged_sampled_conflict_and_zero
          [OF sampled conflict_bound zero_bound])
    show ?thesis
      by (rule order_trans[OF raw]) (simp add: algebra_simps)
  qed
  show ?thesis
    using branch
    by (simp add: trace_empty_one_step_error_for_def
      trace_fri_empty_small_conflict_zero_error_for_def)
qed

lemma trace_header_one_step_error_for_bound:
  fixes trace_bad :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        trace_bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (trace_fri_canonical_layer_len i) (empty_pw i)
            (empty_layer i prefix) (empty_claimed i prefix)
            (empty_dom i prefix)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state
    \<le> trace_header_one_step_error_for budgets A trace_bad"
proof -
  have sampled_query:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> trace_one_step_sampled_error_for budgets trace_bad"
    by (rule trace_one_step_sampled_error_for_bound
        [OF wf controlled trace_subset])
  have sampled_plain:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state
    \<le> trace_one_step_sampled_error_for budgets trace_bad"
    by (rule
        checked_staged_security_trace_fri_sampled_layer_chain_bound_from_sampled_query
        [OF sampled_query])
  have sampled_header:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state
    \<le> trace_one_step_sampled_error_for budgets trace_bad"
  proof (rule order_trans[OF _ sampled_plain])
    show "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_sampled_layer_chain)
        adversary_initial_state
      \<le> wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_sampled_layer_chain)
        adversary_initial_state"
      by (rule wp_event_mono)
        (auto simp: staged_security_with_data_state_verifier_event_def
          dest: trace_fri_header_tied_sampled_layer_chain_imp_sampled_layer_chain
          split: option.splits prod.splits)
  qed
  have conflict_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_sampled_assignment_conflict)
      adversary_initial_state
    \<le> trace_fri_header_replay_conflict_error_for A"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    fix data attacker_state
    assume support:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    let ?M =
      "reachable_verifier_event_bound_for A partial_merkle_inconsistency_bad"
    let ?H =
      "reachable_verifier_event_bound_for A
        trace_fri_header_tied_recorded_sibling_candidate_missing"
    have merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
        \<le> ?M"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
    have recorded_missing_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing ?s) ?s
        \<le> ?H"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
    have head_neq:
      "wp_event verify_monad
        (trace_fri_header_tied_base_head_value_neq_gap ?s) ?s \<le> ?M"
      by (rule
          wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle)
        (rule merkle_bound)
    have head_mismatch:
      "wp_event verify_monad
        (trace_fri_header_tied_base_head_value_mismatch_gap ?s) ?s
        \<le> ?M"
      by (rule
          wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap
          [OF head_neq])
    have alignment:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap ?s) ?s \<le> ?M"
      by (rule
          wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap
          [OF head_mismatch])
    have next_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap ?s) ?s \<le> ?M + 0"
      by (rule
          wp_trace_fri_header_tied_next_value_replay_gap_bound_from_merkle_and_slot)
        (rule merkle_bound,
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
    have successor:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap ?s) ?s \<le> ?M + 0"
      by (rule
          wp_trace_fri_header_tied_successor_replay_gap_bound_from_merkle_and_slot)
        (rule merkle_bound,
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
    have final:
      "wp_event verify_monad
        (trace_fri_header_tied_final_value_replay_gap ?s) ?s \<le> ?M + 0 + 0"
      by (rule
          wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
        (rule merkle_bound,
         rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero,
         rule wp_trace_fri_header_tied_final_value_selected_step_missing_gap_zero)
    have slot:
      "wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap ?s) ?s
        \<le> 0"
      by (rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
    have authenticated_recorded_auth:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap ?s)
        ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap_bound_from_slot_recorded_chunk_gap
          [OF slot])
    have recorded_auth:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_recorded_auth_gap ?s) ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_same_layer_recorded_auth_gap_bound_from_authenticated_recorded_auth_gap
          [OF authenticated_recorded_auth])
    have same_auth:
      "wp_event verify_monad
        (trace_fri_header_tied_same_layer_auth_gap ?s) ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_same_layer_auth_gap_bound_from_recorded_auth_gap
          [OF recorded_auth])
    have auth_gap:
      "wp_event verify_monad
        (trace_fri_header_tied_assignment_auth_gap ?s) ?s \<le> 0"
      by (rule
          wp_trace_fri_header_tied_assignment_auth_gap_bound_from_same_layer_auth_gap
          [OF same_auth])
    have complement:
      "wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_sampled_assignment_conflict ?s out \<and>
          \<not> trace_fri_header_tied_recorded_sibling_candidate_missing ?s out)
        ?s \<le>
        ((((?M + ?M) + (?M + 0) + (?M + 0) + (?M + 0 + 0)) + ?M) + 0)"
      by (rule
          wp_trace_fri_header_tied_sampled_assignment_conflict_without_recorded_missing_bound_from_auth_gap_and_replay_gaps)
        (rule auth_gap, rule merkle_bound, rule alignment,
         rule next_bound, rule successor, rule final)
    show "wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict ?s) ?s
      \<le> trace_fri_header_replay_conflict_error_for A"
      unfolding trace_fri_header_replay_conflict_error_for_def Let_def
      by (rule
          wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_recorded_missing_and_complement)
        (rule recorded_missing_bound, rule complement)
  next
    fix s
    show "\<not> trace_fri_header_tied_sampled_assignment_conflict s None"
      unfolding trace_fri_header_tied_sampled_assignment_conflict_def
        accepted_fri_opening_transcript_def
      by simp
  qed
  have zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state
    \<le> trace_fri_zero_round_agreement_set_target_error_for budgets +
      trace_fri_controlled_merkle_error_for budgets"
  proof -
    have checked:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_zero_round_checked_final_obstruction)
        adversary_initial_state
      \<le> trace_fri_zero_round_agreement_set_target_error_for budgets"
      by (rule checked_staged_security_trace_fri_zero_round_checked_final_obstruction_bound_from_agreement_sets
          [OF wf controlled])
    have merkle:
      "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state
      \<le> trace_fri_controlled_merkle_error_for budgets"
      unfolding trace_fri_controlled_merkle_error_for_def
      by (rule
          checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
          [OF wf controlled])
    have split:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_header_tied_zero_round_final_obstruction)
        adversary_initial_state
      \<le> wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            trace_fri_zero_round_checked_final_obstruction out \<or>
          staged_security_with_data_state_verifier_event
            partial_merkle_inconsistency_bad out)
        adversary_initial_state"
      unfolding staged_security_with_data_state_verifier_event_def
      by (rule wp_event_mono_on_support)
        (auto dest:
          trace_fri_header_tied_zero_round_final_obstruction_imp_checked_or_merkle
          split: option.splits prod.splits)
    also have "... \<le>
        wp_event (checked_staged_security_experiment_with_data_state A)
          (staged_security_with_data_state_verifier_event
            trace_fri_zero_round_checked_final_obstruction)
          adversary_initial_state +
        wp_event (checked_staged_security_experiment_with_data_state A)
          (staged_security_with_data_state_verifier_event
            partial_merkle_inconsistency_bad)
          adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
        trace_fri_zero_round_agreement_set_target_error_for budgets +
        trace_fri_controlled_merkle_error_for budgets"
      by (rule add_mono[OF checked merkle])
    finally show ?thesis .
  qed
  have branch:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state
      \<le> trace_one_step_sampled_error_for budgets trace_bad +
        (trace_fri_header_replay_conflict_error_for A +
         (trace_fri_zero_round_agreement_set_target_error_for budgets +
          trace_fri_controlled_merkle_error_for budgets))"
    by (rule
        checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_sampled_conflict_and_staged_zero
        [OF sampled_header conflict_bound zero_bound])
  show ?thesis
    using branch
    by (simp add: trace_header_one_step_error_for_def
      trace_fri_header_replay_conflict_zero_error_for_def)
qed

definition trace_empty_header_refined_zero_error_for
where
  "trace_empty_header_refined_zero_error_for budgets A empty_bad =
    (trace_fri_zero_round_agreement_set_target_error_for budgets +
     trace_fri_controlled_merkle_error_for budgets +
     (trace_header_one_step_error_for budgets A empty_bad +
      (trace_fri_controlled_merkle_error_for budgets +
       (reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_root_gap +
        reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_query_gap))) +
     trace_header_one_step_error_for budgets A empty_bad)"

definition trace_empty_header_refined_one_step_error_for
where
  "trace_empty_header_refined_one_step_error_for budgets A empty_bad =
    trace_one_step_sampled_error_for budgets empty_bad +
      (reachable_verifier_event_bound_for A
        trace_fri_sampled_assignment_conflict +
       trace_empty_header_refined_zero_error_for budgets A empty_bad)"

definition concrete_trace_empty_header_refined_one_step_error_for
where
  "concrete_trace_empty_header_refined_one_step_error_for budgets A =
    trace_empty_header_refined_one_step_error_for budgets A
      trace_one_step_split_bad"

lemma checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_agreement_sets_and_header:
  fixes H :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and header_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_partial_candidate)
        adversary_initial_state \<le> H"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets +
      trace_fri_controlled_merkle_error_for budgets +
      (H +
       (trace_fri_controlled_merkle_error_for budgets +
        (reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_root_gap +
         reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_query_gap))) +
      H"
proof -
  have checked:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets"
    by (rule
        checked_staged_security_trace_fri_zero_round_checked_final_obstruction_bound_from_agreement_sets
        [OF wf controlled])
  have merkle:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets"
    unfolding trace_fri_controlled_merkle_error_for_def
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
  have hash:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets"
    unfolding trace_fri_controlled_merkle_error_for_def
    by (rule
        checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  have root:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_root_gap)
      adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_root_gap"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    show "\<And>s. \<not> trace_fri_header_tied_low_candidate_untied_root_gap s None"
      unfolding trace_fri_header_tied_low_candidate_untied_root_gap_def
        trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
        accepted_fri_opening_transcript_def
      by simp
  next
    fix data attacker_state
    assume support: "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_root_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_root_gap"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  qed
  have query:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_low_candidate_untied_query_gap)
      adversary_initial_state \<le>
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_query_gap"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    show "\<And>s. \<not> trace_fri_header_tied_low_candidate_untied_query_gap s None"
      unfolding trace_fri_header_tied_low_candidate_untied_query_gap_def
        trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
        accepted_fri_opening_transcript_def
      by simp
  next
    fix data attacker_state
    assume support: "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_query_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_query_gap"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  qed
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?untied =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_untied_reachable_witness_gap"
  let ?hash =
    "staged_security_with_data_state_verifier_event
      hash_map_output_collision_bad"
  let ?root =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_untied_root_gap"
  let ?query =
    "staged_security_with_data_state_verifier_event
      trace_fri_header_tied_low_candidate_untied_query_gap"
  have untied:
    "wp_event ?M ?untied adversary_initial_state \<le>
      trace_fri_controlled_merkle_error_for budgets +
      (reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_root_gap +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_query_gap)"
  proof -
    have "wp_event ?M ?untied adversary_initial_state \<le>
        wp_event ?M (\<lambda>out. ?hash out \<or> ?root out \<or> ?query out)
          adversary_initial_state"
      unfolding staged_security_with_data_state_verifier_event_def
      by (rule wp_event_mono_on_support)
        (auto
          dest:
            trace_fri_header_tied_low_candidate_untied_gap_imp_hash_root_or_query
          split: option.splits prod.splits)
    also have "... \<le>
        wp_event ?M ?hash adversary_initial_state +
        wp_event ?M (\<lambda>out. ?root out \<or> ?query out)
          adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?hash adversary_initial_state +
        (wp_event ?M ?root adversary_initial_state +
         wp_event ?M ?query adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        trace_fri_controlled_merkle_error_for budgets +
        (reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_root_gap +
         reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_untied_query_gap)"
      by (intro add_mono hash root query)
    finally show ?thesis .
  qed
  have transfer:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_candidate_transfer_gap)
      adversary_initial_state \<le>
      H +
      (trace_fri_controlled_merkle_error_for budgets +
       (reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_root_gap +
        reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_query_gap))"
    by (rule
        checked_staged_security_trace_fri_header_tied_candidate_transfer_gap_bound_from_staged_header_and_untied
        [OF header_bound untied])
  show ?thesis
    by (rule
        checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_staged_checked_merkle_transfer_header
        [OF checked merkle transfer header_bound])
qed

lemma trace_empty_header_refined_one_step_error_for_bound:
  fixes empty_bad :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and empty_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        empty_bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (trace_fri_canonical_layer_len i) (empty_pw i)
            (empty_layer i prefix) (empty_claimed i prefix)
            (empty_dom i prefix)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state
    \<le> trace_empty_header_refined_one_step_error_for budgets A empty_bad"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> trace_one_step_sampled_error_for budgets empty_bad"
    by (rule trace_one_step_sampled_error_for_bound
        [OF wf controlled empty_subset])
  have conflict_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_assignment_conflict)
      adversary_initial_state
    \<le> reachable_verifier_event_bound_for A
        trace_fri_sampled_assignment_conflict"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    show "\<And>s. \<not> trace_fri_sampled_assignment_conflict s None"
      unfolding trace_fri_sampled_assignment_conflict_def
        trace_fri_partial_candidate_opening_evidence_def
        accepted_fri_opening_transcript_def
      by simp
  next
    fix data attacker_state
    assume support: "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
      (trace_fri_sampled_assignment_conflict
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        trace_fri_sampled_assignment_conflict"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  qed
  have header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state
    \<le> trace_header_one_step_error_for budgets A empty_bad"
    by (rule trace_header_one_step_error_for_bound
        [OF wf controlled empty_subset])
  have zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state
    \<le> trace_empty_header_refined_zero_error_for budgets A empty_bad"
    unfolding trace_empty_header_refined_zero_error_for_def
    by (rule
        checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_agreement_sets_and_header
        [OF wf controlled header_bound])
  have branch:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state
      \<le> trace_one_step_sampled_error_for budgets empty_bad +
        (reachable_verifier_event_bound_for A
          trace_fri_sampled_assignment_conflict +
         trace_empty_header_refined_zero_error_for budgets A empty_bad)"
    by (rule
        checked_staged_security_trace_fri_empty_header_bound_from_staged_sampled_conflict_and_zero
        [OF sampled conflict_bound zero_bound])
  show ?thesis
    using branch
    by (simp add: trace_empty_header_refined_one_step_error_for_def)
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_one_step_fri_components:
  fixes trace_bad empty_bad :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
    and comp_bad :: "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        trace_bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (trace_fri_canonical_layer_len i) (empty_pw i)
            (empty_layer i prefix) (empty_claimed i prefix)
            (empty_dom i prefix)"
    and comp_subset:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        comp_bad dg i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (composition_fri_canonical_layer_len dg i) (comp_pw dg i)
            (comp_layer dg i prefix) (comp_claimed dg i prefix)
            (comp_dom dg i prefix)"
    and empty_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        empty_bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (trace_fri_canonical_layer_len i) (empty_pw i)
            (empty_layer i prefix) (empty_claimed i prefix)
            (empty_dom i prefix)"
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
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        active_route_current_prefix_authenticated_error_for A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
    trace_header_one_step_error_for budgets A trace_bad +
      composition_one_step_verifier_tied_controlled_error_for budgets
        comp_bad +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound) +
      trace_empty_header_refined_one_step_error_for budgets A empty_bad +
      active_route_current_empty_query_error_for A)"
proof -
  have trace_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state
    \<le> trace_header_one_step_error_for budgets A trace_bad"
    by (rule trace_header_one_step_error_for_bound
        [OF wf controlled trace_subset])
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state
    \<le> composition_one_step_verifier_tied_controlled_error_for budgets
        comp_bad"
    by (rule composition_one_step_verifier_tied_controlled_error_for_bound
        [OF wf controlled comp_subset])
  have empty_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state
    \<le> trace_empty_header_refined_one_step_error_for budgets A empty_bad"
    by (rule trace_empty_header_refined_one_step_error_for_bound
        [OF wf controlled empty_subset])
  show ?thesis
    by (rule
        stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_bounds
        [OF false_statement wf controlled trace_bound comp_bound empty_bound])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_one_step_endpoint:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        active_route_current_prefix_authenticated_error_for A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
    concrete_trace_header_one_step_error_for budgets A +
      concrete_composition_one_step_error_for budgets A +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound) +
      concrete_trace_empty_header_refined_one_step_error_for budgets A +
      active_route_current_empty_query_error_for A)"
  unfolding concrete_trace_header_one_step_error_for_def
    concrete_composition_one_step_error_for_def
    concrete_trace_empty_header_refined_one_step_error_for_def
  by (rule
      stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_one_step_fri_components
      [where trace_bad = trace_one_step_split_bad
        and comp_bad = composition_one_step_split_bad
        and empty_bad = trace_one_step_split_bad
        and empty_pw = trace_one_step_split_pw
        and empty_layer = trace_one_step_split_layer
        and empty_claimed = trace_one_step_split_claimed
        and empty_dom = trace_one_step_split_domain
        and comp_pw = composition_one_step_split_pw
        and comp_layer = composition_one_step_split_layer
        and comp_claimed = composition_one_step_split_claimed
        and comp_dom = composition_one_step_split_domain,
        OF false_statement wf controlled])
    (simp_all add:
      trace_one_step_split_bad_def
      composition_one_step_split_bad_def
      trace_one_step_disagreement_bad_for_def
      composition_one_step_disagreement_bad_for_def)

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_sharpened:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        active_route_current_prefix_authenticated_error_for A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
    sharpened_trace_fri_header_error_for budgets A +
      sharpened_composition_fri_error_for budgets A +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound) +
      sharpened_trace_fri_empty_error_for budgets A +
      active_route_current_empty_query_error_for A)"
  by (rule
      stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_bounds
      [OF false_statement wf controlled
        sharpened_trace_fri_header_error_for_bound[OF wf controlled]
        sharpened_composition_fri_error_for_bound[OF wf controlled]
        sharpened_trace_fri_empty_error_for_bound[OF wf controlled]])

theorem stark_soundness_concrete_fri_sharpened_endpoint:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        active_route_current_prefix_authenticated_error_for A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
    concrete_trace_header_one_step_error_for budgets A +
      concrete_composition_one_step_error_for budgets A +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound) +
      concrete_trace_empty_header_refined_one_step_error_for budgets A +
      active_route_current_empty_query_error_for A)"
  by (rule
      stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_one_step_endpoint
      [OF false_statement wf controlled])

end

hide_fact
  soundness.stark_soundness_concrete_fri_sharpened_endpoint
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_sharpened

end
