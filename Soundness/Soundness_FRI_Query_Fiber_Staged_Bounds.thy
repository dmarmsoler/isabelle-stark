(*  Title:      Stark/Soundness_FRI_Query_Fiber_Staged_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_Fiber_Staged_Bounds
  imports
    Soundness_FRI_Query_Index_Staged_Bounds
    Soundness_FRI_Query_Aware_Interface
begin

text \<open>
  Staged sampled-query FRI bounds from generic query fibers.

  The checked staged query-index accounting currently consumes a fixed query
  target.  This layer derives such a target from the union of the generic
  per-challenge query fibers outside a chosen challenge-list cover.  It keeps
  the query-aware FRI boundary explicit without changing the protocol or the
  random-oracle model.
\<close>

context soundness
begin

definition generic_fri_sampled_query_outside_query_cover
  :: "('f list \<Rightarrow> bool) \<Rightarrow> ('f list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow>
      'f list set \<Rightarrow> nat list set"
where
  "generic_fri_sampled_query_outside_query_cover low_degree candidate_bad
      degree_bound B =
    (\<Union>challenges \<in>
      fri_challenge_space (fri_round_count_for_degree_bound degree_bound) - B.
      generic_fri_sampled_query_query_fiber low_degree candidate_bad
        degree_bound challenges)"

definition generic_fri_sampled_query_missing_full_cover_fiber
  :: "('f list \<Rightarrow> bool) \<Rightarrow> ('f list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> nat list set"
where
  "generic_fri_sampled_query_missing_full_cover_fiber low_degree candidate_bad
      degree_bound challenges =
    {query_idxs \<in> fri_query_index_list_space.
      \<exists>candidate_table roots final_value round_layers layers.
        generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
          candidate_table degree_bound roots challenges final_value query_idxs
          round_layers layers \<and>
        \<not> fri_sampled_layers_cover_fold_indices roots query_idxs}"

lemma generic_fri_sampled_query_missing_full_cover_fiber_subset:
  "generic_fri_sampled_query_missing_full_cover_fiber low_degree candidate_bad
      degree_bound challenges \<subseteq> fri_query_index_list_space"
  unfolding generic_fri_sampled_query_missing_full_cover_fiber_def by auto

lemma finite_generic_fri_sampled_query_missing_full_cover_fiber:
  "finite
    (generic_fri_sampled_query_missing_full_cover_fiber low_degree
      candidate_bad degree_bound challenges)"
  using generic_fri_sampled_query_missing_full_cover_fiber_subset
  by (rule finite_subset) (rule finite_fri_query_index_list_space)

lemma generic_fri_sampled_query_query_fiber_subset_missing_full_cover:
  assumes full_cover_imp:
    "\<And>candidate_table roots final_value round_layers layers query_idxs.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      fri_sampled_layers_cover_fold_indices roots query_idxs \<Longrightarrow>
      challenges \<in> B"
    and challenges_notin: "challenges \<notin> B"
  shows
    "generic_fri_sampled_query_query_fiber low_degree candidate_bad
      degree_bound challenges \<subseteq>
     generic_fri_sampled_query_missing_full_cover_fiber low_degree
      candidate_bad degree_bound challenges"
proof
  fix query_idxs
  assume query_in:
    "query_idxs \<in>
      generic_fri_sampled_query_query_fiber low_degree candidate_bad
        degree_bound challenges"
  then have query_space: "query_idxs \<in> fri_query_index_list_space"
    using generic_fri_sampled_query_query_fiber_subset by blast
  from query_in obtain candidate_table roots final_value round_layers layers
    where evidence:
      "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers"
    unfolding generic_fri_sampled_query_query_fiber_def
      generic_fri_sampled_query_restricted_bad_pairs_def
      generic_fri_sampled_query_bad_pair_union_def
      generic_fri_sampled_query_bad_pair_set_def
      fri_query_challenge_pair_query_fiber_def
    by auto
  have not_cover: "\<not> fri_sampled_layers_cover_fold_indices roots query_idxs"
  proof
    assume cover: "fri_sampled_layers_cover_fold_indices roots query_idxs"
    have "challenges \<in> B"
      by (rule full_cover_imp[OF query_space evidence cover])
    then show False
      using challenges_notin by simp
  qed
  show "query_idxs \<in>
    generic_fri_sampled_query_missing_full_cover_fiber low_degree
      candidate_bad degree_bound challenges"
    unfolding generic_fri_sampled_query_missing_full_cover_fiber_def
    by (intro CollectI conjI exI)
      (rule query_space, rule evidence, rule not_cover)
qed

lemma generic_fri_sampled_query_query_fiber_entries_card_le_missing_full_cover:
  assumes full_cover_imp:
    "\<And>candidate_table roots final_value round_layers layers query_idxs.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      fri_sampled_layers_cover_fold_indices roots query_idxs \<Longrightarrow>
      challenges \<in> B"
    and challenges_notin: "challenges \<notin> B"
  shows
    "card
      (query_index_list_entries
        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges))
    \<le>
    card
      (query_index_list_entries
        (generic_fri_sampled_query_missing_full_cover_fiber low_degree
          candidate_bad degree_bound challenges))"
proof -
  have subset:
    "generic_fri_sampled_query_query_fiber low_degree candidate_bad
      degree_bound challenges \<subseteq>
     generic_fri_sampled_query_missing_full_cover_fiber low_degree
      candidate_bad degree_bound challenges"
    by (rule generic_fri_sampled_query_query_fiber_subset_missing_full_cover
        [OF full_cover_imp challenges_notin])
  have entries_subset:
    "query_index_list_entries
        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges)
      \<subseteq>
     query_index_list_entries
        (generic_fri_sampled_query_missing_full_cover_fiber low_degree
          candidate_bad degree_bound challenges)"
    using subset unfolding query_index_list_entries_def by blast
  show ?thesis
    by (rule card_mono[OF _ entries_subset])
      (rule finite_subset[OF _ finite_query_sample_space],
       unfold query_index_list_entries_def
        generic_fri_sampled_query_missing_full_cover_fiber_def
        fri_query_index_list_space_def, auto)
qed

lemma generic_fri_sampled_query_outside_query_cover_subset:
  "generic_fri_sampled_query_outside_query_cover low_degree candidate_bad
      degree_bound B \<subseteq> fri_query_index_list_space"
  unfolding generic_fri_sampled_query_outside_query_cover_def
  by (auto intro: generic_fri_sampled_query_query_fiber_subset[THEN subsetD])

lemma finite_generic_fri_sampled_query_outside_query_cover:
  "finite
    (generic_fri_sampled_query_outside_query_cover low_degree candidate_bad
      degree_bound B)"
  using generic_fri_sampled_query_outside_query_cover_subset
  by (rule finite_subset) (rule finite_fri_query_index_list_space)

lemma generic_fri_sampled_query_outside_query_cover_card_le_from_fibers:
  "card
    (generic_fri_sampled_query_outside_query_cover low_degree candidate_bad
      degree_bound B)
    \<le>
    (\<Sum>challenges \<in>
      fri_challenge_space (fri_round_count_for_degree_bound degree_bound) - B.
      card
        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges))"
  unfolding generic_fri_sampled_query_outside_query_cover_def
  by (rule card_UN_le) simp

lemma generic_fri_sampled_query_outside_query_cover_entries_card_le_from_fibers:
  "card
    (query_index_list_entries
      (generic_fri_sampled_query_outside_query_cover low_degree candidate_bad
        degree_bound B))
    \<le>
    (\<Sum>challenges \<in>
      fri_challenge_space (fri_round_count_for_degree_bound degree_bound) - B.
      card
        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges)) * rounds"
proof -
  let ?Q =
    "generic_fri_sampled_query_outside_query_cover low_degree candidate_bad
      degree_bound B"
  let ?K =
    "(\<Sum>challenges \<in>
      fri_challenge_space (fri_round_count_for_degree_bound degree_bound) - B.
      card
        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges))"
  have entries_le: "card (query_index_list_entries ?Q) \<le> card ?Q * rounds"
    by (rule query_index_list_entries_card_le)
      (rule finite_generic_fri_sampled_query_outside_query_cover,
       rule generic_fri_sampled_query_outside_query_cover_subset)
  have cover_le: "card ?Q \<le> ?K"
    by (rule generic_fri_sampled_query_outside_query_cover_card_le_from_fibers)
  have "card ?Q * rounds \<le> ?K * rounds"
    by (rule mult_right_mono[OF cover_le]) simp
  then show ?thesis
    using entries_le by linarith
qed

lemma trace_fri_sampled_query_outside_projection_subset:
  "fst `
    ((trace_fri_sampled_query_bad_pair_union \<inter>
      (fri_query_index_list_space \<times> UNIV)) \<inter>
      (UNIV \<times> (- B)))
    \<subseteq>
    generic_fri_sampled_query_outside_query_cover trace_table_low_degree
      (Not \<circ> trace_table_low_degree) (clength - 1) B"
  unfolding trace_fri_sampled_query_bad_pair_union_def
    generic_fri_sampled_query_outside_query_cover_def
    generic_fri_sampled_query_query_fiber_def
    generic_fri_sampled_query_restricted_bad_pairs_def
    fri_query_challenge_pair_query_fiber_def
  using generic_fri_sampled_query_bad_pair_union_subset_challenge_space
    [of trace_table_low_degree "Not \<circ> trace_table_low_degree" "clength - 1"]
  by force

definition composition_fri_sampled_query_outside_query_cover
  :: "('f \<Rightarrow> 'f list set) \<Rightarrow> nat list set"
where
  "composition_fri_sampled_query_outside_query_cover B =
    (\<Union>dg \<in> (UNIV :: 'f set).
      generic_fri_sampled_query_outside_query_cover
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree)
        (to_nat dg) (B dg))"

lemma composition_fri_sampled_query_outside_query_cover_subset:
  "composition_fri_sampled_query_outside_query_cover B
    \<subseteq> fri_query_index_list_space"
  unfolding composition_fri_sampled_query_outside_query_cover_def
  by (auto intro:
      generic_fri_sampled_query_outside_query_cover_subset[THEN subsetD])

lemma finite_composition_fri_sampled_query_outside_query_cover:
  "finite (composition_fri_sampled_query_outside_query_cover B)"
  using composition_fri_sampled_query_outside_query_cover_subset
  by (rule finite_subset) (rule finite_fri_query_index_list_space)

lemma composition_fri_sampled_query_outside_query_cover_card_le_from_fibers:
  "card (composition_fri_sampled_query_outside_query_cover B)
    \<le>
    (\<Sum>dg \<in> (UNIV :: 'f set).
      \<Sum>challenges \<in>
        fri_challenge_space (fri_round_count_for_degree_bound (to_nat dg)) -
          B dg.
        card
          (generic_fri_sampled_query_query_fiber
            (composition_table_low_degree (to_nat dg))
            (Not \<circ> composition_table_low_degree maxDegree)
            (to_nat dg) challenges))"
proof -
  let ?Q = "composition_fri_sampled_query_outside_query_cover B"
  let ?G = "\<lambda>dg.
    generic_fri_sampled_query_outside_query_cover
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree)
      (to_nat dg) (B dg)"
  let ?K = "\<lambda>dg.
    (\<Sum>challenges \<in>
      fri_challenge_space (fri_round_count_for_degree_bound (to_nat dg)) -
        B dg.
      card
        (generic_fri_sampled_query_query_fiber
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree)
          (to_nat dg) challenges))"
  have "card ?Q \<le> (\<Sum>dg \<in> (UNIV :: 'f set). card (?G dg))"
    unfolding composition_fri_sampled_query_outside_query_cover_def
    by (rule card_UN_le) simp
  also have "... \<le> (\<Sum>dg \<in> (UNIV :: 'f set). ?K dg)"
    by (rule sum_mono)
      (rule generic_fri_sampled_query_outside_query_cover_card_le_from_fibers)
  finally show ?thesis .
qed

lemma composition_fri_sampled_query_outside_query_cover_entries_card_le_from_fibers:
  "card
    (query_index_list_entries
      (composition_fri_sampled_query_outside_query_cover B))
    \<le>
    (\<Sum>dg \<in> (UNIV :: 'f set).
      \<Sum>challenges \<in>
        fri_challenge_space (fri_round_count_for_degree_bound (to_nat dg)) -
          B dg.
        card
          (generic_fri_sampled_query_query_fiber
            (composition_table_low_degree (to_nat dg))
            (Not \<circ> composition_table_low_degree maxDegree)
            (to_nat dg) challenges)) * rounds"
proof -
  let ?Q = "composition_fri_sampled_query_outside_query_cover B"
  let ?K =
    "(\<Sum>dg \<in> (UNIV :: 'f set).
      \<Sum>challenges \<in>
        fri_challenge_space (fri_round_count_for_degree_bound (to_nat dg)) -
          B dg.
        card
          (generic_fri_sampled_query_query_fiber
            (composition_table_low_degree (to_nat dg))
            (Not \<circ> composition_table_low_degree maxDegree)
            (to_nat dg) challenges))"
  have entries_le: "card (query_index_list_entries ?Q) \<le> card ?Q * rounds"
    by (rule query_index_list_entries_card_le)
      (rule finite_composition_fri_sampled_query_outside_query_cover,
       rule composition_fri_sampled_query_outside_query_cover_subset)
  have cover_le: "card ?Q \<le> ?K"
    by (rule composition_fri_sampled_query_outside_query_cover_card_le_from_fibers)
  have "card ?Q * rounds \<le> ?K * rounds"
    by (rule mult_right_mono[OF cover_le]) simp
  then show ?thesis
    using entries_le by linarith
qed

lemma composition_fri_sampled_query_outside_projection_subset:
  "fst `
    ((composition_fri_sampled_query_bad_pair_union dg \<inter>
      (fri_query_index_list_space \<times> UNIV)) \<inter>
      (UNIV \<times> (- B dg)))
    \<subseteq> composition_fri_sampled_query_outside_query_cover B"
  unfolding composition_fri_sampled_query_bad_pair_union_def
    composition_fri_sampled_query_outside_query_cover_def
    generic_fri_sampled_query_outside_query_cover_def
    generic_fri_sampled_query_query_fiber_def
    generic_fri_sampled_query_restricted_bad_pairs_def
    fri_query_challenge_pair_query_fiber_def
  using generic_fri_sampled_query_bad_pair_union_subset_challenge_space
    [of "composition_table_low_degree (to_nat dg)"
      "Not \<circ> composition_table_low_degree maxDegree" "to_nat dg"]
  by force

lemma checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fibers:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      staged_phase_target_error
        (query_index_raw_preimage
          (query_index_list_entries
            (generic_fri_sampled_query_outside_query_cover
              trace_table_low_degree (Not \<circ> trace_table_low_degree)
              (clength - 1) B)))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule
      checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_challenge_cover_and_query_projection
      [OF wf controlled finite_B fresh_bound
        trace_fri_sampled_query_outside_projection_subset])

lemma checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fiber_fraction:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and query_fraction:
    "nnreal
      (card
        (query_index_list_entries
          (generic_fri_sampled_query_outside_query_cover
            trace_table_low_degree (Not \<circ> trace_table_low_degree)
            (clength - 1) B))) /
      nnreal (card query_sample_space) \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      nnreal (staged_attacker_query_budget budgets +
        staged_challenge_query_budget) * Q"
proof -
  let ?Qset =
    "generic_fri_sampled_query_outside_query_cover trace_table_low_degree
      (Not \<circ> trace_table_low_degree) (clength - 1) B"
  have base:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries ?Qset))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fibers
        [OF wf controlled finite_B fresh_bound])
  have subset:
    "query_index_list_entries ?Qset \<subseteq> query_sample_space"
    by (rule query_index_list_entries_subset_query_sample_space)
      (rule generic_fri_sampled_query_outside_query_cover_subset)
  have target_bound:
    "staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries ?Qset))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)
      \<le>
      nnreal (staged_attacker_query_budget budgets +
        staged_challenge_query_budget) * Q"
    by (rule staged_phase_query_index_target_error_query_bound
        [OF query_index_raw_preimage_bound_from_sampler_wellformed subset
          query_fraction])
  show ?thesis
    by (rule order_trans[OF base])
      (use target_bound in simp)
qed

lemma checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fiber_card:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and query_fraction:
    "nnreal
      ((\<Sum>challenges \<in>
        fri_challenge_space (fri_round_count_for_degree_bound (clength - 1)) -
          B.
        card
          (generic_fri_sampled_query_query_fiber trace_table_low_degree
            (Not \<circ> trace_table_low_degree) (clength - 1) challenges)) *
        rounds) /
      nnreal (card query_sample_space) \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      nnreal (staged_attacker_query_budget budgets +
        staged_challenge_query_budget) * Q"
proof (rule
    checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fiber_fraction
    [OF wf controlled finite_B fresh_bound])
  let ?Entries =
    "query_index_list_entries
      (generic_fri_sampled_query_outside_query_cover trace_table_low_degree
        (Not \<circ> trace_table_low_degree) (clength - 1) B)"
  let ?K =
    "(\<Sum>challenges \<in>
      fri_challenge_space (fri_round_count_for_degree_bound (clength - 1)) -
        B.
      card
        (generic_fri_sampled_query_query_fiber trace_table_low_degree
          (Not \<circ> trace_table_low_degree) (clength - 1) challenges)) *
      rounds"
  have card_le: "card ?Entries \<le> ?K"
    by (rule
        generic_fri_sampled_query_outside_query_cover_entries_card_le_from_fibers)
  have "nnreal (card ?Entries) / nnreal (card query_sample_space)
      \<le> nnreal ?K / nnreal (card query_sample_space)"
    using card_le by (rule nnreal_nat_divide_right_mono)
  also have "... \<le> Q"
    by (rule query_fraction)
  finally show
    "nnreal (card ?Entries) / nnreal (card query_sample_space) \<le> Q" .
qed

lemma checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fibers:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      staged_phase_target_error
        (query_index_raw_preimage
          (query_index_list_entries
            (composition_fri_sampled_query_outside_query_cover B)))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule
      checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_challenge_cover_and_query_projection
      [OF wf controlled finite_B fresh_bound
        composition_fri_sampled_query_outside_projection_subset])

lemma checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fiber_fraction:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and query_fraction:
    "nnreal
      (card
        (query_index_list_entries
          (composition_fri_sampled_query_outside_query_cover B))) /
      nnreal (card query_sample_space) \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      nnreal (staged_attacker_query_budget budgets +
        staged_challenge_query_budget) * Q"
proof -
  let ?Qset = "composition_fri_sampled_query_outside_query_cover B"
  have base:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries ?Qset))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fibers
        [OF wf controlled finite_B fresh_bound])
  have subset:
    "query_index_list_entries ?Qset \<subseteq> query_sample_space"
    by (rule query_index_list_entries_subset_query_sample_space)
      (rule composition_fri_sampled_query_outside_query_cover_subset)
  have target_bound:
    "staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries ?Qset))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)
      \<le>
      nnreal (staged_attacker_query_budget budgets +
        staged_challenge_query_budget) * Q"
    by (rule staged_phase_query_index_target_error_query_bound
        [OF query_index_raw_preimage_bound_from_sampler_wellformed subset
          query_fraction])
  show ?thesis
    by (rule order_trans[OF base])
      (use target_bound in simp)
qed

lemma checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fiber_card:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and query_fraction:
    "nnreal
      ((\<Sum>dg \<in> (UNIV :: 'f set).
        \<Sum>challenges \<in>
          fri_challenge_space (fri_round_count_for_degree_bound (to_nat dg)) -
            B dg.
          card
            (generic_fri_sampled_query_query_fiber
              (composition_table_low_degree (to_nat dg))
              (Not \<circ> composition_table_low_degree maxDegree)
              (to_nat dg) challenges)) * rounds) /
      nnreal (card query_sample_space) \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      nnreal (staged_attacker_query_budget budgets +
        staged_challenge_query_budget) * Q"
proof (rule
    checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_outside_fiber_fraction
    [OF wf controlled finite_B fresh_bound])
  let ?Entries =
    "query_index_list_entries
      (composition_fri_sampled_query_outside_query_cover B)"
  let ?K =
    "(\<Sum>dg \<in> (UNIV :: 'f set).
      \<Sum>challenges \<in>
        fri_challenge_space (fri_round_count_for_degree_bound (to_nat dg)) -
          B dg.
        card
          (generic_fri_sampled_query_query_fiber
            (composition_table_low_degree (to_nat dg))
            (Not \<circ> composition_table_low_degree maxDegree)
            (to_nat dg) challenges)) * rounds"
  have card_le: "card ?Entries \<le> ?K"
    by (rule
        composition_fri_sampled_query_outside_query_cover_entries_card_le_from_fibers)
  have "nnreal (card ?Entries) / nnreal (card query_sample_space)
      \<le> nnreal ?K / nnreal (card query_sample_space)"
    using card_le by (rule nnreal_nat_divide_right_mono)
  also have "... \<le> Q"
    by (rule query_fraction)
  finally show
    "nnreal (card ?Entries) / nnreal (card query_sample_space) \<le> Q" .
qed

end

end
