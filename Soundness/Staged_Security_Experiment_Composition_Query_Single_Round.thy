(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Single_Round.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Single_Round
  imports Staged_Security_Experiment_Composition_Query_Binding_Gap
begin

text \<open>
  Same-run single-round candidate binding for the composition query branch.

  The actual-alpha diagnostic events in the previous layer intentionally record
  enough data to relate a candidate pair to a query-prefix target, but they are
  too broad for Merkle path-output accounting because the query-prefix branch
  is existential.  This layer states the single-round binding gap directly over
  the query-prefix data-state experiment, where prefix state, sampled query,
  verifier continuation, and authenticated openings are from the same run.
\<close>

context soundness
begin

definition checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
where
  "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
      i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state), continuation),
        final_state) \<Rightarrow>
        checked_staged_query_prefix_dynamic_index_hit
          (staged_query_prefix_single_round_header_supported_query_target i)
          (Some (((prefix, prefix_state), raw), raw_state)))"

lemma checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at_iff_dynamic:
  "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
      i out \<longleftrightarrow>
   checked_staged_security_with_query_prefix_dynamic_index_hit
      (staged_query_prefix_single_round_header_supported_query_target i) out"
  unfolding
    checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at_def
    checked_staged_security_with_query_prefix_dynamic_index_hit_def
  by (cases out) (auto split: prod.splits)

lemma checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at_bound:
  assumes prefix_bound:
      "wp_event (checked_staged_query_prefix_receive_with_state A i)
        (checked_staged_query_prefix_dynamic_index_hit
          (staged_query_prefix_single_round_header_supported_query_target i))
        adversary_initial_state \<le> B"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
        i)
      adversary_initial_state \<le> B"
  unfolding
    checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at_iff_dynamic
  by (rule checked_staged_security_with_query_prefix_dynamic_index_hit_bound
      [OF prefix_bound])

lemma staged_query_prefix_candidate_pair_query_target_from_prefix_empty_if_all_queries_consistent:
  assumes all_queries:
    "all_queries_consistent trace_table composition_table (sqp_alphas prefix)"
  shows
    "staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
      composition_table prefix prefix_state = {}"
  using all_queries
  unfolding staged_query_prefix_candidate_pair_query_target_from_prefix_def
    query_sampling_success_space_def
  by simp

lemma checked_staged_query_prefix_candidate_pair_hit_from_prefix_false_if_all_queries_consistent:
  assumes all_queries:
    "all_queries_consistent trace_table composition_table (sqp_alphas prefix)"
  shows
    "\<not> checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
        composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
  using
    staged_query_prefix_candidate_pair_query_target_from_prefix_empty_if_all_queries_consistent
      [OF all_queries, of prefix_state]
  unfolding checked_staged_query_prefix_dynamic_index_hit_def
  by simp

definition checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
where
  "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
      trace_openings composition_openings trace_table composition_table i out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<and>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<and>
        (trace_table, composition_table) \<notin>
          query_header_supported_single_round_partial_table_candidates
            prefix_state
            (sqp_trace_root prefix)
            (sqp_trace_fri_roots prefix)
            (sqp_trace_final prefix)
            (sqp_alphas prefix)
            (sqp_degree prefix)
            (sqp_composition_fri_roots prefix)
            (sqp_composition_final prefix)
            i)"

definition checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
where
  "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
          trace_openings composition_openings i out \<and>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<and>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<and>
        (trace_table, composition_table) \<notin>
          query_header_supported_single_round_partial_table_candidates
            prefix_state
            (sqp_trace_root prefix)
            (sqp_trace_fri_roots prefix)
            (sqp_trace_final prefix)
            (sqp_alphas prefix)
            (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i)"

definition checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at
where
  "checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out
      \<longleftrightarrow>
    checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
      trace_openings composition_openings trace_table composition_table i out \<and>
    checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
      trace_openings composition_openings i out"

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_iff_fixed_header_component:
  "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out
    \<longleftrightarrow>
   checked_staged_security_with_query_prefix_fixed_header_component
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
  unfolding
    checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at_def
    checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side_def
    checked_staged_security_with_query_prefix_fixed_header_component_def
  by (cases out) (auto split: prod.splits)

lemma checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_imp_current_prefix_authenticated:
  assumes gap:
    "checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
      i out"
  using gap
  unfolding
    checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at_def
    checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_def
  by blast

lemma checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_bound_from_dynamic_target:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event (checked_staged_query_prefix_receive_with_state A i)
        (checked_staged_query_prefix_dynamic_index_hit
          staged_query_prefix_prefix_authenticated_opening_target)
        adversary_initial_state \<le> B"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le> B"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_imp_current_prefix_authenticated)
  have current_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i)
      adversary_initial_state \<le> B"
    by (rule
        checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_dynamic_target
        [OF wf controlled i_bound prefix_bound])
  show ?thesis
    by (rule order_trans[OF event_le current_bound])
qed

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_imp_single_round_header_target_or_binding_gap:
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
     checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  from hit have opening_target:
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
    have
      "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at_def
      using hit trace_candidate comp_candidate False by simp
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_current_imp_prefix_gap_or_opening_path_output_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and current:
      "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
          trace_openings composition_openings trace_table composition_table i)
        trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out \<or>
     checked_staged_security_with_query_prefix_opening_path_output_hit
      trace_openings composition_openings out"
proof -
  have side:
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
      trace_openings composition_openings trace_table composition_table i out"
    and current_hit:
    "checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i out"
    using current
    unfolding
      checked_staged_security_with_query_prefix_fixed_current_authenticated_component_def
      checked_staged_security_with_query_prefix_fixed_header_component_def
    by simp_all
  have split:
    "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out"
    by (rule
        checked_staged_security_with_query_prefix_fixed_current_authenticated_component_imp_prefix_or_path_output_on_support
        [OF wf controlled i_bound support current])
  then show ?thesis
  proof
    assume prefix:
      "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i out"
    have
      "checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i out"
      unfolding
        checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at_def
      using side prefix by simp
    then show ?thesis by simp
  next
    assume
      "checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out"
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_imp_current_or_path_output_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and gap:
      "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
proof -
  have fixed:
    "checked_staged_security_with_query_prefix_fixed_header_component
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
    using gap
    unfolding
      checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_iff_fixed_header_component
    .
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_imp_current_or_witness_path_output_on_support
        [OF wf controlled i_bound support fixed])
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_imp_prefix_gap_or_path_outputs_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and gap:
      "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out \<or>
     checked_staged_security_with_query_prefix_opening_path_output_hit
      trace_openings composition_openings out \<or>
     checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
proof -
  have split:
    "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
    by (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_imp_current_or_path_output_on_support
        [OF wf controlled i_bound support gap])
  then show ?thesis
  proof
    assume current:
      "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
          trace_openings composition_openings trace_table composition_table i)
        trace_openings composition_openings i out"
    have
      "checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i out \<or>
       checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out"
      by (rule
          checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_current_imp_prefix_gap_or_opening_path_output_on_support
          [OF wf controlled i_bound support current])
    then show ?thesis by blast
  next
    assume
      "checked_staged_security_with_query_prefix_header_witness_path_output_hit
        (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
          trace_openings composition_openings trace_table composition_table i)
        trace_openings composition_openings i out"
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_bound_from_prefix_target_and_path_outputs:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event (checked_staged_query_prefix_receive_with_state A i)
        (checked_staged_query_prefix_dynamic_index_hit
          staged_query_prefix_prefix_authenticated_opening_target)
        adversary_initial_state \<le> P"
    and opening_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_opening_path_output_hit
          trace_openings composition_openings)
        adversary_initial_state \<le> Q"
    and witness_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
            trace_openings composition_openings trace_table composition_table i)
          trace_openings composition_openings i)
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le> P + Q + R"
proof -
  let ?m =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?prefix =
    "checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i"
  let ?open_path =
    "checked_staged_security_with_query_prefix_opening_path_output_hit
      trace_openings composition_openings"
  let ?witness_path =
    "checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i"
  have event_le:
    "wp_event ?m
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
     wp_event ?m
      (\<lambda>out. ?prefix out \<or> ?open_path out \<or> ?witness_path out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_imp_prefix_gap_or_path_outputs_on_support
        [OF wf controlled i_bound])
  have union_le:
    "wp_event ?m
      (\<lambda>out. ?prefix out \<or> ?open_path out \<or> ?witness_path out)
      adversary_initial_state \<le>
     wp_event ?m ?prefix adversary_initial_state +
     (wp_event ?m ?open_path adversary_initial_state +
      wp_event ?m ?witness_path adversary_initial_state)"
  proof -
    have
      "wp_event ?m
        (\<lambda>out. ?prefix out \<or> ?open_path out \<or> ?witness_path out)
        adversary_initial_state \<le>
       wp_event ?m ?prefix adversary_initial_state +
       wp_event ?m
        (\<lambda>out. ?open_path out \<or> ?witness_path out)
        adversary_initial_state"
      by (rule wp_event_union_bound)
    also have
      "... \<le>
       wp_event ?m ?prefix adversary_initial_state +
       (wp_event ?m ?open_path adversary_initial_state +
        wp_event ?m ?witness_path adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis .
  qed
  have prefix_gap_bound:
    "wp_event ?m ?prefix adversary_initial_state \<le> P"
    by (rule
        checked_staged_security_with_query_prefix_prefix_single_round_candidate_binding_gap_bound_from_dynamic_target
        [OF wf controlled i_bound prefix_bound])
  have sum_bound:
    "wp_event ?m ?prefix adversary_initial_state +
      (wp_event ?m ?open_path adversary_initial_state +
       wp_event ?m ?witness_path adversary_initial_state) \<le> P + Q + R"
  proof -
    have path_sum_bound:
      "wp_event ?m ?open_path adversary_initial_state +
       wp_event ?m ?witness_path adversary_initial_state \<le> Q + R"
      by (rule add_mono[OF opening_path_bound witness_path_bound])
    have
      "wp_event ?m ?prefix adversary_initial_state +
        (wp_event ?m ?open_path adversary_initial_state +
         wp_event ?m ?witness_path adversary_initial_state) \<le> P + (Q + R)"
      by (rule add_mono[OF prefix_gap_bound path_sum_bound])
    then show ?thesis
      by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF event_le order_trans[OF union_le sum_bound]])
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_bound_from_witness_path_output_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
            trace_openings composition_openings trace_table composition_table i)
          trace_openings composition_openings i)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size + Q"
proof -
  have event_eq:
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i =
     checked_staged_security_with_query_prefix_fixed_header_component
        (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
          trace_openings composition_openings trace_table composition_table i)
        trace_openings composition_openings i"
    by (rule ext)
      (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_iff_fixed_header_component)
  show ?thesis
    unfolding event_eq
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_bound_from_witness_path_output_and_budgets
        [OF wf controlled i_bound path_bound])
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have event_eq:
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i =
     checked_staged_security_with_query_prefix_fixed_header_component
        (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
          trace_openings composition_openings trace_table composition_table i)
        trace_openings composition_openings i"
    by (rule ext)
      (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_iff_fixed_header_component)
  show ?thesis
    unfolding event_eq
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_bound_from_budgets
        [OF wf controlled i_bound])
qed

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_bound_from_target_and_fixed_gap:
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
       nnreal (query_raw_preimage_card_envelope 1) / nnreal size)"
proof -
  let ?m =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?target =
    "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
      i"
  let ?gap =
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
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
            checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_imp_single_round_header_target_or_binding_gap
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
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
    by (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_bound_from_budgets
        [OF wf controlled i_bound])
  have sum_bound:
    "wp_event ?m ?target adversary_initial_state +
      wp_event ?m ?gap adversary_initial_state \<le>
     T +
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
       nnreal (query_raw_preimage_card_envelope 1) / nnreal size)"
    by (rule add_mono[OF target_bound gap_bound])
  show ?thesis
    by (rule order_trans[OF event_le order_trans[OF union_le sum_bound]])
qed

lemma checked_staged_security_with_query_prefix_verifier_unsupported_witness_gap_imp_header_witness_path_output:
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
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and notin_prefix:
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
    and notin_verifier:
      "(trace_table, composition_table) \<notin>
        query_header_supported_single_round_partial_table_candidates
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)
          i"
  shows
    "checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from query_header_supported_partial_opening_witnessesE[OF witness]
  obtain witness_result witness_state rest where comp_nonempty:
      "staged_composition_fri_roots data \<noteq> []"
    and outcome:
      "Some (witness_result, witness_state) \<in>
        set_dist (execute verify_monad ?s)"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings witness_state"
    and comp_auth:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings witness_state"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        rest"
    by blast
  have ext: "?s \<le> witness_state"
    by (rule verify_monad_hash_extends[OF outcome])
  have trace_pull:
    "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings ?s \<or>
     (\<exists>opn \<in> set trace_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state
          (staged_trace_root data) (scale * clength)
          (opening_index opn) (opening_value opn) (opening_path opn))
        ?s witness_state)"
    by (rule partial_authenticated_table_pullback_or_new_output_hit
        [OF ext trace_auth])
  have comp_pull:
    "partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings ?s \<or>
     (\<exists>opn \<in> set composition_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state
          (hd (staged_composition_fri_roots data)) (scale * clength)
          (opening_index opn) (opening_value opn) (opening_path opn))
        ?s witness_state)"
    by (rule partial_authenticated_table_pullback_or_new_output_hit
        [OF ext comp_auth])
  have path:
    "(\<exists>opn \<in> set trace_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state
          (staged_trace_root data) (scale * clength)
          (opening_index opn) (opening_value opn) (opening_path opn))
        ?s witness_state) \<or>
     (\<exists>opn \<in> set composition_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state
          (hd (staged_composition_fri_roots data)) (scale * clength)
          (opening_index opn) (opening_value opn) (opening_path opn))
        ?s witness_state)"
  proof (rule ccontr)
    assume not_path: "\<not> ?thesis"
    have trace_on_s:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings ?s"
      using trace_pull not_path by blast
    have comp_on_s:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings ?s"
      using comp_pull not_path by blast
    show False
      by (rule
          query_header_supported_single_round_partial_table_candidate_notin_contradicts
          [OF notin_verifier comp_nonempty trace_on_s comp_on_s
            trace_candidate comp_candidate header])
  qed
  have side:
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    unfolding
      checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side_def
    using trace_candidate comp_candidate notin_prefix by simp
  show ?thesis
    unfolding
      checked_staged_security_with_query_prefix_header_witness_path_output_hit_def
    using side comp_nonempty outcome header path
    apply (simp add: Let_def)
    apply (intro exI[of _ witness_result] exI[of _ witness_state]
        exI[of _ rest])
    apply auto
    done
qed

lemma checked_staged_security_with_query_prefix_witness_gap_side_imp_verifier_supported_or_header_witness_path_output:
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
    and side:
      "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "(trace_table, composition_table) \<in>
      query_header_supported_single_round_partial_table_candidates
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<or>
     checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof (cases
    "(trace_table, composition_table) \<in>
      query_header_supported_single_round_partial_table_candidates
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i")
  case True
  then show ?thesis by simp
next
  case notin_verifier: False
  from side have trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and notin_prefix:
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
    unfolding
      checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side_def
    by simp_all
  have
    "checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    by (rule
        checked_staged_security_with_query_prefix_verifier_unsupported_witness_gap_imp_header_witness_path_output
        [OF witness trace_candidate comp_candidate notin_prefix notin_verifier])
  then show ?thesis by simp
qed

definition checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
where
  "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
      trace_openings composition_openings trace_table composition_table i out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
          trace_openings composition_openings trace_table composition_table i
          out \<and>
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
            (staged_composition_final data))"

definition checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
where
  "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i out
      \<longleftrightarrow>
    checked_staged_security_with_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table) out \<and>
    checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
      trace_openings composition_openings trace_table composition_table i out"

lemma checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_imp_dynamic_hit:
  assumes gap:
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table) out"
  using gap
  unfolding
    checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_def
  by simp

lemma checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_imp_witness_side:
  assumes gap:
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
      trace_openings composition_openings trace_table composition_table i out"
  using gap
  unfolding
    checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at_def
  by simp

definition checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
where
  "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
      trace_openings composition_openings trace_table composition_table i out
      \<longleftrightarrow>
    checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out \<and>
    checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
      trace_openings composition_openings trace_table composition_table i out"

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_imp_gap:
  assumes hit:
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
      trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out"
  using hit
  unfolding
    checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_def
  by simp

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_imp_witness_side:
  assumes hit:
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
      trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
      trace_openings composition_openings trace_table composition_table i out"
  using hit
  unfolding
    checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_def
  by simp

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_imp_gap)
  have gap_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
    by (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_bound_from_budgets
        [OF wf controlled i_bound])
  show ?thesis
    by (rule order_trans[OF event_le gap_bound])
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_bound_from_witness_side:
  assumes side_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
          trace_openings composition_openings trace_table composition_table i)
        adversary_initial_state \<le> S"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le> S"
  by (rule order_trans[OF _ side_bound])
    (rule wp_event_mono,
      rule checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_imp_witness_side)

definition checked_staged_security_with_query_prefix_single_round_verifier_supported_gap_witness_side
where
  "checked_staged_security_with_query_prefix_single_round_verifier_supported_gap_witness_side
      trace_openings composition_openings trace_table composition_table i out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
          trace_openings composition_openings trace_table composition_table i
          out \<and>
        (trace_table, composition_table) \<in>
          query_header_supported_single_round_partial_table_candidates
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)
            i)"

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_imp_supported_or_path_output:
  assumes hit:
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
      trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_single_round_verifier_supported_gap_witness_side
      trace_openings composition_openings trace_table composition_table i out \<or>
     checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state)"
    by (cases packed) (auto split: prod.splits)
  from hit have side:
      "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i
        out"
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
    unfolding out_eq
      checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_def
    by simp_all
  have split:
    "(trace_table, composition_table) \<in>
      query_header_supported_single_round_partial_table_candidates
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<or>
     checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
    unfolding out_eq
    by (rule
        checked_staged_security_with_query_prefix_witness_gap_side_imp_verifier_supported_or_header_witness_path_output
        [OF witness side[unfolded out_eq]])
  then show ?thesis
  proof
    assume supported:
      "(trace_table, composition_table) \<in>
        query_header_supported_single_round_partial_table_candidates
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)
          i"
    have
      "checked_staged_security_with_query_prefix_single_round_verifier_supported_gap_witness_side
        trace_openings composition_openings trace_table composition_table i out"
      unfolding out_eq
        checked_staged_security_with_query_prefix_single_round_verifier_supported_gap_witness_side_def
      using hit[unfolded out_eq] supported by simp
    then show ?thesis by simp
  next
    assume
      "checked_staged_security_with_query_prefix_header_witness_path_output_hit
        (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
          trace_openings composition_openings trace_table composition_table i)
        trace_openings composition_openings i out"
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_bound_from_supported_and_path_output:
  assumes supported_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_single_round_verifier_supported_gap_witness_side
          trace_openings composition_openings trace_table composition_table i)
        adversary_initial_state \<le> S"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
            trace_openings composition_openings trace_table composition_table i)
          trace_openings composition_openings i)
        adversary_initial_state \<le> P"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le> S + P"
proof -
  let ?m =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?W =
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
      trace_openings composition_openings trace_table composition_table i"
  let ?S =
    "checked_staged_security_with_query_prefix_single_round_verifier_supported_gap_witness_side
      trace_openings composition_openings trace_table composition_table i"
  let ?P =
    "checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i"
  have event_le:
    "wp_event ?m ?W adversary_initial_state \<le>
     wp_event ?m (\<lambda>out. ?S out \<or> ?P out) adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_imp_supported_or_path_output)
  have union_le:
    "wp_event ?m (\<lambda>out. ?S out \<or> ?P out) adversary_initial_state \<le>
     wp_event ?m ?S adversary_initial_state +
     wp_event ?m ?P adversary_initial_state"
    by (rule wp_event_union_bound)
  have sum_le:
    "wp_event ?m ?S adversary_initial_state +
     wp_event ?m ?P adversary_initial_state \<le> S + P"
    by (rule add_mono[OF supported_bound path_bound])
  show ?thesis
    by (rule order_trans[OF event_le order_trans[OF union_le sum_le]])
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_bound_from_supported_and_transcript:
  assumes supported_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_single_round_verifier_supported_gap_witness_side
          trace_openings composition_openings trace_table composition_table i)
        adversary_initial_state \<le> S"
    and transcript_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_hit
          (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
            trace_openings composition_openings trace_table composition_table i))
        adversary_initial_state \<le> P"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le> S + P"
proof -
  let ?m =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?side =
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
      trace_openings composition_openings trace_table composition_table i"
  have path_bound:
    "wp_event ?m
      (checked_staged_security_with_query_prefix_header_witness_path_output_hit
        ?side trace_openings composition_openings i)
      adversary_initial_state \<le> P"
  proof -
    have
      "wp_event ?m
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          ?side trace_openings composition_openings i)
        adversary_initial_state \<le>
       wp_event ?m
        (checked_staged_security_with_query_prefix_header_witness_transcript_hit
          ?side)
        adversary_initial_state"
      by (rule wp_event_mono)
        (rule
          checked_staged_security_with_query_prefix_header_witness_path_output_imp_transcript_hit)
    then show ?thesis
      by (rule order_trans[OF _ transcript_bound])
  qed
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_bound_from_supported_and_path_output
        [OF supported_bound path_bound])
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_bound_from_supported_pre_and_new:
  assumes supported_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_single_round_verifier_supported_gap_witness_side
          trace_openings composition_openings trace_table composition_table i)
        adversary_initial_state \<le> S"
    and pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
          (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
            trace_openings composition_openings trace_table composition_table i))
        adversary_initial_state \<le> R"
    and new_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
          (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
            trace_openings composition_openings trace_table composition_table i))
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le> S + (R + Q)"
proof -
  let ?m =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?side =
    "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
      trace_openings composition_openings trace_table composition_table i"
  have transcript_bound:
    "wp_event ?m
      (checked_staged_security_with_query_prefix_header_witness_transcript_hit
        ?side)
      adversary_initial_state \<le> R + Q"
  proof -
    have event_le:
      "wp_event ?m
        (checked_staged_security_with_query_prefix_header_witness_transcript_hit
          ?side)
        adversary_initial_state \<le>
       wp_event ?m
        (\<lambda>out.
          checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
            ?side out \<or>
          checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
            ?side out)
        adversary_initial_state"
      by (rule wp_event_mono)
        (rule
          checked_staged_security_with_query_prefix_header_witness_transcript_hit_imp_pre_or_new)
    have union_le:
      "wp_event ?m
        (\<lambda>out.
          checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
            ?side out \<or>
          checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
            ?side out)
        adversary_initial_state \<le>
       wp_event ?m
        (checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
          ?side)
        adversary_initial_state +
       wp_event ?m
        (checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
          ?side)
        adversary_initial_state"
      by (rule wp_event_union_bound)
    have sum_le:
      "wp_event ?m
        (checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
          ?side)
        adversary_initial_state +
       wp_event ?m
        (checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
          ?side)
        adversary_initial_state \<le> R + Q"
      by (rule add_mono[OF pre_bound new_bound])
    show ?thesis
      by (rule order_trans[OF event_le order_trans[OF union_le sum_le]])
  qed
  have bound:
    "wp_event ?m
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le> S + (R + Q)"
    by (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_bound_from_supported_and_transcript
        [OF supported_bound transcript_bound])
  then show ?thesis .
qed

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_bound_from_supported_pre_and_new:
  assumes supported_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_single_round_verifier_supported_gap_witness_side
          trace_openings composition_openings trace_table composition_table i)
        adversary_initial_state \<le> S"
    and pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
          (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
            trace_openings composition_openings trace_table composition_table i))
        adversary_initial_state \<le> R"
    and new_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
          (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_side
            trace_openings composition_openings trace_table composition_table i))
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le> S + (R + Q)"
proof -
  have side_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le> S + (R + Q)"
    by (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_side_bound_from_supported_pre_and_new
        [OF supported_bound pre_bound new_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at_bound_from_witness_side
        [OF side_bound])
qed

definition checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_exists
where
  "checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_exists
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (\<exists>result' final_state'.
          partial_merkle_inconsistency_bad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (Some (result', final_state'))))"

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_imp_partial_merkle_event_or_single_round_components:
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
    "checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_exists
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  using
    checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_imp_partial_merkle_or_single_round_header_target_or_gap_witness
      [OF hit i_bound trace_low comp_low not_all]
  unfolding
    checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_exists_def
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_bound_from_single_round_components:
  assumes split:
      "\<And>out.
        out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
                A)
              adversary_initial_state) \<Longrightarrow>
        checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
          i A out \<Longrightarrow>
        checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_exists
          out \<or>
        checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
          i A out \<or>
        checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
          i A out"
    and partial_merkle_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_exists
        adversary_initial_state \<le> P"
    and target_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
          i A)
        adversary_initial_state \<le> Q"
    and gap_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
          i A)
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
        i A)
      adversary_initial_state \<le> P + Q + R"
proof -
  let ?m =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?pm =
    "checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_exists"
  let ?target =
    "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
      i A"
  let ?gap =
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
      i A"
  have event_le:
    "wp_event ?m
      (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
        i A)
      adversary_initial_state \<le>
     wp_event ?m (\<lambda>out. ?pm out \<or> ?target out \<or> ?gap out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule split)
  have union_le:
    "wp_event ?m (\<lambda>out. ?pm out \<or> ?target out \<or> ?gap out)
      adversary_initial_state \<le>
     wp_event ?m ?pm adversary_initial_state +
      (wp_event ?m ?target adversary_initial_state +
       wp_event ?m ?gap adversary_initial_state)"
  proof -
    have
      "wp_event ?m (\<lambda>out. ?pm out \<or> ?target out \<or> ?gap out)
        adversary_initial_state \<le>
       wp_event ?m ?pm adversary_initial_state +
        wp_event ?m (\<lambda>out. ?target out \<or> ?gap out)
          adversary_initial_state"
      by (rule wp_event_union_bound)
    also have
      "... \<le>
       wp_event ?m ?pm adversary_initial_state +
        (wp_event ?m ?target adversary_initial_state +
         wp_event ?m ?gap adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis .
  qed
  have sum_bound:
    "wp_event ?m ?pm adversary_initial_state +
      (wp_event ?m ?target adversary_initial_state +
       wp_event ?m ?gap adversary_initial_state) \<le> P + Q + R"
  proof -
    have
      "wp_event ?m ?target adversary_initial_state +
       wp_event ?m ?gap adversary_initial_state \<le> Q + R"
      by (rule add_mono[OF target_bound gap_bound])
    then have
      "wp_event ?m ?pm adversary_initial_state +
        (wp_event ?m ?target adversary_initial_state +
         wp_event ?m ?gap adversary_initial_state) \<le> P + (Q + R)"
      by (rule add_mono[OF partial_merkle_bound])
    then show ?thesis
      by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF event_le order_trans[OF union_le sum_bound]])
qed

end

end
