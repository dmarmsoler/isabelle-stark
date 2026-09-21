theory Soundness_FRI_RO_Actual_Query_Obstruction_Bounds
  imports Soundness_FRI_RO_Actual_Query_Obstruction_Events
begin

context soundness
begin

definition
  ro_absorb_checked_staged_security_with_first_root_trace_challenge_list_hit
where
  "ro_absorb_checked_staged_security_with_first_root_trace_challenge_list_hit
      B out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        staged_trace_fri_challenges data \<in> B)"

lemma
  ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair_split:
  assumes projection:
    "fst ` (generic_fri_sampled_query_bad_pair_union
        trace_table_low_degree (Not \<circ> trace_table_low_degree)
        (clength - 1) \<inter> (UNIV \<times> (- B))) \<subseteq> Q"
    and hit:
      "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
        out"
  shows
    "ro_absorb_checked_staged_security_with_first_root_trace_challenge_list_hit
        B out \<or>
     ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
       (\<lambda>_ _. Q) out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair_def
    by simp
next
  case (Some a)
  obtain prefix prefix_state data query_start raws query_states
      attacker_state result final_state where
    a:
      "a =
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state)"
    by (cases a) auto
  show ?thesis
  proof (cases "staged_trace_fri_challenges data \<in> B")
    case True
    then show ?thesis
      using Some a
      unfolding
        ro_absorb_checked_staged_security_with_first_root_trace_challenge_list_hit_def
      by simp
  next
    case False
    have pair_hit:
      "(map (\<lambda>raw. index (to_nat raw)) raws,
          staged_trace_fri_challenges data)
        \<in> generic_fri_sampled_query_bad_pair_union
            trace_table_low_degree (Not \<circ> trace_table_low_degree)
            (clength - 1)"
      using hit Some a
      unfolding
        ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair_def
      by simp
    have pair_outside:
      "(map (\<lambda>raw. index (to_nat raw)) raws,
          staged_trace_fri_challenges data)
        \<in> generic_fri_sampled_query_bad_pair_union
            trace_table_low_degree (Not \<circ> trace_table_low_degree)
            (clength - 1) \<inter> (UNIV \<times> (- B))"
      using pair_hit False by simp
    have in_projection_raw:
      "fst (map (\<lambda>raw. index (to_nat raw)) raws,
          staged_trace_fri_challenges data)
        \<in> fst ` (generic_fri_sampled_query_bad_pair_union
            trace_table_low_degree (Not \<circ> trace_table_low_degree)
            (clength - 1) \<inter> (UNIV \<times> (- B)))"
      by (rule imageI[OF pair_outside])
    have in_projection:
      "map (\<lambda>raw. index (to_nat raw)) raws
        \<in> fst ` (generic_fri_sampled_query_bad_pair_union
            trace_table_low_degree (Not \<circ> trace_table_low_degree)
            (clength - 1) \<inter> (UNIV \<times> (- B)))"
      using in_projection_raw by simp
    have in_Q: "map (\<lambda>raw. index (to_nat raw)) raws \<in> Q"
      using projection in_projection by blast
    then show ?thesis
      using Some a
      unfolding
        ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit_def
        ro_checked_staged_first_root_dependent_actual_query_index_list_hit_def
      by simp
  qed
qed

lemma
  wp_ro_absorb_checked_staged_security_with_first_root_constant_actual_query_index_list_hit_eq:
  assumes nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
        (\<lambda>_ _. Q))
      s =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit Q)
      s"
proof -
  let ?project =
    "\<lambda>(((prefix_with_state, data, query_start, raws, query_states),
          attacker_state), result).
      (((data, query_start, raws, query_states), attacker_state), result)"
  have event_map:
    "(\<lambda>out. case out of
        None \<Rightarrow>
          ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
            Q None
      | Some (x, t) \<Rightarrow>
          ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
            Q (Some (?project x, t))) =
      ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
        (\<lambda>_ _. Q)"
    unfolding
      ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit_def
      ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit_def
      ro_checked_staged_first_root_dependent_actual_query_index_list_hit_def
    by (rule ext) (auto split: option.splits prod.splits)
  have mapped:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A \<bind>
        (\<lambda>x. return (?project x)))
      (ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit Q)
      s =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
        (\<lambda>_ _. Q))
      s"
    by (subst wp_event_bind_return_map) (simp only: event_map)
  have projection:
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A \<bind>
        (\<lambda>x. return (?project x)) =
      ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
    using
      ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection[
        OF nonempty, of A]
    by (simp add: split_def)
  show ?thesis
    using mapped
    unfolding projection
    by simp
qed

lemma
  wp_ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair_challenge_query_split:
  assumes projection:
    "fst ` (generic_fri_sampled_query_bad_pair_union
        trace_table_low_degree (Not \<circ> trace_table_low_degree)
        (clength - 1) \<inter> (UNIV \<times> (- B))) \<subseteq> Q"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
      s \<le>
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (ro_absorb_checked_staged_security_with_first_root_trace_challenge_list_hit B)
      s +
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
        (\<lambda>_ _. Q))
      s"
proof -
  let ?M =
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
  have
    "wp_event ?M
        ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
        s \<le>
      wp_event ?M
        (\<lambda>out.
          ro_absorb_checked_staged_security_with_first_root_trace_challenge_list_hit
            B out \<or>
          ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
            (\<lambda>_ _. Q) out)
        s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M s)"
      and hit:
        "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
          out"
    show
      "ro_absorb_checked_staged_security_with_first_root_trace_challenge_list_hit
          B out \<or>
       ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
          (\<lambda>_ _. Q) out"
      by (rule
          ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair_split[
            OF projection hit])
  qed
  also have "... \<le>
    wp_event ?M
      (ro_absorb_checked_staged_security_with_first_root_trace_challenge_list_hit B)
      s +
    wp_event ?M
      (ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
        (\<lambda>_ _. Q))
      s"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

definition active_route_ro_absorb_first_root_trace_challenge_list_error_for
  :: "'f staged_adversary \<Rightarrow> 'f list set \<Rightarrow> prob"
where
  "active_route_ro_absorb_first_root_trace_challenge_list_error_for A B =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (ro_absorb_checked_staged_security_with_first_root_trace_challenge_list_hit B)
      adversary_initial_state"

lemma active_route_ro_absorb_first_root_trace_sampled_bad_pair_challenge_query_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and projection:
      "fst ` (generic_fri_sampled_query_bad_pair_union
          trace_table_low_degree (Not \<circ> trace_table_low_degree)
          (clength - 1) \<inter> (UNIV \<times> (- B))) \<subseteq> Q"
  shows
    "active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for A \<le>
      active_route_ro_absorb_first_root_trace_challenge_list_error_for A B +
      nnreal (card (query_index_raw_list_preimage Q)) *
          (1 / nnreal size) ^ rounds +
        hash_relation_budget_value
          (query_index_raw_list_relation_fiber_bound Q)
          (ro_checked_staged_transcript_hash_query_budget_for budgets)"
proof -
  have split:
    "active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for A \<le>
      active_route_ro_absorb_first_root_trace_challenge_list_error_for A B +
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
        (ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
          (\<lambda>_ _. Q))
        adversary_initial_state"
    unfolding
      active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for_def
      active_route_ro_absorb_first_root_trace_challenge_list_error_for_def
    by (rule
        wp_ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair_challenge_query_split[
          OF projection])
  have query:
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
        (ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
          (\<lambda>_ _. Q))
        adversary_initial_state \<le>
      nnreal (card (query_index_raw_list_preimage Q)) *
          (1 / nnreal size) ^ rounds +
        hash_relation_budget_value
          (query_index_raw_list_relation_fiber_bound Q)
          (ro_checked_staged_transcript_hash_query_budget_for budgets)"
    unfolding
      wp_ro_absorb_checked_staged_security_with_first_root_constant_actual_query_index_list_hit_eq[
        OF nonempty]
    by (rule
        ro_absorb_checked_staged_security_with_query_witnesses_actual_hit_bound[
          OF wf controlled])
  show ?thesis
    by (rule order_trans[OF split])
      (use query in \<open>simp add: add.assoc\<close>)
qed

definition trace_sampled_bad_actual_query_index_lists :: "nat list set"
where
  "trace_sampled_bad_actual_query_index_lists =
    fst ` generic_fri_sampled_query_bad_pair_union
      trace_table_low_degree (Not \<circ> trace_table_low_degree) (clength - 1)"

definition trace_sampled_bad_actual_query_parameter_bound
  :: "staged_budgets \<Rightarrow> prob"
where
  "trace_sampled_bad_actual_query_parameter_bound budgets =
    nnreal
      (card
        (query_index_raw_list_preimage
          trace_sampled_bad_actual_query_index_lists)) *
      (1 / nnreal size) ^ rounds +
    hash_relation_budget_value
      (query_index_raw_list_relation_fiber_bound
        trace_sampled_bad_actual_query_index_lists)
      (ro_checked_staged_transcript_hash_query_budget_for budgets)"

lemma active_route_ro_absorb_first_root_trace_sampled_bad_pair_parameter_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for A
      \<le> trace_sampled_bad_actual_query_parameter_bound budgets"
proof -
  have projection:
    "fst ` (generic_fri_sampled_query_bad_pair_union
        trace_table_low_degree (Not \<circ> trace_table_low_degree)
        (clength - 1) \<inter> (UNIV \<times> (- ({} :: 'f list set))))
      \<subseteq> trace_sampled_bad_actual_query_index_lists"
    unfolding trace_sampled_bad_actual_query_index_lists_def
    by auto
  have bound:
    "active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for A \<le>
      active_route_ro_absorb_first_root_trace_challenge_list_error_for
        A ({} :: 'f list set) +
      nnreal
        (card
          (query_index_raw_list_preimage
            trace_sampled_bad_actual_query_index_lists)) *
        (1 / nnreal size) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          trace_sampled_bad_actual_query_index_lists)
        (ro_checked_staged_transcript_hash_query_budget_for budgets)"
    by (rule
        active_route_ro_absorb_first_root_trace_sampled_bad_pair_challenge_query_bound[
          OF wf controlled nonempty projection])
  have event_false:
    "ro_absorb_checked_staged_security_with_first_root_trace_challenge_list_hit
      ({} :: 'f list set) = (\<lambda>_. False)"
    unfolding
      ro_absorb_checked_staged_security_with_first_root_trace_challenge_list_hit_def
    by (rule ext) (auto split: option.splits prod.splits)
  have empty:
    "active_route_ro_absorb_first_root_trace_challenge_list_error_for
      A ({} :: 'f list set) = 0"
    unfolding
      active_route_ro_absorb_first_root_trace_challenge_list_error_for_def
      event_false
    by simp
  show ?thesis
    using bound
    unfolding
      trace_sampled_bad_actual_query_parameter_bound_def
      empty
    by simp
qed

end
end
