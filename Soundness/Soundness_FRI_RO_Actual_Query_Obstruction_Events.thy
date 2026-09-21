theory Soundness_FRI_RO_Actual_Query_Obstruction_Events
  imports
    Soundness_FRI_RO_Actual_Query_Obstruction_Reduction
    Soundness_FRI_First_Root_RO_Actual_Query_Route
begin

context soundness
begin

definition
  ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
where
  "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        (map (\<lambda>raw. index (to_nat raw)) raws,
          staged_trace_fri_challenges data) \<in>
          generic_fri_sampled_query_bad_pair_union
            trace_table_low_degree (Not \<circ> trace_table_low_degree)
            (clength - 1))"

definition
  ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict
where
  "ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        (\<exists>trace_round_layers.
          generic_fri_sampled_base_opening_conflict
            (first_trace_fri_root_prefix_first_table prefix prefix_state)
            (staged_trace_fri_roots data)
            (staged_trace_fri_challenges data)
            (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers))"

lemma
  ro_absorb_checked_staged_security_with_first_root_clean_first_not_low_degree_obstruction:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and first_bad:
      "ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
        out"
    and clean: "\<not> final_hash_collision_event out"
  shows
    "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict
       out"
proof -
  from first_bad obtain full where out_eq: "out = Some full"
    unfolding
      ro_absorb_checked_staged_security_with_first_root_first_not_low_degree_def
    by (cases out) auto
  obtain prefix prefix_state data query_start raws query_states
      attacker_state result final_state where
    full_eq:
      "full =
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state)"
    by (cases full) (auto split: prod.splits)
  have outcome:
      "Some
          (((((prefix, prefix_state), data, query_start, raws, query_states),
              attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    using support out_eq full_eq by simp
  from
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_outcomeE[
      OF outcome]
  have builder_out:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and verifier_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    by blast+
  have final_clean: "\<not> hash_map_output_collision final_state"
    using clean
    unfolding out_eq full_eq final_hash_collision_event_def
    by simp
  have candidate_bad:
      "\<not> trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
    using first_bad
    unfolding out_eq full_eq
      ro_absorb_checked_staged_security_with_first_root_first_not_low_degree_def
    by simp
  from
    ro_absorb_checked_staged_first_root_actual_query_first_not_low_degree_obstruction[
      OF wf controlled nonempty builder_out verifier_out final_clean
        candidate_bad]
  obtain f_fl f_final trace_round_layers where
    trace_challenges_eq:
      "map fst f_fl = staged_trace_fri_challenges data"
    and trace_roots_eq: "map snd f_fl = staged_trace_fri_roots data"
    and obstruction:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
         (Not \<circ> trace_table_low_degree)
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (clength - 1) (map snd f_fl) (map fst f_fl) f_final
         (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers
         (generic_fri_sampled_assignment_layers
           (first_trace_fri_root_prefix_first_table prefix prefix_state)
           (map snd f_fl) (map fst f_fl) f_final
           (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers) \<or>
       generic_fri_sampled_base_opening_conflict
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (map snd f_fl) (map fst f_fl)
         (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers \<or>
       partial_merkle_inconsistency_bad
         (verifier_state_from_adversary attacker_state
           (staged_proof_transcript data))
         (Some (result, final_state))"
    by blast
  have no_partial:
      "\<not> partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state))"
  proof
    assume partial:
      "partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state))"
    have collision:
        "hash_map_output_collision_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (Some (result, final_state))"
      by (rule partial_merkle_inconsistency_bad_imp_hash_map_output_collision_bad[
            OF partial])
    show False
      using collision final_clean
      unfolding hash_map_output_collision_bad_def accepted_def
      by simp
  qed
  from obstruction no_partial have sampled_or_base:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
         (Not \<circ> trace_table_low_degree)
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (clength - 1) (map snd f_fl) (map fst f_fl) f_final
         (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers
         (generic_fri_sampled_assignment_layers
           (first_trace_fri_root_prefix_first_table prefix prefix_state)
           (map snd f_fl) (map fst f_fl) f_final
           (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers) \<or>
       generic_fri_sampled_base_opening_conflict
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (map snd f_fl) (map fst f_fl)
         (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    by blast
  then show ?thesis
  proof
    assume sampled:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
         (Not \<circ> trace_table_low_degree)
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (clength - 1) (map snd f_fl) (map fst f_fl) f_final
         (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers
         (generic_fri_sampled_assignment_layers
           (first_trace_fri_root_prefix_first_table prefix prefix_state)
           (map snd f_fl) (map fst f_fl) f_final
           (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers)"
    have pair:
        "(map (\<lambda>raw. index (to_nat raw)) raws, map fst f_fl) \<in>
          generic_fri_sampled_query_bad_pair_union trace_table_low_degree
            (Not \<circ> trace_table_low_degree) (clength - 1)"
      using sampled
      unfolding generic_fri_sampled_query_bad_pair_union_def
        generic_fri_sampled_query_bad_pair_set_def
      by blast
    have event_concrete:
        "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
          (Some
            (((((prefix, prefix_state), data, query_start, raws, query_states),
                attacker_state), result), final_state))"
      unfolding
        ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair_def
      using trace_challenges_eq pair by auto
    have event:
        "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
          out"
      using event_concrete out_eq full_eq by simp
    show ?thesis
      using event by simp
  next
    assume base:
      "generic_fri_sampled_base_opening_conflict
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (map snd f_fl) (map fst f_fl)
        (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    have event_concrete:
        "ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict
          (Some
            (((((prefix, prefix_state), data, query_start, raws, query_states),
                attacker_state), result), final_state))"
      unfolding
        ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict_def
      using trace_challenges_eq trace_roots_eq base by auto
    have event:
        "ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict
          out"
      using event_concrete out_eq full_eq by simp
    show ?thesis
      using event by simp
  qed
qed



lemma
  ro_absorb_checked_staged_security_with_first_root_clean_outcome_obstruction_classification:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and accepted_out: "accepted out"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and clean: "\<not> final_hash_collision_event out"
  shows
    "ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
        first_trace_fri_root_prefix_good_agreement_query_lists out \<or>
     ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_tables_equal out"
proof -
  have classified:
      "ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
          first_trace_fri_root_prefix_good_agreement_query_lists out \<or>
       ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_tables_equal out"
    by (rule
        ro_absorb_checked_staged_security_with_first_root_clean_outcome_classification[
          OF wf controlled nonempty accepted_out support clean])
  have first_reduction:
      "ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
          out \<Longrightarrow>
       ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
          out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict
          out"
    by (rule
        ro_absorb_checked_staged_security_with_first_root_clean_first_not_low_degree_obstruction[
          OF wf controlled nonempty support _ clean])
  show ?thesis
    using classified first_reduction by blast
qed


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_le_obstruction_classified_union:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le>
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        (\<lambda>out.
          final_hash_collision_event out \<or>
          ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
            first_trace_fri_root_prefix_good_agreement_query_lists out \<or>
          ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_tables_equal out)
        adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and accepted_out: "accepted out"
  show
      "final_hash_collision_event out \<or>
       ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
         first_trace_fri_root_prefix_good_agreement_query_lists out \<or>
       ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_tables_equal out"
  proof (cases "final_hash_collision_event out")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis
      using
        ro_absorb_checked_staged_security_with_first_root_clean_outcome_obstruction_classification[
          OF wf controlled nonempty accepted_out support False]
      by simp
  qed
qed


definition
  active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for
    :: "'f staged_adversary \<Rightarrow> prob"
where
  "active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for A =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
      adversary_initial_state"

definition
  active_route_ro_absorb_first_root_trace_base_opening_conflict_error_for
    :: "'f staged_adversary \<Rightarrow> prob"
where
  "active_route_ro_absorb_first_root_trace_base_opening_conflict_error_for A =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict
      adversary_initial_state"

definition
  active_route_ro_absorb_first_root_obstruction_classified_bound_for
    :: "staged_budgets \<Rightarrow> 'f staged_adversary \<Rightarrow> prob"
where
  "active_route_ro_absorb_first_root_obstruction_classified_bound_for budgets A =
    hash_collision_budget_value 0
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
    ro_checked_staged_first_root_good_actual_query_error budgets +
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
    active_route_ro_absorb_first_root_trace_not_low_degree_error_for A +
    active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for A +
    active_route_ro_absorb_first_root_trace_base_opening_conflict_error_for A +
    active_route_ro_absorb_first_root_tables_equal_error_for A"

lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_obstruction_classified_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> active_route_ro_absorb_first_root_obstruction_classified_bound_for
          budgets A"
proof -
  let ?M =
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      A"
  let ?Collision = "final_hash_collision_event"
  let ?Query =
    "ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
      first_trace_fri_root_prefix_good_agreement_query_lists"
  let ?Target =
    "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit"
  let ?Trace =
    "ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree"
  let ?Sampled =
    "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair"
  let ?Base =
    "ro_absorb_checked_staged_security_with_first_root_trace_base_opening_conflict"
  let ?Equal =
    "ro_absorb_checked_staged_security_with_first_root_tables_equal"

  have classified:
      "wp_event ?M accepted adversary_initial_state \<le>
       wp_event ?M
         (\<lambda>out.
           ?Collision out \<or> ?Query out \<or> ?Target out \<or> ?Trace out \<or>
           ?Sampled out \<or> ?Base out \<or> ?Equal out)
         adversary_initial_state"
    by (rule
        wp_ro_absorb_checked_staged_security_with_first_root_acceptance_le_obstruction_classified_union[
          OF wf controlled nonempty])
  have union:
      "wp_event ?M
          (\<lambda>out.
            ?Collision out \<or> ?Query out \<or> ?Target out \<or> ?Trace out \<or>
            ?Sampled out \<or> ?Base out \<or> ?Equal out)
          adversary_initial_state
        \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Query adversary_initial_state +
        wp_event ?M ?Target adversary_initial_state +
        wp_event ?M ?Trace adversary_initial_state +
        wp_event ?M ?Sampled adversary_initial_state +
        wp_event ?M ?Base adversary_initial_state +
        wp_event ?M ?Equal adversary_initial_state"
  proof -
    have
      "wp_event ?M
          (\<lambda>out.
            ?Collision out \<or> ?Query out \<or> ?Target out \<or> ?Trace out \<or>
            ?Sampled out \<or> ?Base out \<or> ?Equal out)
          adversary_initial_state
        \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M
          (\<lambda>out.
            ?Query out \<or> ?Target out \<or> ?Trace out \<or>
            ?Sampled out \<or> ?Base out \<or> ?Equal out)
          adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         wp_event ?M
           (\<lambda>out.
             ?Target out \<or> ?Trace out \<or> ?Sampled out \<or>
             ?Base out \<or> ?Equal out)
           adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         (wp_event ?M ?Target adversary_initial_state +
          wp_event ?M
            (\<lambda>out.
              ?Trace out \<or> ?Sampled out \<or> ?Base out \<or> ?Equal out)
            adversary_initial_state))"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         (wp_event ?M ?Target adversary_initial_state +
          (wp_event ?M ?Trace adversary_initial_state +
           wp_event ?M
             (\<lambda>out. ?Sampled out \<or> ?Base out \<or> ?Equal out)
             adversary_initial_state)))"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         (wp_event ?M ?Target adversary_initial_state +
          (wp_event ?M ?Trace adversary_initial_state +
           (wp_event ?M ?Sampled adversary_initial_state +
            wp_event ?M (\<lambda>out. ?Base out \<or> ?Equal out)
              adversary_initial_state))))"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         (wp_event ?M ?Target adversary_initial_state +
          (wp_event ?M ?Trace adversary_initial_state +
           (wp_event ?M ?Sampled adversary_initial_state +
            (wp_event ?M ?Base adversary_initial_state +
             wp_event ?M ?Equal adversary_initial_state)))))"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  have collision:
      "wp_event ?M ?Collision adversary_initial_state
        \<le> hash_collision_budget_value 0
            (ro_absorb_checked_staged_security_hash_query_budget_for budgets)"
    by (rule
        wp_ro_absorb_checked_staged_security_with_first_root_final_hash_collision_bound[
          OF wf controlled nonempty])
  have query:
      "wp_event ?M ?Query adversary_initial_state
        \<le> ro_checked_staged_first_root_good_actual_query_error budgets"
    using
      active_route_ro_absorb_first_root_good_actual_query_bound[
        OF wf controlled nonempty]
    unfolding active_route_ro_absorb_first_root_good_actual_query_error_for_def
    .
  have target:
      "wp_event ?M ?Target adversary_initial_state
        \<le> ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets"
    by (rule
        wp_ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_bound[
          OF nonempty wf controlled])
  have closed:
      "wp_event ?M ?Collision adversary_initial_state +
       wp_event ?M ?Query adversary_initial_state +
       wp_event ?M ?Target adversary_initial_state +
       wp_event ?M ?Trace adversary_initial_state +
       wp_event ?M ?Sampled adversary_initial_state +
       wp_event ?M ?Base adversary_initial_state +
       wp_event ?M ?Equal adversary_initial_state
       \<le>
       hash_collision_budget_value 0
         (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
       ro_checked_staged_first_root_good_actual_query_error budgets +
       ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
       wp_event ?M ?Trace adversary_initial_state +
       wp_event ?M ?Sampled adversary_initial_state +
       wp_event ?M ?Base adversary_initial_state +
       wp_event ?M ?Equal adversary_initial_state"
    by (intro add_mono collision query target order_refl)
  show ?thesis
    unfolding
      active_route_ro_absorb_first_root_obstruction_classified_bound_for_def
      active_route_ro_absorb_first_root_trace_not_low_degree_error_for_def
      active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for_def
      active_route_ro_absorb_first_root_trace_base_opening_conflict_error_for_def
      active_route_ro_absorb_first_root_tables_equal_error_for_def
    by (rule order_trans[OF classified order_trans[OF union closed]])
qed
end
end