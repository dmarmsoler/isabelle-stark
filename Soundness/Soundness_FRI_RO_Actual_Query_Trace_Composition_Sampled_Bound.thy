(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Trace_Composition_Sampled_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Sampled_Bound
  imports
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Target_Bound
begin

context soundness
begin

definition composition_fri_sampled_query_global_query_lists
where
  "composition_fri_sampled_query_global_query_lists =
    (\<Union>dg \<in> (UNIV :: 'f set).
      \<Union>challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
        generic_fri_sampled_query_query_fiber
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree)
          (to_nat dg) challenges)"

lemma composition_fri_sampled_query_global_query_lists_subset:
  "composition_fri_sampled_query_global_query_lists
    \<subseteq> fri_query_index_list_space"
proof
  fix query_idxs
  assume member:
      "query_idxs \<in> composition_fri_sampled_query_global_query_lists"
  then obtain dg challenges where
      "query_idxs \<in>
        generic_fri_sampled_query_query_fiber
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree)
          (to_nat dg) challenges"
    unfolding composition_fri_sampled_query_global_query_lists_def
    by blast
  then show "query_idxs \<in> fri_query_index_list_space"
    using generic_fri_sampled_query_query_fiber_subset by blast
qed

lemma composition_fri_sampled_query_pair_imp_global_query_list:
  assumes pair:
      "(query_idxs, challenges) \<in>
        composition_fri_sampled_query_bad_pair_union dg"
    and query_space: "query_idxs \<in> fri_query_index_list_space"
  shows
    "query_idxs \<in> composition_fri_sampled_query_global_query_lists"
proof -
  have challenge_space:
      "challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
    using pair
      composition_fri_sampled_query_bad_pair_union_challenge_projection[
        of dg]
    by force
  have restricted:
      "(query_idxs, challenges) \<in>
        generic_fri_sampled_query_restricted_bad_pairs
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree)
          (to_nat dg)"
    using pair query_space
    unfolding
      composition_fri_sampled_query_bad_pair_union_def
      generic_fri_sampled_query_restricted_bad_pairs_def
    by simp
  have fiber:
      "query_idxs \<in>
        generic_fri_sampled_query_query_fiber
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree)
          (to_nat dg) challenges"
    using restricted
    unfolding
      generic_fri_sampled_query_query_fiber_def
      fri_query_challenge_pair_query_fiber_def
    by auto
  show ?thesis
    unfolding composition_fri_sampled_query_global_query_lists_def
    using challenge_space fiber by blast
qed




lemma
  ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair_imp_global_query_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and sampled:
      "ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
        out"
  shows
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      (\<lambda>prefix prefix_state data query_start.
        composition_fri_sampled_query_global_query_lists)
      out"
proof -
  from sampled obtain full where out_eq: "out = Some full"
    unfolding
      ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair_def
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
    by blast
  have raws_len: "length raws = rounds"
    using
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled builder_out]
    by blast
  have query_space:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in> fri_query_index_list_space"
    unfolding fri_query_index_list_space_def query_sample_space_def
    using raws_len index_less_query_sample_space by auto
  have pair:
      "(map (\<lambda>raw. index (to_nat raw)) raws,
          staged_composition_fri_challenges data) \<in>
        composition_fri_sampled_query_bad_pair_union (staged_degree data)"
    using sampled
    unfolding out_eq full_eq
      ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair_def
    by simp
  have global:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        composition_fri_sampled_query_global_query_lists"
    by (rule
      composition_fri_sampled_query_pair_imp_global_query_list[
        OF pair query_space])
  show ?thesis
    unfolding out_eq full_eq
      ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
      ro_query_head_dependent_actual_query_index_list_hit_def
    using global by simp
qed


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair_le_global_query_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
        adversary_initial_state
      \<le>
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
          (\<lambda>prefix prefix_state data query_start.
            composition_fri_sampled_query_global_query_lists))
        adversary_initial_state"
  by (rule wp_event_mono_on_support)
    (auto intro:
      ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair_imp_global_query_hit[
        OF wf controlled])



lemma
  wp_ro_absorb_checked_staged_security_with_first_root_global_query_hit_eq:
  assumes nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
          (\<lambda>prefix prefix_state data query_start.
            composition_fri_sampled_query_global_query_lists))
        s
      =
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
        (ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
          composition_fri_sampled_query_global_query_lists)
        s"
proof -
  let ?project =
    "\<lambda>(((prefix_with_state, data, query_start, raws, query_states),
          attacker_state), result).
      (((data, query_start, raws, query_states), attacker_state), result)"
  let ?old =
    "ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
      composition_fri_sampled_query_global_query_lists"
  let ?new =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      (\<lambda>prefix prefix_state data query_start.
        composition_fri_sampled_query_global_query_lists)"
  have event_map:
      "(\<lambda>out. case out of
        None \<Rightarrow> ?old None
      | Some (x, t) \<Rightarrow> ?old (Some (?project x, t))) = ?new"
    by (rule ext)
      (auto simp:
        ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit_def
        ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
        ro_query_head_dependent_actual_query_index_list_hit_def
        split: option.splits prod.splits)
  have mapped:
      "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A \<bind>
          (\<lambda>x. return (?project x)))
        ?old s =
       wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        ?new s"
    by (subst wp_event_bind_return_map)
      (simp only: event_map)
  have projection:
      "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A \<bind>
        (\<lambda>x. return (?project x)) =
       ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
    using
      ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection[
        OF nonempty, of A]
    by (simp add: split_def)
  show ?thesis
    using mapped unfolding projection by simp
qed


definition ro_absorb_checked_staged_composition_sampled_global_query_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_composition_sampled_global_query_error budgets =
    nnreal
      (card
        (query_index_raw_list_preimage
          composition_fri_sampled_query_global_query_lists)) *
      (1 / nnreal size) ^ rounds +
    hash_relation_budget_value
      (query_index_raw_list_relation_fiber_bound
        composition_fri_sampled_query_global_query_lists)
      (ro_checked_staged_transcript_hash_query_budget_for budgets)"


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
        adversary_initial_state
      \<le>
      ro_absorb_checked_staged_composition_sampled_global_query_error budgets"
proof -
  have event_le:
      "wp_event
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A)
          ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
          adversary_initial_state
        \<le>
        wp_event
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A)
          (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
            (\<lambda>prefix prefix_state data query_start.
              composition_fri_sampled_query_global_query_lists))
          adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair_le_global_query_hit[
        OF wf controlled])
  also have "... =
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
        (ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
          composition_fri_sampled_query_global_query_lists)
        adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_global_query_hit_eq[
        OF nonempty])
  also have "... \<le>
      ro_absorb_checked_staged_composition_sampled_global_query_error budgets"
    unfolding
      ro_absorb_checked_staged_composition_sampled_global_query_error_def
    by (rule
      ro_absorb_checked_staged_security_with_query_witnesses_actual_hit_bound[
        OF wf controlled])
  finally show ?thesis .
qed

end
end
