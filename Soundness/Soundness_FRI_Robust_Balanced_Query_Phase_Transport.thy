theory Soundness_FRI_Robust_Balanced_Query_Phase_Transport
  imports
    Stark.Soundness_FRI_Robust_Query_Phase_Transport
    Stark.Soundness_FRI_Robust_Balanced_Actual_Query
    Stark.Soundness_FRI_Conditioned_Explicit_Residual_Query_Phase_Target
begin

context soundness
begin

lemma fri_balanced_trace_residual_query_lists_stable_if_no_builder_target:
  assumes ext: "s \<le> t"
    and no_target:
      "\<not> hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data s) s t"
  shows
    "fri_balanced_trace_residual_query_lists C data t =
      fri_balanced_trace_residual_query_lists C data s"
proof -
  have targets_subset:
      "merkle_prefix_path_targets (set (staged_trace_fri_roots data)) s \<subseteq>
        fri_checked_builder_merkle_targets data s"
    unfolding fri_checked_builder_merkle_targets_def
    by (rule merkle_prefix_path_targets_mono) auto
  have no_trace:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets (set (staged_trace_fri_roots data)) s)
        s t"
    using no_target hash_map_new_output_hit_subset[OF targets_subset]
    by blast
  have layers:
      "fri_builder_conceptual_layers (staged_trace_fri_roots data) t
          (staged_trace_final data) =
        fri_builder_conceptual_layers (staged_trace_fri_roots data) s
          (staged_trace_final data)"
    by (rule fri_builder_conceptual_layers_stable_if_no_target[
        OF ext no_trace])
  show ?thesis
    unfolding fri_balanced_trace_residual_query_lists_def
      fri_balanced_quantitative_residual_query_lists_def
      fri_balanced_residual_active_layers_def
    by (simp add: layers)
qed

lemma fri_balanced_composition_residual_query_lists_stable_if_no_builder_target:
  assumes ext: "s \<le> t"
    and no_target:
      "\<not> hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data s) s t"
  shows
    "fri_balanced_composition_residual_query_lists C data t =
      fri_balanced_composition_residual_query_lists C data s"
proof -
  have targets_subset:
      "merkle_prefix_path_targets
          (set (staged_composition_fri_roots data)) s \<subseteq>
        fri_checked_builder_merkle_targets data s"
    unfolding fri_checked_builder_merkle_targets_def
    by (rule merkle_prefix_path_targets_mono) auto
  have no_composition:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets
          (set (staged_composition_fri_roots data)) s) s t"
    using no_target hash_map_new_output_hit_subset[OF targets_subset]
    by blast
  have layers:
      "fri_builder_conceptual_layers
          (staged_composition_fri_roots data) t
          (staged_composition_final data) =
        fri_builder_conceptual_layers
          (staged_composition_fri_roots data) s
          (staged_composition_final data)"
    by (rule fri_builder_conceptual_layers_stable_if_no_target[
        OF ext no_composition])
  show ?thesis
    unfolding fri_balanced_composition_residual_query_lists_def
      fri_balanced_quantitative_residual_query_lists_def
      fri_balanced_residual_active_layers_def
    by (simp add: layers)
qed

lemma fri_balanced_combined_query_head_lists_stable_if_no_builder_target:
  assumes ext: "s \<le> t"
    and no_target:
      "\<not> hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data s) s t"
  shows
    "fri_balanced_combined_query_head_lists C
        prefix prefix_state data t =
      fri_balanced_combined_query_head_lists C
        prefix prefix_state data s"
  unfolding fri_balanced_combined_query_head_lists_def
    fri_balanced_trace_query_head_lists_def
    fri_balanced_composition_query_head_lists_def
  using
    fri_balanced_trace_residual_query_lists_stable_if_no_builder_target[
      OF ext no_target]
    fri_balanced_composition_residual_query_lists_stable_if_no_builder_target[
      OF ext no_target]
  by simp

lemma checked_builder_balanced_residual_imp_actual_or_query_phase_target:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and residual:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        fri_balanced_combined_query_head_lists C
          prefix prefix_state data attacker_state"
  shows
    "hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data query_start)
        query_start attacker_state \<or>
      ro_query_head_dependent_actual_query_index_list_hit
        (fri_balanced_combined_query_head_lists C)
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
proof (cases
    "hash_map_new_output_hit
      (fri_checked_builder_merkle_targets data query_start)
      query_start attacker_state")
  case True
  then show ?thesis by simp
next
  case False
  have props:
      "length raws = rounds \<and>
       length query_states = rounds \<and>
       length (staged_query_chunks data) = rounds \<and>
       query_start \<le> attacker_state"
    using
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled outcome]
    by blast
  have stable:
      "fri_balanced_combined_query_head_lists C
          prefix prefix_state data attacker_state =
        fri_balanced_combined_query_head_lists C
          prefix prefix_state data query_start"
    by (rule
      fri_balanced_combined_query_head_lists_stable_if_no_builder_target[
        OF _ False])
      (use props in blast)
  have residual_start:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        fri_balanced_combined_query_head_lists C
          prefix prefix_state data query_start"
    using residual stable by simp
  have data_eq:
      "fri_balanced_combined_query_head_lists C
          prefix prefix_state (ro_query_head_data data) query_start =
        fri_balanced_combined_query_head_lists C
          prefix prefix_state data query_start"
    unfolding fri_balanced_combined_query_head_lists_def
      fri_balanced_trace_query_head_lists_def
      fri_balanced_composition_query_head_lists_def
      fri_balanced_trace_residual_query_lists_def
      fri_balanced_composition_residual_query_lists_def
      ro_query_head_data_def
    by simp
  have actual:
      "ro_query_head_dependent_actual_query_index_list_hit
        (fri_balanced_combined_query_head_lists C)
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
    unfolding ro_query_head_dependent_actual_query_index_list_hit_def
    using residual_start data_eq by simp
  then show ?thesis by simp
qed


end

end
