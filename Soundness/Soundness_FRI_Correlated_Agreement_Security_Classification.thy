theory Soundness_FRI_Correlated_Agreement_Security_Classification
 imports Stark.Soundness_FRI_Correlated_Agreement_Actual_Query
   Stark.Soundness_FRI_Robust_Security_Classification
begin
section \<open>Exhaustive correlated-agreement acceptance classification\<close>
text \<open>
  Every supported accepting outcome is covered by an existing collision or
  target event, one of the two new charged chain events, a guarded residual
  query event, the near-code semantic query event, or the decoded-alpha event.
  No global distance or honest full-domain folding premise is assumed.
\<close>

context soundness
begin

definition ro_mca_builder_bad where
 "ro_mca_builder_bad is_trace out \<longleftrightarrow>
  (case out of None \<Rightarrow> False
   | Some ((prefix_with_state, data, query_start, raws, query_states), state) \<Rightarrow>
       if is_trace then fri_mca_trace_builder_bad data state
       else fri_mca_composition_builder_bad data state)"

definition ro_mca_security_bad where
 "ro_mca_security_bad is_trace = ro_absorb_checked_staged_security_builder_head_event
    (ro_mca_builder_bad is_trace)"

definition ro_mca_obstruction_union where
 "ro_mca_obstruction_union N rT rC out \<longleftrightarrow>
  final_hash_collision_event out \<or>
  ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
    (ro_mca_decoded_semantic_query_lists rT rC) out \<or>
  ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit out \<or>
  ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit out \<or>
  ro_absorb_checked_staged_security_clean_builder_merkle_target_hit out \<or>
  ro_absorb_checked_staged_security_builder_initial_target_hit out \<or>
  ro_mca_security_bad True out \<or> ro_mca_security_bad False out \<or>
  ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
    (fri_mca_combined_query_lists N rT rC) out \<or>
  ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit out \<or>
  ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent out"

lemma ro_mca_no_initial_output:
 assumes none: "\<not> ro_absorb_checked_staged_security_builder_initial_target_hit
   (Some (((((prefix, prefix_state), data, query_start, raws, query_states), state), result), final_state))"
 shows "PState adversary_initial_state \<notin> hash_map_output_values state"
proof
 assume inside: "PState adversary_initial_state \<in> hash_map_output_values state"
 then obtain x where lookup: "fmlookup (HashMap state) x = Some (PState adversary_initial_state)"
   unfolding hash_map_output_values_def by blast
 have fresh: "fmlookup (HashMap adversary_initial_state) x = None"
   unfolding adversary_initial_state_def by simp
 have event: "ro_absorb_checked_staged_security_builder_initial_target_hit
   (Some (((((prefix, prefix_state), data, query_start, raws, query_states), state), result), final_state))"
   unfolding ro_absorb_checked_staged_security_builder_initial_target_hit_def
     ro_absorb_checked_staged_security_builder_head_event_def hash_new_output_hit_event_def
     hash_map_new_output_hit_def
   using lookup fresh by auto
 show False using none event by contradiction
qed


lemma ro_mca_acceptance_classification:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0 < ceil_log clength"
   and ep: "clength*scale=2^N"
   and tf: "Suc (ceil_log clength) \<le> N"
   and cf: "Suc (ceil_log (Suc maxDegree)) \<le> N"
   and acc: "accepted out"
   and support: "out \<in> set_dist (execute
     (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
     adversary_initial_state)"
 shows "ro_mca_obstruction_union N rT rC out"
proof (rule ccontr)
 assume absent: "\<not> ro_mca_obstruction_union N rT rC out"
 have absent_events:
   "\<not> final_hash_collision_event out"
   "\<not> ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit (ro_mca_decoded_semantic_query_lists rT rC) out"
   "\<not> ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit out"
   "\<not> ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit out"
   "\<not> ro_absorb_checked_staged_security_clean_builder_merkle_target_hit out"
   "\<not> ro_absorb_checked_staged_security_builder_initial_target_hit out"
   "\<not> ro_mca_security_bad True out"
   "\<not> ro_mca_security_bad False out"
   "\<not> ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit (fri_mca_combined_query_lists N rT rC) out"
   "\<not> ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit out"
   "\<not> ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent out"
   using absent unfolding ro_mca_obstruction_union_def by blast+
 obtain prefix prefix_state data query_start raws query_states state result final_state
   where eq: "out = Some (((((prefix, prefix_state), data, query_start, raws, query_states),
     state), result), final_state)"
   using acc unfolding accepted_def by (cases out) (auto split: prod.splits)
 have outcome: "Some (((((prefix, prefix_state), data, query_start, raws, query_states),
     state), result), final_state) \<in> set_dist (execute
     (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
     adversary_initial_state)"
   using support eq by simp
 from ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_outcomeE[OF outcome]
 have builder: "Some (((prefix, prefix_state), data, query_start, raws, query_states), state) \<in>
     set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and verifier: "Some (result, final_state) \<in> set_dist (execute ro_verify_monad
     (verifier_state_from_adversary state (staged_proof_transcript data)))" by blast+
 have clean: "\<not> hash_map_output_collision final_state"
   using absent_events(1) unfolding eq final_hash_collision_event_def by simp
 note facts = fri_mca_builder_replay_facts[OF wf controlled nonempty builder verifier clean]
 have degree: "to_nat (staged_degree data) \<le> maxDegree"
   using ro_absorb_checked_staged_first_root_actual_query_accepted_evidence[
     OF wf controlled nonempty builder verifier clean] by blast
 have initial: "PState adversary_initial_state \<notin> hash_map_output_values state"
   by (rule ro_mca_no_initial_output[OF absent_events(6)[unfolded eq]])
 have no_builder: "\<not> fri_checked_builder_merkle_target_hit data state final_state"
   using absent_events(5) clean unfolding eq
     ro_absorb_checked_staged_security_clean_builder_merkle_target_hit_def
     final_hash_collision_event_def by simp
 have no_trace: "\<not> hash_map_new_output_hit
     (first_trace_fri_root_prefix_merkle_targets prefix prefix_state) prefix_state final_state"
   using absent_events(3) unfolding eq
     ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def by simp
 have no_comp: "\<not> hash_map_new_output_hit
     (ro_actual_query_composition_prefix_targets data query_start) query_start final_state"
   using absent_events(4) clean unfolding eq
     ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
     ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
     final_hash_collision_event_def by simp
 have no_query: "\<not> hash_map_new_output_hit
     (fri_checked_builder_merkle_targets data query_start) query_start state"
   using absent_events(10) facts(2) unfolding eq
     ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit_def
     ro_absorb_checked_staged_security_builder_head_event_def
     ro_query_head_dependent_fri_builder_merkle_target_hit_def
     ro_query_head_data_def fri_checked_builder_merkle_targets_def by simp
 have trace_good: "\<not> fri_mca_chain_bad_event (clength-1) fri_mca_quarter_radii
     (staged_trace_fri_roots data) (staged_trace_fri_challenges data) state"
   using absent_events(7) facts(2) initial unfolding eq
     ro_mca_security_bad_def ro_absorb_checked_staged_security_builder_head_event_def
     ro_mca_builder_bad_def fri_mca_trace_builder_bad_def by simp
 have comp_good: "\<not> fri_mca_chain_bad_event (to_nat (staged_degree data)) fri_mca_quarter_radii
     (staged_composition_fri_roots data) (staged_composition_fri_challenges data) state"
   using absent_events(8) facts(2) initial degree unfolding eq
     ro_mca_security_bad_def ro_absorb_checked_staged_security_builder_head_event_def
     ro_mca_builder_bad_def fri_mca_composition_builder_bad_def by simp
 have no_residual: "\<not> ro_query_head_dependent_actual_query_index_list_hit
     (fri_mca_combined_query_lists N rT rC)
     (Some (((prefix, prefix_state), data, query_start, raws, query_states), state))"
   using absent_events(9) unfolding eq
     ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def by simp
 let ?T = "first_trace_fri_root_prefix_first_table prefix prefix_state"
 let ?C = "ro_actual_query_composition_candidate data query_start"
 let ?d = "to_nat (staged_degree data)"
 have trace_close: "fri_rs_distance_to_code (fri_padded_degree_bound (clength-1))
     eval_domain (nth ?T) \<le> rT"
 proof (rule ccontr)
   assume "\<not> fri_rs_distance_to_code (fri_padded_degree_bound (clength-1)) eval_domain (nth ?T) \<le> rT"
   then have far: "rT < fri_rs_distance_to_code (fri_padded_degree_bound (clength-1)) eval_domain (nth ?T)" by simp
   have hit: "ro_query_head_dependent_actual_query_index_list_hit (fri_mca_residual_query_lists N rT True)
       (Some (((prefix, prefix_state), data, query_start, raws, query_states), state))"
     by (rule fri_mca_trace_far_actual[
       OF wf controlled nonempty builder verifier clean ep tf cf no_builder no_trace no_query trace_good far])
   show False using no_residual hit unfolding fri_mca_combined_actual_event by simp
 qed
 have comp_close: "fri_rs_distance_to_code (fri_padded_degree_bound ?d) eval_domain (nth ?C) \<le> rC"
 proof (rule ccontr)
   assume "\<not> fri_rs_distance_to_code (fri_padded_degree_bound ?d) eval_domain (nth ?C) \<le> rC"
   then have far: "rC < fri_rs_distance_to_code (fri_padded_degree_bound ?d) eval_domain (nth ?C)" by simp
   have hit: "ro_query_head_dependent_actual_query_index_list_hit (fri_mca_residual_query_lists N rC False)
       (Some (((prefix, prefix_state), data, query_start, raws, query_states), state))"
     by (rule fri_mca_composition_far_actual[
       OF wf controlled nonempty builder verifier clean ep tf cf no_builder no_comp no_query comp_good far])
   show False using no_residual hit unfolding fri_mca_combined_actual_event by simp
 qed
 have queries: "map (\<lambda>raw. index (to_nat raw)) raws \<in>
     ro_actual_query_trace_composition_accepted_query_lists prefix prefix_state data query_start"
   using ro_absorb_checked_staged_first_root_actual_query_trace_composition_indices_or_targets[
     OF wf controlled nonempty builder verifier clean] no_trace no_comp by blast
 have not_decoded: "\<not> (composition_table_low_degree maxDegree (fri_canonical_decoded_table ?d ?C) \<and>
     all_queries_consistent (fri_canonical_decoded_table (clength-1) ?T)
       (fri_canonical_decoded_table ?d ?C) (staged_alphas data))"
   using absent_events(11) unfolding eq
     ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent_def
     ro_absorb_checked_staged_security_builder_head_event_def
     ro_checked_staged_first_root_robust_decoded_all_queries_consistent_def
     robust_first_trace_fri_root_prefix_first_table_def Let_def by simp

 have candidate_eq: "ro_actual_query_composition_candidate (ro_query_head_data data) query_start = ?C"
   unfolding ro_query_head_data_def ro_actual_query_composition_candidate_def by simp
 have degree_eq: "to_nat (staged_degree (ro_query_head_data data)) = ?d"
   unfolding ro_query_head_data_def by simp
 have alphas_eq: "staged_alphas (ro_query_head_data data) = staged_alphas data"
   unfolding ro_query_head_data_def by simp
 have indices_eq: "ro_actual_query_trace_composition_accepted_indices
     prefix prefix_state (ro_query_head_data data) query_start =
     ro_actual_query_trace_composition_accepted_indices prefix prefix_state data query_start"
   unfolding ro_actual_query_trace_composition_accepted_indices_def
     ro_query_head_data_def ro_actual_query_composition_candidate_def by simp
 have semantic: "map (\<lambda>raw. index (to_nat raw)) raws \<in>
     ro_mca_decoded_semantic_query_lists rT rC prefix prefix_state (ro_query_head_data data) query_start"
   using degree trace_close comp_close not_decoded queries
   unfolding ro_mca_decoded_semantic_query_lists_def ro_mca_decoded_semantic_query_indices_def Let_def
     ro_actual_query_trace_composition_accepted_query_lists_def
     query_index_lists_over_def fri_conditioned_query_lists_def
   by (simp add: candidate_eq degree_eq alphas_eq indices_eq)
 show False using absent_events(2) semantic
   unfolding eq
     ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
     ro_query_head_dependent_actual_query_index_list_hit_def by simp
qed

lemma wp_ro_mca_acceptance_classification:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0 < ceil_log clength"
   and ep: "clength*scale=2^N"
   and tf: "Suc (ceil_log clength) \<le> N"
   and cf: "Suc (ceil_log (Suc maxDegree)) \<le> N"
 shows "wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
     accepted adversary_initial_state \<le>
   wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
     (ro_mca_obstruction_union N rT rC) adversary_initial_state"
 by (rule wp_event_mono_on_support)
    (rule ro_mca_acceptance_classification[OF wf controlled nonempty ep tf cf])

end
end
