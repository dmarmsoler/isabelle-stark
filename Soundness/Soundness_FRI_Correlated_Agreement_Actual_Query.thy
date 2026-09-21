theory Soundness_FRI_Correlated_Agreement_Actual_Query
 imports Stark.Soundness_FRI_Correlated_Agreement_Guarded_Rectangles
   Stark.Soundness_FRI_Correlated_Agreement_Accepted_Chains
begin
section \<open>Adaptive probabilities for actual correlated-agreement queries\<close>
text \<open>
  The query families depend only on head data and the guarded pre-query state.
  Trace and composition probabilities are added, not replaced by a maximum.
  The exact raw modulo envelope and staged attacker budget remain unchanged.
  A zero-fold composition candidate has zero distance and cannot enter the far branch.
\<close>

context soundness
begin
definition fri_mca_residual_query_indices ::
 "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('f \<times> 'f list \<times> 'f) \<Rightarrow> 'f protocol_channel \<Rightarrow>
   'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set" where
 "fri_mca_residual_query_indices N r is_trace prefix prefix_state data s =
  (if is_trace then
     fri_mca_guarded_indices (clength-1) N fri_mca_quarter_radii r
       (staged_trace_fri_roots data) (staged_trace_fri_challenges data) (staged_trace_final data) s
   else if to_nat (staged_degree data) \<le> maxDegree then
     fri_mca_guarded_indices (to_nat (staged_degree data)) N fri_mca_quarter_radii r
       (staged_composition_fri_roots data) (staged_composition_fri_challenges data)
       (staged_composition_final data) s
   else {})"

definition fri_mca_residual_query_lists where
 "fri_mca_residual_query_lists N r is_trace prefix prefix_state data s =
   fri_conditioned_query_lists (fri_mca_residual_query_indices N r is_trace prefix prefix_state data s)"

definition fri_mca_residual_branch_bound :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
 "fri_mca_residual_branch_bound r is_trace =
   fri_mca_residual_index_bound (if is_trace then clength-1 else maxDegree) fri_mca_quarter_radii r"

lemma fri_mca_residual_query_indices_subset:
 "fri_mca_residual_query_indices N r b prefix prefix_state data s \<subseteq> query_sample_space"
 unfolding fri_mca_residual_query_indices_def
 using fri_mca_guarded_subset by simp

lemma fri_mca_residual_query_indices_card:
 "card (fri_mca_residual_query_indices N r b prefix prefix_state data s)
   \<le> fri_mca_residual_branch_bound r b"
proof (cases b)
 case True
 then show ?thesis
   unfolding fri_mca_residual_query_indices_def fri_mca_residual_branch_bound_def
   by (simp add: fri_mca_guarded_card)
next
 case False
 show ?thesis
 proof (cases "to_nat (staged_degree data) \<le> maxDegree")
   case True
   have bound: "card (fri_mca_guarded_indices (to_nat (staged_degree data)) N
       fri_mca_quarter_radii r (staged_composition_fri_roots data)
       (staged_composition_fri_challenges data) (staged_composition_final data) s)
       \<le> fri_mca_residual_index_bound (to_nat (staged_degree data)) fri_mca_quarter_radii r"
     by (rule fri_mca_guarded_card)
   have mono: "fri_mca_residual_index_bound (to_nat (staged_degree data)) fri_mca_quarter_radii r
       \<le> fri_mca_residual_index_bound maxDegree fri_mca_quarter_radii r"
     by (rule fri_mca_residual_degree_mono[OF True])
   show ?thesis
     unfolding fri_mca_residual_query_indices_def fri_mca_residual_branch_bound_def
     using bound mono True False by simp
 next
   case degree_bad: False
   then show ?thesis
     unfolding fri_mca_residual_query_indices_def fri_mca_residual_branch_bound_def
     using False by simp
 qed
qed

lemma fri_mca_residual_query_lists_head:
 "fri_mca_residual_query_lists N r b prefix prefix_state (ro_query_head_data data) s =
   fri_mca_residual_query_lists N r b prefix prefix_state data s"
 by (simp add: fri_mca_residual_query_lists_def fri_mca_residual_query_indices_def ro_query_head_data_def)

lemma fri_mca_residual_query_lists_stable:
 assumes ext: "s \<le> u"
   and none: "\<not> hash_map_new_output_hit (fri_checked_builder_merkle_targets data s) s u"
 shows "fri_mca_residual_query_lists N r b prefix prefix_state data u =
   fri_mca_residual_query_lists N r b prefix prefix_state data s"
proof -
 have no: "\<not> hash_map_new_output_hit
     (merkle_prefix_path_targets (set (staged_trace_fri_roots data) \<union>
       set (staged_composition_fri_roots data)) s) s u"
   using none unfolding fri_checked_builder_merkle_targets_def .
 have tn: "\<not> hash_map_new_output_hit
     (merkle_prefix_path_targets (set (staged_trace_fri_roots data)) s) s u"
   by (rule fri_mca_no_target_subset[OF _ no]) auto
 have cn: "\<not> hash_map_new_output_hit
     (merkle_prefix_path_targets (set (staged_composition_fri_roots data)) s) s u"
   by (rule fri_mca_no_target_subset[OF _ no]) auto
 show ?thesis unfolding fri_mca_residual_query_lists_def fri_mca_residual_query_indices_def
   by (simp only: fri_mca_guarded_stable[OF ext tn] fri_mca_guarded_stable[OF ext cn])
qed

lemma wp_ro_mca_residual_rectangle:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
 shows "wp_event
    (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
    (ro_query_head_dependent_actual_query_index_list_hit (fri_mca_residual_query_lists N r b))
    adversary_initial_state
  \<le> ro_mca_rectangle_error (fri_mca_residual_branch_bound r b) budgets"
 unfolding ro_mca_rectangle_error_def
 by (rule wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_bound[
      OF wf controlled, where I="fri_mca_residual_query_indices N r b"])
    (simp_all add: fri_mca_residual_query_lists_def
       fri_mca_residual_query_indices_subset fri_mca_residual_query_indices_card)

lemma fri_mca_residual_actual_if_member:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and outcome: "Some (((prefix, prefix_state), data, query_start, raws, query_states), attacker_state) \<in>
       set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
         adversary_initial_state)"
   and none: "\<not> hash_map_new_output_hit
     (fri_checked_builder_merkle_targets data query_start) query_start attacker_state"
   and member: "map (\<lambda>raw. index (to_nat raw)) raws \<in>
     fri_mca_residual_query_lists N r b prefix prefix_state data attacker_state"
 shows "ro_query_head_dependent_actual_query_index_list_hit (fri_mca_residual_query_lists N r b)
     (Some (((prefix, prefix_state), data, query_start, raws, query_states), attacker_state))"
proof -
 have ext: "query_start \<le> attacker_state"
   using ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
     OF wf controlled outcome] by blast
 have stable: "fri_mca_residual_query_lists N r b prefix prefix_state data attacker_state =
     fri_mca_residual_query_lists N r b prefix prefix_state data query_start"
   by (rule fri_mca_residual_query_lists_stable[OF ext none])
 show ?thesis unfolding ro_query_head_dependent_actual_query_index_list_hit_def
   using member stable fri_mca_residual_query_lists_head[of N r b prefix prefix_state data query_start]
   by simp
qed

definition fri_mca_combined_query_lists where
 "fri_mca_combined_query_lists N rT rC prefix prefix_state data s =
    fri_mca_residual_query_lists N rT True prefix prefix_state data s \<union>
    fri_mca_residual_query_lists N rC False prefix prefix_state data s"

definition ro_mca_combined_rectangle_error :: "nat \<Rightarrow> nat \<Rightarrow> staged_budgets \<Rightarrow> prob" where
 "ro_mca_combined_rectangle_error rT rC budgets =
    ro_mca_rectangle_error (fri_mca_residual_branch_bound rT True) budgets +
    ro_mca_rectangle_error (fri_mca_residual_branch_bound rC False) budgets"

lemma fri_mca_combined_actual_event:
 "ro_query_head_dependent_actual_query_index_list_hit (fri_mca_combined_query_lists N rT rC) =
  (\<lambda>out. ro_query_head_dependent_actual_query_index_list_hit (fri_mca_residual_query_lists N rT True) out \<or>
         ro_query_head_dependent_actual_query_index_list_hit (fri_mca_residual_query_lists N rC False) out)"
 unfolding ro_query_head_dependent_actual_query_index_list_hit_def fri_mca_combined_query_lists_def
 by (rule ext) (auto split: option.splits prod.splits)

lemma wp_ro_mca_combined_rectangle:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
 shows "wp_event
    (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
    (ro_query_head_dependent_actual_query_index_list_hit (fri_mca_combined_query_lists N rT rC))
    adversary_initial_state \<le> ro_mca_combined_rectangle_error rT rC budgets"
 unfolding fri_mca_combined_actual_event ro_mca_combined_rectangle_error_def
 by (rule order_trans[OF wp_event_union_bound])
    (intro add_mono wp_ro_mca_residual_rectangle[OF wf controlled])

lemma fri_mca_trace_far_actual:
 fixes final_state :: "'f protocol_channel"
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0 < ceil_log clength"
   and builder_out:
     "Some (((prefix, prefix_state), data, query_start, raws, query_states), attacker_state) \<in>
       set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
         adversary_initial_state)"
   and verifier_out: "Some (results, final_state) \<in> set_dist (execute ro_verify_monad
     (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
   and final_clean: "\<not> hash_map_output_collision final_state"
   and ep: "clength*scale=2^N"
   and tf: "Suc (ceil_log clength) \<le> N"
   and cf: "Suc (ceil_log (Suc maxDegree)) \<le> N"
   and no_builder: "\<not> fri_checked_builder_merkle_target_hit data attacker_state final_state"
   and no_prefix: "\<not> hash_map_new_output_hit
     (first_trace_fri_root_prefix_merkle_targets prefix prefix_state) prefix_state final_state"
   and no_query: "\<not> hash_map_new_output_hit
     (fri_checked_builder_merkle_targets data query_start) query_start attacker_state"
   and good: "\<not> fri_mca_chain_bad_event (clength-1) fri_mca_quarter_radii
     (staged_trace_fri_roots data) (staged_trace_fri_challenges data) attacker_state"
   and far: "r < fri_rs_distance_to_code (fri_padded_degree_bound (clength-1))
     eval_domain (nth (first_trace_fri_root_prefix_first_table prefix prefix_state))"
 shows "ro_query_head_dependent_actual_query_index_list_hit (fri_mca_residual_query_lists N r True)
     (Some (((prefix, prefix_state), data, query_start, raws, query_states), attacker_state))"
proof -
 note facts = fri_mca_builder_replay_facts[OF wf controlled nonempty builder_out verifier_out final_clean]
 obtain T where actual: "fri_authenticated_global_chain_realizable (clength-1) N
     (staged_trace_fri_roots data) (staged_trace_fri_challenges data) (staged_trace_final data)
     (map (\<lambda>raw. index (to_nat raw)) raws) T attacker_state final_state"
   by (rule fri_mca_accepted_global_chains[
     OF wf controlled nonempty builder_out verifier_out final_clean ep tf cf no_builder]) blast
 have active: "staged_trace_fri_roots data \<noteq> []"
   using facts(6) nonempty by auto
 have positive: "0 < length (staged_trace_fri_challenges data)"
   using facts(7) nonempty by simp
 have table: "first_trace_fri_root_prefix_first_table prefix prefix_state =
     conceptual_table attacker_state (staged_trace_fri_roots data ! 0)
       (length (fri_canonical_domain_at 0))"
   by (rule fri_mca_trace_initial_table_transport[
     OF facts(5) active facts(3,1,2) no_prefix no_builder])
 have far': "r < fri_rs_distance_to_code (fri_padded_degree_bound (clength-1))
     (fri_canonical_domain_at 0)
     (nth (conceptual_table attacker_state (staged_trace_fri_roots data ! 0)
       (length (fri_canonical_domain_at 0))))"
   using far table by (simp add: fri_canonical_domain_at_0)
 have member: "map (\<lambda>raw. index (to_nat raw)) raws \<in>
     fri_mca_residual_query_lists N r True prefix prefix_state data attacker_state"
   unfolding fri_mca_residual_query_lists_def fri_mca_residual_query_indices_def if_True
   by (rule fri_mca_guarded_member[OF actual positive good far'])
 show ?thesis by (rule fri_mca_residual_actual_if_member[OF wf controlled builder_out no_query member])
qed

lemma fri_mca_composition_far_actual:
 fixes final_state :: "'f protocol_channel"
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0 < ceil_log clength"
   and builder_out:
     "Some (((prefix, prefix_state), data, query_start, raws, query_states), attacker_state) \<in>
       set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
         adversary_initial_state)"
   and verifier_out: "Some (results, final_state) \<in> set_dist (execute ro_verify_monad
     (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
   and final_clean: "\<not> hash_map_output_collision final_state"
   and ep: "clength*scale=2^N"
   and tf: "Suc (ceil_log clength) \<le> N"
   and cf: "Suc (ceil_log (Suc maxDegree)) \<le> N"
   and no_builder: "\<not> fri_checked_builder_merkle_target_hit data attacker_state final_state"
   and no_prefix: "\<not> hash_map_new_output_hit
     (ro_actual_query_composition_prefix_targets data query_start) query_start final_state"
   and no_query: "\<not> hash_map_new_output_hit
     (fri_checked_builder_merkle_targets data query_start) query_start attacker_state"
   and good: "\<not> fri_mca_chain_bad_event (to_nat (staged_degree data)) fri_mca_quarter_radii
     (staged_composition_fri_roots data) (staged_composition_fri_challenges data) attacker_state"
   and far: "r < fri_rs_distance_to_code (fri_padded_degree_bound (to_nat (staged_degree data)))
     eval_domain (nth (ro_actual_query_composition_candidate data query_start))"
 shows "ro_query_head_dependent_actual_query_index_list_hit (fri_mca_residual_query_lists N r False)
     (Some (((prefix, prefix_state), data, query_start, raws, query_states), attacker_state))"
proof -
 note facts = fri_mca_builder_replay_facts[OF wf controlled nonempty builder_out verifier_out final_clean]
 obtain C where actual: "fri_authenticated_global_chain_realizable (to_nat (staged_degree data)) N
     (staged_composition_fri_roots data) (staged_composition_fri_challenges data) (staged_composition_final data)
     (map (\<lambda>raw. index (to_nat raw)) raws) C attacker_state final_state"
   and degree: "to_nat (staged_degree data) \<le> maxDegree"
   by (rule fri_mca_accepted_global_chains[
     OF wf controlled nonempty builder_out verifier_out final_clean ep tf cf no_builder]) blast
 have active: "staged_composition_fri_roots data \<noteq> []"
 proof
   assume empty: "staged_composition_fri_roots data = []"
   have zero: "fri_rs_distance_to_code (fri_padded_degree_bound (to_nat (staged_degree data)))
     eval_domain (nth (ro_actual_query_composition_candidate data query_start)) = 0"
     by (rule fri_mca_composition_zero_distance[OF empty])
   show False using far zero by simp
 qed
 have positive: "0 < length (staged_composition_fri_challenges data)"
   using facts(8,9) active by force
 have table: "ro_actual_query_composition_candidate data query_start =
     conceptual_table attacker_state (staged_composition_fri_roots data ! 0)
       (length (fri_canonical_domain_at 0))"
   by (rule fri_mca_composition_initial_table_transport[
     OF active facts(4,1) no_prefix no_builder])
 have far': "r < fri_rs_distance_to_code (fri_padded_degree_bound (to_nat (staged_degree data)))
     (fri_canonical_domain_at 0)
     (nth (conceptual_table attacker_state (staged_composition_fri_roots data ! 0)
       (length (fri_canonical_domain_at 0))))"
   using far table by (simp add: fri_canonical_domain_at_0)
 have member: "map (\<lambda>raw. index (to_nat raw)) raws \<in>
     fri_mca_residual_query_lists N r False prefix prefix_state data attacker_state"
   unfolding fri_mca_residual_query_lists_def fri_mca_residual_query_indices_def if_False if_P[OF degree]
   by (rule fri_mca_guarded_member[OF actual positive good far'])
 show ?thesis by (rule fri_mca_residual_actual_if_member[OF wf controlled builder_out no_query member])
qed

end
end
