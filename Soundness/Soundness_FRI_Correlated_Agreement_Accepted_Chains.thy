theory Soundness_FRI_Correlated_Agreement_Accepted_Chains
 imports Stark.Soundness_FRI_Correlated_Agreement_Adaptive_Charging
   Stark.Soundness_FRI_Conditioned_Explicit_Residual_Complete_List_Classification
begin
section \<open>Actual accepted-chain extraction and table transport\<close>
text \<open>
  The witnesses below come from the existing checked builder and verifier
  executions, including both terminal values and the exact composition degree.
  Prefix, query-start, builder and replay states are not identified without
  their explicit extension and already charged target conditions.
\<close>

context soundness
begin

lemma fri_mca_accepted_recorded_chains:
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
 obtains trace_layers composition_layers where
   "generic_fri_recorded_value_chain_evidence (staged_trace_fri_roots data)
      (staged_trace_fri_challenges data) (staged_trace_final data)
      (map (\<lambda>raw. index (to_nat raw)) raws) trace_layers"
   "generic_fri_recorded_value_chain_evidence (staged_composition_fri_roots data)
      (staged_composition_fri_challenges data) (staged_composition_final data)
      (map (\<lambda>raw. index (to_nat raw)) raws) composition_layers"
   "generic_fri_recorded_chunks_authenticated (staged_trace_fri_roots data)
      (map (\<lambda>raw. index (to_nat raw)) raws) trace_layers final_state"
   "generic_fri_recorded_chunks_authenticated (staged_composition_fri_roots data)
      (map (\<lambda>raw. index (to_nat raw)) raws) composition_layers final_state"
   "to_nat (staged_degree data) \<le> maxDegree"
proof -
  from
    ro_absorb_checked_staged_first_root_actual_query_accepted_evidence[
      OF wf controlled nonempty builder_out verifier_out final_clean]
  obtain f_fl fl fr f_final as final trace_round_layers
      composition_round_layers where
    fr_eq: "fr = staged_trace_root data"
    and trace_challenges_eq:
      "map fst f_fl = staged_trace_fri_challenges data"
    and trace_roots_eq:
      "map snd f_fl = staged_trace_fri_roots data"
    and trace_final_eq: "f_final = staged_trace_final data"
    and alphas_eq: "as = staged_alphas data"
    and composition_challenges_eq:
      "map fst fl = staged_composition_fri_challenges data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and composition_final_eq:
      "final = staged_composition_final data"
    and f_fl_nonempty: "f_fl \<noteq> []"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and trace_layers_len:
      "length trace_round_layers = length raws"
    and composition_layers_len:
      "length composition_round_layers = length raws"
    and layer_transcripts:
      "\<forall>j < length raws.
        query_round_fri_layer_transcripts
          (map (\<lambda>raw. index (to_nat raw)) raws ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)
          (trace_round_layers ! j) (composition_round_layers ! j)"
    and raw_bound:
      "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
    and accepted:
      "\<forall>round_idx < length raws.
        ro_recorded_query_fri_accepted_evidence
          fr f_fl f_final as fl final (raws ! round_idx)
          (trace_round_layers ! round_idx)
          (composition_round_layers ! round_idx) final_state"
    .


 have chains:
   "generic_fri_recorded_value_chain_evidence
      (map snd f_fl) (map fst f_fl) f_final (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers \<and>
    generic_fri_recorded_value_chain_evidence
      (map snd fl) (map fst fl) final (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
   by (rule ro_recorded_query_fri_accepted_evidence_all_value_chains[
     OF trace_layers_len composition_layers_len accepted])
 have authenticated:
   "generic_fri_recorded_chunks_authenticated (map snd f_fl)
      (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers final_state \<and>
    generic_fri_recorded_chunks_authenticated (map snd fl)
      (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers final_state"
   by (rule ro_recorded_query_fri_accepted_evidence_all_chunks_authenticated[
     OF trace_layers_len composition_layers_len accepted])
 show thesis
   using that chains authenticated degree_bound trace_challenges_eq trace_roots_eq
     trace_final_eq composition_challenges_eq composition_roots_eq composition_final_eq
   by auto
qed

lemma fri_mca_builder_replay_facts:
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
 shows "attacker_state \<le> final_state"
   and "\<not> hash_map_output_collision attacker_state"
   and "prefix_state \<le> attacker_state"
   and "query_start \<le> attacker_state"
   and "prefix = (staged_trace_root data, [], hd (staged_trace_fri_roots data))"
   and "length (staged_trace_fri_roots data) = ceil_log clength"
   and "length (staged_trace_fri_challenges data) = ceil_log clength"
   and "length (staged_composition_fri_roots data) = ceil_log (Suc (to_nat (staged_degree data)))"
   and "length (staged_composition_fri_challenges data) = ceil_log (Suc (to_nat (staged_degree data)))"
   and "map (\<lambda>raw. index (to_nat raw)) raws \<in> fri_query_index_list_space"
proof -
 have original_out: "Some (data, attacker_state) \<in>
     set_dist (execute (ro_checked_staged_transcript_program A) adversary_initial_state)"
   by (rule ro_checked_staged_transcript_program_with_first_root_projection_outcome[
     OF nonempty builder_out])
 have initial_ext: "attacker_state \<le>
     verifier_state_from_adversary attacker_state (staged_proof_transcript data)"
   by (rule hash_extends_verifier_state_from_adversary_right) (rule hash_ext_refl)
 have replay_ext: "verifier_state_from_adversary attacker_state
     (staged_proof_transcript data) \<le> final_state"
   using ro_checked_staged_transcript_program_ro_verify_monad_sync[
     OF wf controlled original_out verifier_out] by blast
 show ext: "attacker_state \<le> final_state" by (rule hash_ext_trans[OF initial_ext replay_ext])
 show clean: "\<not> hash_map_output_collision attacker_state"
   using hash_map_output_collision_mono[OF _ ext] final_clean by blast
 show "prefix_state \<le> attacker_state"
   using ro_checked_staged_transcript_program_with_first_root_good_fields[
     OF wf controlled nonempty builder_out] by blast
 have query_props: "length raws = rounds \<and> query_start \<le> attacker_state"
   using ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
     OF wf controlled builder_out] by blast
 then show "query_start \<le> attacker_state" by blast
 show "prefix = (staged_trace_root data, [], hd (staged_trace_fri_roots data))"
   using ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
     OF wf controlled nonempty builder_out clean rounds_positive] by blast
 note shape = ro_checked_staged_transcript_program_outcome_shape[OF original_out]
 show "length (staged_trace_fri_roots data) = ceil_log clength"
   and "length (staged_trace_fri_challenges data) = ceil_log clength"
   and "length (staged_composition_fri_roots data) = ceil_log (Suc (to_nat (staged_degree data)))"
   and "length (staged_composition_fri_challenges data) = ceil_log (Suc (to_nat (staged_degree data)))"
   using shape by auto
 show "map (\<lambda>raw. index (to_nat raw)) raws \<in> fri_query_index_list_space"
   unfolding fri_query_index_list_space_def query_sample_space_def
   using query_props index_less_query_sample_space by auto
qed

lemma fri_mca_no_target_subset:
 assumes sub: "R \<subseteq> S"
   and none: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets S s) s u"
 shows "\<not> hash_map_new_output_hit (merkle_prefix_path_targets R s) s u"
 using hash_map_new_output_hit_subset[OF merkle_prefix_path_targets_mono[OF sub]] none
 by blast

lemma fri_mca_builder_no_family_target:
 assumes roots: "set roots \<subseteq> set (staged_trace_fri_roots data) \<union> set (staged_composition_fri_roots data)"
   and none: "\<not> fri_checked_builder_merkle_target_hit data s u"
 shows "\<not> hash_map_new_output_hit (merkle_prefix_path_targets (set roots) s) s u"
 by (rule fri_mca_no_target_subset[OF roots])
    (use none in \<open>simp add: fri_checked_builder_merkle_target_hit_def fri_checked_builder_merkle_targets_def\<close>)

lemma fri_mca_table_common_extension:
 assumes su: "s \<le> u" and bu: "b \<le> u"
   and sno: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {rt} s) s u"
   and bno: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {rt} b) b u"
 shows "conceptual_table s rt n = conceptual_table b rt n"
 using conceptual_table_prefix_stable_if_no_target[OF su sno, of n]
       conceptual_table_prefix_stable_if_no_target[OF bu bno, of n] by simp

lemma fri_mca_trace_initial_table_transport:
 assumes pref: "prefix = (staged_trace_root data, [], hd (staged_trace_fri_roots data))"
   and active: "staged_trace_fri_roots data \<noteq> []"
   and pb: "prefix_state \<le> attacker_state" and bu: "attacker_state \<le> final_state"
   and clean: "\<not> hash_map_output_collision attacker_state"
   and no_prefix: "\<not> hash_map_new_output_hit
     (first_trace_fri_root_prefix_merkle_targets prefix prefix_state) prefix_state final_state"
   and no_builder: "\<not> fri_checked_builder_merkle_target_hit data attacker_state final_state"
 shows "first_trace_fri_root_prefix_first_table prefix prefix_state =
   conceptual_table attacker_state (staged_trace_fri_roots data ! 0)
     (length (fri_canonical_domain_at 0))"
proof -
 let ?rt = "hd (staged_trace_fri_roots data)"
 have pu: "prefix_state \<le> final_state" by (rule hash_ext_trans[OF pb bu])
 have pc: "\<not> hash_map_output_collision prefix_state"
   using hash_map_output_collision_mono[OF _ pb] clean by blast
 have pno: "\<not> hash_map_new_output_hit
     (merkle_prefix_path_targets {staged_trace_root data, ?rt} prefix_state)
     prefix_state final_state"
   using no_prefix unfolding pref first_trace_fri_root_prefix_merkle_targets_def
   by (simp add: pc)
 have pno1: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {?rt} prefix_state)
     prefix_state final_state"
   by (rule fri_mca_no_target_subset[OF _ pno]) auto
 have bno: "\<not> hash_map_new_output_hit
     (merkle_prefix_path_targets (set (staged_trace_fri_roots data)) attacker_state)
     attacker_state final_state"
   by (rule fri_mca_builder_no_family_target[OF _ no_builder]) auto
 have bno1: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {?rt} attacker_state)
     attacker_state final_state"
   by (rule fri_mca_no_target_subset[OF _ bno]) (use active in auto)
 have eq: "conceptual_table prefix_state ?rt (scale*clength) =
     conceptual_table attacker_state ?rt (scale*clength)"
   by (rule fri_mca_table_common_extension[OF pu bu pno1 bno1])
 show ?thesis
   unfolding pref first_trace_fri_root_prefix_first_table_def
   using eq active by (simp add: hd_conv_nth fri_canonical_domain_at_length mult.commute)
qed

lemma fri_mca_composition_initial_table_transport:
 assumes active: "staged_composition_fri_roots data \<noteq> []"
   and qb: "query_start \<le> attacker_state" and bu: "attacker_state \<le> final_state"
   and no_prefix: "\<not> hash_map_new_output_hit
     (ro_actual_query_composition_prefix_targets data query_start) query_start final_state"
   and no_builder: "\<not> fri_checked_builder_merkle_target_hit data attacker_state final_state"
 shows "ro_actual_query_composition_candidate data query_start =
   conceptual_table attacker_state (staged_composition_fri_roots data ! 0)
     (length (fri_canonical_domain_at 0))"
proof -
 let ?rt = "hd (staged_composition_fri_roots data)"
 have qu: "query_start \<le> final_state" by (rule hash_ext_trans[OF qb bu])
 have qno: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {?rt} query_start)
     query_start final_state"
   using no_prefix active unfolding ro_actual_query_composition_prefix_targets_def by simp
 have bno: "\<not> hash_map_new_output_hit
     (merkle_prefix_path_targets (set (staged_composition_fri_roots data)) attacker_state)
     attacker_state final_state"
   by (rule fri_mca_builder_no_family_target[OF _ no_builder]) auto
 have bno1: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {?rt} attacker_state)
     attacker_state final_state"
   by (rule fri_mca_no_target_subset[OF _ bno]) (use active in auto)
 have eq: "conceptual_table query_start ?rt (scale*clength) =
     conceptual_table attacker_state ?rt (scale*clength)"
   by (rule fri_mca_table_common_extension[OF qu bu qno bno1])
 show ?thesis unfolding ro_actual_query_composition_candidate_def
   using eq active by (simp add: hd_conv_nth fri_canonical_domain_at_length mult.commute)
qed

lemma fri_mca_accepted_global_chains:
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
 obtains trace_layers composition_layers where
   "fri_authenticated_global_chain_realizable (clength-1) N
     (staged_trace_fri_roots data) (staged_trace_fri_challenges data) (staged_trace_final data)
     (map (\<lambda>raw. index (to_nat raw)) raws) trace_layers attacker_state final_state"
   "fri_authenticated_global_chain_realizable (to_nat (staged_degree data)) N
     (staged_composition_fri_roots data) (staged_composition_fri_challenges data) (staged_composition_final data)
     (map (\<lambda>raw. index (to_nat raw)) raws) composition_layers attacker_state final_state"
   "to_nat (staged_degree data) \<le> maxDegree"
proof -
 obtain T C where
   tc: "generic_fri_recorded_value_chain_evidence (staged_trace_fri_roots data)
      (staged_trace_fri_challenges data) (staged_trace_final data)
      (map (\<lambda>raw. index (to_nat raw)) raws) T"
   and cc: "generic_fri_recorded_value_chain_evidence (staged_composition_fri_roots data)
      (staged_composition_fri_challenges data) (staged_composition_final data)
      (map (\<lambda>raw. index (to_nat raw)) raws) C"
   and ta: "generic_fri_recorded_chunks_authenticated (staged_trace_fri_roots data)
      (map (\<lambda>raw. index (to_nat raw)) raws) T final_state"
   and ca: "generic_fri_recorded_chunks_authenticated (staged_composition_fri_roots data)
      (map (\<lambda>raw. index (to_nat raw)) raws) C final_state"
   and degree: "to_nat (staged_degree data) \<le> maxDegree"
   by (rule fri_mca_accepted_recorded_chains[OF wf controlled nonempty builder_out verifier_out final_clean])
 note facts = fri_mca_builder_replay_facts[OF wf controlled nonempty builder_out verifier_out final_clean]
 have tn: "\<not> hash_map_new_output_hit
     (merkle_prefix_path_targets (set (staged_trace_fri_roots data)) attacker_state)
     attacker_state final_state"
   by (rule fri_mca_builder_no_family_target[OF _ no_builder]) auto
 have cn: "\<not> hash_map_new_output_hit
     (merkle_prefix_path_targets (set (staged_composition_fri_roots data)) attacker_state)
     attacker_state final_state"
   by (rule fri_mca_builder_no_family_target[OF _ no_builder]) auto
 have dc: "ceil_log (Suc (to_nat (staged_degree data))) \<le> ceil_log (Suc maxDegree)"
   by (rule ceil_log_mono) (use degree in simp)
 have actual_t: "fri_authenticated_global_chain_realizable (clength-1) N
     (staged_trace_fri_roots data) (staged_trace_fri_challenges data) (staged_trace_final data)
     (map (\<lambda>raw. index (to_nat raw)) raws) T attacker_state final_state"
   unfolding fri_authenticated_global_chain_realizable_def
   using tc ta ep tf tn facts(1,2,7,10) clength_pos by auto
 have actual_c: "fri_authenticated_global_chain_realizable (to_nat (staged_degree data)) N
     (staged_composition_fri_roots data) (staged_composition_fri_challenges data) (staged_composition_final data)
     (map (\<lambda>raw. index (to_nat raw)) raws) C attacker_state final_state"
   unfolding fri_authenticated_global_chain_realizable_def
   using cc ca ep cf cn dc facts(1,2,9,10) by auto
 show thesis by (rule that[OF actual_t actual_c degree])
qed

end
end
