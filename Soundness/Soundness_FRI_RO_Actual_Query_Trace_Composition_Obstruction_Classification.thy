(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Trace_Composition_Obstruction_Classification.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Obstruction_Classification
  imports
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Security_Query_Bound
begin

context soundness
begin

definition
  ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
where
  "ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
        composition_table_low_degree maxDegree
          (ro_actual_query_composition_candidate data query_start) \<and>
        all_queries_consistent
          (first_trace_fri_root_prefix_first_table prefix prefix_state)
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data))"

lemma
  ro_absorb_checked_staged_security_with_first_root_clean_trace_composition_classification:
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
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_trace_composition_good_query_lists out \<or>
     ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
       out"
proof -
  from accepted_out obtain full where out_eq: "out = Some full"
    unfolding accepted_def by (cases out) auto
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
  have trace_class:
      "ro_absorb_checked_staged_security_with_first_root_trace_candidate_ready
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
         out"
    by (rule
      ro_absorb_checked_staged_security_with_first_root_clean_trace_candidate_classification[
        OF wf controlled nonempty accepted_out support clean])
  then show ?thesis
  proof
    assume ready:
      "ro_absorb_checked_staged_security_with_first_root_trace_candidate_ready
        out"
    have trace_low:
        "trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state)"
      using ready
      unfolding out_eq full_eq
        ro_absorb_checked_staged_security_with_first_root_trace_candidate_ready_def
      by simp
    have composition_class:
        "(case out of
          None \<Rightarrow> False
        | Some
            (((((prefix, prefix_state), data, query_start, raws, query_states),
                attacker_state), result), final_state) \<Rightarrow>
            composition_table_low_degree maxDegree
              (ro_actual_query_composition_candidate data query_start)) \<or>
         ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
           out \<or>
         ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
           out"
      by (rule
        ro_absorb_checked_staged_security_with_first_root_clean_composition_candidate_classification[
          OF wf controlled nonempty accepted_out support clean])
    then show ?thesis
    proof
      assume low_case:
        "case out of
          None \<Rightarrow> False
        | Some
            (((((prefix, prefix_state), data, query_start, raws, query_states),
                attacker_state), result), final_state) \<Rightarrow>
            composition_table_low_degree maxDegree
              (ro_actual_query_composition_candidate data query_start)"
      have composition_low:
          "composition_table_low_degree maxDegree
            (ro_actual_query_composition_candidate data query_start)"
        using low_case unfolding out_eq full_eq by simp
      have indices_or_targets:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
              ro_actual_query_trace_composition_accepted_query_lists
                prefix prefix_state data query_start \<or>
           hash_map_new_output_hit
             (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
             prefix_state final_state \<or>
           hash_map_new_output_hit
             (ro_actual_query_composition_prefix_targets data query_start)
             query_start final_state"
        by (rule
          ro_absorb_checked_staged_first_root_actual_query_trace_composition_indices_or_targets[
            OF wf controlled nonempty builder_out verifier_out final_clean])
      then show ?thesis
      proof
        assume accepted_queries:
            "map (\<lambda>raw. index (to_nat raw)) raws \<in>
              ro_actual_query_trace_composition_accepted_query_lists
                prefix prefix_state data query_start"
        show ?thesis
        proof (cases
            "all_queries_consistent
              (first_trace_fri_root_prefix_first_table prefix prefix_state)
              (ro_actual_query_composition_candidate data query_start)
              (staged_alphas data)")
          case True
          have event:
              "ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
                out"
            using trace_low composition_low True
            unfolding out_eq full_eq
              ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent_def
            by simp
          then show ?thesis by simp
        next
          case False
          have candidate_eq:
              "ro_actual_query_composition_candidate
                  (ro_query_head_data data) query_start =
                ro_actual_query_composition_candidate data query_start"
            unfolding ro_query_head_data_def
              ro_actual_query_composition_candidate_def
            by simp
          have accepted_eq:
              "ro_actual_query_trace_composition_accepted_query_lists
                  prefix prefix_state (ro_query_head_data data) query_start =
                ro_actual_query_trace_composition_accepted_query_lists
                  prefix prefix_state data query_start"
            unfolding ro_query_head_data_def
              ro_actual_query_trace_composition_accepted_query_lists_def
              ro_actual_query_trace_composition_accepted_indices_def
              ro_actual_query_composition_candidate_def
            by simp
          have alphas_eq:
              "staged_alphas (ro_query_head_data data) = staged_alphas data"
            unfolding ro_query_head_data_def by simp
          have good_member:
              "map (\<lambda>raw. index (to_nat raw)) raws \<in>
                ro_actual_query_trace_composition_good_query_lists
                  prefix prefix_state (ro_query_head_data data) query_start"
            using trace_low composition_low False accepted_queries
            unfolding ro_actual_query_trace_composition_good_query_lists_def
            by (simp add: candidate_eq accepted_eq alphas_eq)
          have event:
              "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
                ro_actual_query_trace_composition_good_query_lists out"
            using good_member
            unfolding out_eq full_eq
              ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
              ro_query_head_dependent_actual_query_index_list_hit_def
            by simp
          then show ?thesis by simp
        qed
      next
        assume targets:
            "hash_map_new_output_hit
               (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
               prefix_state final_state \<or>
             hash_map_new_output_hit
               (ro_actual_query_composition_prefix_targets data query_start)
               query_start final_state"
        then show ?thesis
        proof
          assume trace_target:
              "hash_map_new_output_hit
                (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
                prefix_state final_state"
          have event:
              "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
                out"
            using trace_target
            unfolding out_eq full_eq
              ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def
            by simp
          then show ?thesis by simp
        next
          assume composition_target:
              "hash_map_new_output_hit
                (ro_actual_query_composition_prefix_targets data query_start)
                query_start final_state"
          have event:
              "ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
                out"
            using composition_target
            unfolding out_eq full_eq
              ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
            by simp
          then show ?thesis by simp
        qed
      qed
    next
      assume composition_side:
          "ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
             out \<or>
           ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
             out"
      then show ?thesis by blast
    qed
  next
    assume trace_side:
        "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
           out \<or>
         ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
           out"
    then show ?thesis by blast
  qed
qed


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_le_trace_composition_obstruction_union:
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
          ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
            ro_actual_query_trace_composition_good_query_lists out \<or>
          ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
            out)
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
       ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
         ro_actual_query_trace_composition_good_query_lists out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
         out"
  proof (cases "final_hash_collision_event out")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis
      using
        ro_absorb_checked_staged_security_with_first_root_clean_trace_composition_classification[
          OF wf controlled nonempty accepted_out support False]
      by simp
  qed
qed

end
end
