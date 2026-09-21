theory Soundness_FRI_Robust_Balanced_Security_Classification
  imports
    Stark.Soundness_FRI_Robust_Security_Classification
    Stark.Soundness_FRI_Robust_Balanced_Trace_Classification
    Stark.Soundness_FRI_Robust_Balanced_Composition_Classification
    Stark.Soundness_FRI_Robust_Balanced_Decoded_Rectangle
    Stark.Soundness_FRI_Robust_Balanced_Challenge_Relation
begin

context soundness
begin

lemma
  ro_absorb_checked_staged_security_clean_robust_classification_balanced_exact_two:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and trace_exact:
      "fri_balanced_exact_list_cap
        (clength - 1) (ceil_log clength) C 2"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_balanced_exact_list_cap d (ceil_log (Suc d)) C 2"
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
        (ro_balanced_decoded_semantic_query_lists C) out \<or>
     ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
        out \<or>
     ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
        out \<or>
     ro_absorb_checked_staged_security_clean_builder_merkle_target_hit out \<or>
     ro_absorb_checked_staged_security_builder_initial_target_hit out \<or>
     ro_absorb_checked_staged_security_builder_relation_transition
       (conditioned_fri_relation_bounded
         (ro_checked_staged_transcript_hash_query_budget_for budgets)
         (balanced_conditioned_trace_fri_bad_challenge_relation C)) out \<or>
     ro_absorb_checked_staged_security_builder_relation_transition
       (conditioned_fri_relation_bounded
         (ro_checked_staged_transcript_hash_query_budget_for budgets)
         (balanced_conditioned_composition_fri_bad_challenge_relation C)) out \<or>
     ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
       (fri_balanced_combined_query_head_lists C) out \<or>
     ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit
       out \<or>
     ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent
       out"
proof -
  from accepted_out obtain full where accepted_eq: "out = Some full"
    unfolding accepted_def by (cases out) auto
  obtain prefix prefix_state data query_start raws query_states
      attacker_state result final_state where
    full_eq:
      "full =
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state)"
    by (cases full) (auto split: prod.splits)
  have out_eq:
      "out =
        Some (((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state), result), final_state)"
    using accepted_eq full_eq by simp
  have outcome:
      "Some
          (((((prefix, prefix_state), data, query_start, raws, query_states),
              attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    using support out_eq by simp
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
    using clean unfolding out_eq final_hash_collision_event_def by simp
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty builder_out])
  have attacker_verifier_ext:
      "attacker_state \<le> verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    by (rule hash_extends_verifier_state_from_adversary_right)
      (rule hash_ext_refl)
  have verifier_final_ext:
      "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data) \<le> final_state"
    using ro_checked_staged_transcript_program_ro_verify_monad_sync[
      OF wf controlled original_out verifier_out]
    by blast
  have attacker_final_ext: "attacker_state \<le> final_state"
    by (rule hash_ext_trans[OF attacker_verifier_ext verifier_final_ext])
  have attacker_clean: "\<not> hash_map_output_collision attacker_state"
  proof
    assume collision: "hash_map_output_collision attacker_state"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[OF collision attacker_final_ext])
    then show False using final_clean by contradiction
  qed
  have degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    using ro_absorb_checked_staged_first_root_actual_query_accepted_evidence[
      OF wf controlled nonempty builder_out verifier_out final_clean]
    by blast
  show ?thesis
  proof (cases
      "PState adversary_initial_state \<in> hash_map_output_values attacker_state")
    case True
    then obtain x where lookup:

        "fmlookup (HashMap attacker_state) x =
          Some (PState adversary_initial_state)"
      unfolding hash_map_output_values_def by blast
    have none: "fmlookup (HashMap adversary_initial_state) x = None"
      unfolding adversary_initial_state_def by simp
    have head_hit:
        "hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state
          (Some ((((prefix, prefix_state), data, query_start, raws,
            query_states), attacker_state)))"
      unfolding hash_new_output_hit_event_def hash_map_new_output_hit_def
      using none lookup by auto
    have initial_event:
        "ro_absorb_checked_staged_security_builder_initial_target_hit out"
      unfolding out_eq
        ro_absorb_checked_staged_security_builder_initial_target_hit_def
        ro_absorb_checked_staged_security_builder_head_event_def
      using head_hit by simp
    then show ?thesis by blast
  next
    case no_initial: False
    let ?trace_table =
      "first_trace_fri_root_prefix_first_table prefix prefix_state"
    let ?composition =
      "ro_actual_query_composition_candidate data query_start"
    let ?d = "to_nat (staged_degree data)"
    let ?decoded_trace =
      "fri_canonical_decoded_table (clength - 1) ?trace_table"
    let ?decoded_composition =
      "fri_canonical_decoded_table ?d ?composition"
    let ?trace_close =
      "fri_rs_distance_to_code
        (fri_padded_degree_bound (clength - 1)) eval_domain
        (nth ?trace_table)
        \<le> fri_balanced_radius (ceil_log clength) C 0"
    let ?composition_close =
      "fri_rs_distance_to_code (fri_padded_degree_bound ?d) eval_domain
        (nth ?composition)
        \<le> fri_balanced_radius (ceil_log (Suc ?d)) C 0"
    show ?thesis
    proof (cases ?trace_close)
      case trace_close: True
      show ?thesis
      proof (cases ?composition_close)
        case composition_close: True
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
              "composition_table_low_degree maxDegree ?decoded_composition \<and>
               all_queries_consistent ?decoded_trace ?decoded_composition
                 (staged_alphas data)")
            case True
            have builder_event:
                "ro_checked_staged_first_root_robust_decoded_all_queries_consistent
                  (Some ((((prefix, prefix_state), data, query_start, raws,
                    query_states), attacker_state)))"
              using True
              unfolding
                ro_checked_staged_first_root_robust_decoded_all_queries_consistent_def
                robust_first_trace_fri_root_prefix_first_table_def Let_def
              by simp
            have event:
                "ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent
                  out"
              using builder_event
              unfolding out_eq
                ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent_def
                ro_absorb_checked_staged_security_builder_head_event_def
              by simp
            then show ?thesis by blast
          next
            case False
            have candidate_eq:
                "ro_actual_query_composition_candidate
                    (ro_query_head_data data) query_start = ?composition"
              unfolding ro_query_head_data_def
                ro_actual_query_composition_candidate_def
              by simp
            have degree_eq:
                "to_nat (staged_degree (ro_query_head_data data)) = ?d"
              unfolding ro_query_head_data_def by simp
            have alphas_eq:
                "staged_alphas (ro_query_head_data data) =
                  staged_alphas data"
              unfolding ro_query_head_data_def by simp
            have accepted_indices_eq:
                "ro_actual_query_trace_composition_accepted_indices
                    prefix prefix_state (ro_query_head_data data) query_start =
                  ro_actual_query_trace_composition_accepted_indices
                    prefix prefix_state data query_start"
              unfolding
                ro_actual_query_trace_composition_accepted_indices_def
                ro_query_head_data_def
                ro_actual_query_composition_candidate_def
              by simp
            have semantic_member:
                "map (\<lambda>raw. index (to_nat raw)) raws \<in>
                  ro_balanced_decoded_semantic_query_lists C
                    prefix prefix_state (ro_query_head_data data) query_start"
              using degree_bound trace_close composition_close False
                accepted_queries
              unfolding ro_balanced_decoded_semantic_query_lists_def
                ro_balanced_decoded_semantic_query_indices_def Let_def
                ro_actual_query_trace_composition_accepted_query_lists_def
                query_index_lists_over_def fri_conditioned_query_lists_def
              by (simp add: candidate_eq degree_eq alphas_eq
                accepted_indices_eq)
            have event:
                "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
                  (ro_balanced_decoded_semantic_query_lists C) out"
              using semantic_member
              unfolding out_eq

                ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
                ro_query_head_dependent_actual_query_index_list_hit_def
              by simp
            then show ?thesis by blast
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
              unfolding out_eq
                ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def
              by simp
            then show ?thesis by blast
          next
            assume composition_target:
                "hash_map_new_output_hit
                  (ro_actual_query_composition_prefix_targets data query_start)
                  query_start final_state"
            have event:
                "ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
                  out"
              using clean composition_target
              unfolding out_eq
                ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
                ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
              by simp
            then show ?thesis by blast
          qed
        qed
      next
        case composition_far: False
        have split:
            "hash_map_new_output_hit
                (ro_actual_query_composition_prefix_targets data query_start)
                query_start final_state \<or>
             fri_checked_builder_merkle_target_hit
                data attacker_state final_state \<or>
             hash_state_relation_transition
                (conditioned_fri_relation_bounded
                  (ro_checked_staged_transcript_hash_query_budget_for budgets)
                  (balanced_conditioned_composition_fri_bad_challenge_relation C))
                (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
             hash_map_new_output_hit
                (fri_checked_builder_merkle_targets data query_start)
                query_start attacker_state \<or>
             ro_query_head_dependent_actual_query_index_list_hit
                (fri_balanced_combined_query_head_lists C)
                (Some ((((prefix, prefix_state), data, query_start, raws,
                  query_states), attacker_state)))"
          by (rule
            checked_builder_composition_not_robust_close_imp_residual_or_targets_balanced_exact_two[
              OF wf controlled nonempty eval_power composition_rounds_fit
                composition_exact builder_out verifier_out final_clean
                no_initial composition_far])
        then show ?thesis
        proof
          assume composition_target:
              "hash_map_new_output_hit
                (ro_actual_query_composition_prefix_targets data query_start)
                query_start final_state"
          have event:
              "ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
                out"
            using clean composition_target
            unfolding out_eq
              ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
              ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
            by simp
          then show ?thesis by blast
        next
          assume side:
              "fri_checked_builder_merkle_target_hit
                  data attacker_state final_state \<or>
               hash_state_relation_transition
                  (conditioned_fri_relation_bounded
                    (ro_checked_staged_transcript_hash_query_budget_for budgets)
                    (balanced_conditioned_composition_fri_bad_challenge_relation C))
                  (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
               hash_map_new_output_hit
                  (fri_checked_builder_merkle_targets data query_start)
                  query_start attacker_state \<or>
               ro_query_head_dependent_actual_query_index_list_hit
                  (fri_balanced_combined_query_head_lists C)
                  (Some ((((prefix, prefix_state), data, query_start, raws,
                    query_states), attacker_state)))"
          have lifted:
              "ro_absorb_checked_staged_security_clean_builder_merkle_target_hit
                  out \<or>
               ro_absorb_checked_staged_security_builder_relation_transition
                  (conditioned_fri_relation_bounded
                    (ro_checked_staged_transcript_hash_query_budget_for budgets)
                    (balanced_conditioned_composition_fri_bad_challenge_relation C))
                  out \<or>
               ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit
                  out \<or>
               ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
                  (fri_balanced_combined_query_head_lists C) out"
            by (rule ro_robust_builder_side_events_lift[
              OF out_eq clean attacker_clean side])
          then show ?thesis by blast
        qed
      qed
    next
      case trace_far: False
      have split:
          "hash_map_new_output_hit
              (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
              prefix_state final_state \<or>
           fri_checked_builder_merkle_target_hit
              data attacker_state final_state \<or>
           hash_state_relation_transition
              (conditioned_fri_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets)
                (balanced_conditioned_trace_fri_bad_challenge_relation C))
              (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
           hash_map_new_output_hit

              (fri_checked_builder_merkle_targets data query_start)
              query_start attacker_state \<or>
           ro_query_head_dependent_actual_query_index_list_hit
              (fri_balanced_combined_query_head_lists C)
              (Some ((((prefix, prefix_state), data, query_start, raws,
                query_states), attacker_state)))"
        by (rule
          checked_builder_trace_not_robust_close_imp_residual_or_targets_balanced_exact_two[
            OF wf controlled nonempty eval_power trace_rounds_fit
              trace_exact builder_out verifier_out final_clean
              no_initial trace_far])
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
          unfolding out_eq
            ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def
          by simp
        then show ?thesis by blast
      next
        assume side:
            "fri_checked_builder_merkle_target_hit
                data attacker_state final_state \<or>
             hash_state_relation_transition
                (conditioned_fri_relation_bounded
                  (ro_checked_staged_transcript_hash_query_budget_for budgets)
                  (balanced_conditioned_trace_fri_bad_challenge_relation C))
                (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
             hash_map_new_output_hit
                (fri_checked_builder_merkle_targets data query_start)
                query_start attacker_state \<or>
             ro_query_head_dependent_actual_query_index_list_hit
                (fri_balanced_combined_query_head_lists C)
                (Some ((((prefix, prefix_state), data, query_start, raws,
                  query_states), attacker_state)))"
        have lifted:
            "ro_absorb_checked_staged_security_clean_builder_merkle_target_hit
                out \<or>
             ro_absorb_checked_staged_security_builder_relation_transition
                (conditioned_fri_relation_bounded
                  (ro_checked_staged_transcript_hash_query_budget_for budgets)
                  (balanced_conditioned_trace_fri_bad_challenge_relation C))
                out \<or>
             ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit
                out \<or>
             ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
                (fri_balanced_combined_query_head_lists C) out"
          by (rule ro_robust_builder_side_events_lift[
            OF out_eq clean attacker_clean side])
        then show ?thesis by blast
      qed
    qed
  qed
qed


definition ro_absorb_checked_staged_balanced_obstruction_union
where
  "ro_absorb_checked_staged_balanced_obstruction_union C budgets out \<longleftrightarrow>
    final_hash_collision_event out \<or>
    ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      (ro_balanced_decoded_semantic_query_lists C) out \<or>
    ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
      out \<or>
    ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
      out \<or>
    ro_absorb_checked_staged_security_clean_builder_merkle_target_hit out \<or>
    ro_absorb_checked_staged_security_builder_initial_target_hit out \<or>
    ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (balanced_conditioned_trace_fri_bad_challenge_relation C)) out \<or>
    ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (balanced_conditioned_composition_fri_bad_challenge_relation C)) out \<or>
    ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      (fri_balanced_combined_query_head_lists C) out \<or>
    ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit
      out \<or>
    ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent
      out"

lemma
  wp_ro_absorb_checked_staged_security_acceptance_le_robust_obstruction_union_balanced_exact_two:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and trace_exact:
      "fri_balanced_exact_list_cap
        (clength - 1) (ceil_log clength) C 2"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_balanced_exact_list_cap d (ceil_log (Suc d)) C 2"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le>
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        (ro_absorb_checked_staged_balanced_obstruction_union C budgets)
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
      "ro_absorb_checked_staged_balanced_obstruction_union C budgets out"
  proof (cases "final_hash_collision_event out")
    case True
    then show ?thesis
      unfolding ro_absorb_checked_staged_balanced_obstruction_union_def
      by simp
  next
    case False
    from
      ro_absorb_checked_staged_security_clean_robust_classification_balanced_exact_two[
        OF wf controlled nonempty eval_power trace_rounds_fit
          composition_rounds_fit trace_exact composition_exact
          accepted_out support False]
    show ?thesis
      unfolding ro_absorb_checked_staged_balanced_obstruction_union_def
      by blast
  qed
qed

end
end
