theory Soundness_FRI_Conditioned_Explicit_Complete_List_Security_Classification
  imports
    Stark.Soundness_FRI_Conditioned_Explicit_Security_Events
    Stark.Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Security_Bound
    Stark.Soundness_FRI_Conditioned_Security_Target_Bound
    Stark.Soundness_FRI_Conditioned_Explicit_Residual_Query_Phase_Target
    Stark.Soundness_FRI_Conditioned_Explicit_Complete_List_Padding_Zero
begin

context soundness
begin

definition
  ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit
where
  "ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit out \<longleftrightarrow>
    ro_absorb_checked_staged_security_builder_head_event
      ro_query_head_dependent_fri_builder_merkle_target_hit out"

lemma
  ro_absorb_checked_staged_security_clean_conditioned_explicit_complete_list_classification:
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
     ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
        out \<or>
     ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
        out \<or>
     ro_absorb_checked_staged_security_clean_builder_merkle_target_hit out \<or>
     ro_absorb_checked_staged_security_builder_initial_target_hit out \<or>
     ro_absorb_checked_staged_security_builder_relation_transition
       (conditioned_fri_relation_bounded
         (ro_checked_staged_transcript_hash_query_budget_for budgets)
         conditioned_trace_fri_bad_challenge_relation) out \<or>
     ro_absorb_checked_staged_security_builder_relation_transition
       (conditioned_fri_relation_bounded
         (ro_checked_staged_transcript_hash_query_budget_for budgets)
         conditioned_composition_fri_bad_challenge_relation) out \<or>
     ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
       fri_conditioned_combined_query_head_lists out \<or>
     ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit out \<or>
     ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
       ro_trace_composition_padding_query_head_lists out \<or>
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
  show ?thesis
  proof (cases
      "PState adversary_initial_state \<in> hash_map_output_values attacker_state")
    case True
    then obtain x where lookup:
        "fmlookup (HashMap attacker_state) x =
          Some (PState adversary_initial_state)"
      unfolding hash_map_output_values_def
      by blast
    have none:
        "fmlookup (HashMap adversary_initial_state) x = None"
      unfolding adversary_initial_state_def
      by simp
    have head_hit:
        "hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state
          (Some ((((prefix, prefix_state), data, query_start, raws,
            query_states), attacker_state)))"
      unfolding hash_new_output_hit_event_def hash_map_new_output_hit_def
      using none lookup
      by auto
    have initial_event:
        "ro_absorb_checked_staged_security_builder_initial_target_hit out"
      unfolding out_eq full_eq
        ro_absorb_checked_staged_security_builder_initial_target_hit_def
        ro_absorb_checked_staged_security_builder_head_event_def
      using head_hit
      by simp
    then show ?thesis by blast
  next
    case no_initial: False
    show ?thesis
    proof (cases
        "trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state)")
      case first_trace_low: True
      show ?thesis
      proof (cases
          "composition_table_low_degree maxDegree
            (ro_actual_query_composition_candidate data query_start)")
        case composition_low: True
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
              using first_trace_low composition_low True
              unfolding out_eq full_eq
                ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent_def
              by simp
            then show ?thesis by blast
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
              using first_trace_low composition_low False accepted_queries
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
              unfolding out_eq full_eq
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
              unfolding out_eq full_eq
                ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
                ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
              by simp
            then show ?thesis by blast
          qed
        qed
      next
        case composition_bad: False
        show ?thesis
        proof (cases
            "composition_table_low_degree
              (fri_padded_degree_bound (to_nat (staged_degree data)))
              (ro_actual_query_composition_candidate data query_start)")
          case padded_low: True
          have split:
              "ro_query_head_dependent_actual_query_index_list_hit
                  ro_trace_composition_padding_query_head_lists
                  (Some ((((prefix, prefix_state), data, query_start, raws,
                    query_states), attacker_state))) \<or>
               hash_map_new_output_hit
                  (first_trace_fri_root_prefix_merkle_targets
                    prefix prefix_state)
                  prefix_state final_state \<or>
               hash_map_new_output_hit
                  (ro_actual_query_composition_prefix_targets data query_start)
                  query_start final_state"
            by (rule
              checked_builder_trace_composition_padding_bad_imp_actual_or_targets[
                OF wf controlled nonempty builder_out verifier_out final_clean
                  first_trace_low padded_low composition_bad])
          then show ?thesis
          proof
            assume actual:
                "ro_query_head_dependent_actual_query_index_list_hit
                  ro_trace_composition_padding_query_head_lists
                  (Some ((((prefix, prefix_state), data, query_start, raws,
                    query_states), attacker_state)))"
            have event:
                "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
                  ro_trace_composition_padding_query_head_lists out"
              using actual
              unfolding out_eq full_eq
                ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
              by simp
            then show ?thesis by blast
          next
            assume targets:
              "hash_map_new_output_hit
                  (first_trace_fri_root_prefix_merkle_targets
                    prefix prefix_state)
                  prefix_state final_state \<or>
               hash_map_new_output_hit
                  (ro_actual_query_composition_prefix_targets data query_start)
                  query_start final_state"
            then show ?thesis
            proof
              assume trace_target:
                "hash_map_new_output_hit
                  (first_trace_fri_root_prefix_merkle_targets
                    prefix prefix_state)
                  prefix_state final_state"
              have event:
                  "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
                    out"
                using trace_target
                unfolding out_eq full_eq
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
                unfolding out_eq full_eq
                  ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
                  ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
                by simp
              then show ?thesis by blast
            qed
          qed        next
          case padded_bad: False
          have split:
              "hash_map_new_output_hit
                  (ro_actual_query_composition_prefix_targets data query_start)
                  query_start final_state \<or>
               fri_checked_builder_merkle_target_hit
                  data attacker_state final_state \<or>
               hash_state_relation_transition
                  (conditioned_fri_relation_bounded
                    (ro_checked_staged_transcript_hash_query_budget_for budgets)
                    conditioned_composition_fri_bad_challenge_relation)
                  (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
               hash_map_new_output_hit
                  (fri_checked_builder_merkle_targets data query_start)
                  query_start attacker_state \<or>
               ro_query_head_dependent_actual_query_index_list_hit
                  fri_conditioned_combined_query_head_lists
                  (Some ((((prefix, prefix_state), data, query_start, raws,
                    query_states), attacker_state)))"
            by (rule
              checked_builder_composition_padded_candidate_bad_imp_actual_residual_or_targets[
                OF wf controlled nonempty builder_out verifier_out final_clean
                  no_initial padded_bad])
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
              unfolding out_eq full_eq
                ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
                ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
              by simp
            then show ?thesis by blast
          next
            assume rest:
                "fri_checked_builder_merkle_target_hit
                    data attacker_state final_state \<or>
                 hash_state_relation_transition
                    (conditioned_fri_relation_bounded
                      (ro_checked_staged_transcript_hash_query_budget_for budgets)
                      conditioned_composition_fri_bad_challenge_relation)
                    (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
                 hash_map_new_output_hit
                    (fri_checked_builder_merkle_targets data query_start)
                    query_start attacker_state \<or>
                 ro_query_head_dependent_actual_query_index_list_hit
                    fri_conditioned_combined_query_head_lists
                    (Some ((((prefix, prefix_state), data, query_start, raws,
                      query_states), attacker_state)))"
            then show ?thesis
            proof
              assume builder_target:
                  "fri_checked_builder_merkle_target_hit
                    data attacker_state final_state"
              have event:
                  "ro_absorb_checked_staged_security_clean_builder_merkle_target_hit
                    out"
                using clean builder_target
                unfolding out_eq full_eq
                  ro_absorb_checked_staged_security_clean_builder_merkle_target_hit_def
                  final_hash_collision_event_def
                by simp
              then show ?thesis by blast
            next
              assume transitions:
                  "hash_state_relation_transition
                      (conditioned_fri_relation_bounded
                        (ro_checked_staged_transcript_hash_query_budget_for budgets)
                        conditioned_composition_fri_bad_challenge_relation)
                      (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
                   hash_map_new_output_hit
                      (fri_checked_builder_merkle_targets data query_start)
                      query_start attacker_state \<or>
                   ro_query_head_dependent_actual_query_index_list_hit
                      fri_conditioned_combined_query_head_lists
                      (Some ((((prefix, prefix_state), data, query_start, raws,
                        query_states), attacker_state)))"
              then show ?thesis
              proof
                assume transition:
                    "hash_state_relation_transition
                      (conditioned_fri_relation_bounded
                        (ro_checked_staged_transcript_hash_query_budget_for budgets)
                        conditioned_composition_fri_bad_challenge_relation)
                      (HashMap adversary_initial_state) (HashMap attacker_state)"
                have event:
                    "ro_absorb_checked_staged_security_builder_relation_transition
                      (conditioned_fri_relation_bounded
                        (ro_checked_staged_transcript_hash_query_budget_for budgets)
                        conditioned_composition_fri_bad_challenge_relation)
                      out"
                  using transition
                  unfolding out_eq full_eq
                    ro_absorb_checked_staged_security_builder_relation_transition_def
                    ro_absorb_checked_staged_security_builder_head_event_def
                    hash_state_relation_transition_event_def
                  by simp
                then show ?thesis by blast
              next
                assume residual:
                    "hash_map_new_output_hit
                       (fri_checked_builder_merkle_targets data query_start)
                       query_start attacker_state \<or>
                     ro_query_head_dependent_actual_query_index_list_hit
                       fri_conditioned_combined_query_head_lists
                       (Some ((((prefix, prefix_state), data, query_start, raws,
                         query_states), attacker_state)))"
                then show ?thesis
                proof
                  assume query_target:
                      "hash_map_new_output_hit
                        (fri_checked_builder_merkle_targets data query_start)
                        query_start attacker_state"
                  have event:
                      "ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit
                        out"
                    using attacker_clean query_target
                    unfolding out_eq full_eq
                      ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit_def
                      ro_absorb_checked_staged_security_builder_head_event_def
                      ro_query_head_dependent_fri_builder_merkle_target_hit_def
                      ro_query_head_data_def
                      fri_checked_builder_merkle_targets_def
                    by simp
                  then show ?thesis by blast
                next
                  assume actual:
                      "ro_query_head_dependent_actual_query_index_list_hit
                        fri_conditioned_combined_query_head_lists
                        (Some ((((prefix, prefix_state), data, query_start,
                          raws, query_states), attacker_state)))"
                  have event:
                      "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
                        fri_conditioned_combined_query_head_lists out"
                    using actual
                    unfolding out_eq full_eq
                      ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
                    by simp
                  then show ?thesis by blast
                qed
              qed
            qed
            qed
          qed
    qed
    next
      case first_trace_bad: False
      have split:
          "hash_map_new_output_hit
              (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
              prefix_state final_state \<or>
           fri_checked_builder_merkle_target_hit
              data attacker_state final_state \<or>
           hash_state_relation_transition
              (conditioned_fri_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets)
                conditioned_trace_fri_bad_challenge_relation)
              (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
           hash_map_new_output_hit
              (fri_checked_builder_merkle_targets data query_start)
              query_start attacker_state \<or>
           ro_query_head_dependent_actual_query_index_list_hit
              fri_conditioned_combined_query_head_lists
              (Some ((((prefix, prefix_state), data, query_start, raws,
                query_states), attacker_state)))"
        by (rule
          checked_builder_trace_candidate_bad_imp_actual_residual_or_targets[
            OF wf controlled nonempty builder_out verifier_out final_clean
              no_initial first_trace_bad])
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
        then show ?thesis by blast
      next
        assume rest:
            "fri_checked_builder_merkle_target_hit
                data attacker_state final_state \<or>
             hash_state_relation_transition
                (conditioned_fri_relation_bounded
                  (ro_checked_staged_transcript_hash_query_budget_for budgets)
                  conditioned_trace_fri_bad_challenge_relation)
                (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
             hash_map_new_output_hit
                (fri_checked_builder_merkle_targets data query_start)
                query_start attacker_state \<or>
             ro_query_head_dependent_actual_query_index_list_hit
                fri_conditioned_combined_query_head_lists
                (Some ((((prefix, prefix_state), data, query_start, raws,
                  query_states), attacker_state)))"
        then show ?thesis
        proof
          assume builder_target:
              "fri_checked_builder_merkle_target_hit
                data attacker_state final_state"
          have event:
              "ro_absorb_checked_staged_security_clean_builder_merkle_target_hit
                out"
            using clean builder_target
            unfolding out_eq full_eq
              ro_absorb_checked_staged_security_clean_builder_merkle_target_hit_def
              final_hash_collision_event_def
            by simp
          then show ?thesis by blast
        next
          assume transitions:
              "hash_state_relation_transition
                  (conditioned_fri_relation_bounded
                    (ro_checked_staged_transcript_hash_query_budget_for budgets)
                    conditioned_trace_fri_bad_challenge_relation)
                  (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
               hash_map_new_output_hit
                  (fri_checked_builder_merkle_targets data query_start)
                  query_start attacker_state \<or>
               ro_query_head_dependent_actual_query_index_list_hit
                  fri_conditioned_combined_query_head_lists
                  (Some ((((prefix, prefix_state), data, query_start, raws,
                    query_states), attacker_state)))"
          then show ?thesis
          proof
            assume transition:
                "hash_state_relation_transition
                  (conditioned_fri_relation_bounded
                    (ro_checked_staged_transcript_hash_query_budget_for budgets)
                    conditioned_trace_fri_bad_challenge_relation)
                  (HashMap adversary_initial_state) (HashMap attacker_state)"
            have event:
                "ro_absorb_checked_staged_security_builder_relation_transition
                  (conditioned_fri_relation_bounded
                    (ro_checked_staged_transcript_hash_query_budget_for budgets)
                    conditioned_trace_fri_bad_challenge_relation)
                  out"
              using transition
              unfolding out_eq full_eq
                ro_absorb_checked_staged_security_builder_relation_transition_def
                ro_absorb_checked_staged_security_builder_head_event_def
                hash_state_relation_transition_event_def
              by simp
            then show ?thesis by blast
          next
            assume residual:
                "hash_map_new_output_hit
                    (fri_checked_builder_merkle_targets data query_start)
                    query_start attacker_state \<or>
                 ro_query_head_dependent_actual_query_index_list_hit
                    fri_conditioned_combined_query_head_lists
                    (Some ((((prefix, prefix_state), data, query_start, raws,
                      query_states), attacker_state)))"
            then show ?thesis
            proof
              assume query_target:
                  "hash_map_new_output_hit
                    (fri_checked_builder_merkle_targets data query_start)
                    query_start attacker_state"
              have event:
                  "ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit
                    out"
                using attacker_clean query_target
                unfolding out_eq full_eq
                  ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit_def
                  ro_absorb_checked_staged_security_builder_head_event_def
                  ro_query_head_dependent_fri_builder_merkle_target_hit_def
                  ro_query_head_data_def
                  fri_checked_builder_merkle_targets_def
                by simp
              then show ?thesis by blast
            next
              assume actual:
                  "ro_query_head_dependent_actual_query_index_list_hit
                    fri_conditioned_combined_query_head_lists
                    (Some ((((prefix, prefix_state), data, query_start,
                      raws, query_states), attacker_state)))"
              have event:
                  "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
                    fri_conditioned_combined_query_head_lists out"
                using actual
                unfolding out_eq full_eq
                  ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
                by simp
              then show ?thesis by blast
            qed
          qed
        qed
      qed
    qed
  qed
qed

definition
  ro_absorb_checked_staged_conditioned_explicit_complete_list_obstruction_union
where
  "ro_absorb_checked_staged_conditioned_explicit_complete_list_obstruction_union budgets out \<longleftrightarrow>
    final_hash_collision_event out \<or>
    ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      ro_actual_query_trace_composition_good_query_lists out \<or>
    ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
      out \<or>
    ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
      out \<or>
    ro_absorb_checked_staged_security_clean_builder_merkle_target_hit out \<or>
    ro_absorb_checked_staged_security_builder_initial_target_hit out \<or>
    ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        conditioned_trace_fri_bad_challenge_relation) out \<or>
    ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        conditioned_composition_fri_bad_challenge_relation) out \<or>
    ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      fri_conditioned_combined_query_head_lists out \<or>
    ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit out \<or>
    ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      ro_trace_composition_padding_query_head_lists out \<or>    ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
      out"

lemma
  wp_ro_absorb_checked_staged_security_acceptance_le_conditioned_explicit_complete_list_obstruction_union:
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
        (ro_absorb_checked_staged_conditioned_explicit_complete_list_obstruction_union budgets)
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
      "ro_absorb_checked_staged_conditioned_explicit_complete_list_obstruction_union
        budgets out"
  proof (cases "final_hash_collision_event out")
    case True
    then show ?thesis
      unfolding
        ro_absorb_checked_staged_conditioned_explicit_complete_list_obstruction_union_def
      by simp
  next
    case False
    from
      ro_absorb_checked_staged_security_clean_conditioned_explicit_complete_list_classification[
        OF wf controlled nonempty accepted_out support False]
    show ?thesis
      unfolding
        ro_absorb_checked_staged_conditioned_explicit_complete_list_obstruction_union_def
      by blast
  qed
qed

end
end