theory Soundness_FRI_Conditioned_Zero_Round_Security
  imports
    Stark.Soundness_FRI_Conditioned_Zero_Round_Outcome_Bridge
    Stark.Soundness_FRI_Conditioned_Explicit_Security_Events
    Stark.Soundness_FRI_RO_Actual_Query_Zero_Round_Parameter_Bound
begin

context soundness
begin

definition ro_checked_staged_conditioned_zero_round_composition_padding_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_zero_round_composition_padding_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in nnreal
       (q * (composition_padding_query_raw_fiber_bound + (5 * q + 2))) /
       nnreal size)"

lemma
  wp_ro_absorb_checked_staged_security_builder_zero_round_composition_padding_transition_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          composition_padding_absorbed_query_relation))
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_zero_round_composition_padding_error budgets"
proof -
  have lift:
      "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        (ro_absorb_checked_staged_security_builder_relation_transition
          (conditioned_fri_relation_bounded
            (ro_checked_staged_transcript_hash_query_budget_for budgets)
            composition_padding_absorbed_query_relation))
        adversary_initial_state
      \<le>
      wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (conditioned_fri_relation_bounded
            (ro_checked_staged_transcript_hash_query_budget_for budgets)
            composition_padding_absorbed_query_relation)
          (HashMap adversary_initial_state))
        adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_relation_transition_le)
  have head:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (conditioned_fri_relation_bounded
            (ro_checked_staged_transcript_hash_query_budget_for budgets)
            composition_padding_absorbed_query_relation)
          (HashMap adversary_initial_state))
        adversary_initial_state
      \<le> ro_checked_staged_conditioned_zero_round_composition_padding_error budgets"
    unfolding
      ro_checked_staged_conditioned_zero_round_composition_padding_error_def
      Let_def
    by (rule
      wp_ro_checked_staged_transcript_with_query_witnesses_composition_padding_relation[
        OF wf controlled])
  show ?thesis by (rule order_trans[OF lift head])
qed

lemma
  ro_absorb_checked_staged_security_clean_conditioned_explicit_zero_round_classification:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
        ro_actual_query_zero_round_bad_query_lists out \<or>
     ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit out \<or>
     ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_zero_round_trace_composition_good_query_lists_for out \<or>
     ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
        out \<or>
     ro_absorb_checked_staged_security_clean_builder_merkle_target_hit out \<or>
     ro_absorb_checked_staged_security_builder_initial_target_hit out \<or>
     ro_absorb_checked_staged_security_builder_relation_transition
       (conditioned_fri_relation_bounded
         (ro_checked_staged_transcript_hash_query_budget_for budgets)
         conditioned_composition_fri_bad_challenge_relation) out \<or>
     ro_absorb_checked_staged_security_builder_relation_transition
       (conditioned_fri_relation_bounded
         (ro_checked_staged_transcript_hash_query_budget_for budgets)
         ro_conditioned_augmented_absorbed_query_relation) out \<or>
     ro_absorb_checked_staged_security_builder_relation_transition
       (conditioned_fri_relation_bounded
         (ro_checked_staged_transcript_hash_query_budget_for budgets)
         composition_padding_absorbed_query_relation) out \<or>
     ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent
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
    have trace_class:
        "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
            ro_actual_query_zero_round_bad_query_lists out \<or>
         ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit out \<or>
         ro_absorb_checked_staged_security_zero_round_trace_low_degree out"
      by (rule
        ro_absorb_checked_staged_security_clean_zero_round_trace_classification[
          OF zero wf controlled accepted_out support clean])
    then consider
        (trace_bad)
          "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
            ro_actual_query_zero_round_bad_query_lists out"
      | (trace_target)
          "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit out"
      | (trace_low)
          "ro_absorb_checked_staged_security_zero_round_trace_low_degree out"
      by blast
    then show ?thesis
    proof cases
      case trace_bad
      then show ?thesis by blast
    next
      case trace_target
      then show ?thesis by blast
    next
      case trace_low
      have trace_low_concrete:
          "trace_table_low_degree
            (ro_actual_query_zero_round_trace_table data prefix_state)"
        using trace_low
        unfolding out_eq full_eq
          ro_absorb_checked_staged_security_zero_round_trace_low_degree_def
        by simp
      show ?thesis
      proof (cases
          "composition_table_low_degree maxDegree
            (ro_actual_query_composition_candidate data query_start)")
        case composition_low: True
        have consistent_or_targets:
            "(\<forall>j < length raws.
              query_consistent_at
                (ro_actual_query_zero_round_trace_table data prefix_state)
                (ro_actual_query_composition_candidate data query_start)
                (staged_alphas data) (index (to_nat (raws ! j)))) \<or>
             hash_map_new_output_hit
               (ro_zero_round_first_root_prefix_merkle_targets
                 prefix prefix_state)
               prefix_state final_state \<or>
             hash_map_new_output_hit
               (ro_actual_query_composition_prefix_targets data query_start)
               query_start final_state"
          by (rule
            ro_absorb_checked_staged_zero_round_actual_query_conceptual_consistency_or_targets[
              OF zero wf controlled builder_out verifier_out final_clean])
        then show ?thesis
        proof
          assume sampled_consistent:
              "\<forall>j < length raws.
                query_consistent_at
                  (ro_actual_query_zero_round_trace_table data prefix_state)
                  (ro_actual_query_composition_candidate data query_start)
                  (staged_alphas data) (index (to_nat (raws ! j)))"
          show ?thesis
          proof (cases
              "all_queries_consistent
                (ro_actual_query_zero_round_trace_table data prefix_state)
                (ro_actual_query_composition_candidate data query_start)
                (staged_alphas data)")
            case True
            have event:
                "ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent
                  out"
              using trace_low_concrete composition_low True
              unfolding out_eq full_eq
                ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent_def
              by simp
            then show ?thesis by blast
          next
            case False
            have raws_rounds: "length raws = rounds"
            proof -
              from
                ro_absorb_checked_staged_zero_round_actual_query_boundary_syncE[
                  OF zero wf controlled builder_out verifier_out final_clean]
              show ?thesis by blast
            qed
            have mapped_subset:
                "set (map (\<lambda>raw. index (to_nat raw)) raws) \<subseteq>
                  ro_actual_query_zero_round_trace_composition_accepted_indices
                    data prefix_state query_start"
            proof
              fix idx
              assume idx_in:
                "idx \<in> set (map (\<lambda>raw. index (to_nat raw)) raws)"
              then obtain raw where
                raw_in: "raw \<in> set raws"
                and idx_raw: "idx = index (to_nat raw)"
                by auto
              from raw_in obtain j where
                j_bound: "j < length raws"
                and raw_eq: "raws ! j = raw"
                unfolding in_set_conv_nth by blast
              have idx_eq: "idx = index (to_nat (raws ! j))"
                using idx_raw raw_eq by simp
              have consistent:
                  "query_consistent_at
                    (ro_actual_query_zero_round_trace_table data prefix_state)
                    (ro_actual_query_composition_candidate data query_start)
                    (staged_alphas data) idx"
                using sampled_consistent[rule_format, OF j_bound] idx_eq
                by simp
              have sample: "idx \<in> query_sample_space"
                using idx_eq index_less_query_sample_space
                unfolding query_sample_space_def by simp
              show
                  "idx \<in>
                    ro_actual_query_zero_round_trace_composition_accepted_indices
                      data prefix_state query_start"
                using sample consistent
                unfolding
                  ro_actual_query_zero_round_trace_composition_accepted_indices_def
                  query_agreement_indices_def
                by simp
            qed
            have sampled_member:
                "map (\<lambda>raw. index (to_nat raw)) raws \<in>
                  ro_actual_query_zero_round_trace_composition_accepted_query_lists
                    data prefix_state query_start"
              using raws_rounds mapped_subset
              unfolding
                ro_actual_query_zero_round_trace_composition_accepted_query_lists_def
                query_index_lists_over_def
              by simp
            have good_member:
                "map (\<lambda>raw. index (to_nat raw)) raws \<in>
                  ro_actual_query_zero_round_trace_composition_good_query_lists
                    data prefix_state query_start"
              unfolding
                ro_actual_query_zero_round_trace_composition_good_query_lists_def
              using trace_low_concrete composition_low False sampled_member
              by simp
            have trace_table_head_eq:
                "ro_actual_query_zero_round_trace_table
                    (ro_query_head_data data) prefix_state =
                  ro_actual_query_zero_round_trace_table data prefix_state"
              unfolding ro_actual_query_zero_round_trace_table_def
                ro_query_head_data_def
              by simp
            have candidate_head_eq:
                "ro_actual_query_composition_candidate
                    (ro_query_head_data data) query_start =
                  ro_actual_query_composition_candidate data query_start"
              unfolding ro_actual_query_composition_candidate_def
                ro_query_head_data_def
              by simp
            have alphas_head_eq:
                "staged_alphas (ro_query_head_data data) = staged_alphas data"
              unfolding ro_query_head_data_def by simp
            have accepted_lists_head_eq:
                "ro_actual_query_zero_round_trace_composition_accepted_query_lists
                    (ro_query_head_data data) prefix_state query_start =
                  ro_actual_query_zero_round_trace_composition_accepted_query_lists
                    data prefix_state query_start"
              unfolding
                ro_actual_query_zero_round_trace_composition_accepted_query_lists_def
                ro_actual_query_zero_round_trace_composition_accepted_indices_def
              by (simp only: trace_table_head_eq candidate_head_eq alphas_head_eq)
            have good_eq:
                "ro_actual_query_zero_round_trace_composition_good_query_lists_for
                    prefix prefix_state (ro_query_head_data data) query_start =
                  ro_actual_query_zero_round_trace_composition_good_query_lists
                    data prefix_state query_start"
              unfolding
                ro_actual_query_zero_round_trace_composition_good_query_lists_for_def
                ro_actual_query_zero_round_trace_composition_good_query_lists_def
              by (simp only: trace_table_head_eq candidate_head_eq alphas_head_eq
                  accepted_lists_head_eq)
            have event:
                "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
                  ro_actual_query_zero_round_trace_composition_good_query_lists_for
                  out"
              using good_member good_eq
              unfolding out_eq full_eq
                ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
                ro_query_head_dependent_actual_query_index_list_hit_def
              by simp
            then show ?thesis by blast
          qed
        next
          assume targets:
              "hash_map_new_output_hit
                 (ro_zero_round_first_root_prefix_merkle_targets
                   prefix prefix_state)
                 prefix_state final_state \<or>
               hash_map_new_output_hit
                 (ro_actual_query_composition_prefix_targets data query_start)
                 query_start final_state"
          then show ?thesis
          proof
            assume trace_target:
                "hash_map_new_output_hit
                  (ro_zero_round_first_root_prefix_merkle_targets
                    prefix prefix_state)
                  prefix_state final_state"
            have event:
                "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit
                  out"
              using trace_target
              unfolding out_eq full_eq
                ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit_def
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
          have trace_low_conceptual:
              "trace_table_low_degree
                (conceptual_table prefix_state (staged_trace_root data)
                  (scale * clength))"
            using trace_low_concrete
            unfolding ro_actual_query_zero_round_trace_table_def
            .
          have split:
              "hash_map_new_output_hit
                  (ro_zero_round_first_root_prefix_merkle_targets
                    prefix prefix_state)
                  prefix_state final_state \<or>
               hash_map_new_output_hit
                  (ro_actual_query_composition_prefix_targets data query_start)
                  query_start final_state \<or>
               hash_state_relation_transition
                  (conditioned_fri_relation_bounded
                    (ro_checked_staged_transcript_hash_query_budget_for budgets)
                    composition_padding_absorbed_query_relation)
                  (HashMap adversary_initial_state) (HashMap attacker_state)"
            by (rule
              checked_builder_zero_round_composition_padding_bad_imp_transition_or_targets[
                OF wf controlled zero builder_out verifier_out final_clean
                  no_initial trace_low_conceptual padded_low composition_bad])
          then show ?thesis
          proof
            assume trace_target:
                "hash_map_new_output_hit
                  (ro_zero_round_first_root_prefix_merkle_targets
                    prefix prefix_state)
                  prefix_state final_state"
            have event:
                "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit
                  out"
              using trace_target
              unfolding out_eq full_eq
                ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit_def
              by simp
            then show ?thesis by blast
          next
            assume rest:
                "hash_map_new_output_hit
                    (ro_actual_query_composition_prefix_targets data query_start)
                    query_start final_state \<or>
                 hash_state_relation_transition
                    (conditioned_fri_relation_bounded
                      (ro_checked_staged_transcript_hash_query_budget_for budgets)
                      composition_padding_absorbed_query_relation)
                    (HashMap adversary_initial_state) (HashMap attacker_state)"
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
              assume transition:
                  "hash_state_relation_transition
                    (conditioned_fri_relation_bounded
                      (ro_checked_staged_transcript_hash_query_budget_for budgets)
                      composition_padding_absorbed_query_relation)
                    (HashMap adversary_initial_state) (HashMap attacker_state)"
              have event:
                  "ro_absorb_checked_staged_security_builder_relation_transition
                    (conditioned_fri_relation_bounded
                      (ro_checked_staged_transcript_hash_query_budget_for budgets)
                      composition_padding_absorbed_query_relation)
                    out"
                using transition
                unfolding out_eq full_eq
                  ro_absorb_checked_staged_security_builder_relation_transition_def
                  ro_absorb_checked_staged_security_builder_head_event_def
                  hash_state_relation_transition_event_def
                by simp
              then show ?thesis by blast
            qed
          qed
        next
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
               hash_state_relation_transition
                  (conditioned_fri_relation_bounded
                    (ro_checked_staged_transcript_hash_query_budget_for budgets)
                    ro_conditioned_augmented_absorbed_query_relation)
                  (HashMap adversary_initial_state) (HashMap attacker_state)"
            by (rule
              checked_builder_zero_round_composition_padded_candidate_bad_imp_conditioned_transitions_or_targets[
                OF wf controlled zero builder_out verifier_out final_clean
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
                 hash_state_relation_transition
                    (conditioned_fri_relation_bounded
                      (ro_checked_staged_transcript_hash_query_budget_for budgets)
                      ro_conditioned_augmented_absorbed_query_relation)
                    (HashMap adversary_initial_state) (HashMap attacker_state)"
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
                   hash_state_relation_transition
                      (conditioned_fri_relation_bounded
                        (ro_checked_staged_transcript_hash_query_budget_for budgets)
                        ro_conditioned_augmented_absorbed_query_relation)
                      (HashMap adversary_initial_state) (HashMap attacker_state)"
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
                assume transition:
                    "hash_state_relation_transition
                      (conditioned_fri_relation_bounded
                        (ro_checked_staged_transcript_hash_query_budget_for budgets)
                        ro_conditioned_augmented_absorbed_query_relation)
                      (HashMap adversary_initial_state) (HashMap attacker_state)"
                have event:
                    "ro_absorb_checked_staged_security_builder_relation_transition
                      (conditioned_fri_relation_bounded
                        (ro_checked_staged_transcript_hash_query_budget_for budgets)
                        ro_conditioned_augmented_absorbed_query_relation)
                      out"
                  using transition
                  unfolding out_eq full_eq
                    ro_absorb_checked_staged_security_builder_relation_transition_def
                    ro_absorb_checked_staged_security_builder_head_event_def
                    hash_state_relation_transition_event_def
                  by simp
                then show ?thesis by blast
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

end
end
