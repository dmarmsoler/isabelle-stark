theory Soundness_FRI_First_Root_RO_Actual_Query_Route
  imports
    Soundness_FRI_First_Root_RO_Actual_Query_Classification
    Soundness_FRI_First_Root_RO_Security_Query_Bound
    Staged_Security_Experiment_RO_Verifier_Budgets
begin


context soundness
begin

definition
  ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
where
  "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        hash_map_new_output_hit
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
          prefix_state final_state)"

definition
  ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree
where
  "ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        \<not> trace_table_low_degree
          (first_trace_fri_root_prefix_trace_table prefix prefix_state))"

definition
  ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
where
  "ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        \<not> trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state))"

definition
  ro_absorb_checked_staged_security_with_first_root_tables_equal
where
  "ro_absorb_checked_staged_security_with_first_root_tables_equal out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        first_trace_fri_root_prefix_trace_table prefix prefix_state =
          first_trace_fri_root_prefix_first_table prefix prefix_state)"

lemma
  ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_outcomeE:
  assumes outcome:
    "Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A)
          initial_state)"
  obtains
    "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute ro_verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
  using outcome
  unfolding
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
  by (auto elim!: set_dist_bindE intro: that)

lemma
  ro_absorb_checked_staged_security_with_first_root_clean_outcome_classification:
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
      ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
        out \<or>
      ro_absorb_checked_staged_security_with_first_root_tables_equal out"
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
  have support':
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
      OF support']
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
  have classified:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          first_trace_fri_root_prefix_good_agreement_query_lists
            prefix prefix_state \<or>
        hash_map_new_output_hit
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
          prefix_state final_state \<or>
        \<not> trace_table_low_degree
            (first_trace_fri_root_prefix_trace_table prefix prefix_state) \<or>
        \<not> trace_table_low_degree
            (first_trace_fri_root_prefix_first_table prefix prefix_state) \<or>
        first_trace_fri_root_prefix_trace_table prefix prefix_state =
          first_trace_fri_root_prefix_first_table prefix prefix_state"
    by (rule
        ro_absorb_checked_staged_first_root_actual_query_classification[
          OF wf controlled nonempty builder_out verifier_out final_clean])
  show ?thesis
    using classified
    unfolding out_eq full_eq
      ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit_def
      ro_checked_staged_first_root_dependent_actual_query_index_list_hit_def
      ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def
      ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree_def
      ro_absorb_checked_staged_security_with_first_root_first_not_low_degree_def
      ro_absorb_checked_staged_security_with_first_root_tables_equal_def
    by simp
qed

lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_le_classified_union:
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
          ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
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
       ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
          out \<or>
       ro_absorb_checked_staged_security_with_first_root_tables_equal out"
  proof (cases "final_hash_collision_event out")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis
      using
        ro_absorb_checked_staged_security_with_first_root_clean_outcome_classification[
          OF wf controlled nonempty accepted_out support False]
      by simp
  qed
qed

definition
  ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program
where
  "ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program
      A prefix_with_state =
    do {
      (prefix_with_state, data, query_start, raws, query_states) \<leftarrow>
        ro_checked_staged_after_first_root_with_query_witnesses_program
          A prefix_with_state;
      attacker_state \<leftarrow>
        ro_checked_verifier_state_transfer_with_saved
          (staged_proof_transcript data);
      result \<leftarrow> ro_verify_monad;
      return
        (((prefix_with_state, data, query_start, raws, query_states),
            attacker_state), result)
    }"

lemma
  ro_absorb_checked_staged_security_with_first_root_prefix_decomposition:
  "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      A =
    ro_staged_first_trace_fri_root_prefix_program A \<bind>
      ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program
        A"
  unfolding
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
    ro_checked_staged_transcript_program_with_first_root_prefix_decomposition
    ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program_def
    ro_checked_verifier_state_transfer_with_saved_def
  by (simp add: sm_bind_assoc split_def)

lemma
  hash_target_program_ro_absorb_checked_staged_after_first_root_with_query_witnesses_security:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (ro_checked_staged_after_first_root_with_query_hash_query_budget_for
          budgets +
        ro_verifier_hash_query_budget)
      (ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program
        A prefix_with_state)"
proof -
  let ?builder =
    "ro_checked_staged_after_first_root_with_query_hash_query_budget_for
      budgets"
  have builder:
      "hash_target_program B ?builder
        (ro_checked_staged_after_first_root_with_query_witnesses_program
          A prefix_with_state)"
    by (rule
        hash_target_program_ro_checked_staged_after_first_root_with_query_witnesses[
          OF nonempty wf controlled])
  have continuation:
      "\<And>saved_prefix data query_start raws query_states.
        hash_target_program B (0 + (ro_verifier_hash_query_budget + 0))
          (ro_checked_verifier_state_transfer_with_saved
              (staged_proof_transcript data) \<bind>
            (\<lambda>attacker_state.
              ro_verify_monad \<bind>
                (\<lambda>result.
                  return
                    (((saved_prefix, data, query_start, raws, query_states),
                        attacker_state), result))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_checked_verifier_state_transfer_with_saved,
       rule hash_target_program_bind,
       rule hash_target_program_ro_verify_monad,
       rule hash_target_program_return)

  have whole:
      "hash_target_program B
        (?builder + (0 + (ro_verifier_hash_query_budget + 0)))
        (ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program
          A prefix_with_state)"
    unfolding
      ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program_def
    apply (rule hash_target_program_bind[OF builder])
    apply (auto split: prod.splits)
    apply (rule continuation[simplified])
    done
  show ?thesis
    using whole by simp
qed



definition
  ro_absorb_checked_staged_first_root_prefix_merkle_target_error
    :: "staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets =
    nnreal
      ((ro_checked_staged_after_first_root_with_query_hash_query_budget_for
          budgets +
        ro_verifier_hash_query_budget) *
        (2 + 2 * (staged_trace_fri_search_queries budgets 0 + 2))) /
      nnreal size"


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_bound:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
      adversary_initial_state
    \<le> ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets"
proof -
  let ?M = "ro_staged_first_trace_fri_root_prefix_program A"
  let ?K =
    "ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program
      A"
  let ?E =
    "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit"
  let ?n =
    "ro_checked_staged_after_first_root_with_query_hash_query_budget_for
        budgets +
      ro_verifier_hash_query_budget"
  have decomposition:
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A = ?M \<bind> ?K"
    by (rule
      ro_absorb_checked_staged_security_with_first_root_prefix_decomposition)
  show ?thesis
    unfolding decomposition
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_by_target_budget[
        where
          B="\<lambda>prefix_with_state t.
            first_trace_fri_root_prefix_merkle_targets
              (fst prefix_with_state) (snd prefix_with_state)" and
          n="?n" and
          C="ro_absorb_checked_staged_first_root_prefix_merkle_target_error
            budgets"])
    show "\<not> ?E None"
      unfolding
        ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def
      by simp
  next
    fix prefix_with_state t out
    assume head:
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
      and out_support: "out \<in> set_dist (execute (?K prefix_with_state) t)"
      and event: "?E out"
    obtain prefix prefix_state where prefix_with_state_eq:
      "prefix_with_state = (prefix, prefix_state)"
      by (cases prefix_with_state) simp
    have state_eq: "t = prefix_state"
      using head
      unfolding prefix_with_state_eq
        ro_staged_first_trace_fri_root_prefix_program_def
      using nonempty
      by (auto elim!: set_dist_bindE split: nat.splits)
    show
      "hash_new_output_hit_event
        (first_trace_fri_root_prefix_merkle_targets
          (fst prefix_with_state) (snd prefix_with_state))
        t out"
      using event out_support state_eq
      unfolding prefix_with_state_eq
        ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def
        hash_new_output_hit_event_def
        ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program_def
        ro_checked_staged_after_first_root_with_query_witnesses_program_def
      by (cases out)
        (auto elim!: set_dist_bindE split: prod.splits)
  next
    fix prefix_with_state t
    assume head:
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
    show
      "hash_target_budget
        (first_trace_fri_root_prefix_merkle_targets
          (fst prefix_with_state) (snd prefix_with_state))
        ?n (?K prefix_with_state)"
      by (rule hash_target_program_budget)
        (rule
          hash_target_program_ro_absorb_checked_staged_after_first_root_with_query_witnesses_security[
            OF nonempty wf controlled])
  next
    fix prefix_with_state t
    assume head:
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
    obtain prefix prefix_state where prefix_with_state_eq:
      "prefix_with_state = (prefix, prefix_state)"
      by (cases prefix_with_state) simp
    have card_bound:
      "card
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        \<le> 2 + 2 * (staged_trace_fri_search_queries budgets 0 + 2)"
      by (rule
        ro_staged_first_trace_fri_root_prefix_target_card_bound[
          OF nonempty wf controlled])
        (use head prefix_with_state_eq in simp)
    have numerator_bound:
      "?n * card
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        \<le> ?n *
          (2 + 2 * (staged_trace_fri_search_queries budgets 0 + 2))"
      by (rule mult_left_mono[OF card_bound]) simp
    show
      "hash_target_budget_value
          (first_trace_fri_root_prefix_merkle_targets
            (fst prefix_with_state) (snd prefix_with_state))
          ?n
        \<le> ro_absorb_checked_staged_first_root_prefix_merkle_target_error
            budgets"
      unfolding prefix_with_state_eq hash_target_budget_value_def
        ro_absorb_checked_staged_first_root_prefix_merkle_target_error_def
      apply (simp only: fst_conv snd_conv)
      apply (rule nnreal_nat_divide_right_mono)
      apply (rule numerator_bound)
      done
  qed
qed


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_final_hash_collision_eq:
  assumes nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        final_hash_collision_event s =
      wp_event
        (ro_absorb_checked_staged_security_experiment A)
        final_hash_collision_event s"
proof -
  let ?project_first =
    "\<lambda>(((prefix_with_state, data, query_start, raws, query_states),
          attacker_state), result).
      (((data, query_start, raws, query_states), attacker_state), result)"
  let ?project_witnesses =
    "\<lambda>(((data, query_start, raws, query_states), attacker_state), result).
      ((data, attacker_state), result)"
  have first_event_map:
    "(\<lambda>out. case out of
        None \<Rightarrow> final_hash_collision_event None
      | Some (x, t) \<Rightarrow>
          final_hash_collision_event (Some (?project_first x, t))) =
      final_hash_collision_event"
    unfolding final_hash_collision_event_def
    by (rule ext) (auto split: option.splits prod.splits)
  have first_mapped:
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A \<bind>
          (\<lambda>x. return (?project_first x)))
        final_hash_collision_event s =
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        final_hash_collision_event s"
    by (subst wp_event_bind_return_map) (simp only: first_event_map)
  have first_projection:
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A \<bind>
        (\<lambda>x. return (?project_first x)) =
      ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
    using
      ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection[
        OF nonempty, of A]
    by (simp add: split_def)
  have first_eq:
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        final_hash_collision_event s =
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
        final_hash_collision_event s"
    using first_mapped
    unfolding first_projection
    by simp

  have witnesses_event_map:
    "(\<lambda>out. case out of
        None \<Rightarrow> final_hash_collision_event None
      | Some (x, t) \<Rightarrow>
          final_hash_collision_event (Some (?project_witnesses x, t))) =
      final_hash_collision_event"
    unfolding final_hash_collision_event_def
    by (rule ext) (auto split: option.splits prod.splits)
  have witnesses_mapped:
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_query_witnesses A \<bind>
          (\<lambda>x. return (?project_witnesses x)))
        final_hash_collision_event s =
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
        final_hash_collision_event s"
    by (subst wp_event_bind_return_map) (simp only: witnesses_event_map)
  have witnesses_projection:
    "ro_absorb_checked_staged_security_experiment_with_query_witnesses A \<bind>
        (\<lambda>x. return (?project_witnesses x)) =
      ro_absorb_checked_staged_security_experiment_with_data_state A"
    using
      ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection[
        of A]
    by (simp add: split_def)
  have witnesses_eq:
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
        final_hash_collision_event s =
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_data_state A)
        final_hash_collision_event s"
    using witnesses_mapped
    unfolding witnesses_projection
    by simp

  have data_state_event_map:
    "(\<lambda>out. case out of
        None \<Rightarrow> final_hash_collision_event None
      | Some (x, t) \<Rightarrow>
          final_hash_collision_event (Some (snd x, t))) =
      final_hash_collision_event"
    unfolding final_hash_collision_event_def
    by (rule ext) (auto split: option.splits prod.splits)
  have data_state_mapped:
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_data_state A \<bind>
          (\<lambda>x. return (snd x)))
        final_hash_collision_event s =
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_data_state A)
        final_hash_collision_event s"
    by (subst wp_event_bind_return_map) (simp only: data_state_event_map)
  have data_state_eq:
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_data_state A)
        final_hash_collision_event s =
      wp_event
        (ro_absorb_checked_staged_security_experiment A)
        final_hash_collision_event s"
    using data_state_mapped
    unfolding
      ro_absorb_checked_staged_security_experiment_with_data_state_projection
    by simp
  show ?thesis
    using first_eq witnesses_eq data_state_eq by simp
qed


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_final_hash_collision_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        final_hash_collision_event adversary_initial_state
      \<le> hash_collision_budget_value 0
          (ro_absorb_checked_staged_security_hash_query_budget_for budgets)"
proof -
  have event_eq:
    "(final_hash_collision_event ::
        (unit list \<times> 'f protocol_channel) option \<Rightarrow> bool) =
      hash_map_output_collision_bad adversary_initial_state"
    unfolding final_hash_collision_event_def
      hash_map_output_collision_bad_def accepted_def
    by (rule ext) (auto split: option.splits prod.splits)
  have
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        final_hash_collision_event adversary_initial_state =
      wp_event
        (ro_absorb_checked_staged_security_experiment A)
        final_hash_collision_event adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_final_hash_collision_eq[
        OF nonempty])
  also have "... =
      wp_event
        (ro_absorb_checked_staged_security_experiment A)
        (hash_map_output_collision_bad adversary_initial_state)
        adversary_initial_state"
    by (simp only: event_eq)
  also have "... \<le>
      hash_collision_budget_value 0
        (ro_absorb_checked_staged_security_hash_query_budget_for budgets)"
    by (rule
      ro_absorb_checked_staged_security_experiment_hash_map_output_collision_bad_bound_controlled[
        OF wf controlled])
  finally show ?thesis .
qed


definition
  active_route_ro_absorb_first_root_trace_not_low_degree_error_for
    :: "'f staged_adversary \<Rightarrow> prob"
where
  "active_route_ro_absorb_first_root_trace_not_low_degree_error_for A =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree
      adversary_initial_state"

definition
  active_route_ro_absorb_first_root_first_not_low_degree_error_for
    :: "'f staged_adversary \<Rightarrow> prob"
where
  "active_route_ro_absorb_first_root_first_not_low_degree_error_for A =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
      adversary_initial_state"

definition
  active_route_ro_absorb_first_root_tables_equal_error_for
    :: "'f staged_adversary \<Rightarrow> prob"
where
  "active_route_ro_absorb_first_root_tables_equal_error_for A =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_with_first_root_tables_equal
      adversary_initial_state"

definition
  active_route_ro_absorb_first_root_classified_bound_for
    :: "staged_budgets \<Rightarrow> 'f staged_adversary \<Rightarrow> prob"
where
  "active_route_ro_absorb_first_root_classified_bound_for budgets A =
    hash_collision_budget_value 0
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
    ro_checked_staged_first_root_good_actual_query_error budgets +
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
    active_route_ro_absorb_first_root_trace_not_low_degree_error_for A +
    active_route_ro_absorb_first_root_first_not_low_degree_error_for A +
    active_route_ro_absorb_first_root_tables_equal_error_for A"


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_classified_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> active_route_ro_absorb_first_root_classified_bound_for budgets A"
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
  let ?First =
    "ro_absorb_checked_staged_security_with_first_root_first_not_low_degree"
  let ?Equal =
    "ro_absorb_checked_staged_security_with_first_root_tables_equal"
  have classified:
    "wp_event ?M accepted adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out.
          ?Collision out \<or> ?Query out \<or> ?Target out \<or> ?Trace out \<or>
          ?First out \<or> ?Equal out)
        adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_acceptance_le_classified_union[
        OF wf controlled nonempty])
  have union:
    "wp_event ?M
        (\<lambda>out.
          ?Collision out \<or> ?Query out \<or> ?Target out \<or> ?Trace out \<or>
          ?First out \<or> ?Equal out)
        adversary_initial_state
      \<le>
      wp_event ?M ?Collision adversary_initial_state +
      wp_event ?M ?Query adversary_initial_state +
      wp_event ?M ?Target adversary_initial_state +
      wp_event ?M ?Trace adversary_initial_state +
      wp_event ?M ?First adversary_initial_state +
      wp_event ?M ?Equal adversary_initial_state"
  proof -
    have
      "wp_event ?M
          (\<lambda>out.
            ?Collision out \<or> ?Query out \<or> ?Target out \<or> ?Trace out \<or>
            ?First out \<or> ?Equal out)
          adversary_initial_state
        \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M
          (\<lambda>out.
            ?Query out \<or> ?Target out \<or> ?Trace out \<or> ?First out \<or> ?Equal out)
          adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         wp_event ?M
           (\<lambda>out. ?Target out \<or> ?Trace out \<or> ?First out \<or> ?Equal out)
           adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         (wp_event ?M ?Target adversary_initial_state +
          wp_event ?M (\<lambda>out. ?Trace out \<or> ?First out \<or> ?Equal out)
            adversary_initial_state))"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         (wp_event ?M ?Target adversary_initial_state +
          (wp_event ?M ?Trace adversary_initial_state +
           wp_event ?M (\<lambda>out. ?First out \<or> ?Equal out)
             adversary_initial_state)))"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         (wp_event ?M ?Target adversary_initial_state +
          (wp_event ?M ?Trace adversary_initial_state +
           (wp_event ?M ?First adversary_initial_state +
            wp_event ?M ?Equal adversary_initial_state))))"
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
       wp_event ?M ?First adversary_initial_state +
       wp_event ?M ?Equal adversary_initial_state
     \<le>
     hash_collision_budget_value 0
       (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
     ro_checked_staged_first_root_good_actual_query_error budgets +
     ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
       wp_event ?M ?Trace adversary_initial_state +
       wp_event ?M ?First adversary_initial_state +
       wp_event ?M ?Equal adversary_initial_state"
    by (intro add_mono collision query target order_refl)
  show ?thesis
    unfolding active_route_ro_absorb_first_root_classified_bound_for_def
      active_route_ro_absorb_first_root_trace_not_low_degree_error_for_def
      active_route_ro_absorb_first_root_first_not_low_degree_error_for_def
      active_route_ro_absorb_first_root_tables_equal_error_for_def
    by (rule order_trans[OF classified order_trans[OF union closed]])
qed
end
end