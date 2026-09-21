theory Soundness_FRI_Conditioned_Security_Target_Bound
  imports
    Soundness_FRI_Conditioned_Security_Bridge
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Prequery_Closed_Bound
begin

context soundness
begin

lemma hash_target_program_ro_verify_monad_with_fri_prefixes:
  "hash_target_program B ro_verifier_hash_query_budget
    ro_verify_monad_with_fri_prefixes"
proof (rule hash_target_program_of_projection[
    where n=ro_verify_monad and project=snd])
  show "ro_verify_monad_with_fri_prefixes \<bind>
      (\<lambda>x. return (snd x)) = ro_verify_monad"
    by (rule ro_verify_monad_with_fri_prefixes_projection)
  show "hash_target_program B ro_verifier_hash_query_budget ro_verify_monad"
    by (rule hash_target_program_ro_verify_monad)
qed

definition
  ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit
where
  "ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit
      out \<longleftrightarrow>
    \<not> final_hash_collision_event out \<and>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((((prefix, prefix_state), data, query_start, raws, query_states),
             attacker_state), fri_prefixes), result), final_state) \<Rightarrow>
        fri_checked_builder_merkle_target_hit
          data attacker_state final_state)"

definition ro_absorb_checked_staged_fri_builder_merkle_target_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_fri_builder_merkle_target_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in nnreal
          (ro_verifier_hash_query_budget *
            (ceil_log clength + ceil_log (maxDegree + 1) + 2 * q)) /
        nnreal size)"

lemma hash_target_program_ro_absorb_conditioned_verifier_tail:
  "hash_target_program B ro_verifier_hash_query_budget
    (ro_checked_verifier_state_transfer_with_saved
        (staged_proof_transcript data) \<bind>
      (\<lambda>attacker_state.
        ro_verify_monad_with_fri_prefixes \<bind>
          (\<lambda>verifier_result.
            return
              ((((prefix_with_state, data, query_start, raws, query_states),
                  attacker_state), fst verifier_result),
                snd verifier_result))))"
proof -
  have whole:
      "hash_target_program B
        (0 + (ro_verifier_hash_query_budget + 0))
        (ro_checked_verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>attacker_state.
            ro_verify_monad_with_fri_prefixes \<bind>
              (\<lambda>verifier_result.
                return
                  ((((prefix_with_state, data, query_start, raws, query_states),
                      attacker_state), fst verifier_result),
                    snd verifier_result))))"
    by (rule hash_target_program_bind,
        rule hash_target_program_ro_checked_verifier_state_transfer_with_saved,
        rule hash_target_program_bind,
        rule hash_target_program_ro_verify_monad_with_fri_prefixes,
        rule hash_target_program_return)
  show ?thesis
    using whole by simp
qed

lemma fri_checked_builder_merkle_targets_card_bound:
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
    and clean: "\<not> hash_map_output_collision attacker_state"
  shows
    "card (fri_checked_builder_merkle_targets data attacker_state) \<le>
      ceil_log clength + ceil_log (maxDegree + 1) +
        2 * ro_checked_staged_transcript_hash_query_budget_for budgets"
proof -
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       ceil_log (to_nat (staged_degree data) + 1) \<le>
         ceil_log (maxDegree + 1)"
    using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
    by blast
  have roots_card:
      "card
          (set (staged_trace_fri_roots data) \<union>
            set (staged_composition_fri_roots data)) \<le>
        ceil_log clength + ceil_log (maxDegree + 1)"
  proof -
    have "card
        (set (staged_trace_fri_roots data) \<union>
          set (staged_composition_fri_roots data)) \<le>
        card (set (staged_trace_fri_roots data)) +
          card (set (staged_composition_fri_roots data))"
      by (rule card_Un_le)
    also have "... \<le>
        length (staged_trace_fri_roots data) +
          length (staged_composition_fri_roots data)"
      by (rule add_mono; rule card_length)
    also have "... \<le>
        ceil_log clength + ceil_log (maxDegree + 1)"
      using shape by simp
    finally show ?thesis .
  qed
  have map_card:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds[
        OF wf controlled outcome clean])
  have target_card:
      "card (fri_checked_builder_merkle_targets data attacker_state) \<le>
        card
          (set (staged_trace_fri_roots data) \<union>
            set (staged_composition_fri_roots data)) +
          2 * card (fmdom' (HashMap attacker_state))"
    unfolding fri_checked_builder_merkle_targets_def
    by (rule card_merkle_prefix_path_targets_le) simp
  show ?thesis
    using target_card roots_card map_card by linarith
qed

lemma
  wp_ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit
      adversary_initial_state
    \<le> ro_absorb_checked_staged_fri_builder_merkle_target_error budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?K =
    "\<lambda>(prefix_with_state, data, query_start, raws, query_states).
      ro_checked_verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>attacker_state.
          ro_verify_monad_with_fri_prefixes \<bind>
            (\<lambda>verifier_result.
              return
                ((((prefix_with_state, data, query_start, raws, query_states),
                    attacker_state), fst verifier_result),
                  snd verifier_result)))"
  let ?E =
    "ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit"
  let ?B =
    "\<lambda>(prefix_with_state, data, query_start, raws, query_states) t.
      fri_checked_builder_merkle_targets data t"
  let ?n = "ro_verifier_hash_query_budget"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have decomposition:
      "ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses
          A = ?M \<bind> ?K"
    unfolding
      ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses_def
      ro_checked_verifier_state_transfer_with_saved_def
    by (simp add: sm_bind_assoc split_def)
  show ?thesis
    unfolding decomposition
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_conditional[
        where B="?B" and n="?n" and
          C="ro_absorb_checked_staged_fri_builder_merkle_target_error budgets"])
    show "\<not> ?E None"
      unfolding
        ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit_def
        final_hash_collision_event_def
      by simp
  next
    fix x t out
    assume head:
        "Some (x, t) \<in>
          set_dist (execute ?M adversary_initial_state)"
      and tail_support: "out \<in> set_dist (execute (?K x) t)"
      and event: "?E out"
    obtain prefix prefix_state data query_start raws query_states where x_eq:
        "x = ((prefix, prefix_state), data, query_start, raws, query_states)"
      by (cases x) (auto split: prod.splits)
    show "hash_new_output_hit_event (?B x t) t out"
      using event tail_support
      unfolding x_eq
        ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit_def
        fri_checked_builder_merkle_target_hit_def
        hash_new_output_hit_event_def
        ro_checked_verifier_state_transfer_with_saved_def
      by (cases out)
        (auto elim!: set_dist_bindE split: prod.splits)
  next
    fix x t
    assume head:
      "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
    obtain prefix prefix_state data query_start raws query_states where x_eq:
        "x = ((prefix, prefix_state), data, query_start, raws, query_states)"
      by (cases x) (auto split: prod.splits)
    show "hash_target_budget (?B x t) ?n (?K x)"
      unfolding x_eq
      apply (simp only: prod.case)
      apply (rule hash_target_program_budget)
      apply (rule hash_target_program_ro_absorb_conditioned_verifier_tail)
      done
  next
    fix x t
    assume head:
        "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
      and witness:
        "\<exists>out \<in> set_dist (execute (?K x) t). ?E out"
    obtain prefix prefix_state data query_start raws query_states where x_eq:
        "x = ((prefix, prefix_state), data, query_start, raws, query_states)"
      by (cases x) (auto split: prod.splits)
    from witness obtain out where
      tail_support: "out \<in> set_dist (execute (?K x) t)"
      and event: "?E out"
      by blast
    obtain fri_prefixes result final_state where out_eq:
        "out =
          Some (((((x, t), fri_prefixes), result), final_state))"
      using tail_support event
      unfolding x_eq ro_checked_verifier_state_transfer_with_saved_def
        ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit_def
      by (cases out)
        (auto elim!: set_dist_bindE split: prod.splits)
    have tail_program:
        "hash_target_program (?B x t) ?n (?K x)"
      unfolding x_eq
      apply (simp only: prod.case)
      apply (rule hash_target_program_ro_absorb_conditioned_verifier_tail)
      done
    have tail_extension: "hash_extension_preserving (?K x)"
      using tail_program unfolding hash_target_program_def by blast
    have t_final: "t \<le> final_state"
      using tail_extension tail_support
      unfolding out_eq hash_extension_preserving_def
      by blast
    have final_clean: "\<not> hash_map_output_collision final_state"
      using event
      unfolding out_eq
        ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit_def
        final_hash_collision_event_def
      by simp
    have clean: "\<not> hash_map_output_collision t"
    proof
      assume collision: "hash_map_output_collision t"
      have "hash_map_output_collision final_state"
        by (rule hash_map_output_collision_mono[OF collision t_final])
      then show False
        using final_clean by contradiction
    qed
    have head':
        "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
            t)) \<in>
          set_dist
            (execute
              (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
                A)
              adversary_initial_state)"
      using head unfolding x_eq .
    have card_bound:
        "card (fri_checked_builder_merkle_targets data t) \<le>
          ceil_log clength + ceil_log (maxDegree + 1) + 2 * ?q"
      by (rule fri_checked_builder_merkle_targets_card_bound[
        OF wf controlled head' clean])
    have numerator_bound:
        "?n * card (fri_checked_builder_merkle_targets data t) \<le>
          ?n * (ceil_log clength + ceil_log (maxDegree + 1) + 2 * ?q)"
      by (rule mult_left_mono[OF card_bound]) simp
    show
      "hash_target_budget_value (?B x t) ?n \<le>
        ro_absorb_checked_staged_fri_builder_merkle_target_error budgets"
      unfolding x_eq hash_target_budget_value_def
        ro_absorb_checked_staged_fri_builder_merkle_target_error_def
      apply (simp only: prod.case Let_def)
      apply (rule nnreal_nat_divide_right_mono)
      apply (rule numerator_bound)
      done
  qed
qed

definition
  ro_absorb_checked_staged_security_clean_builder_merkle_target_hit
where
  "ro_absorb_checked_staged_security_clean_builder_merkle_target_hit out \<longleftrightarrow>
    \<not> final_hash_collision_event out \<and>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
             attacker_state), result), final_state) \<Rightarrow>
        fri_checked_builder_merkle_target_hit
          data attacker_state final_state)"

lemma
  wp_ro_absorb_checked_staged_security_clean_builder_merkle_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_clean_builder_merkle_target_hit
      adversary_initial_state
    \<le> ro_absorb_checked_staged_fri_builder_merkle_target_error budgets"
proof -
  let ?project =
    "\<lambda>((base, fri_prefixes), result). (base, result)"
  have event_map:
      "(\<lambda>out. case out of
          None \<Rightarrow>
            ro_absorb_checked_staged_security_clean_builder_merkle_target_hit
              None
        | Some (x, t) \<Rightarrow>
            ro_absorb_checked_staged_security_clean_builder_merkle_target_hit
              (Some (?project x, t))) =
        ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit"
    unfolding
      ro_absorb_checked_staged_security_clean_builder_merkle_target_hit_def
      ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit_def
      final_hash_collision_event_def
    by (rule ext) (auto split: option.splits prod.splits)
  have mapped:
      "wp_event
        (ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses
            A \<bind>
          (\<lambda>x. return (?project x)))
        ro_absorb_checked_staged_security_clean_builder_merkle_target_hit
        adversary_initial_state =
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses
          A)
        ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit
        adversary_initial_state"
    by (subst wp_event_bind_return_map) (simp only: event_map)
  have projection:
      "ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses
          A \<bind>
        (\<lambda>x. return (?project x)) =
      ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A"
    using
      ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses_projection[
        of A]
    by (simp add: split_def)
  have annotated_bound:
      "wp_event
        (ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses
          A)
        ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit
        adversary_initial_state
      \<le> ro_absorb_checked_staged_fri_builder_merkle_target_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_with_fri_prefixes_clean_builder_merkle_target_hit_bound[
        OF wf controlled])
  show ?thesis
    using mapped annotated_bound
    unfolding projection
    by simp
qed

end

end
