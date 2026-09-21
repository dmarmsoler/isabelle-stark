theory Soundness_FRI_Conditioned_Explicit_Security_Events
  imports
    Stark.Soundness_FRI_Conditioned_Trace_Composition_Padding_Outcome_Bridge
begin

context soundness
begin

definition ro_absorb_checked_staged_security_builder_head_event
where
  "ro_absorb_checked_staged_security_builder_head_event P out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        P (Some
          ((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state))))"

definition ro_absorb_checked_staged_security_builder_initial_target_hit
where
  "ro_absorb_checked_staged_security_builder_initial_target_hit out \<longleftrightarrow>
    ro_absorb_checked_staged_security_builder_head_event
      (hash_new_output_hit_event {PState adversary_initial_state}
        adversary_initial_state)
      out"

definition ro_absorb_checked_staged_security_builder_relation_transition
where
  "ro_absorb_checked_staged_security_builder_relation_transition R out \<longleftrightarrow>
    ro_absorb_checked_staged_security_builder_head_event
      (hash_state_relation_transition_event R
        (HashMap adversary_initial_state))
      out"

lemma wp_ro_absorb_checked_staged_security_builder_head_event_le:
  "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_head_event P)
      s
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      P s"
  unfolding
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
proof (rule wp_event_bind_bound_by_head_event)
  show
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      P s \<le>
     wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      P s"
    by simp
next
  show
    "ro_absorb_checked_staged_security_builder_head_event P None \<Longrightarrow> P None"
    unfolding ro_absorb_checked_staged_security_builder_head_event_def
    by simp
next
  fix x t out
  assume head:
    "Some (x, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          s)"
  obtain prefix_with_state data query_start raws query_states where x_eq:
    "x = (prefix_with_state, data, query_start, raws, query_states)"
    by (cases x) auto
  assume tail:
    "out \<in>
      set_dist
        (execute
          (case x of
            (prefix_with_state, data, query_start, raws, query_states) \<Rightarrow>
              get \<bind>
              (\<lambda>attacker_state.
                put
                  (verifier_state_from_adversary attacker_state
                    (staged_proof_transcript data)) \<bind>
                (\<lambda>_. ro_verify_monad \<bind>
                  (\<lambda>result.
                    return
                      (((prefix_with_state, data, query_start, raws,
                          query_states), attacker_state), result)))))
          t)"
    and event:
      "ro_absorb_checked_staged_security_builder_head_event P out"
  show "P (Some (x, t))"
    using tail event
    unfolding x_eq ro_absorb_checked_staged_security_builder_head_event_def
    by (auto simp: wpsimps elim!: set_dist_bindE
        split: option.splits prod.splits)
qed

lemma wp_ro_absorb_checked_staged_security_builder_initial_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_builder_initial_target_hit
      adversary_initial_state
    \<le> nnreal q / nnreal size"
proof -
  have lift:
      "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        ro_absorb_checked_staged_security_builder_initial_target_hit
        adversary_initial_state
      \<le>
      wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state)
        adversary_initial_state"
    unfolding
      ro_absorb_checked_staged_security_builder_initial_target_hit_def
    by (rule wp_ro_absorb_checked_staged_security_builder_head_event_le)
  have head:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state)
        adversary_initial_state
      \<le> nnreal q / nnreal size"
    unfolding q_def
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_initial_target_bound_all_rounds[
        OF wf controlled])
  show ?thesis by (rule order_trans[OF lift head])
qed

lemma wp_ro_absorb_checked_staged_security_builder_relation_transition_le:
  "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition R)
      s
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (hash_state_relation_transition_event R
        (HashMap adversary_initial_state))
      s"
  unfolding
    ro_absorb_checked_staged_security_builder_relation_transition_def
  by (rule wp_ro_absorb_checked_staged_security_builder_head_event_le)

definition ro_checked_staged_conditioned_trace_challenge_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_trace_challenge_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in nnreal (q * (1 + (7 * q + 2))) / nnreal size)"

definition ro_checked_staged_conditioned_composition_challenge_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_composition_challenge_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in nnreal (q * (1 + (7 * q + 2))) / nnreal size)"

definition ro_checked_staged_conditioned_residual_query_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_residual_query_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in nnreal
       (q * (ro_conditioned_augmented_query_raw_relation_fiber_bound +
         (q * q + 7 * q + 2))) / nnreal size)"

definition ro_checked_staged_conditioned_composition_padding_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_composition_padding_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in nnreal
       (q * (trace_composition_padding_query_raw_fiber_bound +
         (5 * q + 2))) / nnreal size)"

definition ro_checked_staged_conditioned_trace_sampled_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_trace_sampled_error budgets =
    ro_checked_staged_conditioned_trace_challenge_error budgets +
    ro_checked_staged_conditioned_residual_query_error budgets"

definition ro_checked_staged_conditioned_composition_sampled_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_composition_sampled_error budgets =
    ro_checked_staged_conditioned_composition_challenge_error budgets +
    ro_checked_staged_conditioned_residual_query_error budgets +
    ro_checked_staged_conditioned_composition_padding_error budgets"

definition ro_checked_staged_conditioned_joint_sampled_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_joint_sampled_error budgets =
    ro_checked_staged_conditioned_trace_challenge_error budgets +
    ro_checked_staged_conditioned_composition_challenge_error budgets +
    ro_checked_staged_conditioned_residual_query_error budgets +
    ro_checked_staged_conditioned_composition_padding_error budgets"

lemma
  wp_ro_absorb_checked_staged_security_builder_trace_challenge_transition_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          conditioned_trace_fri_bad_challenge_relation))
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_trace_challenge_error budgets"
proof -
  have lift:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          conditioned_trace_fri_bad_challenge_relation))
      adversary_initial_state
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          conditioned_trace_fri_bad_challenge_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_relation_transition_le)
  have head:
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          conditioned_trace_fri_bad_challenge_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_trace_challenge_error budgets"
    unfolding ro_checked_staged_conditioned_trace_challenge_error_def Let_def
    by (rule
      wp_ro_checked_staged_transcript_with_query_witnesses_conditioned_trace_fri_relation[
        OF wf controlled])
  show ?thesis by (rule order_trans[OF lift head])
qed

lemma
  wp_ro_absorb_checked_staged_security_builder_composition_challenge_transition_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          conditioned_composition_fri_bad_challenge_relation))
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_composition_challenge_error budgets"
proof -
  have lift:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          conditioned_composition_fri_bad_challenge_relation))
      adversary_initial_state
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          conditioned_composition_fri_bad_challenge_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_relation_transition_le)
  have head:
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          conditioned_composition_fri_bad_challenge_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_composition_challenge_error budgets"
    unfolding ro_checked_staged_conditioned_composition_challenge_error_def Let_def
    by (rule
      wp_ro_checked_staged_transcript_with_query_witnesses_conditioned_composition_fri_relation[
        OF wf controlled])
  show ?thesis by (rule order_trans[OF lift head])
qed
lemma
  wp_ro_absorb_checked_staged_security_builder_residual_query_transition_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          ro_conditioned_augmented_absorbed_query_relation))
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_residual_query_error budgets"
proof -
  have lift:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          ro_conditioned_augmented_absorbed_query_relation))
      adversary_initial_state
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          ro_conditioned_augmented_absorbed_query_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_relation_transition_le)
  have head:
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          ro_conditioned_augmented_absorbed_query_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_residual_query_error budgets"
    unfolding ro_checked_staged_conditioned_residual_query_error_def Let_def
    by (rule
      wp_ro_checked_staged_transcript_with_query_witnesses_conditioned_augmented_query_relation[
        OF wf controlled])
  show ?thesis by (rule order_trans[OF lift head])
qed

lemma
  wp_ro_absorb_checked_staged_security_builder_composition_padding_transition_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          trace_composition_padding_absorbed_query_relation))
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_composition_padding_error budgets"
proof -
  have lift:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          trace_composition_padding_absorbed_query_relation))
      adversary_initial_state
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          trace_composition_padding_absorbed_query_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_relation_transition_le)
  have head:
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          trace_composition_padding_absorbed_query_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_composition_padding_error budgets"
    unfolding
      ro_checked_staged_conditioned_composition_padding_error_def Let_def
    by (rule
      wp_ro_checked_staged_transcript_with_query_witnesses_trace_composition_padding_relation[
        OF wf controlled])
  show ?thesis by (rule order_trans[OF lift head])
qed

end
end