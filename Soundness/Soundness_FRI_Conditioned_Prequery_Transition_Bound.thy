theory Soundness_FRI_Conditioned_Prequery_Transition_Bound
  imports
    Stark.Soundness_FRI_Conditioned_Prequery_Drift_Bound
    Stark.Soundness_FRI_Conditioned_Challenge_Relation
begin

context soundness
begin

lemma ro_conditioned_augmented_bounded_transition_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_transition
        (conditioned_fri_relation_bounded L
          ro_conditioned_augmented_absorbed_query_relation)
        M (fmupd x y M)}
      \<le> ro_conditioned_augmented_query_raw_relation_fiber_bound +
        (L * L + 7 * L + 2)"
proof (rule conditioned_fri_bounded_transition_fiber_card_bound[
    OF fresh])
  assume "card (fmdom' M) \<le> L"
  show
    "card {y.
      hash_state_relation_direct_activation
        ro_conditioned_augmented_absorbed_query_relation M x y}
      \<le> ro_conditioned_augmented_query_raw_relation_fiber_bound"
    by (rule
      ro_conditioned_augmented_absorbed_query_relation_direct_fiber_card_bound)
next
  assume domain: "card (fmdom' M) \<le> L"
  have
    "card {y.
      hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y}
      \<le> card (fmdom' M) * card (fmdom' M) +
        7 * card (fmdom' M) + 2"
    by (rule
      ro_conditioned_augmented_absorbed_query_relation_drift_fiber_card_bound[
        OF fresh])
  also have "... \<le> L * L + 7 * L + 2"
  proof -
    have square:
        "card (fmdom' M) * card (fmdom' M) \<le> L * L"
      by (rule mult_le_mono[OF domain domain])
    have linear: "7 * card (fmdom' M) \<le> 7 * L"
      by (rule mult_left_mono[OF domain], simp)
    show ?thesis
      by (rule add_le_mono[
        OF add_le_mono[OF square linear] order_refl])
  qed
  finally show
    "card {y.
      hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y}
      \<le> L * L + 7 * L + 2"
    .
qed

lemma
  wp_ro_checked_staged_transcript_with_query_witnesses_conditioned_augmented_query_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded q
          ro_conditioned_augmented_absorbed_query_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state
      \<le> nnreal
        (q *
          (ro_conditioned_augmented_query_raw_relation_fiber_bound +
            (q * q + 7 * q + 2))) /
        nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B =
    "ro_conditioned_augmented_query_raw_relation_fiber_bound +
      (?Q * ?Q + 7 * ?Q + 2)"
  have steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition
            (conditioned_fri_relation_bounded ?Q
              ro_conditioned_augmented_absorbed_query_relation)
            M (fmupd x y M)}
          \<le> ?B"
    by (rule ro_conditioned_augmented_bounded_transition_fiber_card_bound)
  have bound:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (conditioned_fri_relation_bounded ?Q
            ro_conditioned_augmented_absorbed_query_relation)
          (HashMap adversary_initial_state))
        adversary_initial_state
        \<le> nnreal (?Q * ?B) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound_all_rounds[
        OF wf controlled steps])
  show ?thesis
    using bound unfolding q_def by simp
qed

end
end
