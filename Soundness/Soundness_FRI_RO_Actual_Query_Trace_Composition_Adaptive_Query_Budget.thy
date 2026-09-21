theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Adaptive_Query_Budget
  imports
    Soundness_FRI_RO_Actual_Query_Trace_Composition_State_Relation
    Soundness_FRI_First_Root_RO_Adaptive_Query_Budget
begin

context soundness
begin

definition trace_composition_absorbed_query_relation_bounded
  :: "nat \<Rightarrow>
      (('f protocol_hash_input, 'f) fmap \<Rightarrow>
        'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "trace_composition_absorbed_query_relation_bounded L M x y \<longleftrightarrow>
    card (fmdom' M) \<le> L \<and>
    trace_composition_absorbed_query_relation M x y"


lemma trace_composition_bounded_direct_activation_subset:
  assumes fresh: "fmlookup M x = None"
  shows
    "{y.
      hash_state_relation_direct_activation
        (trace_composition_absorbed_query_relation_bounded L) M x y}
      \<subseteq>
    {y.
      hash_state_relation_direct_activation
        trace_composition_absorbed_query_relation M x y}"
proof
  fix y
  assume y:
    "y \<in> {y.
      hash_state_relation_direct_activation
        (trace_composition_absorbed_query_relation_bounded L) M x y}"
  have active_new:
      "hash_state_relation_active
        (trace_composition_absorbed_query_relation_bounded L)
        (fmupd x y M) x y"
    using y unfolding hash_state_relation_direct_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) x = Some y"
    and bounded_rel_new:
      "trace_composition_absorbed_query_relation_bounded L
        (fmupd x y M) x y"
    using active_new unfolding hash_state_relation_active_def by blast+
  have rel_new:
      "trace_composition_absorbed_query_relation (fmupd x y M) x y"
    using bounded_rel_new
    unfolding trace_composition_absorbed_query_relation_bounded_def
    by blast
  have original_new:
      "hash_state_relation_active
        trace_composition_absorbed_query_relation
        (fmupd x y M) x y"
    unfolding hash_state_relation_active_def
    using lookup_new rel_new by simp
  have original_old:
      "\<not> hash_state_relation_active
        trace_composition_absorbed_query_relation M x y"
    using fresh unfolding hash_state_relation_active_def by simp
  show
    "y \<in> {y.
      hash_state_relation_direct_activation
        trace_composition_absorbed_query_relation M x y}"
    unfolding hash_state_relation_direct_activation_def
    using original_new original_old by simp
qed


lemma trace_composition_bounded_direct_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_direct_activation
        (trace_composition_absorbed_query_relation_bounded L) M x y}
      \<le> query_raw_preimage_card_envelope
        trace_composition_query_index_bound"
proof -
  let ?A =
    "{y.
      hash_state_relation_direct_activation
        (trace_composition_absorbed_query_relation_bounded L) M x y}"
  let ?B =
    "{y.
      hash_state_relation_direct_activation
        trace_composition_absorbed_query_relation M x y}"
  have subset: "?A \<subseteq> ?B"
    by (rule trace_composition_bounded_direct_activation_subset[OF fresh])
  have finite_B: "finite ?B"
  proof -
    have "card ?B \<le>
        query_raw_preimage_card_envelope
          trace_composition_query_index_bound"
      by (rule
        trace_composition_absorbed_query_relation_direct_fiber_card_bound)
    then show ?thesis by simp
  qed
  have "card ?A \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  also have "... \<le>
      query_raw_preimage_card_envelope
        trace_composition_query_index_bound"
    by (rule
      trace_composition_absorbed_query_relation_direct_fiber_card_bound)
  finally show ?thesis .
qed

lemma trace_composition_bounded_drift_activation_subset:
  assumes fresh: "fmlookup M x = None"
  shows
    "{y.
      hash_state_relation_drift_activation
        (trace_composition_absorbed_query_relation_bounded L) M x y}
      \<subseteq>
    {y.
      hash_state_relation_drift_activation
        trace_composition_absorbed_query_relation M x y}"
proof
  fix y
  assume y:
    "y \<in> {y.
      hash_state_relation_drift_activation
        (trace_composition_absorbed_query_relation_bounded L) M x y}"
  then obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        (trace_composition_absorbed_query_relation_bounded L)
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        (trace_composition_absorbed_query_relation_bounded L) M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and bounded_rel_new:
      "trace_composition_absorbed_query_relation_bounded L
        (fmupd x y M) k z"
    using active_new unfolding hash_state_relation_active_def by blast+
  have domain_new: "card (fmdom' (fmupd x y M)) \<le> L"
    and rel_new:
      "trace_composition_absorbed_query_relation
        (fmupd x y M) k z"
    using bounded_rel_new
    unfolding trace_composition_absorbed_query_relation_bounded_def
    by blast+
  have domain_old: "card (fmdom' M) \<le> L"
    using card_fmdom_fmupd_mono[of M x y] domain_new
    by linarith
  have original_new:
      "hash_state_relation_active
        trace_composition_absorbed_query_relation
        (fmupd x y M) k z"
    unfolding hash_state_relation_active_def
    using lookup_new rel_new by simp
  have original_old:
      "\<not> hash_state_relation_active
        trace_composition_absorbed_query_relation M k z"
  proof
    assume old:
      "hash_state_relation_active
        trace_composition_absorbed_query_relation M k z"
    have lookup_old: "fmlookup M k = Some z"
      and rel_old:
        "trace_composition_absorbed_query_relation M k z"
      using old unfolding hash_state_relation_active_def by blast+
    have bounded_old:
        "trace_composition_absorbed_query_relation_bounded L M k z"
      unfolding trace_composition_absorbed_query_relation_bounded_def
      using domain_old rel_old by simp
    have
        "hash_state_relation_active
          (trace_composition_absorbed_query_relation_bounded L) M k z"
      unfolding hash_state_relation_active_def
      using lookup_old bounded_old by simp
    then show False using inactive_old by contradiction
  qed
  show
      "y \<in> {y.
        hash_state_relation_drift_activation
          trace_composition_absorbed_query_relation M x y}"
    unfolding hash_state_relation_drift_activation_def
    using key_neq original_new original_old by blast
qed


lemma trace_composition_bounded_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
    and domain: "card (fmdom' M) \<le> L"
  shows
    "card {y.
      hash_state_relation_drift_activation
        (trace_composition_absorbed_query_relation_bounded L) M x y}
      \<le> 5 * L + 2"
proof -
  let ?A =
    "{y.
      hash_state_relation_drift_activation
        (trace_composition_absorbed_query_relation_bounded L) M x y}"
  let ?B =
    "{y.
      hash_state_relation_drift_activation
        trace_composition_absorbed_query_relation M x y}"
  have subset: "?A \<subseteq> ?B"
    by (rule trace_composition_bounded_drift_activation_subset[OF fresh])
  have finite_B: "finite ?B"
  proof -
    have "card ?B \<le> 5 * card (fmdom' M) + 2"
      by (rule
        trace_composition_absorbed_query_relation_drift_fiber_card_bound[
          OF fresh])
    then show ?thesis by simp
  qed
  have "card ?A \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  also have "... \<le> 5 * card (fmdom' M) + 2"
    by (rule
      trace_composition_absorbed_query_relation_drift_fiber_card_bound[
        OF fresh])
  also have "... \<le> 5 * L + 2"
    using domain by simp
  finally show ?thesis .
qed


lemma trace_composition_bounded_transition_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_transition
        (trace_composition_absorbed_query_relation_bounded L)
        M (fmupd x y M)}
      \<le>
      query_raw_preimage_card_envelope
        trace_composition_query_index_bound +
      (5 * L + 2)"
proof (cases "card (fmdom' M) \<le> L")
  case True
  have direct:
      "card {y.
        hash_state_relation_direct_activation
          (trace_composition_absorbed_query_relation_bounded L) M x y}
        \<le> query_raw_preimage_card_envelope
          trace_composition_query_index_bound"
    by (rule trace_composition_bounded_direct_fiber_card_bound[OF fresh])
  have drift:
      "card {y.
        hash_state_relation_drift_activation
          (trace_composition_absorbed_query_relation_bounded L) M x y}
        \<le> 5 * L + 2"
    by (rule
      trace_composition_bounded_drift_fiber_card_bound[OF fresh True])
  show ?thesis
    by (rule hash_state_relation_transition_update_fiber_card_bound[
      OF direct drift])
next
  case False
  have no_active:
      "\<And>y k z.
        \<not> hash_state_relation_active
          (trace_composition_absorbed_query_relation_bounded L)
          (fmupd x y M) k z"
  proof
    fix y k z
    assume active_new:
      "hash_state_relation_active
        (trace_composition_absorbed_query_relation_bounded L)
        (fmupd x y M) k z"
    have domain_new: "card (fmdom' (fmupd x y M)) \<le> L"
      using active_new
      unfolding hash_state_relation_active_def
        trace_composition_absorbed_query_relation_bounded_def
      by blast
    have domain_old: "card (fmdom' M) \<le> L"
      using card_fmdom_fmupd_mono[of M x y] domain_new
      by linarith
    show False using False domain_old by contradiction
  qed
  have no_transition:
      "{y.
        hash_state_relation_transition
          (trace_composition_absorbed_query_relation_bounded L)
          M (fmupd x y M)} = {}"
    unfolding hash_state_relation_transition_def
    using no_active by auto
  show ?thesis using no_transition by simp
qed


lemma wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_trace_composition_bounded_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  defines
    "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (trace_composition_absorbed_query_relation_bounded q)
          (HashMap adversary_initial_state))
        adversary_initial_state
      \<le>
      nnreal
        (q *
          (query_raw_preimage_card_envelope
              trace_composition_query_index_bound +
            (5 * q + 2))) /
        nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B =
    "query_raw_preimage_card_envelope
        trace_composition_query_index_bound +
      (5 * ?Q + 2)"
  have steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition
            (trace_composition_absorbed_query_relation_bounded ?Q)
            M (fmupd x y M)}
          \<le> ?B"
    by (rule trace_composition_bounded_transition_fiber_card_bound)
  have bound:
      "wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (hash_state_relation_transition_event
            (trace_composition_absorbed_query_relation_bounded ?Q)
            (HashMap adversary_initial_state))
          adversary_initial_state
        \<le> nnreal (?Q * ?B) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound[
        OF wf controlled nonempty steps])
  show ?thesis
    using bound unfolding q_def by simp
qed


lemma wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_trace_composition_bounded_relation_all_rounds:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  defines
    "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (trace_composition_absorbed_query_relation_bounded q)
          (HashMap adversary_initial_state))
        adversary_initial_state
      \<le>
      nnreal
        (q *
          (query_raw_preimage_card_envelope
              trace_composition_query_index_bound +
            (5 * q + 2))) /
        nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B =
    "query_raw_preimage_card_envelope
        trace_composition_query_index_bound +
      (5 * ?Q + 2)"
  have steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition
            (trace_composition_absorbed_query_relation_bounded ?Q)
            M (fmupd x y M)}
          \<le> ?B"
    by (rule trace_composition_bounded_transition_fiber_card_bound)
  have bound:
      "wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (hash_state_relation_transition_event
            (trace_composition_absorbed_query_relation_bounded ?Q)
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
