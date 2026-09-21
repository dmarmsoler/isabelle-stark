theory Soundness_FRI_Robust_Exact_Rate_Challenge_Relation
  imports
    Soundness_FRI_Robust_Challenge_Relation
    Soundness_FRI_Robust_Exact_Rate_Conceptual_Split
begin

context soundness
begin

lemma card_fri_online_robust_bad_challenges_uniform_exact_two:
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and exponent_fit: "m + K \<le> N"
    and K_pos: "0 < K"
    and exact: "fri_linear_exact_list_cap d m K 2"
    and i_bound: "i < m"
  shows
    "card (fri_online_robust_bad_challenges
      d m K i state fri_root) \<le>
        fri_robust_challenge_card_bound m K"
proof -
  have local:
      "card (fri_online_robust_bad_challenges
        d m K i state fri_root) \<le>
          2 * fri_linear_good_radius m K i + 3"
    by (rule card_fri_online_robust_bad_challenges_exact_two[
          OF eval_power rounds_eq exponent_fit K_pos exact i_bound])
  have radius:
      "fri_linear_good_radius m K i \<le>
        fri_linear_good_radius m K 0"
    by (rule fri_linear_good_radius_le_initial[
          OF eval_power i_bound exponent_fit])
  have
      "2 * fri_linear_good_radius m K i + 3 \<le>
        fri_robust_challenge_card_bound m K"
    unfolding fri_robust_challenge_card_bound_def
    using radius by simp
  then show ?thesis
    using local by linarith
qed


lemma robust_conditioned_trace_fri_bad_challenge_relation_direct_fiber_card_bound_exact_two:
  assumes eval_power: "clength * scale = 2 ^ N"
    and trace_exponent_fit: "ceil_log clength + K \<le> N"
    and K_pos: "0 < K"
    and trace_exact:
      "fri_linear_exact_list_cap
        (clength - 1) (ceil_log clength) K 2"
  shows
    "card {y.
      hash_state_relation_direct_activation
        (robust_conditioned_trace_fri_bad_challenge_relation K) M x y}
      \<le> fri_robust_challenge_card_bound (ceil_log clength) K"
proof (cases "{y.
    hash_state_relation_direct_activation
      (robust_conditioned_trace_fri_bad_challenge_relation K) M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
      "hash_state_relation_direct_activation
        (robust_conditioned_trace_fri_bad_challenge_relation K) M x y0"
    by blast
  have rel0:
      "robust_conditioned_trace_fri_bad_challenge_relation K
        (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from robust_conditioned_trace_fri_bad_challenge_relationD[OF rel0]
  obtain fr0 roots0 final0 j0 where
    clean0:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y0 M))"
    and no_initial0:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y0 M))"
    and roots_len0: "length roots0 = ceil_log clength"
    and j_bound0: "j0 < length roots0"
    and chain0:
      "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state)
        (fr0 # take (Suc j0) roots0) final0"
    and x_eq0: "x = TraceFriChallenge j0 final0"
    and y0_bad:
      "y0 \<in> fri_online_robust_bad_challenges
        (clength - 1) (length roots0) K j0
        (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
    .
  let ?B =
    "fri_online_robust_bad_challenges
      (clength - 1) (length roots0) K j0
      (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          (robust_conditioned_trace_fri_bad_challenge_relation K) M x y}
        \<subseteq> ?B"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          (robust_conditioned_trace_fri_bad_challenge_relation K) M x y}"
    have rel:
        "robust_conditioned_trace_fri_bad_challenge_relation K
          (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from robust_conditioned_trace_fri_bad_challenge_relationD[OF rel]
    obtain fr roots final j where
      clean:
        "\<not> hash_map_output_collision
          (channel_for_hash_map (fmupd x y M))"
      and no_initial:
        "PState adversary_initial_state \<notin>
          hash_map_output_values (channel_for_hash_map (fmupd x y M))"
      and roots_len: "length roots = ceil_log clength"
      and j_bound: "j < length roots"
      and chain:
        "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
          (PState adversary_initial_state)
          (fr # take (Suc j) roots) final"
      and x_eq: "x = TraceFriChallenge j final"
      and y_bad:
        "y \<in> fri_online_robust_bad_challenges
          (clength - 1) (length roots) K j
          (channel_for_hash_map (fmupd x y M)) (roots ! j)"
      .
    have j_eq: "j = j0" and final_eq: "final = final0"
      using x_eq x_eq0 by simp_all
    have chain_base:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          (fr # take (Suc j) roots) final0"
      using chain j_eq final_eq unfolding x_eq0
      by (simp only: ro_absorb_lookup_chain_trace_fri_challenge_update)
    have chain_ref:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (fr # take (Suc j) roots) final0"
      using chain_base unfolding x_eq0
      by (simp only: ro_absorb_lookup_chain_trace_fri_challenge_update)
    have messages_eq:
        "fr # take (Suc j) roots = fr0 # take (Suc j0) roots0"
      by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
            OF clean0 no_initial0 chain_ref chain0])
    have roots_prefix_eq:
        "take (Suc j0) roots = take (Suc j0) roots0"
      using messages_eq j_eq by simp
    have prefix_nth_eq:
        "take (Suc j0) roots ! j0 = take (Suc j0) roots0 ! j0"
      using roots_prefix_eq by simp
    have root_eq: "roots ! j0 = roots0 ! j0"

      using prefix_nth_eq j_bound j_eq j_bound0 by simp
    show "y \<in> ?B"
      using y_bad j_eq root_eq roots_len roots_len0
      unfolding x_eq0
      by simp
  qed
  have finite_B: "finite ?B"
    by simp
  have fiber_le: "card {y.
      hash_state_relation_direct_activation
        (robust_conditioned_trace_fri_bad_challenge_relation K) M x y}
      \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  have rounds_eq:
      "length roots0 = ceil_log (Suc (clength - 1))"
    using roots_len0 clength_pos by simp
  have exponent_fit: "length roots0 + K \<le> N"
    using roots_len0 trace_exponent_fit by simp
  have exact:
      "fri_linear_exact_list_cap
        (clength - 1) (length roots0) K 2"
    using roots_len0 trace_exact by simp
  have B_card:
      "card ?B \<le>
        fri_robust_challenge_card_bound (length roots0) K"
    by (rule card_fri_online_robust_bad_challenges_uniform_exact_two[
          OF eval_power rounds_eq exponent_fit K_pos exact j_bound0])
  have bound_eq:
      "fri_robust_challenge_card_bound (length roots0) K =
        fri_robust_challenge_card_bound (ceil_log clength) K"
    using roots_len0 by simp
  show ?thesis
    using fiber_le B_card unfolding bound_eq by linarith
qed


lemma robust_conditioned_trace_fri_bounded_transition_fiber_card_bound_exact_two:
  assumes fresh: "fmlookup M x = None"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_exponent_fit: "ceil_log clength + K \<le> N"
    and K_pos: "0 < K"
    and trace_exact:
      "fri_linear_exact_list_cap
        (clength - 1) (ceil_log clength) K 2"
  shows
    "card {y.
      hash_state_relation_transition
        (conditioned_fri_relation_bounded L
          (robust_conditioned_trace_fri_bad_challenge_relation K))
        M (fmupd x y M)}
      \<le> fri_robust_challenge_card_bound (ceil_log clength) K +
        (7 * L + 2)"
proof (rule conditioned_fri_bounded_transition_fiber_card_bound[
    OF fresh])
  assume "card (fmdom' M) \<le> L"
  show
    "card {y.
      hash_state_relation_direct_activation
        (robust_conditioned_trace_fri_bad_challenge_relation K) M x y}
      \<le> fri_robust_challenge_card_bound (ceil_log clength) K"
    by (rule
      robust_conditioned_trace_fri_bad_challenge_relation_direct_fiber_card_bound_exact_two[
        OF eval_power trace_exponent_fit K_pos trace_exact])
next
  assume domain: "card (fmdom' M) \<le> L"
  have
    "card {y.
      hash_state_relation_drift_activation
        (robust_conditioned_trace_fri_bad_challenge_relation K) M x y}
      \<le> 7 * card (fmdom' M) + 2"
    by (rule
      robust_conditioned_trace_fri_bad_challenge_relation_drift_fiber_card_bound[
        OF fresh])
  also have "... \<le> 7 * L + 2"
    by (rule add_le_mono[OF mult_left_mono[OF domain] order_refl], simp)
  finally show
    "card {y.
      hash_state_relation_drift_activation
        (robust_conditioned_trace_fri_bad_challenge_relation K) M x y}
      \<le> 7 * L + 2"
    .
qed


lemma
  wp_ro_checked_staged_transcript_with_query_witnesses_robust_conditioned_trace_fri_relation_exact_two:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_exponent_fit: "ceil_log clength + K \<le> N"
    and K_pos: "0 < K"
    and trace_exact:
      "fri_linear_exact_list_cap
        (clength - 1) (ceil_log clength) K 2"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded q
          (robust_conditioned_trace_fri_bad_challenge_relation K))
        (HashMap adversary_initial_state))
      adversary_initial_state
      \<le> nnreal
          (q *
            (fri_robust_challenge_card_bound (ceil_log clength) K +
              (7 * q + 2))) /
        nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B =
    "fri_robust_challenge_card_bound (ceil_log clength) K +
      (7 * ?Q + 2)"
  have steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition
            (conditioned_fri_relation_bounded ?Q
              (robust_conditioned_trace_fri_bad_challenge_relation K))
            M (fmupd x y M)}
          \<le> ?B"
    by (rule
      robust_conditioned_trace_fri_bounded_transition_fiber_card_bound_exact_two[
        OF _ eval_power trace_exponent_fit K_pos trace_exact])
  have bound:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (conditioned_fri_relation_bounded ?Q
            (robust_conditioned_trace_fri_bad_challenge_relation K))
          (HashMap adversary_initial_state))
        adversary_initial_state
        \<le> nnreal (?Q * ?B) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound_all_rounds[
        OF wf controlled steps])
  show ?thesis
    using bound unfolding q_def by simp
qed


lemma robust_conditioned_composition_fri_bad_challenge_relation_direct_fiber_card_bound_exact_two:
  assumes eval_power: "clength * scale = 2 ^ N"
    and composition_exponent_fit:
      "ceil_log (Suc maxDegree) + K \<le> N"
    and K_pos: "0 < K"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>

        fri_linear_exact_list_cap d (ceil_log (Suc d)) K 2"
  shows
    "card {y.
      hash_state_relation_direct_activation
        (robust_conditioned_composition_fri_bad_challenge_relation K)
        M x y}
      \<le> fri_robust_challenge_card_bound
          (ceil_log (Suc maxDegree)) K"
proof (cases "{y.
    hash_state_relation_direct_activation
      (robust_conditioned_composition_fri_bad_challenge_relation K)
      M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
      "hash_state_relation_direct_activation
        (robust_conditioned_composition_fri_bad_challenge_relation K)
        M x y0"
    by blast
  have rel0:
      "robust_conditioned_composition_fri_bad_challenge_relation K
        (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from robust_conditioned_composition_fri_bad_challenge_relationD[OF rel0]
  obtain fr0 trace_roots0 trace_final0 as0 dg0 roots0 final0 j0 where
    clean0:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y0 M))"
    and no_initial0:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y0 M))"
    and trace_len0: "length trace_roots0 = ceil_log clength"
    and alpha_len0: "length as0 = length spec"
    and degree_bound0: "to_nat dg0 \<le> maxDegree"
    and roots_len0:
      "length roots0 = ceil_log (Suc (to_nat dg0))"
    and j_bound0: "j0 < length roots0"
    and chain0:
      "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr0 trace_roots0 trace_final0 as0 dg0 roots0 j0) final0"
    and x_eq0: "x = CompositionFriChallenge j0 final0"
    and y0_bad:
      "y0 \<in> fri_online_robust_bad_challenges
        (to_nat dg0) (length roots0) K j0
        (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
    .
  let ?B =
    "fri_online_robust_bad_challenges
      (to_nat dg0) (length roots0) K j0
      (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          (robust_conditioned_composition_fri_bad_challenge_relation K)
          M x y}
        \<subseteq> ?B"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          (robust_conditioned_composition_fri_bad_challenge_relation K)
          M x y}"
    have rel:
        "robust_conditioned_composition_fri_bad_challenge_relation K
          (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from robust_conditioned_composition_fri_bad_challenge_relationD[OF rel]
    obtain fr trace_roots trace_final as dg roots final j where
      clean:
        "\<not> hash_map_output_collision
          (channel_for_hash_map (fmupd x y M))"
      and no_initial:
        "PState adversary_initial_state \<notin>
          hash_map_output_values (channel_for_hash_map (fmupd x y M))"
      and trace_len: "length trace_roots = ceil_log clength"
      and alpha_len: "length as = length spec"
      and degree_bound: "to_nat dg \<le> maxDegree"
      and roots_len:
        "length roots = ceil_log (Suc (to_nat dg))"
      and j_bound: "j < length roots"
      and chain:
        "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
          (PState adversary_initial_state)
          (composition_fri_challenge_prefix_messages
            fr trace_roots trace_final as dg roots j) final"
      and x_eq: "x = CompositionFriChallenge j final"
      and y_bad:
        "y \<in> fri_online_robust_bad_challenges
          (to_nat dg) (length roots) K j
          (channel_for_hash_map (fmupd x y M)) (roots ! j)"
      .
    have j_eq: "j = j0" and final_eq: "final = final0"
      using x_eq x_eq0 by simp_all
    have chain_base:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          (composition_fri_challenge_prefix_messages
            fr trace_roots trace_final as dg roots j0) final0"
      using chain j_eq final_eq unfolding x_eq0
      by (simp only:
        ro_absorb_lookup_chain_composition_fri_challenge_update)
    have chain_ref:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (composition_fri_challenge_prefix_messages
            fr trace_roots trace_final as dg roots j0) final0"
      using chain_base unfolding x_eq0
      by (simp only:
        ro_absorb_lookup_chain_composition_fri_challenge_update)
    have messages_eq:
        "composition_fri_challenge_prefix_messages
            fr trace_roots trace_final as dg roots j0 =
          composition_fri_challenge_prefix_messages
            fr0 trace_roots0 trace_final0 as0 dg0 roots0 j0"
      by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
        OF clean0 no_initial0 chain_ref chain0])
    from composition_fri_challenge_prefix_messages_degree_roots_eq[
        OF trace_len trace_len0 alpha_len alpha_len0 messages_eq]
    have degree_eq: "dg = dg0"
      and roots_prefix_eq:
        "take (Suc j0) roots = take (Suc j0) roots0"
      by blast+
    have prefix_nth_eq:
        "take (Suc j0) roots ! j0 = take (Suc j0) roots0 ! j0"
      using roots_prefix_eq by simp
    have root_eq: "roots ! j0 = roots0 ! j0"
      using prefix_nth_eq j_bound j_eq j_bound0 by simp
    show "y \<in> ?B"
      using y_bad j_eq degree_eq root_eq roots_len roots_len0
      unfolding x_eq0 by simp
  qed
  have finite_B: "finite ?B"
    by simp
  have fiber_le:
      "card {y.
        hash_state_relation_direct_activation
          (robust_conditioned_composition_fri_bad_challenge_relation K)
          M x y}

        \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  have local_log_le:
      "ceil_log (Suc (to_nat dg0)) \<le> ceil_log (Suc maxDegree)"
    by (rule ceil_log_mono) (use degree_bound0 in simp)
  have roots_le:
      "length roots0 \<le> ceil_log (Suc maxDegree)"
    using roots_len0 local_log_le by simp
  have exponent_fit: "length roots0 + K \<le> N"
    using roots_le composition_exponent_fit by linarith
  have exact:
      "fri_linear_exact_list_cap
        (to_nat dg0) (length roots0) K 2"
  proof -
    have at_log:
        "fri_linear_exact_list_cap
          (to_nat dg0) (ceil_log (Suc (to_nat dg0))) K 2"
      by (rule composition_exact[OF degree_bound0])
    show ?thesis
      using at_log roots_len0 by simp
  qed
  have B_card:
      "card ?B \<le>
        fri_robust_challenge_card_bound (length roots0) K"
    by (rule card_fri_online_robust_bad_challenges_uniform_exact_two[
          OF eval_power roots_len0 exponent_fit K_pos exact j_bound0])
  have local_bound:
      "fri_robust_challenge_card_bound (length roots0) K \<le>
        fri_robust_challenge_card_bound
          (ceil_log (Suc maxDegree)) K"
    by (rule fri_robust_challenge_card_bound_mono[OF roots_le])
  show ?thesis
    using fiber_le B_card local_bound by linarith
qed


lemma robust_conditioned_composition_fri_bounded_transition_fiber_card_bound_exact_two:
  assumes fresh: "fmlookup M x = None"
    and eval_power: "clength * scale = 2 ^ N"
    and composition_exponent_fit:
      "ceil_log (Suc maxDegree) + K \<le> N"
    and K_pos: "0 < K"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_linear_exact_list_cap d (ceil_log (Suc d)) K 2"
  shows
    "card {y.
      hash_state_relation_transition
        (conditioned_fri_relation_bounded L
          (robust_conditioned_composition_fri_bad_challenge_relation K))
        M (fmupd x y M)}
      \<le> fri_robust_challenge_card_bound
          (ceil_log (Suc maxDegree)) K +
        (7 * L + 2)"
proof (rule conditioned_fri_bounded_transition_fiber_card_bound[
    OF fresh])
  assume "card (fmdom' M) \<le> L"
  show
    "card {y.
      hash_state_relation_direct_activation
        (robust_conditioned_composition_fri_bad_challenge_relation K)
        M x y}
      \<le> fri_robust_challenge_card_bound
          (ceil_log (Suc maxDegree)) K"
    by (rule
      robust_conditioned_composition_fri_bad_challenge_relation_direct_fiber_card_bound_exact_two[
        OF eval_power composition_exponent_fit K_pos composition_exact])
next
  assume domain: "card (fmdom' M) \<le> L"
  have
    "card {y.
      hash_state_relation_drift_activation
        (robust_conditioned_composition_fri_bad_challenge_relation K) M x y}
      \<le> 7 * card (fmdom' M) + 2"
    by (rule
      robust_conditioned_composition_fri_bad_challenge_relation_drift_fiber_card_bound[
        OF fresh])
  also have "... \<le> 7 * L + 2"
    by (rule add_le_mono[OF mult_left_mono[OF domain] order_refl], simp)
  finally show
    "card {y.
      hash_state_relation_drift_activation
        (robust_conditioned_composition_fri_bad_challenge_relation K) M x y}
      \<le> 7 * L + 2"
    .
qed


lemma
  wp_ro_checked_staged_transcript_with_query_witnesses_robust_conditioned_composition_fri_relation_exact_two:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and composition_exponent_fit:
      "ceil_log (Suc maxDegree) + K \<le> N"
    and K_pos: "0 < K"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_linear_exact_list_cap d (ceil_log (Suc d)) K 2"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded q
          (robust_conditioned_composition_fri_bad_challenge_relation K))
        (HashMap adversary_initial_state))
      adversary_initial_state
      \<le> nnreal
          (q *
            (fri_robust_challenge_card_bound
                (ceil_log (Suc maxDegree)) K +
              (7 * q + 2))) /
        nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B =
    "fri_robust_challenge_card_bound
        (ceil_log (Suc maxDegree)) K +
      (7 * ?Q + 2)"
  have steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition
            (conditioned_fri_relation_bounded ?Q
              (robust_conditioned_composition_fri_bad_challenge_relation K))
            M (fmupd x y M)}
          \<le> ?B"
    by (rule
      robust_conditioned_composition_fri_bounded_transition_fiber_card_bound_exact_two[
        OF _ eval_power composition_exponent_fit K_pos composition_exact])
  have bound:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (conditioned_fri_relation_bounded ?Q
            (robust_conditioned_composition_fri_bad_challenge_relation K))
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
