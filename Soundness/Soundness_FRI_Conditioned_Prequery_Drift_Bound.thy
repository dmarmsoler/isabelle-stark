theory Soundness_FRI_Conditioned_Prequery_Drift_Bound
  imports Stark.Soundness_FRI_Conditioned_Prequery_Challenge_Activation
begin

context soundness
begin

lemma ro_conditioned_augmented_absorbed_query_relation_drift_imp_clean:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y"
  shows "\<not> hash_map_output_collision (channel_for_hash_map M)"
proof -
  from drift obtain k z where
    active_new:
      "hash_state_relation_active
        ro_conditioned_augmented_absorbed_query_relation
        (fmupd x y M) k z"
    unfolding hash_state_relation_drift_activation_def by blast
  then have rel_new:
      "ro_conditioned_augmented_absorbed_query_relation
        (fmupd x y M) k z"
    unfolding hash_state_relation_active_def by blast
  have clean_new:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
    using rel_new
    unfolding ro_conditioned_augmented_absorbed_query_relation_def
      ro_conditioned_residual_absorbed_query_relation_def
      ro_conditioned_degenerate_absorbed_query_relation_def Let_def
    by blast
  show ?thesis
    by (rule hash_map_clean_fresh_update_pullback[
      OF fresh clean_new])
qed

lemma ro_conditioned_augmented_absorbed_query_relation_drift_imp_no_initial:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y"
  shows
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
proof -
  from drift obtain k z where
    active_new:
      "hash_state_relation_active
        ro_conditioned_augmented_absorbed_query_relation
        (fmupd x y M) k z"
    unfolding hash_state_relation_drift_activation_def by blast
  then have rel_new:
      "ro_conditioned_augmented_absorbed_query_relation
        (fmupd x y M) k z"
    unfolding hash_state_relation_active_def by blast
  have no_initial_new:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
    using rel_new
    unfolding ro_conditioned_augmented_absorbed_query_relation_def
      ro_conditioned_residual_absorbed_query_relation_def
      ro_conditioned_degenerate_absorbed_query_relation_def Let_def
    by blast
  show ?thesis
    by (rule hash_map_no_initial_fresh_update_pullback[
      OF fresh no_initial_new])
qed

lemma ro_conditioned_augmented_absorbed_query_relation_trace_challenge_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
    and x_trace: "x = TraceFriChallenge c ast"
  shows
    "card {y.
      hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y}
      \<le> card (fmdom' M) * card (fmdom' M) +
        7 * card (fmdom' M) + 2"
proof (cases "{y.
    hash_state_relation_drift_activation
      ro_conditioned_augmented_absorbed_query_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where drift0:
      "hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y0"
    by blast
  have clean:
      "\<not> hash_map_output_collision (channel_for_hash_map M)"
    by (rule
      ro_conditioned_augmented_absorbed_query_relation_drift_imp_clean[
        OF fresh drift0])
  have no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
    by (rule
      ro_conditioned_augmented_absorbed_query_relation_drift_imp_no_initial[
        OF fresh drift0])
  let ?D = "{y.
    hash_state_relation_drift_activation
      ro_conditioned_augmented_absorbed_query_relation M x y}"
  let ?T = "conditioned_fri_relation_drift_targets M x"
  let ?C =
    "ro_conditioned_trace_nondegenerate_challenge_drift_values M x"
  have subset: "?D \<subseteq> ?T \<union> ?C"
    using
      ro_conditioned_augmented_absorbed_query_relation_trace_challenge_drift_subset[
        OF fresh x_trace]
    by blast
  have finite_union: "finite (?T \<union> ?C)" by simp
  have card_subset: "card ?D \<le> card (?T \<union> ?C)"
    by (rule card_mono[OF finite_union subset])
  have union_le: "card (?T \<union> ?C) \<le> card ?T + card ?C"
    by (rule card_Un_le)
  have target_le: "card ?T \<le> 7 * card (fmdom' M) + 2"
    by (rule card_conditioned_fri_relation_drift_targets_le)
  have candidate_le:
      "card ?C \<le> card (fmdom' M) * card (fmdom' M)"
    by (rule
      card_ro_conditioned_trace_nondegenerate_challenge_drift_values[
        OF clean no_initial])
  have
      "card ?D \<le> card ?T + card ?C"
    by (rule order_trans[OF card_subset union_le])
  also have "... \<le>
      (7 * card (fmdom' M) + 2) +
        card (fmdom' M) * card (fmdom' M)"
    by (rule add_mono[OF target_le candidate_le])
  also have "... =
      card (fmdom' M) * card (fmdom' M) +
        7 * card (fmdom' M) + 2"
    by arith
  finally show ?thesis .
qed

lemma ro_conditioned_augmented_absorbed_query_relation_composition_challenge_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
    and x_composition: "x = CompositionFriChallenge c ast"
  shows
    "card {y.
      hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y}
      \<le> card (fmdom' M) * card (fmdom' M) +
        7 * card (fmdom' M) + 2"
proof (cases "{y.
    hash_state_relation_drift_activation
      ro_conditioned_augmented_absorbed_query_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where drift0:
      "hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y0"
    by blast
  have clean:
      "\<not> hash_map_output_collision (channel_for_hash_map M)"
    by (rule
      ro_conditioned_augmented_absorbed_query_relation_drift_imp_clean[
        OF fresh drift0])
  have no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
    by (rule
      ro_conditioned_augmented_absorbed_query_relation_drift_imp_no_initial[
        OF fresh drift0])
  let ?D = "{y.
    hash_state_relation_drift_activation
      ro_conditioned_augmented_absorbed_query_relation M x y}"
  let ?T = "conditioned_fri_relation_drift_targets M x"
  let ?C =
    "ro_conditioned_composition_nondegenerate_challenge_drift_values M x"
  have subset: "?D \<subseteq> ?T \<union> ?C"
    using
      ro_conditioned_augmented_absorbed_query_relation_composition_challenge_drift_subset[
        OF fresh x_composition]
    by blast
  have finite_union: "finite (?T \<union> ?C)" by simp
  have card_subset: "card ?D \<le> card (?T \<union> ?C)"
    by (rule card_mono[OF finite_union subset])
  have union_le: "card (?T \<union> ?C) \<le> card ?T + card ?C"
    by (rule card_Un_le)
  have target_le: "card ?T \<le> 7 * card (fmdom' M) + 2"
    by (rule card_conditioned_fri_relation_drift_targets_le)
  have candidate_le:
      "card ?C \<le> card (fmdom' M) * card (fmdom' M)"
    by (rule
      card_ro_conditioned_composition_nondegenerate_challenge_drift_values[
        OF clean no_initial])
  have
      "card ?D \<le> card ?T + card ?C"
    by (rule order_trans[OF card_subset union_le])
  also have "... \<le>
      (7 * card (fmdom' M) + 2) +
        card (fmdom' M) * card (fmdom' M)"
    by (rule add_mono[OF target_le candidate_le])
  also have "... =
      card (fmdom' M) * card (fmdom' M) +
        7 * card (fmdom' M) + 2"
    by arith
  finally show ?thesis .
qed

lemma ro_conditioned_augmented_absorbed_query_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y}
      \<le> card (fmdom' M) * card (fmdom' M) +
        7 * card (fmdom' M) + 2"
proof (cases "\<exists>c ast. x = TraceFriChallenge c ast")
  case True
  then obtain c ast where x_trace: "x = TraceFriChallenge c ast"
    by blast
  show ?thesis
    by (rule
      ro_conditioned_augmented_absorbed_query_relation_trace_challenge_drift_fiber_card_bound[
        OF fresh x_trace])
next
  case no_trace: False
  show ?thesis
  proof (cases "\<exists>c ast. x = CompositionFriChallenge c ast")
    case True
    then obtain c ast where
      x_composition: "x = CompositionFriChallenge c ast"
      by blast
    show ?thesis
      by (rule
        ro_conditioned_augmented_absorbed_query_relation_composition_challenge_drift_fiber_card_bound[
          OF fresh x_composition])
  next
    case no_composition: False
    have not_trace: "\<And>c ast. x \<noteq> TraceFriChallenge c ast"
      using no_trace by blast
    have not_composition:
        "\<And>c ast. x \<noteq> CompositionFriChallenge c ast"
      using no_composition by blast
    have
        "card {y.
          hash_state_relation_drift_activation
            ro_conditioned_augmented_absorbed_query_relation M x y}
          \<le> 7 * card (fmdom' M) + 2"
      by (rule
        ro_conditioned_augmented_absorbed_query_relation_nonchallenge_drift_fiber_card_bound[
          OF fresh not_trace not_composition])
    also have "... \<le>
        card (fmdom' M) * card (fmdom' M) +
          7 * card (fmdom' M) + 2"
      by simp
    finally show ?thesis .
  qed
qed

end
end
