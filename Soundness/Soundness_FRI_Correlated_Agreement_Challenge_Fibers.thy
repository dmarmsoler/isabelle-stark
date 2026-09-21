theory Soundness_FRI_Correlated_Agreement_Challenge_Fibers
  imports
    Soundness_FRI_Correlated_Agreement_Challenge_Relations
begin

section \<open>Direct challenge fibers at uniquely determined prefixes\<close>
text \<open>
  A clean trace key determines one root. A clean composition key determines one
  encoded degree and root. The existing binary cardinality theorem bounds that
  single target; the uniform cap is an explicit relaxation over layer radii.
\<close>

context soundness
begin

lemma mca_conditioned_trace_fri_bad_challenge_relation_direct_fiber_card_bound:
  assumes eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and trace_rate: "4*fri_padded_degree_bound (clength - 1) \<le> clength*scale"
  shows
    "card {y.
      hash_state_relation_direct_activation
        (mca_conditioned_trace_fri_bad_challenge_relation) M x y}
      \<le> fri_mca_direct_cap"
proof (cases "{y.
    hash_state_relation_direct_activation
      (mca_conditioned_trace_fri_bad_challenge_relation) M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
      "hash_state_relation_direct_activation
        (mca_conditioned_trace_fri_bad_challenge_relation) M x y0"
    by blast
  have rel0:
      "mca_conditioned_trace_fri_bad_challenge_relation
        (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from mca_conditioned_trace_fri_bad_challenge_relationD[OF rel0]
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
      "y0 \<in> fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j0) j0
        (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
    .
  let ?B =
    "fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j0) j0
      (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          (mca_conditioned_trace_fri_bad_challenge_relation) M x y}
        \<subseteq> ?B"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          (mca_conditioned_trace_fri_bad_challenge_relation) M x y}"
    have rel:
        "mca_conditioned_trace_fri_bad_challenge_relation
          (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from mca_conditioned_trace_fri_bad_challenge_relationD[OF rel]
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
        "y \<in> fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j
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
        (mca_conditioned_trace_fri_bad_challenge_relation) M x y}
      \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  have rounds_eq:
      "length roots0 = ceil_log (Suc (clength - 1))"
    using roots_len0 clength_pos by simp
  have rounds_fit: "Suc (length roots0) \<le> N"
    using roots_len0 trace_rounds_fit by simp
  have B_card: "card ?B \<le> fri_mca_direct_cap"
    by (rule fri_mca_online_uniform_card[
      OF eval_power rounds_eq rounds_fit trace_rate j_bound0])
  show ?thesis using fiber_le B_card by linarith
qed

lemma mca_conditioned_composition_fri_bad_challenge_relation_direct_fiber_card_bound:
  assumes eval_power: "clength * scale = 2 ^ N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and composition_rate: "4*fri_padded_degree_bound maxDegree \<le> clength*scale"
  shows
    "card {y.
      hash_state_relation_direct_activation
        (mca_conditioned_composition_fri_bad_challenge_relation)
        M x y}
      \<le> fri_mca_direct_cap"
proof (cases "{y.
    hash_state_relation_direct_activation
      (mca_conditioned_composition_fri_bad_challenge_relation)
      M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
      "hash_state_relation_direct_activation
        (mca_conditioned_composition_fri_bad_challenge_relation)
        M x y0"
    by blast
  have rel0:
      "mca_conditioned_composition_fri_bad_challenge_relation
        (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from mca_conditioned_composition_fri_bad_challenge_relationD[OF rel0]
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
      "y0 \<in> fri_mca_online_bad_challenges (to_nat dg0) (fri_mca_quarter_radii j0) j0
        (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
    .
  let ?B =
    "fri_mca_online_bad_challenges (to_nat dg0) (fri_mca_quarter_radii j0) j0
      (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          (mca_conditioned_composition_fri_bad_challenge_relation)
          M x y}
        \<subseteq> ?B"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          (mca_conditioned_composition_fri_bad_challenge_relation)
          M x y}"
    have rel:
        "mca_conditioned_composition_fri_bad_challenge_relation
          (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from mca_conditioned_composition_fri_bad_challenge_relationD[OF rel]
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
        "y \<in> fri_mca_online_bad_challenges (to_nat dg) (fri_mca_quarter_radii j) j
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
          (mca_conditioned_composition_fri_bad_challenge_relation)
          M x y}

        \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  have local_log_le:
      "ceil_log (Suc (to_nat dg0)) \<le> ceil_log (Suc maxDegree)"
    by (rule ceil_log_mono) (use degree_bound0 in simp)
  have roots_le:
      "length roots0 \<le> ceil_log (Suc maxDegree)"
    using roots_len0 local_log_le by simp
  have rounds_fit: "Suc (length roots0) \<le> N"
    using roots_le composition_rounds_fit by linarith
  have padded: "fri_padded_degree_bound (to_nat dg0) \<le> fri_padded_degree_bound maxDegree"
    by (rule fri_padded_degree_bound_mono[OF degree_bound0])
  have rate: "4*fri_padded_degree_bound (to_nat dg0) \<le> clength*scale"
    using padded composition_rate by linarith
  have B_card: "card ?B \<le> fri_mca_direct_cap"
    by (rule fri_mca_online_uniform_card[
      OF eval_power roots_len0 rounds_fit rate j_bound0])
  show ?thesis using fiber_le B_card by linarith
qed

end
end
