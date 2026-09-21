theory Soundness_FRI_Robust_Balanced_Challenge_Relation_Base
  imports
    Stark.Soundness_FRI_Robust_Challenge_Relation
    Stark.Soundness_FRI_Robust_Balanced_Conceptual_Split
begin

context soundness
begin

lemma fri_online_balanced_bad_challenges_trace_fri_challenge_update[simp]:
  "fri_online_balanced_bad_challenges d m C i
      (channel_for_hash_map (fmupd (TraceFriChallenge c ast) y M))
      fri_root =
    fri_online_balanced_bad_challenges d m C i
      (channel_for_hash_map M) fri_root"
  unfolding fri_online_balanced_bad_challenges_def
    fri_balanced_conditioned_bad_challenges_def
    fri_conditioned_layer_table_def
  by simp

lemma fri_online_balanced_bad_challenges_composition_fri_challenge_update[simp]:
  "fri_online_balanced_bad_challenges d m C i
      (channel_for_hash_map (fmupd (CompositionFriChallenge c ast) y M))
      fri_root =
    fri_online_balanced_bad_challenges d m C i
      (channel_for_hash_map M) fri_root"
  unfolding fri_online_balanced_bad_challenges_def
    fri_balanced_conditioned_bad_challenges_def
    fri_conditioned_layer_table_def
  by simp

definition balanced_conditioned_trace_fri_bad_challenge_relation
  :: "nat \<Rightarrow> (('f protocol_hash_input, 'f) fmap) \<Rightarrow>
    'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "balanced_conditioned_trace_fri_bad_challenge_relation C M x y \<longleftrightarrow>
    (let s = channel_for_hash_map M in
      \<not> hash_map_output_collision s \<and>
      PState adversary_initial_state \<notin> hash_map_output_values s \<and>
      (\<exists>fr roots final j.
        length roots = ceil_log clength \<and>
        j < length roots \<and>
        ro_absorb_lookup_chain s (PState adversary_initial_state)
          (fr # take (Suc j) roots) final \<and>
        x = TraceFriChallenge j final \<and>
        y \<in> fri_online_balanced_bad_challenges
          (clength - 1) (length roots) C j s (roots ! j)))"

lemma balanced_conditioned_trace_fri_bad_challenge_relationD:
  assumes rel:
    "balanced_conditioned_trace_fri_bad_challenge_relation C M x y"
  obtains fr roots final j where
    "\<not> hash_map_output_collision (channel_for_hash_map M)"
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
    "length roots = ceil_log clength"
    "j < length roots"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state)
      (fr # take (Suc j) roots) final"
    "x = TraceFriChallenge j final"
    "y \<in> fri_online_balanced_bad_challenges
      (clength - 1) (length roots) C j
      (channel_for_hash_map M) (roots ! j)"
  using rel
  unfolding balanced_conditioned_trace_fri_bad_challenge_relation_def Let_def
  by blast



lemma balanced_conditioned_trace_fri_bad_challenge_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "balanced_conditioned_trace_fri_bad_challenge_relation C
        (fmupd x y M) k z"
    and no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows "balanced_conditioned_trace_fri_bad_challenge_relation C M k z"
proof -
  from balanced_conditioned_trace_fri_bad_challenge_relationD[OF rel]
  obtain fr roots final j where
    clean_new:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
    and no_initial_new:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
    and roots_len: "length roots = ceil_log clength"
    and j_bound: "j < length roots"
    and chain_new:
      "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (fr # take (Suc j) roots) final"
    and k_eq: "k = TraceFriChallenge j final"
    and z_bad_new:
      "z \<in> fri_online_balanced_bad_challenges
        (clength - 1) (length roots) C j
        (channel_for_hash_map (fmupd x y M)) (roots ! j)"
    .
  have old_lookup: "fmlookup M k = Some z"
    using active_lookup key_neq by simp
  have final_target: "final \<in> trace_fri_challenge_state_values M"
  proof -
    have "fmlookup M (TraceFriChallenge j final) = Some z"
      using old_lookup k_eq by simp
    then show ?thesis
      by (rule trace_fri_challenge_lookup_state_value)
  qed
  have chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (fr # take (Suc j) roots) final"
    by (rule
      ro_absorb_lookup_chain_conditioned_fri_fresh_update_pullback[
        OF fresh chain_new _ no_target])
      (use final_target in simp)
  have ext:
      "channel_for_hash_map M \<le>
        channel_for_hash_map (fmupd x y M)"
    by (rule channel_for_hash_map_fresh_update_extends[OF fresh])
  have clean_old:
      "\<not> hash_map_output_collision (channel_for_hash_map M)"
  proof
    assume collision_old:
      "hash_map_output_collision (channel_for_hash_map M)"
    have
      "hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
      by (rule hash_map_output_collision_mono[OF collision_old ext])
    then show False using clean_new by contradiction
  qed
  have no_initial_old:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
  proof
    assume initial_old:
      "PState adversary_initial_state \<in>
        hash_map_output_values (channel_for_hash_map M)"
    from initial_old obtain q where q_lookup0:
      "fmlookup (HashMap (channel_for_hash_map M)) q =
        Some (PState adversary_initial_state)"
      unfolding hash_map_output_values_def by blast
    have q_lookup:
        "fmlookup M q = Some (PState adversary_initial_state)"
      using q_lookup0 unfolding channel_for_hash_map_def by simp
    have q_lookup_new:
        "fmlookup (fmupd x y M) q =
          Some (PState adversary_initial_state)"
      using q_lookup fresh by (cases "q = x") simp_all
    have
      "PState adversary_initial_state \<in>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
    proof (rule hash_map_output_valuesI)
      show
        "fmlookup
          (HashMap (channel_for_hash_map (fmupd x y M))) q =
          Some (PState adversary_initial_state)"
        using q_lookup_new unfolding channel_for_hash_map_def by simp
    qed
    then show False using no_initial_new by contradiction
  qed
  have messages_target:
      "set (fr # take (Suc j) roots) \<subseteq>
        transcript_absorb_message_values M"
    by (rule ro_absorb_lookup_chain_messages_subset[OF chain_old])
  have root_in_take:
      "take (Suc j) roots ! j \<in> set (take (Suc j) roots)"
    by (rule nth_mem) (use j_bound in simp)
  have root_in_messages:
      "roots ! j \<in> set (fr # take (Suc j) roots)"
    using root_in_take j_bound by simp
  have root_target:
      "roots ! j \<in> transcript_absorb_message_values M"
    by (rule set_mp[OF messages_target root_in_messages])
  have old_no_target:
      "y \<notin> first_root_relation_drift_targets M x"
    using no_target
    unfolding conditioned_fri_relation_drift_targets_def by blast
  have table_eq:
      "conceptual_table (channel_for_hash_map (fmupd x y M))
          (roots ! j) (length (fri_canonical_domain_at j)) =
        conceptual_table (channel_for_hash_map M)
          (roots ! j) (length (fri_canonical_domain_at j))"
    by (rule conceptual_table_fresh_update[
      OF fresh root_target old_no_target])
  have family_eq:
      "fri_online_balanced_bad_challenges
          (clength - 1) (length roots) C j
          (channel_for_hash_map (fmupd x y M)) (roots ! j) =
        fri_online_balanced_bad_challenges
          (clength - 1) (length roots) C j
          (channel_for_hash_map M) (roots ! j)"
    unfolding fri_online_balanced_bad_challenges_def
    using table_eq by simp
  have z_bad_old:
      "z \<in> fri_online_balanced_bad_challenges
        (clength - 1) (length roots) C j
        (channel_for_hash_map M) (roots ! j)"
    using z_bad_new family_eq by simp
  show ?thesis
    unfolding balanced_conditioned_trace_fri_bad_challenge_relation_def Let_def
    using clean_old no_initial_old roots_len j_bound chain_old
      k_eq z_bad_old
    by blast
qed


lemma balanced_conditioned_trace_fri_bad_challenge_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        (balanced_conditioned_trace_fri_bad_challenge_relation C) M x y"
  shows "y \<in> conditioned_fri_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        (balanced_conditioned_trace_fri_bad_challenge_relation C)
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        (balanced_conditioned_trace_fri_bad_challenge_relation C) M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "balanced_conditioned_trace_fri_bad_challenge_relation C
        (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def
    by blast+
  have rel_old:
      "balanced_conditioned_trace_fri_bad_challenge_relation C M k z"
    by (rule
      balanced_conditioned_trace_fri_bad_challenge_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
      "hash_state_relation_active
        (balanced_conditioned_trace_fri_bad_challenge_relation C) M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed

lemma balanced_conditioned_trace_fri_bad_challenge_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        (balanced_conditioned_trace_fri_bad_challenge_relation C) M x y}
      \<le> 7 * card (fmdom' M) + 2"
proof -
  have subset:
      "{y.
        hash_state_relation_drift_activation
          (balanced_conditioned_trace_fri_bad_challenge_relation C) M x y}
        \<subseteq> conditioned_fri_relation_drift_targets M x"
    using
      balanced_conditioned_trace_fri_bad_challenge_relation_drift_activation_imp_target[
        OF fresh]
    by blast
  have
      "card {y.
        hash_state_relation_drift_activation
          (balanced_conditioned_trace_fri_bad_challenge_relation C) M x y}
        \<le> card (conditioned_fri_relation_drift_targets M x)"
    by (rule card_mono[
      OF finite_conditioned_fri_relation_drift_targets subset])
  also have "... \<le> 7 * card (fmdom' M) + 2"
    by (rule card_conditioned_fri_relation_drift_targets_le)
  finally show ?thesis .
qed



definition balanced_conditioned_composition_fri_bad_challenge_relation
  :: "nat \<Rightarrow> (('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "balanced_conditioned_composition_fri_bad_challenge_relation C M x y \<longleftrightarrow>
    (let s = channel_for_hash_map M in
      \<not> hash_map_output_collision s \<and>
      PState adversary_initial_state \<notin> hash_map_output_values s \<and>
      (\<exists>fr trace_roots trace_final as dg roots final j.
        length trace_roots = ceil_log clength \<and>
        length as = length spec \<and>
        to_nat dg \<le> maxDegree \<and>
        length roots = ceil_log (Suc (to_nat dg)) \<and>
        j < length roots \<and>
        ro_absorb_lookup_chain s (PState adversary_initial_state)
          (composition_fri_challenge_prefix_messages
            fr trace_roots trace_final as dg roots j) final \<and>
        x = CompositionFriChallenge j final \<and>
        y \<in> fri_online_balanced_bad_challenges
          (to_nat dg) (length roots) C j s (roots ! j)))"

lemma balanced_conditioned_composition_fri_bad_challenge_relationD:
  assumes rel:
    "balanced_conditioned_composition_fri_bad_challenge_relation C M x y"
  obtains fr trace_roots trace_final as dg roots final j where
    "\<not> hash_map_output_collision (channel_for_hash_map M)"
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
    "length trace_roots = ceil_log clength"
    "length as = length spec"
    "to_nat dg \<le> maxDegree"
    "length roots = ceil_log (Suc (to_nat dg))"
    "j < length roots"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state)
      (composition_fri_challenge_prefix_messages
        fr trace_roots trace_final as dg roots j) final"
    "x = CompositionFriChallenge j final"
    "y \<in> fri_online_balanced_bad_challenges
      (to_nat dg) (length roots) C j
      (channel_for_hash_map M) (roots ! j)"
  using rel
  unfolding balanced_conditioned_composition_fri_bad_challenge_relation_def
    Let_def
  by blast



lemma
  balanced_conditioned_composition_fri_bad_challenge_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "balanced_conditioned_composition_fri_bad_challenge_relation C
        (fmupd x y M) k z"
    and no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows "balanced_conditioned_composition_fri_bad_challenge_relation C M k z"
proof -
  from balanced_conditioned_composition_fri_bad_challenge_relationD[OF rel]
  obtain fr trace_roots trace_final as dg roots final j where
    clean_new:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
    and no_initial_new:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
    and trace_len: "length trace_roots = ceil_log clength"
    and alpha_len: "length as = length spec"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and roots_len: "length roots = ceil_log (Suc (to_nat dg))"
    and j_bound: "j < length roots"
    and chain_new:
      "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots j) final"
    and k_eq: "k = CompositionFriChallenge j final"
    and z_bad_new:
      "z \<in> fri_online_balanced_bad_challenges
        (to_nat dg) (length roots) C j
        (channel_for_hash_map (fmupd x y M)) (roots ! j)"
    .
  have old_lookup: "fmlookup M k = Some z"
    using active_lookup key_neq by simp
  have final_target:
      "final \<in> composition_fri_challenge_state_values M"
  proof -
    have "fmlookup M (CompositionFriChallenge j final) = Some z"
      using old_lookup k_eq by simp
    then show ?thesis
      by (rule composition_fri_challenge_lookup_state_value)
  qed
  have chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots j) final"
    by (rule
      ro_absorb_lookup_chain_conditioned_fri_fresh_update_pullback[
        OF fresh chain_new _ no_target])
      (use final_target in simp)
  have ext:
      "channel_for_hash_map M \<le>
        channel_for_hash_map (fmupd x y M)"
    by (rule channel_for_hash_map_fresh_update_extends[OF fresh])
  have clean_old:
      "\<not> hash_map_output_collision (channel_for_hash_map M)"
  proof
    assume collision_old:
      "hash_map_output_collision (channel_for_hash_map M)"
    have
      "hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
      by (rule hash_map_output_collision_mono[OF collision_old ext])
    then show False using clean_new by contradiction
  qed
  have no_initial_old:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
  proof
    assume initial_old:
      "PState adversary_initial_state \<in>
        hash_map_output_values (channel_for_hash_map M)"
    from initial_old obtain q where q_lookup0:
      "fmlookup (HashMap (channel_for_hash_map M)) q =
        Some (PState adversary_initial_state)"
      unfolding hash_map_output_values_def by blast
    have q_lookup:
        "fmlookup M q = Some (PState adversary_initial_state)"
      using q_lookup0 unfolding channel_for_hash_map_def by simp
    have q_lookup_new:
        "fmlookup (fmupd x y M) q =
          Some (PState adversary_initial_state)"
      using q_lookup fresh by (cases "q = x") simp_all
    have
      "PState adversary_initial_state \<in>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
    proof (rule hash_map_output_valuesI)
      show
        "fmlookup
          (HashMap (channel_for_hash_map (fmupd x y M))) q =
          Some (PState adversary_initial_state)"
        using q_lookup_new unfolding channel_for_hash_map_def by simp
    qed
    then show False using no_initial_new by contradiction
  qed
  have messages_target:
      "set (composition_fri_challenge_prefix_messages
        fr trace_roots trace_final as dg roots j)
        \<subseteq> transcript_absorb_message_values M"
    by (rule ro_absorb_lookup_chain_messages_subset[OF chain_old])
  have root_in_take:
      "take (Suc j) roots ! j \<in> set (take (Suc j) roots)"
    by (rule nth_mem) (use j_bound in simp)
  have root_in_messages:
      "roots ! j \<in> set (composition_fri_challenge_prefix_messages
        fr trace_roots trace_final as dg roots j)"
    using root_in_take j_bound
    unfolding composition_fri_challenge_prefix_messages_def by simp
  have root_target:
      "roots ! j \<in> transcript_absorb_message_values M"
    by (rule set_mp[OF messages_target root_in_messages])
  have old_no_target:
      "y \<notin> first_root_relation_drift_targets M x"
    using no_target
    unfolding conditioned_fri_relation_drift_targets_def by blast
  have table_eq:
      "conceptual_table (channel_for_hash_map (fmupd x y M))
          (roots ! j) (length (fri_canonical_domain_at j)) =
        conceptual_table (channel_for_hash_map M)
          (roots ! j) (length (fri_canonical_domain_at j))"
    by (rule conceptual_table_fresh_update[
      OF fresh root_target old_no_target])
  have family_eq:
      "fri_online_balanced_bad_challenges
          (to_nat dg) (length roots) C j
          (channel_for_hash_map (fmupd x y M)) (roots ! j) =
        fri_online_balanced_bad_challenges
          (to_nat dg) (length roots) C j
          (channel_for_hash_map M) (roots ! j)"
    unfolding fri_online_balanced_bad_challenges_def
    using table_eq by simp
  have z_bad_old:
      "z \<in> fri_online_balanced_bad_challenges
        (to_nat dg) (length roots) C j
        (channel_for_hash_map M) (roots ! j)"
    using z_bad_new family_eq by simp
  show ?thesis
    unfolding
      balanced_conditioned_composition_fri_bad_challenge_relation_def Let_def
    using clean_old no_initial_old trace_len alpha_len degree_bound
      roots_len j_bound chain_old k_eq z_bad_old
    by blast
qed


lemma
  balanced_conditioned_composition_fri_bad_challenge_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        (balanced_conditioned_composition_fri_bad_challenge_relation C)
        M x y"
  shows "y \<in> conditioned_fri_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        (balanced_conditioned_composition_fri_bad_challenge_relation C)
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        (balanced_conditioned_composition_fri_bad_challenge_relation C) M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "balanced_conditioned_composition_fri_bad_challenge_relation C
        (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def
    by blast+
  have rel_old:
      "balanced_conditioned_composition_fri_bad_challenge_relation C M k z"
    by (rule
      balanced_conditioned_composition_fri_bad_challenge_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
      "hash_state_relation_active
        (balanced_conditioned_composition_fri_bad_challenge_relation C) M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed

lemma balanced_conditioned_composition_fri_bad_challenge_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        (balanced_conditioned_composition_fri_bad_challenge_relation C)
        M x y}
      \<le> 7 * card (fmdom' M) + 2"
proof -
  have subset:
      "{y.
        hash_state_relation_drift_activation
          (balanced_conditioned_composition_fri_bad_challenge_relation C)
          M x y}
        \<subseteq> conditioned_fri_relation_drift_targets M x"
    using
      balanced_conditioned_composition_fri_bad_challenge_relation_drift_activation_imp_target[
        OF fresh]
    by blast
  have
      "card {y.
        hash_state_relation_drift_activation
          (balanced_conditioned_composition_fri_bad_challenge_relation C)
          M x y}
        \<le> card (conditioned_fri_relation_drift_targets M x)"
    by (rule card_mono[
      OF finite_conditioned_fri_relation_drift_targets subset])
  also have "... \<le> 7 * card (fmdom' M) + 2"
    by (rule card_conditioned_fri_relation_drift_targets_le)
  finally show ?thesis .
qed


lemma checked_builder_trace_balanced_online_bad_imp_conditioned_relation_active:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision t"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values t"
    and hit:
      "\<exists>j < length (staged_trace_fri_roots data).
        staged_trace_fri_challenges data ! j \<in>
          fri_online_balanced_bad_challenges
            (clength - 1) (length (staged_trace_fri_roots data)) C j t
            (staged_trace_fri_roots data ! j)"
  shows
    "\<exists>x y.
      hash_state_relation_active
        (balanced_conditioned_trace_fri_bad_challenge_relation C)
        (HashMap t) x y"
proof -
  from hit obtain j where
    j_bound: "j < length (staged_trace_fri_roots data)"
    and bad:
      "staged_trace_fri_challenges data ! j \<in>
        fri_online_balanced_bad_challenges
          (clength - 1) (length (staged_trace_fri_roots data)) C j t
          (staged_trace_fri_roots data ! j)"
    by blast
  have prefixes:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength \<and>
       (\<forall>j < length (staged_trace_fri_roots data). \<exists>final.
         ro_absorb_lookup_chain t (PState adversary_initial_state)
           (staged_trace_root data #
             take (Suc j) (staged_trace_fri_roots data)) final \<and>
         fmlookup (HashMap t) (TraceFriChallenge j final) =
           Some (staged_trace_fri_challenges data ! j))"
    using ro_checked_staged_transcript_program_conditioned_challenge_prefixes[
      OF wf controlled outcome]
    by blast
  from prefixes j_bound obtain final where
    chain:
      "ro_absorb_lookup_chain t (PState adversary_initial_state)
        (staged_trace_root data #
          take (Suc j) (staged_trace_fri_roots data)) final"
    and lookup:
      "fmlookup (HashMap t) (TraceFriChallenge j final) =
        Some (staged_trace_fri_challenges data ! j)"
    by blast
  have final_map:
      "HashMap (channel_for_hash_map (HashMap t)) = HashMap t"
    unfolding channel_for_hash_map_def adversary_initial_state_def by simp
  have chain_map:
      "ro_absorb_lookup_chain (channel_for_hash_map (HashMap t))
        (PState adversary_initial_state)
        (staged_trace_root data #
          take (Suc j) (staged_trace_fri_roots data)) final"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule chain)
  have clean_map:
      "\<not> hash_map_output_collision (channel_for_hash_map (HashMap t))"
    using clean final_map unfolding hash_map_output_collision_def by simp
  have no_initial_map:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (HashMap t))"
    using no_initial final_map unfolding hash_map_output_values_def by simp
  have tables:
      "conceptual_table (channel_for_hash_map (HashMap t)) =
        conceptual_table t"
    by (rule ext)+
      (rule conceptual_table_cong_hash_map[OF final_map])
  have family_eq:
      "fri_online_balanced_bad_challenges
          (clength - 1) (length (staged_trace_fri_roots data)) C j
          (channel_for_hash_map (HashMap t))
          (staged_trace_fri_roots data ! j) =
        fri_online_balanced_bad_challenges
          (clength - 1) (length (staged_trace_fri_roots data)) C j t
          (staged_trace_fri_roots data ! j)"
    unfolding fri_online_balanced_bad_challenges_def tables by simp
  have bad_map:
      "staged_trace_fri_challenges data ! j \<in>
        fri_online_balanced_bad_challenges
          (clength - 1) (length (staged_trace_fri_roots data)) C j
          (channel_for_hash_map (HashMap t))
          (staged_trace_fri_roots data ! j)"
    using bad family_eq by simp
  have rel:
      "balanced_conditioned_trace_fri_bad_challenge_relation C
        (HashMap t)
        (TraceFriChallenge j final)
        (staged_trace_fri_challenges data ! j)"
    unfolding balanced_conditioned_trace_fri_bad_challenge_relation_def Let_def
    apply (intro conjI)
     apply (rule clean_map)
     apply (rule no_initial_map)
    apply (rule exI[where x="staged_trace_root data"])
    apply (rule exI[where x="staged_trace_fri_roots data"])
    apply (rule exI[where x=final])
    apply (rule exI[where x=j])
    using prefixes j_bound chain_map bad_map
    by simp
  have active:
      "hash_state_relation_active
        (balanced_conditioned_trace_fri_bad_challenge_relation C)
        (HashMap t)
        (TraceFriChallenge j final)
        (staged_trace_fri_challenges data ! j)"
    unfolding hash_state_relation_active_def using lookup rel by blast
  show ?thesis
    using active by blast
qed


lemma checked_builder_composition_balanced_online_bad_imp_conditioned_relation_active:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision t"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values t"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and hit:
      "\<exists>j < length (staged_composition_fri_roots data).
        staged_composition_fri_challenges data ! j \<in>
          fri_online_balanced_bad_challenges
            (to_nat (staged_degree data))
            (length (staged_composition_fri_roots data)) C j t
            (staged_composition_fri_roots data ! j)"
  shows
    "\<exists>x y.
      hash_state_relation_active
        (balanced_conditioned_composition_fri_bad_challenge_relation C)
        (HashMap t) x y"
proof -
  from hit obtain j where
    j_bound: "j < length (staged_composition_fri_roots data)"
    and bad:
      "staged_composition_fri_challenges data ! j \<in>
        fri_online_balanced_bad_challenges
          (to_nat (staged_degree data))
          (length (staged_composition_fri_roots data)) C j t
          (staged_composition_fri_roots data ! j)"
    by blast
  have prefixes:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_alphas data) = length spec \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (Suc (to_nat (staged_degree data))) \<and>
       (\<forall>j < length (staged_composition_fri_roots data). \<exists>final.
         ro_absorb_lookup_chain t (PState adversary_initial_state)
           (composition_fri_challenge_prefix_messages
             (staged_trace_root data)
             (staged_trace_fri_roots data)
             (staged_trace_final data)
             (staged_alphas data)
             (staged_degree data)
             (staged_composition_fri_roots data) j) final \<and>
         fmlookup (HashMap t) (CompositionFriChallenge j final) =
           Some (staged_composition_fri_challenges data ! j))"
    using ro_checked_staged_transcript_program_conditioned_challenge_prefixes[
      OF wf controlled outcome]
    by blast
  from prefixes j_bound obtain final where
    chain:
      "ro_absorb_lookup_chain t (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data) j) final"
    and lookup:
      "fmlookup (HashMap t) (CompositionFriChallenge j final) =
        Some (staged_composition_fri_challenges data ! j)"
    by blast
  have final_map:
      "HashMap (channel_for_hash_map (HashMap t)) = HashMap t"
    unfolding channel_for_hash_map_def adversary_initial_state_def by simp
  have chain_map:
      "ro_absorb_lookup_chain (channel_for_hash_map (HashMap t))
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data) j) final"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule chain)
  have clean_map:
      "\<not> hash_map_output_collision (channel_for_hash_map (HashMap t))"
    using clean final_map unfolding hash_map_output_collision_def by simp
  have no_initial_map:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (HashMap t))"
    using no_initial final_map unfolding hash_map_output_values_def by simp
  have tables:
      "conceptual_table (channel_for_hash_map (HashMap t)) =
        conceptual_table t"
    by (rule ext)+
      (rule conceptual_table_cong_hash_map[OF final_map])
  have family_eq:
      "fri_online_balanced_bad_challenges
          (to_nat (staged_degree data))
          (length (staged_composition_fri_roots data)) C j
          (channel_for_hash_map (HashMap t))
          (staged_composition_fri_roots data ! j) =
        fri_online_balanced_bad_challenges
          (to_nat (staged_degree data))
          (length (staged_composition_fri_roots data)) C j t
          (staged_composition_fri_roots data ! j)"
    unfolding fri_online_balanced_bad_challenges_def tables by simp
  have bad_map:
      "staged_composition_fri_challenges data ! j \<in>
        fri_online_balanced_bad_challenges
          (to_nat (staged_degree data))
          (length (staged_composition_fri_roots data)) C j
          (channel_for_hash_map (HashMap t))
          (staged_composition_fri_roots data ! j)"
    using bad family_eq by simp
  have rel:
      "balanced_conditioned_composition_fri_bad_challenge_relation C
        (HashMap t)
        (CompositionFriChallenge j final)
        (staged_composition_fri_challenges data ! j)"
    unfolding
      balanced_conditioned_composition_fri_bad_challenge_relation_def Let_def
    apply (intro conjI)
     apply (rule clean_map)
     apply (rule no_initial_map)
    apply (rule exI[where x="staged_trace_root data"])
    apply (rule exI[where x="staged_trace_fri_roots data"])
    apply (rule exI[where x="staged_trace_final data"])
    apply (rule exI[where x="staged_alphas data"])
    apply (rule exI[where x="staged_degree data"])
    apply (rule exI[where x="staged_composition_fri_roots data"])
    apply (rule exI[where x=final])
    apply (rule exI[where x=j])
    using prefixes degree_bound j_bound chain_map bad_map
    by simp
  have active:
      "hash_state_relation_active
        (balanced_conditioned_composition_fri_bad_challenge_relation C)
        (HashMap t)
        (CompositionFriChallenge j final)
        (staged_composition_fri_challenges data ! j)"
    unfolding hash_state_relation_active_def using lookup rel by blast
  show ?thesis
    using active by blast
qed


lemma checked_builder_trace_balanced_online_bad_imp_bounded_relation_transition:
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
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values attacker_state"
    and hit:
      "\<exists>j < length (staged_trace_fri_roots data).
        staged_trace_fri_challenges data ! j \<in>
          fri_online_balanced_bad_challenges
            (clength - 1) (length (staged_trace_fri_roots data)) C j
            attacker_state (staged_trace_fri_roots data ! j)"
  shows
    "hash_state_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (balanced_conditioned_trace_fri_bad_challenge_relation C))
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have active:
      "\<exists>x y.
        hash_state_relation_active
          (balanced_conditioned_trace_fri_bad_challenge_relation C)
          (HashMap attacker_state) x y"
    by (rule
      checked_builder_trace_balanced_online_bad_imp_conditioned_relation_active[
        OF wf controlled original_out clean no_initial hit])
  have domain:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds[
        OF wf controlled outcome clean])
  show ?thesis
    by (rule conditioned_relation_active_imp_bounded_initial_transition[
      OF active domain])
qed

lemma checked_builder_composition_balanced_online_bad_imp_bounded_relation_transition:
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
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values attacker_state"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and hit:
      "\<exists>j < length (staged_composition_fri_roots data).
        staged_composition_fri_challenges data ! j \<in>
          fri_online_balanced_bad_challenges
            (to_nat (staged_degree data))
            (length (staged_composition_fri_roots data)) C j
            attacker_state
            (staged_composition_fri_roots data ! j)"
  shows
    "hash_state_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (balanced_conditioned_composition_fri_bad_challenge_relation C))
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have active:
      "\<exists>x y.
        hash_state_relation_active
          (balanced_conditioned_composition_fri_bad_challenge_relation C)
          (HashMap attacker_state) x y"
    by (rule
      checked_builder_composition_balanced_online_bad_imp_conditioned_relation_active[
        OF wf controlled original_out clean no_initial degree_bound hit])
  have domain:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds[
        OF wf controlled outcome clean])
  show ?thesis
    by (rule conditioned_relation_active_imp_bounded_initial_transition[
      OF active domain])
qed

end
end
