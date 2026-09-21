theory Soundness_FRI_Correlated_Agreement_Challenge_Relations
  imports
    Soundness_FRI_Correlated_Agreement_Parameter_Gate
    Soundness_FRI_Conditioned_Challenge_Relation
begin

section \<open>Evolving correlated-agreement challenge targets\<close>
text \<open>
  These auxiliary targets use the existing conceptual tables and absorbed
  prefixes. Challenge-key insertion leaves them unchanged; other inserts can
  activate old keys only through the existing drift targets. Collision and
  initial-target complements remain internal event conditions, not new locale or
  public premises.
\<close>

context soundness
begin

lemma fri_mca_online_trace_challenge_update[simp]:
 "fri_mca_online_bad_challenges d t i
    (channel_for_hash_map (fmupd (TraceFriChallenge c ast) y M)) rt =
  fri_mca_online_bad_challenges d t i (channel_for_hash_map M) rt"
 unfolding fri_mca_online_bad_challenges_def by simp

lemma fri_mca_online_composition_challenge_update[simp]:
 "fri_mca_online_bad_challenges d t i
    (channel_for_hash_map (fmupd (CompositionFriChallenge c ast) y M)) rt =
  fri_mca_online_bad_challenges d t i (channel_for_hash_map M) rt"
 unfolding fri_mca_online_bad_challenges_def by simp

lemma fri_mca_quarter_radii_le_initial:
 "fri_mca_quarter_radii i \<le> fri_mca_quarter_radii 0"
 unfolding fri_mca_quarter_radii_def fri_canonical_domain_at_length
 apply (simp only: power_Suc power_0 mult_1_right div_mult2_eq)
 by (rule div_le_mono) simp

definition fri_mca_direct_cap :: nat
where "fri_mca_direct_cap = max 1 (2*fri_mca_quarter_radii 0)"

lemma fri_mca_online_uniform_card:
 assumes ep: "clength*scale=2^N" and count: "m=ceil_log (Suc d)"
   and fit: "Suc m\<le>N" and rate: "4*fri_padded_degree_bound d\<le>clength*scale"
   and active: "i<m"
 shows "card (fri_mca_online_bad_challenges d (fri_mca_quarter_radii i) i state rt)
     \<le> fri_mca_direct_cap"
proof -
 have local: "card (fri_mca_online_bad_challenges d (fri_mca_quarter_radii i) i state rt)
     \<le> max 1 (2*fri_mca_quarter_radii i)"
   by (rule fri_mca_quarter_layer_card[OF ep _ _ rate]) (use active fit count in auto)
 also have "... \<le> fri_mca_direct_cap"
   using fri_mca_quarter_radii_le_initial[of i] unfolding fri_mca_direct_cap_def by simp
 finally show ?thesis .
qed

definition mca_conditioned_trace_fri_bad_challenge_relation
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
    'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "mca_conditioned_trace_fri_bad_challenge_relation M x y \<longleftrightarrow>
    (let s = channel_for_hash_map M in
      \<not> hash_map_output_collision s \<and>
      PState adversary_initial_state \<notin> hash_map_output_values s \<and>
      (\<exists>fr roots final j.
        length roots = ceil_log clength \<and>
        j < length roots \<and>
        ro_absorb_lookup_chain s (PState adversary_initial_state)
          (fr # take (Suc j) roots) final \<and>
        x = TraceFriChallenge j final \<and>
        y \<in> fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j s (roots ! j)))"

lemma mca_conditioned_trace_fri_bad_challenge_relationD:
  assumes rel:
    "mca_conditioned_trace_fri_bad_challenge_relation M x y"
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
    "y \<in> fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j
      (channel_for_hash_map M) (roots ! j)"
  using rel
  unfolding mca_conditioned_trace_fri_bad_challenge_relation_def Let_def
  by blast




lemma mca_conditioned_trace_fri_bad_challenge_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "mca_conditioned_trace_fri_bad_challenge_relation
        (fmupd x y M) k z"
    and no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows "mca_conditioned_trace_fri_bad_challenge_relation M k z"
proof -
  from mca_conditioned_trace_fri_bad_challenge_relationD[OF rel]
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
      "z \<in> fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j
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
      "fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j
          (channel_for_hash_map (fmupd x y M)) (roots ! j) =
        fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j
          (channel_for_hash_map M) (roots ! j)"
    unfolding fri_mca_online_bad_challenges_def
    using table_eq by simp
  have z_bad_old:
      "z \<in> fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j
        (channel_for_hash_map M) (roots ! j)"
    using z_bad_new family_eq by simp
  show ?thesis
    unfolding mca_conditioned_trace_fri_bad_challenge_relation_def Let_def
    using clean_old no_initial_old roots_len j_bound chain_old
      k_eq z_bad_old
    by blast
qed



lemma mca_conditioned_trace_fri_bad_challenge_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        (mca_conditioned_trace_fri_bad_challenge_relation) M x y"
  shows "y \<in> conditioned_fri_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        (mca_conditioned_trace_fri_bad_challenge_relation)
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        (mca_conditioned_trace_fri_bad_challenge_relation) M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "mca_conditioned_trace_fri_bad_challenge_relation
        (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def
    by blast+
  have rel_old:
      "mca_conditioned_trace_fri_bad_challenge_relation M k z"
    by (rule
      mca_conditioned_trace_fri_bad_challenge_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
      "hash_state_relation_active
        (mca_conditioned_trace_fri_bad_challenge_relation) M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed

lemma mca_conditioned_trace_fri_bad_challenge_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        (mca_conditioned_trace_fri_bad_challenge_relation) M x y}
      \<le> 7 * card (fmdom' M) + 2"
proof -
  have subset:
      "{y.
        hash_state_relation_drift_activation
          (mca_conditioned_trace_fri_bad_challenge_relation) M x y}
        \<subseteq> conditioned_fri_relation_drift_targets M x"
    using
      mca_conditioned_trace_fri_bad_challenge_relation_drift_activation_imp_target[
        OF fresh]
    by blast
  have
      "card {y.
        hash_state_relation_drift_activation
          (mca_conditioned_trace_fri_bad_challenge_relation) M x y}
        \<le> card (conditioned_fri_relation_drift_targets M x)"
    by (rule card_mono[
      OF finite_conditioned_fri_relation_drift_targets subset])
  also have "... \<le> 7 * card (fmdom' M) + 2"
    by (rule card_conditioned_fri_relation_drift_targets_le)
  finally show ?thesis .
qed

definition mca_conditioned_composition_fri_bad_challenge_relation
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "mca_conditioned_composition_fri_bad_challenge_relation M x y \<longleftrightarrow>
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
        y \<in> fri_mca_online_bad_challenges (to_nat dg) (fri_mca_quarter_radii j) j s (roots ! j)))"

lemma mca_conditioned_composition_fri_bad_challenge_relationD:
  assumes rel:
    "mca_conditioned_composition_fri_bad_challenge_relation M x y"
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
    "y \<in> fri_mca_online_bad_challenges (to_nat dg) (fri_mca_quarter_radii j) j
      (channel_for_hash_map M) (roots ! j)"
  using rel
  unfolding mca_conditioned_composition_fri_bad_challenge_relation_def
    Let_def
  by blast



lemma
  mca_conditioned_composition_fri_bad_challenge_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "mca_conditioned_composition_fri_bad_challenge_relation
        (fmupd x y M) k z"
    and no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows "mca_conditioned_composition_fri_bad_challenge_relation M k z"
proof -
  from mca_conditioned_composition_fri_bad_challenge_relationD[OF rel]
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
      "z \<in> fri_mca_online_bad_challenges (to_nat dg) (fri_mca_quarter_radii j) j
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
      "fri_mca_online_bad_challenges (to_nat dg) (fri_mca_quarter_radii j) j
          (channel_for_hash_map (fmupd x y M)) (roots ! j) =
        fri_mca_online_bad_challenges (to_nat dg) (fri_mca_quarter_radii j) j
          (channel_for_hash_map M) (roots ! j)"
    unfolding fri_mca_online_bad_challenges_def
    using table_eq by simp
  have z_bad_old:
      "z \<in> fri_mca_online_bad_challenges (to_nat dg) (fri_mca_quarter_radii j) j
        (channel_for_hash_map M) (roots ! j)"
    using z_bad_new family_eq by simp
  show ?thesis
    unfolding
      mca_conditioned_composition_fri_bad_challenge_relation_def Let_def
    using clean_old no_initial_old trace_len alpha_len degree_bound
      roots_len j_bound chain_old k_eq z_bad_old
    by blast
qed


lemma
  mca_conditioned_composition_fri_bad_challenge_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        (mca_conditioned_composition_fri_bad_challenge_relation)
        M x y"
  shows "y \<in> conditioned_fri_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        (mca_conditioned_composition_fri_bad_challenge_relation)
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        (mca_conditioned_composition_fri_bad_challenge_relation) M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "mca_conditioned_composition_fri_bad_challenge_relation
        (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def
    by blast+
  have rel_old:
      "mca_conditioned_composition_fri_bad_challenge_relation M k z"
    by (rule
      mca_conditioned_composition_fri_bad_challenge_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
      "hash_state_relation_active
        (mca_conditioned_composition_fri_bad_challenge_relation) M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed

lemma mca_conditioned_composition_fri_bad_challenge_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        (mca_conditioned_composition_fri_bad_challenge_relation)
        M x y}
      \<le> 7 * card (fmdom' M) + 2"
proof -
  have subset:
      "{y.
        hash_state_relation_drift_activation
          (mca_conditioned_composition_fri_bad_challenge_relation)
          M x y}
        \<subseteq> conditioned_fri_relation_drift_targets M x"
    using
      mca_conditioned_composition_fri_bad_challenge_relation_drift_activation_imp_target[
        OF fresh]
    by blast
  have
      "card {y.
        hash_state_relation_drift_activation
          (mca_conditioned_composition_fri_bad_challenge_relation)
          M x y}
        \<le> card (conditioned_fri_relation_drift_targets M x)"
    by (rule card_mono[
      OF finite_conditioned_fri_relation_drift_targets subset])
  also have "... \<le> 7 * card (fmdom' M) + 2"
    by (rule card_conditioned_fri_relation_drift_targets_le)
  finally show ?thesis .
qed

end
end
