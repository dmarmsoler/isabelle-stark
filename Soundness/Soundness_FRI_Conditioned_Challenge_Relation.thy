theory Soundness_FRI_Conditioned_Challenge_Relation
  imports
    Stark.Soundness_FRI_Conditioned_Actual_Bridge
    Stark.Soundness_FRI_RO_Actual_Query_Trace_Composition_Adaptive_Query_Budget
begin

context soundness
begin

definition conditioned_trace_fri_bad_challenge_relation
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "conditioned_trace_fri_bad_challenge_relation M x y \<longleftrightarrow>
    (let s = channel_for_hash_map M in
      \<not> hash_map_output_collision s \<and>
      PState adversary_initial_state \<notin> hash_map_output_values s \<and>
      (\<exists>fr roots final j.
        length roots = ceil_log clength \<and>
        j < length roots \<and>
        ro_absorb_lookup_chain s (PState adversary_initial_state)
          (fr # take (Suc j) roots) final \<and>
        x = TraceFriChallenge j final \<and>
        y \<in> fri_online_bad_challenges (clength - 1) j s (roots ! j)))"

lemma conditioned_trace_fri_bad_challenge_relationD:
  assumes rel: "conditioned_trace_fri_bad_challenge_relation M x y"
  obtains fr roots final j where
    "\<not> hash_map_output_collision (channel_for_hash_map M)"
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
    "length roots = ceil_log clength"
    "j < length roots"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state) (fr # take (Suc j) roots) final"
    "x = TraceFriChallenge j final"
    "y \<in> fri_online_bad_challenges (clength - 1) j
      (channel_for_hash_map M) (roots ! j)"
  using rel
  unfolding conditioned_trace_fri_bad_challenge_relation_def Let_def
  by blast

lemma ro_absorb_lookup_chain_trace_fri_challenge_update[simp]:
  "ro_absorb_lookup_chain
      (channel_for_hash_map (fmupd (TraceFriChallenge c ast) y M))
      st xs final \<longleftrightarrow>
    ro_absorb_lookup_chain (channel_for_hash_map M) st xs final"
  unfolding channel_for_hash_map_def
proof (induction xs arbitrary: st)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  show ?case
    by (simp add: Cons.IH)
qed

lemma merkle_path_bound_trace_fri_challenge_update[simp]:
  "merkle_path_bound rt len idx v path
      (channel_for_hash_map (fmupd (TraceFriChallenge c st) y M)) =
    merkle_path_bound rt len idx v path (channel_for_hash_map M)"
  unfolding channel_for_hash_map_def
  by (induction path arbitrary: rt len idx v) auto

lemma authenticated_opening_in_trace_fri_challenge_update[simp]:
  "authenticated_opening_in
      (channel_for_hash_map (fmupd (TraceFriChallenge c st) y M)) opening =
    authenticated_opening_in (channel_for_hash_map M) opening"
  unfolding authenticated_opening_in_def by simp

lemma authenticated_value_at_trace_fri_challenge_update[simp]:
  "authenticated_value_at
      (channel_for_hash_map (fmupd (TraceFriChallenge c st) y M))
      r len i v =
    authenticated_value_at (channel_for_hash_map M) r len i v"
  unfolding authenticated_value_at_def by simp

lemma conceptual_opening_value_trace_fri_challenge_update[simp]:
  "conceptual_opening_value
      (channel_for_hash_map (fmupd (TraceFriChallenge c ast) y M))
      r len i =
    conceptual_opening_value (channel_for_hash_map M) r len i"
  unfolding conceptual_opening_value_def
  by (rule arg_cong[where f=The])
    (rule ext, simp)

lemma conceptual_table_trace_fri_challenge_update[simp]:
  fixes fri_root :: 'f
    and len :: nat
  shows
    "conceptual_table
        (channel_for_hash_map (fmupd (TraceFriChallenge c ast) y M))
        fri_root len =
      conceptual_table (channel_for_hash_map M) fri_root len"
  unfolding conceptual_table_def by simp

lemma fri_online_bad_challenges_trace_fri_challenge_update[simp]:
  fixes fri_root :: 'f
  shows
    "fri_online_bad_challenges d i
        (channel_for_hash_map (fmupd (TraceFriChallenge c ast) y M))
        fri_root =
      fri_online_bad_challenges d i (channel_for_hash_map M) fri_root"
  unfolding fri_online_bad_challenges_def fri_online_conceptual_layer_def
  by simp

lemma conditioned_trace_fri_bad_challenge_relation_direct_fiber_card_bound:
  "card {y.
      hash_state_relation_direct_activation
        conditioned_trace_fri_bad_challenge_relation M x y} \<le> 1"
proof (cases "{y.
    hash_state_relation_direct_activation
      conditioned_trace_fri_bad_challenge_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
    "hash_state_relation_direct_activation
      conditioned_trace_fri_bad_challenge_relation M x y0"
    by blast
  have rel0:
      "conditioned_trace_fri_bad_challenge_relation (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from conditioned_trace_fri_bad_challenge_relationD[OF rel0]
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
      "y0 \<in> fri_online_bad_challenges (clength - 1) j0
        (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
    .
  let ?B =
    "fri_online_bad_challenges (clength - 1) j0
      (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          conditioned_trace_fri_bad_challenge_relation M x y} \<subseteq> ?B"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          conditioned_trace_fri_bad_challenge_relation M x y}"
    have rel:
        "conditioned_trace_fri_bad_challenge_relation (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from conditioned_trace_fri_bad_challenge_relationD[OF rel]
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
        "y \<in> fri_online_bad_challenges (clength - 1) j
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
      using y_bad j_eq root_eq unfolding x_eq0
      by simp
  qed
  have finite_B: "finite ?B"
    by simp
  have "card {y.
      hash_state_relation_direct_activation
        conditioned_trace_fri_bad_challenge_relation M x y}
      \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  also have "... \<le> 1"
    by (rule card_fri_online_bad_challenges_le_one)
  finally show ?thesis .
qed

definition trace_fri_challenge_state_values
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow> 'f set"
where
  "trace_fri_challenge_state_values M =
    {st. \<exists>c out. fmlookup M (TraceFriChallenge c st) = Some out}"

definition composition_fri_challenge_state_values
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow> 'f set"
where
  "composition_fri_challenge_state_values M =
    {st. \<exists>c out. fmlookup M (CompositionFriChallenge c st) = Some out}"

definition conditioned_fri_relation_drift_targets
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f set"
where
  "conditioned_fri_relation_drift_targets M x =
    first_root_relation_drift_targets M x \<union>
    trace_fri_challenge_state_values M \<union>
    composition_fri_challenge_state_values M"

lemma trace_fri_challenge_state_values_subset_image:
  "trace_fri_challenge_state_values M \<subseteq>
    Set.image
      (\<lambda>k. case k of TraceFriChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
      (fmdom' M)"
  unfolding trace_fri_challenge_state_values_def
proof
  fix st
  assume "st \<in> {st. \<exists>c out.
    fmlookup M (TraceFriChallenge c st) = Some out}"
  then obtain c out where lookup:
      "fmlookup M (TraceFriChallenge c st) = Some out"
    by blast
  have dom: "TraceFriChallenge c st \<in> fmdom' M"
    using lookup by (simp add: fmlookup_dom'_iff)
  show "st \<in> Set.image
    (\<lambda>k. case k of TraceFriChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
    (fmdom' M)"
    by (rule image_eqI[OF _ dom]) simp
qed

lemma composition_fri_challenge_state_values_subset_image:
  "composition_fri_challenge_state_values M \<subseteq>
    Set.image
      (\<lambda>k. case k of CompositionFriChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
      (fmdom' M)"
  unfolding composition_fri_challenge_state_values_def
proof
  fix st
  assume "st \<in> {st. \<exists>c out.
    fmlookup M (CompositionFriChallenge c st) = Some out}"
  then obtain c out where lookup:
      "fmlookup M (CompositionFriChallenge c st) = Some out"
    by blast
  have dom: "CompositionFriChallenge c st \<in> fmdom' M"
    using lookup by (simp add: fmlookup_dom'_iff)
  show "st \<in> Set.image
    (\<lambda>k. case k of CompositionFriChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
    (fmdom' M)"
    by (rule image_eqI[OF _ dom]) simp
qed

lemma finite_trace_fri_challenge_state_values[simp]:
  "finite (trace_fri_challenge_state_values M)"
  by (rule finite_subset[OF trace_fri_challenge_state_values_subset_image])
    simp

lemma finite_composition_fri_challenge_state_values[simp]:
  "finite (composition_fri_challenge_state_values M)"
  by (rule finite_subset[
      OF composition_fri_challenge_state_values_subset_image])
    simp

lemma card_trace_fri_challenge_state_values_le:
  "card (trace_fri_challenge_state_values M) \<le> card (fmdom' M)"
proof -
  have "card (trace_fri_challenge_state_values M) \<le>
      card (Set.image
        (\<lambda>k. case k of TraceFriChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
        (fmdom' M))"
    apply (rule card_mono)
     apply simp
    by (rule trace_fri_challenge_state_values_subset_image)
  also have "... \<le> card (fmdom' M)"
    by (rule card_image_le) simp
  finally show ?thesis .
qed

lemma card_composition_fri_challenge_state_values_le:
  "card (composition_fri_challenge_state_values M) \<le> card (fmdom' M)"
proof -
  have "card (composition_fri_challenge_state_values M) \<le>
      card (Set.image
        (\<lambda>k. case k of CompositionFriChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
        (fmdom' M))"
    apply (rule card_mono)
     apply simp
    by (rule composition_fri_challenge_state_values_subset_image)
  also have "... \<le> card (fmdom' M)"
    by (rule card_image_le) simp
  finally show ?thesis .
qed

lemma finite_conditioned_fri_relation_drift_targets[simp]:
  "finite (conditioned_fri_relation_drift_targets M x)"
  unfolding conditioned_fri_relation_drift_targets_def by simp

lemma card_conditioned_fri_relation_drift_targets_le:
  "card (conditioned_fri_relation_drift_targets M x)
    \<le> 7 * card (fmdom' M) + 2"
proof -
  let ?A = "first_root_relation_drift_targets M x"
  let ?B = "trace_fri_challenge_state_values M"
  let ?C = "composition_fri_challenge_state_values M"
  have union_le:
      "card (conditioned_fri_relation_drift_targets M x)
        \<le> card ?A + card ?B + card ?C"
    unfolding conditioned_fri_relation_drift_targets_def
    by (rule order_trans[OF card_Un_le])
      (use card_Un_le[of ?A ?B] in linarith)
  show ?thesis
    by (rule order_trans[OF union_le])
      (use card_first_root_relation_drift_targets_le[of M x]
        card_trace_fri_challenge_state_values_le[of M]
        card_composition_fri_challenge_state_values_le[of M]
        in linarith)
qed

lemma trace_fri_challenge_lookup_state_value:
  assumes "fmlookup M (TraceFriChallenge c st) = Some out"
  shows "st \<in> trace_fri_challenge_state_values M"
  using assms unfolding trace_fri_challenge_state_values_def by blast

lemma composition_fri_challenge_lookup_state_value:
  assumes "fmlookup M (CompositionFriChallenge c st) = Some out"
  shows "st \<in> composition_fri_challenge_state_values M"
  using assms unfolding composition_fri_challenge_state_values_def by blast

lemma ro_absorb_lookup_chain_conditioned_fri_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and chain:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        start messages final"
    and final_target:
      "final \<in> trace_fri_challenge_state_values M \<union>
        composition_fri_challenge_state_values M"
    and no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      start messages final"
  using chain
proof (induction messages arbitrary: start)
  case Nil
  then show ?case by simp
next
  case (Cons msg messages)
  from Cons.prems obtain nxt where
    lookup:
      "fmlookup (fmupd x y M)
        (TranscriptAbsorb start msg) = Some nxt"
    and tail:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        nxt messages final"
    unfolding channel_for_hash_map_def by auto
  have key_neq: "TranscriptAbsorb start msg \<noteq> x"
  proof
    assume key_eq: "TranscriptAbsorb start msg = x"
    have nxt_eq: "nxt = y"
      using lookup key_eq by simp
    show False
    proof (cases messages)
      case Nil
      have final_eq: "final = y"
        using tail nxt_eq Nil by simp
      have "y \<in> conditioned_fri_relation_drift_targets M x"
        using final_target final_eq
        unfolding conditioned_fri_relation_drift_targets_def by blast
      then show False using no_target by contradiction
    next
      case (Cons next_msg rest)
      from tail[unfolded Cons] obtain after where
        next_lookup:
          "fmlookup (fmupd x y M)
            (TranscriptAbsorb nxt next_msg) = Some after"
        unfolding channel_for_hash_map_def by auto
      show False
      proof (cases "TranscriptAbsorb nxt next_msg = x")
        case True
        have x_eq: "x = TranscriptAbsorb nxt next_msg"
          using True by simp
        have "y \<in> hash_input_component_values x"
          using x_eq nxt_eq
          unfolding hash_input_component_values_def by simp
        then have "y \<in> conditioned_fri_relation_drift_targets M x"
          unfolding conditioned_fri_relation_drift_targets_def
            first_root_relation_drift_targets_def
          by blast
        then show False using no_target by contradiction
      next
        case False
        have old_lookup:
          "fmlookup M (TranscriptAbsorb nxt next_msg) = Some after"
          using next_lookup False by simp
        have "y \<in> transcript_absorb_input_values M"
          using transcript_absorb_lookup_input_value[OF old_lookup]
            nxt_eq by simp
        then have "y \<in> conditioned_fri_relation_drift_targets M x"
          unfolding conditioned_fri_relation_drift_targets_def
            first_root_relation_drift_targets_def
          by blast
        then show False using no_target by contradiction
      qed
    qed
  qed
  have lookup_old:
      "fmlookup M (TranscriptAbsorb start msg) = Some nxt"
    using lookup key_neq by simp
  have tail_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        nxt messages final"
    by (rule Cons.IH[OF tail])
  show ?case
    using lookup_old tail_old
    unfolding channel_for_hash_map_def by auto
qed

lemma conditioned_trace_fri_bad_challenge_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "conditioned_trace_fri_bad_challenge_relation (fmupd x y M) k z"
    and no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows "conditioned_trace_fri_bad_challenge_relation M k z"
proof -
  from conditioned_trace_fri_bad_challenge_relationD[OF rel]
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
      "z \<in> fri_online_bad_challenges (clength - 1) j
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
  have z_bad_old:
      "z \<in> fri_online_bad_challenges (clength - 1) j
        (channel_for_hash_map M) (roots ! j)"
    using z_bad_new table_eq
    unfolding fri_online_bad_challenges_def
      fri_online_conceptual_layer_def
    by simp
  show ?thesis
    unfolding conditioned_trace_fri_bad_challenge_relation_def Let_def
    using clean_old no_initial_old roots_len j_bound chain_old
      k_eq z_bad_old
    by blast
qed

lemma conditioned_trace_fri_bad_challenge_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        conditioned_trace_fri_bad_challenge_relation M x y"
  shows "y \<in> conditioned_fri_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        conditioned_trace_fri_bad_challenge_relation
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        conditioned_trace_fri_bad_challenge_relation M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "conditioned_trace_fri_bad_challenge_relation
        (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def
    by blast+
  have rel_old:
      "conditioned_trace_fri_bad_challenge_relation M k z"
    by (rule
      conditioned_trace_fri_bad_challenge_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
      "hash_state_relation_active
        conditioned_trace_fri_bad_challenge_relation M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed

lemma conditioned_trace_fri_bad_challenge_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        conditioned_trace_fri_bad_challenge_relation M x y}
      \<le> 7 * card (fmdom' M) + 2"
proof -
  have subset:
      "{y.
        hash_state_relation_drift_activation
          conditioned_trace_fri_bad_challenge_relation M x y}
        \<subseteq> conditioned_fri_relation_drift_targets M x"
    using
      conditioned_trace_fri_bad_challenge_relation_drift_activation_imp_target[
        OF fresh]
    by blast
  have
      "card {y.
        hash_state_relation_drift_activation
          conditioned_trace_fri_bad_challenge_relation M x y}
        \<le> card (conditioned_fri_relation_drift_targets M x)"
    by (rule card_mono[
      OF finite_conditioned_fri_relation_drift_targets subset])
  also have "... \<le> 7 * card (fmdom' M) + 2"
    by (rule card_conditioned_fri_relation_drift_targets_le)
  finally show ?thesis .
qed

definition conditioned_fri_relation_bounded
  :: "nat \<Rightarrow>
      ((('f protocol_hash_input, 'f) fmap) \<Rightarrow>
        'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
      (('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "conditioned_fri_relation_bounded L R M x y \<longleftrightarrow>
    card (fmdom' M) \<le> L \<and> R M x y"

lemma conditioned_fri_bounded_direct_activation_subset:
  assumes fresh: "fmlookup M x = None"
  shows
    "{y.
      hash_state_relation_direct_activation
        (conditioned_fri_relation_bounded L R) M x y}
      \<subseteq>
     {y. hash_state_relation_direct_activation R M x y}"
proof
  fix y
  assume y:
    "y \<in> {y.
      hash_state_relation_direct_activation
        (conditioned_fri_relation_bounded L R) M x y}"
  have active_new:
      "hash_state_relation_active
        (conditioned_fri_relation_bounded L R)
        (fmupd x y M) x y"
    using y unfolding hash_state_relation_direct_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) x = Some y"
    and bounded_rel_new:
      "conditioned_fri_relation_bounded L R
        (fmupd x y M) x y"
    using active_new unfolding hash_state_relation_active_def by blast+
  have rel_new: "R (fmupd x y M) x y"
    using bounded_rel_new
    unfolding conditioned_fri_relation_bounded_def by blast
  have original_new:
      "hash_state_relation_active R (fmupd x y M) x y"
    unfolding hash_state_relation_active_def
    using lookup_new rel_new by simp
  have original_old:
      "\<not> hash_state_relation_active R M x y"
    using fresh unfolding hash_state_relation_active_def by simp
  show
    "y \<in> {y. hash_state_relation_direct_activation R M x y}"
    unfolding hash_state_relation_direct_activation_def
    using original_new original_old by simp
qed

lemma conditioned_fri_bounded_drift_activation_subset:
  assumes fresh: "fmlookup M x = None"
  shows
    "{y.
      hash_state_relation_drift_activation
        (conditioned_fri_relation_bounded L R) M x y}
      \<subseteq>
     {y. hash_state_relation_drift_activation R M x y}"
proof
  fix y
  assume y:
    "y \<in> {y.
      hash_state_relation_drift_activation
        (conditioned_fri_relation_bounded L R) M x y}"
  then obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        (conditioned_fri_relation_bounded L R)
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        (conditioned_fri_relation_bounded L R) M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and bounded_rel_new:
      "conditioned_fri_relation_bounded L R
        (fmupd x y M) k z"
    using active_new unfolding hash_state_relation_active_def by blast+
  have domain_new: "card (fmdom' (fmupd x y M)) \<le> L"
    and rel_new: "R (fmupd x y M) k z"
    using bounded_rel_new
    unfolding conditioned_fri_relation_bounded_def by blast+
  have domain_old: "card (fmdom' M) \<le> L"
    using card_fmdom_fmupd_mono[of M x y] domain_new by linarith
  have original_new:
      "hash_state_relation_active R (fmupd x y M) k z"
    unfolding hash_state_relation_active_def
    using lookup_new rel_new by simp
  have original_old:
      "\<not> hash_state_relation_active R M k z"
  proof
    assume old: "hash_state_relation_active R M k z"
    have lookup_old: "fmlookup M k = Some z"
      and rel_old: "R M k z"
      using old unfolding hash_state_relation_active_def by blast+
    have bounded_old:
        "conditioned_fri_relation_bounded L R M k z"
      unfolding conditioned_fri_relation_bounded_def
      using domain_old rel_old by simp
    have
        "hash_state_relation_active
          (conditioned_fri_relation_bounded L R) M k z"
      unfolding hash_state_relation_active_def
      using lookup_old bounded_old by simp
    then show False using inactive_old by contradiction
  qed
  show
    "y \<in> {y. hash_state_relation_drift_activation R M x y}"
    unfolding hash_state_relation_drift_activation_def
    using key_neq original_new original_old by blast
qed

lemma conditioned_fri_bounded_transition_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
    and direct:
      "card (fmdom' M) \<le> L \<Longrightarrow>
        card {y. hash_state_relation_direct_activation R M x y} \<le> b"
    and drift:
      "card (fmdom' M) \<le> L \<Longrightarrow>
        card {y. hash_state_relation_drift_activation R M x y} \<le> d"
  shows
    "card {y.
      hash_state_relation_transition
        (conditioned_fri_relation_bounded L R)
        M (fmupd x y M)}
      \<le> b + d"
proof (cases "card (fmdom' M) \<le> L")
  case True
  let ?BD =
    "{y. hash_state_relation_direct_activation
      (conditioned_fri_relation_bounded L R) M x y}"
  let ?D = "{y. hash_state_relation_direct_activation R M x y}"
  have direct_subset: "?BD \<subseteq> ?D"
    by (rule conditioned_fri_bounded_direct_activation_subset[OF fresh])
  have finite_D: "finite ?D" by simp
  have direct_bound: "card ?BD \<le> b"
    by (rule order_trans[OF card_mono[OF finite_D direct_subset]
      direct[OF True]])
  let ?BF =
    "{y. hash_state_relation_drift_activation
      (conditioned_fri_relation_bounded L R) M x y}"
  let ?F = "{y. hash_state_relation_drift_activation R M x y}"
  have drift_subset: "?BF \<subseteq> ?F"
    by (rule conditioned_fri_bounded_drift_activation_subset[OF fresh])
  have finite_F: "finite ?F" by simp
  have drift_bound: "card ?BF \<le> d"
    by (rule order_trans[OF card_mono[OF finite_F drift_subset]
      drift[OF True]])
  show ?thesis
    by (rule hash_state_relation_transition_update_fiber_card_bound[
      OF direct_bound drift_bound])
next
  case False
  have no_active:
      "\<And>y k z.
        \<not> hash_state_relation_active
          (conditioned_fri_relation_bounded L R)
          (fmupd x y M) k z"
  proof
    fix y k z
    assume active_new:
      "hash_state_relation_active
        (conditioned_fri_relation_bounded L R)
        (fmupd x y M) k z"
    have domain_new: "card (fmdom' (fmupd x y M)) \<le> L"
      using active_new
      unfolding hash_state_relation_active_def
        conditioned_fri_relation_bounded_def
      by blast
    have domain_old: "card (fmdom' M) \<le> L"
      using card_fmdom_fmupd_mono[of M x y] domain_new by linarith
    show False using False domain_old by contradiction
  qed
  have
    "{y.
      hash_state_relation_transition
        (conditioned_fri_relation_bounded L R)
        M (fmupd x y M)} = {}"
    unfolding hash_state_relation_transition_def using no_active by auto
  then show ?thesis by simp
qed

lemma conditioned_trace_fri_bounded_transition_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_transition
        (conditioned_fri_relation_bounded L
          conditioned_trace_fri_bad_challenge_relation)
        M (fmupd x y M)}
      \<le> 1 + (7 * L + 2)"
proof (rule conditioned_fri_bounded_transition_fiber_card_bound[
    OF fresh])
  assume "card (fmdom' M) \<le> L"
  show
    "card {y.
      hash_state_relation_direct_activation
        conditioned_trace_fri_bad_challenge_relation M x y} \<le> 1"
    by (rule
      conditioned_trace_fri_bad_challenge_relation_direct_fiber_card_bound)
next
  assume domain: "card (fmdom' M) \<le> L"
  have
    "card {y.
      hash_state_relation_drift_activation
        conditioned_trace_fri_bad_challenge_relation M x y}
      \<le> 7 * card (fmdom' M) + 2"
    by (rule
      conditioned_trace_fri_bad_challenge_relation_drift_fiber_card_bound[
        OF fresh])
  also have "... \<le> 7 * L + 2"
    by (rule add_le_mono[OF mult_left_mono[OF domain] order_refl], simp)
  finally show
    "card {y.
      hash_state_relation_drift_activation
        conditioned_trace_fri_bad_challenge_relation M x y}
      \<le> 7 * L + 2"
    .
qed

lemma
  wp_ro_checked_staged_transcript_with_query_witnesses_conditioned_trace_fri_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded q
          conditioned_trace_fri_bad_challenge_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state
      \<le> nnreal (q * (1 + (7 * q + 2))) / nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B = "1 + (7 * ?Q + 2)"
  have steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition
            (conditioned_fri_relation_bounded ?Q
              conditioned_trace_fri_bad_challenge_relation)
            M (fmupd x y M)}
          \<le> ?B"
    by (rule conditioned_trace_fri_bounded_transition_fiber_card_bound)
  have bound:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (conditioned_fri_relation_bounded ?Q
            conditioned_trace_fri_bad_challenge_relation)
          (HashMap adversary_initial_state))
        adversary_initial_state
        \<le> nnreal (?Q * ?B) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound_all_rounds[
        OF wf controlled steps])
  show ?thesis
    using bound unfolding q_def by simp
qed

lemma ro_absorb_lookup_chain_composition_fri_challenge_update[simp]:
  "ro_absorb_lookup_chain
      (channel_for_hash_map (fmupd (CompositionFriChallenge c ast) y M))
      st xs final \<longleftrightarrow>
    ro_absorb_lookup_chain (channel_for_hash_map M) st xs final"
  unfolding channel_for_hash_map_def
proof (induction xs arbitrary: st)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  show ?case
    by (simp add: Cons.IH)
qed

lemma merkle_path_bound_composition_fri_challenge_update[simp]:
  "merkle_path_bound rt len idx v path
      (channel_for_hash_map (fmupd (CompositionFriChallenge c st) y M)) =
    merkle_path_bound rt len idx v path (channel_for_hash_map M)"
  unfolding channel_for_hash_map_def
  by (induction path arbitrary: rt len idx v) auto

lemma authenticated_opening_in_composition_fri_challenge_update[simp]:
  "authenticated_opening_in
      (channel_for_hash_map
        (fmupd (CompositionFriChallenge c st) y M)) opening =
    authenticated_opening_in (channel_for_hash_map M) opening"
  unfolding authenticated_opening_in_def by simp

lemma authenticated_value_at_composition_fri_challenge_update[simp]:
  "authenticated_value_at
      (channel_for_hash_map
        (fmupd (CompositionFriChallenge c st) y M))
      r len i v =
    authenticated_value_at (channel_for_hash_map M) r len i v"
  unfolding authenticated_value_at_def by simp

lemma conceptual_opening_value_composition_fri_challenge_update[simp]:
  "conceptual_opening_value
      (channel_for_hash_map
        (fmupd (CompositionFriChallenge c ast) y M))
      r len i =
    conceptual_opening_value (channel_for_hash_map M) r len i"
  unfolding conceptual_opening_value_def
  by (rule arg_cong[where f=The])
    (rule ext, simp)

lemma conceptual_table_composition_fri_challenge_update[simp]:
  fixes fri_root :: 'f
    and len :: nat
  shows
    "conceptual_table
        (channel_for_hash_map
          (fmupd (CompositionFriChallenge c ast) y M))
        fri_root len =
      conceptual_table (channel_for_hash_map M) fri_root len"
  unfolding conceptual_table_def by simp

lemma fri_online_bad_challenges_composition_fri_challenge_update[simp]:
  fixes fri_root :: 'f
  shows
    "fri_online_bad_challenges d i
        (channel_for_hash_map
          (fmupd (CompositionFriChallenge c ast) y M))
        fri_root =
      fri_online_bad_challenges d i (channel_for_hash_map M) fri_root"
  unfolding fri_online_bad_challenges_def fri_online_conceptual_layer_def
  by simp

definition composition_fri_challenge_prefix_messages
  :: "'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list"
where
  "composition_fri_challenge_prefix_messages
      fr trace_roots trace_final as dg roots j =
    fr # trace_roots @ [trace_final] @ as @ [dg] @ take (Suc j) roots"

lemma composition_fri_challenge_prefix_messages_degree_roots_eq:
  assumes trace_len:
      "length trace_roots = ceil_log clength"
      "length trace_roots' = ceil_log clength"
    and alpha_len:
      "length as = length spec"
      "length as' = length spec"
    and messages_eq:
      "composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots j =
        composition_fri_challenge_prefix_messages
          fr' trace_roots' trace_final' as' dg' roots' j"
  shows "dg = dg' \<and> take (Suc j) roots = take (Suc j) roots'"
proof -
  let ?k = "2 + ceil_log clength + length spec"
  have suffix:
      "drop ?k
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots j) =
       dg # take (Suc j) roots"
    unfolding composition_fri_challenge_prefix_messages_def
    using trace_len alpha_len by simp
  have suffix':
      "drop ?k
        (composition_fri_challenge_prefix_messages
          fr' trace_roots' trace_final' as' dg' roots' j) =
       dg' # take (Suc j) roots'"
    unfolding composition_fri_challenge_prefix_messages_def
    using trace_len alpha_len by simp
  have suffix_eq:
      "drop ?k
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots j) =
       drop ?k
        (composition_fri_challenge_prefix_messages
          fr' trace_roots' trace_final' as' dg' roots' j)"
    using messages_eq by simp
  show ?thesis
    using suffix suffix' suffix_eq by simp
qed

definition conditioned_composition_fri_bad_challenge_relation
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "conditioned_composition_fri_bad_challenge_relation M x y \<longleftrightarrow>
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
        y \<in> fri_online_bad_challenges (to_nat dg) j s (roots ! j)))"

lemma conditioned_composition_fri_bad_challenge_relationD:
  assumes rel: "conditioned_composition_fri_bad_challenge_relation M x y"
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
    "y \<in> fri_online_bad_challenges (to_nat dg) j
      (channel_for_hash_map M) (roots ! j)"
  using rel
  unfolding conditioned_composition_fri_bad_challenge_relation_def Let_def
  by blast

lemma conditioned_composition_fri_bad_challenge_relation_direct_fiber_card_bound:
  "card {y.
      hash_state_relation_direct_activation
        conditioned_composition_fri_bad_challenge_relation M x y} \<le> 1"
proof (cases "{y.
    hash_state_relation_direct_activation
      conditioned_composition_fri_bad_challenge_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
    "hash_state_relation_direct_activation
      conditioned_composition_fri_bad_challenge_relation M x y0"
    by blast
  have rel0:
      "conditioned_composition_fri_bad_challenge_relation
        (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from conditioned_composition_fri_bad_challenge_relationD[OF rel0]
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
    and roots_len0: "length roots0 = ceil_log (Suc (to_nat dg0))"
    and j_bound0: "j0 < length roots0"
    and chain0:
      "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr0 trace_roots0 trace_final0 as0 dg0 roots0 j0) final0"
    and x_eq0: "x = CompositionFriChallenge j0 final0"
    and y0_bad:
      "y0 \<in> fri_online_bad_challenges (to_nat dg0) j0
        (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
    .
  let ?B =
    "fri_online_bad_challenges (to_nat dg0) j0
      (channel_for_hash_map (fmupd x y0 M)) (roots0 ! j0)"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          conditioned_composition_fri_bad_challenge_relation M x y} \<subseteq> ?B"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          conditioned_composition_fri_bad_challenge_relation M x y}"
    have rel:
        "conditioned_composition_fri_bad_challenge_relation
          (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from conditioned_composition_fri_bad_challenge_relationD[OF rel]
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
      and roots_len: "length roots = ceil_log (Suc (to_nat dg))"
      and j_bound: "j < length roots"
      and chain:
        "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
          (PState adversary_initial_state)
          (composition_fri_challenge_prefix_messages
            fr trace_roots trace_final as dg roots j) final"
      and x_eq: "x = CompositionFriChallenge j final"
      and y_bad:
        "y \<in> fri_online_bad_challenges (to_nat dg) j
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
      using y_bad j_eq degree_eq root_eq unfolding x_eq0
      by simp
  qed
  have finite_B: "finite ?B"
    by simp
  have "card {y.
      hash_state_relation_direct_activation
        conditioned_composition_fri_bad_challenge_relation M x y}
      \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  also have "... \<le> 1"
    by (rule card_fri_online_bad_challenges_le_one)
  finally show ?thesis .
qed

lemma
  conditioned_composition_fri_bad_challenge_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "conditioned_composition_fri_bad_challenge_relation
        (fmupd x y M) k z"
    and no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows "conditioned_composition_fri_bad_challenge_relation M k z"
proof -
  from conditioned_composition_fri_bad_challenge_relationD[OF rel]
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
      "z \<in> fri_online_bad_challenges (to_nat dg) j
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
  have z_bad_old:
      "z \<in> fri_online_bad_challenges (to_nat dg) j
        (channel_for_hash_map M) (roots ! j)"
    using z_bad_new table_eq
    unfolding fri_online_bad_challenges_def
      fri_online_conceptual_layer_def
    by simp
  show ?thesis
    unfolding
      conditioned_composition_fri_bad_challenge_relation_def Let_def
    using clean_old no_initial_old trace_len alpha_len degree_bound
      roots_len j_bound chain_old k_eq z_bad_old
    by blast
qed

lemma
  conditioned_composition_fri_bad_challenge_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        conditioned_composition_fri_bad_challenge_relation M x y"
  shows "y \<in> conditioned_fri_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        conditioned_composition_fri_bad_challenge_relation
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        conditioned_composition_fri_bad_challenge_relation M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "conditioned_composition_fri_bad_challenge_relation
        (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def
    by blast+
  have rel_old:
      "conditioned_composition_fri_bad_challenge_relation M k z"
    by (rule
      conditioned_composition_fri_bad_challenge_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
      "hash_state_relation_active
        conditioned_composition_fri_bad_challenge_relation M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed

lemma conditioned_composition_fri_bad_challenge_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        conditioned_composition_fri_bad_challenge_relation M x y}
      \<le> 7 * card (fmdom' M) + 2"
proof -
  have subset:
      "{y.
        hash_state_relation_drift_activation
          conditioned_composition_fri_bad_challenge_relation M x y}
        \<subseteq> conditioned_fri_relation_drift_targets M x"
    using
      conditioned_composition_fri_bad_challenge_relation_drift_activation_imp_target[
        OF fresh]
    by blast
  have
      "card {y.
        hash_state_relation_drift_activation
          conditioned_composition_fri_bad_challenge_relation M x y}
        \<le> card (conditioned_fri_relation_drift_targets M x)"
    by (rule card_mono[
      OF finite_conditioned_fri_relation_drift_targets subset])
  also have "... \<le> 7 * card (fmdom' M) + 2"
    by (rule card_conditioned_fri_relation_drift_targets_le)
  finally show ?thesis .
qed

lemma conditioned_composition_fri_bounded_transition_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_transition
        (conditioned_fri_relation_bounded L
          conditioned_composition_fri_bad_challenge_relation)
        M (fmupd x y M)}
      \<le> 1 + (7 * L + 2)"
proof (rule conditioned_fri_bounded_transition_fiber_card_bound[
    OF fresh])
  assume "card (fmdom' M) \<le> L"
  show
    "card {y.
      hash_state_relation_direct_activation
        conditioned_composition_fri_bad_challenge_relation M x y} \<le> 1"
    by (rule
      conditioned_composition_fri_bad_challenge_relation_direct_fiber_card_bound)
next
  assume domain: "card (fmdom' M) \<le> L"
  have
    "card {y.
      hash_state_relation_drift_activation
        conditioned_composition_fri_bad_challenge_relation M x y}
      \<le> 7 * card (fmdom' M) + 2"
    by (rule
      conditioned_composition_fri_bad_challenge_relation_drift_fiber_card_bound[
        OF fresh])
  also have "... \<le> 7 * L + 2"
    by (rule add_le_mono[OF mult_left_mono[OF domain] order_refl], simp)
  finally show
    "card {y.
      hash_state_relation_drift_activation
        conditioned_composition_fri_bad_challenge_relation M x y}
      \<le> 7 * L + 2"
    .
qed

lemma
  wp_ro_checked_staged_transcript_with_query_witnesses_conditioned_composition_fri_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded q
          conditioned_composition_fri_bad_challenge_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state
      \<le> nnreal (q * (1 + (7 * q + 2))) / nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B = "1 + (7 * ?Q + 2)"
  have steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition
            (conditioned_fri_relation_bounded ?Q
              conditioned_composition_fri_bad_challenge_relation)
            M (fmupd x y M)}
          \<le> ?B"
    by (rule
      conditioned_composition_fri_bounded_transition_fiber_card_bound)
  have bound:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (conditioned_fri_relation_bounded ?Q
            conditioned_composition_fri_bad_challenge_relation)
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