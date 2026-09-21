theory Soundness_FRI_Conditioned_Prequery_Drift_Base
  imports Stark.Soundness_FRI_Conditioned_Prequery_Dual_Relation
begin

context soundness
begin

lemma hash_map_clean_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and clean_new:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
  shows "\<not> hash_map_output_collision (channel_for_hash_map M)"
proof
  assume collision_old:
    "hash_map_output_collision (channel_for_hash_map M)"
  have ext:
      "channel_for_hash_map M \<le>
        channel_for_hash_map (fmupd x y M)"
    by (rule channel_for_hash_map_fresh_update_extends[OF fresh])
  have
    "hash_map_output_collision
      (channel_for_hash_map (fmupd x y M))"
    by (rule hash_map_output_collision_mono[OF collision_old ext])
  then show False using clean_new by contradiction
qed

lemma hash_map_no_initial_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and no_initial_new:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
  shows
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
        hash_map_output_values
          (channel_for_hash_map (fmupd x y M))"
  proof (rule hash_map_output_valuesI)
    show
      "fmlookup
        (HashMap (channel_for_hash_map (fmupd x y M))) q =
        Some (PState adversary_initial_state)"
      using q_lookup_new unfolding channel_for_hash_map_def by simp
  qed
  then show False using no_initial_new by contradiction
qed

lemma fri_conditioned_quantitative_residual_query_lists_at_value_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and roots_target:
      "set roots \<subseteq> transcript_absorb_message_values M"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows
    "fri_conditioned_quantitative_residual_query_lists_at_value d roots b
        final_value (channel_for_hash_map (fmupd x y M)) i =
      fri_conditioned_quantitative_residual_query_lists_at_value d roots b
        final_value (channel_for_hash_map M) i"
proof -
  have layers:
      "fri_builder_conceptual_layers roots
          (channel_for_hash_map (fmupd x y M)) final_value =
        fri_builder_conceptual_layers roots
          (channel_for_hash_map M) final_value"
    by (rule fri_builder_conceptual_layers_fresh_update[
      OF fresh roots_target no_target])
  show ?thesis
    unfolding
      fri_conditioned_quantitative_residual_query_lists_at_value_def
    using layers by simp
qed

lemma fri_conditioned_quantitative_degenerate_query_lists_at_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and roots_target:
      "set roots \<subseteq> transcript_absorb_message_values M"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows
    "fri_conditioned_quantitative_degenerate_query_lists_at d roots
        final_value (channel_for_hash_map (fmupd x y M)) i round_idx =
      fri_conditioned_quantitative_degenerate_query_lists_at d roots
        final_value (channel_for_hash_map M) i round_idx"
proof -
  have layers:
      "fri_builder_conceptual_layers roots
          (channel_for_hash_map (fmupd x y M)) final_value =
        fri_builder_conceptual_layers roots
          (channel_for_hash_map M) final_value"
    by (rule fri_builder_conceptual_layers_fresh_update[
      OF fresh roots_target no_target])
  show ?thesis
    unfolding
      fri_conditioned_quantitative_degenerate_query_lists_at_def
    using layers by simp
qed



lemma ro_conditioned_trace_challenge_evidence_at_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and evidence:
      "ro_conditioned_trace_challenge_evidence_at
        (fmupd x y M) fr roots i b"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
    and not_key: "\<And>c st. x \<noteq> TraceFriChallenge c st"
  shows "ro_conditioned_trace_challenge_evidence_at M fr roots i b"
proof -
  from evidence obtain final where
    i_bound: "i < length roots"
    and chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (fr # take (Suc i) roots) final"
    and lookup_new:
      "fmlookup (fmupd x y M) (TraceFriChallenge i final) = Some b"
    unfolding ro_conditioned_trace_challenge_evidence_at_def by blast
  have key_neq: "TraceFriChallenge i final \<noteq> x"
    using not_key[of i final] by simp
  have lookup_old:
      "fmlookup M (TraceFriChallenge i final) = Some b"
    using lookup_new key_neq by simp
  have final_target:
      "final \<in> trace_fri_challenge_state_values M \<union>
        composition_fri_challenge_state_values M"
    using trace_fri_challenge_lookup_state_value[OF lookup_old]
    by blast
  have chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (fr # take (Suc i) roots) final"
    by (rule
      ro_absorb_lookup_chain_conditioned_fri_fresh_update_pullback[
        OF fresh chain_new final_target no_target])
  show ?thesis
    unfolding ro_conditioned_trace_challenge_evidence_at_def
    using i_bound chain_old lookup_old by blast
qed

lemma ro_conditioned_composition_challenge_evidence_at_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and evidence:
      "ro_conditioned_composition_challenge_evidence_at
        (fmupd x y M) fr trace_roots trace_final as dg roots i b"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
    and not_key: "\<And>c st. x \<noteq> CompositionFriChallenge c st"
  shows
    "ro_conditioned_composition_challenge_evidence_at M
      fr trace_roots trace_final as dg roots i b"
proof -
  from evidence obtain final where
    i_bound: "i < length roots"
    and chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots i)
        final"
    and lookup_new:
      "fmlookup (fmupd x y M)
        (CompositionFriChallenge i final) = Some b"
    unfolding ro_conditioned_composition_challenge_evidence_at_def
    by blast
  have key_neq: "CompositionFriChallenge i final \<noteq> x"
    using not_key[of i final] by simp
  have lookup_old:
      "fmlookup M (CompositionFriChallenge i final) = Some b"
    using lookup_new key_neq by simp
  have final_target:
      "final \<in> trace_fri_challenge_state_values M \<union>
        composition_fri_challenge_state_values M"
    using composition_fri_challenge_lookup_state_value[OF lookup_old]
    by blast
  have chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots i)
        final"
    by (rule
      ro_absorb_lookup_chain_conditioned_fri_fresh_update_pullback[
        OF fresh chain_new final_target no_target])
  show ?thesis
    unfolding ro_conditioned_composition_challenge_evidence_at_def
    using i_bound chain_old lookup_old by blast
qed

lemma ro_conditioned_trace_challenge_evidence_at_fresh_update_pushforward:
  assumes fresh: "fmlookup M x = None"
    and evidence:
      "ro_conditioned_trace_challenge_evidence_at M fr roots i b"
    and not_key: "\<And>c st. x \<noteq> TraceFriChallenge c st"
  shows
    "ro_conditioned_trace_challenge_evidence_at
      (fmupd x y M) fr roots i b"
proof -
  from evidence obtain final where
    i_bound: "i < length roots"
    and chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (fr # take (Suc i) roots) final"
    and lookup_old:
      "fmlookup M (TraceFriChallenge i final) = Some b"
    unfolding ro_conditioned_trace_challenge_evidence_at_def by blast
  have ext:
      "channel_for_hash_map M \<le>
        channel_for_hash_map (fmupd x y M)"
    by (rule channel_for_hash_map_fresh_update_extends[OF fresh])
  have chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (fr # take (Suc i) roots) final"
    by (rule ro_absorb_lookup_chain_mono[OF chain_old ext])
  have key_neq: "TraceFriChallenge i final \<noteq> x"
    using not_key[of i final] by simp
  have lookup_new:
      "fmlookup (fmupd x y M) (TraceFriChallenge i final) = Some b"
    using lookup_old key_neq by simp
  show ?thesis
    unfolding ro_conditioned_trace_challenge_evidence_at_def
    using i_bound chain_new lookup_new by blast
qed

lemma ro_conditioned_composition_challenge_evidence_at_fresh_update_pushforward:
  assumes fresh: "fmlookup M x = None"
    and evidence:
      "ro_conditioned_composition_challenge_evidence_at M
        fr trace_roots trace_final as dg roots i b"
    and not_key: "\<And>c st. x \<noteq> CompositionFriChallenge c st"
  shows
    "ro_conditioned_composition_challenge_evidence_at
      (fmupd x y M) fr trace_roots trace_final as dg roots i b"
proof -
  from evidence obtain final where
    i_bound: "i < length roots"
    and chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots i)
        final"
    and lookup_old:
      "fmlookup M (CompositionFriChallenge i final) = Some b"
    unfolding ro_conditioned_composition_challenge_evidence_at_def
    by blast
  have ext:
      "channel_for_hash_map M \<le>
        channel_for_hash_map (fmupd x y M)"
    by (rule channel_for_hash_map_fresh_update_extends[OF fresh])
  have chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots i)
        final"
    by (rule ro_absorb_lookup_chain_mono[OF chain_old ext])
  have key_neq: "CompositionFriChallenge i final \<noteq> x"
    using not_key[of i final] by simp
  have lookup_new:
      "fmlookup (fmupd x y M)
        (CompositionFriChallenge i final) = Some b"
    using lookup_old key_neq by simp
  show ?thesis
    unfolding ro_conditioned_composition_challenge_evidence_at_def
    using i_bound chain_new lookup_new by blast
qed

lemma ro_conditioned_trace_challenge_values_at_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
    and not_key: "\<And>c st. x \<noteq> TraceFriChallenge c st"
  shows
    "ro_conditioned_trace_challenge_values_at (fmupd x y M)
        fr roots i =
      ro_conditioned_trace_challenge_values_at M fr roots i"
  unfolding ro_conditioned_trace_challenge_values_at_def
  using
    ro_conditioned_trace_challenge_evidence_at_fresh_update_pullback[
      OF fresh _ no_target not_key]
    ro_conditioned_trace_challenge_evidence_at_fresh_update_pushforward[
      OF fresh _ not_key]
  by blast

lemma ro_conditioned_composition_challenge_values_at_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
    and not_key: "\<And>c st. x \<noteq> CompositionFriChallenge c st"
  shows
    "ro_conditioned_composition_challenge_values_at (fmupd x y M)
        fr trace_roots trace_final as dg roots i =
      ro_conditioned_composition_challenge_values_at M
        fr trace_roots trace_final as dg roots i"
  unfolding ro_conditioned_composition_challenge_values_at_def
  using
    ro_conditioned_composition_challenge_evidence_at_fresh_update_pullback[
      OF fresh _ no_target not_key]
    ro_conditioned_composition_challenge_evidence_at_fresh_update_pushforward[
      OF fresh _ not_key]
  by blast



lemma ro_conditioned_trace_residual_query_lists_at_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and roots_target:
      "set roots \<subseteq> transcript_absorb_message_values M"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
    and not_key: "\<And>c st. x \<noteq> TraceFriChallenge c st"
  shows
    "ro_conditioned_trace_residual_query_lists_at (fmupd x y M)
        fr roots final_value i =
      ro_conditioned_trace_residual_query_lists_at M
        fr roots final_value i"
proof -
  have vals:
      "ro_conditioned_trace_challenge_values_at (fmupd x y M)
          fr roots i =
        ro_conditioned_trace_challenge_values_at M fr roots i"
    by (rule ro_conditioned_trace_challenge_values_at_fresh_update[
      OF fresh no_target not_key])
  have residual:
      "\<And>b.
        ro_conditioned_trace_residual_query_lists_at_value
          (fmupd x y M) roots b final_value i =
        ro_conditioned_trace_residual_query_lists_at_value
          M roots b final_value i"
    unfolding ro_conditioned_trace_residual_query_lists_at_value_def
    by (rule
      fri_conditioned_quantitative_residual_query_lists_at_value_fresh_update[
        OF fresh roots_target no_target])
  show ?thesis
    unfolding ro_conditioned_trace_residual_query_lists_at_def
    using vals residual by simp
qed

lemma ro_conditioned_composition_residual_query_lists_at_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and roots_target:
      "set roots \<subseteq> transcript_absorb_message_values M"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
    and not_key: "\<And>c st. x \<noteq> CompositionFriChallenge c st"
  shows
    "ro_conditioned_composition_residual_query_lists_at (fmupd x y M)
        fr trace_roots trace_final as dg roots final_value i =
      ro_conditioned_composition_residual_query_lists_at M
        fr trace_roots trace_final as dg roots final_value i"
proof -
  have vals:
      "ro_conditioned_composition_challenge_values_at (fmupd x y M)
          fr trace_roots trace_final as dg roots i =
        ro_conditioned_composition_challenge_values_at M
          fr trace_roots trace_final as dg roots i"
    by (rule
      ro_conditioned_composition_challenge_values_at_fresh_update[
        OF fresh no_target not_key])
  have residual:
      "\<And>b.
        ro_conditioned_composition_residual_query_lists_at_value
          (fmupd x y M) dg roots b final_value i =
        ro_conditioned_composition_residual_query_lists_at_value
          M dg roots b final_value i"
    unfolding ro_conditioned_composition_residual_query_lists_at_value_def
    by (cases "to_nat dg \<le> maxDegree")
      (use
        fri_conditioned_quantitative_residual_query_lists_at_value_fresh_update[
          OF fresh roots_target no_target, where d="to_nat dg"]
        in simp_all)
  show ?thesis
    unfolding ro_conditioned_composition_residual_query_lists_at_def
    using vals residual by simp
qed

lemma ro_conditioned_combined_residual_query_lists_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and messages_target:
      "set
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        \<subseteq> transcript_absorb_message_values M"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
    and not_trace: "\<And>c st. x \<noteq> TraceFriChallenge c st"
    and not_composition:
      "\<And>c st. x \<noteq> CompositionFriChallenge c st"
  shows
    "ro_conditioned_combined_residual_query_lists (fmupd x y M)
        fr trace_roots trace_final as dg composition_roots
        composition_final =
      ro_conditioned_combined_residual_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final"
proof -
  have trace_target:
      "set trace_roots \<subseteq> transcript_absorb_message_values M"
    and composition_target:
      "set composition_roots \<subseteq> transcript_absorb_message_values M"
    using messages_target
    unfolding verifier_header_messages_def by simp_all
  have trace:
      "ro_conditioned_trace_residual_query_lists (fmupd x y M)
          fr trace_roots trace_final =
        ro_conditioned_trace_residual_query_lists M
          fr trace_roots trace_final"
    unfolding ro_conditioned_trace_residual_query_lists_def
    using ro_conditioned_trace_residual_query_lists_at_fresh_update[
      OF fresh trace_target no_target not_trace]
    by simp
  have composition:
      "ro_conditioned_composition_residual_query_lists (fmupd x y M)
          fr trace_roots trace_final as dg composition_roots
          composition_final =
        ro_conditioned_composition_residual_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    unfolding ro_conditioned_composition_residual_query_lists_def
    using
      ro_conditioned_composition_residual_query_lists_at_fresh_update[
        OF fresh composition_target no_target not_composition]
    by simp
  show ?thesis
    unfolding ro_conditioned_combined_residual_query_lists_def
    using trace composition by simp
qed

lemma ro_conditioned_trace_degenerate_query_lists_at_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and roots_target:
      "set roots \<subseteq> transcript_absorb_message_values M"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows
    "ro_conditioned_trace_degenerate_query_lists_at (fmupd x y M)
        roots final_value i round_idx =
      ro_conditioned_trace_degenerate_query_lists_at M
        roots final_value i round_idx"
  unfolding ro_conditioned_trace_degenerate_query_lists_at_def
  by (rule
    fri_conditioned_quantitative_degenerate_query_lists_at_fresh_update[
      OF fresh roots_target no_target])

lemma ro_conditioned_composition_degenerate_query_lists_at_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and roots_target:
      "set roots \<subseteq> transcript_absorb_message_values M"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows
    "ro_conditioned_composition_degenerate_query_lists_at (fmupd x y M)
        dg roots final_value i round_idx =
      ro_conditioned_composition_degenerate_query_lists_at M
        dg roots final_value i round_idx"
  unfolding ro_conditioned_composition_degenerate_query_lists_at_def
  by (cases "to_nat dg \<le> maxDegree")
    (use
      fri_conditioned_quantitative_degenerate_query_lists_at_fresh_update[
        OF fresh roots_target no_target, where d="to_nat dg"]
      in simp_all)



lemma ro_conditioned_absorbed_query_header_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and clean_new:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
    and no_initial_new:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
    and header_chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        query_start"
    and query_chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        query_start (List.concat (take j query_chunks)) final"
    and k_eq: "k = QueryIndexChallenge j final"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
  obtains query_start_old where
    "\<not> hash_map_output_collision (channel_for_hash_map M)"
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state)
      (verifier_header_messages fr trace_roots trace_final as dg
        composition_roots composition_final)
      query_start_old"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      query_start_old (List.concat (take j query_chunks)) final"
    "set
      (verifier_header_messages fr trace_roots trace_final as dg
        composition_roots composition_final)
      \<subseteq> transcript_absorb_message_values M"
proof -
  have old_lookup: "fmlookup M k = Some z"
    using active_lookup key_neq by simp
  have final_target: "final \<in> query_index_state_values M"
  proof -
    have "fmlookup M (QueryIndexChallenge j final) = Some z"
      using old_lookup k_eq by simp
    then show ?thesis by (rule query_index_lookup_state_value)
  qed
  have full_chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final @
          List.concat (take j query_chunks))
        final"
    by (rule ro_absorb_lookup_chain_append[
      OF header_chain_new query_chain_new])
  have no_first:
      "y \<notin> first_root_relation_drift_targets M x"
    using no_target
    unfolding conditioned_fri_relation_drift_targets_def by blast
  have full_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final @
          List.concat (take j query_chunks))
        final"
    by (rule ro_absorb_lookup_chain_fresh_update_pullback[
      OF fresh full_chain_new final_target no_first])
  from ro_absorb_lookup_chain_append_split[OF full_chain_old]
  obtain query_start_old where
    header_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        query_start_old"
    and query_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        query_start_old (List.concat (take j query_chunks)) final"
    by blast
  have messages_target:
      "set
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        \<subseteq> transcript_absorb_message_values M"
  proof -
    have
      "set
        (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final @
          List.concat (take j query_chunks))
        \<subseteq> transcript_absorb_message_values M"
      by (rule ro_absorb_lookup_chain_messages_subset[OF full_chain_old])
    then show ?thesis by simp
  qed
  have clean_old:
      "\<not> hash_map_output_collision (channel_for_hash_map M)"
    by (rule hash_map_clean_fresh_update_pullback[
      OF fresh clean_new])
  have no_initial_old:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
    by (rule hash_map_no_initial_fresh_update_pullback[
      OF fresh no_initial_new])
  show thesis
    by (rule that[OF clean_old no_initial_old header_chain_old
      query_chain_old messages_target])
qed



lemma ro_conditioned_residual_absorbed_query_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "ro_conditioned_residual_absorbed_query_relation
        (fmupd x y M) k z"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
    and not_trace: "\<And>c st. x \<noteq> TraceFriChallenge c st"
    and not_composition:
      "\<And>c st. x \<noteq> CompositionFriChallenge c st"
  shows "ro_conditioned_residual_absorbed_query_relation M k z"
proof -
  from ro_conditioned_residual_absorbed_query_relationD[OF rel]
  obtain fr trace_roots trace_final as dg
      composition_roots composition_final
      query_chunks raws query_start final j where
    clean_new:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
    and no_initial_new:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
    and trace_len: "length trace_roots = ceil_log clength"
    and alpha_len: "length as = length spec"
    and composition_len:
      "length composition_roots = ceil_log (Suc (to_nat dg))"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and header_chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        query_start"
    and query_chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        query_start (List.concat (take j query_chunks)) final"
    and raws_len: "length raws = rounds"
    and raws_in_new:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_conditioned_combined_residual_query_lists (fmupd x y M)
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    and j_bound: "j < rounds"
    and k_eq: "k = QueryIndexChallenge j final"
    and z_eq: "z = raws ! j"
    .
  from ro_conditioned_absorbed_query_header_fresh_update_pullback[
    OF fresh key_neq active_lookup clean_new no_initial_new
      header_chain_new query_chain_new k_eq no_target]
  obtain query_start_old where
    clean_old:
      "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial_old:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
    and header_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        query_start_old"
    and query_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        query_start_old (List.concat (take j query_chunks)) final"
    and messages_target:
      "set
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        \<subseteq> transcript_absorb_message_values M"
    .
  have query_lists:
      "ro_conditioned_combined_residual_query_lists (fmupd x y M)
          fr trace_roots trace_final as dg composition_roots
          composition_final =
        ro_conditioned_combined_residual_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    by (rule ro_conditioned_combined_residual_query_lists_fresh_update[
      OF fresh messages_target no_target not_trace not_composition])
  have raws_in_old:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_conditioned_combined_residual_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    using raws_in_new query_lists by simp
  show ?thesis
    unfolding ro_conditioned_residual_absorbed_query_relation_def Let_def
    using clean_old no_initial_old trace_len alpha_len composition_len
      degree_bound header_chain_old query_chain_old raws_len raws_in_old
      j_bound k_eq z_eq
    by blast
qed



lemma ro_conditioned_degenerate_absorbed_query_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "ro_conditioned_degenerate_absorbed_query_relation
        (fmupd x y M) k z"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows "ro_conditioned_degenerate_absorbed_query_relation M k z"
proof -
  from ro_conditioned_degenerate_absorbed_query_relationD[OF rel]
  obtain fr trace_roots trace_final as dg
      composition_roots composition_final
      query_chunks raws query_start final j where
    clean_new:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
    and no_initial_new:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
    and trace_len: "length trace_roots = ceil_log clength"
    and alpha_len: "length as = length spec"
    and composition_len:
      "length composition_roots = ceil_log (Suc (to_nat dg))"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and header_chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        query_start"
    and query_chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        query_start (List.concat (take j query_chunks)) final"
    and raws_len: "length raws = rounds"
    and degenerate_new:
      "(\<exists>i < length trace_roots.
          map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_degenerate_query_lists_at
              (fmupd x y M) trace_roots trace_final i j) \<or>
       (\<exists>i < length composition_roots.
          map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_degenerate_query_lists_at
              (fmupd x y M) dg composition_roots composition_final i j)"
    and j_bound: "j < rounds"
    and k_eq: "k = QueryIndexChallenge j final"
    and z_eq: "z = raws ! j"
    .
  from ro_conditioned_absorbed_query_header_fresh_update_pullback[
    OF fresh key_neq active_lookup clean_new no_initial_new
      header_chain_new query_chain_new k_eq no_target]
  obtain query_start_old where
    clean_old:
      "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial_old:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
    and header_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        query_start_old"
    and query_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        query_start_old (List.concat (take j query_chunks)) final"
    and messages_target:
      "set
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        \<subseteq> transcript_absorb_message_values M"
    .
  have trace_target:
      "set trace_roots \<subseteq> transcript_absorb_message_values M"
    and composition_target:
      "set composition_roots \<subseteq> transcript_absorb_message_values M"
    using messages_target
    unfolding verifier_header_messages_def by simp_all
  have degenerate_old:
      "(\<exists>i < length trace_roots.
          map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_degenerate_query_lists_at
              M trace_roots trace_final i j) \<or>
       (\<exists>i < length composition_roots.
          map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_degenerate_query_lists_at
              M dg composition_roots composition_final i j)"
    using degenerate_new
  proof
    assume trace_new:
      "\<exists>i < length trace_roots.
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_trace_degenerate_query_lists_at
            (fmupd x y M) trace_roots trace_final i j"
    then obtain i where i_bound: "i < length trace_roots"
      and member_new:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_trace_degenerate_query_lists_at
            (fmupd x y M) trace_roots trace_final i j"
      by blast
    have stable:
        "ro_conditioned_trace_degenerate_query_lists_at
            (fmupd x y M) trace_roots trace_final i j =
          ro_conditioned_trace_degenerate_query_lists_at
            M trace_roots trace_final i j"
      by (rule
        ro_conditioned_trace_degenerate_query_lists_at_fresh_update[
          OF fresh trace_target no_target])
    show ?thesis using i_bound member_new stable by blast
  next
    assume composition_new:
      "\<exists>i < length composition_roots.
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_composition_degenerate_query_lists_at
            (fmupd x y M) dg composition_roots composition_final i j"
    then obtain i where i_bound: "i < length composition_roots"
      and member_new:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_composition_degenerate_query_lists_at
            (fmupd x y M) dg composition_roots composition_final i j"
      by blast
    have stable:
        "ro_conditioned_composition_degenerate_query_lists_at
            (fmupd x y M) dg composition_roots composition_final i j =
          ro_conditioned_composition_degenerate_query_lists_at
            M dg composition_roots composition_final i j"
      by (rule
        ro_conditioned_composition_degenerate_query_lists_at_fresh_update[
          OF fresh composition_target no_target])
    show ?thesis using i_bound member_new stable by blast
  qed
  show ?thesis
    unfolding ro_conditioned_degenerate_absorbed_query_relation_def Let_def
    using clean_old no_initial_old trace_len alpha_len composition_len
      degree_bound header_chain_old query_chain_old raws_len degenerate_old
      j_bound k_eq z_eq
    by blast
qed



lemma ro_conditioned_augmented_absorbed_query_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "ro_conditioned_augmented_absorbed_query_relation
        (fmupd x y M) k z"
    and no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
    and not_trace: "\<And>c st. x \<noteq> TraceFriChallenge c st"
    and not_composition:
      "\<And>c st. x \<noteq> CompositionFriChallenge c st"
  shows "ro_conditioned_augmented_absorbed_query_relation M k z"
proof -
  from rel show ?thesis
    unfolding ro_conditioned_augmented_absorbed_query_relation_def
  proof
    assume residual:
      "ro_conditioned_residual_absorbed_query_relation
        (fmupd x y M) k z"
    have "ro_conditioned_residual_absorbed_query_relation M k z"
      by (rule
        ro_conditioned_residual_absorbed_query_relation_fresh_update_pullback[
          OF fresh key_neq active_lookup residual no_target
            not_trace not_composition])
    then show
      "ro_conditioned_residual_absorbed_query_relation M k z \<or>
       ro_conditioned_degenerate_absorbed_query_relation M k z"
      by blast
  next
    assume degenerate:
      "ro_conditioned_degenerate_absorbed_query_relation
        (fmupd x y M) k z"
    have "ro_conditioned_degenerate_absorbed_query_relation M k z"
      by (rule
        ro_conditioned_degenerate_absorbed_query_relation_fresh_update_pullback[
          OF fresh key_neq active_lookup degenerate no_target])
    then show
      "ro_conditioned_residual_absorbed_query_relation M k z \<or>
       ro_conditioned_degenerate_absorbed_query_relation M k z"
      by blast
  qed
qed

lemma ro_conditioned_augmented_absorbed_query_relation_nonchallenge_drift_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y"
    and not_trace: "\<And>c st. x \<noteq> TraceFriChallenge c st"
    and not_composition:
      "\<And>c st. x \<noteq> CompositionFriChallenge c st"
  shows "y \<in> conditioned_fri_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        ro_conditioned_augmented_absorbed_query_relation
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        ro_conditioned_augmented_absorbed_query_relation M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "ro_conditioned_augmented_absorbed_query_relation
        (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def by blast+
  have rel_old:
      "ro_conditioned_augmented_absorbed_query_relation M k z"
    by (rule
      ro_conditioned_augmented_absorbed_query_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target
          not_trace not_composition])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
      "hash_state_relation_active
        ro_conditioned_augmented_absorbed_query_relation M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed

lemma ro_conditioned_augmented_absorbed_query_relation_nonchallenge_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
    and not_trace: "\<And>c st. x \<noteq> TraceFriChallenge c st"
    and not_composition:
      "\<And>c st. x \<noteq> CompositionFriChallenge c st"
  shows
    "card {y.
      hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y}
      \<le> 7 * card (fmdom' M) + 2"
proof -
  have subset:
      "{y.
        hash_state_relation_drift_activation
          ro_conditioned_augmented_absorbed_query_relation M x y}
        \<subseteq> conditioned_fri_relation_drift_targets M x"
    using
      ro_conditioned_augmented_absorbed_query_relation_nonchallenge_drift_imp_target[
        OF fresh _ not_trace not_composition]
    by blast
  have
      "card {y.
        hash_state_relation_drift_activation
          ro_conditioned_augmented_absorbed_query_relation M x y}
        \<le> card (conditioned_fri_relation_drift_targets M x)"
    by (rule card_mono[
      OF finite_conditioned_fri_relation_drift_targets subset])
  also have "... \<le> 7 * card (fmdom' M) + 2"
    by (rule card_conditioned_fri_relation_drift_targets_le)
  finally show ?thesis .
qed
end
end
