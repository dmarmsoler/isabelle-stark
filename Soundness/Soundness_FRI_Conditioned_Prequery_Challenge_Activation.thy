theory Soundness_FRI_Conditioned_Prequery_Challenge_Activation
  imports Stark.Soundness_FRI_Conditioned_Prequery_Challenge_Fibers
begin

context soundness
begin

lemma ro_conditioned_augmented_absorbed_query_relation_trace_challenge_drift_subset:
  assumes fresh: "fmlookup M x = None"
    and x_trace: "x = TraceFriChallenge c ast"
    and drift:
      "hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y"
  shows
    "y \<in> conditioned_fri_relation_drift_targets M x \<union>
      ro_conditioned_trace_nondegenerate_challenge_drift_values M x"
proof (cases "y \<in> conditioned_fri_relation_drift_targets M x")
  case True
  then show ?thesis by blast
next
  case False
  then have no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x" .
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
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  from rel_new show ?thesis
    unfolding ro_conditioned_augmented_absorbed_query_relation_def
  proof
    assume residual_new:
      "ro_conditioned_residual_absorbed_query_relation
        (fmupd x y M) k z"
    from ro_conditioned_residual_absorbed_query_relationD[
      OF residual_new]
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
      OF fresh key_neq lookup_new clean_new no_initial_new
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
    have contradiction_from_old:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_combined_residual_query_lists M
            fr trace_roots trace_final as dg composition_roots
            composition_final
        \<Longrightarrow> False"
    proof -
      assume raws_in_old:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_combined_residual_query_lists M
            fr trace_roots trace_final as dg composition_roots
            composition_final"
      have rel_old:
          "ro_conditioned_residual_absorbed_query_relation M k z"
        unfolding ro_conditioned_residual_absorbed_query_relation_def Let_def
        using clean_old no_initial_old trace_len alpha_len composition_len
          degree_bound header_chain_old query_chain_old raws_len raws_in_old
          j_bound k_eq z_eq
        by blast
      have active_old:
          "hash_state_relation_active
            ro_conditioned_augmented_absorbed_query_relation M k z"
        unfolding hash_state_relation_active_def
          ro_conditioned_augmented_absorbed_query_relation_def
        using lookup_old rel_old by blast
      show False using inactive_old active_old by contradiction
    qed
    have trace_or_composition:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_residual_query_lists
              (fmupd x y M) fr trace_roots trace_final \<or>
         map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_residual_query_lists
              (fmupd x y M) fr trace_roots trace_final as dg
              composition_roots composition_final"
      using raws_in_new
      unfolding ro_conditioned_combined_residual_query_lists_def
      by blast
    from trace_or_composition show ?thesis
    proof
      assume trace_residual_new:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_residual_query_lists
              (fmupd x y M) fr trace_roots trace_final"
      from trace_residual_new obtain i where
        i_bound: "i < length trace_roots"
        and at_new:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_residual_query_lists_at
              (fmupd x y M) fr trace_roots trace_final i"
        unfolding ro_conditioned_trace_residual_query_lists_def
        by blast
      from at_new obtain b where
        evidence_new:
          "ro_conditioned_trace_challenge_evidence_at
            (fmupd x y M) fr trace_roots i b"
        and value_new:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_residual_query_lists_at_value
              (fmupd x y M) trace_roots b trace_final i"
        unfolding ro_conditioned_trace_residual_query_lists_at_def
          ro_conditioned_trace_challenge_values_at_def
        by blast
      have value_stable:
          "ro_conditioned_trace_residual_query_lists_at_value
              (fmupd x y M) trace_roots b trace_final i =
            ro_conditioned_trace_residual_query_lists_at_value
              M trace_roots b trace_final i"
        unfolding ro_conditioned_trace_residual_query_lists_at_value_def
        by (rule
          fri_conditioned_quantitative_residual_query_lists_at_value_fresh_update[
            OF fresh trace_target no_target])
      have value_old:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_residual_query_lists_at_value
              M trace_roots b trace_final i"
        using value_new value_stable by simp
      from evidence_new obtain challenge_state where
        challenge_chain_new:
          "ro_absorb_lookup_chain
            (channel_for_hash_map (fmupd x y M))
            (PState adversary_initial_state)
            (fr # take (Suc i) trace_roots) challenge_state"
        and challenge_lookup_new:
          "fmlookup (fmupd x y M)
            (TraceFriChallenge i challenge_state) = Some b"
        unfolding ro_conditioned_trace_challenge_evidence_at_def
        by blast
      show ?thesis
      proof (cases "TraceFriChallenge i challenge_state = x")
        case False
        have challenge_lookup_old:
            "fmlookup M (TraceFriChallenge i challenge_state) = Some b"
          using challenge_lookup_new False by simp
        have challenge_state_target:
            "challenge_state \<in>
              trace_fri_challenge_state_values M \<union>
                composition_fri_challenge_state_values M"
          using trace_fri_challenge_lookup_state_value[
            OF challenge_lookup_old]
          by blast
        have challenge_chain_old:
            "ro_absorb_lookup_chain (channel_for_hash_map M)
              (PState adversary_initial_state)
              (fr # take (Suc i) trace_roots) challenge_state"
          by (rule
            ro_absorb_lookup_chain_conditioned_fri_fresh_update_pullback[
              OF fresh challenge_chain_new challenge_state_target no_target])
        have evidence_old:
            "ro_conditioned_trace_challenge_evidence_at
              M fr trace_roots i b"
          unfolding ro_conditioned_trace_challenge_evidence_at_def
          using i_bound challenge_chain_old challenge_lookup_old by blast
        have at_old:
            "map (\<lambda>raw. index (to_nat raw)) raws \<in>
              ro_conditioned_trace_residual_query_lists_at
                M fr trace_roots trace_final i"
          unfolding ro_conditioned_trace_residual_query_lists_at_def
            ro_conditioned_trace_challenge_values_at_def
          using evidence_old value_old by blast
        have raws_in_old:
            "map (\<lambda>raw. index (to_nat raw)) raws \<in>
              ro_conditioned_combined_residual_query_lists M
                fr trace_roots trace_final as dg composition_roots
                composition_final"
          unfolding ro_conditioned_combined_residual_query_lists_def
            ro_conditioned_trace_residual_query_lists_def
          using i_bound at_old by blast
        show ?thesis
          using contradiction_from_old[OF raws_in_old] by blast
      next
        case True
        have b_eq: "b = y"
          using challenge_lookup_new True by simp
        have challenge_chain_old:
            "ro_absorb_lookup_chain (channel_for_hash_map M)
              (PState adversary_initial_state)
              (fr # take (Suc i) trace_roots) challenge_state"
          using challenge_chain_new
          by (simp only: x_trace
            ro_absorb_lookup_chain_trace_fri_challenge_update)
        let ?qs = "map (\<lambda>raw. index (to_nat raw)) raws"
        have quantitative_old:
            "?qs \<in>
              fri_conditioned_quantitative_residual_query_lists_at_value
                (clength - 1) trace_roots b trace_final
                (channel_for_hash_map M) i"
          using value_old
          unfolding ro_conditioned_trace_residual_query_lists_at_value_def .
        have round_list_bound: "j < length ?qs"
          using raws_len j_bound by simp
        have agreement_actual:
            "fri_evidence_next_idx trace_roots ?qs j i \<in>
              fri_conditioned_agreement_indices i
                (fri_builder_conceptual_layers trace_roots
                  (channel_for_hash_map M) trace_final ! i)
                (fri_builder_conceptual_layers trace_roots
                  (channel_for_hash_map M) trace_final ! Suc i) b"
          using quantitative_old round_list_bound
          unfolding
            fri_conditioned_quantitative_residual_query_lists_at_value_def
            fri_conditioned_residual_query_lists_at_value_def Let_def
          by blast
        have query_entry: "?qs ! j = index (to_nat z)"
          using raws_len j_bound z_eq by simp
        have query_idx_eq:
            "fri_evidence_next_idx trace_roots ?qs j i =
              fri_evidence_next_idx trace_roots
                [index (to_nat z)] 0 i"
          using query_entry
          unfolding fri_evidence_next_idx_def fri_evidence_layer_idx_def
            fri_evidence_layer_len_def
          by simp
        have agreement_single:
            "fri_evidence_next_idx trace_roots
                [index (to_nat z)] 0 i \<in>
              fri_conditioned_agreement_indices i
                (fri_builder_conceptual_layers trace_roots
                  (channel_for_hash_map M) trace_final ! i)
                (fri_builder_conceptual_layers trace_roots
                  (channel_for_hash_map M) trace_final ! Suc i) b"
          using agreement_actual query_idx_eq by simp
        have nondegenerate_single:
            "fri_evidence_next_idx trace_roots
                [index (to_nat z)] 0 i \<notin>
              fri_conditioned_degenerate_agreement_indices i
                (fri_builder_conceptual_layers trace_roots
                  (channel_for_hash_map M) trace_final ! i)
                (fri_builder_conceptual_layers trace_roots
                  (channel_for_hash_map M) trace_final ! Suc i)"
        proof
          assume degenerate_single:
              "fri_evidence_next_idx trace_roots
                  [index (to_nat z)] 0 i \<in>
                fri_conditioned_degenerate_agreement_indices i
                  (fri_builder_conceptual_layers trace_roots
                    (channel_for_hash_map M) trace_final ! i)
                  (fri_builder_conceptual_layers trace_roots
                    (channel_for_hash_map M) trace_final ! Suc i)"
          have degenerate_actual:
              "fri_evidence_next_idx trace_roots ?qs j i \<in>
                fri_conditioned_degenerate_agreement_indices i
                  (fri_builder_conceptual_layers trace_roots
                    (channel_for_hash_map M) trace_final ! i)
                  (fri_builder_conceptual_layers trace_roots
                    (channel_for_hash_map M) trace_final ! Suc i)"
            using degenerate_single query_idx_eq by simp
          have degenerate_list:
              "?qs \<in>
                fri_conditioned_quantitative_degenerate_query_lists_at
                  (clength - 1) trace_roots trace_final
                  (channel_for_hash_map M) i j"
            by (rule
              fri_conditioned_quantitative_residual_imp_degenerate[
                OF quantitative_old round_list_bound degenerate_actual])
          have trace_degenerate_old:
              "?qs \<in>
                ro_conditioned_trace_degenerate_query_lists_at
                  M trace_roots trace_final i j"
            using degenerate_list
            unfolding ro_conditioned_trace_degenerate_query_lists_at_def .
          have degenerate_rel_old:
              "ro_conditioned_degenerate_absorbed_query_relation M k z"
            unfolding
              ro_conditioned_degenerate_absorbed_query_relation_def Let_def
            using clean_old no_initial_old trace_len alpha_len
              composition_len degree_bound header_chain_old query_chain_old
              raws_len i_bound trace_degenerate_old j_bound k_eq z_eq
            by blast
          have active_old:
              "hash_state_relation_active
                ro_conditioned_augmented_absorbed_query_relation M k z"
            unfolding hash_state_relation_active_def
              ro_conditioned_augmented_absorbed_query_relation_def
            using lookup_old degenerate_rel_old by blast
          show False using inactive_old active_old by contradiction
        qed
        have trace_final_target:
            "trace_final \<in> transcript_absorb_message_values M"
          using messages_target
          unfolding verifier_header_messages_def by simp
        let ?u =
          "if Suc i < length trace_roots
           then trace_roots ! Suc i else trace_final"
        have successor_target:
            "?u \<in> transcript_absorb_message_values M"
        proof (cases "Suc i < length trace_roots")
          case True
          then have root_mem:
              "trace_roots ! Suc i \<in> set trace_roots"
            by simp
          have root_target:
              "trace_roots ! Suc i \<in> transcript_absorb_message_values M"
            using trace_target root_mem by auto
          show ?thesis using True root_target by simp
        next
          case False
          then show ?thesis using trace_final_target by simp
        qed
        have z_target:
            "z \<in> hash_map_output_values (channel_for_hash_map M)"
        proof (rule hash_map_output_valuesI)
          show
            "fmlookup (HashMap (channel_for_hash_map M)) k = Some z"
            using lookup_old unfolding channel_for_hash_map_def by simp
        qed
        have candidate:
            "y \<in>
              ro_conditioned_trace_nondegenerate_challenge_candidates
                M x ?u z"
          unfolding
            ro_conditioned_trace_nondegenerate_challenge_candidates_def
            Let_def
          using trace_len i_bound challenge_chain_old True b_eq
            agreement_single nondegenerate_single
          by blast
        have
            "y \<in>
              ro_conditioned_trace_nondegenerate_challenge_drift_values M x"
          unfolding
            ro_conditioned_trace_nondegenerate_challenge_drift_values_def
          using successor_target z_target candidate by blast
        then show ?thesis by simp
      qed
    next
      assume composition_residual_new:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_residual_query_lists
              (fmupd x y M) fr trace_roots trace_final as dg
              composition_roots composition_final"
      from composition_residual_new obtain i where
        i_bound: "i < length composition_roots"
        and at_new:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_residual_query_lists_at
              (fmupd x y M) fr trace_roots trace_final as dg
              composition_roots composition_final i"
        unfolding ro_conditioned_composition_residual_query_lists_def
        by blast
      have not_composition: "\<And>d st. x \<noteq> CompositionFriChallenge d st"
        using x_trace by simp
      have at_stable:
          "ro_conditioned_composition_residual_query_lists_at
              (fmupd x y M) fr trace_roots trace_final as dg
              composition_roots composition_final i =
            ro_conditioned_composition_residual_query_lists_at
              M fr trace_roots trace_final as dg
              composition_roots composition_final i"
        by (rule
          ro_conditioned_composition_residual_query_lists_at_fresh_update[
            OF fresh composition_target no_target not_composition])
      have at_old:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_residual_query_lists_at
              M fr trace_roots trace_final as dg
              composition_roots composition_final i"
        using at_new at_stable by simp
      have raws_in_old:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_combined_residual_query_lists M
              fr trace_roots trace_final as dg composition_roots
              composition_final"
        unfolding ro_conditioned_combined_residual_query_lists_def
          ro_conditioned_composition_residual_query_lists_def
        using i_bound at_old by blast
      show ?thesis
        using contradiction_from_old[OF raws_in_old] by blast
    qed
  next
    assume degenerate_new:
      "ro_conditioned_degenerate_absorbed_query_relation
        (fmupd x y M) k z"
    have degenerate_old:
        "ro_conditioned_degenerate_absorbed_query_relation M k z"
      by (rule
        ro_conditioned_degenerate_absorbed_query_relation_fresh_update_pullback[
          OF fresh key_neq lookup_new degenerate_new no_target])
    have active_old:
        "hash_state_relation_active
          ro_conditioned_augmented_absorbed_query_relation M k z"
      unfolding hash_state_relation_active_def
        ro_conditioned_augmented_absorbed_query_relation_def
      using lookup_old degenerate_old by blast
    then show ?thesis using inactive_old by contradiction
  qed
qed



lemma ro_conditioned_augmented_absorbed_query_relation_composition_challenge_drift_subset:
  assumes fresh: "fmlookup M x = None"
    and x_composition: "x = CompositionFriChallenge c ast"
    and drift:
      "hash_state_relation_drift_activation
        ro_conditioned_augmented_absorbed_query_relation M x y"
  shows
    "y \<in> conditioned_fri_relation_drift_targets M x \<union>
      ro_conditioned_composition_nondegenerate_challenge_drift_values M x"
proof (cases "y \<in> conditioned_fri_relation_drift_targets M x")
  case True
  then show ?thesis by blast
next
  case False
  then have no_target:
      "y \<notin> conditioned_fri_relation_drift_targets M x" .
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
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  from rel_new show ?thesis
    unfolding ro_conditioned_augmented_absorbed_query_relation_def
  proof
    assume residual_new:
      "ro_conditioned_residual_absorbed_query_relation
        (fmupd x y M) k z"
    from ro_conditioned_residual_absorbed_query_relationD[
      OF residual_new]
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
      OF fresh key_neq lookup_new clean_new no_initial_new
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
    have contradiction_from_old:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_combined_residual_query_lists M
            fr trace_roots trace_final as dg composition_roots
            composition_final
        \<Longrightarrow> False"
    proof -
      assume raws_in_old:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_combined_residual_query_lists M
            fr trace_roots trace_final as dg composition_roots
            composition_final"
      have rel_old:
          "ro_conditioned_residual_absorbed_query_relation M k z"
        unfolding ro_conditioned_residual_absorbed_query_relation_def Let_def
        using clean_old no_initial_old trace_len alpha_len composition_len
          degree_bound header_chain_old query_chain_old raws_len raws_in_old
          j_bound k_eq z_eq
        by blast
      have active_old:
          "hash_state_relation_active
            ro_conditioned_augmented_absorbed_query_relation M k z"
        unfolding hash_state_relation_active_def
          ro_conditioned_augmented_absorbed_query_relation_def
        using lookup_old rel_old by blast
      show False using inactive_old active_old by contradiction
    qed
    have trace_or_composition:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_residual_query_lists
              (fmupd x y M) fr trace_roots trace_final \<or>
         map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_residual_query_lists
              (fmupd x y M) fr trace_roots trace_final as dg
              composition_roots composition_final"
      using raws_in_new
      unfolding ro_conditioned_combined_residual_query_lists_def
      by blast
    from trace_or_composition show ?thesis
    proof
      assume trace_residual_new:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_residual_query_lists
              (fmupd x y M) fr trace_roots trace_final"
      from trace_residual_new obtain i where
        i_bound: "i < length trace_roots"
        and at_new:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_residual_query_lists_at
              (fmupd x y M) fr trace_roots trace_final i"
        unfolding ro_conditioned_trace_residual_query_lists_def
        by blast
      have not_trace: "\<And>d st. x \<noteq> TraceFriChallenge d st"
        using x_composition by simp
      have at_stable:
          "ro_conditioned_trace_residual_query_lists_at
              (fmupd x y M) fr trace_roots trace_final i =
            ro_conditioned_trace_residual_query_lists_at
              M fr trace_roots trace_final i"
        by (rule
          ro_conditioned_trace_residual_query_lists_at_fresh_update[
            OF fresh trace_target no_target not_trace])
      have at_old:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_residual_query_lists_at
              M fr trace_roots trace_final i"
        using at_new at_stable by simp
      have raws_in_old:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_combined_residual_query_lists M
              fr trace_roots trace_final as dg composition_roots
              composition_final"
        unfolding ro_conditioned_combined_residual_query_lists_def
          ro_conditioned_trace_residual_query_lists_def
        using i_bound at_old by blast
      show ?thesis
        using contradiction_from_old[OF raws_in_old] by blast
    next
      assume composition_residual_new:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_residual_query_lists
              (fmupd x y M) fr trace_roots trace_final as dg
              composition_roots composition_final"
      from composition_residual_new obtain i where
        i_bound: "i < length composition_roots"
        and at_new:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_residual_query_lists_at
              (fmupd x y M) fr trace_roots trace_final as dg
              composition_roots composition_final i"
        unfolding ro_conditioned_composition_residual_query_lists_def
        by blast
      from at_new obtain b where
        evidence_new:
          "ro_conditioned_composition_challenge_evidence_at
            (fmupd x y M) fr trace_roots trace_final as dg
            composition_roots i b"
        and value_new:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_residual_query_lists_at_value
              (fmupd x y M) dg composition_roots b composition_final i"
        unfolding ro_conditioned_composition_residual_query_lists_at_def
          ro_conditioned_composition_challenge_values_at_def
        by blast
      let ?qs = "map (\<lambda>raw. index (to_nat raw)) raws"
      have quantitative_new:
          "?qs \<in>
            fri_conditioned_quantitative_residual_query_lists_at_value
              (to_nat dg) composition_roots b composition_final
              (channel_for_hash_map (fmupd x y M)) i"
        using value_new degree_bound
        unfolding
          ro_conditioned_composition_residual_query_lists_at_value_def
        by simp
      have quantitative_stable:
          "fri_conditioned_quantitative_residual_query_lists_at_value
              (to_nat dg) composition_roots b composition_final
              (channel_for_hash_map (fmupd x y M)) i =
            fri_conditioned_quantitative_residual_query_lists_at_value
              (to_nat dg) composition_roots b composition_final
              (channel_for_hash_map M) i"
        by (rule
          fri_conditioned_quantitative_residual_query_lists_at_value_fresh_update[
            OF fresh composition_target no_target])
      have quantitative_old:
          "?qs \<in>
            fri_conditioned_quantitative_residual_query_lists_at_value
              (to_nat dg) composition_roots b composition_final
              (channel_for_hash_map M) i"
        using quantitative_new quantitative_stable by simp
      from evidence_new obtain challenge_state where
        challenge_chain_new:
          "ro_absorb_lookup_chain
            (channel_for_hash_map (fmupd x y M))
            (PState adversary_initial_state)
            (composition_fri_challenge_prefix_messages
              fr trace_roots trace_final as dg composition_roots i)
            challenge_state"
        and challenge_lookup_new:
          "fmlookup (fmupd x y M)
            (CompositionFriChallenge i challenge_state) = Some b"
        unfolding ro_conditioned_composition_challenge_evidence_at_def
        by blast
      show ?thesis
      proof (cases "CompositionFriChallenge i challenge_state = x")
        case False
        have challenge_lookup_old:
            "fmlookup M (CompositionFriChallenge i challenge_state) = Some b"
          using challenge_lookup_new False by simp
        have challenge_state_target:
            "challenge_state \<in>
              trace_fri_challenge_state_values M \<union>
                composition_fri_challenge_state_values M"
          using composition_fri_challenge_lookup_state_value[
            OF challenge_lookup_old]
          by blast
        have challenge_chain_old:
            "ro_absorb_lookup_chain (channel_for_hash_map M)
              (PState adversary_initial_state)
              (composition_fri_challenge_prefix_messages
                fr trace_roots trace_final as dg composition_roots i)
              challenge_state"
          by (rule
            ro_absorb_lookup_chain_conditioned_fri_fresh_update_pullback[
              OF fresh challenge_chain_new challenge_state_target no_target])
        have evidence_old:
            "ro_conditioned_composition_challenge_evidence_at
              M fr trace_roots trace_final as dg composition_roots i b"
          unfolding ro_conditioned_composition_challenge_evidence_at_def
          using i_bound challenge_chain_old challenge_lookup_old by blast
        have value_old:
            "?qs \<in>
              ro_conditioned_composition_residual_query_lists_at_value
                M dg composition_roots b composition_final i"
          using quantitative_old degree_bound
          unfolding
            ro_conditioned_composition_residual_query_lists_at_value_def
          by simp
        have at_old:
            "?qs \<in>
              ro_conditioned_composition_residual_query_lists_at
                M fr trace_roots trace_final as dg
                composition_roots composition_final i"
          unfolding ro_conditioned_composition_residual_query_lists_at_def
            ro_conditioned_composition_challenge_values_at_def
          using evidence_old value_old by blast
        have raws_in_old:
            "?qs \<in>
              ro_conditioned_combined_residual_query_lists M
                fr trace_roots trace_final as dg composition_roots
                composition_final"
          unfolding ro_conditioned_combined_residual_query_lists_def
            ro_conditioned_composition_residual_query_lists_def
          using i_bound at_old by blast
        show ?thesis
          using contradiction_from_old[OF raws_in_old] by blast
      next
        case True
        have b_eq: "b = y"
          using challenge_lookup_new True by simp
        have challenge_chain_old:
            "ro_absorb_lookup_chain (channel_for_hash_map M)
              (PState adversary_initial_state)
              (composition_fri_challenge_prefix_messages
                fr trace_roots trace_final as dg composition_roots i)
              challenge_state"
          using challenge_chain_new
          by (simp only: x_composition
            ro_absorb_lookup_chain_composition_fri_challenge_update)
        have round_list_bound: "j < length ?qs"
          using raws_len j_bound by simp
        have agreement_actual:
            "fri_evidence_next_idx composition_roots ?qs j i \<in>
              fri_conditioned_agreement_indices i
                (fri_builder_conceptual_layers composition_roots
                  (channel_for_hash_map M) composition_final ! i)
                (fri_builder_conceptual_layers composition_roots
                  (channel_for_hash_map M) composition_final ! Suc i) b"
          using quantitative_old round_list_bound
          unfolding
            fri_conditioned_quantitative_residual_query_lists_at_value_def
            fri_conditioned_residual_query_lists_at_value_def Let_def
          by blast
        have query_entry: "?qs ! j = index (to_nat z)"
          using raws_len j_bound z_eq by simp
        have query_idx_eq:
            "fri_evidence_next_idx composition_roots ?qs j i =
              fri_evidence_next_idx composition_roots
                [index (to_nat z)] 0 i"
          using query_entry
          unfolding fri_evidence_next_idx_def fri_evidence_layer_idx_def
            fri_evidence_layer_len_def
          by simp
        have agreement_single:
            "fri_evidence_next_idx composition_roots
                [index (to_nat z)] 0 i \<in>
              fri_conditioned_agreement_indices i
                (fri_builder_conceptual_layers composition_roots
                  (channel_for_hash_map M) composition_final ! i)
                (fri_builder_conceptual_layers composition_roots
                  (channel_for_hash_map M) composition_final ! Suc i) b"
          using agreement_actual query_idx_eq by simp
        have nondegenerate_single:
            "fri_evidence_next_idx composition_roots
                [index (to_nat z)] 0 i \<notin>
              fri_conditioned_degenerate_agreement_indices i
                (fri_builder_conceptual_layers composition_roots
                  (channel_for_hash_map M) composition_final ! i)
                (fri_builder_conceptual_layers composition_roots
                  (channel_for_hash_map M) composition_final ! Suc i)"
        proof
          assume degenerate_single:
              "fri_evidence_next_idx composition_roots
                  [index (to_nat z)] 0 i \<in>
                fri_conditioned_degenerate_agreement_indices i
                  (fri_builder_conceptual_layers composition_roots
                    (channel_for_hash_map M) composition_final ! i)
                  (fri_builder_conceptual_layers composition_roots
                    (channel_for_hash_map M) composition_final ! Suc i)"
          have degenerate_actual:
              "fri_evidence_next_idx composition_roots ?qs j i \<in>
                fri_conditioned_degenerate_agreement_indices i
                  (fri_builder_conceptual_layers composition_roots
                    (channel_for_hash_map M) composition_final ! i)
                  (fri_builder_conceptual_layers composition_roots
                    (channel_for_hash_map M) composition_final ! Suc i)"
            using degenerate_single query_idx_eq by simp
          have degenerate_list:
              "?qs \<in>
                fri_conditioned_quantitative_degenerate_query_lists_at
                  (to_nat dg) composition_roots composition_final
                  (channel_for_hash_map M) i j"
            by (rule
              fri_conditioned_quantitative_residual_imp_degenerate[
                OF quantitative_old round_list_bound degenerate_actual])
          have composition_degenerate_old:
              "?qs \<in>
                ro_conditioned_composition_degenerate_query_lists_at
                  M dg composition_roots composition_final i j"
            using degenerate_list degree_bound
            unfolding
              ro_conditioned_composition_degenerate_query_lists_at_def
            by simp
          have degenerate_rel_old:
              "ro_conditioned_degenerate_absorbed_query_relation M k z"
            unfolding
              ro_conditioned_degenerate_absorbed_query_relation_def Let_def
            using clean_old no_initial_old trace_len alpha_len
              composition_len degree_bound header_chain_old query_chain_old
              raws_len i_bound composition_degenerate_old j_bound k_eq z_eq
            by blast
          have active_old:
              "hash_state_relation_active
                ro_conditioned_augmented_absorbed_query_relation M k z"
            unfolding hash_state_relation_active_def
              ro_conditioned_augmented_absorbed_query_relation_def
            using lookup_old degenerate_rel_old by blast
          show False using inactive_old active_old by contradiction
        qed
        have composition_final_target:
            "composition_final \<in> transcript_absorb_message_values M"
          using messages_target
          unfolding verifier_header_messages_def by simp
        let ?u =
          "if Suc i < length composition_roots
           then composition_roots ! Suc i else composition_final"
        have successor_target:
            "?u \<in> transcript_absorb_message_values M"
        proof (cases "Suc i < length composition_roots")
          case True
          then have root_mem:
              "composition_roots ! Suc i \<in> set composition_roots"
            by simp
          have root_target:
              "composition_roots ! Suc i \<in>
                transcript_absorb_message_values M"
            using composition_target root_mem by auto
          show ?thesis using True root_target by simp
        next
          case False
          then show ?thesis using composition_final_target by simp
        qed
        have z_target:
            "z \<in> hash_map_output_values (channel_for_hash_map M)"
        proof (rule hash_map_output_valuesI)
          show
            "fmlookup (HashMap (channel_for_hash_map M)) k = Some z"
            using lookup_old unfolding channel_for_hash_map_def by simp
        qed
        have candidate:
            "y \<in>
              ro_conditioned_composition_nondegenerate_challenge_candidates
                M x ?u z"
          unfolding
            ro_conditioned_composition_nondegenerate_challenge_candidates_def
            Let_def
          using trace_len alpha_len degree_bound composition_len i_bound
            challenge_chain_old True b_eq agreement_single
            nondegenerate_single
          by blast
        have
            "y \<in>
              ro_conditioned_composition_nondegenerate_challenge_drift_values
                M x"
          unfolding
            ro_conditioned_composition_nondegenerate_challenge_drift_values_def
          using successor_target z_target candidate by blast
        then show ?thesis by simp
      qed
    qed
  next
    assume degenerate_new:
      "ro_conditioned_degenerate_absorbed_query_relation
        (fmupd x y M) k z"
    have degenerate_old:
        "ro_conditioned_degenerate_absorbed_query_relation M k z"
      by (rule
        ro_conditioned_degenerate_absorbed_query_relation_fresh_update_pullback[
          OF fresh key_neq lookup_new degenerate_new no_target])
    have active_old:
        "hash_state_relation_active
          ro_conditioned_augmented_absorbed_query_relation M k z"
      unfolding hash_state_relation_active_def
        ro_conditioned_augmented_absorbed_query_relation_def
      using lookup_old degenerate_old by blast
    then show ?thesis using inactive_old by contradiction
  qed
qed

end
end
