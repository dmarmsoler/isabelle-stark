theory Soundness_FRI_Conditioned_Prequery_Header
  imports
    Stark.Soundness_FRI_Conditioned_Query_Start
    Stark.Soundness_FRI_RO_Actual_Query_Trace_Composition_Adaptive_Query_Budget
begin

context soundness
begin

definition ro_conditioned_header_data
  :: "'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f staged_proof_data"
where
  "ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
      composition_roots composition_bs composition_final =
    \<lparr>staged_trace_root = fr,
     staged_trace_fri_roots = trace_roots,
     staged_trace_fri_challenges = trace_bs,
     staged_trace_final = trace_final,
     staged_alphas = as,
     staged_degree = dg,
     staged_composition_fri_roots = composition_roots,
     staged_composition_fri_challenges = composition_bs,
     staged_composition_final = composition_final,
     staged_query_chunks = []\<rparr>"

definition ro_conditioned_header_residual_query_lists
where
  "ro_conditioned_header_residual_query_lists M
      fr trace_roots trace_bs trace_final as dg
      composition_roots composition_bs composition_final =
    fri_conditioned_combined_query_head_lists
      (fr, [], fr) (channel_for_hash_map M)
      (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final)
      (channel_for_hash_map M)"

lemma ro_conditioned_header_data_fields[simp]:
  "staged_trace_root
      (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final) = fr"
  "staged_trace_fri_roots
      (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final) = trace_roots"
  "staged_trace_fri_challenges
      (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final) = trace_bs"
  "staged_trace_final
      (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final) = trace_final"
  "staged_alphas
      (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final) = as"
  "staged_degree
      (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final) = dg"
  "staged_composition_fri_roots
      (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final) = composition_roots"
  "staged_composition_fri_challenges
      (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final) = composition_bs"
  "staged_composition_final
      (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final) = composition_final"
  unfolding ro_conditioned_header_data_def by simp_all

lemma ro_conditioned_header_residual_query_lists_query_index_update[simp]:
  "ro_conditioned_header_residual_query_lists
      (fmupd (QueryIndexChallenge c st) y M)
      fr trace_roots trace_bs trace_final as dg
      composition_roots composition_bs composition_final =
    ro_conditioned_header_residual_query_lists M
      fr trace_roots trace_bs trace_final as dg
      composition_roots composition_bs composition_final"
  unfolding ro_conditioned_header_residual_query_lists_def
    fri_conditioned_combined_query_head_lists_def
    fri_conditioned_trace_query_head_lists_def
    fri_conditioned_composition_query_head_lists_def
    fri_conditioned_trace_residual_query_lists_def
    fri_conditioned_composition_residual_query_lists_def
    fri_conditioned_quantitative_residual_query_lists_def
    fri_conditioned_quantitative_residual_query_lists_at_def
    fri_builder_conceptual_layers_def
  by simp

lemma fri_builder_conceptual_layers_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and roots_target: "set roots \<subseteq> transcript_absorb_message_values M"
    and no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows
    "fri_builder_conceptual_layers roots
        (channel_for_hash_map (fmupd x y M)) final_value =
      fri_builder_conceptual_layers roots
        (channel_for_hash_map M) final_value"
proof -
  have no_first: "y \<notin> first_root_relation_drift_targets M x"
    using no_target
    unfolding conditioned_fri_relation_drift_targets_def by blast
  have tables:
      "map
        (\<lambda>j. conceptual_table
          (channel_for_hash_map (fmupd x y M)) (roots ! j)
          (length (fri_canonical_domain_at j)))
        [0..<length roots] =
       map
        (\<lambda>j. conceptual_table
          (channel_for_hash_map M) (roots ! j)
          (length (fri_canonical_domain_at j)))
        [0..<length roots]"
  proof (rule map_cong)
    show "[0..<length roots] = [0..<length roots]" by simp
    fix j
    assume "j \<in> set [0..<length roots]"
    then have j_bound: "j < length roots"
      by simp
    have root_target:
        "roots ! j \<in> transcript_absorb_message_values M"
      by (rule set_mp[OF roots_target]) (rule nth_mem[OF j_bound])
    show
      "conceptual_table
          (channel_for_hash_map (fmupd x y M)) (roots ! j)
          (length (fri_canonical_domain_at j)) =
       conceptual_table
          (channel_for_hash_map M) (roots ! j)
          (length (fri_canonical_domain_at j))"
      by (rule conceptual_table_fresh_update[
          OF fresh root_target no_first])
  qed
  show ?thesis
    unfolding fri_builder_conceptual_layers_def
    using tables by simp
qed

lemma fri_conditioned_quantitative_residual_query_lists_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and roots_target: "set roots \<subseteq> transcript_absorb_message_values M"
    and no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows
    "fri_conditioned_quantitative_residual_query_lists d roots challenges
        final_value (channel_for_hash_map (fmupd x y M)) =
      fri_conditioned_quantitative_residual_query_lists d roots challenges
        final_value (channel_for_hash_map M)"
proof -
  have layers:
      "fri_builder_conceptual_layers roots
          (channel_for_hash_map (fmupd x y M)) final_value =
       fri_builder_conceptual_layers roots
          (channel_for_hash_map M) final_value"
    by (rule fri_builder_conceptual_layers_fresh_update[
        OF fresh roots_target no_target])
  show ?thesis
    unfolding fri_conditioned_quantitative_residual_query_lists_def
    using layers by simp
qed

lemma ro_conditioned_header_residual_query_lists_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and messages_target:
      "set
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        \<subseteq> transcript_absorb_message_values M"
    and no_target: "y \<notin> conditioned_fri_relation_drift_targets M x"
  shows
    "ro_conditioned_header_residual_query_lists (fmupd x y M)
        fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final =
      ro_conditioned_header_residual_query_lists M
        fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final"
proof -
  have trace_target:
      "set trace_roots \<subseteq> transcript_absorb_message_values M"
    and composition_target:
      "set composition_roots \<subseteq> transcript_absorb_message_values M"
    using messages_target
    unfolding verifier_header_messages_def by simp_all
  have trace_core:
      "fri_conditioned_quantitative_residual_query_lists
          (clength - 1) trace_roots trace_bs trace_final
          (channel_for_hash_map (fmupd x y M)) =
       fri_conditioned_quantitative_residual_query_lists
          (clength - 1) trace_roots trace_bs trace_final
          (channel_for_hash_map M)"
    by (rule
        fri_conditioned_quantitative_residual_query_lists_fresh_update[
          OF fresh trace_target no_target])
  have trace:
      "fri_conditioned_trace_residual_query_lists
          (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
            composition_roots composition_bs composition_final)
          (channel_for_hash_map (fmupd x y M)) =
       fri_conditioned_trace_residual_query_lists
          (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
            composition_roots composition_bs composition_final)
          (channel_for_hash_map M)"
    using trace_core
    unfolding fri_conditioned_trace_residual_query_lists_def
    by simp
  have composition:
      "fri_conditioned_composition_residual_query_lists
          (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
            composition_roots composition_bs composition_final)
          (channel_for_hash_map (fmupd x y M)) =
       fri_conditioned_composition_residual_query_lists
          (ro_conditioned_header_data fr trace_roots trace_bs trace_final as dg
            composition_roots composition_bs composition_final)
          (channel_for_hash_map M)"
    unfolding fri_conditioned_composition_residual_query_lists_def
    using
      fri_conditioned_quantitative_residual_query_lists_fresh_update[
        OF fresh composition_target no_target,
        where d="to_nat dg" and challenges=composition_bs
          and final_value=composition_final]
    by simp
  show ?thesis
    unfolding ro_conditioned_header_residual_query_lists_def
      fri_conditioned_combined_query_head_lists_def
      fri_conditioned_trace_query_head_lists_def
      fri_conditioned_composition_query_head_lists_def
    using trace composition by simp
qed

lemma ro_conditioned_header_residual_query_lists_cong:
  assumes fields:
    "fr = fr' \<and> trace_roots = trace_roots' \<and> trace_bs = trace_bs' \<and>
     trace_final = trace_final' \<and> as = as' \<and> dg = dg' \<and>
     composition_roots = composition_roots' \<and>
     composition_bs = composition_bs' \<and>
     composition_final = composition_final'"
  shows
    "ro_conditioned_header_residual_query_lists M
        fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final =
      ro_conditioned_header_residual_query_lists M
        fr' trace_roots' trace_bs' trace_final' as' dg'
        composition_roots' composition_bs' composition_final'"
  using fields by simp

lemma ro_conditioned_header_residual_query_lists_relation_fiber_bound:
  assumes trace_roots:
      "length trace_roots = ceil_log clength"
    and trace_challenges:
      "length trace_bs = ceil_log clength"
    and composition_roots:
      "length composition_roots = ceil_log (Suc (to_nat dg))"
    and composition_challenges:
      "length composition_bs = ceil_log (Suc (to_nat dg))"
  shows
    "query_index_raw_list_relation_fiber_bound
      (ro_conditioned_header_residual_query_lists M
        fr trace_roots trace_bs trace_final as dg
        composition_roots composition_bs composition_final) \<le>
      rounds *
        query_raw_preimage_card_envelope
          (rounds *
            (fri_conditioned_residual_query_list_card_bound (clength - 1) +
             fri_conditioned_residual_query_list_card_bound maxDegree))"
  unfolding ro_conditioned_header_residual_query_lists_def
  by (rule
      fri_conditioned_combined_query_head_lists_relation_fiber_bound)
    (use trace_roots trace_challenges composition_roots
      composition_challenges in simp_all)

definition ro_conditioned_trace_challenge_evidence
where
  "ro_conditioned_trace_challenge_evidence M fr roots challenges \<longleftrightarrow>
    length challenges = length roots \<and>
    (\<forall>j < length roots. \<exists>final.
      ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state) (fr # take (Suc j) roots) final \<and>
      fmlookup M (TraceFriChallenge j final) = Some (challenges ! j))"

definition ro_conditioned_composition_challenge_evidence
where
  "ro_conditioned_composition_challenge_evidence M
      fr trace_roots trace_final as dg roots challenges \<longleftrightarrow>
    length challenges = length roots \<and>
    (\<forall>j < length roots. \<exists>final.
      ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots j)
        final \<and>
      fmlookup M (CompositionFriChallenge j final) =
        Some (challenges ! j))"

lemma ro_conditioned_trace_challenge_evidence_unique:
  assumes left:
      "ro_conditioned_trace_challenge_evidence M fr roots left_bs"
    and right:
      "ro_conditioned_trace_challenge_evidence M fr roots right_bs"
  shows "left_bs = right_bs"
proof (rule nth_equalityI)
  show "length left_bs = length right_bs"
    using left right
    unfolding ro_conditioned_trace_challenge_evidence_def by simp
  fix i
  assume i_bound: "i < length left_bs"
  have root_bound: "i < length roots"
    using left i_bound
    unfolding ro_conditioned_trace_challenge_evidence_def by simp
  from left root_bound obtain left_final where
    left_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state) (fr # take (Suc i) roots)
        left_final"
    and left_lookup:
      "fmlookup M (TraceFriChallenge i left_final) = Some (left_bs ! i)"
    unfolding ro_conditioned_trace_challenge_evidence_def by blast
  from right root_bound obtain right_final where
    right_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state) (fr # take (Suc i) roots)
        right_final"
    and right_lookup:
      "fmlookup M (TraceFriChallenge i right_final) =
        Some (right_bs ! i)"
    unfolding ro_conditioned_trace_challenge_evidence_def by blast
  have final_eq: "left_final = right_final"
    by (rule ro_absorb_lookup_chain_functional[
        OF left_chain right_chain])
  show "left_bs ! i = right_bs ! i"
    using left_lookup right_lookup final_eq by simp
qed

lemma ro_conditioned_composition_challenge_evidence_unique:
  assumes left:
      "ro_conditioned_composition_challenge_evidence M
        fr trace_roots trace_final as dg roots left_bs"
    and right:
      "ro_conditioned_composition_challenge_evidence M
        fr trace_roots trace_final as dg roots right_bs"
  shows "left_bs = right_bs"
proof (rule nth_equalityI)
  show "length left_bs = length right_bs"
    using left right
    unfolding ro_conditioned_composition_challenge_evidence_def by simp
  fix i
  assume i_bound: "i < length left_bs"
  have root_bound: "i < length roots"
    using left i_bound
    unfolding ro_conditioned_composition_challenge_evidence_def by simp
  from left root_bound obtain left_final where
    left_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots i)
        left_final"
    and left_lookup:
      "fmlookup M (CompositionFriChallenge i left_final) =
        Some (left_bs ! i)"
    unfolding ro_conditioned_composition_challenge_evidence_def by blast
  from right root_bound obtain right_final where
    right_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots i)
        right_final"
    and right_lookup:
      "fmlookup M (CompositionFriChallenge i right_final) =
        Some (right_bs ! i)"
    unfolding ro_conditioned_composition_challenge_evidence_def by blast
  have final_eq: "left_final = right_final"
    by (rule ro_absorb_lookup_chain_functional[
        OF left_chain right_chain])
  show "left_bs ! i = right_bs ! i"
    using left_lookup right_lookup final_eq by simp
qed

end
end
