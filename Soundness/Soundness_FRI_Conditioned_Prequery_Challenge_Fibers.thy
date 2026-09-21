theory Soundness_FRI_Conditioned_Prequery_Challenge_Fibers
  imports Stark.Soundness_FRI_Conditioned_Prequery_Drift_Base
begin

context soundness
begin

definition ro_conditioned_trace_nondegenerate_challenge_candidates
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f set"
where
  "ro_conditioned_trace_nondegenerate_challenge_candidates M x u z =
    {b. \<exists>fr roots last_value i ast.
      length roots = ceil_log clength \<and>
      i < length roots \<and>
      ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (fr # take (Suc i) roots) ast \<and>
      x = TraceFriChallenge i ast \<and>
      u = (if Suc i < length roots then roots ! Suc i else last_value) \<and>
      (let layers =
        fri_builder_conceptual_layers roots
          (channel_for_hash_map M) last_value;
        query_idx =
          fri_evidence_next_idx roots [index (to_nat z)] 0 i
       in query_idx \<in>
            fri_conditioned_agreement_indices i
              (layers ! i) (layers ! Suc i) b \<and>
          query_idx \<notin>
            fri_conditioned_degenerate_agreement_indices i
              (layers ! i) (layers ! Suc i))}"

definition ro_conditioned_composition_nondegenerate_challenge_candidates
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f set"
where
  "ro_conditioned_composition_nondegenerate_challenge_candidates M x u z =
    {b. \<exists>fr trace_roots trace_final as dg roots last_value i ast.
      length trace_roots = ceil_log clength \<and>
      length as = length spec \<and>
      to_nat dg \<le> maxDegree \<and>
      length roots = ceil_log (Suc (to_nat dg)) \<and>
      i < length roots \<and>
      ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots i) ast \<and>
      x = CompositionFriChallenge i ast \<and>
      u = (if Suc i < length roots then roots ! Suc i else last_value) \<and>
      (let layers =
        fri_builder_conceptual_layers roots
          (channel_for_hash_map M) last_value;
        query_idx =
          fri_evidence_next_idx roots [index (to_nat z)] 0 i
       in query_idx \<in>
            fri_conditioned_agreement_indices i
              (layers ! i) (layers ! Suc i) b \<and>
          query_idx \<notin>
            fri_conditioned_degenerate_agreement_indices i
              (layers ! i) (layers ! Suc i))}"



lemma fri_evidence_next_idx_same_length_singleton:
  assumes "length roots = length roots'"
  shows
    "fri_evidence_next_idx roots [q] 0 i =
      fri_evidence_next_idx roots' [q] 0 i"
  using assms
  unfolding fri_evidence_next_idx_def fri_evidence_layer_idx_def
    fri_evidence_layer_len_def
  by simp

lemma fri_builder_conceptual_layers_pair_eq:
  assumes len_eq: "length roots = length roots'"
    and i_bound: "i < length roots"
    and current_root: "roots ! i = roots' ! i"
    and next_left:
      "u = (if Suc i < length roots then roots ! Suc i else last_value)"
    and next_right:
      "u = (if Suc i < length roots' then roots' ! Suc i else last_value')"
  shows
    "fri_builder_conceptual_layers roots s last_value ! i =
       fri_builder_conceptual_layers roots' s last_value' ! i"
    "fri_builder_conceptual_layers roots s last_value ! Suc i =
       fri_builder_conceptual_layers roots' s last_value' ! Suc i"
proof -
  show current:
      "fri_builder_conceptual_layers roots s last_value ! i =
       fri_builder_conceptual_layers roots' s last_value' ! i"
    using i_bound len_eq current_root
    by (simp add: fri_builder_conceptual_layers_at)
  show next_layer:
      "fri_builder_conceptual_layers roots s last_value ! Suc i =
       fri_builder_conceptual_layers roots' s last_value' ! Suc i"
  proof (cases "Suc i < length roots")
    case True
    then have right_bound: "Suc i < length roots'"
      using len_eq by simp
    have next_root: "roots ! Suc i = roots' ! Suc i"
      using next_left next_right True right_bound by simp
    show ?thesis
      using True right_bound len_eq next_root
      by (simp add: fri_builder_conceptual_layers_at)
  next
    case False
    have left_final: "Suc i = length roots"
      using i_bound False by arith
    have right_final: "Suc i = length roots'"
      using left_final len_eq by simp
    have value_eq: "last_value = last_value'"
      using next_left next_right False left_final right_final by simp
    show ?thesis
      using left_final right_final len_eq value_eq
        fri_builder_conceptual_layers_final[of roots s last_value]
        fri_builder_conceptual_layers_final[of roots' s last_value']
      by simp
  qed
qed



lemma card_ro_conditioned_trace_nondegenerate_challenge_candidates_le_one:
  assumes clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
  shows
    "card (ro_conditioned_trace_nondegenerate_challenge_candidates
      M x u z) \<le> 1"
proof -
  let ?C =
    "ro_conditioned_trace_nondegenerate_challenge_candidates M x u z"
  have finite_C: "finite ?C" by simp
  have unique: "\<forall>b \<in> ?C. \<forall>b' \<in> ?C. b = b'"
  proof (intro ballI)
    fix b b'
    assume left: "b \<in> ?C" and right: "b' \<in> ?C"
    from left obtain fr roots last_value i ast where
      roots_len: "length roots = ceil_log clength"
      and i_bound: "i < length roots"
      and chain:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          (fr # take (Suc i) roots) ast"
      and x_eq: "x = TraceFriChallenge i ast"
      and successor:
        "u = (if Suc i < length roots then roots ! Suc i else last_value)"
      and agreement:
        "fri_evidence_next_idx roots [index (to_nat z)] 0 i \<in>
          fri_conditioned_agreement_indices i
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! i)
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! Suc i) b"
      and nondegenerate:
        "fri_evidence_next_idx roots [index (to_nat z)] 0 i \<notin>
          fri_conditioned_degenerate_agreement_indices i
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! i)
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! Suc i)"
      unfolding ro_conditioned_trace_nondegenerate_challenge_candidates_def
        Let_def
      by blast
    from right obtain fr' roots' last_value' i' ast' where
      roots_len': "length roots' = ceil_log clength"
      and i_bound': "i' < length roots'"
      and chain':
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          (fr' # take (Suc i') roots') ast'"
      and x_eq': "x = TraceFriChallenge i' ast'"
      and successor':
        "u =
          (if Suc i' < length roots' then roots' ! Suc i' else last_value')"
      and agreement':
        "fri_evidence_next_idx roots' [index (to_nat z)] 0 i' \<in>
          fri_conditioned_agreement_indices i'
            (fri_builder_conceptual_layers roots'
              (channel_for_hash_map M) last_value' ! i')
            (fri_builder_conceptual_layers roots'
              (channel_for_hash_map M) last_value' ! Suc i') b'"
      unfolding ro_conditioned_trace_nondegenerate_challenge_candidates_def
        Let_def
      by blast
    have i_eq: "i' = i" and ast_eq: "ast' = ast"
      using x_eq x_eq' by simp_all
    have chain'_same:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          (fr' # take (Suc i) roots') ast"
      using chain' i_eq ast_eq by simp
    have i_bound'_same: "i < length roots'"
      using i_bound' i_eq by simp
    have successor'_same:
        "u =
          (if Suc i < length roots' then roots' ! Suc i else last_value')"
      using successor' i_eq by simp
    have agreement'_same:
        "fri_evidence_next_idx roots' [index (to_nat z)] 0 i \<in>
          fri_conditioned_agreement_indices i
            (fri_builder_conceptual_layers roots'
              (channel_for_hash_map M) last_value' ! i)
            (fri_builder_conceptual_layers roots'
              (channel_for_hash_map M) last_value' ! Suc i) b'"
      using agreement' i_eq by simp
    have messages_eq:
        "fr # take (Suc i) roots = fr' # take (Suc i) roots'"
      by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
        OF clean no_initial chain chain'_same])
    have take_eq: "take (Suc i) roots = take (Suc i) roots'"
      using messages_eq by simp
    have take_nth_eq:
        "take (Suc i) roots ! i = take (Suc i) roots' ! i"
      using take_eq by simp
    have root_eq: "roots ! i = roots' ! i"
      using take_nth_eq i_bound i_bound'_same by simp
    have len_eq: "length roots = length roots'"
      using roots_len roots_len' by simp
    have layers_eq:
        "fri_builder_conceptual_layers roots
            (channel_for_hash_map M) last_value ! i =
          fri_builder_conceptual_layers roots'
            (channel_for_hash_map M) last_value' ! i"
        "fri_builder_conceptual_layers roots
            (channel_for_hash_map M) last_value ! Suc i =
          fri_builder_conceptual_layers roots'
            (channel_for_hash_map M) last_value' ! Suc i"
      by (rule fri_builder_conceptual_layers_pair_eq[
          OF len_eq i_bound root_eq successor successor'_same])+
    have query_idx_eq:
        "fri_evidence_next_idx roots [index (to_nat z)] 0 i =
          fri_evidence_next_idx roots' [index (to_nat z)] 0 i"
      by (rule fri_evidence_next_idx_same_length_singleton[OF len_eq])
    have agreement_right:
        "fri_evidence_next_idx roots [index (to_nat z)] 0 i \<in>
          fri_conditioned_agreement_indices i
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! i)
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! Suc i) b'"
      using agreement'_same layers_eq query_idx_eq by simp
    show "b = b'"
      by (rule fri_conditioned_nondegenerate_agreement_challenge_unique[
        OF agreement agreement_right nondegenerate])
  qed
  show ?thesis
    using card_le_Suc0_iff_eq[OF finite_C] unique by simp
qed



lemma card_ro_conditioned_composition_nondegenerate_challenge_candidates_le_one:
  assumes clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
  shows
    "card (ro_conditioned_composition_nondegenerate_challenge_candidates
      M x u z) \<le> 1"
proof -
  let ?C =
    "ro_conditioned_composition_nondegenerate_challenge_candidates M x u z"
  have finite_C: "finite ?C" by simp
  have unique: "\<forall>b \<in> ?C. \<forall>b' \<in> ?C. b = b'"
  proof (intro ballI)
    fix b b'
    assume left: "b \<in> ?C" and right: "b' \<in> ?C"
    from left obtain fr trace_roots trace_final as dg roots
        last_value i ast where
      trace_len: "length trace_roots = ceil_log clength"
      and alpha_len: "length as = length spec"
      and degree_bound: "to_nat dg \<le> maxDegree"
      and roots_len: "length roots = ceil_log (Suc (to_nat dg))"
      and i_bound: "i < length roots"
      and chain:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          (composition_fri_challenge_prefix_messages
            fr trace_roots trace_final as dg roots i) ast"
      and x_eq: "x = CompositionFriChallenge i ast"
      and successor:
        "u = (if Suc i < length roots then roots ! Suc i else last_value)"
      and agreement:
        "fri_evidence_next_idx roots [index (to_nat z)] 0 i \<in>
          fri_conditioned_agreement_indices i
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! i)
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! Suc i) b"
      and nondegenerate:
        "fri_evidence_next_idx roots [index (to_nat z)] 0 i \<notin>
          fri_conditioned_degenerate_agreement_indices i
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! i)
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! Suc i)"
      unfolding
        ro_conditioned_composition_nondegenerate_challenge_candidates_def
        Let_def
      by blast
    from right obtain fr' trace_roots' trace_final' as' dg' roots'
        last_value' i' ast' where
      trace_len': "length trace_roots' = ceil_log clength"
      and alpha_len': "length as' = length spec"
      and degree_bound': "to_nat dg' \<le> maxDegree"
      and roots_len': "length roots' = ceil_log (Suc (to_nat dg'))"
      and i_bound': "i' < length roots'"
      and chain':
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          (composition_fri_challenge_prefix_messages
            fr' trace_roots' trace_final' as' dg' roots' i') ast'"
      and x_eq': "x = CompositionFriChallenge i' ast'"
      and successor':
        "u =
          (if Suc i' < length roots' then roots' ! Suc i' else last_value')"
      and agreement':
        "fri_evidence_next_idx roots' [index (to_nat z)] 0 i' \<in>
          fri_conditioned_agreement_indices i'
            (fri_builder_conceptual_layers roots'
              (channel_for_hash_map M) last_value' ! i')
            (fri_builder_conceptual_layers roots'
              (channel_for_hash_map M) last_value' ! Suc i') b'"
      unfolding
        ro_conditioned_composition_nondegenerate_challenge_candidates_def
        Let_def
      by blast
    have i_eq: "i' = i" and ast_eq: "ast' = ast"
      using x_eq x_eq' by simp_all
    have chain'_same:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          (composition_fri_challenge_prefix_messages
            fr' trace_roots' trace_final' as' dg' roots' i) ast"
      using chain' i_eq ast_eq by simp
    have i_bound'_same: "i < length roots'"
      using i_bound' i_eq by simp
    have successor'_same:
        "u =
          (if Suc i < length roots' then roots' ! Suc i else last_value')"
      using successor' i_eq by simp
    have agreement'_same:
        "fri_evidence_next_idx roots' [index (to_nat z)] 0 i \<in>
          fri_conditioned_agreement_indices i
            (fri_builder_conceptual_layers roots'
              (channel_for_hash_map M) last_value' ! i)
            (fri_builder_conceptual_layers roots'
              (channel_for_hash_map M) last_value' ! Suc i) b'"
      using agreement' i_eq by simp
    have messages_eq:
        "composition_fri_challenge_prefix_messages
            fr trace_roots trace_final as dg roots i =
          composition_fri_challenge_prefix_messages
            fr' trace_roots' trace_final' as' dg' roots' i"
      by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
        OF clean no_initial chain chain'_same])
    have degree_prefix_eq:
        "dg = dg' \<and> take (Suc i) roots = take (Suc i) roots'"
      by (rule composition_fri_challenge_prefix_messages_degree_roots_eq[
        OF trace_len trace_len' alpha_len alpha_len' messages_eq])
    have degree_eq: "dg = dg'"
      using degree_prefix_eq by blast
    have take_eq: "take (Suc i) roots = take (Suc i) roots'"
      using degree_prefix_eq by blast
    have take_nth_eq:
        "take (Suc i) roots ! i = take (Suc i) roots' ! i"
      using take_eq by simp
    have root_eq: "roots ! i = roots' ! i"
      using take_nth_eq i_bound i_bound'_same by simp
    have len_eq: "length roots = length roots'"
      using roots_len roots_len' degree_eq by simp
    have layers_eq:
        "fri_builder_conceptual_layers roots
            (channel_for_hash_map M) last_value ! i =
          fri_builder_conceptual_layers roots'
            (channel_for_hash_map M) last_value' ! i"
        "fri_builder_conceptual_layers roots
            (channel_for_hash_map M) last_value ! Suc i =
          fri_builder_conceptual_layers roots'
            (channel_for_hash_map M) last_value' ! Suc i"
      by (rule fri_builder_conceptual_layers_pair_eq[
          OF len_eq i_bound root_eq successor successor'_same])+
    have query_idx_eq:
        "fri_evidence_next_idx roots [index (to_nat z)] 0 i =
          fri_evidence_next_idx roots' [index (to_nat z)] 0 i"
      by (rule fri_evidence_next_idx_same_length_singleton[OF len_eq])
    have agreement_right:
        "fri_evidence_next_idx roots [index (to_nat z)] 0 i \<in>
          fri_conditioned_agreement_indices i
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! i)
            (fri_builder_conceptual_layers roots
              (channel_for_hash_map M) last_value ! Suc i) b'"
      using agreement'_same layers_eq query_idx_eq by simp
    show "b = b'"
      by (rule fri_conditioned_nondegenerate_agreement_challenge_unique[
        OF agreement agreement_right nondegenerate])
  qed
  show ?thesis
    using card_le_Suc0_iff_eq[OF finite_C] unique by simp
qed



definition ro_conditioned_trace_nondegenerate_challenge_drift_values
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f set"
where
  "ro_conditioned_trace_nondegenerate_challenge_drift_values M x =
    (\<Union>u \<in> transcript_absorb_message_values M.
      \<Union>z \<in> hash_map_output_values (channel_for_hash_map M).
        ro_conditioned_trace_nondegenerate_challenge_candidates M x u z)"

definition ro_conditioned_composition_nondegenerate_challenge_drift_values
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f set"
where
  "ro_conditioned_composition_nondegenerate_challenge_drift_values M x =
    (\<Union>u \<in> transcript_absorb_message_values M.
      \<Union>z \<in> hash_map_output_values (channel_for_hash_map M).
        ro_conditioned_composition_nondegenerate_challenge_candidates
          M x u z)"

lemma card_bounded_pair_union:
  fixes A :: "'a set" and B :: "'b set" and C :: "'a \<Rightarrow> 'b \<Rightarrow> 'c set"
  assumes finite_A: "finite A"
    and finite_B: "finite B"
    and finite_C: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> finite (C a b)"
    and local: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> card (C a b) \<le> 1"
  shows "card (\<Union>a \<in> A. \<Union>b \<in> B. C a b) \<le> card A * card B"
proof -
  have finite_inner:
      "\<And>a. a \<in> A \<Longrightarrow> finite (\<Union>b \<in> B. C a b)"
    using finite_B finite_C by simp
  have inner_le:
      "\<And>a. a \<in> A \<Longrightarrow>
        card (\<Union>b \<in> B. C a b) \<le> (\<Sum>b \<in> B. card (C a b))"
    by (rule card_UN_le) (simp add: finite_B finite_C)
  have outer_le:
      "card (\<Union>a \<in> A. \<Union>b \<in> B. C a b) \<le>
        (\<Sum>a \<in> A. card (\<Union>b \<in> B. C a b))"
    by (rule card_UN_le)
      (simp add: finite_A finite_inner)
  also have "... \<le> (\<Sum>a \<in> A. \<Sum>b \<in> B. card (C a b))"
    by (intro sum_mono inner_le)
  also have "... \<le> (\<Sum>a \<in> A. \<Sum>b \<in> B. 1)"
    by (intro sum_mono local)
  also have "... = card A * card B"
    using finite_A finite_B by simp
  finally show ?thesis .
qed

lemma card_ro_conditioned_trace_nondegenerate_challenge_drift_values:
  assumes clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
  shows
    "card (ro_conditioned_trace_nondegenerate_challenge_drift_values M x)
      \<le> card (fmdom' M) * card (fmdom' M)"
proof -
  let ?U = "transcript_absorb_message_values M"
  let ?Z = "hash_map_output_values (channel_for_hash_map M)"
  let ?C =
    "\<lambda>u z. ro_conditioned_trace_nondegenerate_challenge_candidates M x u z"
  have pair_local: "\<And>u z. u \<in> ?U \<Longrightarrow> z \<in> ?Z \<Longrightarrow> card (?C u z) \<le> 1"
    by (rule
      card_ro_conditioned_trace_nondegenerate_challenge_candidates_le_one[
        OF clean no_initial])
  have pair_le: "card (\<Union>u \<in> ?U. \<Union>z \<in> ?Z. ?C u z) \<le> card ?U * card ?Z"
    apply (rule card_bounded_pair_union)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal for u z by (rule pair_local)
    done
  have U_le: "card ?U \<le> card (fmdom' M)"
    by (rule card_transcript_absorb_message_values_le)
  have Z_le: "card ?Z \<le> card (fmdom' M)"
    using card_hash_map_output_values_le_fmdom[
      of "channel_for_hash_map M"]
    unfolding channel_for_hash_map_def by simp
  have product_le:
      "card ?U * card ?Z \<le> card (fmdom' M) * card (fmdom' M)"
    by (rule mult_le_mono[OF U_le Z_le])
  show ?thesis
    unfolding
      ro_conditioned_trace_nondegenerate_challenge_drift_values_def
    by (rule order_trans[OF pair_le product_le])
qed

lemma card_ro_conditioned_composition_nondegenerate_challenge_drift_values:
  assumes clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
  shows
    "card
      (ro_conditioned_composition_nondegenerate_challenge_drift_values M x)
      \<le> card (fmdom' M) * card (fmdom' M)"
proof -
  let ?U = "transcript_absorb_message_values M"
  let ?Z = "hash_map_output_values (channel_for_hash_map M)"
  let ?C =
    "\<lambda>u z.
      ro_conditioned_composition_nondegenerate_challenge_candidates M x u z"
  have pair_local: "\<And>u z. u \<in> ?U \<Longrightarrow> z \<in> ?Z \<Longrightarrow> card (?C u z) \<le> 1"
    by (rule
      card_ro_conditioned_composition_nondegenerate_challenge_candidates_le_one[
        OF clean no_initial])
  have pair_le: "card (\<Union>u \<in> ?U. \<Union>z \<in> ?Z. ?C u z) \<le> card ?U * card ?Z"
    apply (rule card_bounded_pair_union)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal for u z by (rule pair_local)
    done
  have U_le: "card ?U \<le> card (fmdom' M)"
    by (rule card_transcript_absorb_message_values_le)
  have Z_le: "card ?Z \<le> card (fmdom' M)"
    using card_hash_map_output_values_le_fmdom[
      of "channel_for_hash_map M"]
    unfolding channel_for_hash_map_def by simp
  have product_le:
      "card ?U * card ?Z \<le> card (fmdom' M) * card (fmdom' M)"
    by (rule mult_le_mono[OF U_le Z_le])
  show ?thesis
    unfolding
      ro_conditioned_composition_nondegenerate_challenge_drift_values_def
    by (rule order_trans[OF pair_le product_le])
qed
end
end
