theory Soundness_FRI_Conditioned_Composition_Padding_Relation
  imports
    Stark.Soundness_FRI_Conditioned_Composition_Padding_Agreement
    Stark.Soundness_FRI_RO_Actual_Query_Trace_Composition_State_Relation
begin

context soundness
begin

lemma fri_padded_degree_bound_mono:
  assumes "d \<le> D"
  shows "fri_padded_degree_bound d \<le> fri_padded_degree_bound D"
proof -
  have logs: "ceil_log (Suc d) \<le> ceil_log (Suc D)"
    by (rule ceil_log_mono) (use assms in simp)
  have powers:
      "(2::nat) ^ ceil_log (Suc d) \<le> 2 ^ ceil_log (Suc D)"
    by (rule power_increasing[where a = "2::nat", OF logs]) simp
  show ?thesis
    unfolding fri_padded_degree_bound_def
    by (rule diff_le_mono[OF powers])
qed

lemma query_agreement_bound_for_mono:
  assumes "d \<le> D"
  shows "query_agreement_bound_for d \<le> query_agreement_bound_for D"
  using assms
  unfolding query_agreement_bound_for_def
  by simp

definition composition_padding_query_index_bound :: nat
where
  "composition_padding_query_index_bound =
    query_agreement_bound_for (fri_padded_degree_bound maxDegree)"

definition composition_padding_query_raw_fiber_bound :: nat
where
  "composition_padding_query_raw_fiber_bound =
    query_raw_preimage_card_envelope composition_padding_query_index_bound"

definition ro_composition_padding_header_query_lists
where
  "ro_composition_padding_header_query_lists M fr trace_roots trace_final as
      dg composition_roots composition_final =
    (if to_nat dg \<le> maxDegree
     then composition_padding_query_lists
       (conceptual_table (channel_for_hash_map M) fr (scale * clength))
       (ro_actual_query_composition_candidate
         (ro_trace_composition_header_data fr trace_roots trace_final as dg
           composition_roots composition_final)
         (channel_for_hash_map M))
       as (fri_padded_degree_bound (to_nat dg))
     else {})"

lemma ro_composition_padding_header_query_lists_query_index_update[simp]:
  "ro_composition_padding_header_query_lists
      (fmupd (QueryIndexChallenge c st) y M)
      fr trace_roots trace_final as dg composition_roots composition_final =
    ro_composition_padding_header_query_lists M
      fr trace_roots trace_final as dg composition_roots composition_final"
  unfolding ro_composition_padding_header_query_lists_def
    ro_actual_query_composition_candidate_def
    ro_trace_composition_header_data_def
  by simp

lemma ro_composition_padding_header_query_lists_cong:
  assumes
    "fr = fr' \<and> trace_roots = trace_roots' \<and>
      trace_final = trace_final' \<and> as = as' \<and> dg = dg' \<and>
      composition_roots = composition_roots' \<and>
      composition_final = composition_final'"
  shows
    "ro_composition_padding_header_query_lists M
        fr trace_roots trace_final as dg composition_roots composition_final =
      ro_composition_padding_header_query_lists M
        fr' trace_roots' trace_final' as' dg' composition_roots'
        composition_final'"
  using assms by simp

lemma ro_composition_padding_header_query_lists_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and messages_target:
      "set
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        \<subseteq> transcript_absorb_message_values M"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows
    "ro_composition_padding_header_query_lists (fmupd x y M)
        fr trace_roots trace_final as dg composition_roots composition_final =
      ro_composition_padding_header_query_lists M
        fr trace_roots trace_final as dg composition_roots composition_final"
proof -
  have fr_target: "fr \<in> transcript_absorb_message_values M"
    and composition_roots_target:
      "set composition_roots \<subseteq> transcript_absorb_message_values M"
    using messages_target
    unfolding verifier_header_messages_def
    by simp_all
  have original_eq:
      "conceptual_table (channel_for_hash_map (fmupd x y M))
          fr (scale * clength) =
        conceptual_table (channel_for_hash_map M)
          fr (scale * clength)"
    by (rule conceptual_table_fresh_update[
      OF fresh fr_target no_target])
  have composition_eq:
      "ro_actual_query_composition_candidate
          (ro_trace_composition_header_data fr trace_roots trace_final as dg
            composition_roots composition_final)
          (channel_for_hash_map (fmupd x y M)) =
        ro_actual_query_composition_candidate
          (ro_trace_composition_header_data fr trace_roots trace_final as dg
            composition_roots composition_final)
          (channel_for_hash_map M)"
  proof (cases "composition_roots = []")
    assume empty: "composition_roots = []"
    then show ?thesis
      unfolding ro_actual_query_composition_candidate_def
        ro_trace_composition_header_data_def
      by simp
  next
    assume nonempty: "composition_roots \<noteq> []"
    have composition_first_target:
        "hd composition_roots \<in> transcript_absorb_message_values M"
      by (rule set_mp[OF composition_roots_target])
        (rule hd_in_set[OF nonempty])
    show ?thesis
      unfolding ro_actual_query_composition_candidate_def
        ro_trace_composition_header_data_def
      using nonempty conceptual_table_fresh_update[
        OF fresh composition_first_target no_target]
      by simp
  qed
  show ?thesis
    unfolding ro_composition_padding_header_query_lists_def
    using original_eq composition_eq
    by simp
qed

lemma composition_padding_query_index_bound_mono:
  assumes degree_bound: "to_nat dg \<le> maxDegree"
  shows
    "query_agreement_bound_for
        (fri_padded_degree_bound (to_nat dg)) \<le>
      composition_padding_query_index_bound"
proof -
  have padded:
      "fri_padded_degree_bound (to_nat dg) \<le>
        fri_padded_degree_bound maxDegree"
    by (rule fri_padded_degree_bound_mono[OF degree_bound])
  show ?thesis
    unfolding composition_padding_query_index_bound_def
    by (rule query_agreement_bound_for_mono[OF padded])
qed

lemma ro_composition_padding_header_query_lists_position_card_bound:
  assumes i_bound: "i < rounds"
  shows
    "card
      (query_index_raw_list_position_values
        (ro_composition_padding_header_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final)
        i)
      \<le> composition_padding_query_raw_fiber_bound"
proof (cases "to_nat dg \<le> maxDegree")
  assume degree_bound: "to_nat dg \<le> maxDegree"
  let ?trace_table =
    "conceptual_table (channel_for_hash_map M) fr (scale * clength)"
  let ?composition_table =
    "ro_actual_query_composition_candidate
      (ro_trace_composition_header_data fr trace_roots trace_final as dg
        composition_roots composition_final)
      (channel_for_hash_map M)"
  let ?D = "fri_padded_degree_bound (to_nat dg)"
  let ?indices =
    "query_agreement_indices ?trace_table ?composition_table as"
  let ?Q =
    "ro_composition_padding_header_query_lists M
      fr trace_roots trace_final as dg composition_roots composition_final"
  show ?thesis
  proof (cases
      "trace_table_low_degree ?trace_table \<and>
        composition_table_low_degree ?D ?composition_table \<and>
        \<not> composition_table_low_degree maxDegree ?composition_table")
    assume condition:
        "trace_table_low_degree ?trace_table \<and>
          composition_table_low_degree ?D ?composition_table \<and>
          \<not> composition_table_low_degree maxDegree ?composition_table"
    then have trace_low: "trace_table_low_degree ?trace_table"
      and composition_low:
        "composition_table_low_degree ?D ?composition_table"
      and composition_not_low:
        "\<not> composition_table_low_degree maxDegree ?composition_table"
      by blast+
    have Q_eq: "?Q = query_index_lists_over ?indices"
      unfolding ro_composition_padding_header_query_lists_def
        composition_padding_query_lists_def
      by (simp only: if_P[OF degree_bound] if_P[OF condition])
    have pos_subset:
        "query_index_raw_list_position_values ?Q i \<subseteq>
          query_index_raw_preimage ?indices"
      unfolding Q_eq
      by (rule
        query_index_raw_list_position_values_query_index_lists_over_subset[
          OF i_bound])
    have card_le:
        "card (query_index_raw_list_position_values ?Q i) \<le>
          card (query_index_raw_preimage ?indices)"
      by (rule card_mono[OF _ pos_subset]) simp
    have indices_subset: "?indices \<subseteq> query_sample_space"
      unfolding query_agreement_indices_def by auto
    have raw_card:
        "card (query_index_raw_preimage ?indices) \<le>
          query_raw_preimage_card_envelope (card ?indices)"
      by (rule card_query_index_raw_preimage_le_query_envelope[
        OF indices_subset])
    have indices_card:
        "card ?indices \<le> query_agreement_bound_for ?D"
      by (rule
        query_agreement_indices_card_bound_for_if_composition_not_low_max[
          OF trace_low composition_low composition_not_low])
    have uniform:
        "query_agreement_bound_for ?D \<le>
          composition_padding_query_index_bound"
      by (rule composition_padding_query_index_bound_mono[
        OF degree_bound])
    have indices_uniform:
        "card ?indices \<le> composition_padding_query_index_bound"
      by (rule order_trans[OF indices_card uniform])
    have envelope:
        "query_raw_preimage_card_envelope (card ?indices) \<le>
          query_raw_preimage_card_envelope
            composition_padding_query_index_bound"
      by (rule query_raw_preimage_card_envelope_mono[OF indices_uniform])
    show ?thesis
      unfolding composition_padding_query_raw_fiber_bound_def
      by (rule order_trans[OF card_le])
        (rule order_trans[OF raw_card envelope])
  next
    assume not_condition:
        "\<not> (trace_table_low_degree ?trace_table \<and>
          composition_table_low_degree ?D ?composition_table \<and>
          \<not> composition_table_low_degree maxDegree ?composition_table)"
    have Q_empty: "?Q = {}"
      unfolding ro_composition_padding_header_query_lists_def
        composition_padding_query_lists_def
      by (simp only: if_P[OF degree_bound] if_not_P[OF not_condition])
    show ?thesis
      unfolding Q_empty query_index_raw_list_position_values_def
        query_index_raw_list_preimage_def
      by simp
  qed
next
  assume no_degree: "\<not> to_nat dg \<le> maxDegree"
  have Q_empty:
      "ro_composition_padding_header_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final = {}"
    unfolding ro_composition_padding_header_query_lists_def
    by (simp only: if_not_P[OF no_degree])
  show ?thesis
    unfolding Q_empty query_index_raw_list_position_values_def
      query_index_raw_list_preimage_def
    by simp
qed

definition composition_padding_absorbed_query_relation
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "composition_padding_absorbed_query_relation M x y \<longleftrightarrow>
    (let s = channel_for_hash_map M in
      \<not> hash_map_output_collision s \<and>
      PState adversary_initial_state \<notin> hash_map_output_values s \<and>
      (\<exists>fr trace_roots trace_final as dg composition_roots
          composition_final query_chunks raws query_start final j.
        length trace_roots = ceil_log clength \<and>
        length as = length spec \<and>
        length composition_roots = ceil_log (to_nat dg + 1) \<and>
        ro_absorb_lookup_chain s (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start \<and>
        ro_absorb_lookup_chain s query_start
          (List.concat (take j query_chunks)) final \<and>
        length raws = rounds \<and>
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_composition_padding_header_query_lists M
            fr trace_roots trace_final as dg composition_roots
            composition_final \<and>
        j < rounds \<and>
        x = QueryIndexChallenge j final \<and>
        y = raws ! j))"

lemma composition_padding_absorbed_query_relationD:
  assumes rel: "composition_padding_absorbed_query_relation M x y"
  obtains fr trace_roots trace_final as dg composition_roots
      composition_final query_chunks raws query_start final j where
    "\<not> hash_map_output_collision (channel_for_hash_map M)"
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
    "length trace_roots = ceil_log clength"
    "length as = length spec"
    "length composition_roots = ceil_log (to_nat dg + 1)"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state)
      (verifier_header_messages fr trace_roots trace_final as dg
        composition_roots composition_final)
      query_start"
    "ro_absorb_lookup_chain (channel_for_hash_map M) query_start
      (List.concat (take j query_chunks)) final"
    "length raws = rounds"
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
      ro_composition_padding_header_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final"
    "j < rounds"
    "x = QueryIndexChallenge j final"
    "y = raws ! j"
  using rel
  unfolding composition_padding_absorbed_query_relation_def Let_def
  by blast

lemma composition_padding_absorbed_query_relation_direct_fiber_card_bound:
  "card {y.
      hash_state_relation_direct_activation
        composition_padding_absorbed_query_relation M x y}
    \<le> composition_padding_query_raw_fiber_bound"
proof (cases "{y.
    hash_state_relation_direct_activation
      composition_padding_absorbed_query_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
    "hash_state_relation_direct_activation
      composition_padding_absorbed_query_relation M x y0"
    by blast
  have rel0:
      "composition_padding_absorbed_query_relation (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from composition_padding_absorbed_query_relationD[OF rel0]
  obtain fr0 trace_roots0 trace_final0 as0 dg0 composition_roots0
      composition_final0 query_chunks0 raws0 query_start0 final0 j0 where
    clean0:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y0 M))"
    and no_initial0:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y0 M))"
    and trace_len0: "length trace_roots0 = ceil_log clength"
    and alpha_len0: "length as0 = length spec"
    and composition_len0:
      "length composition_roots0 = ceil_log (to_nat dg0 + 1)"
    and header_chain0:
      "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state)
        (verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
          composition_roots0 composition_final0)
        query_start0"
    and query_chain0:
      "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y0 M))
        query_start0 (List.concat (take j0 query_chunks0)) final0"
    and raws_len0: "length raws0 = rounds"
    and raws_in0:
      "map (\<lambda>raw. index (to_nat raw)) raws0 \<in>
        ro_composition_padding_header_query_lists (fmupd x y0 M)
          fr0 trace_roots0 trace_final0 as0 dg0 composition_roots0
          composition_final0"
    and j0_bound: "j0 < rounds"
    and x0: "x = QueryIndexChallenge j0 final0"
    and y0_eq: "y0 = raws0 ! j0"
    .
  let ?Q0 =
    "ro_composition_padding_header_query_lists (fmupd x y0 M)
      fr0 trace_roots0 trace_final0 as0 dg0 composition_roots0
      composition_final0"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          composition_padding_absorbed_query_relation M x y}
        \<subseteq> query_index_raw_list_position_values ?Q0 j0"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          composition_padding_absorbed_query_relation M x y}"
    have rely:
        "composition_padding_absorbed_query_relation (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from composition_padding_absorbed_query_relationD[OF rely]
    obtain fr trace_roots trace_final as dg composition_roots
        composition_final query_chunks raws query_start final j where
      clean:
        "\<not> hash_map_output_collision
          (channel_for_hash_map (fmupd x y M))"
      and no_initial:
        "PState adversary_initial_state \<notin>
          hash_map_output_values (channel_for_hash_map (fmupd x y M))"
      and trace_len: "length trace_roots = ceil_log clength"
      and alpha_len: "length as = length spec"
      and composition_len:
        "length composition_roots = ceil_log (to_nat dg + 1)"
      and header_chain:
        "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start"
      and query_chain:
        "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
          query_start (List.concat (take j query_chunks)) final"
      and raws_len: "length raws = rounds"
      and raws_in:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_composition_padding_header_query_lists (fmupd x y M)
            fr trace_roots trace_final as dg composition_roots
            composition_final"
      and j_bound: "j < rounds"
      and x_eq: "x = QueryIndexChallenge j final"
      and y_eq: "y = raws ! j"
      .
    have j_eq: "j = j0"
      and final_eq: "final = final0"
      using x_eq x0 by simp_all
    have full0:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
              composition_roots0 composition_final0 @
            List.concat (take j0 query_chunks0))
          final0"
      by (rule ro_absorb_lookup_chain_append[
            OF header_chain0 query_chain0])
    have header_chain_base:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start"
      using header_chain unfolding x0
      by simp
    have query_chain_base:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          query_start (List.concat (take j0 query_chunks)) final0"
      using query_chain j_eq final_eq unfolding x0
      by simp
    have header_chain_ref:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start"
      using header_chain_base unfolding x0 by simp
    have query_chain_ref:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          query_start (List.concat (take j0 query_chunks)) final0"
      using query_chain_base unfolding x0 by simp
    have full:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
              composition_roots composition_final @
            List.concat (take j0 query_chunks))
          final0"
      by (rule ro_absorb_lookup_chain_append[
            OF header_chain_ref query_chain_ref])
    have messages_eq:
        "verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final @
          List.concat (take j0 query_chunks) =
         verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
            composition_roots0 composition_final0 @
          List.concat (take j0 query_chunks0)"
      by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
            OF clean0 no_initial0 full full0])
    have header_eq:
        "verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final =
         verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
            composition_roots0 composition_final0"
      by (rule verifier_header_messages_prefix_eq_from_append_eq[
            OF trace_len trace_len0 alpha_len alpha_len0
              composition_len composition_len0 messages_eq])
    have fields_eq:
        "fr = fr0 \<and> trace_roots = trace_roots0 \<and>
         trace_final = trace_final0 \<and> as = as0 \<and> dg = dg0 \<and>
         composition_roots = composition_roots0 \<and>
         composition_final = composition_final0"
      by (rule verifier_header_messages_relevant_fields_eq[
            OF trace_len trace_len0 alpha_len alpha_len0
              composition_len composition_len0 header_eq])
    have Q_eq:
        "ro_composition_padding_header_query_lists (fmupd x y M)
            fr trace_roots trace_final as dg composition_roots
            composition_final = ?Q0"
      using fields_eq unfolding x0 by simp
    have raws_preimage:
        "raws \<in> query_index_raw_list_preimage ?Q0"
      unfolding query_index_raw_list_preimage_def
      using raws_len raws_in Q_eq by simp
    show "y \<in> query_index_raw_list_position_values ?Q0 j0"
      unfolding query_index_raw_list_position_values_def
      using raws_preimage y_eq j_eq j0_bound by blast
  qed
  have finite_Q0:
      "finite (query_index_raw_list_position_values ?Q0 j0)"
    by simp
  have card_le:
      "card {y.
        hash_state_relation_direct_activation
          composition_padding_absorbed_query_relation M x y}
        \<le> card (query_index_raw_list_position_values ?Q0 j0)"
    by (rule card_mono[OF finite_Q0 subset])
  have position_le:
      "card (query_index_raw_list_position_values ?Q0 j0)
        \<le> composition_padding_query_raw_fiber_bound"
    unfolding x0
    by (rule
        ro_composition_padding_header_query_lists_position_card_bound[
          OF j0_bound])
  show ?thesis
    by (rule order_trans[OF card_le position_le])
qed

lemma composition_padding_absorbed_query_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "composition_padding_absorbed_query_relation (fmupd x y M) k z"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows "composition_padding_absorbed_query_relation M k z"
proof -
  from composition_padding_absorbed_query_relationD[OF rel]
  obtain fr trace_roots trace_final as dg composition_roots
      composition_final query_chunks raws query_start final j where
    clean_new:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
    and no_initial_new:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
    and trace_len: "length trace_roots = ceil_log clength"
    and alpha_len: "length as = length spec"
    and composition_len:
      "length composition_roots = ceil_log (to_nat dg + 1)"
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
        ro_composition_padding_header_query_lists (fmupd x y M)
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    and j_bound: "j < rounds"
    and k_eq: "k = QueryIndexChallenge j final"
    and z_eq: "z = raws ! j"
    .
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
  have full_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final @
          List.concat (take j query_chunks))
        final"
    by (rule ro_absorb_lookup_chain_fresh_update_pullback[
          OF fresh full_chain_new final_target no_target])
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
  have query_lists_eq:
      "ro_composition_padding_header_query_lists (fmupd x y M)
          fr trace_roots trace_final as dg composition_roots
          composition_final =
        ro_composition_padding_header_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    by (rule ro_composition_padding_header_query_lists_fresh_update[
          OF fresh messages_target no_target])
  have raws_in_old:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_composition_padding_header_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    using raws_in_new query_lists_eq by simp
  show ?thesis
    unfolding composition_padding_absorbed_query_relation_def Let_def
    using clean_old no_initial_old trace_len alpha_len
      composition_len header_chain_old query_chain_old raws_len
      raws_in_old j_bound k_eq z_eq
    by blast
qed


lemma composition_padding_absorbed_query_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        composition_padding_absorbed_query_relation M x y"
  shows "y \<in> first_root_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> first_root_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        composition_padding_absorbed_query_relation (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        composition_padding_absorbed_query_relation M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "composition_padding_absorbed_query_relation (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def
    by blast+
  have rel_old:
      "composition_padding_absorbed_query_relation M k z"
    by (rule
      composition_padding_absorbed_query_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
      "hash_state_relation_active
        composition_padding_absorbed_query_relation M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed


lemma composition_padding_absorbed_query_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        composition_padding_absorbed_query_relation M x y}
      \<le> 5 * card (fmdom' M) + 2"
proof -
  have subset:
      "{y.
        hash_state_relation_drift_activation
          composition_padding_absorbed_query_relation M x y}
        \<subseteq> first_root_relation_drift_targets M x"
    using
      composition_padding_absorbed_query_relation_drift_activation_imp_target[
        OF fresh]
    by blast
  have
      "card {y.
        hash_state_relation_drift_activation
          composition_padding_absorbed_query_relation M x y}
        \<le> card (first_root_relation_drift_targets M x)"
    by (rule card_mono[OF finite_first_root_relation_drift_targets subset])
  also have "... \<le> 5 * card (fmdom' M) + 2"
    by (rule card_first_root_relation_drift_targets_le)
  finally show ?thesis .
qed

lemma composition_padding_bounded_transition_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_transition
        (conditioned_fri_relation_bounded L
          composition_padding_absorbed_query_relation)
        M (fmupd x y M)}
      \<le> composition_padding_query_raw_fiber_bound + (5 * L + 2)"
proof (rule conditioned_fri_bounded_transition_fiber_card_bound[
    OF fresh])
  assume "card (fmdom' M) \<le> L"
  show
    "card {y.
      hash_state_relation_direct_activation
        composition_padding_absorbed_query_relation M x y}
      \<le> composition_padding_query_raw_fiber_bound"
    by (rule
      composition_padding_absorbed_query_relation_direct_fiber_card_bound)
next
  assume domain: "card (fmdom' M) \<le> L"
  have
    "card {y.
      hash_state_relation_drift_activation
        composition_padding_absorbed_query_relation M x y}
      \<le> 5 * card (fmdom' M) + 2"
    by (rule
      composition_padding_absorbed_query_relation_drift_fiber_card_bound[
        OF fresh])
  also have "... \<le> 5 * L + 2"
    by (rule add_right_mono)
      (rule mult_left_mono[OF domain], simp)
  finally show
    "card {y.
      hash_state_relation_drift_activation
        composition_padding_absorbed_query_relation M x y}
      \<le> 5 * L + 2"
    .
qed

lemma
  wp_ro_checked_staged_transcript_with_query_witnesses_composition_padding_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded q
          composition_padding_absorbed_query_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state
      \<le> nnreal
        (q * (composition_padding_query_raw_fiber_bound + (5 * q + 2))) /
        nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B =
    "composition_padding_query_raw_fiber_bound + (5 * ?Q + 2)"
  have steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition
            (conditioned_fri_relation_bounded ?Q
              composition_padding_absorbed_query_relation)
            M (fmupd x y M)}
          \<le> ?B"
    by (rule composition_padding_bounded_transition_fiber_card_bound)
  have bound:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (conditioned_fri_relation_bounded ?Q
            composition_padding_absorbed_query_relation)
          (HashMap adversary_initial_state))
        adversary_initial_state
        \<le> nnreal (?Q * ?B) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound_all_rounds[
        OF wf controlled steps])
  show ?thesis
    using bound unfolding q_def by simp
qed

lemma composition_padding_absorbed_query_relation_activeI:
  assumes clean:
      "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
    and trace_len: "length trace_roots = ceil_log clength"
    and as_len: "length as = length spec"
    and composition_len:
      "length composition_roots = ceil_log (to_nat dg + 1)"
    and header_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        query_start"
    and query_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M) query_start
        (List.concat (take j query_chunks)) final"
    and raws_len: "length raws = rounds"
    and member:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_composition_padding_header_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    and j_bound: "j < rounds"
    and lookup:
      "fmlookup M (QueryIndexChallenge j final) = Some (raws ! j)"
  shows
    "hash_state_relation_active
      composition_padding_absorbed_query_relation M
      (QueryIndexChallenge j final) (raws ! j)"
proof -
  have rel:
      "composition_padding_absorbed_query_relation M
        (QueryIndexChallenge j final) (raws ! j)"
    unfolding composition_padding_absorbed_query_relation_def Let_def
    using clean no_initial trace_len as_len composition_len header_chain
      query_chain raws_len member j_bound
    by blast
  show ?thesis
    unfolding hash_state_relation_active_def
    using lookup rel by blast
qed

end
end
