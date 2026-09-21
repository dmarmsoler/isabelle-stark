(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Zero_Round_State_Relation.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Zero_Round_State_Relation
  imports
    Soundness_FRI_RO_Actual_Query_Zero_Round_Query_Classification
    Soundness_FRI_First_Root_RO_Prequery_Closed_Bound
begin

text \<open>
  Adaptive prequery relation for the zero trace-FRI branch.  The relation is
  fixed by the domain-separated absorption of the initial trace root and the
  structured verifier header.  It uses only prefix conceptual tables and never
  reconstructs a complete committed table from sampled openings.
\<close>

context soundness
begin

definition ro_zero_round_header_bad_query_lists
where
  "ro_zero_round_header_bad_query_lists M fr trace_final =
    (let table =
      conceptual_table (channel_for_hash_map M) fr (scale * clength)
     in if \<not> trace_table_low_degree table
        then query_index_lists_over
          (fri_final_value_agreement_set table trace_final)
        else {})"

lemma ro_zero_round_header_bad_query_lists_query_index_update[simp]:
  "ro_zero_round_header_bad_query_lists
      (fmupd (QueryIndexChallenge c st) y M) fr trace_final =
    ro_zero_round_header_bad_query_lists M fr trace_final"
  unfolding ro_zero_round_header_bad_query_lists_def
  by simp

lemma ro_zero_round_header_bad_query_lists_subset:
  "ro_zero_round_header_bad_query_lists M fr trace_final
    \<subseteq> fri_query_index_list_space"
  unfolding ro_zero_round_header_bad_query_lists_def Let_def
    query_index_lists_over_def fri_query_index_list_space_def
    fri_final_value_agreement_set_def query_sample_space_def
  by auto

lemma ro_zero_round_header_bad_query_lists_card_bound:
  assumes zero: "ceil_log clength = 0"
  shows
    "card (ro_zero_round_header_bad_query_lists M fr trace_final)
      \<le> (query_sample_space_size - 1) ^ rounds"
proof (cases
    "trace_table_low_degree
      (conceptual_table (channel_for_hash_map M) fr (scale * clength))")
  case True
  then show ?thesis
    unfolding ro_zero_round_header_bad_query_lists_def Let_def
    by simp
next
  case False
  let ?data =
    "ro_trace_composition_header_data fr [] trace_final []
      0 [] 0"
  have table_eq:
    "ro_actual_query_zero_round_trace_table
        ?data (channel_for_hash_map M) =
      conceptual_table (channel_for_hash_map M) fr (scale * clength)"
    unfolding ro_actual_query_zero_round_trace_table_def
      ro_trace_composition_header_data_def
    by simp
  have family_eq:
    "ro_zero_round_header_bad_query_lists M fr trace_final =
      ro_actual_query_zero_round_bad_query_lists
        (fr, [], fr) (channel_for_hash_map M) ?data
        (channel_for_hash_map M)"
    unfolding ro_zero_round_header_bad_query_lists_def
      ro_actual_query_zero_round_bad_query_lists_def
      ro_actual_query_zero_round_trace_query_lists_def
      ro_actual_query_zero_round_trace_indices_def
      ro_actual_query_zero_round_trace_table_def
      ro_trace_composition_header_data_def Let_def
    by simp
  have bound:
      "card
        (ro_actual_query_zero_round_bad_query_lists
          (fr, [], fr) (channel_for_hash_map M) ?data
          (channel_for_hash_map M))
        \<le> (query_sample_space_size - 1) ^ rounds"
    by (rule ro_actual_query_zero_round_bad_query_lists_card_bound[
      OF zero])
  show ?thesis
    by (subst family_eq) (rule bound)
qed

lemma ro_zero_round_header_bad_query_lists_position_card_bound:
  assumes zero: "ceil_log clength = 0"
    and i_bound: "i < rounds"
  shows
    "card
      (query_index_raw_list_position_values
        (ro_zero_round_header_bad_query_lists M fr trace_final) i)
      \<le> query_raw_preimage_card_envelope
          (query_sample_space_size - 1)"
proof -
  let ?data =
    "ro_trace_composition_header_data fr [] trace_final []
      0 [] 0"
  have family_eq:
    "ro_zero_round_header_bad_query_lists M fr trace_final =
      ro_actual_query_zero_round_bad_query_lists
        (fr, [], fr) (channel_for_hash_map M) ?data
        (channel_for_hash_map M)"
    unfolding ro_zero_round_header_bad_query_lists_def
      ro_actual_query_zero_round_bad_query_lists_def
      ro_actual_query_zero_round_trace_query_lists_def
      ro_actual_query_zero_round_trace_indices_def
      ro_actual_query_zero_round_trace_table_def
      ro_trace_composition_header_data_def Let_def
    by simp
  have bound:
      "card
        (query_index_raw_list_position_values
          (ro_actual_query_zero_round_bad_query_lists
            (fr, [], fr) (channel_for_hash_map M) ?data
            (channel_for_hash_map M)) i)
        \<le> query_raw_preimage_card_envelope
            (query_sample_space_size - 1)"
    by (rule
      ro_actual_query_zero_round_bad_query_lists_position_card_bound[
        OF zero i_bound])
  show ?thesis
    by (subst family_eq) (rule bound)
qed

definition zero_round_absorbed_query_relation
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "zero_round_absorbed_query_relation M x y \<longleftrightarrow>
    (let s = channel_for_hash_map M in
      \<not> hash_map_output_collision s \<and>
      PState adversary_initial_state \<notin> hash_map_output_values s \<and>
      (\<exists>fr trace_final as dg composition_roots composition_final
          query_chunks raws query_start final j.
        ceil_log clength = 0 \<and>
        length as = length spec \<and>
        length composition_roots = ceil_log (to_nat dg + 1) \<and>
        ro_absorb_lookup_chain s (PState adversary_initial_state)
          (verifier_header_messages fr [] trace_final as dg
            composition_roots composition_final)
          query_start \<and>
        ro_absorb_lookup_chain s query_start
          (List.concat (take j query_chunks)) final \<and>
        length raws = rounds \<and>
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_zero_round_header_bad_query_lists M fr trace_final \<and>
        j < rounds \<and>
        x = QueryIndexChallenge j final \<and>
        y = raws ! j))"

lemma zero_round_absorbed_query_relationD:
  assumes rel: "zero_round_absorbed_query_relation M x y"
  obtains fr trace_final as dg composition_roots composition_final
      query_chunks raws query_start final j where
    "\<not> hash_map_output_collision (channel_for_hash_map M)"
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
    "ceil_log clength = 0"
    "length as = length spec"
    "length composition_roots = ceil_log (to_nat dg + 1)"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state)
      (verifier_header_messages fr [] trace_final as dg
        composition_roots composition_final)
      query_start"
    "ro_absorb_lookup_chain (channel_for_hash_map M) query_start
      (List.concat (take j query_chunks)) final"
    "length raws = rounds"
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
      ro_zero_round_header_bad_query_lists M fr trace_final"
    "j < rounds"
    "x = QueryIndexChallenge j final"
    "y = raws ! j"
  using rel
  unfolding zero_round_absorbed_query_relation_def Let_def
  by blast


lemma zero_round_absorbed_query_relation_direct_fiber_card_bound:
  "card {y.
      hash_state_relation_direct_activation
        zero_round_absorbed_query_relation M x y}
    \<le> query_raw_preimage_card_envelope
        (query_sample_space_size - 1)"
proof (cases "{y.
    hash_state_relation_direct_activation
      zero_round_absorbed_query_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
    "hash_state_relation_direct_activation
      zero_round_absorbed_query_relation M x y0"
    by blast
  have rel0:
    "zero_round_absorbed_query_relation (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from zero_round_absorbed_query_relationD[OF rel0]
  obtain fr0 trace_final0 as0 dg0 composition_roots0 composition_final0
      query_chunks0 raws0 query_start0 final0 j0 where
    clean0:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y0 M))"
    and no_initial0:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y0 M))"
    and zero0: "ceil_log clength = 0"
    and alpha_len0: "length as0 = length spec"
    and composition_len0:
      "length composition_roots0 = ceil_log (to_nat dg0 + 1)"
    and header_chain0:
      "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state)
        (verifier_header_messages fr0 [] trace_final0 as0 dg0
          composition_roots0 composition_final0)
        query_start0"
    and query_chain0:
      "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y0 M))
        query_start0 (List.concat (take j0 query_chunks0)) final0"
    and raws_len0: "length raws0 = rounds"
    and raws_in0:
      "map (\<lambda>raw. index (to_nat raw)) raws0 \<in>
        ro_zero_round_header_bad_query_lists
          (fmupd x y0 M) fr0 trace_final0"
    and j0_bound: "j0 < rounds"
    and x0: "x = QueryIndexChallenge j0 final0"
    and y0_eq: "y0 = raws0 ! j0"
    .
  let ?Q0 =
    "ro_zero_round_header_bad_query_lists
      (fmupd x y0 M) fr0 trace_final0"
  have subset:
    "{y.
      hash_state_relation_direct_activation
        zero_round_absorbed_query_relation M x y}
      \<subseteq> query_index_raw_list_position_values ?Q0 j0"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          zero_round_absorbed_query_relation M x y}"
    have rely:
      "zero_round_absorbed_query_relation (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from zero_round_absorbed_query_relationD[OF rely]
    obtain fr trace_final as dg composition_roots composition_final
        query_chunks raws query_start final j where
      clean:
        "\<not> hash_map_output_collision
          (channel_for_hash_map (fmupd x y M))"
      and no_initial:
        "PState adversary_initial_state \<notin>
          hash_map_output_values (channel_for_hash_map (fmupd x y M))"
      and zero: "ceil_log clength = 0"
      and alpha_len: "length as = length spec"
      and composition_len:
        "length composition_roots = ceil_log (to_nat dg + 1)"
      and header_chain:
        "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
          (PState adversary_initial_state)
          (verifier_header_messages fr [] trace_final as dg
            composition_roots composition_final)
          query_start"
      and query_chain:
        "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
          query_start (List.concat (take j query_chunks)) final"
      and raws_len: "length raws = rounds"
      and raws_in:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_zero_round_header_bad_query_lists
            (fmupd x y M) fr trace_final"
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
        (verifier_header_messages fr0 [] trace_final0 as0 dg0
            composition_roots0 composition_final0 @
          List.concat (take j0 query_chunks0))
        final0"
      by (rule ro_absorb_lookup_chain_append[
        OF header_chain0 query_chain0])
    have header_chain_base:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (verifier_header_messages fr [] trace_final as dg
          composition_roots composition_final)
        query_start"
      using header_chain unfolding x0 by simp
    have query_chain_base:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        query_start (List.concat (take j0 query_chunks)) final0"
      using query_chain j_eq final_eq unfolding x0 by simp
    have header_chain_ref:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state)
        (verifier_header_messages fr [] trace_final as dg
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
        (verifier_header_messages fr [] trace_final as dg
            composition_roots composition_final @
          List.concat (take j0 query_chunks))
        final0"
      by (rule ro_absorb_lookup_chain_append[
        OF header_chain_ref query_chain_ref])
    have messages_eq:
      "verifier_header_messages fr [] trace_final as dg
          composition_roots composition_final @
        List.concat (take j0 query_chunks) =
       verifier_header_messages fr0 [] trace_final0 as0 dg0
          composition_roots0 composition_final0 @
        List.concat (take j0 query_chunks0)"
      by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
        OF clean0 no_initial0 full full0])
    have trace_len: "length ([] :: 'f list) = ceil_log clength"
      using zero by simp
    have trace_len0: "length ([] :: 'f list) = ceil_log clength"
      using zero0 by simp
    have header_eq:
      "verifier_header_messages fr [] trace_final as dg
          composition_roots composition_final =
       verifier_header_messages fr0 [] trace_final0 as0 dg0
          composition_roots0 composition_final0"
      by (rule verifier_header_messages_prefix_eq_from_append_eq[
        OF trace_len trace_len0 alpha_len alpha_len0
          composition_len composition_len0 messages_eq])
    have fields_eq:
      "fr = fr0 \<and> trace_final = trace_final0 \<and> as = as0 \<and> dg = dg0 \<and>
       composition_roots = composition_roots0 \<and>
       composition_final = composition_final0"
      using verifier_header_messages_relevant_fields_eq[
        OF trace_len trace_len0 alpha_len alpha_len0
          composition_len composition_len0 header_eq]
      by simp
    have Q_eq:
      "ro_zero_round_header_bad_query_lists
          (fmupd x y M) fr trace_final = ?Q0"
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
        zero_round_absorbed_query_relation M x y}
      \<le> card (query_index_raw_list_position_values ?Q0 j0)"
    by (rule card_mono[OF finite_Q0 subset])
  have position_le:
    "card (query_index_raw_list_position_values ?Q0 j0)
      \<le> query_raw_preimage_card_envelope
          (query_sample_space_size - 1)"
    unfolding x0
    by (rule
      ro_zero_round_header_bad_query_lists_position_card_bound[
        OF zero0 j0_bound])
  show ?thesis
    by (rule order_trans[OF card_le position_le])
qed


lemma zero_round_absorbed_query_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "zero_round_absorbed_query_relation (fmupd x y M) k z"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows "zero_round_absorbed_query_relation M k z"
proof -
  from zero_round_absorbed_query_relationD[OF rel]
  obtain fr trace_final as dg composition_roots composition_final
      query_chunks raws query_start final j where
    clean_new:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
    and no_initial_new:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
    and zero: "ceil_log clength = 0"
    and alpha_len: "length as = length spec"
    and composition_len:
      "length composition_roots = ceil_log (to_nat dg + 1)"
    and header_chain_new:
      "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (verifier_header_messages fr [] trace_final as dg
          composition_roots composition_final)
        query_start"
    and query_chain_new:
      "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
        query_start (List.concat (take j query_chunks)) final"
    and raws_len: "length raws = rounds"
    and raws_in_new:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_zero_round_header_bad_query_lists (fmupd x y M)
          fr trace_final"
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
      (verifier_header_messages fr [] trace_final as dg
          composition_roots composition_final @
        List.concat (take j query_chunks))
      final"
    by (rule ro_absorb_lookup_chain_append[
      OF header_chain_new query_chain_new])
  have full_chain_old:
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state)
      (verifier_header_messages fr [] trace_final as dg
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
        (verifier_header_messages fr [] trace_final as dg
          composition_roots composition_final)
        query_start_old"
    and query_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        query_start_old (List.concat (take j query_chunks)) final"
    by blast
  have messages_target:
    "set
      (verifier_header_messages fr [] trace_final as dg
          composition_roots composition_final @
        List.concat (take j query_chunks))
      \<subseteq> transcript_absorb_message_values M"
    by (rule ro_absorb_lookup_chain_messages_subset[OF full_chain_old])
  have fr_target: "fr \<in> transcript_absorb_message_values M"
    using messages_target
    unfolding verifier_header_messages_def
    by simp
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
  have table_eq:
    "conceptual_table
        (channel_for_hash_map (fmupd x y M)) fr (scale * clength) =
      conceptual_table (channel_for_hash_map M) fr (scale * clength)"
    by (rule conceptual_table_fresh_update[
      OF fresh fr_target no_target])
  have query_lists_eq:
    "ro_zero_round_header_bad_query_lists (fmupd x y M)
        fr trace_final =
      ro_zero_round_header_bad_query_lists M fr trace_final"
    unfolding ro_zero_round_header_bad_query_lists_def Let_def
    using table_eq by simp
  have raws_in_old:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
      ro_zero_round_header_bad_query_lists M fr trace_final"
    using raws_in_new query_lists_eq by simp
  show ?thesis
    unfolding zero_round_absorbed_query_relation_def Let_def
    using clean_old no_initial_old zero alpha_len composition_len
      header_chain_old query_chain_old raws_len raws_in_old j_bound
      k_eq z_eq
    by blast
qed

lemma zero_round_absorbed_query_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        zero_round_absorbed_query_relation M x y"
  shows "y \<in> first_root_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> first_root_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active zero_round_absorbed_query_relation
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active zero_round_absorbed_query_relation
        M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "zero_round_absorbed_query_relation (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def
    by blast+
  have rel_old: "zero_round_absorbed_query_relation M k z"
    by (rule zero_round_absorbed_query_relation_fresh_update_pullback[
      OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
    "hash_state_relation_active zero_round_absorbed_query_relation M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed

lemma zero_round_absorbed_query_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        zero_round_absorbed_query_relation M x y}
      \<le> 5 * card (fmdom' M) + 2"
proof -
  have subset:
    "{y.
      hash_state_relation_drift_activation
        zero_round_absorbed_query_relation M x y}
      \<subseteq> first_root_relation_drift_targets M x"
    using zero_round_absorbed_query_relation_drift_activation_imp_target[
      OF fresh]
    by blast
  have
    "card {y.
      hash_state_relation_drift_activation
        zero_round_absorbed_query_relation M x y}
      \<le> card (first_root_relation_drift_targets M x)"
    by (rule card_mono[
      OF finite_first_root_relation_drift_targets subset])
  also have "... \<le> 5 * card (fmdom' M) + 2"
    by (rule card_first_root_relation_drift_targets_le)
  finally show ?thesis .
qed


definition zero_round_absorbed_query_relation_bounded
  :: "nat \<Rightarrow>
      (('f protocol_hash_input, 'f) fmap \<Rightarrow>
        'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "zero_round_absorbed_query_relation_bounded L M x y \<longleftrightarrow>
    card (fmdom' M) \<le> L \<and>
    zero_round_absorbed_query_relation M x y"

lemma zero_round_bounded_direct_activation_subset:
  assumes fresh: "fmlookup M x = None"
  shows
    "{y.
      hash_state_relation_direct_activation
        (zero_round_absorbed_query_relation_bounded L) M x y}
      \<subseteq>
    {y.
      hash_state_relation_direct_activation
        zero_round_absorbed_query_relation M x y}"
proof
  fix y
  assume y:
    "y \<in> {y.
      hash_state_relation_direct_activation
        (zero_round_absorbed_query_relation_bounded L) M x y}"
  have active_new:
    "hash_state_relation_active
      (zero_round_absorbed_query_relation_bounded L)
      (fmupd x y M) x y"
    using y unfolding hash_state_relation_direct_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) x = Some y"
    and bounded_rel_new:
      "zero_round_absorbed_query_relation_bounded L
        (fmupd x y M) x y"
    using active_new unfolding hash_state_relation_active_def by blast+
  have rel_new:
    "zero_round_absorbed_query_relation (fmupd x y M) x y"
    using bounded_rel_new
    unfolding zero_round_absorbed_query_relation_bounded_def
    by blast
  have original_new:
    "hash_state_relation_active zero_round_absorbed_query_relation
      (fmupd x y M) x y"
    unfolding hash_state_relation_active_def
    using lookup_new rel_new by simp
  have original_old:
    "\<not> hash_state_relation_active zero_round_absorbed_query_relation M x y"
    using fresh unfolding hash_state_relation_active_def by simp
  show
    "y \<in> {y.
      hash_state_relation_direct_activation
        zero_round_absorbed_query_relation M x y}"
    unfolding hash_state_relation_direct_activation_def
    using original_new original_old by simp
qed

lemma zero_round_bounded_direct_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_direct_activation
        (zero_round_absorbed_query_relation_bounded L) M x y}
      \<le> query_raw_preimage_card_envelope
          (query_sample_space_size - 1)"
proof -
  let ?A =
    "{y.
      hash_state_relation_direct_activation
        (zero_round_absorbed_query_relation_bounded L) M x y}"
  let ?B =
    "{y.
      hash_state_relation_direct_activation
        zero_round_absorbed_query_relation M x y}"
  have subset: "?A \<subseteq> ?B"
    by (rule zero_round_bounded_direct_activation_subset[OF fresh])
  have finite_B: "finite ?B"
  proof -
    have "card ?B \<le>
        query_raw_preimage_card_envelope
          (query_sample_space_size - 1)"
      by (rule zero_round_absorbed_query_relation_direct_fiber_card_bound)
    then show ?thesis by simp
  qed
  have "card ?A \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  also have "... \<le>
      query_raw_preimage_card_envelope
        (query_sample_space_size - 1)"
    by (rule zero_round_absorbed_query_relation_direct_fiber_card_bound)
  finally show ?thesis .
qed

lemma zero_round_bounded_drift_activation_subset:
  assumes fresh: "fmlookup M x = None"
  shows
    "{y.
      hash_state_relation_drift_activation
        (zero_round_absorbed_query_relation_bounded L) M x y}
      \<subseteq>
    {y.
      hash_state_relation_drift_activation
        zero_round_absorbed_query_relation M x y}"
proof
  fix y
  assume y:
    "y \<in> {y.
      hash_state_relation_drift_activation
        (zero_round_absorbed_query_relation_bounded L) M x y}"
  then obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        (zero_round_absorbed_query_relation_bounded L)
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        (zero_round_absorbed_query_relation_bounded L) M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and bounded_rel_new:
      "zero_round_absorbed_query_relation_bounded L
        (fmupd x y M) k z"
    using active_new unfolding hash_state_relation_active_def by blast+
  have domain_new: "card (fmdom' (fmupd x y M)) \<le> L"
    and rel_new:
      "zero_round_absorbed_query_relation (fmupd x y M) k z"
    using bounded_rel_new
    unfolding zero_round_absorbed_query_relation_bounded_def
    by blast+
  have domain_old: "card (fmdom' M) \<le> L"
    using card_fmdom_fmupd_mono[of M x y] domain_new
    by linarith
  have original_new:
    "hash_state_relation_active zero_round_absorbed_query_relation
      (fmupd x y M) k z"
    unfolding hash_state_relation_active_def
    using lookup_new rel_new by simp
  have original_old:
    "\<not> hash_state_relation_active zero_round_absorbed_query_relation M k z"
  proof
    assume old:
      "hash_state_relation_active zero_round_absorbed_query_relation M k z"
    have lookup_old: "fmlookup M k = Some z"
      and rel_old: "zero_round_absorbed_query_relation M k z"
      using old unfolding hash_state_relation_active_def by blast+
    have bounded_old:
      "zero_round_absorbed_query_relation_bounded L M k z"
      unfolding zero_round_absorbed_query_relation_bounded_def
      using domain_old rel_old by simp
    have
      "hash_state_relation_active
        (zero_round_absorbed_query_relation_bounded L) M k z"
      unfolding hash_state_relation_active_def
      using lookup_old bounded_old by simp
    then show False using inactive_old by contradiction
  qed
  show
    "y \<in> {y.
      hash_state_relation_drift_activation
        zero_round_absorbed_query_relation M x y}"
    unfolding hash_state_relation_drift_activation_def
    using key_neq original_new original_old by blast
qed

lemma zero_round_bounded_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
    and domain: "card (fmdom' M) \<le> L"
  shows
    "card {y.
      hash_state_relation_drift_activation
        (zero_round_absorbed_query_relation_bounded L) M x y}
      \<le> 5 * L + 2"
proof -
  let ?A =
    "{y.
      hash_state_relation_drift_activation
        (zero_round_absorbed_query_relation_bounded L) M x y}"
  let ?B =
    "{y.
      hash_state_relation_drift_activation
        zero_round_absorbed_query_relation M x y}"
  have subset: "?A \<subseteq> ?B"
    by (rule zero_round_bounded_drift_activation_subset[OF fresh])
  have finite_B: "finite ?B"
  proof -
    have "card ?B \<le> 5 * card (fmdom' M) + 2"
      by (rule
        zero_round_absorbed_query_relation_drift_fiber_card_bound[OF fresh])
    then show ?thesis by simp
  qed
  have "card ?A \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  also have "... \<le> 5 * card (fmdom' M) + 2"
    by (rule
      zero_round_absorbed_query_relation_drift_fiber_card_bound[OF fresh])
  also have "... \<le> 5 * L + 2"
    using domain by simp
  finally show ?thesis .
qed


lemma zero_round_bounded_transition_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_transition
        (zero_round_absorbed_query_relation_bounded L)
        M (fmupd x y M)}
      \<le>
      query_raw_preimage_card_envelope
          (query_sample_space_size - 1) +
        (5 * L + 2)"
proof (cases "card (fmdom' M) \<le> L")
  case True
  have direct:
    "card {y.
      hash_state_relation_direct_activation
        (zero_round_absorbed_query_relation_bounded L) M x y}
      \<le> query_raw_preimage_card_envelope
          (query_sample_space_size - 1)"
    by (rule zero_round_bounded_direct_fiber_card_bound[OF fresh])
  have drift:
    "card {y.
      hash_state_relation_drift_activation
        (zero_round_absorbed_query_relation_bounded L) M x y}
      \<le> 5 * L + 2"
    by (rule zero_round_bounded_drift_fiber_card_bound[OF fresh True])
  show ?thesis
    by (rule hash_state_relation_transition_update_fiber_card_bound[
      OF direct drift])
next
  case False
  have no_active:
    "\<And>y k z.
      \<not> hash_state_relation_active
        (zero_round_absorbed_query_relation_bounded L)
        (fmupd x y M) k z"
  proof
    fix y k z
    assume active_new:
      "hash_state_relation_active
        (zero_round_absorbed_query_relation_bounded L)
        (fmupd x y M) k z"
    have domain_new: "card (fmdom' (fmupd x y M)) \<le> L"
      using active_new
      unfolding hash_state_relation_active_def
        zero_round_absorbed_query_relation_bounded_def
      by blast
    have domain_old: "card (fmdom' M) \<le> L"
      using card_fmdom_fmupd_mono[of M x y] domain_new
      by linarith
    show False using False domain_old by contradiction
  qed
  have no_transition:
    "{y.
      hash_state_relation_transition
        (zero_round_absorbed_query_relation_bounded L)
        M (fmupd x y M)} = {}"
    unfolding hash_state_relation_transition_def
    using no_active by auto
  show ?thesis using no_transition by simp
qed

lemma wp_ro_checked_staged_transcript_zero_round_bounded_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  defines
    "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (zero_round_absorbed_query_relation_bounded q)
          (HashMap adversary_initial_state))
        adversary_initial_state
      \<le>
      nnreal
        (q *
          (query_raw_preimage_card_envelope
              (query_sample_space_size - 1) +
            (5 * q + 2))) /
        nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B =
    "query_raw_preimage_card_envelope
        (query_sample_space_size - 1) +
      (5 * ?Q + 2)"
  have steps:
    "\<And>M x. fmlookup M x = None \<Longrightarrow>
      card {y.
        hash_state_relation_transition
          (zero_round_absorbed_query_relation_bounded ?Q)
          M (fmupd x y M)}
        \<le> ?B"
    by (rule zero_round_bounded_transition_fiber_card_bound)
  have bound:
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (zero_round_absorbed_query_relation_bounded ?Q)
          (HashMap adversary_initial_state))
        adversary_initial_state
      \<le> nnreal (?Q * ?B) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound_all_rounds[
        OF wf controlled steps])
  show ?thesis
    using bound unfolding q_def by simp
qed


lemma ro_checked_staged_transcript_zero_round_header_query_prefix_chain:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
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
    and j_bound: "j < rounds"
  shows
    "\<exists>fr.
      prefix = (fr, [], fr) \<and>
      staged_trace_root data = fr \<and>
      staged_trace_fri_roots data = [] \<and>
      ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state)
        (verifier_header_messages
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data))
        (PState query_start) \<and>
      ro_absorb_lookup_chain attacker_state
        (PState query_start)
        (List.concat (take j (staged_query_chunks data)))
        (PState (query_states ! j))"
proof -
  from ro_checked_staged_transcript_program_with_first_root_outcomeE[
      OF outcome]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute
            (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program
              A prefix)
            prefix_final)"
    and query_out:
      "Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots head_data)
              (staged_composition_fri_roots head_data)
              query_start 0 rounds)
            query_start)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    by blast
  from ro_checked_staged_transcript_program_with_first_root_zero_fields[
      OF zero wf controlled outcome]
  obtain fr where zero_fields:
    "prefix = (fr, [], fr) \<and>
     staged_trace_root data = fr \<and>
     staged_trace_fri_roots data = [] \<and>
     staged_trace_fri_challenges data = [] \<and>
     prefix_state \<le> query_start \<and>
     query_start \<le> attacker_state \<and>
     PQueryCounter query_start = 0"
    by blast
  have original_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (ro_checked_staged_transcript_program A)
          adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have full_chain:
    "ro_absorb_lookup_chain attacker_state
      (PState adversary_initial_state)
      (staged_proof_transcript data) (PState attacker_state)"
    using ro_checked_staged_transcript_program_absorb_lookup_chain[
      OF wf controlled original_out]
    by blast
  let ?header =
    "verifier_header_messages
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)"
  have transcript_eq:
    "staged_proof_transcript data =
      ?header @ List.concat (staged_query_chunks data)"
    unfolding staged_proof_transcript_def by simp
  from ro_absorb_lookup_chain_append_split[
      OF full_chain[unfolded transcript_eq]]
  obtain header_end where
    header_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state) ?header header_end"
    and query_tail:
      "ro_absorb_lookup_chain attacker_state header_end
        (List.concat (staged_query_chunks data))
        (PState attacker_state)"
    by blast
  have query_bound:
    "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_full:
    "ro_absorb_lookup_chain attacker_state
      (PState query_start)
      (List.concat (staged_query_chunks data))
      (PState attacker_state)"
    using
      ro_checked_staged_query_program_with_witnesses_absorb_lookup_chain[
        OF controlled query_bound query_out]
      data_eq
    by simp
  have header_end_eq: "header_end = PState query_start"
    by (rule ro_absorb_lookup_chain_start_functional_if_clean[
      OF clean query_tail query_full])
  have header_chain':
    "ro_absorb_lookup_chain attacker_state
      (PState adversary_initial_state) ?header (PState query_start)"
    using header_chain header_end_eq by simp
  have query_prefix:
    "ro_absorb_lookup_chain attacker_state
      (PState query_start)
      (List.concat (take j (staged_query_chunks data)))
      (PState (query_states ! j))"
    using ro_checked_staged_query_program_with_witnesses_prefix_chain[
      OF controlled query_bound query_out j_bound]
      data_eq
    by simp
  show ?thesis
    by (intro exI[of _ fr])
      (use zero_fields header_chain' query_prefix in simp)
qed


lemma zero_round_absorbed_query_relation_bounded_activeI:
  assumes map_bound: "card (fmdom' (HashMap attacker_state)) \<le> L"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values attacker_state"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and query_start_ext: "query_start \<le> attacker_state"
    and prefix_eq:
      "prefix =
        (staged_trace_root data, [], staged_trace_root data)"
    and no_trace_merkle:
      "\<not> hash_map_new_output_hit
        (ro_actual_query_zero_round_trace_merkle_targets data prefix_state)
        prefix_state attacker_state"
    and header_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state)
        (verifier_header_messages
          (staged_trace_root data) []
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data))
        (PState query_start)"
    and query_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState query_start)
        (List.concat (take j (staged_query_chunks data)))
        (PState (query_states ! j))"
    and zero: "ceil_log clength = 0"
    and alpha_len: "length (staged_alphas data) = length spec"
    and composition_len:
      "length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1)"
    and raws_len: "length raws = rounds"
    and raws_in:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_actual_query_zero_round_bad_query_lists
          prefix prefix_state (ro_query_head_data data) query_start"
    and j_bound: "j < rounds"
    and lookup:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge j (PState (query_states ! j))) =
        Some (raws ! j)"
  shows
    "hash_state_relation_active
      (zero_round_absorbed_query_relation_bounded L)
      (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j)))
      (raws ! j)"
proof -
  let ?final = "channel_for_hash_map (HashMap attacker_state)"
  have final_map: "HashMap ?final = HashMap attacker_state"
    unfolding channel_for_hash_map_def by simp
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision attacker_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_ext])
    then show False using clean by contradiction
  qed
  have no_trace:
    "\<not> hash_map_new_output_hit
      (merkle_prefix_path_targets {staged_trace_root data} prefix_state)
      prefix_state attacker_state"
    using no_trace_merkle
    unfolding ro_actual_query_zero_round_trace_merkle_targets_def
    by simp
  have final_attacker:
    "conceptual_table ?final (staged_trace_root data)
        (scale * clength) =
      conceptual_table attacker_state (staged_trace_root data)
        (scale * clength)"
    by (rule conceptual_table_cong_hash_map[OF final_map])
  have attacker_prefix:
    "conceptual_table attacker_state (staged_trace_root data)
        (scale * clength) =
      conceptual_table prefix_state (staged_trace_root data)
        (scale * clength)"
    by (rule conceptual_table_prefix_stable_if_no_target[
      OF prefix_ext no_trace])
  have table_eq:
    "conceptual_table ?final (staged_trace_root data)
        (scale * clength) =
      conceptual_table prefix_state (staged_trace_root data)
        (scale * clength)"
    using final_attacker attacker_prefix by simp
  have query_lists_eq:
    "ro_zero_round_header_bad_query_lists
        (HashMap attacker_state)
        (staged_trace_root data) (staged_trace_final data) =
      ro_actual_query_zero_round_bad_query_lists
        prefix prefix_state (ro_query_head_data data) query_start"
    unfolding ro_zero_round_header_bad_query_lists_def
      ro_actual_query_zero_round_bad_query_lists_def
      ro_actual_query_zero_round_trace_query_lists_def
      ro_actual_query_zero_round_trace_indices_def
      ro_actual_query_zero_round_trace_table_def
      ro_query_head_data_def Let_def
    using table_eq
    by simp
  have raws_in_final:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
      ro_zero_round_header_bad_query_lists
        (HashMap attacker_state)
        (staged_trace_root data) (staged_trace_final data)"
    using raws_in query_lists_eq by simp
  have header_chain_final:
    "ro_absorb_lookup_chain ?final
      (PState adversary_initial_state)
      (verifier_header_messages
        (staged_trace_root data) []
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data))
      (PState query_start)"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule header_chain)
  have query_chain_final:
    "ro_absorb_lookup_chain ?final
      (PState query_start)
      (List.concat (take j (staged_query_chunks data)))
      (PState (query_states ! j))"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule query_chain)
  have clean_final: "\<not> hash_map_output_collision ?final"
    using clean final_map
    unfolding hash_map_output_collision_def by simp
  have no_initial_final:
    "PState adversary_initial_state \<notin> hash_map_output_values ?final"
    using no_initial final_map
    unfolding hash_map_output_values_def by simp
  have relation:
    "zero_round_absorbed_query_relation
      (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j)))
      (raws ! j)"
    unfolding zero_round_absorbed_query_relation_def Let_def
    using clean_final no_initial_final zero alpha_len composition_len
      header_chain_final query_chain_final raws_len raws_in_final j_bound
    by blast
  have bounded_relation:
    "zero_round_absorbed_query_relation_bounded L
      (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j)))
      (raws ! j)"
    unfolding zero_round_absorbed_query_relation_bounded_def
    using map_bound relation by simp
  show ?thesis
    unfolding hash_state_relation_active_def
    using lookup bounded_relation by simp
qed


end
end
