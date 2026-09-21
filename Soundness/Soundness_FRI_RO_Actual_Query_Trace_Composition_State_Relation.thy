theory Soundness_FRI_RO_Actual_Query_Trace_Composition_State_Relation
  imports Soundness_FRI_RO_Actual_Query_Trace_Composition_Query_Bound
begin

context soundness
begin

lemma verifier_header_messages_prefix_eq_from_append_eq:
  assumes trace_len:
      "length trace_roots = ceil_log clength"
      "length trace_roots' = ceil_log clength"
    and alpha_len:
      "length as = length spec"
      "length as' = length spec"
    and composition_len:
      "length composition_roots = ceil_log (to_nat dg + 1)"
      "length composition_roots' = ceil_log (to_nat dg' + 1)"
    and full_eq:
      "verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final @ xs =
       verifier_header_messages fr' trace_roots' trace_final' as' dg'
          composition_roots' composition_final' @ ys"
  shows
    "verifier_header_messages fr trace_roots trace_final as dg
        composition_roots composition_final =
     verifier_header_messages fr' trace_roots' trace_final' as' dg'
        composition_roots' composition_final'"
proof -
  let ?k = "2 + ceil_log clength + length spec"
  have prefix_eq:
      "take (Suc ?k)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final @ xs) =
       take (Suc ?k)
          (verifier_header_messages fr' trace_roots' trace_final' as' dg'
            composition_roots' composition_final' @ ys)"
    using full_eq by simp
  have dg_eq: "dg = dg'"
    using prefix_eq trace_len alpha_len
    unfolding verifier_header_messages_def
    by simp
  have header_len:
      "length
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final) =
       length
        (verifier_header_messages fr' trace_roots' trace_final' as' dg'
          composition_roots' composition_final')"
    using trace_len alpha_len composition_len dg_eq
    unfolding verifier_header_messages_def
    by simp
  have
      "take
        (length
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final))
        (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final @ xs) =
       take
        (length
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final))
        (verifier_header_messages fr' trace_roots' trace_final' as' dg'
            composition_roots' composition_final' @ ys)"
    using full_eq by simp
  then show ?thesis
    using header_len by simp
qed


lemma verifier_header_messages_relevant_fields_eq:
  assumes trace_len:
      "length trace_roots = ceil_log clength"
      "length trace_roots' = ceil_log clength"
    and alpha_len:
      "length as = length spec"
      "length as' = length spec"
    and composition_len:
      "length composition_roots = ceil_log (to_nat dg + 1)"
      "length composition_roots' = ceil_log (to_nat dg' + 1)"
    and header_eq:
      "verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final =
       verifier_header_messages fr' trace_roots' trace_final' as' dg'
          composition_roots' composition_final'"
  shows
    "fr = fr' \<and> trace_roots = trace_roots' \<and>
     trace_final = trace_final' \<and> as = as' \<and> dg = dg' \<and>
     composition_roots = composition_roots' \<and>
     composition_final = composition_final'"
  using header_eq trace_len alpha_len composition_len
  unfolding verifier_header_messages_def
  by (auto simp: append_eq_append_conv_if)


definition ro_trace_composition_header_data
where
  "ro_trace_composition_header_data fr trace_roots trace_final as dg
      composition_roots composition_final =
    \<lparr>staged_trace_root = fr,
     staged_trace_fri_roots = trace_roots,
     staged_trace_fri_challenges = [],
     staged_trace_final = trace_final,
     staged_alphas = as,
     staged_degree = dg,
     staged_composition_fri_roots = composition_roots,
     staged_composition_fri_challenges = [],
     staged_composition_final = composition_final,
     staged_query_chunks = []\<rparr>"

lemma staged_proof_transcript_ro_trace_composition_header_data[simp]:
  "staged_proof_transcript
      (ro_trace_composition_header_data fr trace_roots trace_final as dg
        composition_roots composition_final) =
    verifier_header_messages fr trace_roots trace_final as dg
      composition_roots composition_final"
  unfolding ro_trace_composition_header_data_def staged_proof_transcript_def
  by simp

lemma ro_trace_composition_header_data_fields[simp]:
  "staged_trace_root
      (ro_trace_composition_header_data fr trace_roots trace_final as dg
        composition_roots composition_final) = fr"
  "staged_trace_fri_roots
      (ro_trace_composition_header_data fr trace_roots trace_final as dg
        composition_roots composition_final) = trace_roots"
  "staged_trace_final
      (ro_trace_composition_header_data fr trace_roots trace_final as dg
        composition_roots composition_final) = trace_final"
  "staged_alphas
      (ro_trace_composition_header_data fr trace_roots trace_final as dg
        composition_roots composition_final) = as"
  "staged_degree
      (ro_trace_composition_header_data fr trace_roots trace_final as dg
        composition_roots composition_final) = dg"
  "staged_composition_fri_roots
      (ro_trace_composition_header_data fr trace_roots trace_final as dg
        composition_roots composition_final) = composition_roots"
  "staged_composition_final
      (ro_trace_composition_header_data fr trace_roots trace_final as dg
        composition_roots composition_final) = composition_final"
  unfolding ro_trace_composition_header_data_def
  by simp_all

definition trace_composition_header_trace_root
where
  "trace_composition_header_trace_root fr trace_roots =
    (if trace_roots = [] then fr else hd trace_roots)"

lemma trace_composition_header_trace_root_nonempty:
  assumes "trace_roots \<noteq> []"
  shows "trace_composition_header_trace_root fr trace_roots = hd trace_roots"
  using assms
  unfolding trace_composition_header_trace_root_def
  by simp

lemma trace_composition_header_trace_root_empty:
  assumes "trace_roots = []"
  shows "trace_composition_header_trace_root fr trace_roots = fr"
  using assms
  unfolding trace_composition_header_trace_root_def
  by simp


definition ro_trace_composition_header_query_lists
where
  "ro_trace_composition_header_query_lists M fr trace_roots trace_final as dg
      composition_roots composition_final =
    ro_actual_query_trace_composition_good_query_lists
      (fr, [], trace_composition_header_trace_root fr trace_roots)
      (channel_for_hash_map M)
      (ro_trace_composition_header_data fr trace_roots trace_final as dg
        composition_roots composition_final)
      (channel_for_hash_map M)"

lemma ro_trace_composition_header_query_lists_query_index_update[simp]:
  "ro_trace_composition_header_query_lists
      (fmupd (QueryIndexChallenge c st) y M)
      fr trace_roots trace_final as dg composition_roots composition_final =
    ro_trace_composition_header_query_lists M
      fr trace_roots trace_final as dg composition_roots composition_final"
proof -
  let ?updated =
    "channel_for_hash_map
      (fmupd (QueryIndexChallenge c st) y M)"
  let ?base = "channel_for_hash_map M"
  let ?data =
    "ro_trace_composition_header_data fr trace_roots trace_final as dg
      composition_roots composition_final"
  have original:
      "conceptual_table ?updated fr (scale * clength) =
        conceptual_table ?base fr (scale * clength)"
    by simp
  have first:
      "first_trace_fri_root_prefix_first_table
          (fr, [], trace_composition_header_trace_root fr trace_roots) ?updated =
        first_trace_fri_root_prefix_first_table
          (fr, [], trace_composition_header_trace_root fr trace_roots) ?base"
    unfolding first_trace_fri_root_prefix_first_table_def by simp
  have composition:
      "ro_actual_query_composition_candidate ?data ?updated =
        ro_actual_query_composition_candidate ?data ?base"
    unfolding ro_actual_query_composition_candidate_def
      ro_trace_composition_header_data_def
    by simp
  have accepted:
      "ro_actual_query_trace_composition_accepted_query_lists
          (fr, [], trace_composition_header_trace_root fr trace_roots) ?updated ?data ?updated =
        ro_actual_query_trace_composition_accepted_query_lists
          (fr, [], trace_composition_header_trace_root fr trace_roots) ?base ?data ?base"
    unfolding
      ro_actual_query_trace_composition_accepted_query_lists_def
      ro_actual_query_trace_composition_accepted_indices_def
      trace_composition_accepted_indices_def
    using original first composition
    by simp
  show ?thesis
    unfolding
      ro_trace_composition_header_query_lists_def
      ro_actual_query_trace_composition_good_query_lists_def
    using first composition accepted
    by simp
qed

lemma ro_trace_composition_header_query_lists_cong:
  assumes fields:
    "fr = fr' \<and> trace_roots = trace_roots' \<and>
     trace_final = trace_final' \<and> as = as' \<and> dg = dg' \<and>
     composition_roots = composition_roots' \<and>
     composition_final = composition_final'"
  shows
    "ro_trace_composition_header_query_lists M
        fr trace_roots trace_final as dg composition_roots composition_final =
     ro_trace_composition_header_query_lists M
        fr' trace_roots' trace_final' as' dg'
        composition_roots' composition_final'"
  using fields by simp

lemma ro_trace_composition_header_query_lists_position_card_bound:
  assumes i_bound: "i < rounds"
    and trace_len: "length trace_roots = ceil_log clength"
  shows
    "card
      (query_index_raw_list_position_values
        (ro_trace_composition_header_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final)
        i)
      \<le> query_raw_preimage_card_envelope
        trace_composition_query_index_bound"
proof -
  let ?Q =
    "ro_trace_composition_header_query_lists M
      fr trace_roots trace_final as dg composition_roots composition_final"
  let ?data =
    "ro_trace_composition_header_data fr trace_roots trace_final as dg
      composition_roots composition_final"
  let ?indices =
    "ro_actual_query_trace_composition_accepted_indices
      (fr, [], trace_composition_header_trace_root fr trace_roots) (channel_for_hash_map M)
      ?data (channel_for_hash_map M)"
  let ?good =
    "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table
          (fr, [], trace_composition_header_trace_root fr trace_roots) (channel_for_hash_map M)) \<and>
      composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate
          ?data (channel_for_hash_map M)) \<and>
      \<not> all_queries_consistent
        (first_trace_fri_root_prefix_first_table
          (fr, [], trace_composition_header_trace_root fr trace_roots) (channel_for_hash_map M))
        (ro_actual_query_composition_candidate
          ?data (channel_for_hash_map M))
        (staged_alphas ?data)"
  show ?thesis
  proof (cases ?good)
    case True
    have Q_eq: "?Q = query_index_lists_over ?indices"
      using True
      unfolding
        ro_trace_composition_header_query_lists_def
        ro_actual_query_trace_composition_good_query_lists_def
        ro_actual_query_trace_composition_accepted_query_lists_def
      by simp
    have pos_subset:
        "query_index_raw_list_position_values ?Q i
          \<subseteq> query_index_raw_preimage ?indices"
      unfolding Q_eq
      by (rule
          query_index_raw_list_position_values_query_index_lists_over_subset[
            OF i_bound])
    have card_le:
        "card (query_index_raw_list_position_values ?Q i)
          \<le> card (query_index_raw_preimage ?indices)"
      by (rule card_mono[OF _ pos_subset]) simp
    have raw_card:
        "card (query_index_raw_preimage ?indices) \<le>
          query_raw_preimage_card_envelope (card ?indices)"
      by (rule card_query_index_raw_preimage_le_query_envelope)
        (rule ro_actual_query_trace_composition_accepted_indices_subset)
    have indices_bound:
        "card ?indices \<le> trace_composition_query_index_bound"
      by (rule
          ro_actual_query_trace_composition_accepted_indices_card_bound)
        (use True in blast)+
    have envelope_bound:
        "query_raw_preimage_card_envelope (card ?indices) \<le>
          query_raw_preimage_card_envelope
            trace_composition_query_index_bound"
      by (rule query_raw_preimage_card_envelope_mono[OF indices_bound])
    show ?thesis
      by (rule order_trans[OF card_le])
        (rule order_trans[OF raw_card envelope_bound])
  next
    case False
    have Q_empty: "?Q = {}"
      unfolding
        ro_trace_composition_header_query_lists_def
        ro_actual_query_trace_composition_good_query_lists_def
      by (rule if_not_P) (use False in simp)
    show ?thesis
      unfolding Q_empty query_index_raw_list_position_values_def
        query_index_raw_list_preimage_def
      by simp
  qed
qed


lemma ro_trace_composition_header_query_lists_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and messages_target:
      "set
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        \<subseteq> transcript_absorb_message_values M"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows
    "ro_trace_composition_header_query_lists (fmupd x y M)
        fr trace_roots trace_final as dg composition_roots composition_final =
      ro_trace_composition_header_query_lists M
        fr trace_roots trace_final as dg composition_roots composition_final"
proof -
  have fr_target: "fr \<in> transcript_absorb_message_values M"
    and trace_roots_target:
      "set trace_roots \<subseteq> transcript_absorb_message_values M"
    and composition_roots_target:
      "set composition_roots \<subseteq> transcript_absorb_message_values M"
    using messages_target
    unfolding verifier_header_messages_def
    by simp_all
  have trace_selected_target:
      "trace_composition_header_trace_root fr trace_roots \<in>
        transcript_absorb_message_values M"
    using fr_target trace_roots_target
    unfolding trace_composition_header_trace_root_def
    by (cases trace_roots) auto
  have original_eq:
      "conceptual_table (channel_for_hash_map (fmupd x y M))
          fr (scale * clength) =
        conceptual_table (channel_for_hash_map M)
          fr (scale * clength)"
    by (rule conceptual_table_fresh_update[
          OF fresh fr_target no_target])
  have first_eq:
      "first_trace_fri_root_prefix_first_table
          (fr, [], trace_composition_header_trace_root fr trace_roots)
          (channel_for_hash_map (fmupd x y M)) =
        first_trace_fri_root_prefix_first_table
          (fr, [], trace_composition_header_trace_root fr trace_roots)
          (channel_for_hash_map M)"
    unfolding first_trace_fri_root_prefix_first_table_def
    using conceptual_table_fresh_update[
      OF fresh trace_selected_target no_target]
    by simp
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
    case True
    then show ?thesis
      unfolding ro_actual_query_composition_candidate_def
        ro_trace_composition_header_data_def
      by simp
  next
    case False
    have composition_first_target:
        "hd composition_roots \<in> transcript_absorb_message_values M"
      by (rule set_mp[OF composition_roots_target])
        (rule hd_in_set[OF False])
    show ?thesis
      unfolding ro_actual_query_composition_candidate_def
        ro_trace_composition_header_data_def
      using False conceptual_table_fresh_update[
        OF fresh composition_first_target no_target]
      by simp
  qed
  show ?thesis
    unfolding ro_trace_composition_header_query_lists_def
      ro_actual_query_trace_composition_good_query_lists_def
      ro_actual_query_trace_composition_accepted_query_lists_def
      ro_actual_query_trace_composition_accepted_indices_def
    using original_eq first_eq composition_eq
    by simp
qed


definition trace_composition_absorbed_query_relation
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "trace_composition_absorbed_query_relation M x y \<longleftrightarrow>
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
          ro_trace_composition_header_query_lists M
            fr trace_roots trace_final as dg composition_roots
            composition_final \<and>
        j < rounds \<and>
        x = QueryIndexChallenge j final \<and>
        y = raws ! j))"

lemma trace_composition_absorbed_query_relationD:
  assumes rel: "trace_composition_absorbed_query_relation M x y"
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
      ro_trace_composition_header_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final"
    "j < rounds"
    "x = QueryIndexChallenge j final"
    "y = raws ! j"
  using rel
  unfolding trace_composition_absorbed_query_relation_def Let_def
  by blast


lemma trace_composition_absorbed_query_relation_direct_fiber_card_bound:
  "card {y.
      hash_state_relation_direct_activation
        trace_composition_absorbed_query_relation M x y}
    \<le> query_raw_preimage_card_envelope
      trace_composition_query_index_bound"
proof (cases "{y.
    hash_state_relation_direct_activation
      trace_composition_absorbed_query_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
    "hash_state_relation_direct_activation
      trace_composition_absorbed_query_relation M x y0"
    by blast
  have rel0:
      "trace_composition_absorbed_query_relation (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from trace_composition_absorbed_query_relationD[OF rel0]
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
        ro_trace_composition_header_query_lists (fmupd x y0 M)
          fr0 trace_roots0 trace_final0 as0 dg0 composition_roots0
          composition_final0"
    and j0_bound: "j0 < rounds"
    and x0: "x = QueryIndexChallenge j0 final0"
    and y0_eq: "y0 = raws0 ! j0"
    .
  let ?Q0 =
    "ro_trace_composition_header_query_lists (fmupd x y0 M)
      fr0 trace_roots0 trace_final0 as0 dg0 composition_roots0
      composition_final0"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          trace_composition_absorbed_query_relation M x y}
        \<subseteq> query_index_raw_list_position_values ?Q0 j0"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          trace_composition_absorbed_query_relation M x y}"
    have rely:
        "trace_composition_absorbed_query_relation (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from trace_composition_absorbed_query_relationD[OF rely]
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
          ro_trace_composition_header_query_lists (fmupd x y M)
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
        "ro_trace_composition_header_query_lists (fmupd x y M)
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
          trace_composition_absorbed_query_relation M x y}
        \<le> card (query_index_raw_list_position_values ?Q0 j0)"
    by (rule card_mono[OF finite_Q0 subset])
  have position_le:
      "card (query_index_raw_list_position_values ?Q0 j0)
        \<le> query_raw_preimage_card_envelope
          trace_composition_query_index_bound"
    unfolding x0
    by (rule
        ro_trace_composition_header_query_lists_position_card_bound[
          OF j0_bound trace_len0])
  show ?thesis
    by (rule order_trans[OF card_le position_le])
qed

lemma trace_composition_absorbed_query_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "trace_composition_absorbed_query_relation (fmupd x y M) k z"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows "trace_composition_absorbed_query_relation M k z"
proof -
  from trace_composition_absorbed_query_relationD[OF rel]
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
        ro_trace_composition_header_query_lists (fmupd x y M)
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
      "ro_trace_composition_header_query_lists (fmupd x y M)
          fr trace_roots trace_final as dg composition_roots
          composition_final =
        ro_trace_composition_header_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    by (rule ro_trace_composition_header_query_lists_fresh_update[
          OF fresh messages_target no_target])
  have raws_in_old:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_trace_composition_header_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    using raws_in_new query_lists_eq by simp
  show ?thesis
    unfolding trace_composition_absorbed_query_relation_def Let_def
    using clean_old no_initial_old trace_len alpha_len
      composition_len header_chain_old query_chain_old raws_len
      raws_in_old j_bound k_eq z_eq
    by blast
qed


lemma trace_composition_absorbed_query_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        trace_composition_absorbed_query_relation M x y"
  shows "y \<in> first_root_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> first_root_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        trace_composition_absorbed_query_relation (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        trace_composition_absorbed_query_relation M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "trace_composition_absorbed_query_relation (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def
    by blast+
  have rel_old:
      "trace_composition_absorbed_query_relation M k z"
    by (rule
      trace_composition_absorbed_query_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
      "hash_state_relation_active
        trace_composition_absorbed_query_relation M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed


lemma trace_composition_absorbed_query_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        trace_composition_absorbed_query_relation M x y}
      \<le> 5 * card (fmdom' M) + 2"
proof -
  have subset:
      "{y.
        hash_state_relation_drift_activation
          trace_composition_absorbed_query_relation M x y}
        \<subseteq> first_root_relation_drift_targets M x"
    using
      trace_composition_absorbed_query_relation_drift_activation_imp_target[
        OF fresh]
    by blast
  have
      "card {y.
        hash_state_relation_drift_activation
          trace_composition_absorbed_query_relation M x y}
        \<le> card (first_root_relation_drift_targets M x)"
    by (rule card_mono[OF finite_first_root_relation_drift_targets subset])
  also have "... \<le> 5 * card (fmdom' M) + 2"
    by (rule card_first_root_relation_drift_targets_le)
  finally show ?thesis .
qed


end
end
