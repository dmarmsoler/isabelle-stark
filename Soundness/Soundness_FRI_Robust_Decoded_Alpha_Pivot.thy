theory Soundness_FRI_Robust_Decoded_Alpha_Pivot
  imports
    Soundness_FRI_Robust_Decoded_Semantics
    Stark.Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Closed_Bound
    Stark.Soundness_FRI_Conditioned_Challenge_Relation
begin

context soundness
begin

definition robust_alpha_pivot_trace_table
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f list"
where
  "robust_alpha_pivot_trace_table M fr trace_roots =
    fri_canonical_decoded_table (clength - 1)
      (alpha_pivot_trace_table M fr trace_roots)"

lemma robust_alpha_pivot_trace_table_low_degree:
  "trace_table_low_degree
    (robust_alpha_pivot_trace_table M fr trace_roots)"
  unfolding robust_alpha_pivot_trace_table_def
  by (rule fri_canonical_decoded_trace_table_low_degree)

lemma robust_alpha_pivot_trace_table_cong:
  assumes
    "alpha_pivot_trace_table M fr trace_roots =
      alpha_pivot_trace_table M' fr trace_roots"
  shows
    "robust_alpha_pivot_trace_table M fr trace_roots =
      robust_alpha_pivot_trace_table M' fr trace_roots"
  using assms unfolding robust_alpha_pivot_trace_table_def by simp

definition robust_alpha_pivot_absorbed_query_relation
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "robust_alpha_pivot_absorbed_query_relation M x y \<longleftrightarrow>
    (let s = channel_for_hash_map M in
      \<not> hash_map_output_collision s \<and>
      PState adversary_initial_state \<notin> hash_map_output_values s \<and>
      (\<exists>fr trace_roots trace_final alpha_start alpha_prefix pivot_state.
        length trace_roots = ceil_log clength \<and>
        ro_absorb_lookup_chain s (PState adversary_initial_state)
          ([fr] @ trace_roots @ [trace_final]) alpha_start \<and>
        ro_alpha_lookup_prefix M
          (PAlphaCounter adversary_initial_state)
          alpha_start alpha_prefix pivot_state \<and>
        length alpha_prefix =
          composition_alpha_pivot
            (low_degree_trace_witness
              (robust_alpha_pivot_trace_table M fr trace_roots)) \<and>
        x = AlphaChallenge
          (PAlphaCounter adversary_initial_state + length alpha_prefix)
          pivot_state \<and>
        y \<in> composition_trace_bad_alpha_pivot_values
          (robust_alpha_pivot_trace_table M fr trace_roots)
          alpha_prefix))"

lemma robust_alpha_pivot_absorbed_query_relationD:
  assumes rel: "robust_alpha_pivot_absorbed_query_relation M x y"
  obtains fr trace_roots trace_final alpha_start alpha_prefix pivot_state
  where
    "\<not> hash_map_output_collision (channel_for_hash_map M)"
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
    "length trace_roots = ceil_log clength"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state)
      ([fr] @ trace_roots @ [trace_final]) alpha_start"
    "ro_alpha_lookup_prefix M
      (PAlphaCounter adversary_initial_state)
      alpha_start alpha_prefix pivot_state"
    "length alpha_prefix =
      composition_alpha_pivot
        (low_degree_trace_witness
          (robust_alpha_pivot_trace_table M fr trace_roots))"
    "x = AlphaChallenge
      (PAlphaCounter adversary_initial_state + length alpha_prefix)
      pivot_state"
    "y \<in> composition_trace_bad_alpha_pivot_values
      (robust_alpha_pivot_trace_table M fr trace_roots)
      alpha_prefix"
  using rel
  unfolding robust_alpha_pivot_absorbed_query_relation_def Let_def
  by blast

lemma robust_alpha_pivot_absorbed_query_relation_direct_fiber_card_bound:
  "card {y.
      hash_state_relation_direct_activation
        robust_alpha_pivot_absorbed_query_relation M x y} \<le> 1"
proof (cases "{y.
    hash_state_relation_direct_activation
      robust_alpha_pivot_absorbed_query_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
      "hash_state_relation_direct_activation
        robust_alpha_pivot_absorbed_query_relation M x y0"
    by blast
  have rel0:
      "robust_alpha_pivot_absorbed_query_relation (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from robust_alpha_pivot_absorbed_query_relationD[OF rel0]
  obtain fr0 trace_roots0 trace_final0 alpha_start0 alpha_prefix0
      pivot_state0 where
    clean0:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y0 M))"
    and no_initial0:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y0 M))"
    and trace_len0: "length trace_roots0 = ceil_log clength"
    and header_chain0:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state)
        ([fr0] @ trace_roots0 @ [trace_final0]) alpha_start0"
    and alpha_chain0:
      "ro_alpha_lookup_prefix (fmupd x y0 M)
        (PAlphaCounter adversary_initial_state)
        alpha_start0 alpha_prefix0 pivot_state0"
    and pivot_len0:
      "length alpha_prefix0 =
        composition_alpha_pivot
          (low_degree_trace_witness
            (robust_alpha_pivot_trace_table
              (fmupd x y0 M) fr0 trace_roots0))"
    and x0:
      "x = AlphaChallenge
        (PAlphaCounter adversary_initial_state + length alpha_prefix0)
        pivot_state0"
    and y0_mem:
      "y0 \<in> composition_trace_bad_alpha_pivot_values
        (robust_alpha_pivot_trace_table (fmupd x y0 M) fr0 trace_roots0)
        alpha_prefix0"
    .
  let ?T0 =
    "robust_alpha_pivot_trace_table (fmupd x y0 M) fr0 trace_roots0"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          robust_alpha_pivot_absorbed_query_relation M x y}
        \<subseteq> composition_trace_bad_alpha_pivot_values ?T0 alpha_prefix0"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          robust_alpha_pivot_absorbed_query_relation M x y}"
    have rely:
        "robust_alpha_pivot_absorbed_query_relation (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from robust_alpha_pivot_absorbed_query_relationD[OF rely]
    obtain fr trace_roots trace_final alpha_start alpha_prefix
        pivot_state where
      clean:
        "\<not> hash_map_output_collision
          (channel_for_hash_map (fmupd x y M))"
      and no_initial:
        "PState adversary_initial_state \<notin>
          hash_map_output_values (channel_for_hash_map (fmupd x y M))"
      and trace_len: "length trace_roots = ceil_log clength"
      and header_chain:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y M))
          (PState adversary_initial_state)
          ([fr] @ trace_roots @ [trace_final]) alpha_start"
      and alpha_chain:
        "ro_alpha_lookup_prefix (fmupd x y M)
          (PAlphaCounter adversary_initial_state)
          alpha_start alpha_prefix pivot_state"
      and pivot_len:
        "length alpha_prefix =
          composition_alpha_pivot
            (low_degree_trace_witness
              (robust_alpha_pivot_trace_table
                (fmupd x y M) fr trace_roots))"
      and x_eq:
        "x = AlphaChallenge
          (PAlphaCounter adversary_initial_state + length alpha_prefix)
          pivot_state"
      and y_mem:
        "y \<in> composition_trace_bad_alpha_pivot_values
          (robust_alpha_pivot_trace_table (fmupd x y M) fr trace_roots)
          alpha_prefix"
      .
    have prefix_len_eq: "length alpha_prefix = length alpha_prefix0"
      and pivot_state_eq: "pivot_state = pivot_state0"
      using x_eq x0 by simp_all
    have header_chain_base:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          ([fr] @ trace_roots @ [trace_final]) alpha_start"
      using header_chain unfolding x_eq
      by (simp only: ro_absorb_lookup_chain_alpha_challenge_update)
    have header_chain_ref:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          ([fr] @ trace_roots @ [trace_final]) alpha_start"
      using header_chain_base unfolding x0
      by (simp only: ro_absorb_lookup_chain_alpha_challenge_update)
    have alpha_chain_base:
        "ro_alpha_lookup_prefix M
          (PAlphaCounter adversary_initial_state)
          alpha_start alpha_prefix pivot_state"
    proof -
      have updated:
          "ro_alpha_lookup_prefix
            (fmupd
              (AlphaChallenge
                (PAlphaCounter adversary_initial_state +
                  length alpha_prefix)
                pivot_state)
              y M)
            (PAlphaCounter adversary_initial_state)
            alpha_start alpha_prefix pivot_state"
        using alpha_chain unfolding x_eq .
      show ?thesis
        by (rule iffD1[
              OF ro_alpha_lookup_prefix_future_update[OF refl]])
          (rule updated)
    qed
    have alpha_chain_ref:
        "ro_alpha_lookup_prefix (fmupd x y0 M)
          (PAlphaCounter adversary_initial_state)
          alpha_start alpha_prefix pivot_state"
    proof -
      have updated:
          "ro_alpha_lookup_prefix
            (fmupd
              (AlphaChallenge
                (PAlphaCounter adversary_initial_state +
                  length alpha_prefix)
                pivot_state0)
              y0 M)
            (PAlphaCounter adversary_initial_state)
            alpha_start alpha_prefix pivot_state"
        by (rule iffD2[
              OF ro_alpha_lookup_prefix_future_update[OF refl]])
          (rule alpha_chain_base)
      show ?thesis
        using updated unfolding x0 prefix_len_eq .
    qed
    have alpha_absorb:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          alpha_start alpha_prefix pivot_state"
      by (rule ro_alpha_lookup_prefix_absorb_lookup_chain[OF alpha_chain_ref])
    have alpha_absorb0:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          alpha_start0 alpha_prefix0 pivot_state0"
      by (rule ro_alpha_lookup_prefix_absorb_lookup_chain[OF alpha_chain0])
    have full:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (([fr] @ trace_roots @ [trace_final]) @ alpha_prefix)
          pivot_state"
      by (rule ro_absorb_lookup_chain_append[
            OF header_chain_ref alpha_absorb])
    have full0:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (([fr0] @ trace_roots0 @ [trace_final0]) @ alpha_prefix0)
          pivot_state0"
      by (rule ro_absorb_lookup_chain_append[
            OF header_chain0 alpha_absorb0])
    have messages_eq:
        "([fr] @ trace_roots @ [trace_final]) @ alpha_prefix =
         ([fr0] @ trace_roots0 @ [trace_final0]) @ alpha_prefix0"
      by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
            OF clean0 no_initial0])
        (use full full0 pivot_state_eq in simp_all)
    have header_eq:
        "[fr] @ trace_roots @ [trace_final] =
         [fr0] @ trace_roots0 @ [trace_final0]"
    proof -
      let ?n = "Suc (Suc (ceil_log clength))"
      have take_eq:
          "take ?n
              (([fr] @ trace_roots @ [trace_final]) @ alpha_prefix) =
           take ?n
              (([fr0] @ trace_roots0 @ [trace_final0]) @ alpha_prefix0)"
        by (rule arg_cong[where f="take ?n"])
          (rule messages_eq)
      have left_take:
          "take ?n (([fr] @ trace_roots @ [trace_final]) @ alpha_prefix) =
           [fr] @ trace_roots @ [trace_final]"
        using trace_len by simp
      have right_take:
          "take ?n
              (([fr0] @ trace_roots0 @ [trace_final0]) @ alpha_prefix0) =
           [fr0] @ trace_roots0 @ [trace_final0]"
        using trace_len0 by simp
      show ?thesis
        using take_eq left_take right_take by simp
    qed
    have fields_eq:
        "fr = fr0 \<and> trace_roots = trace_roots0 \<and>
         trace_final = trace_final0"
      by (rule fixed_length_header_fields_eq[
            OF trace_len trace_len0 header_eq])
    have prefix_eq: "alpha_prefix = alpha_prefix0"
    proof -
      let ?n = "Suc (Suc (ceil_log clength))"
      have drop_eq:
          "drop ?n
              (([fr] @ trace_roots @ [trace_final]) @ alpha_prefix) =
           drop ?n
              (([fr0] @ trace_roots0 @ [trace_final0]) @ alpha_prefix0)"
        by (rule arg_cong[where f="drop ?n"])
          (rule messages_eq)
      have left_drop:
          "drop ?n
              (([fr] @ trace_roots @ [trace_final]) @ alpha_prefix) =
           alpha_prefix"
        using trace_len by simp
      have right_drop:
          "drop ?n
              (([fr0] @ trace_roots0 @ [trace_final0]) @ alpha_prefix0) =
           alpha_prefix0"
        using trace_len0 by simp
      show ?thesis
        using drop_eq left_drop right_drop by simp
    qed
    have table_eq:
        "robust_alpha_pivot_trace_table (fmupd x y M) fr trace_roots = ?T0"
      using fields_eq
      unfolding x0 robust_alpha_pivot_trace_table_def
        alpha_pivot_trace_table_def
      by simp
    show
      "y \<in> composition_trace_bad_alpha_pivot_values ?T0 alpha_prefix0"
      using y_mem table_eq prefix_eq by simp
  qed
  have finite_target:
      "finite
        (composition_trace_bad_alpha_pivot_values ?T0 alpha_prefix0)"
    by simp
  have card_le:
      "card {y.
        hash_state_relation_direct_activation
          robust_alpha_pivot_absorbed_query_relation M x y}
        \<le> card
          (composition_trace_bad_alpha_pivot_values ?T0 alpha_prefix0)"
    by (rule card_mono[OF finite_target subset])
  show ?thesis
    by (rule order_trans[OF card_le])
      (rule composition_trace_bad_alpha_pivot_values_card_le_one)
qed

lemma robust_alpha_pivot_absorbed_query_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "robust_alpha_pivot_absorbed_query_relation (fmupd x y M) k z"
    and no_target: "y \<notin> alpha_pivot_relation_drift_targets M x"
  shows "robust_alpha_pivot_absorbed_query_relation M k z"
proof -
  from robust_alpha_pivot_absorbed_query_relationD[OF rel]
  obtain fr trace_roots trace_final alpha_start alpha_prefix pivot_state where
    clean_new:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
    and no_initial_new:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y M))"
    and trace_len: "length trace_roots = ceil_log clength"
    and header_chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        ([fr] @ trace_roots @ [trace_final]) alpha_start"
    and alpha_chain_new:
      "ro_alpha_lookup_prefix (fmupd x y M)
        (PAlphaCounter adversary_initial_state)
        alpha_start alpha_prefix pivot_state"
    and pivot_len_new:
      "length alpha_prefix =
        composition_alpha_pivot
          (low_degree_trace_witness
            (robust_alpha_pivot_trace_table (fmupd x y M) fr trace_roots))"
    and k_eq:
      "k = AlphaChallenge
        (PAlphaCounter adversary_initial_state + length alpha_prefix)
        pivot_state"
    and z_mem_new:
      "z \<in> composition_trace_bad_alpha_pivot_values
        (robust_alpha_pivot_trace_table (fmupd x y M) fr trace_roots)
        alpha_prefix"
    .
  have old_lookup: "fmlookup M k = Some z"
    using active_lookup key_neq by simp
  have pivot_target: "pivot_state \<in> alpha_challenge_state_values M"
  proof -
    have
      "fmlookup M
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + length alpha_prefix)
          pivot_state) = Some z"
      using old_lookup k_eq by simp
    then show ?thesis by (rule alpha_challenge_lookup_state_value)
  qed
  have alpha_absorb_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        alpha_start alpha_prefix pivot_state"
    by (rule ro_alpha_lookup_prefix_absorb_lookup_chain[OF alpha_chain_new])
  have full_chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        (([fr] @ trace_roots @ [trace_final]) @ alpha_prefix)
        pivot_state"
    by (rule ro_absorb_lookup_chain_append[
          OF header_chain_new alpha_absorb_new])
  have full_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (([fr] @ trace_roots @ [trace_final]) @ alpha_prefix)
        pivot_state"
    by (rule ro_absorb_lookup_chain_alpha_final_fresh_update_pullback[
          OF fresh full_chain_new pivot_target no_target])
  from ro_absorb_lookup_chain_append_split[OF full_chain_old]
  obtain alpha_start_old where
    header_chain_old0:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        ([fr] @ trace_roots @ [trace_final]) alpha_start_old"
    and alpha_absorb_old0:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        alpha_start_old alpha_prefix pivot_state"
    by blast
  have ext:
      "channel_for_hash_map M \<le>
       channel_for_hash_map (fmupd x y M)"
    by (rule channel_for_hash_map_fresh_update_extends[OF fresh])
  have header_chain_old_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state)
        ([fr] @ trace_roots @ [trace_final]) alpha_start_old"
    by (rule ro_absorb_lookup_chain_mono[OF header_chain_old0 ext])
  have alpha_start_eq: "alpha_start_old = alpha_start"
    by (rule ro_absorb_lookup_chain_functional[
          OF header_chain_old_new header_chain_new])
  have header_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        ([fr] @ trace_roots @ [trace_final]) alpha_start"
    using header_chain_old0 alpha_start_eq by simp
  have alpha_absorb_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        alpha_start alpha_prefix pivot_state"
    using alpha_absorb_old0 alpha_start_eq by simp
  have alpha_chain_old:
      "ro_alpha_lookup_prefix M
        (PAlphaCounter adversary_initial_state)
        alpha_start alpha_prefix pivot_state"
    by (rule ro_alpha_lookup_prefix_fresh_update_pullback[
          OF fresh alpha_chain_new alpha_absorb_old no_target])
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
  have full_messages_target:
      "set (([fr] @ trace_roots @ [trace_final]) @ alpha_prefix)
        \<subseteq> transcript_absorb_message_values M"
    by (rule ro_absorb_lookup_chain_messages_subset[OF full_chain_old])
  have selected_root_target:
      "alpha_pivot_trace_root fr trace_roots \<in>
        transcript_absorb_message_values M"
    using full_messages_target
    unfolding alpha_pivot_trace_root_def
    by (cases trace_roots) auto
  have no_selected_target:
      "y \<notin> first_root_relation_drift_targets M x"
    using no_target
    unfolding alpha_pivot_relation_drift_targets_def by blast
  have trace_table_eq:
      "robust_alpha_pivot_trace_table (fmupd x y M) fr trace_roots =
       robust_alpha_pivot_trace_table M fr trace_roots"
    unfolding robust_alpha_pivot_trace_table_def alpha_pivot_trace_table_def
    using conceptual_table_fresh_update[
      OF fresh selected_root_target no_selected_target]
    by simp
  have pivot_len_old:
      "length alpha_prefix =
        composition_alpha_pivot
          (low_degree_trace_witness
            (robust_alpha_pivot_trace_table M fr trace_roots))"
    using pivot_len_new trace_table_eq by simp
  have z_mem_old:
      "z \<in> composition_trace_bad_alpha_pivot_values
        (robust_alpha_pivot_trace_table M fr trace_roots)
        alpha_prefix"
    using z_mem_new trace_table_eq by simp
  show ?thesis
    unfolding robust_alpha_pivot_absorbed_query_relation_def Let_def
    using clean_old no_initial_old trace_len
      header_chain_old alpha_chain_old pivot_len_old k_eq z_mem_old
    by blast
qed

lemma robust_alpha_pivot_absorbed_query_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        robust_alpha_pivot_absorbed_query_relation M x y"
  shows "y \<in> alpha_pivot_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> alpha_pivot_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        robust_alpha_pivot_absorbed_query_relation (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        robust_alpha_pivot_absorbed_query_relation M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "robust_alpha_pivot_absorbed_query_relation (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def
    by blast+
  have rel_old:
      "robust_alpha_pivot_absorbed_query_relation M k z"
    by (rule
      robust_alpha_pivot_absorbed_query_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
      "hash_state_relation_active
        robust_alpha_pivot_absorbed_query_relation M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed

lemma robust_alpha_pivot_absorbed_query_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        robust_alpha_pivot_absorbed_query_relation M x y}
      \<le> 6 * card (fmdom' M) + 2"
proof -
  have subset:
      "{y.
        hash_state_relation_drift_activation
          robust_alpha_pivot_absorbed_query_relation M x y}
        \<subseteq> alpha_pivot_relation_drift_targets M x"
    using
      robust_alpha_pivot_absorbed_query_relation_drift_activation_imp_target[
        OF fresh]
    by blast
  have
      "card {y.
        hash_state_relation_drift_activation
          robust_alpha_pivot_absorbed_query_relation M x y}
        \<le> card (alpha_pivot_relation_drift_targets M x)"
    by (rule card_mono[
          OF finite_alpha_pivot_relation_drift_targets subset])
  also have "... \<le> 6 * card (fmdom' M) + 2"
    by (rule card_alpha_pivot_relation_drift_targets_le)
  finally show ?thesis .
qed


lemma robust_alpha_pivot_bounded_transition_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_transition
        (conditioned_fri_relation_bounded L
          robust_alpha_pivot_absorbed_query_relation)
        M (fmupd x y M)}
      \<le> 1 + (6 * L + 2)"
proof (rule conditioned_fri_bounded_transition_fiber_card_bound[
    OF fresh])
  assume "card (fmdom' M) \<le> L"
  show
    "card {y.
      hash_state_relation_direct_activation
        robust_alpha_pivot_absorbed_query_relation M x y} \<le> 1"
    by (rule
      robust_alpha_pivot_absorbed_query_relation_direct_fiber_card_bound)
next
  assume domain: "card (fmdom' M) \<le> L"
  have
    "card {y.
      hash_state_relation_drift_activation
        robust_alpha_pivot_absorbed_query_relation M x y}
      \<le> 6 * card (fmdom' M) + 2"
    by (rule
      robust_alpha_pivot_absorbed_query_relation_drift_fiber_card_bound[
        OF fresh])
  also have "... \<le> 6 * L + 2"
    by (rule add_le_mono[OF mult_left_mono[OF domain] order_refl], simp)
  finally show
    "card {y.
      hash_state_relation_drift_activation
        robust_alpha_pivot_absorbed_query_relation M x y}
      \<le> 6 * L + 2"
    .
qed

lemma
  wp_ro_checked_staged_transcript_with_query_witnesses_robust_alpha_pivot_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded q
          robust_alpha_pivot_absorbed_query_relation)
        (HashMap adversary_initial_state))
      adversary_initial_state
      \<le> nnreal (q * (1 + (6 * q + 2))) / nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B = "1 + (6 * ?Q + 2)"
  have steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition
            (conditioned_fri_relation_bounded ?Q
              robust_alpha_pivot_absorbed_query_relation)
            M (fmupd x y M)}
          \<le> ?B"
    by (rule robust_alpha_pivot_bounded_transition_fiber_card_bound)
  have bound:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (conditioned_fri_relation_bounded ?Q
            robust_alpha_pivot_absorbed_query_relation)
          (HashMap adversary_initial_state))
        adversary_initial_state
        \<le> nnreal (?Q * ?B) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound_all_rounds[
        OF wf controlled steps])
  show ?thesis
    using bound unfolding q_def by simp
qed


definition robust_first_trace_fri_root_prefix_first_table
where
  "robust_first_trace_fri_root_prefix_first_table prefix prefix_state =
    fri_canonical_decoded_table (clength - 1)
      (first_trace_fri_root_prefix_first_table prefix prefix_state)"

lemma robust_alpha_pivot_trace_table_nonempty:
  assumes "trace_roots \<noteq> []"
  shows
    "robust_alpha_pivot_trace_table M fr trace_roots =
      robust_first_trace_fri_root_prefix_first_table
        (fr, [], hd trace_roots) (channel_for_hash_map M)"
  using alpha_pivot_trace_table_nonempty[OF assms, of M fr]
  unfolding robust_alpha_pivot_trace_table_def
    robust_first_trace_fri_root_prefix_first_table_def
  by simp

definition robust_alpha_pivot_absorbed_query_relation_bounded
  :: "nat \<Rightarrow> (('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "robust_alpha_pivot_absorbed_query_relation_bounded L M x y \<longleftrightarrow>
    card (fmdom' M) \<le> L \<and>
    robust_alpha_pivot_absorbed_query_relation M x y"

lemma robust_alpha_pivot_absorbed_query_relation_bounded_eq:
  "robust_alpha_pivot_absorbed_query_relation_bounded L =
    conditioned_fri_relation_bounded L
      robust_alpha_pivot_absorbed_query_relation"
  by (rule ext)+
    (simp add: robust_alpha_pivot_absorbed_query_relation_bounded_def
      conditioned_fri_relation_bounded_def)

lemma robust_trace_composition_bad_alpha_imp_alpha_pivot_relation_transition:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
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
    and no_trace_merkle:
      "\<not> hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state attacker_state"
    and as_bad:
      "staged_alphas data \<in>
        composition_trace_bad_alpha_space
          (robust_first_trace_fri_root_prefix_first_table prefix prefix_state)"
  shows
    "hash_state_relation_transition
      (robust_alpha_pivot_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have canonical_props:
      "prefix =
          (staged_trace_root data, [],
            hd (staged_trace_fri_roots data)) \<and>
       prefix_state \<le> attacker_state"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_prefix_canonical[
        OF wf controlled nonempty outcome])
  then have prefix_eq:
      "prefix =
        (staged_trace_root data, [],
          hd (staged_trace_fri_roots data))"
    and prefix_ext: "prefix_state \<le> attacker_state"
    by blast+

  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty outcome])
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_alphas data) = length spec"
    using ro_checked_staged_transcript_program_outcome_shape[
      OF original_out]
    by blast
  have trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    and alpha_len: "length (staged_alphas data) = length spec"
    using shape by blast+
  have trace_nonempty: "staged_trace_fri_roots data \<noteq> []"
    using trace_len nonempty by auto
  from ro_checked_staged_transcript_program_alpha_lookup_chain[
    OF wf controlled original_out]
  obtain alpha_start alpha_final where
    prealpha_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state)
        ([staged_trace_root data] @
          staged_trace_fri_roots data @
          [staged_trace_final data])
        alpha_start"
    and alpha_chain:
      "ro_alpha_lookup_prefix (HashMap attacker_state)
        (PAlphaCounter adversary_initial_state)
        alpha_start (staged_alphas data) alpha_final"
    by blast

  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision attacker_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_ext])
    then show False using clean by contradiction
  qed
  have no_trace_merkle':
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets
          {staged_trace_root data, hd (staged_trace_fri_roots data)}
          prefix_state)
        prefix_state attacker_state"
    using no_trace_merkle prefix_clean
    unfolding prefix_eq first_trace_fri_root_prefix_merkle_targets_def
    by simp
  have first_targets:
      "merkle_prefix_path_targets
          {hd (staged_trace_fri_roots data)} prefix_state
        \<subseteq>
       merkle_prefix_path_targets
          {staged_trace_root data, hd (staged_trace_fri_roots data)}
          prefix_state"
    by (rule merkle_prefix_path_targets_mono) auto
  have no_first:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets
          {hd (staged_trace_fri_roots data)} prefix_state)
        prefix_state attacker_state"
    using no_trace_merkle'
      hash_map_new_output_hit_subset[OF first_targets]
    by blast

  let ?final = "channel_for_hash_map (HashMap attacker_state)"
  have final_map: "HashMap ?final = HashMap attacker_state"
    unfolding channel_for_hash_map_def by simp
  have first_final:
      "robust_first_trace_fri_root_prefix_first_table
          (staged_trace_root data, [],
            hd (staged_trace_fri_roots data))
          ?final =
       robust_first_trace_fri_root_prefix_first_table
          (staged_trace_root data, [],
            hd (staged_trace_fri_roots data))
          prefix_state"
  proof -
    have final_attacker:
        "conceptual_table ?final
            (hd (staged_trace_fri_roots data)) (scale * clength) =
         conceptual_table attacker_state
            (hd (staged_trace_fri_roots data)) (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have attacker_prefix:
        "conceptual_table attacker_state
            (hd (staged_trace_fri_roots data)) (scale * clength) =
         conceptual_table prefix_state
            (hd (staged_trace_fri_roots data)) (scale * clength)"
      by (rule conceptual_table_prefix_stable_if_no_target[
        OF prefix_ext no_first])
    show ?thesis
      unfolding robust_first_trace_fri_root_prefix_first_table_def
        first_trace_fri_root_prefix_first_table_def
      using final_attacker attacker_prefix by simp
  qed
  have as_bad_final:
      "staged_alphas data \<in>
        composition_trace_bad_alpha_space
          (robust_first_trace_fri_root_prefix_first_table
            (staged_trace_root data, [],
              hd (staged_trace_fri_roots data))
            ?final)"
    using as_bad prefix_eq first_final by simp
  have violated:
      "violated_constraints
        (low_degree_trace_witness
          (robust_first_trace_fri_root_prefix_first_table
            (staged_trace_root data, [],
              hd (staged_trace_fri_roots data))
            ?final)) \<noteq> {}"
    by (rule composition_trace_bad_alpha_space_violated[OF as_bad_final])
  let ?pivot =
    "composition_alpha_pivot
      (low_degree_trace_witness
        (robust_first_trace_fri_root_prefix_first_table
          (staged_trace_root data, [],
            hd (staged_trace_fri_roots data))
          ?final))"
  have pivot_spec: "?pivot < length spec"
    by (rule composition_alpha_pivot_bound[OF violated])
  have pivot_bound: "?pivot < length (staged_alphas data)"
    using pivot_spec alpha_len by simp
  from ro_alpha_lookup_prefix_take_lookup[
    OF alpha_chain pivot_bound]
  obtain pivot_state where
    alpha_prefix:
      "ro_alpha_lookup_prefix (HashMap attacker_state)
        (PAlphaCounter adversary_initial_state)
        alpha_start (take ?pivot (staged_alphas data)) pivot_state"
    and pivot_lookup:
      "fmlookup (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state) =
        Some (staged_alphas data ! ?pivot)"
    by blast
  have pivot_member:
      "staged_alphas data ! ?pivot \<in>
        composition_trace_bad_alpha_pivot_values
          (robust_first_trace_fri_root_prefix_first_table
            (staged_trace_root data, [],
              hd (staged_trace_fri_roots data))
            ?final)
          (take ?pivot (staged_alphas data))"
    by (rule
      composition_trace_bad_alpha_pivot_value_member[OF as_bad_final])
  have prefix_length:
      "length (take ?pivot (staged_alphas data)) = ?pivot"
    using pivot_bound by simp

  have prealpha_final:
      "ro_absorb_lookup_chain ?final
        (PState adversary_initial_state)
        ([staged_trace_root data] @
          staged_trace_fri_roots data @
          [staged_trace_final data])
        alpha_start"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule prealpha_chain)
  have clean_final: "\<not> hash_map_output_collision ?final"
    using clean final_map
    unfolding hash_map_output_collision_def by simp
  have no_initial_final:
      "PState adversary_initial_state \<notin> hash_map_output_values ?final"
    using no_initial final_map
    unfolding hash_map_output_values_def by simp
  have trace_table_eq:
      "robust_alpha_pivot_trace_table (HashMap attacker_state)
          (staged_trace_root data) (staged_trace_fri_roots data) =
       robust_first_trace_fri_root_prefix_first_table
          (staged_trace_root data, [], hd (staged_trace_fri_roots data))
          ?final"
    by (rule robust_alpha_pivot_trace_table_nonempty[OF trace_nonempty])
  have relation:
      "robust_alpha_pivot_absorbed_query_relation
        (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding robust_alpha_pivot_absorbed_query_relation_def Let_def
  proof (intro conjI)
    show "\<not> hash_map_output_collision ?final"
      by (rule clean_final)
    show "PState adversary_initial_state \<notin> hash_map_output_values ?final"
      by (rule no_initial_final)
    show
      "\<exists>fr trace_roots trace_final alpha_start' alpha_prefix pivot_state'.
        length trace_roots = ceil_log clength \<and>
        ro_absorb_lookup_chain ?final
          (PState adversary_initial_state)
          ([fr] @ trace_roots @ [trace_final]) alpha_start' \<and>
        ro_alpha_lookup_prefix (HashMap attacker_state)
          (PAlphaCounter adversary_initial_state)
          alpha_start' alpha_prefix pivot_state' \<and>
        length alpha_prefix =
          composition_alpha_pivot
            (low_degree_trace_witness
              (robust_alpha_pivot_trace_table
                (HashMap attacker_state) fr trace_roots)) \<and>
        AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state =
          AlphaChallenge
            (PAlphaCounter adversary_initial_state + length alpha_prefix)
            pivot_state' \<and>
        staged_alphas data ! ?pivot \<in>
          composition_trace_bad_alpha_pivot_values
            (robust_alpha_pivot_trace_table
              (HashMap attacker_state) fr trace_roots)
            alpha_prefix"
    proof (rule exI[of _ "staged_trace_root data"],
        rule exI[of _ "staged_trace_fri_roots data"],
        rule exI[of _ "staged_trace_final data"],
        rule exI[of _ alpha_start],
        rule exI[of _ "take ?pivot (staged_alphas data)"],
        rule exI[of _ pivot_state],
        intro conjI)
      show "length (staged_trace_fri_roots data) = ceil_log clength"
        by (rule trace_len)
      show
        "ro_absorb_lookup_chain ?final
          (PState adversary_initial_state)
          ([staged_trace_root data] @ staged_trace_fri_roots data @
            [staged_trace_final data])
          alpha_start"
        by (rule prealpha_final)
      show
        "ro_alpha_lookup_prefix (HashMap attacker_state)
          (PAlphaCounter adversary_initial_state)
          alpha_start (take ?pivot (staged_alphas data)) pivot_state"
        by (rule alpha_prefix)
      show
        "length (take ?pivot (staged_alphas data)) =
          composition_alpha_pivot
            (low_degree_trace_witness
              (robust_alpha_pivot_trace_table
                (HashMap attacker_state)
                (staged_trace_root data)
                (staged_trace_fri_roots data)))"
        using prefix_length trace_table_eq by simp
      show
        "AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state =
         AlphaChallenge
          (PAlphaCounter adversary_initial_state +
            length (take ?pivot (staged_alphas data)))
          pivot_state"
        using prefix_length by simp
      show
        "staged_alphas data ! ?pivot \<in>
          composition_trace_bad_alpha_pivot_values
            (robust_alpha_pivot_trace_table
              (HashMap attacker_state)
              (staged_trace_root data)
              (staged_trace_fri_roots data))
            (take ?pivot (staged_alphas data))"
        using pivot_member trace_table_eq by simp
    qed
  qed
  have map_bound:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound[
        OF wf controlled nonempty outcome clean])
  have bounded_relation:
      "robust_alpha_pivot_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding robust_alpha_pivot_absorbed_query_relation_bounded_def
    using map_bound relation by simp
  have active:
      "hash_state_relation_active
        (robust_alpha_pivot_absorbed_query_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets))
        (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding hash_state_relation_active_def
    using pivot_lookup bounded_relation by simp
  have inactive_initial:
      "\<not> hash_state_relation_active
        (robust_alpha_pivot_absorbed_query_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets))
        (HashMap adversary_initial_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding hash_state_relation_active_def adversary_initial_state_def
    by simp
  show ?thesis
    unfolding hash_state_relation_transition_def
    using active inactive_initial by blast
qed


definition
  ro_checked_staged_first_root_robust_decoded_all_queries_consistent
where
  "ro_checked_staged_first_root_robust_decoded_all_queries_consistent out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        (let decoded_trace =
          robust_first_trace_fri_root_prefix_first_table prefix prefix_state;
             decoded_composition =
          fri_canonical_decoded_table (to_nat (staged_degree data))
            (ro_actual_query_composition_candidate data query_start)
         in composition_table_low_degree maxDegree decoded_composition \<and>
            all_queries_consistent decoded_trace decoded_composition
              (staged_alphas data)))"

definition
  ro_checked_staged_first_root_robust_alpha_pivot_side_event
where
  "ro_checked_staged_first_root_robust_alpha_pivot_side_event budgets out \<longleftrightarrow>
    final_hash_collision_event out \<or>
    hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state out \<or>
    ro_checked_staged_first_root_prefix_merkle_target_hit out \<or>
    hash_state_relation_transition_event
      (robust_alpha_pivot_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state) out"

definition ro_checked_staged_first_root_robust_alpha_pivot_error
where
  "ro_checked_staged_first_root_robust_alpha_pivot_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in hash_collision_budget_value 0 q +
       nnreal q / nnreal size +
       ro_checked_staged_first_root_prefix_merkle_target_error budgets +
       nnreal (q * (1 + (6 * q + 2))) / nnreal size)"

lemma
  ro_checked_staged_first_root_robust_decoded_all_queries_consistent_some_imp_alpha_pivot_side_event:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and all_consistent:
      "ro_checked_staged_first_root_robust_decoded_all_queries_consistent
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
  shows
    "ro_checked_staged_first_root_robust_alpha_pivot_side_event budgets
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
proof -
  let ?trace =
    "robust_first_trace_fri_root_prefix_first_table prefix prefix_state"
  let ?composition =
    "fri_canonical_decoded_table (to_nat (staged_degree data))
      (ro_actual_query_composition_candidate data query_start)"
  have low_and_consistent:
      "composition_table_low_degree maxDegree ?composition \<and>
       all_queries_consistent ?trace ?composition (staged_alphas data)"
    using all_consistent
    unfolding
      ro_checked_staged_first_root_robust_decoded_all_queries_consistent_def
      Let_def
    by simp
  have trace_low: "trace_table_low_degree ?trace"
    unfolding robust_first_trace_fri_root_prefix_first_table_def
    by (rule fri_canonical_decoded_trace_table_low_degree)
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty outcome])
  have alpha_len: "length (staged_alphas data) = length spec"
    using ro_checked_staged_transcript_program_outcome_shape[
      OF original_out]
    by blast
  have as_bad:
      "staged_alphas data \<in>
        composition_trace_bad_alpha_space ?trace"
    by (rule
      low_degree_all_queries_consistent_imp_composition_trace_bad_alpha_space[
        OF false_statement alpha_len trace_low])
      (use low_and_consistent in blast)+

  show ?thesis
  proof (cases "hash_map_output_collision attacker_state")
    case True
    then show ?thesis
      unfolding
        ro_checked_staged_first_root_robust_alpha_pivot_side_event_def
        final_hash_collision_event_def
      by simp
  next
    case clean: False
    show ?thesis
    proof (cases
        "PState adversary_initial_state \<in>
          hash_map_output_values attacker_state")
      case True
      then obtain x where final_lookup:
          "fmlookup (HashMap attacker_state) x =
            Some (PState adversary_initial_state)"
        unfolding hash_map_output_values_def by blast
      have initial_lookup:
          "fmlookup (HashMap adversary_initial_state) x = None"
        unfolding adversary_initial_state_def by simp
      have initial_hit:
          "hash_map_new_output_hit {PState adversary_initial_state}
            adversary_initial_state attacker_state"
        unfolding hash_map_new_output_hit_def
        using initial_lookup final_lookup by blast
      then show ?thesis
        unfolding
          ro_checked_staged_first_root_robust_alpha_pivot_side_event_def
          hash_new_output_hit_event_def
        by simp
    next
      case no_initial: False
      show ?thesis
      proof (cases
          "hash_map_new_output_hit
            (first_trace_fri_root_prefix_merkle_targets
              prefix prefix_state)
            prefix_state attacker_state")
        case True
        then show ?thesis
          unfolding
            ro_checked_staged_first_root_robust_alpha_pivot_side_event_def
            ro_checked_staged_first_root_prefix_merkle_target_hit_def
          by simp
      next
        case no_merkle: False
        have relation:
            "hash_state_relation_transition
              (robust_alpha_pivot_absorbed_query_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets))
              (HashMap adversary_initial_state)
              (HashMap attacker_state)"
          by (rule
            robust_trace_composition_bad_alpha_imp_alpha_pivot_relation_transition[
              OF wf controlled nonempty outcome clean no_initial no_merkle
                as_bad])
        then show ?thesis
          unfolding
            ro_checked_staged_first_root_robust_alpha_pivot_side_event_def
            hash_state_relation_transition_event_def
          by simp
      qed
    qed
  qed
qed

lemma
  ro_checked_staged_first_root_robust_decoded_all_queries_consistent_imp_alpha_pivot_side_event:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and all_consistent:
      "ro_checked_staged_first_root_robust_decoded_all_queries_consistent out"
  shows
    "ro_checked_staged_first_root_robust_alpha_pivot_side_event budgets out"
proof (cases out)
  case None
  then show ?thesis
    using all_consistent
    unfolding
      ro_checked_staged_first_root_robust_decoded_all_queries_consistent_def
    by simp
next
  case (Some packed)
  obtain prefix prefix_state data query_start raws query_states
      attacker_state where packed_eq:
    "packed =
      (((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)"
    by (cases packed) (auto split: prod.splits)
  have outcome:
    "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          adversary_initial_state)"
    using support unfolding Some packed_eq .
  have all_consistent':
    "ro_checked_staged_first_root_robust_decoded_all_queries_consistent
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
    using all_consistent unfolding Some packed_eq .
  have side:
    "ro_checked_staged_first_root_robust_alpha_pivot_side_event budgets
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
    by (rule
      ro_checked_staged_first_root_robust_decoded_all_queries_consistent_some_imp_alpha_pivot_side_event[
        OF false_statement wf controlled nonempty outcome all_consistent'])
  show ?thesis
    using side unfolding Some packed_eq .
qed

lemma wp_ro_checked_staged_first_root_robust_decoded_all_queries_consistent_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_first_root_robust_decoded_all_queries_consistent
      adversary_initial_state
    \<le> ro_checked_staged_first_root_robust_alpha_pivot_error budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?All =
    "ro_checked_staged_first_root_robust_decoded_all_queries_consistent"
  let ?Collision = "final_hash_collision_event"
  let ?Initial =
    "hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state"
  let ?Merkle = "ro_checked_staged_first_root_prefix_merkle_target_hit"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?Relation =
    "hash_state_relation_transition_event
      (robust_alpha_pivot_absorbed_query_relation_bounded ?q)
      (HashMap adversary_initial_state)"
  have event_le:
    "wp_event ?M ?All adversary_initial_state \<le>
      wp_event ?M
        (ro_checked_staged_first_root_robust_alpha_pivot_side_event budgets)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and all_consistent: "?All out"
    show "ro_checked_staged_first_root_robust_alpha_pivot_side_event budgets out"
      by (rule
        ro_checked_staged_first_root_robust_decoded_all_queries_consistent_imp_alpha_pivot_side_event[
          OF false_statement wf controlled nonempty support all_consistent])
  qed
  have union:
    "wp_event ?M
        (ro_checked_staged_first_root_robust_alpha_pivot_side_event budgets)
        adversary_initial_state
      \<le> wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Initial adversary_initial_state +
        wp_event ?M ?Merkle adversary_initial_state +
        wp_event ?M ?Relation adversary_initial_state"
    unfolding ro_checked_staged_first_root_robust_alpha_pivot_side_event_def
    by (rule wp_event_union_bound4)
  have collision:
    "wp_event ?M ?Collision adversary_initial_state \<le>
      hash_collision_budget_value 0 ?q"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_collision_bound[
        OF wf controlled nonempty])
  have initial:
    "wp_event ?M ?Initial adversary_initial_state \<le>
      nnreal ?q / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_initial_target_bound[
        OF wf controlled nonempty])
  have merkle:
    "wp_event ?M ?Merkle adversary_initial_state \<le>
      ro_checked_staged_first_root_prefix_merkle_target_error budgets"
    by (rule
      wp_ro_checked_staged_first_root_prefix_merkle_target_hit_bound[
        OF nonempty wf controlled])
  have relation:
    "wp_event ?M ?Relation adversary_initial_state \<le>
      nnreal (?q * (1 + (6 * ?q + 2))) / nnreal size"
    unfolding robust_alpha_pivot_absorbed_query_relation_bounded_eq
    by (rule
      wp_ro_checked_staged_transcript_with_query_witnesses_robust_alpha_pivot_relation[
        OF wf controlled])
  have closed:
    "wp_event ?M
        (ro_checked_staged_first_root_robust_alpha_pivot_side_event budgets)
        adversary_initial_state
      \<le> ro_checked_staged_first_root_robust_alpha_pivot_error budgets"
    apply (rule order_trans[OF union])
    unfolding ro_checked_staged_first_root_robust_alpha_pivot_error_def Let_def
    apply (intro add_mono)
       apply (rule collision)
      apply (rule initial)
     apply (rule merkle)
    apply (rule relation)
    done
  show ?thesis
    by (rule order_trans[OF event_le closed])
qed


end
end
