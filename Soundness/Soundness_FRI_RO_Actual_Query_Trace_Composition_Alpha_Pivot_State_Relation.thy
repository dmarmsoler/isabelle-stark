theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_State_Relation
  imports Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Fiber
begin

context soundness
begin

primrec ro_alpha_lookup_prefix
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> bool"
where
  "ro_alpha_lookup_prefix M c st [] final \<longleftrightarrow> final = st"
| "ro_alpha_lookup_prefix M c st (a # as) final \<longleftrightarrow>
    (\<exists>next.
      fmlookup M (AlphaChallenge c st) = Some a \<and>
      fmlookup M (TranscriptAbsorb st a) = Some next \<and>
      ro_alpha_lookup_prefix M (Suc c) next as final)"

lemma ro_alpha_lookup_prefix_absorb_lookup_chain:
  assumes chain: "ro_alpha_lookup_prefix M c st as final"
  shows
    "ro_absorb_lookup_chain (channel_for_hash_map M) st as final"
  using chain
proof (induction as arbitrary: c st)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then obtain st' where
    absorb:
      "fmlookup M (TranscriptAbsorb st a) = Some st'"
    and tail:
      "ro_alpha_lookup_prefix M (Suc c) st' as final"
    by auto
  have lookup:
      "fmlookup (HashMap (channel_for_hash_map M))
        (TranscriptAbsorb st a) = Some st'"
    using absorb unfolding channel_for_hash_map_def by simp
  have tail_absorb:
      "ro_absorb_lookup_chain
        (channel_for_hash_map M) st' as final"
    by (rule Cons.IH[OF tail])
  show ?case
    using lookup tail_absorb by auto
qed

definition alpha_challenge_state_values
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow> 'f set"
where
  "alpha_challenge_state_values M =
    {st. \<exists>c out. fmlookup M (AlphaChallenge c st) = Some out}"

lemma alpha_challenge_state_values_subset_image:
  "alpha_challenge_state_values M \<subseteq>
    Set.image
      (\<lambda>k. case k of AlphaChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
      (fmdom' M)"
  unfolding alpha_challenge_state_values_def
proof
  fix st
  assume "st \<in> {st. \<exists>c out.
    fmlookup M (AlphaChallenge c st) = Some out}"
  then obtain c out where
    lookup: "fmlookup M (AlphaChallenge c st) = Some out"
    by blast
  have dom: "AlphaChallenge c st \<in> fmdom' M"
    using lookup by (simp add: fmlookup_dom'_iff)
  show "st \<in> Set.image
    (\<lambda>k. case k of AlphaChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
    (fmdom' M)"
    by (rule image_eqI[OF _ dom]) simp
qed

lemma finite_alpha_challenge_state_values[simp]:
  "finite (alpha_challenge_state_values M)"
  by (rule finite_subset[OF alpha_challenge_state_values_subset_image])
    simp

lemma card_alpha_challenge_state_values_le:
  "card (alpha_challenge_state_values M) \<le> card (fmdom' M)"
proof -
  have "card (alpha_challenge_state_values M) \<le>
      card (Set.image
        (\<lambda>k. case k of AlphaChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
        (fmdom' M))"
    by (rule card_mono)
      (simp_all add: alpha_challenge_state_values_subset_image)
  also have "... \<le> card (fmdom' M)"
    by (rule card_image_le) simp
  finally show ?thesis .
qed

definition alpha_pivot_relation_drift_targets
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f set"
where
  "alpha_pivot_relation_drift_targets M x =
    first_root_relation_drift_targets M x \<union>
    alpha_challenge_state_values M"

lemma finite_alpha_pivot_relation_drift_targets[simp]:
  "finite (alpha_pivot_relation_drift_targets M x)"
  unfolding alpha_pivot_relation_drift_targets_def by simp

lemma card_alpha_pivot_relation_drift_targets_le:
  "card (alpha_pivot_relation_drift_targets M x)
    \<le> 6 * card (fmdom' M) + 2"
proof -
  have union:
      "card (alpha_pivot_relation_drift_targets M x) \<le>
        card (first_root_relation_drift_targets M x) +
        card (alpha_challenge_state_values M)"
    unfolding alpha_pivot_relation_drift_targets_def
    by (rule card_Un_le)
  have first:
      "card (first_root_relation_drift_targets M x)
        \<le> 5 * card (fmdom' M) + 2"
    by (rule card_first_root_relation_drift_targets_le)
  have alpha:
      "card (alpha_challenge_state_values M)
        \<le> card (fmdom' M)"
    by (rule card_alpha_challenge_state_values_le)
  show ?thesis
    by (rule order_trans[OF union]) (use first alpha in simp)
qed


definition alpha_pivot_trace_root
where
  "alpha_pivot_trace_root fr trace_roots =
    (if trace_roots = [] then fr else hd trace_roots)"

definition alpha_pivot_trace_table
where
  "alpha_pivot_trace_table M fr trace_roots =
    conceptual_table (channel_for_hash_map M)
      (alpha_pivot_trace_root fr trace_roots) (scale * clength)"

lemma alpha_pivot_trace_table_nonempty:
  assumes "trace_roots \<noteq> []"
  shows
    "alpha_pivot_trace_table M fr trace_roots =
      first_trace_fri_root_prefix_first_table
        (fr, [], hd trace_roots) (channel_for_hash_map M)"
  using assms
  unfolding alpha_pivot_trace_table_def alpha_pivot_trace_root_def
    first_trace_fri_root_prefix_first_table_def
  by simp

lemma alpha_pivot_trace_table_empty:
  assumes "trace_roots = []"
  shows
    "alpha_pivot_trace_table M fr trace_roots =
      conceptual_table (channel_for_hash_map M) fr (scale * clength)"
  using assms
  unfolding alpha_pivot_trace_table_def alpha_pivot_trace_root_def
  by simp

definition alpha_pivot_absorbed_query_relation
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "alpha_pivot_absorbed_query_relation M x y \<longleftrightarrow>
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
              (alpha_pivot_trace_table M fr trace_roots)) \<and>
        x = AlphaChallenge
          (PAlphaCounter adversary_initial_state + length alpha_prefix)
          pivot_state \<and>
        y \<in> composition_trace_bad_alpha_pivot_values
          (alpha_pivot_trace_table M fr trace_roots)
          alpha_prefix))"

lemma alpha_pivot_absorbed_query_relationD:
  assumes rel: "alpha_pivot_absorbed_query_relation M x y"
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
          (alpha_pivot_trace_table M fr trace_roots))"
    "x = AlphaChallenge
      (PAlphaCounter adversary_initial_state + length alpha_prefix)
      pivot_state"
    "y \<in> composition_trace_bad_alpha_pivot_values
      (alpha_pivot_trace_table M fr trace_roots)
      alpha_prefix"
  using rel
  unfolding alpha_pivot_absorbed_query_relation_def Let_def
  by blast

lemma fixed_length_header_fields_eq:
  assumes roots_len: "length roots = n"
    and roots0_len: "length roots0 = n"
    and eq:
      "[fr] @ roots @ [final] = [fr0] @ roots0 @ [final0]"
  shows "fr = fr0 \<and> roots = roots0 \<and> final = final0"
proof -
  have fr_eq: "fr = fr0"
    using eq by simp
  have roots_eq:
      "take n (tl ([fr] @ roots @ [final])) =
       take n (tl ([fr0] @ roots0 @ [final0]))"
    using eq by simp
  have roots_take: "take n (tl ([fr] @ roots @ [final])) = roots"
    using roots_len by simp
  have roots0_take:
      "take n (tl ([fr0] @ roots0 @ [final0])) = roots0"
    using roots0_len by simp
  have rr: "roots = roots0"
    using roots_eq roots_take roots0_take by simp
  have final_eq:
      "last ([fr] @ roots @ [final]) =
       last ([fr0] @ roots0 @ [final0])"
    using eq by simp
  show ?thesis
    using fr_eq rr final_eq by simp
qed


lemma ro_absorb_lookup_chain_alpha_challenge_update[simp]:
  "ro_absorb_lookup_chain
      (channel_for_hash_map (fmupd (AlphaChallenge c ast) y M))
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

lemma merkle_path_bound_alpha_challenge_update[simp]:
  "merkle_path_bound rt len idx v path
      (channel_for_hash_map (fmupd (AlphaChallenge c st) y M)) =
    merkle_path_bound rt len idx v path (channel_for_hash_map M)"
  unfolding channel_for_hash_map_def
  by (induction path arbitrary: rt len idx v) auto

lemma authenticated_opening_in_alpha_challenge_update[simp]:
  "authenticated_opening_in
      (channel_for_hash_map (fmupd (AlphaChallenge c st) y M)) opening =
    authenticated_opening_in (channel_for_hash_map M) opening"
  unfolding authenticated_opening_in_def by simp

lemma authenticated_value_at_alpha_challenge_update[simp]:
  "authenticated_value_at
      (channel_for_hash_map (fmupd (AlphaChallenge c st) y M))
      r len i v =
    authenticated_value_at (channel_for_hash_map M) r len i v"
  unfolding authenticated_value_at_def by simp

lemma conceptual_opening_value_alpha_challenge_update[simp]:
  "conceptual_opening_value
      (channel_for_hash_map (fmupd (AlphaChallenge c ast) y M))
      r len i =
    conceptual_opening_value (channel_for_hash_map M) r len i"
  unfolding conceptual_opening_value_def
  by (rule arg_cong[where f=The])
    (rule ext, simp)

lemma conceptual_table_alpha_challenge_update[simp]:
  fixes root :: 'f
    and len :: nat
  shows
    "conceptual_table
        (channel_for_hash_map (fmupd (AlphaChallenge c ast) y M))
        root len =
      conceptual_table (channel_for_hash_map M) root len"
  unfolding conceptual_table_def by simp

lemma ro_alpha_lookup_prefix_future_update:
  assumes future: "d = c + length as"
  shows
    "ro_alpha_lookup_prefix
        (fmupd (AlphaChallenge d target_state) y M)
        c st as final \<longleftrightarrow>
      ro_alpha_lookup_prefix M c st as final"
  using future
proof (induction as arbitrary: c st d)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have c_ne: "c \<noteq> d"
    using Cons.prems by simp
  have tail_index: "d = Suc c + length as"
    using Cons.prems by simp
  show ?case
    unfolding ro_alpha_lookup_prefix.simps
    using Cons.IH[OF tail_index] c_ne
    by simp
qed

lemma alpha_pivot_absorbed_query_relation_direct_fiber_card_bound:
  "card {y.
      hash_state_relation_direct_activation
        alpha_pivot_absorbed_query_relation M x y} \<le> 1"
proof (cases "{y.
    hash_state_relation_direct_activation
      alpha_pivot_absorbed_query_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
      "hash_state_relation_direct_activation
        alpha_pivot_absorbed_query_relation M x y0"
    by blast
  have rel0:
      "alpha_pivot_absorbed_query_relation (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from alpha_pivot_absorbed_query_relationD[OF rel0]
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
            (alpha_pivot_trace_table
              (fmupd x y0 M) fr0 trace_roots0))"
    and x0:
      "x = AlphaChallenge
        (PAlphaCounter adversary_initial_state + length alpha_prefix0)
        pivot_state0"
    and y0_mem:
      "y0 \<in> composition_trace_bad_alpha_pivot_values
        (alpha_pivot_trace_table (fmupd x y0 M) fr0 trace_roots0)
        alpha_prefix0"
    .
  let ?T0 =
    "alpha_pivot_trace_table (fmupd x y0 M) fr0 trace_roots0"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          alpha_pivot_absorbed_query_relation M x y}
        \<subseteq> composition_trace_bad_alpha_pivot_values ?T0 alpha_prefix0"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          alpha_pivot_absorbed_query_relation M x y}"
    have rely:
        "alpha_pivot_absorbed_query_relation (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from alpha_pivot_absorbed_query_relationD[OF rely]
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
              (alpha_pivot_trace_table
                (fmupd x y M) fr trace_roots))"
      and x_eq:
        "x = AlphaChallenge
          (PAlphaCounter adversary_initial_state + length alpha_prefix)
          pivot_state"
      and y_mem:
        "y \<in> composition_trace_bad_alpha_pivot_values
          (alpha_pivot_trace_table (fmupd x y M) fr trace_roots)
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
        "alpha_pivot_trace_table (fmupd x y M) fr trace_roots = ?T0"
      using fields_eq
      unfolding x0 alpha_pivot_trace_table_def
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
          alpha_pivot_absorbed_query_relation M x y}
        \<le> card
          (composition_trace_bad_alpha_pivot_values ?T0 alpha_prefix0)"
    by (rule card_mono[OF finite_target subset])
  show ?thesis
    by (rule order_trans[OF card_le])
      (rule composition_trace_bad_alpha_pivot_values_card_le_one)
qed
lemma ro_absorb_lookup_chain_alpha_final_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and chain:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        start messages final"
    and final_target: "final \<in> alpha_challenge_state_values M"
    and no_target: "y \<notin> alpha_pivot_relation_drift_targets M x"
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
      have "y \<in> alpha_pivot_relation_drift_targets M x"
        using final_target final_eq
        unfolding alpha_pivot_relation_drift_targets_def by blast
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
        then have "y \<in> alpha_pivot_relation_drift_targets M x"
          unfolding alpha_pivot_relation_drift_targets_def
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
        then have "y \<in> alpha_pivot_relation_drift_targets M x"
          unfolding alpha_pivot_relation_drift_targets_def
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

lemma ro_alpha_lookup_prefix_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and alpha_new:
      "ro_alpha_lookup_prefix (fmupd x y M) c st as final"
    and absorb_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M) st as final"
    and no_target: "y \<notin> alpha_pivot_relation_drift_targets M x"
  shows "ro_alpha_lookup_prefix M c st as final"
  using alpha_new absorb_old
proof (induction as arbitrary: c st)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  from Cons.prems(1) obtain nxt where
    challenge_new:
      "fmlookup (fmupd x y M) (AlphaChallenge c st) = Some a"
    and absorb_new:
      "fmlookup (fmupd x y M) (TranscriptAbsorb st a) = Some nxt"
    and alpha_tail_new:
      "ro_alpha_lookup_prefix (fmupd x y M)
        (Suc c) nxt as final"
    by auto
  from Cons.prems(2) obtain nxt_old where
    absorb_old_lookup:
      "fmlookup M (TranscriptAbsorb st a) = Some nxt_old"
    and absorb_tail_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        nxt_old as final"
    unfolding channel_for_hash_map_def by auto
  have absorb_key_neq: "TranscriptAbsorb st a \<noteq> x"
    using absorb_old_lookup fresh by auto
  have absorb_old_lookup_new:
      "fmlookup (fmupd x y M) (TranscriptAbsorb st a) = Some nxt_old"
    using absorb_old_lookup absorb_key_neq by simp
  have nxt_eq: "nxt = nxt_old"
    using absorb_new absorb_old_lookup_new by simp
  have challenge_key_neq: "AlphaChallenge c st \<noteq> x"
  proof
    assume key_eq: "AlphaChallenge c st = x"
    have a_eq: "a = y"
      using challenge_new key_eq by simp
    have message_target: "a \<in> transcript_absorb_message_values M"
      by (rule transcript_absorb_lookup_message_value[OF absorb_old_lookup])
    have "y \<in> alpha_pivot_relation_drift_targets M x"
      using message_target a_eq
      unfolding alpha_pivot_relation_drift_targets_def
        first_root_relation_drift_targets_def
      by blast
    then show False using no_target by contradiction
  qed
  have challenge_old: "fmlookup M (AlphaChallenge c st) = Some a"
    using challenge_new challenge_key_neq by simp
  have alpha_tail_old:
      "ro_alpha_lookup_prefix M (Suc c) nxt_old as final"
    by (rule Cons.IH)
      (use alpha_tail_new absorb_tail_old nxt_eq in simp_all)
  show ?case
    using challenge_old absorb_old_lookup alpha_tail_old by auto
qed

lemma alpha_challenge_lookup_state_value:
  assumes "fmlookup M (AlphaChallenge c st) = Some out"
  shows "st \<in> alpha_challenge_state_values M"
  using assms unfolding alpha_challenge_state_values_def by blast

lemma alpha_pivot_absorbed_query_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "alpha_pivot_absorbed_query_relation (fmupd x y M) k z"
    and no_target: "y \<notin> alpha_pivot_relation_drift_targets M x"
  shows "alpha_pivot_absorbed_query_relation M k z"
proof -
  from alpha_pivot_absorbed_query_relationD[OF rel]
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
            (alpha_pivot_trace_table (fmupd x y M) fr trace_roots))"
    and k_eq:
      "k = AlphaChallenge
        (PAlphaCounter adversary_initial_state + length alpha_prefix)
        pivot_state"
    and z_mem_new:
      "z \<in> composition_trace_bad_alpha_pivot_values
        (alpha_pivot_trace_table (fmupd x y M) fr trace_roots)
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
      "alpha_pivot_trace_table (fmupd x y M) fr trace_roots =
       alpha_pivot_trace_table M fr trace_roots"
    unfolding alpha_pivot_trace_table_def
    using conceptual_table_fresh_update[
      OF fresh selected_root_target no_selected_target]
    by simp
  have pivot_len_old:
      "length alpha_prefix =
        composition_alpha_pivot
          (low_degree_trace_witness
            (alpha_pivot_trace_table M fr trace_roots))"
    using pivot_len_new trace_table_eq by simp
  have z_mem_old:
      "z \<in> composition_trace_bad_alpha_pivot_values
        (alpha_pivot_trace_table M fr trace_roots)
        alpha_prefix"
    using z_mem_new trace_table_eq by simp
  show ?thesis
    unfolding alpha_pivot_absorbed_query_relation_def Let_def
    using clean_old no_initial_old trace_len
      header_chain_old alpha_chain_old pivot_len_old k_eq z_mem_old
    by blast
qed

lemma alpha_pivot_absorbed_query_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        alpha_pivot_absorbed_query_relation M x y"
  shows "y \<in> alpha_pivot_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> alpha_pivot_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        alpha_pivot_absorbed_query_relation (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        alpha_pivot_absorbed_query_relation M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "alpha_pivot_absorbed_query_relation (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def
    by blast+
  have rel_old:
      "alpha_pivot_absorbed_query_relation M k z"
    by (rule
      alpha_pivot_absorbed_query_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
      "hash_state_relation_active
        alpha_pivot_absorbed_query_relation M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed

lemma alpha_pivot_absorbed_query_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        alpha_pivot_absorbed_query_relation M x y}
      \<le> 6 * card (fmdom' M) + 2"
proof -
  have subset:
      "{y.
        hash_state_relation_drift_activation
          alpha_pivot_absorbed_query_relation M x y}
        \<subseteq> alpha_pivot_relation_drift_targets M x"
    using
      alpha_pivot_absorbed_query_relation_drift_activation_imp_target[
        OF fresh]
    by blast
  have
      "card {y.
        hash_state_relation_drift_activation
          alpha_pivot_absorbed_query_relation M x y}
        \<le> card (alpha_pivot_relation_drift_targets M x)"
    by (rule card_mono[
          OF finite_alpha_pivot_relation_drift_targets subset])
  also have "... \<le> 6 * card (fmdom' M) + 2"
    by (rule card_alpha_pivot_relation_drift_targets_le)
  finally show ?thesis .
qed

end
end
