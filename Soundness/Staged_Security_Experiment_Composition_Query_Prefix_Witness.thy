(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Prefix_Witness.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Prefix_Witness
  imports Staged_Security_Experiment_Composition_Query_Augmented
begin

text \<open>
  Witness-level bridge for the composition query-prefix path.

  The existing query-prefix bounds are fixed-witness bounds: the trace and
  composition openings must already be selected before the query challenge is
  sampled.  This layer records the exact local bridge from such fixed witness
  data to the augmented query-prefix component event.  The remaining public
  soundness work is to derive these fixed witnesses from prefix Merkle/candidate
  evidence, or charge failures to existing Merkle/collision side events.
\<close>

context soundness
begin

lemma partial_query_openings_consistent_canonical_trace_index:
  assumes consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        as idx"
  shows "trace_openings \<noteq> []"
    and "idx = opening_index (hd trace_openings)"
proof -
  have trace_indices:
    "map opening_index trace_openings = powers_scaled idx"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have powers_nonempty: "powers_scaled idx \<noteq> []"
    unfolding powers_scaled_def using powers_pos by simp
  then show trace_nonempty: "trace_openings \<noteq> []"
    using trace_indices by auto
  have "hd (map opening_index trace_openings) = hd (powers_scaled idx)"
    using trace_indices by simp
  then have "opening_index (hd trace_openings) = hd (powers_scaled idx)"
    using trace_nonempty by (simp add: hd_map)
  then show "idx = opening_index (hd trace_openings)"
    using powers_scaled_hd by simp
qed

lemma partial_query_success_indices_at_subset_canonical_trace_index:
  "partial_query_success_indices_at trace_openings composition_openings as i
    \<subseteq> {opening_index (hd (trace_openings ! i))}"
proof
  fix idx
  assume idx_in:
    "idx \<in> partial_query_success_indices_at trace_openings
      composition_openings as i"
  have trace_indices:
    "map opening_index (trace_openings ! i) = powers_scaled idx"
    using idx_in
    unfolding partial_query_success_indices_at_def
      partial_query_round_consistent_def
    by simp
  have trace_nonempty: "trace_openings ! i \<noteq> []"
  proof -
    have "powers_scaled idx \<noteq> []"
      unfolding powers_scaled_def using powers_pos by simp
    then show ?thesis
      using trace_indices by auto
  qed
  have "hd (map opening_index (trace_openings ! i)) = hd (powers_scaled idx)"
    using trace_indices by simp
  then have "opening_index (hd (trace_openings ! i)) = hd (powers_scaled idx)"
    using trace_nonempty by (simp add: hd_map)
  then show "idx \<in> {opening_index (hd (trace_openings ! i))}"
    using powers_scaled_hd by simp
qed

lemma staged_query_prefix_candidate_opening_query_target_from_prefix_subset_canonical_trace_index:
  "staged_query_prefix_candidate_opening_query_target_from_prefix
      trace_openings composition_openings i prefix prefix_state \<subseteq>
    {opening_index (hd (trace_openings ! i))}"
  unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
  by (rule partial_query_success_indices_at_subset_canonical_trace_index)

definition query_header_supported_partial_opening_canonical_indices
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat set"
where
  "query_header_supported_partial_opening_canonical_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final =
    {opening_index (hd trace_openings) |
      trace_openings composition_openings.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses s fr
            f_fri_roots f_final as dg composition_fri_roots final \<and>
        trace_openings \<noteq> []}"

definition query_header_supported_partial_opening_canonical_query_indices
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat set"
where
  "query_header_supported_partial_opening_canonical_query_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final =
    query_header_supported_partial_opening_canonical_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final \<inter>
    query_sample_space"

lemma query_header_supported_partial_opening_canonical_query_indices_subset:
  "query_header_supported_partial_opening_canonical_query_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final \<subseteq>
    query_sample_space"
  unfolding query_header_supported_partial_opening_canonical_query_indices_def
  by blast

lemma query_header_supported_partial_opening_canonical_query_indices_iff:
  "idx \<in> query_header_supported_partial_opening_canonical_query_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final \<longleftrightarrow>
    idx \<in> query_sample_space \<and>
    idx \<in> query_header_supported_partial_opening_canonical_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final"
  unfolding query_header_supported_partial_opening_canonical_query_indices_def
  by blast

lemma finite_query_header_supported_partial_opening_canonical_query_indices[simp]:
  "finite
    (query_header_supported_partial_opening_canonical_query_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final)"
  by (rule finite_subset
      [OF query_header_supported_partial_opening_canonical_query_indices_subset
        finite_query_sample_space])

lemma card_query_header_supported_partial_opening_canonical_query_indices_le:
  "card
    (query_header_supported_partial_opening_canonical_query_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final)
    \<le> card query_sample_space"
  by (rule card_mono)
    (rule finite_query_sample_space,
      rule query_header_supported_partial_opening_canonical_query_indices_subset)

lemma query_header_supported_partial_opening_canonical_query_indices_eq_query_sample_space_if_all_indices_witnessed:
  assumes witnessed:
      "\<And>idx. idx \<in> query_sample_space \<Longrightarrow>
        \<exists>trace_openings composition_openings.
          (trace_openings, composition_openings) \<in>
            query_header_supported_partial_opening_witnesses s fr
              f_fri_roots f_final as dg composition_fri_roots final \<and>
          trace_openings \<noteq> [] \<and>
          opening_index (hd trace_openings) = idx"
  shows
    "query_header_supported_partial_opening_canonical_query_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final =
    query_sample_space"
proof
  show
    "query_header_supported_partial_opening_canonical_query_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final \<subseteq>
    query_sample_space"
    by (rule query_header_supported_partial_opening_canonical_query_indices_subset)
next
  show
    "query_sample_space \<subseteq>
    query_header_supported_partial_opening_canonical_query_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final"
  proof
    fix idx
    assume idx_sample: "idx \<in> query_sample_space"
    then obtain trace_openings composition_openings where witness:
        "(trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses s fr
            f_fri_roots f_final as dg composition_fri_roots final"
      and nonempty: "trace_openings \<noteq> []"
      and idx_eq: "opening_index (hd trace_openings) = idx"
      using witnessed by blast
    have idx_canonical:
      "idx \<in>
        query_header_supported_partial_opening_canonical_indices s fr
          f_fri_roots f_final as dg composition_fri_roots final"
      unfolding query_header_supported_partial_opening_canonical_indices_def
      using witness nonempty idx_eq by blast
    show
      "idx \<in>
        query_header_supported_partial_opening_canonical_query_indices s fr
          f_fri_roots f_final as dg composition_fri_roots final"
      unfolding query_header_supported_partial_opening_canonical_query_indices_def
      using idx_sample idx_canonical by simp
  qed
qed

lemma table_agrees_with_authenticated_openings_from_partial_authenticated_table_if_no_partial_merkle_bad:
  assumes table:
      "partial_authenticated_table rt (scale * clength) openings final_state"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad s (Some (result, final_state))"
  shows "\<exists>table.
    table_agrees_with_authenticated_openings table (scale * clength)
      openings"
proof -
  have accepted_out: "accepted (Some (result, final_state))"
    unfolding accepted_def by simp
  have idx_bound:
    "\<And>opn. opn \<in> set openings \<Longrightarrow>
      opening_index opn < scale * clength"
  proof -
    fix opn
    assume opn_in: "opn \<in> set openings"
    have auth: "authenticated_opening_in final_state opn"
      using table opn_in unfolding partial_authenticated_table_def by blast
    have len: "opening_length opn = scale * clength"
      using table opn_in unfolding partial_authenticated_table_def by blast
    show "opening_index opn < scale * clength"
      using auth len unfolding authenticated_opening_in_def by simp
  qed
  have consistent:
    "\<And>opn opn'. opn \<in> set openings \<Longrightarrow>
      opn' \<in> set openings \<Longrightarrow>
      opening_index opn = opening_index opn' \<Longrightarrow>
      opening_value opn = opening_value opn'"
  proof (rule ccontr)
    fix opn opn'
    assume opn_in: "opn \<in> set openings"
      and opn'_in: "opn' \<in> set openings"
      and same_index: "opening_index opn = opening_index opn'"
      and neq: "opening_value opn \<noteq> opening_value opn'"
    have auth: "authenticated_opening_in final_state opn"
      using table opn_in unfolding partial_authenticated_table_def by blast
    have auth': "authenticated_opening_in final_state opn'"
      using table opn'_in unfolding partial_authenticated_table_def by blast
    have root: "opening_root opn = opening_root opn'"
      using table opn_in opn'_in unfolding partial_authenticated_table_def
      by auto
    have len: "opening_length opn = opening_length opn'"
      using table opn_in opn'_in unfolding partial_authenticated_table_def
      by auto
    have bad:
      "partial_merkle_inconsistency_bad s (Some (result, final_state))"
      unfolding partial_merkle_inconsistency_bad_def
      by (intro conjI exI[of _ result] exI[of _ final_state]
          exI[of _ opn] exI[of _ opn'])
        (use accepted_out auth auth' root len same_index neq in simp_all)
    then show False
      using no_bad by contradiction
  qed
  show ?thesis
    by (rule table_agrees_with_authenticated_openings_consistent_exists
        [OF idx_bound consistent])
qed

lemma partial_trace_table_candidate_single_witness_if_no_partial_merkle_bad:
  assumes auth:
      "partial_authenticated_table fr (scale * clength) trace_openings
        final_state"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad s (Some (result, final_state))"
    and i_bound: "i < rounds"
  shows "\<exists>trace_table.
    partial_trace_table_candidate trace_table
      ((replicate rounds []) [i := trace_openings])"
proof -
  obtain trace_table where agrees:
    "table_agrees_with_authenticated_openings trace_table (scale * clength)
      trace_openings"
    using
      table_agrees_with_authenticated_openings_from_partial_authenticated_table_if_no_partial_merkle_bad
        [OF auth outcome no_bad]
    by blast
  have len: "length trace_table = scale * clength"
    using agrees unfolding table_agrees_with_authenticated_openings_def
    by simp
  have candidate:
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [i := trace_openings])"
    by (rule partial_trace_table_candidate_single_roundI
        [OF i_bound len agrees])
  then show ?thesis by blast
qed

lemma partial_composition_table_candidate_single_witness_if_no_partial_merkle_bad:
  assumes auth:
      "partial_authenticated_table composition_root (scale * clength)
        composition_openings final_state"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad s (Some (result, final_state))"
    and i_bound: "i < rounds"
  shows "\<exists>composition_table.
    partial_composition_table_candidate composition_table
      ((replicate rounds []) [i := composition_openings])"
proof -
  obtain composition_table where agrees:
    "table_agrees_with_authenticated_openings composition_table
      (scale * clength) composition_openings"
    using
      table_agrees_with_authenticated_openings_from_partial_authenticated_table_if_no_partial_merkle_bad
        [OF auth outcome no_bad]
    by blast
  have len: "length composition_table = scale * clength"
    using agrees unfolding table_agrees_with_authenticated_openings_def
    by simp
  have candidate:
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [i := composition_openings])"
    by (rule partial_composition_table_candidate_single_roundI
        [OF i_bound len agrees])
  then show ?thesis by blast
qed

lemma query_header_supported_partial_opening_witness_single_round_candidates_or_partial_merkle_bad:
  assumes witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses s fr f_fri_roots
          f_final as dg composition_fri_roots final"
    and i_bound: "i < rounds"
  shows
    "(\<exists>result final_state.
      partial_merkle_inconsistency_bad s (Some (result, final_state))) \<or>
    (\<exists>trace_table composition_table.
      partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings]) \<and>
      partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings]))"
proof -
  from query_header_supported_partial_opening_witnessesE[OF witness]
  obtain result final_state rest where outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_auth:
      "partial_authenticated_table fr (scale * clength) trace_openings
        final_state"
    and comp_auth:
      "partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) composition_openings final_state"
    by blast
  show ?thesis
  proof (cases
      "partial_merkle_inconsistency_bad s (Some (result, final_state))")
    case True
    then show ?thesis by blast
  next
    case False
    obtain trace_table where trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
      using partial_trace_table_candidate_single_witness_if_no_partial_merkle_bad
          [OF trace_auth outcome False i_bound]
      by blast
    obtain composition_table where comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
      using
        partial_composition_table_candidate_single_witness_if_no_partial_merkle_bad
          [OF comp_auth outcome False i_bound]
      by blast
    show ?thesis
      using trace_candidate comp_candidate by blast
  qed
qed

lemma query_header_supported_partial_opening_witness_success_indices_fraction_bound_if_low_degree_candidates:
  assumes i_bound: "i < rounds"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "nnreal
      (card
        {idx \<in> query_sample_space.
          partial_query_openings_consistent trace_openings
            composition_openings as idx}) /
      nnreal (card query_sample_space) \<le> query_error_bound"
  by (rule
      partial_query_openings_consistent_indices_fraction_bound_if_candidate_low_degree
      [OF i_bound trace_candidate comp_candidate trace_low comp_low not_all])

lemma accepted_with_partial_trace_openings_update_round:
  assumes partial:
      "accepted_with_partial_trace_openings s (Some (result, final_state))
        fr query_idxs trace_openings"
    and i_bound: "i < rounds"
    and consistent:
      "partial_query_openings_consistent trace_openings_i
        composition_openings_i as (query_idxs ! i)"
    and auth:
      "partial_authenticated_table fr (scale * clength) trace_openings_i
        final_state"
  shows
    "accepted_with_partial_trace_openings s (Some (result, final_state))
      fr query_idxs (trace_openings[i := trace_openings_i])"
proof -
  have len_query: "length query_idxs = rounds"
    using accepted_with_partial_trace_openings_shapes(1)[OF partial] .
  have len_trace: "length trace_openings = rounds"
    using accepted_with_partial_trace_openings_shapes(2)[OF partial] .
  have trace_indices_i:
    "map opening_index trace_openings_i = powers_scaled (query_idxs ! i)"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have indices:
    "\<forall>j < rounds.
      map opening_index ((trace_openings[i := trace_openings_i]) ! j) =
        powers_scaled (query_idxs ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < rounds"
    show
      "map opening_index ((trace_openings[i := trace_openings_i]) ! j) =
        powers_scaled (query_idxs ! j)"
    proof (cases "j = i")
      case True
      then show ?thesis
        using i_bound len_trace trace_indices_i by simp
    next
      case False
      then show ?thesis
        using accepted_with_partial_trace_openings_shapes(3)[OF partial j_bound]
          len_trace j_bound
        by simp
    qed
  qed
  have tables:
    "\<forall>j < rounds.
      partial_authenticated_table fr (scale * clength)
        ((trace_openings[i := trace_openings_i]) ! j) final_state"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < rounds"
    show
      "partial_authenticated_table fr (scale * clength)
        ((trace_openings[i := trace_openings_i]) ! j) final_state"
    proof (cases "j = i")
      case True
      then show ?thesis
        using i_bound len_trace auth by simp
    next
      case False
      then show ?thesis
        using partial j_bound len_trace
        unfolding accepted_with_partial_trace_openings_def
        by simp
    qed
  qed
  show ?thesis
    unfolding accepted_with_partial_trace_openings_def accepted_def
    by (intro conjI exI[of _ result] exI[of _ final_state])
      (use len_query len_trace indices tables in simp_all)
qed

lemma accepted_with_partial_composition_openings_update_round:
  assumes partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) composition_root query_idxs
        composition_openings"
    and i_bound: "i < rounds"
    and consistent:
      "partial_query_openings_consistent trace_openings_i
        composition_openings_i as (query_idxs ! i)"
    and auth:
      "partial_authenticated_table composition_root (scale * clength)
        composition_openings_i final_state"
  shows
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) composition_root query_idxs
      (composition_openings[i := composition_openings_i])"
proof -
  have len_query: "length query_idxs = rounds"
    using accepted_with_partial_composition_openings_shapes(1)[OF partial] .
  have len_comp: "length composition_openings = rounds"
    using accepted_with_partial_composition_openings_shapes(2)[OF partial] .
  have comp_indices_i:
    "map opening_index composition_openings_i =
      [query_idxs ! i,
       fri_sibling_index (scale * clength) (query_idxs ! i)]"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have indices:
    "\<forall>j < rounds.
      map opening_index
        ((composition_openings[i := composition_openings_i]) ! j) =
        [query_idxs ! j,
         fri_sibling_index (scale * clength) (query_idxs ! j)]"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < rounds"
    show
      "map opening_index
        ((composition_openings[i := composition_openings_i]) ! j) =
        [query_idxs ! j,
         fri_sibling_index (scale * clength) (query_idxs ! j)]"
    proof (cases "j = i")
      case True
      then show ?thesis
        using i_bound len_comp comp_indices_i by simp
    next
      case False
      then show ?thesis
        using accepted_with_partial_composition_openings_shapes(3)
            [OF partial j_bound]
          len_comp j_bound
        by simp
    qed
  qed
  have tables:
    "\<forall>j < rounds.
      partial_authenticated_table composition_root (scale * clength)
        ((composition_openings[i := composition_openings_i]) ! j)
        final_state"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < rounds"
    show
      "partial_authenticated_table composition_root (scale * clength)
        ((composition_openings[i := composition_openings_i]) ! j)
        final_state"
    proof (cases "j = i")
      case True
      then show ?thesis
        using i_bound len_comp auth by simp
    next
      case False
      then show ?thesis
        using partial j_bound len_comp
        unfolding accepted_with_partial_composition_openings_def
        by simp
    qed
  qed
  show ?thesis
    unfolding accepted_with_partial_composition_openings_def accepted_def
    by (intro conjI exI[of _ result] exI[of _ final_state])
      (use len_query len_comp indices tables in simp_all)
qed

lemma accepted_with_partial_initial_openings_update_round:
  assumes partial:
      "accepted_with_partial_initial_openings s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and i_bound: "i < rounds"
    and same_idx: "trace_query_idxs ! i = composition_query_idxs ! i"
    and consistent:
      "partial_query_openings_consistent trace_openings_i
        composition_openings_i as (trace_query_idxs ! i)"
    and trace_auth:
      "partial_authenticated_table fr (scale * clength) trace_openings_i
        final_state"
    and comp_auth:
      "partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) composition_openings_i final_state"
  shows
    "accepted_with_partial_initial_openings s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs
      (trace_openings[i := trace_openings_i]) composition_query_idxs
      (composition_openings[i := composition_openings_i])"
proof -
  have comp_nonempty: "composition_fri_roots \<noteq> []"
    using accepted_with_partial_initial_openings_shapes(1)[OF partial] .
  have header:
    "\<exists>rest. verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    using accepted_with_partial_initial_openings_shapes(2)[OF partial] .
  have trace_partial:
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr trace_query_idxs trace_openings"
    using accepted_with_partial_initial_openings_shapes(3)[OF partial] .
  have comp_partial:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots)
      composition_query_idxs composition_openings"
    using accepted_with_partial_initial_openings_shapes(4)[OF partial] .
  have trace_updated:
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr trace_query_idxs
      (trace_openings[i := trace_openings_i])"
    by (rule accepted_with_partial_trace_openings_update_round
        [OF trace_partial i_bound consistent trace_auth])
  have comp_consistent:
    "partial_query_openings_consistent trace_openings_i
      composition_openings_i as (composition_query_idxs ! i)"
    using consistent same_idx by simp
  have comp_updated:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots)
      composition_query_idxs
      (composition_openings[i := composition_openings_i])"
    by (rule accepted_with_partial_composition_openings_update_round
        [OF comp_partial i_bound comp_consistent comp_auth])
  have accepted_out: "accepted (Some (result, final_state))"
    by (rule accepted_with_partial_trace_openings_imp_accepted
        [OF trace_updated])
  show ?thesis
    unfolding accepted_with_partial_initial_openings_def
    using accepted_out comp_nonempty header trace_updated comp_updated
    by simp
qed

lemma accepted_with_partial_initial_openings_update_round_candidates_if_no_partial_merkle_bad:
  assumes partial:
      "accepted_with_partial_initial_openings s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad s (Some (result, final_state))"
    and i_bound: "i < rounds"
    and same_idx: "trace_query_idxs ! i = composition_query_idxs ! i"
    and consistent:
      "partial_query_openings_consistent trace_openings_i
        composition_openings_i as (trace_query_idxs ! i)"
    and trace_auth:
      "partial_authenticated_table fr (scale * clength) trace_openings_i
        final_state"
    and comp_auth:
      "partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) composition_openings_i final_state"
  shows
    "\<exists>trace_table composition_table.
      partial_trace_table_candidate trace_table
        (trace_openings[i := trace_openings_i]) \<and>
      partial_composition_table_candidate composition_table
        (composition_openings[i := composition_openings_i])"
proof -
  have updated:
    "accepted_with_partial_initial_openings s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs
      (trace_openings[i := trace_openings_i]) composition_query_idxs
      (composition_openings[i := composition_openings_i])"
    by (rule accepted_with_partial_initial_openings_update_round
        [OF partial i_bound same_idx consistent trace_auth comp_auth])
  show ?thesis
    by (rule accepted_with_partial_initial_openings_candidates_if_no_partial_merkle_bad
        [OF updated no_bad])
qed

lemma query_header_supported_partial_opening_success_indices_at_subset_canonical_indices:
  "query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i \<subseteq>
    query_header_supported_partial_opening_canonical_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final"
proof
  fix idx
  assume idx_in:
    "idx \<in> query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i"
  then obtain trace_openings composition_openings where witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses s fr
          f_fri_roots f_final as dg composition_fri_roots final"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        as idx"
    by (rule query_header_supported_partial_opening_success_indices_atE)
  have nonempty: "trace_openings \<noteq> []"
    and idx_eq: "idx = opening_index (hd trace_openings)"
    by (rule partial_query_openings_consistent_canonical_trace_index
        [OF consistent])+
  show
    "idx \<in> query_header_supported_partial_opening_canonical_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_opening_canonical_indices_def
    using witness nonempty idx_eq by blast
qed

lemma query_header_supported_partial_opening_success_indices_at_subset_canonical_query_indices:
  "query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i \<subseteq>
    query_header_supported_partial_opening_canonical_query_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final"
proof
  fix idx
  assume idx_in:
    "idx \<in> query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i"
  have idx_canonical:
    "idx \<in> query_header_supported_partial_opening_canonical_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final"
    using idx_in
      query_header_supported_partial_opening_success_indices_at_subset_canonical_indices
    by blast
  have idx_sample: "idx \<in> query_sample_space"
    using idx_in query_header_supported_partial_opening_success_indices_at_subset
    by blast
  show
    "idx \<in> query_header_supported_partial_opening_canonical_query_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_opening_canonical_query_indices_def
    using idx_canonical idx_sample by simp
qed

lemma query_header_supported_partial_opening_success_indices_at_fraction_bound_if_canonical_query_indices:
  assumes canonical_bound:
      "nnreal
        (card
          (query_header_supported_partial_opening_canonical_query_indices
            s fr f_fri_roots f_final as dg composition_fri_roots final)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
  shows
    "nnreal
      (card
        (query_header_supported_partial_opening_success_indices_at s fr
          f_fri_roots f_final as dg composition_fri_roots final i)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof -
  have subset:
    "query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i \<subseteq>
    query_header_supported_partial_opening_canonical_query_indices s fr
      f_fri_roots f_final as dg composition_fri_roots final"
    by (rule
        query_header_supported_partial_opening_success_indices_at_subset_canonical_query_indices)
  have finite_canonical:
    "finite
      (query_header_supported_partial_opening_canonical_query_indices s fr
        f_fri_roots f_final as dg composition_fri_roots final)"
    by simp
  have card_le:
    "card
      (query_header_supported_partial_opening_success_indices_at s fr
        f_fri_roots f_final as dg composition_fri_roots final i) \<le>
    card
      (query_header_supported_partial_opening_canonical_query_indices s fr
        f_fri_roots f_final as dg composition_fri_roots final)"
    by (rule card_mono[OF finite_canonical subset])
  have
    "nnreal
      (card
        (query_header_supported_partial_opening_success_indices_at s fr
          f_fri_roots f_final as dg composition_fri_roots final i)) /
      nnreal (card query_sample_space) \<le>
    nnreal
      (card
        (query_header_supported_partial_opening_canonical_query_indices s fr
          f_fri_roots f_final as dg composition_fri_roots final)) /
      nnreal (card query_sample_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> query_error_bound"
    by (rule canonical_bound)
  finally show ?thesis .
qed

lemma query_header_supported_partial_opening_success_indices_at_subset_if_canonical_indices:
  assumes canonical_cover:
      "query_header_supported_partial_opening_canonical_indices s fr
        f_fri_roots f_final as dg composition_fri_roots final \<subseteq> B"
  shows
    "query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i \<subseteq> B"
  by (rule order_trans
      [OF
        query_header_supported_partial_opening_success_indices_at_subset_canonical_indices
        canonical_cover])

lemma query_header_supported_partial_opening_success_indices_at_subset_if_canonical_query_indices:
  assumes canonical_cover:
      "query_header_supported_partial_opening_canonical_query_indices s fr
        f_fri_roots f_final as dg composition_fri_roots final \<subseteq> B"
  shows
    "query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i \<subseteq> B"
  by (rule order_trans
      [OF
        query_header_supported_partial_opening_success_indices_at_subset_canonical_query_indices
        canonical_cover])

lemma staged_query_header_supported_partial_opening_success_indices_at_subset_if_canonical_indices:
  assumes canonical_cover:
      "query_header_supported_partial_opening_canonical_indices
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data) \<subseteq> B"
  shows
    "query_header_supported_partial_opening_success_indices_at
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      i \<subseteq> B"
  by (rule
      query_header_supported_partial_opening_success_indices_at_subset_if_canonical_indices
      [OF canonical_cover])

lemma staged_query_header_supported_partial_opening_success_indices_at_subset_if_canonical_query_indices:
  assumes canonical_cover:
      "query_header_supported_partial_opening_canonical_query_indices
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data) \<subseteq> B"
  shows
    "query_header_supported_partial_opening_success_indices_at
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      i \<subseteq> B"
  by (rule
      query_header_supported_partial_opening_success_indices_at_subset_if_canonical_query_indices
      [OF canonical_cover])

lemma checked_staged_security_with_data_state_partial_opening_hit_bound_from_canonical_query_error_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
      "\<And>data attacker_state.
        query_header_supported_partial_opening_canonical_query_indices
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<subseteq> B"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
  proof (rule
      checked_staged_security_with_data_state_partial_opening_hit_bound_from_fixed_query_error_cover
      [OF wf controlled _ raw_bound subset frac])
    fix data attacker_state i
    assume "i < rounds"
    show
      "query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<subseteq> B"
      by (rule
          staged_query_header_supported_partial_opening_success_indices_at_subset_if_canonical_query_indices
          [OF cover])
  qed
qed

lemma checked_staged_security_with_data_state_query_bad_bound_from_canonical_query_error_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
      "\<And>data attacker_state.
        query_header_supported_partial_opening_canonical_query_indices
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<subseteq> B"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
proof -
  have partial_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
    by (rule
        checked_staged_security_with_data_state_partial_opening_hit_bound_from_canonical_query_error_cover
        [OF wf controlled cover subset frac])
  show ?thesis
    by (rule order.trans
        [OF checked_staged_security_with_data_state_query_bad_bound_from_partial_opening_hit
          [OF wf controlled] partial_bound])
qed

lemma checked_staged_query_prefix_candidate_opening_target_from_prefix_canonical_indexD:
  assumes i_bound: "i < rounds"
    and hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i)
        (Some (((prefix, prefix_state), raw), raw_state))"
  shows "index (to_nat raw) = opening_index (hd trace_openings)"
proof -
  have idx_in:
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state"
    using hit unfolding checked_staged_query_prefix_dynamic_index_hit_def
    by simp
  have singleton:
    "staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state \<subseteq>
      {opening_index
        (hd (((replicate rounds []) [i := trace_openings]) ! i))}"
    by (rule
        staged_query_prefix_candidate_opening_query_target_from_prefix_subset_canonical_trace_index)
  have "index (to_nat raw) =
      opening_index
        (hd (((replicate rounds []) [i := trace_openings]) ! i))"
    using idx_in singleton by auto
  then show ?thesis
    using i_bound by simp
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_canonical_indexD:
  assumes i_bound: "i < rounds"
    and hit:
      "checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows "index (to_nat raw) = opening_index (hd trace_openings)"
proof -
  from checked_staged_security_with_query_prefix_fixed_header_componentE[OF hit]
  have target:
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state"
    by blast
  have singleton:
    "staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state \<subseteq>
      {opening_index
        (hd (((replicate rounds []) [i := trace_openings]) ! i))}"
    by (rule
        staged_query_prefix_candidate_opening_query_target_from_prefix_subset_canonical_trace_index)
  have "index (to_nat raw) =
      opening_index
        (hd (((replicate rounds []) [i := trace_openings]) ! i))"
    using target singleton by auto
  then show ?thesis
    using i_bound by simp
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_trace_openings_nonempty:
  assumes i_bound: "i < rounds"
    and hit:
      "checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows "trace_openings \<noteq> []"
proof -
  from checked_staged_security_with_query_prefix_fixed_header_componentE[OF hit]
  have target:
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state"
    by blast
  then have round:
    "partial_query_round_consistent
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      (sqp_alphas prefix) i (index (to_nat raw))"
    unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
      partial_query_success_indices_at_def
    by simp
  have trace_indices:
    "map opening_index
      (((replicate rounds []) [i := trace_openings]) ! i) =
      powers_scaled (index (to_nat raw))"
    using round unfolding partial_query_round_consistent_def by blast
  have "powers_scaled (index (to_nat raw)) \<noteq> []"
    unfolding powers_scaled_def using powers_pos by simp
  then have "((replicate rounds []) [i := trace_openings]) ! i \<noteq> []"
    using trace_indices by auto
  then show ?thesis
    using i_bound by simp
qed

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_canonical_query_indexD:
  assumes i_bound: "i < rounds"
    and hit:
      "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
        trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "index (to_nat raw) \<in>
      query_header_supported_partial_opening_canonical_query_indices
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
proof -
  from checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hitE
      [OF hit]
  have witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
    and target:
      "index (to_nat raw) \<in>
        staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i prefix prefix_state"
    by blast+
  have idx_sample: "index (to_nat raw) \<in> query_sample_space"
    using target staged_query_prefix_candidate_opening_query_target_from_prefix_subset
    by blast
  have round:
    "partial_query_round_consistent
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      (sqp_alphas prefix) i (index (to_nat raw))"
    using target
    unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
      partial_query_success_indices_at_def
    by simp
  have trace_indices:
    "map opening_index
      (((replicate rounds []) [i := trace_openings]) ! i) =
      powers_scaled (index (to_nat raw))"
    using round unfolding partial_query_round_consistent_def by blast
  have trace_nonempty: "trace_openings \<noteq> []"
  proof -
    have "powers_scaled (index (to_nat raw)) \<noteq> []"
      unfolding powers_scaled_def using powers_pos by simp
    then have "((replicate rounds []) [i := trace_openings]) ! i \<noteq> []"
      using trace_indices by auto
    then show ?thesis
      using i_bound by simp
  qed
  have singleton:
    "staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state \<subseteq>
      {opening_index
        (hd (((replicate rounds []) [i := trace_openings]) ! i))}"
    by (rule
        staged_query_prefix_candidate_opening_query_target_from_prefix_subset_canonical_trace_index)
  have idx_eq:
    "index (to_nat raw) = opening_index (hd trace_openings)"
    using target singleton i_bound by auto
  have idx_canonical:
    "index (to_nat raw) \<in>
      query_header_supported_partial_opening_canonical_indices
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    unfolding query_header_supported_partial_opening_canonical_indices_def
    using witness trace_nonempty idx_eq by blast
  show ?thesis
    unfolding query_header_supported_partial_opening_canonical_query_indices_def
    using idx_sample idx_canonical by simp
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_canonical_query_indexD:
  assumes i_bound: "i < rounds"
    and hit:
      "checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "index (to_nat raw) \<in>
      query_header_supported_partial_opening_canonical_query_indices
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
proof -
  have header:
    "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    using hit
    unfolding checked_staged_security_with_query_prefix_fixed_header_component_def
    by simp
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_canonical_query_indexD
        [OF i_bound header])
qed

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hitI_from_dynamic_hit:
  assumes witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
    and target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i)
        (Some (((prefix, prefix_state), raw), raw_state))"
  shows
    "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  from query_header_supported_partial_opening_witnessesE[OF witness]
  have comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    by blast
  have actual:
    "checked_staged_security_with_actual_query_prefix_candidate_opening_hit
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    using target_hit
    unfolding checked_staged_security_with_actual_query_prefix_candidate_opening_hit_def
      checked_staged_security_with_query_prefix_dynamic_index_hit_def
    by simp
  show ?thesis
    unfolding
      checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_def
    using comp_nonempty witness actual by simp
qed

lemma checked_staged_security_with_query_prefix_fixed_header_componentI_from_dynamic_hit:
  assumes event:
      "E (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    and witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
    and target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i)
        (Some (((prefix, prefix_state), raw), raw_state))"
  shows
    "checked_staged_security_with_query_prefix_fixed_header_component
      E trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
  unfolding checked_staged_security_with_query_prefix_fixed_header_component_def
  by (intro conjI event
      checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hitI_from_dynamic_hit
        [OF witness target_hit])

lemma checked_staged_security_with_query_prefix_fixed_header_component_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_bound
        [OF raw_bound wf controlled i_bound])
qed

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_bound
        [OF raw_bound wf controlled i_bound])
qed

lemma checked_staged_query_prefix_candidate_opening_target_from_prefix_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_query_prefix_candidate_opening_target_from_prefix_hit_bound
        [OF raw_bound wf controlled _ trace_candidate comp_candidate
          trace_low comp_low not_all])
      (use i_bound in simp)
qed

end

end
