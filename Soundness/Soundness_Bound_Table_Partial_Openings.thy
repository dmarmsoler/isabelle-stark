(*  Title:      Stark/Soundness_Bound_Table_Partial_Openings.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Bound_Table_Partial_Openings
  imports Soundness_Partial_Merkle
begin

text \<open>
  Bridges from complete Merkle-bound table witnesses to partial authenticated
  openings.  This proof layer is kept separate from
  \<^verbatim>\<open>Soundness_Partial_Merkle\<close>
  to avoid growing the base Merkle/event theory.
\<close>

context soundness
begin

definition partial_composition_openings_inconsistent_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "partial_composition_openings_inconsistent_bad s out \<longleftrightarrow>
    (\<exists>composition_root query_idxs composition_openings result final_state
        i opn opn'.
      out = Some (result, final_state) \<and>
      accepted_with_partial_composition_openings s out composition_root
        query_idxs composition_openings \<and>
      i < rounds \<and>
      opn \<in> set (composition_openings ! i) \<and>
      opn' \<in> set (composition_openings ! i) \<and>
      opening_index opn = opening_index opn' \<and>
      opening_value opn \<noteq> opening_value opn')"

lemma partial_composition_openings_inconsistent_bad_imp_partial_merkle_inconsistency_bad:
  assumes bad: "partial_composition_openings_inconsistent_bad s out"
  shows "partial_merkle_inconsistency_bad s out"
proof -
  obtain composition_root query_idxs composition_openings result final_state
      i opn opn' where
    out: "out = Some (result, final_state)"
    and partial:
      "accepted_with_partial_composition_openings s out composition_root
        query_idxs composition_openings"
    and i_bound: "i < rounds"
    and opn_in: "opn \<in> set (composition_openings ! i)"
    and opn'_in: "opn' \<in> set (composition_openings ! i)"
    and same_index: "opening_index opn = opening_index opn'"
    and diff_value: "opening_value opn \<noteq> opening_value opn'"
    using bad
    unfolding partial_composition_openings_inconsistent_bad_def by blast
  have table:
    "partial_authenticated_table composition_root (scale * clength)
      (composition_openings ! i) final_state"
  proof -
    obtain result' final_state' where
      partial_out: "out = Some (result', final_state')"
      and tables:
        "\<forall>i < rounds.
          partial_authenticated_table composition_root (scale * clength)
            (composition_openings ! i) final_state'"
      using partial
      unfolding accepted_with_partial_composition_openings_def by auto
    have final_state_eq: "final_state' = final_state"
      using out partial_out by simp
    show ?thesis
      using tables i_bound unfolding final_state_eq by simp
  qed
  have opn_auth: "authenticated_opening_in final_state opn"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have opn'_auth: "authenticated_opening_in final_state opn'"
    using table opn'_in unfolding partial_authenticated_table_def by blast
  have same_root: "opening_root opn = opening_root opn'"
  proof -
    have root_opn: "opening_root opn = composition_root"
      using table opn_in unfolding partial_authenticated_table_def by simp
    have root_opn': "opening_root opn' = composition_root"
      using table opn'_in unfolding partial_authenticated_table_def by simp
    show ?thesis
      using root_opn root_opn' by simp
  qed
  have same_length: "opening_length opn = opening_length opn'"
  proof -
    have length_opn: "opening_length opn = scale * clength"
      using table opn_in unfolding partial_authenticated_table_def by simp
    have length_opn': "opening_length opn' = scale * clength"
      using table opn'_in unfolding partial_authenticated_table_def by simp
    show ?thesis
      using length_opn length_opn' by simp
  qed
  have accepted_out: "accepted out"
    using partial
    unfolding accepted_with_partial_composition_openings_def by simp
  show ?thesis
    unfolding partial_merkle_inconsistency_bad_def
    using accepted_out out opn_auth opn'_auth same_root same_length
      same_index diff_value
    by blast
qed

lemma partial_composition_openings_inconsistent_bad_imp_hash_map_output_collision_bad:
  assumes "partial_composition_openings_inconsistent_bad s out"
  shows "hash_map_output_collision_bad s out"
  by (rule partial_merkle_inconsistency_bad_imp_hash_map_output_collision_bad)
    (rule
      partial_composition_openings_inconsistent_bad_imp_partial_merkle_inconsistency_bad
      [OF assms])

lemma partial_composition_openings_inconsistent_bad_mono_hash_map_output_collision_bad:
  "wp_event verify_monad (partial_composition_openings_inconsistent_bad s) s
    \<le> wp_event verify_monad (hash_map_output_collision_bad s) s"
  by (rule wp_event_mono)
    (rule partial_composition_openings_inconsistent_bad_imp_hash_map_output_collision_bad)

lemma partial_composition_openings_inconsistent_bad_bound_from_hash_map_output_collision:
  fixes H :: prob
  assumes "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad
      (partial_composition_openings_inconsistent_bad s) s \<le> H"
  by (rule order_trans
      [OF
        partial_composition_openings_inconsistent_bad_mono_hash_map_output_collision_bad
        assms])

lemma table_agrees_with_authenticated_openings_from_maps:
  assumes len_table: "length table = len"
    and indices: "map opening_index openings = idxs"
    and value_map: "map opening_value openings = map ((!) table) idxs"
    and idx_bound: "\<And>idx. idx \<in> set idxs \<Longrightarrow> idx < len"
  shows "table_agrees_with_authenticated_openings table len openings"
proof -
  have opening_props:
    "\<forall>opn \<in> set openings.
      opening_index opn < len \<and>
      table ! opening_index opn = opening_value opn"
  proof
    fix opn
    assume opn_in: "opn \<in> set openings"
    then obtain k where k_bound: "k < length openings"
      and opn_eq: "opn = openings ! k"
      by (metis in_set_conv_nth)
    have idxs_len: "length idxs = length openings"
      using arg_cong[OF indices, of length] by simp
    have idx_eq: "opening_index opn = idxs ! k"
      using indices k_bound idxs_len opn_eq
      by (metis length_map nth_map)
    have value_eq: "opening_value opn = table ! (idxs ! k)"
    proof -
      have "opening_value opn = map opening_value openings ! k"
        using k_bound opn_eq by simp
      also have "... = map ((!) table) idxs ! k"
        using value_map by simp
      also have "... = table ! (idxs ! k)"
        using k_bound idxs_len by simp
      finally show ?thesis .
    qed
    have idx_in: "idxs ! k \<in> set idxs"
      by (rule nth_mem) (use k_bound idxs_len in simp)
    show "opening_index opn < len \<and>
      table ! opening_index opn = opening_value opn"
      using idx_bound[OF idx_in] idx_eq value_eq by simp
  qed
  show ?thesis
    unfolding table_agrees_with_authenticated_openings_def
    using len_table opening_props by simp
qed

lemma accepted_with_bound_tables_partial_opening_witnesses:
  assumes bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
  obtains result final_state fr f_fri_roots f_final dg composition_fri_roots
      final rest trace_openings composition_openings where
    "out = Some (result, final_state)"
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    "composition_fri_roots \<noteq> []"
    "accepted_with_partial_trace_openings s out fr query_idxs
      trace_openings"
    "accepted_with_partial_composition_openings s out
      (hd composition_fri_roots) query_idxs composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "merkle_root_binds_table fr trace_table final_state"
    "merkle_root_binds_table (hd composition_fri_roots) composition_table
      final_state"
proof -
  from bound obtain result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest where out_eq:
      "out = Some (result, final_state)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and trace_bind:
      "merkle_root_binds_table fr trace_table final_state"
    and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots) composition_table
        final_state"
    unfolding accepted_with_bound_tables_def by blast
  have accepted_out: "accepted out"
    by (rule accepted_with_bound_tables_imp_accepted[OF bound])
  have trace_len_mult: "length trace_table = scale * clength"
    using accepted_with_bound_tables_shapes(1)[OF bound]
    by (simp add: mult.commute)
  have comp_len_mult: "length composition_table = scale * clength"
    using accepted_with_bound_tables_shapes(2)[OF bound]
    by (simp add: mult.commute)
  have query_len: "length query_idxs = rounds"
    by (rule accepted_with_bound_tables_shapes(4)[OF bound])
  have trace_exists:
    "\<And>i. i < rounds \<Longrightarrow>
      \<exists>openings.
        map opening_index openings = powers_scaled (query_idxs ! i) \<and>
        map opening_value openings =
          map ((!) trace_table) (powers_scaled (query_idxs ! i)) \<and>
        partial_authenticated_table fr (scale * clength) openings
          final_state"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have idx_in: "query_idxs ! i \<in> set query_idxs"
      by (rule nth_mem) (use i_bound query_len in simp)
    have idx_sample: "query_idxs ! i \<in> query_sample_space"
      by (rule accepted_with_bound_tables_query_sample_space[OF bound idx_in])
    have idxs_bound:
      "\<And>idx. idx \<in> set (powers_scaled (query_idxs ! i)) \<Longrightarrow>
        idx < scale * clength"
      using query_sample_space_powers_scaled_bound[OF idx_sample]
      by (simp add: mult.commute)
    show
      "\<exists>openings.
        map opening_index openings = powers_scaled (query_idxs ! i) \<and>
        map opening_value openings =
          map ((!) trace_table) (powers_scaled (query_idxs ! i)) \<and>
        partial_authenticated_table fr (scale * clength) openings
          final_state"
    proof (rule merkle_root_binds_table_authenticated_openings[
        OF trace_bind trace_len_mult idxs_bound])
      fix openings
      assume index_map:
          "map opening_index openings = powers_scaled (query_idxs ! i)"
        and value_map:
          "map opening_value openings =
            map ((!) trace_table) (powers_scaled (query_idxs ! i))"
        and partial:
          "partial_authenticated_table fr (scale * clength) openings
            final_state"
      show ?thesis
        by (intro exI[of _ openings] conjI index_map value_map partial)
    qed
  qed
  let ?trace_opening = "\<lambda>i. SOME openings.
    map opening_index openings = powers_scaled (query_idxs ! i) \<and>
    map opening_value openings =
      map ((!) trace_table) (powers_scaled (query_idxs ! i)) \<and>
    partial_authenticated_table fr (scale * clength) openings final_state"
  define trace_openings where
    "trace_openings = map ?trace_opening [0..<rounds]"
  have trace_openings_len: "length trace_openings = rounds"
    unfolding trace_openings_def by simp
  have trace_openings_props:
    "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i) \<and>
      map opening_value (trace_openings ! i) =
        map ((!) trace_table) (powers_scaled (query_idxs ! i)) \<and>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have some_prop:
      "map opening_index (?trace_opening i) = powers_scaled (query_idxs ! i) \<and>
       map opening_value (?trace_opening i) =
        map ((!) trace_table) (powers_scaled (query_idxs ! i)) \<and>
       partial_authenticated_table fr (scale * clength)
        (?trace_opening i) final_state"
      by (rule someI_ex[OF trace_exists[OF i_bound]])
    show
      "map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i) \<and>
      map opening_value (trace_openings ! i) =
        map ((!) trace_table) (powers_scaled (query_idxs ! i)) \<and>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
      using some_prop i_bound unfolding trace_openings_def by simp
  qed
  have comp_exists:
    "\<And>i. i < rounds \<Longrightarrow>
      \<exists>openings.
        map opening_index openings =
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
        map opening_value openings =
          map ((!) composition_table)
            [query_idxs ! i,
             fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
        partial_authenticated_table (hd composition_fri_roots)
          (scale * clength) openings final_state"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have idx_in: "query_idxs ! i \<in> set query_idxs"
      by (rule nth_mem) (use i_bound query_len in simp)
    have idx_bound: "query_idxs ! i < scale * clength"
      using accepted_with_bound_tables_shapes(5)[OF bound idx_in]
      by (simp add: mult.commute)
    have sibling_bound:
      "fri_sibling_index (scale * clength) (query_idxs ! i) <
        scale * clength"
      unfolding fri_sibling_index_def
      using eval_domain_size_pos by (simp add: mult.commute)
    have idxs_bound:
      "\<And>idx. idx \<in>
        set [query_idxs ! i,
          fri_sibling_index (scale * clength) (query_idxs ! i)] \<Longrightarrow>
        idx < scale * clength"
    proof -
      fix idx
      assume "idx \<in>
        set [query_idxs ! i,
          fri_sibling_index (scale * clength) (query_idxs ! i)]"
      then have "idx = query_idxs ! i \<or>
        idx = fri_sibling_index (scale * clength) (query_idxs ! i)"
        by simp
      then show "idx < scale * clength"
        using idx_bound sibling_bound by blast
    qed
    show
      "\<exists>openings.
        map opening_index openings =
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
        map opening_value openings =
          map ((!) composition_table)
            [query_idxs ! i,
             fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
        partial_authenticated_table (hd composition_fri_roots)
          (scale * clength) openings final_state"
    proof (rule merkle_root_binds_table_authenticated_openings[
        OF comp_bind comp_len_mult idxs_bound])
      fix openings
      assume index_map:
          "map opening_index openings =
            [query_idxs ! i,
             fri_sibling_index (scale * clength) (query_idxs ! i)]"
        and value_map:
          "map opening_value openings =
            map ((!) composition_table)
              [query_idxs ! i,
               fri_sibling_index (scale * clength) (query_idxs ! i)]"
        and partial:
          "partial_authenticated_table (hd composition_fri_roots)
            (scale * clength) openings final_state"
      show ?thesis
        by (intro exI[of _ openings] conjI index_map value_map partial)
    qed
  qed
  let ?composition_opening = "\<lambda>i. SOME openings.
    map opening_index openings =
      [query_idxs ! i,
       fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
    map opening_value openings =
      map ((!) composition_table)
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
    partial_authenticated_table (hd composition_fri_roots)
      (scale * clength) openings final_state"
  define composition_openings where
    "composition_openings = map ?composition_opening [0..<rounds]"
  have comp_openings_len: "length composition_openings = rounds"
    unfolding composition_openings_def by simp
  have comp_openings_props:
    "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (composition_openings ! i) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
      map opening_value (composition_openings ! i) =
        map ((!) composition_table)
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
      partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) (composition_openings ! i) final_state"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have some_prop:
      "map opening_index (?composition_opening i) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
       map opening_value (?composition_opening i) =
        map ((!) composition_table)
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
       partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) (?composition_opening i) final_state"
      by (rule someI_ex[OF comp_exists[OF i_bound]])
    show
      "map opening_index (composition_openings ! i) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
      map opening_value (composition_openings ! i) =
        map ((!) composition_table)
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
      partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) (composition_openings ! i) final_state"
      using some_prop i_bound unfolding composition_openings_def by simp
  qed
  have trace_partial:
    "accepted_with_partial_trace_openings s out fr query_idxs
      trace_openings"
  proof -
    have indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
      using trace_openings_props by simp
    have partials:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) final_state"
      using trace_openings_props by simp
    show ?thesis
      unfolding accepted_with_partial_trace_openings_def
      by (intro conjI exI[of _ result] exI[of _ final_state])
        (use accepted_out out_eq query_len trace_openings_len indices partials
          in simp_all)
  qed
  have comp_partial:
    "accepted_with_partial_composition_openings s out
      (hd composition_fri_roots) query_idxs composition_openings"
  proof -
    have indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (composition_openings ! i) =
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)]"
      using comp_openings_props by simp
    have partials:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table (hd composition_fri_roots)
          (scale * clength) (composition_openings ! i) final_state"
      using comp_openings_props by simp
    show ?thesis
      unfolding accepted_with_partial_composition_openings_def
      by (intro conjI exI[of _ result] exI[of _ final_state])
        (use accepted_out out_eq query_len comp_openings_len indices partials
          in simp_all)
  qed
  have trace_candidate:
    "partial_trace_table_candidate trace_table trace_openings"
  proof -
    have agrees:
      "\<And>i. i < rounds \<Longrightarrow>
        table_agrees_with_authenticated_openings trace_table
          (scale * clength) (trace_openings ! i)"
    proof -
      fix i
      assume i_bound: "i < rounds"
      have idx_in: "query_idxs ! i \<in> set query_idxs"
        by (rule nth_mem) (use i_bound query_len in simp)
      have idx_sample: "query_idxs ! i \<in> query_sample_space"
        by (rule accepted_with_bound_tables_query_sample_space[
            OF bound idx_in])
      have idxs_bound:
        "\<And>idx. idx \<in> set (powers_scaled (query_idxs ! i)) \<Longrightarrow>
          idx < scale * clength"
        using query_sample_space_powers_scaled_bound[OF idx_sample]
        by (simp add: mult.commute)
      show
        "table_agrees_with_authenticated_openings trace_table
          (scale * clength) (trace_openings ! i)"
      proof -
        have index_map:
          "map opening_index (trace_openings ! i) =
            powers_scaled (query_idxs ! i)"
          using trace_openings_props[OF i_bound] by blast
        have value_map:
          "map opening_value (trace_openings ! i) =
            map ((!) trace_table) (powers_scaled (query_idxs ! i))"
          using trace_openings_props[OF i_bound] by blast
        show ?thesis
          by (rule table_agrees_with_authenticated_openings_from_maps[
              OF trace_len_mult index_map value_map idxs_bound])
      qed
    qed
    show ?thesis
      unfolding partial_trace_table_candidate_def
      by (intro conjI allI impI)
        (use trace_len_mult trace_openings_len agrees in simp_all)
  qed
  have comp_candidate:
    "partial_composition_table_candidate composition_table
      composition_openings"
  proof -
    have agrees:
      "\<And>i. i < rounds \<Longrightarrow>
        table_agrees_with_authenticated_openings composition_table
          (scale * clength) (composition_openings ! i)"
    proof -
      fix i
      assume i_bound: "i < rounds"
      have idx_in: "query_idxs ! i \<in> set query_idxs"
        by (rule nth_mem) (use i_bound query_len in simp)
      have idx_bound: "query_idxs ! i < scale * clength"
        using accepted_with_bound_tables_shapes(5)[OF bound idx_in]
        by (simp add: mult.commute)
      have sibling_bound:
        "fri_sibling_index (scale * clength) (query_idxs ! i) <
          scale * clength"
        unfolding fri_sibling_index_def
        using eval_domain_size_pos by (simp add: mult.commute)
      have idxs_bound:
        "\<And>idx. idx \<in>
          set [query_idxs ! i,
            fri_sibling_index (scale * clength) (query_idxs ! i)] \<Longrightarrow>
          idx < scale * clength"
      proof -
        fix idx
        assume "idx \<in>
          set [query_idxs ! i,
            fri_sibling_index (scale * clength) (query_idxs ! i)]"
        then have "idx = query_idxs ! i \<or>
          idx = fri_sibling_index (scale * clength) (query_idxs ! i)"
          by simp
        then show "idx < scale * clength"
          using idx_bound sibling_bound by blast
      qed
      show
        "table_agrees_with_authenticated_openings composition_table
          (scale * clength) (composition_openings ! i)"
      proof -
        have index_map:
          "map opening_index (composition_openings ! i) =
            [query_idxs ! i,
             fri_sibling_index (scale * clength) (query_idxs ! i)]"
          using comp_openings_props[OF i_bound] by blast
        have value_map:
          "map opening_value (composition_openings ! i) =
            map ((!) composition_table)
              [query_idxs ! i,
               fri_sibling_index (scale * clength) (query_idxs ! i)]"
          using comp_openings_props[OF i_bound] by blast
        show ?thesis
          by (rule table_agrees_with_authenticated_openings_from_maps[
              OF comp_len_mult index_map value_map idxs_bound])
      qed
    qed
    show ?thesis
      unfolding partial_composition_table_candidate_def
      by (intro conjI allI impI)
        (use comp_len_mult comp_openings_len agrees in simp_all)
  qed
  show ?thesis
    by (rule that[OF out_eq header comp_nonempty trace_partial comp_partial
          trace_candidate comp_candidate trace_bind comp_bind])
qed

lemma accepted_with_bound_tables_partial_opening_witnesses_Some:
  assumes bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
  obtains fr f_fri_roots f_final dg composition_fri_roots final rest
      trace_openings composition_openings where
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    "composition_fri_roots \<noteq> []"
    "accepted_with_partial_trace_openings s (Some (result, final_state))
      fr query_idxs trace_openings"
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots) query_idxs
      composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "merkle_root_binds_table fr trace_table final_state"
    "merkle_root_binds_table (hd composition_fri_roots) composition_table
      final_state"
proof -
  show ?thesis
  proof (rule accepted_with_bound_tables_partial_opening_witnesses[OF bound])
    fix result' final_state' fr f_fri_roots f_final dg
        composition_fri_roots final rest trace_openings composition_openings
    assume out_eq:
      "Some (result, final_state) = Some (result', final_state')"
      and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
      and comp_nonempty: "composition_fri_roots \<noteq> []"
      and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
      and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots) query_idxs
        composition_openings"
      and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
      and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
      and trace_bind:
      "merkle_root_binds_table fr trace_table final_state'"
      and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots) composition_table
        final_state'"
    have final_state_eq: "final_state' = final_state"
      using out_eq by simp
    have trace_bind_outer:
      "merkle_root_binds_table fr trace_table final_state"
      using trace_bind final_state_eq by simp
    have comp_bind_outer:
      "merkle_root_binds_table (hd composition_fri_roots) composition_table
        final_state"
      using comp_bind final_state_eq by simp
    show ?thesis
      by (rule that[OF header comp_nonempty trace_partial comp_partial
          trace_candidate comp_candidate trace_bind_outer comp_bind_outer])
  qed
qed

end

end
