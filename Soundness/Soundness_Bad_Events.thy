(*  Title:      Stark/Soundness_Bad_Events.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Bad_Events
  imports
    Soundness_Execution
    Soundness_Query_Index_Modulo_Bounds
begin

context soundness
begin

text \<open>
  At this stage \<^term>\<open>accepted_with_tables\<close> is the boundary between the
  verifier execution and the algebraic proof.  It records the trace table,
  composition table, and verifier challenges associated with an accepted
  execution.  It now also records that the initial verifier transcript has the
  expected header shape and that the sampled query positions are locally
  consistent with the associated tables.  Merkle binding is separated into
  \<^term>\<open>accepted_with_bound_tables\<close>, because malicious binding requires
  additional Merkle/collision-resistance reasoning.
\<close>

definition composition_bad_context
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f poly \<Rightarrow> bool"
  where
    "composition_bad_context s out trace_table composition_table as query_idxs f \<longleftrightarrow>
      accepted_with_bound_tables s out trace_table composition_table as query_idxs \<and>
      degree f < clength \<and>
      trace_table = map (poly f) eval_domain \<and>
      violated_constraints f \<noteq> {} \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as"

definition composition_degree_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_degree_bad s out \<longleftrightarrow>
      (\<exists>trace_table composition_table as query_idxs f.
        composition_bad_context s out trace_table composition_table as query_idxs f \<and>
        \<not> common_denominator_degree_bounds f as)"

definition composition_randomization_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_randomization_bad s out \<longleftrightarrow>
      (\<exists>trace_table composition_table as query_idxs f.
        composition_bad_context s out trace_table composition_table as query_idxs f \<and>
        common_denominator_degree_bounds f as \<and>
        random_combination_common_denominator_hides_violations f as)"

definition composition_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_bad s out \<longleftrightarrow>
      composition_degree_bad s out \<or> composition_randomization_bad s out"

lemma composition_bad_has_common_denominator_witness:
  assumes "composition_bad s out"
  shows "\<exists>trace_table composition_table as query_idxs f.
    accepted_with_bound_tables s out trace_table composition_table as query_idxs \<and>
    degree f < clength \<and>
    trace_table = map (poly f) eval_domain \<and>
    violated_constraints f \<noteq> {} \<and>
    composition_table_low_degree maxDegree composition_table \<and>
    all_queries_consistent trace_table composition_table as \<and>
    (\<not> common_denominator_degree_bounds f as \<or>
      random_combination_common_denominator_hides_violations f as)"
  using assms
  unfolding composition_bad_def composition_degree_bad_def
    composition_randomization_bad_def composition_bad_context_def
  by blast

lemma composition_bad_imp_spec_nonempty:
  assumes "composition_bad s out"
  shows "spec \<noteq> []"
proof -
  obtain trace_table composition_table as query_idxs f
    where "violated_constraints f \<noteq> {}"
    using composition_bad_has_common_denominator_witness[OF assms] by blast
  then obtain entry where "entry \<in> violated_constraints f"
    by auto
  then have "entry \<in> set spec"
    unfolding violated_constraints_def by simp
  then show ?thesis
    by auto
qed

definition trace_fri_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_bad s out \<longleftrightarrow>
      (\<exists>trace_table composition_table as query_idxs.
        accepted_with_bound_tables s out trace_table composition_table as query_idxs \<and>
        \<not> trace_table_low_degree trace_table)"

definition composition_fri_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_fri_bad s out \<longleftrightarrow>
      (\<exists>trace_table composition_table as query_idxs.
        accepted_with_bound_tables s out trace_table composition_table as query_idxs \<and>
        trace_table_low_degree trace_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table)"

definition query_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_bad s out \<longleftrightarrow>
      (\<exists>trace_table composition_table as query_idxs.
        accepted_with_bound_tables s out trace_table composition_table as query_idxs \<and>
        trace_table_low_degree trace_table \<and>
        composition_table_low_degree maxDegree composition_table \<and>
        \<not> all_queries_consistent trace_table composition_table as)"

definition soundness_bad_event
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event s out \<longleftrightarrow>
      composition_bad s out \<or>
      trace_fri_bad s out \<or>
      composition_fri_bad s out \<or>
      query_bad s out"

definition query_sampling_success_space
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
  where
    "query_sampling_success_space trace_table composition_table as =
      (if trace_table_low_degree trace_table \<and>
          composition_table_low_degree maxDegree composition_table \<and>
          \<not> all_queries_consistent trace_table composition_table as
       then query_agreement_indices trace_table composition_table as
       else {})"

definition query_index_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_index_set_hit s good_sets out \<longleftrightarrow>
      (\<exists>trace_table composition_table as query_idxs.
        accepted_with_bound_tables s out trace_table composition_table as query_idxs \<and>
        set query_idxs \<subseteq> good_sets trace_table composition_table as)"

definition query_index_round_set_hit_at
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set) \<Rightarrow>
      nat \<Rightarrow> (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_index_round_set_hit_at s good_sets i out \<longleftrightarrow>
      (\<exists>trace_table composition_table as query_idxs.
        accepted_with_bound_tables s out trace_table composition_table as
          query_idxs \<and>
        i < rounds \<and>
        query_idxs ! i \<in> good_sets trace_table composition_table as)"

definition query_index_round_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_index_round_set_hit s good_sets out \<longleftrightarrow>
      (\<exists>i < rounds. query_index_round_set_hit_at s good_sets i out)"

definition query_round_index_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat set \<Rightarrow>
      (unit \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_round_index_set_hit s B out \<longleftrightarrow>
      (\<exists>raw t.
        out = Some ((), t) \<and>
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw \<and>
        index (to_nat raw) \<in> B)"

definition query_round_any_index_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat set \<Rightarrow>
      (unit \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_round_any_index_set_hit s B out \<longleftrightarrow>
      (\<exists>raw t x.
        out = Some ((), t) \<and>
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s) x) = Some raw \<and>
        index (to_nat raw) \<in> B)"

definition query_rounds_any_index_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_rounds_any_index_set_hit s B n out \<longleftrightarrow>
      (\<exists>results t i x raw.
        out = Some (results, t) \<and>
        i < n \<and>
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i) x) = Some raw \<and>
        index (to_nat raw) \<in> B)"

lemma accepted_with_bound_tables_query_rounds_any_index_set_hit:
  assumes bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and i_bound: "i < rounds"
    and hit: "query_idxs ! i \<in> B"
  shows "query_rounds_any_index_set_hit s B rounds out"
proof -
  have shape: "accepted_transcript_shape s out as query_idxs"
    using accepted_with_bound_tables_imp_accepted_with_tables[OF bound]
      accepted_with_tables_imp_accepted_transcript_shape by blast
  then obtain result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest raw_idxs query_chunks trailing where
    out_eq: "out = Some (result, final_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<forall>i < rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks
              (verifier_header_state s fr f_fri_roots f_final as dg
                composition_fri_roots final)
              query_chunks i)) =
          Some (raw_idxs ! i)"
    unfolding accepted_transcript_shape_def verifier_query_indices_derived_def
    by blast
  have raw_hit: "index (to_nat (raw_idxs ! i)) \<in> B"
    using hit query_idxs_eq len_raw i_bound by simp
  have lookup_i:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge (PQueryCounter s + i)
        (state_after_query_chunks
          (verifier_header_state s fr f_fri_roots f_final as dg
            composition_fri_roots final)
          query_chunks i)) =
      Some (raw_idxs ! i)"
    using lookup i_bound by simp
  show ?thesis
    unfolding query_rounds_any_index_set_hit_def
    apply (rule exI[where x=result])
    apply (rule exI[where x=final_state])
    apply (rule exI[where x=i])
    apply (rule exI[
      where x="state_after_query_chunks
        (verifier_header_state s fr f_fri_roots f_final as dg
          composition_fri_roots final)
        query_chunks i"])
    apply (rule exI[where x="raw_idxs ! i"])
    using out_eq i_bound lookup_i raw_hit by simp
qed

lemma query_index_round_set_hit_at_imp_query_rounds_any_index_set_hit:
  assumes hit: "query_index_round_set_hit_at s good_sets i out"
  shows
    "\<exists>trace_table composition_table as.
      query_rounds_any_index_set_hit s
        (good_sets trace_table composition_table as) rounds out"
proof -
  from hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and i_bound: "i < rounds"
    and query_hit:
      "query_idxs ! i \<in> good_sets trace_table composition_table as"
    unfolding query_index_round_set_hit_at_def by blast
  have round_hit:
    "query_rounds_any_index_set_hit s
      (good_sets trace_table composition_table as) rounds out"
    by (rule accepted_with_bound_tables_query_rounds_any_index_set_hit
        [OF bound i_bound query_hit])
  show ?thesis
    using round_hit by blast
qed

definition query_header_supported_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> ('f list \<times> 'f list) set"
  where
    "query_header_supported_table_candidates s fr f_fri_roots f_final as dg
      composition_fri_roots final =
      {(trace_table, composition_table).
        \<exists>out query_idxs rest.
          out \<in> set_dist (execute verify_monad s) \<and>
          accepted_with_bound_tables s out trace_table composition_table as
            query_idxs \<and>
          verifier_header_transcript s fr f_fri_roots f_final as dg
            composition_fri_roots final rest}"

definition query_header_supported_table_candidate_state
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "query_header_supported_table_candidate_state s fr f_fri_roots f_final
      as dg composition_fri_roots final trace_table composition_table
      final_state \<longleftrightarrow>
      (\<exists>result query_idxs rest.
        Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
        accepted_with_bound_tables s (Some (result, final_state))
          trace_table composition_table as query_idxs \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest \<and>
        merkle_root_binds_table fr trace_table final_state \<and>
        composition_fri_roots \<noteq> [] \<and>
        merkle_root_binds_table (hd composition_fri_roots) composition_table
          final_state)"

lemma query_header_supported_table_candidates_iff_state:
  "(trace_table, composition_table) \<in>
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final \<longleftrightarrow>
    (\<exists>final_state.
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state)"
proof
  assume candidate:
    "(trace_table, composition_table) \<in>
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final"
  then obtain out query_idxs rest where
    outcome: "out \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding query_header_supported_table_candidates_def by blast
  from bound obtain result final_state fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    out_eq: "out = Some (result, final_state)"
    and header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and trace_bind:
      "merkle_root_binds_table fr' trace_table final_state"
    and comp_nonempty: "composition_fri_roots' \<noteq> []"
    and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots')
        composition_table final_state"
    unfolding accepted_with_bound_tables_def by blast
  have eqs:
    "fr' = fr \<and>
     f_fri_roots' = f_fri_roots \<and>
     f_final' = f_final \<and>
     dg' = dg \<and>
     composition_fri_roots' = composition_fri_roots \<and>
     final' = final \<and>
     rest' = rest"
    using verifier_header_transcript_unique[OF header' header] by simp
  have state:
    "query_header_supported_table_candidate_state s fr f_fri_roots f_final
      as dg composition_fri_roots final trace_table composition_table
      final_state"
    unfolding query_header_supported_table_candidate_state_def
    by (intro exI[of _ result] exI[of _ query_idxs] exI[of _ rest])
      (use outcome out_eq bound header trace_bind comp_nonempty comp_bind eqs
        in simp)
  then show
    "\<exists>final_state.
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
    by blast
next
  assume
    "\<exists>final_state.
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
  then obtain final_state result query_idxs rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding query_header_supported_table_candidate_state_def by blast
  show "(trace_table, composition_table) \<in>
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final"
    unfolding query_header_supported_table_candidates_def
    using outcome bound header by blast
qed

lemma query_header_supported_table_candidate_state_hash_extends:
  assumes
    "query_header_supported_table_candidate_state s fr f_fri_roots f_final
      as dg composition_fri_roots final trace_table composition_table
      final_state"
  shows "s \<le> final_state"
proof -
  from assms obtain result query_idxs rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    unfolding query_header_supported_table_candidate_state_def by blast
  show ?thesis
    by (rule verify_monad_hash_extends[OF outcome])
qed

lemma query_header_supported_table_candidate_states_merkle_compatible_unique_if_clean_merge:
  assumes compatible:
      "merkle_hash_maps_compatible final_state final_state'"
    and clean:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    and candidate:
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
    and candidate':
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state'"
  shows
    "trace_table = trace_table' \<and>
     composition_table = composition_table'"
proof -
  from candidate obtain result query_idxs rest where
    bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and trace_bind:
      "merkle_root_binds_table fr trace_table final_state"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots) composition_table
        final_state"
    unfolding query_header_supported_table_candidate_state_def by blast
  from candidate' obtain result' query_idxs' rest' where
    bound':
      "accepted_with_bound_tables s (Some (result', final_state'))
        trace_table' composition_table' as query_idxs'"
    and trace_bind':
      "merkle_root_binds_table fr trace_table' final_state'"
    and comp_bind':
      "merkle_root_binds_table (hd composition_fri_roots) composition_table'
        final_state'"
    unfolding query_header_supported_table_candidate_state_def by blast
  have same_trace_len: "length trace_table = length trace_table'"
    using accepted_with_bound_tables_shapes(1)[OF bound]
      accepted_with_bound_tables_shapes(1)[OF bound']
    by simp
  have trace_nonempty: "trace_table \<noteq> []"
    using accepted_with_bound_tables_shapes(1)[OF bound]
      eval_domain_nontrivial by auto
  have trace_eq: "trace_table = trace_table'"
    by (rule
        merkle_root_binds_same_length_tables_merkle_compatible_unique_if_clean_merge
        [OF compatible clean trace_bind trace_bind' same_trace_len
          trace_nonempty])
  have same_comp_len: "length composition_table = length composition_table'"
    using accepted_with_bound_tables_shapes(2)[OF bound]
      accepted_with_bound_tables_shapes(2)[OF bound']
    by simp
  have comp_nonempty': "composition_table \<noteq> []"
    using accepted_with_bound_tables_shapes(2)[OF bound]
      eval_domain_nontrivial by auto
  have comp_eq: "composition_table = composition_table'"
    by (rule
        merkle_root_binds_same_length_tables_merkle_compatible_unique_if_clean_merge
        [OF compatible clean comp_bind comp_bind' same_comp_len
          comp_nonempty'])
  show ?thesis
    using trace_eq comp_eq by simp
qed

lemma query_header_supported_table_candidates_subset_singleton_if_pairwise_merkle_clean_merge:
  assumes pairwise:
      "\<And>trace_table composition_table final_state trace_table'
          composition_table' final_state'.
        query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table composition_table
          final_state \<Longrightarrow>
        query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table' composition_table'
          final_state' \<Longrightarrow>
        merkle_hash_maps_compatible final_state final_state' \<and>
        \<not> hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table composition_table.
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final \<subseteq>
        {(trace_table, composition_table)}"
proof (cases
    "query_header_supported_table_candidates s fr f_fri_roots f_final as dg
      composition_fri_roots final = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"] exI[of _ "[]"]) simp
next
  case False
  then obtain table_pair0 where table_pair0:
    "table_pair0 \<in>
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final"
    by blast
  obtain trace_table0 composition_table0 where table_pair0_eq:
    "table_pair0 = (trace_table0, composition_table0)"
    by (cases table_pair0)
  have table0:
    "(trace_table0, composition_table0) \<in>
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final"
    using table_pair0 unfolding table_pair0_eq .
  then obtain final_state0 where state0:
    "query_header_supported_table_candidate_state s fr f_fri_roots f_final
      as dg composition_fri_roots final trace_table0 composition_table0
      final_state0"
    using query_header_supported_table_candidates_iff_state by blast
  have subset:
    "query_header_supported_table_candidates s fr f_fri_roots f_final as dg
      composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)}"
  proof
    fix table_pair
    assume pair_in:
      "table_pair \<in>
        query_header_supported_table_candidates s fr f_fri_roots f_final as
          dg composition_fri_roots final"
    obtain trace_table composition_table where pair_eq:
      "table_pair = (trace_table, composition_table)"
      by (cases table_pair)
    from pair_in obtain final_state where state:
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
      unfolding pair_eq
      using query_header_supported_table_candidates_iff_state by blast
    have compatible:
      "merkle_hash_maps_compatible final_state final_state0"
      using pairwise[OF state state0] by simp
    have clean:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state0)"
      using pairwise[OF state state0] by simp
    have eqs:
      "trace_table = trace_table0 \<and>
       composition_table = composition_table0"
      by (rule
          query_header_supported_table_candidate_states_merkle_compatible_unique_if_clean_merge
          [OF compatible clean state state0])
    show "table_pair \<in> {(trace_table0, composition_table0)}"
      using pair_eq eqs by simp
  qed
  then show ?thesis
    by blast
qed

lemma query_header_supported_table_candidates_subset_singleton_if_pairwise_no_merkle_value_conflict_clean_merge:
  assumes pairwise:
      "\<And>trace_table composition_table final_state trace_table'
          composition_table' final_state'.
        query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table composition_table
          final_state \<Longrightarrow>
        query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table' composition_table'
          final_state' \<Longrightarrow>
        \<not> merkle_hash_value_conflict final_state final_state' \<and>
        \<not> hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table composition_table.
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final \<subseteq>
        {(trace_table, composition_table)}"
proof (rule
    query_header_supported_table_candidates_subset_singleton_if_pairwise_merkle_clean_merge)
  fix trace_table composition_table final_state trace_table'
      composition_table' final_state'
  assume candidate:
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
    and candidate':
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state'"
  have no_conflict:
    "\<not> merkle_hash_value_conflict final_state final_state'"
    using pairwise[OF candidate candidate'] by simp
  have compatible:
    "merkle_hash_maps_compatible final_state final_state'"
    using no_conflict
    unfolding merkle_hash_maps_compatible_iff_no_value_conflict .
  have clean:
    "\<not> hash_map_output_collision
      (merkle_hash_state_merge final_state final_state')"
    using pairwise[OF candidate candidate'] by simp
  show "merkle_hash_maps_compatible final_state final_state' \<and>
      \<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    using compatible clean by simp
qed

lemma query_header_supported_table_candidates_subset_singleton_if_common_clean_merkle_extension:
  assumes clean: "\<not> hash_map_output_collision u"
    and common_ext:
      "\<And>trace_table composition_table final_state.
        query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table composition_table
          final_state \<Longrightarrow>
        merkle_hash_extends final_state u"
  shows
    "\<exists>trace_table composition_table.
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final \<subseteq>
        {(trace_table, composition_table)}"
proof (rule
    query_header_supported_table_candidates_subset_singleton_if_pairwise_no_merkle_value_conflict_clean_merge)
  fix trace_table composition_table final_state trace_table'
      composition_table' final_state'
  assume candidate:
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
    and candidate':
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state'"
  have ext: "merkle_hash_extends final_state u"
    by (rule common_ext[OF candidate])
  have ext': "merkle_hash_extends final_state' u"
    by (rule common_ext[OF candidate'])
  show "\<not> merkle_hash_value_conflict final_state final_state' \<and>
      \<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    by (rule common_clean_merkle_extension_imp_pairwise_merkle_clean
        [OF ext ext' clean])
qed

lemma query_header_supported_table_candidate_states_distinct_imp_merkle_conflict_or_merge_collision:
  assumes candidate:
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
    and candidate':
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state'"
    and distinct_tables:
      "trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table'"
  shows
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
proof (rule ccontr)
  assume no_bad:
    "\<not> (merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state'))"
  have compatible:
    "merkle_hash_maps_compatible final_state final_state'"
    using no_bad unfolding merkle_hash_maps_compatible_iff_no_value_conflict
    by simp
  have clean:
    "\<not> hash_map_output_collision
      (merkle_hash_state_merge final_state final_state')"
    using no_bad by simp
  have eqs:
    "trace_table = trace_table' \<and>
     composition_table = composition_table'"
    by (rule
        query_header_supported_table_candidate_states_merkle_compatible_unique_if_clean_merge
        [OF compatible clean candidate candidate'])
  then show False
    using distinct_tables by simp
qed

definition query_header_supported_pairwise_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "query_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final as
      dg composition_fri_roots final \<longleftrightarrow>
      (\<exists>trace_table composition_table final_state trace_table'
          composition_table' final_state'.
        query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table composition_table
          final_state \<and>
        query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table' composition_table'
          final_state' \<and>
        (trace_table \<noteq> trace_table' \<or>
         composition_table \<noteq> composition_table') \<and>
        (merkle_hash_value_conflict final_state final_state' \<or>
          hash_map_output_collision
            (merkle_hash_state_merge final_state final_state')))"

definition query_supported_pairwise_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "query_supported_pairwise_merkle_bad s \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final.
        query_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final
          as dg composition_fri_roots final)"

lemma query_header_supported_table_candidates_not_singleton_imp_pairwise_merkle_bad:
  assumes not_unique:
      "\<not> (\<exists>trace_table composition_table.
        query_header_supported_table_candidates s fr f_fri_roots f_final as dg
          composition_fri_roots final \<subseteq>
          {(trace_table, composition_table)})"
  shows
    "\<exists>trace_table composition_table final_state trace_table'
        composition_table' final_state'.
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state \<and>
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state' \<and>
      (trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table') \<and>
      (merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state'))"
proof -
  let ?C =
    "query_header_supported_table_candidates s fr f_fri_roots f_final as dg
      composition_fri_roots final"
  have nonempty: "?C \<noteq> {}"
    using not_unique by auto
  then obtain table_pair where table_pair:
    "table_pair \<in> ?C"
    by blast
  obtain trace_table composition_table where table_pair_eq:
    "table_pair = (trace_table, composition_table)"
    by (cases table_pair)
  have table:
    "(trace_table, composition_table) \<in> ?C"
    using table_pair unfolding table_pair_eq .
  have "\<not> ?C \<subseteq> {(trace_table, composition_table)}"
    using not_unique by blast
  then obtain table_pair' where table_pair':
      "table_pair' \<in> ?C"
    and table_pair'_not:
      "table_pair' \<notin> {(trace_table, composition_table)}"
    by auto
  obtain trace_table' composition_table' where table_pair'_eq:
    "table_pair' = (trace_table', composition_table')"
    by (cases table_pair')
  have table':
    "(trace_table', composition_table') \<in> ?C"
    using table_pair' unfolding table_pair'_eq .
  have distinct_tables:
    "trace_table \<noteq> trace_table' \<or>
     composition_table \<noteq> composition_table'"
    using table_pair'_not unfolding table_pair'_eq by auto
  from table obtain final_state where candidate:
    "query_header_supported_table_candidate_state s fr f_fri_roots f_final
      as dg composition_fri_roots final trace_table composition_table
      final_state"
    using query_header_supported_table_candidates_iff_state by blast
  from table' obtain final_state' where candidate':
    "query_header_supported_table_candidate_state s fr f_fri_roots f_final
      as dg composition_fri_roots final trace_table' composition_table'
      final_state'"
    using query_header_supported_table_candidates_iff_state by blast
  have bad:
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    by (rule
        query_header_supported_table_candidate_states_distinct_imp_merkle_conflict_or_merge_collision
        [OF candidate candidate' distinct_tables])
  show ?thesis
    using candidate candidate' distinct_tables bad by blast
qed

lemma query_header_supported_pairwise_merkle_bad_extends_initial:
  assumes bad:
    "query_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final as
      dg composition_fri_roots final"
  obtains trace_table composition_table final_state trace_table'
      composition_table' final_state'
  where
    "query_header_supported_table_candidate_state s fr f_fri_roots f_final
      as dg composition_fri_roots final trace_table composition_table
      final_state"
    "query_header_supported_table_candidate_state s fr f_fri_roots f_final
      as dg composition_fri_roots final trace_table' composition_table'
      final_state'"
    "trace_table \<noteq> trace_table' \<or>
     composition_table \<noteq> composition_table'"
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    "s \<le> final_state"
    "s \<le> final_state'"
proof -
  from bad obtain trace_table composition_table final_state trace_table'
      composition_table' final_state' where
    candidate:
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
    and candidate':
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state'"
    and distinct:
      "trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table'"
    and pair_bad:
      "merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
    unfolding query_header_supported_pairwise_merkle_bad_def by blast
  have ext: "s \<le> final_state"
    by (rule query_header_supported_table_candidate_state_hash_extends
        [OF candidate])
  have ext': "s \<le> final_state'"
    by (rule query_header_supported_table_candidate_state_hash_extends
        [OF candidate'])
  show ?thesis
    by (rule that[OF candidate candidate' distinct pair_bad ext ext'])
qed

definition query_header_supported_pairwise_coupling_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "query_header_supported_pairwise_coupling_bad s fr f_fri_roots f_final as
      dg composition_fri_roots final \<longleftrightarrow>
      (\<exists>trace_table composition_table final_state trace_table'
          composition_table' final_state'.
        query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table composition_table
          final_state \<and>
        query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table' composition_table'
          final_state' \<and>
        (trace_table \<noteq> trace_table' \<or>
         composition_table \<noteq> composition_table') \<and>
        merkle_hash_pairwise_coupling_bad final_state final_state')"

definition query_supported_pairwise_coupling_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "query_supported_pairwise_coupling_bad s \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final.
        query_header_supported_pairwise_coupling_bad s fr f_fri_roots f_final
          as dg composition_fri_roots final)"

lemma query_header_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad:
  assumes bad:
    "query_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final as
      dg composition_fri_roots final"
  shows
    "(\<exists>trace_table composition_table final_state trace_table'
        composition_table' final_state'.
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state \<and>
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state' \<and>
      (trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table') \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     query_header_supported_pairwise_coupling_bad s fr f_fri_roots f_final as
      dg composition_fri_roots final"
proof -
  from bad obtain trace_table composition_table final_state trace_table'
      composition_table' final_state'
    where candidate:
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
    and candidate':
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state'"
    and distinct:
      "trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table'"
    and pair_bad:
      "merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
    unfolding query_header_supported_pairwise_merkle_bad_def by blast
  have decomp:
    "hash_map_output_collision final_state \<or>
     hash_map_output_collision final_state' \<or>
     merkle_hash_pairwise_coupling_bad final_state final_state'"
    by (rule merkle_hash_pairwise_bad_imp_local_collision_or_coupling_bad
        [OF pair_bad])
  show ?thesis
    using candidate candidate' distinct decomp
    unfolding query_header_supported_pairwise_coupling_bad_def by blast
qed

lemma query_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad:
  assumes bad: "query_supported_pairwise_merkle_bad s"
  shows
    "(\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
        trace_table composition_table final_state trace_table'
        composition_table' final_state'.
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state \<and>
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state' \<and>
      (trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table') \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     query_supported_pairwise_coupling_bad s"
proof -
  from bad obtain fr f_fri_roots f_final as dg composition_fri_roots final
    where header_bad:
      "query_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final
        as dg composition_fri_roots final"
    unfolding query_supported_pairwise_merkle_bad_def by blast
  from
    query_header_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad
      [OF header_bad]
  show ?thesis
    unfolding query_supported_pairwise_coupling_bad_def by blast
qed

lemma query_supported_pairwise_merkle_bad_imp_supported_hash_collision_possible_or_coupling_bad:
  assumes bad: "query_supported_pairwise_merkle_bad s"
  shows
    "supported_hash_output_collision_possible s \<or>
     query_supported_pairwise_coupling_bad s"
proof -
  have decomp:
    "(\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
        trace_table composition_table final_state trace_table'
        composition_table' final_state'.
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state \<and>
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state' \<and>
      (trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table') \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     query_supported_pairwise_coupling_bad s"
    by (rule query_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad
        [OF bad])
  then show ?thesis
  proof
    assume local:
      "\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
        trace_table composition_table final_state trace_table'
        composition_table' final_state'.
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state \<and>
      query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state' \<and>
      (trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table') \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')"
    then obtain fr f_fri_roots f_final as dg composition_fri_roots final
        trace_table composition_table final_state trace_table'
        composition_table' final_state' where
      candidate:
        "query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table composition_table
          final_state"
      and candidate':
        "query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table' composition_table'
          final_state'"
      and collision:
        "hash_map_output_collision final_state \<or>
         hash_map_output_collision final_state'"
      by blast
    from collision show ?thesis
    proof
      assume collision_final: "hash_map_output_collision final_state"
      from candidate obtain result query_idxs rest where
        outcome:
          "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
        and bound:
          "accepted_with_bound_tables s (Some (result, final_state))
            trace_table composition_table as query_idxs"
        unfolding query_header_supported_table_candidate_state_def by blast
      have "supported_hash_output_collision_possible s"
        by (rule
            accepted_with_bound_tables_hash_collision_imp_supported_hash_output_collision_possible
            [OF outcome bound collision_final])
      then show ?thesis by simp
    next
      assume collision_final': "hash_map_output_collision final_state'"
      from candidate' obtain result' query_idxs' rest' where
        outcome':
          "Some (result', final_state') \<in> set_dist (execute verify_monad s)"
        and bound':
          "accepted_with_bound_tables s (Some (result', final_state'))
            trace_table' composition_table' as query_idxs'"
        unfolding query_header_supported_table_candidate_state_def by blast
      have "supported_hash_output_collision_possible s"
        by (rule
            accepted_with_bound_tables_hash_collision_imp_supported_hash_output_collision_possible
            [OF outcome' bound' collision_final'])
      then show ?thesis by simp
    qed
  next
    assume "query_supported_pairwise_coupling_bad s"
    then show ?thesis by simp
  qed
qed

lemma query_header_supported_candidate_unique_if_no_pairwise_merkle_bad:
  assumes no_bad:
    "\<not> query_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final
      as dg composition_fri_roots final"
  shows
    "\<exists>trace_table composition_table.
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final \<subseteq>
        {(trace_table, composition_table)}"
proof (rule ccontr)
  assume not_unique:
    "\<not> (\<exists>trace_table composition_table.
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final \<subseteq>
        {(trace_table, composition_table)})"
  have "query_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final
      as dg composition_fri_roots final"
    using
      query_header_supported_table_candidates_not_singleton_imp_pairwise_merkle_bad
        [OF not_unique]
    unfolding query_header_supported_pairwise_merkle_bad_def
    by blast
  then show False
    using no_bad by contradiction
qed

lemma query_header_supported_candidate_unique_if_no_global_pairwise_merkle_bad:
  assumes no_bad: "\<not> query_supported_pairwise_merkle_bad s"
  shows
    "\<exists>trace_table composition_table.
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final \<subseteq>
        {(trace_table, composition_table)}"
proof (rule query_header_supported_candidate_unique_if_no_pairwise_merkle_bad)
  show "\<not> query_header_supported_pairwise_merkle_bad s fr f_fri_roots
      f_final as dg composition_fri_roots final"
    using no_bad unfolding query_supported_pairwise_merkle_bad_def by blast
qed

definition query_header_supported_union_good_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat set"
  where
    "query_header_supported_union_good_sets s good_sets fr f_fri_roots
      f_final as dg composition_fri_roots final =
      {idx \<in> query_sample_space.
        \<exists>trace_table composition_table.
          (trace_table, composition_table) \<in>
            query_header_supported_table_candidates s fr f_fri_roots f_final
              as dg composition_fri_roots final \<and>
          idx \<in> good_sets trace_table composition_table as}"

lemma query_header_supported_union_good_sets_subset:
  "query_header_supported_union_good_sets s good_sets fr f_fri_roots
      f_final as dg composition_fri_roots final \<subseteq> query_sample_space"
  unfolding query_header_supported_union_good_sets_def by auto

definition query_header_rounds_any_index_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
        'f list \<Rightarrow> 'f \<Rightarrow> nat set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_header_rounds_any_index_set_hit s B out \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final rest.
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest \<and>
        query_rounds_any_index_set_hit s
          (B fr f_fri_roots f_final as dg composition_fri_roots final)
          rounds out)"

lemma query_header_supported_union_good_sets_fraction_bound_if_unique_candidate:
  assumes unique:
      "\<exists>trace_table composition_table.
        query_header_supported_table_candidates s fr f_fri_roots f_final as
          dg composition_fri_roots final \<subseteq>
          {(trace_table, composition_table)}"
    and subset:
      "\<And>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and bound:
      "\<And>trace_table composition_table as.
        nnreal
          (query_raw_preimage_card_envelope
            (card (good_sets trace_table composition_table as))) /
          nnreal size \<le> query_error_bound"
  shows
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (query_header_supported_union_good_sets s good_sets fr f_fri_roots
            f_final as dg composition_fri_roots final))) /
      nnreal size \<le> query_error_bound"
proof -
  from unique obtain trace_table composition_table where candidates:
    "query_header_supported_table_candidates s fr f_fri_roots f_final as dg
      composition_fri_roots final \<subseteq>
      {(trace_table, composition_table)}"
    by blast
  have union_subset:
    "query_header_supported_union_good_sets s good_sets fr f_fri_roots
      f_final as dg composition_fri_roots final \<subseteq>
      good_sets trace_table composition_table as"
    unfolding query_header_supported_union_good_sets_def
    using candidates by auto
  have finite_good: "finite (good_sets trace_table composition_table as)"
    by (rule finite_subset[OF subset finite_query_sample_space])
  have card_le:
    "card
      (query_header_supported_union_good_sets s good_sets fr f_fri_roots
        f_final as dg composition_fri_roots final) \<le>
      card (good_sets trace_table composition_table as)"
    by (rule card_mono[OF finite_good union_subset])
  have envelope_le:
    "query_raw_preimage_card_envelope
        (card
          (query_header_supported_union_good_sets s good_sets fr f_fri_roots
            f_final as dg composition_fri_roots final)) \<le>
      query_raw_preimage_card_envelope
        (card (good_sets trace_table composition_table as))"
    by (rule query_raw_preimage_card_envelope_mono[OF card_le])
  have "nnreal
        (query_raw_preimage_card_envelope
          (card
            (query_header_supported_union_good_sets s good_sets fr f_fri_roots
              f_final as dg composition_fri_roots final))) /
      nnreal size \<le>
      nnreal
        (query_raw_preimage_card_envelope
          (card (good_sets trace_table composition_table as))) /
        nnreal size"
    by (rule nnreal_nat_divide_right_mono[OF envelope_le])
  also have "... \<le> query_error_bound"
    by (rule bound)
  finally show ?thesis .
qed

lemma query_header_supported_union_good_sets_fraction_bound_if_no_pairwise_merkle_bad:
  assumes no_bad:
      "\<not> query_header_supported_pairwise_merkle_bad s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    and subset:
      "\<And>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and bound:
      "\<And>trace_table composition_table as.
        nnreal
          (query_raw_preimage_card_envelope
            (card (good_sets trace_table composition_table as))) /
          nnreal size \<le> query_error_bound"
  shows
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (query_header_supported_union_good_sets s good_sets fr f_fri_roots
            f_final as dg composition_fri_roots final))) /
      nnreal size \<le> query_error_bound"
proof -
  have unique:
    "\<exists>trace_table composition_table.
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final \<subseteq>
        {(trace_table, composition_table)}"
    by (rule query_header_supported_candidate_unique_if_no_pairwise_merkle_bad
        [OF no_bad])
  show ?thesis
    by (rule query_header_supported_union_good_sets_fraction_bound_if_unique_candidate
        [OF unique subset bound])
qed

lemma query_header_supported_union_good_sets_fraction_bound_if_no_global_pairwise_merkle_bad:
  assumes no_bad: "\<not> query_supported_pairwise_merkle_bad s"
    and subset:
      "\<And>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and bound:
      "\<And>trace_table composition_table as.
        nnreal
          (query_raw_preimage_card_envelope
            (card (good_sets trace_table composition_table as))) /
          nnreal size \<le> query_error_bound"
  shows
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (query_header_supported_union_good_sets s good_sets fr f_fri_roots
            f_final as dg composition_fri_roots final))) /
      nnreal size \<le> query_error_bound"
proof -
  have no_header_bad:
    "\<not> query_header_supported_pairwise_merkle_bad s fr f_fri_roots
      f_final as dg composition_fri_roots final"
    using no_bad unfolding query_supported_pairwise_merkle_bad_def by blast
  show ?thesis
    by (rule
        query_header_supported_union_good_sets_fraction_bound_if_no_pairwise_merkle_bad
        [OF no_header_bad subset bound])
qed

definition query_header_committed_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> ('f list \<times> 'f list) set"
  where
    "query_header_committed_table_candidates s fr composition_fri_roots =
      {(trace_table, composition_table).
        merkle_root_binds_table fr trace_table s \<and>
        composition_fri_roots \<noteq> [] \<and>
        merkle_root_binds_table (hd composition_fri_roots) composition_table
          s}"

definition query_header_committed_union_good_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
  where
    "query_header_committed_union_good_sets s good_sets fr as
      composition_fri_roots =
      {idx \<in> query_sample_space.
        \<exists>trace_table composition_table.
          (trace_table, composition_table) \<in>
            query_header_committed_table_candidates s fr
              composition_fri_roots \<and>
          idx \<in> good_sets trace_table composition_table as}"

lemma query_header_committed_union_good_sets_subset:
  "query_header_committed_union_good_sets s good_sets fr as
      composition_fri_roots \<subseteq> query_sample_space"
  unfolding query_header_committed_union_good_sets_def by auto

lemma query_header_committed_union_good_sets_fraction_bound_if_unique_candidate:
  assumes unique:
      "\<exists>trace_table composition_table.
        query_header_committed_table_candidates s fr composition_fri_roots
          \<subseteq> {(trace_table, composition_table)}"
    and subset:
      "\<And>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and bound:
      "\<And>trace_table composition_table as.
        nnreal
          (query_raw_preimage_card_envelope
            (card (good_sets trace_table composition_table as))) /
          nnreal size \<le> query_error_bound"
  shows
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (query_header_committed_union_good_sets s good_sets fr as
            composition_fri_roots))) /
      nnreal size \<le> query_error_bound"
proof -
  from unique obtain trace_table composition_table where candidates:
    "query_header_committed_table_candidates s fr composition_fri_roots
      \<subseteq> {(trace_table, composition_table)}"
    by blast
  have union_subset:
    "query_header_committed_union_good_sets s good_sets fr as
      composition_fri_roots \<subseteq> good_sets trace_table composition_table as"
    unfolding query_header_committed_union_good_sets_def
    using candidates by auto
  have finite_good: "finite (good_sets trace_table composition_table as)"
    by (rule finite_subset[OF subset finite_query_sample_space])
  have card_le:
    "card
      (query_header_committed_union_good_sets s good_sets fr as
        composition_fri_roots) \<le>
      card (good_sets trace_table composition_table as)"
    by (rule card_mono[OF finite_good union_subset])
  have envelope_le:
    "query_raw_preimage_card_envelope
        (card
          (query_header_committed_union_good_sets s good_sets fr as
            composition_fri_roots)) \<le>
      query_raw_preimage_card_envelope
        (card (good_sets trace_table composition_table as))"
    by (rule query_raw_preimage_card_envelope_mono[OF card_le])
  have "nnreal
        (query_raw_preimage_card_envelope
          (card
            (query_header_committed_union_good_sets s good_sets fr as
              composition_fri_roots))) /
      nnreal size \<le>
      nnreal
        (query_raw_preimage_card_envelope
          (card (good_sets trace_table composition_table as))) /
        nnreal size"
    by (rule nnreal_nat_divide_right_mono[OF envelope_le])
  also have "... \<le> query_error_bound"
    by (rule bound)
  finally show ?thesis .
qed

lemma query_header_committed_table_candidates_subset_singleton_if_no_root_collisions:
  assumes trace_clean: "\<not> merkle_root_binding_collision fr s"
    and comp_clean:
      "\<And>rt. composition_fri_roots \<noteq> [] \<Longrightarrow>
        rt = hd composition_fri_roots \<Longrightarrow>
        \<not> merkle_root_binding_collision rt s"
  shows
    "\<exists>trace_table composition_table.
      query_header_committed_table_candidates s fr composition_fri_roots
        \<subseteq> {(trace_table, composition_table)}"
proof (cases
    "query_header_committed_table_candidates s fr composition_fri_roots = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"] exI[of _ "[]"]) simp
next
  case False
  then obtain pair where pair_in:
    "pair \<in>
      query_header_committed_table_candidates s fr composition_fri_roots"
    by blast
  then obtain trace_table composition_table where pair_eq:
    "pair = (trace_table, composition_table)"
    by (cases pair)
  have candidate:
    "(trace_table, composition_table) \<in>
      query_header_committed_table_candidates s fr composition_fri_roots"
    using pair_in unfolding pair_eq .
  have trace_bind:
    "merkle_root_binds_table fr trace_table s"
    using candidate unfolding query_header_committed_table_candidates_def
    by simp
  have comp_nonempty: "composition_fri_roots \<noteq> []"
    using candidate unfolding query_header_committed_table_candidates_def
    by simp
  have comp_bind:
    "merkle_root_binds_table (hd composition_fri_roots) composition_table s"
    using candidate unfolding query_header_committed_table_candidates_def
    by simp
  have candidates:
    "query_header_committed_table_candidates s fr composition_fri_roots
      \<subseteq> {(trace_table, composition_table)}"
  proof
    fix pair
    assume pair_in:
      "pair \<in>
        query_header_committed_table_candidates s fr composition_fri_roots"
    obtain trace_table' composition_table' where pair_eq:
      "pair = (trace_table', composition_table')"
      by (cases pair)
    have trace_bind':
      "merkle_root_binds_table fr trace_table' s"
      using pair_in unfolding pair_eq
        query_header_committed_table_candidates_def
      by simp
    have comp_bind':
      "merkle_root_binds_table (hd composition_fri_roots) composition_table'
        s"
      using pair_in unfolding pair_eq
        query_header_committed_table_candidates_def
      by simp
    have trace_eq: "trace_table' = trace_table"
      using merkle_root_binds_table_unique_if_no_collision
        [OF trace_clean trace_bind' trace_bind] by simp
    have comp_eq: "composition_table' = composition_table"
      using merkle_root_binds_table_unique_if_no_collision
        [OF comp_clean[OF comp_nonempty refl] comp_bind' comp_bind]
      by simp
    show "pair \<in> {(trace_table, composition_table)}"
      unfolding pair_eq trace_eq comp_eq by simp
  qed
  show ?thesis
    using candidates by blast
qed

lemma query_index_round_set_hit_at_imp_query_header_supported_union_hit:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and hit: "query_index_round_set_hit_at s good_sets i out"
  shows
    "\<exists>fr f_fri_roots f_final as dg composition_fri_roots final.
      query_rounds_any_index_set_hit s
        (query_header_supported_union_good_sets s good_sets fr f_fri_roots
          f_final as dg composition_fri_roots final)
        rounds out"
proof -
  from hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and i_bound: "i < rounds"
    and query_hit:
      "query_idxs ! i \<in> good_sets trace_table composition_table as"
    unfolding query_index_round_set_hit_at_def by blast
  from bound obtain result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    out_eq: "out = Some (result, final_state)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding accepted_with_bound_tables_def by blast
  have candidate:
    "(trace_table, composition_table) \<in>
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final"
    unfolding query_header_supported_table_candidates_def
    using outcome bound header by blast
  have len: "length query_idxs = rounds"
    by (rule accepted_with_bound_tables_shapes(4)[OF bound])
  have idx_mem: "query_idxs ! i \<in> set query_idxs"
    by (rule nth_mem) (use i_bound len in simp)
  have idx_sample: "query_idxs ! i \<in> query_sample_space"
    by (rule accepted_with_bound_tables_query_sample_space
        [OF bound idx_mem])
  have union_hit:
    "query_idxs ! i \<in>
      query_header_supported_union_good_sets s good_sets fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_union_good_sets_def
    using idx_sample candidate query_hit by blast
  have round_hit:
    "query_rounds_any_index_set_hit s
      (query_header_supported_union_good_sets s good_sets fr f_fri_roots
        f_final as dg composition_fri_roots final)
      rounds out"
    by (rule accepted_with_bound_tables_query_rounds_any_index_set_hit
        [OF bound i_bound union_hit])
  show ?thesis
    using round_hit by blast
qed

lemma query_index_round_set_hit_at_imp_query_header_supported_rounds_hit:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and hit: "query_index_round_set_hit_at s good_sets i out"
  shows
    "query_header_rounds_any_index_set_hit s
      (query_header_supported_union_good_sets s good_sets) out"
proof -
  from hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and i_bound: "i < rounds"
    and query_hit:
      "query_idxs ! i \<in> good_sets trace_table composition_table as"
    unfolding query_index_round_set_hit_at_def by blast
  from bound obtain result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding accepted_with_bound_tables_def by blast
  from query_index_round_set_hit_at_imp_query_header_supported_union_hit
      [OF outcome hit]
  obtain fr' f_fri_roots' f_final' as' dg' composition_fri_roots' final'
    where round_hit':
      "query_rounds_any_index_set_hit s
        (query_header_supported_union_good_sets s good_sets fr' f_fri_roots'
          f_final' as' dg' composition_fri_roots' final')
        rounds out"
    by blast
  have candidate:
    "(trace_table, composition_table) \<in>
      query_header_supported_table_candidates s fr f_fri_roots f_final as dg
        composition_fri_roots final"
    unfolding query_header_supported_table_candidates_def
    using outcome bound header by blast
  have len: "length query_idxs = rounds"
    by (rule accepted_with_bound_tables_shapes(4)[OF bound])
  have idx_mem: "query_idxs ! i \<in> set query_idxs"
    by (rule nth_mem) (use i_bound len in simp)
  have idx_sample: "query_idxs ! i \<in> query_sample_space"
    by (rule accepted_with_bound_tables_query_sample_space
        [OF bound idx_mem])
  have union_hit:
    "query_idxs ! i \<in>
      query_header_supported_union_good_sets s good_sets fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_union_good_sets_def
    using idx_sample candidate query_hit by blast
  have round_hit:
    "query_rounds_any_index_set_hit s
      (query_header_supported_union_good_sets s good_sets fr f_fri_roots
        f_final as dg composition_fri_roots final)
      rounds out"
    by (rule accepted_with_bound_tables_query_rounds_any_index_set_hit
        [OF bound i_bound union_hit])
  show ?thesis
    unfolding query_header_rounds_any_index_set_hit_def
    using header round_hit by blast
qed

lemma query_index_round_set_hit_imp_query_header_supported_rounds_hit:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and hit: "query_index_round_set_hit s good_sets out"
  shows
    "query_header_rounds_any_index_set_hit s
      (query_header_supported_union_good_sets s good_sets) out"
proof -
  from hit obtain i where
    hit_at: "query_index_round_set_hit_at s good_sets i out"
    unfolding query_index_round_set_hit_def by blast
  show ?thesis
    by (rule query_index_round_set_hit_at_imp_query_header_supported_rounds_hit
        [OF outcome hit_at])
qed

lemma query_index_set_hit_empty_queries:
  assumes bound:
    "accepted_with_bound_tables s out trace_table composition_table as []"
  shows "query_index_set_hit s good_sets out"
  unfolding query_index_set_hit_def
  apply (rule exI[where x=trace_table])
  apply (rule exI[where x=composition_table])
  apply (rule exI[where x=as])
  apply (rule exI[where x="[]"])
  using bound by simp

lemma query_index_set_hit_vacuous_if_rounds_zero:
  assumes rounds_zero: "rounds = 0"
    and bound:
      "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
  shows "query_index_set_hit s good_sets out"
proof -
  have "length query_idxs = 0"
    using accepted_with_bound_tables_shapes(4)[OF bound] rounds_zero by simp
  then have query_idxs_empty: "query_idxs = []"
    by simp
  show ?thesis
    using bound unfolding query_idxs_empty
    by (rule query_index_set_hit_empty_queries)
qed

lemma query_index_set_hit_imp_round_set_hit:
  assumes hit: "query_index_set_hit s good_sets out"
  shows "query_index_round_set_hit s good_sets out"
proof -
  from hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and subset:
      "set query_idxs \<subseteq> good_sets trace_table composition_table as"
    unfolding query_index_set_hit_def by blast
  have len: "length query_idxs = rounds"
    by (rule accepted_with_bound_tables_shapes(4)[OF bound])
  have zero_bound: "0 < length query_idxs"
    using len rounds_positive by simp
  have nth_in: "query_idxs ! 0 \<in> set query_idxs"
    by (rule nth_mem[OF zero_bound])
  have round_hit:
    "query_index_round_set_hit_at s good_sets 0 out"
    unfolding query_index_round_set_hit_at_def
    apply (rule exI[where x=trace_table])
    apply (rule exI[where x=composition_table])
    apply (rule exI[where x=as])
    apply (rule exI[where x=query_idxs])
    using bound subset nth_in rounds_positive by auto
  show ?thesis
    unfolding query_index_round_set_hit_def
    using round_hit rounds_positive by blast
qed

lemma accepted_with_bound_tables_query_samples_miss_if_not_all_consistent:
  assumes bound:
      "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows "query_samples_miss_disagreements trace_table composition_table as query_idxs"
proof -
  have disagreements:
    "query_disagreement_indices trace_table composition_table as \<noteq> {}"
    using not_all query_disagreement_indices_nonempty_iff by blast
  have samples_agree:
    "set query_idxs \<subseteq> query_agreement_indices trace_table composition_table as"
  proof
    fix idx
    assume idx_in: "idx \<in> set query_idxs"
    have sample: "idx \<in> query_sample_space"
      by (rule accepted_with_bound_tables_query_sample_space[OF bound idx_in])
    have consistent:
      "query_consistent_at trace_table composition_table as idx"
      by (rule accepted_with_bound_tables_query_consistency[OF bound idx_in])
    show "idx \<in> query_agreement_indices trace_table composition_table as"
      using sample consistent unfolding query_agreement_indices_def by simp
  qed
  show ?thesis
    using disagreements samples_agree
    unfolding query_samples_miss_disagreements_def by simp
qed

lemma query_sampling_success_space_subset:
  "query_sampling_success_space trace_table composition_table as \<subseteq> query_sample_space"
  unfolding query_sampling_success_space_def query_agreement_indices_def by auto

lemma query_sampling_success_space_fraction_bound:
  shows
    "nnreal (card (query_sampling_success_space trace_table composition_table as)) /
      nnreal query_sample_space_size \<le> query_error_bound"
proof (cases
    "trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      \<not> all_queries_consistent trace_table composition_table as")
  case True
  then have space_eq:
    "query_sampling_success_space trace_table composition_table as =
      query_agreement_indices trace_table composition_table as"
    unfolding query_sampling_success_space_def by simp
  have card_le:
    "card (query_sampling_success_space trace_table composition_table as) \<le>
      query_agreement_bound"
    unfolding space_eq
    by (rule query_agreement_indices_card_bound)
      (use True in auto)
  show ?thesis
    by (rule query_uniform_fraction_le_query_error_bound[OF card_le])
next
  case False
  then have space_eq:
    "query_sampling_success_space trace_table composition_table as = {}"
    unfolding query_sampling_success_space_def by auto
  show ?thesis
    unfolding space_eq by simp
qed

lemma query_sampling_success_space_envelope_fraction_bound:
  shows
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (query_sampling_success_space trace_table composition_table as))) /
      nnreal size \<le> query_error_bound"
proof (cases
    "trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      \<not> all_queries_consistent trace_table composition_table as")
  case True
  then have space_eq:
    "query_sampling_success_space trace_table composition_table as =
      query_agreement_indices trace_table composition_table as"
    unfolding query_sampling_success_space_def by simp
  have card_le:
    "card (query_sampling_success_space trace_table composition_table as) \<le>
      query_agreement_bound"
    unfolding space_eq
    by (rule query_agreement_indices_card_bound)
      (use True in auto)
  show ?thesis
    by (rule
        query_raw_preimage_card_envelope_probability_le_query_error_bound[
          OF card_le])
next
  case False
  then have space_eq:
    "query_sampling_success_space trace_table composition_table as = {}"
    unfolding query_sampling_success_space_def by auto
  show ?thesis
    unfolding space_eq query_raw_preimage_card_envelope_def by simp
qed


lemma query_sampling_success_space_fraction_bound_query_sample_space:
  shows
    "nnreal (card (query_sampling_success_space trace_table composition_table as)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
  using query_sampling_success_space_fraction_bound[of trace_table composition_table as]
  by simp

lemma query_sampling_success_header_supported_union_fraction_bound_if_no_global_pairwise_merkle_bad:
  assumes no_bad: "\<not> query_supported_pairwise_merkle_bad s"
  shows
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (query_header_supported_union_good_sets s query_sampling_success_space
            fr f_fri_roots f_final as dg composition_fri_roots final))) /
      nnreal size \<le> query_error_bound"
  by (rule
      query_header_supported_union_good_sets_fraction_bound_if_no_global_pairwise_merkle_bad
      [OF no_bad query_sampling_success_space_subset
        query_sampling_success_space_envelope_fraction_bound])

definition query_index_raw_preimage_bound :: bool
  where
    "query_index_raw_preimage_bound \<longleftrightarrow>
      (\<forall>B.
        B \<subseteq> query_sample_space \<longrightarrow>
        nnreal (card (query_index_raw_preimage B)) / nnreal size \<le>
          nnreal (query_raw_preimage_card_envelope (card B)) /
            nnreal size)"

lemma query_index_raw_preimage_bound_from_sampler_wellformed:
  "query_index_raw_preimage_bound"
  unfolding query_index_raw_preimage_bound_def
  using query_index_raw_preimage_probability_le_envelope by blast

lemma query_index_raw_preimage_singleton_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and b_in: "b \<in> query_sample_space"
  shows
    "nnreal (card (query_index_raw_preimage {b})) / nnreal size \<le>
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have subset: "{b} \<subseteq> query_sample_space"
    using b_in by simp
  have "nnreal (card (query_index_raw_preimage {b})) / nnreal size \<le>
      nnreal (query_raw_preimage_card_envelope (card {b})) / nnreal size"
    using raw_bound subset unfolding query_index_raw_preimage_bound_def
    by blast
  then show ?thesis
    by simp
qed

lemma query_index_raw_preimage_fraction_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and envelope:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "nnreal (card (query_index_raw_preimage B)) / nnreal size \<le>
      query_error_bound"
proof -
  have "nnreal (card (query_index_raw_preimage B)) / nnreal size \<le>
      nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size"
    using raw_bound subset unfolding query_index_raw_preimage_bound_def by blast
  also have "... \<le> query_error_bound"
    by (rule envelope)
  finally show ?thesis .
qed

lemma wp_receive_query_index_challenge_fresh_index_set_raw_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
  shows
    "wp_event receive_query_index_challenge
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B) s \<le>
      nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size"
proof -
  have fresh:
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
    by (rule query_future_fresh_current[OF future])
  have exact:
    "wp_event receive_query_index_challenge
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B) s =
      nnreal (card (query_index_raw_preimage B)) / nnreal size"
    by (rule wp_receive_query_index_challenge_fresh_index_set[OF fresh])
  have raw:
    "nnreal (card (query_index_raw_preimage B)) / nnreal size \<le>
      nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size"
    using raw_bound subset
    unfolding query_index_raw_preimage_bound_def by blast
  show ?thesis
    unfolding exact by (rule raw)
qed

lemma wp_receive_query_index_challenge_fresh_index_set_query_error_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and envelope:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event receive_query_index_challenge
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B) s \<le>
      query_error_bound"
  by (rule order_trans
      [OF wp_receive_query_index_challenge_fresh_index_set_raw_bound
        [OF future raw_bound subset] envelope])

lemma wp_verifier_query_round_program_index_set_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
  shows
    "wp_event
      (verifier_query_round_program fr f_fl f_final as fl final)
      (query_round_index_set_hit s B) s \<le>
      nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size"
proof -
  let ?P =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B"
  have head_bound:
    "wp_event receive_query_index_challenge ?P s \<le>
      nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size"
    by (rule wp_receive_query_index_challenge_fresh_index_set_raw_bound
        [OF future raw_bound subset])
  show ?thesis
    unfolding verifier_query_round_program_alt_def
  proof (rule wp_event_bind_bound_by_head_event[OF head_bound])
    show "query_round_index_set_hit s B None \<Longrightarrow> ?P None"
      unfolding query_round_index_set_hit_def by simp
  next
    fix raw s0 out
    assume head:
        "Some (raw, s0) \<in>
          set_dist (execute receive_query_index_challenge s)"
      and tail:
        "out \<in>
          set_dist
            (execute
              (verifier_query_round_after_index_program fr f_fl f_final as fl
                final raw) s0)"
      and hit: "query_round_index_set_hit s B out"
    from hit obtain raw' t where out_eq: "out = Some ((), t)"
      and lookup_t:
        "fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw'"
      and raw'_in: "index (to_nat raw') \<in> B"
      unfolding query_round_index_set_hit_def by blast
    have tail_out:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw) s0)"
      using tail out_eq by simp
    have ext_s0_t: "s0 \<le> t"
      using verifier_query_round_after_index_program_outcome[OF tail_out]
      by simp
    have lookup_s0:
      "fmlookup (HashMap s0)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
      using receive_query_index_challenge_outcome[OF head] by blast
    have lookup_t_raw:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
      by (rule hash_extension_lookup[OF lookup_s0 ext_s0_t])
    have "raw = raw'"
      using lookup_t_raw lookup_t by simp
    then show "?P (Some (raw, s0))"
      using raw'_in by simp
  qed
qed

lemma wp_verifier_query_round_program_index_set_query_error_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and envelope:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event
      (verifier_query_round_program fr f_fl f_final as fl final)
      (query_round_index_set_hit s B) s \<le> query_error_bound"
  by (rule order_trans
      [OF wp_verifier_query_round_program_index_set_bound
        [OF future raw_bound subset] envelope])

lemma wp_verifier_query_round_program_any_index_set_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
  shows
    "wp_event
      (verifier_query_round_program fr f_fl f_final as fl final)
      (query_round_any_index_set_hit s B) s \<le>
      nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size"
proof -
  let ?P =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B"
  have head_bound:
    "wp_event receive_query_index_challenge ?P s \<le>
      nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size"
    by (rule wp_receive_query_index_challenge_fresh_index_set_raw_bound
        [OF future raw_bound subset])
  show ?thesis
    unfolding verifier_query_round_program_alt_def
  proof (rule wp_event_bind_bound_by_head_event[OF head_bound])
    show "query_round_any_index_set_hit s B None \<Longrightarrow> ?P None"
      unfolding query_round_any_index_set_hit_def by simp
  next
    fix raw s0 out
    assume head:
        "Some (raw, s0) \<in>
          set_dist (execute receive_query_index_challenge s)"
      and tail:
        "out \<in>
          set_dist
            (execute
              (verifier_query_round_after_index_program fr f_fl f_final as fl
                final raw) s0)"
      and hit: "query_round_any_index_set_hit s B out"
    from hit obtain raw' t x where out_eq: "out = Some ((), t)"
      and lookup_t:
        "fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s) x) = Some raw'"
      and raw'_in: "index (to_nat raw') \<in> B"
      unfolding query_round_any_index_set_hit_def by blast
    have tail_out:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw) s0)"
      using tail out_eq by simp
    have lookup_s0_x:
      "fmlookup (HashMap s0)
        (QueryIndexChallenge (PQueryCounter s) x) = Some raw'"
      using verifier_query_round_after_index_program_preserves_query_lookup
          [OF tail_out, of "PQueryCounter s" x]
        lookup_t
      by simp
    have lookup_current:
      "fmlookup (HashMap s0)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
      using receive_query_index_challenge_outcome[OF head] by blast
    have key_eq:
      "QueryIndexChallenge (PQueryCounter s) x =
        QueryIndexChallenge (PQueryCounter s) (PState s)"
    proof (rule ccontr)
      assume neq:
        "QueryIndexChallenge (PQueryCounter s) x \<noteq>
          QueryIndexChallenge (PQueryCounter s) (PState s)"
      have lookup_s0_x':
        "fmlookup (HashMap s0)
          (QueryIndexChallenge (PQueryCounter s) x) =
         fmlookup (HashMap s)
          (QueryIndexChallenge (PQueryCounter s) x)"
        by (rule receive_query_index_challenge_preserves_other_lookup
            [OF head neq])
      have "fmlookup (HashMap s)
          (QueryIndexChallenge (PQueryCounter s) x) = None"
        using future unfolding query_future_fresh_def by simp
      then show False
        using lookup_s0_x lookup_s0_x' by simp
    qed
    have "raw' = raw"
      using lookup_s0_x lookup_current key_eq by simp
    then show "?P (Some (raw, s0))"
      using raw'_in by simp
  qed
qed

lemma wp_ntimes_verifier_query_round_program_any_index_set_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
  shows
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n)
      (query_rounds_any_index_set_hit s B n) s \<le>
      nnreal n *
        (nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size)"
  using future
proof (induction n arbitrary: s)
  case 0
  show ?case
    unfolding query_rounds_any_index_set_hit_def
    by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  let ?prog = "verifier_query_round_program fr f_fl f_final as fl final"
  let ?C = "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size"
  let ?Q = "query_rounds_any_index_set_hit s B (Suc n)"
  let ?Head =
    "\<lambda>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of None \<Rightarrow> False
      | Some (_, t) \<Rightarrow>
          (\<exists>raw x.
            fmlookup (HashMap t)
              (QueryIndexChallenge (PQueryCounter s) x) = Some raw \<and>
            index (to_nat raw) \<in> B)"
  let ?Tail =
    "\<lambda>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of None \<Rightarrow> False
      | Some (_, t) \<Rightarrow>
          (\<exists>i < n. \<exists>x raw.
            fmlookup (HashMap t)
              (QueryIndexChallenge (PQueryCounter s + Suc i) x) =
                Some raw \<and>
            index (to_nat raw) \<in> B)"
  have split_hit:
    "\<And>out. ?Q out \<Longrightarrow> ?Head out \<or> ?Tail out"
  proof -
    fix out
    assume "?Q out"
    then obtain results t i x raw where out_eq: "out = Some (results, t)"
      and i_bound: "i < Suc n"
      and lookup:
        "fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i) x) = Some raw"
      and raw_in: "index (to_nat raw) \<in> B"
      unfolding query_rounds_any_index_set_hit_def by blast
    show "?Head out \<or> ?Tail out"
    proof (cases i)
      case 0
      then have "?Head out"
        using out_eq lookup raw_in by simp blast
      then show ?thesis by simp
    next
      case (Suc j)
      then have j_bound: "j < n"
        using i_bound by simp
      have "?Tail out"
        using out_eq lookup raw_in j_bound Suc by simp blast
      then show ?thesis by simp
    qed
  qed
  have head_bound:
    "wp_event (ntimes ?prog (Suc n)) ?Head s \<le> ?C"
  proof -
    have one_bound:
      "wp_event ?prog (query_round_any_index_set_hit s B) s \<le> ?C"
      by (rule wp_verifier_query_round_program_any_index_set_bound
          [OF Suc.prems raw_bound subset])
    show ?thesis
      unfolding ntimes.simps
    proof (rule wp_event_bind_bound_by_head_event[OF one_bound])
      show "?Head None \<Longrightarrow> query_round_any_index_set_hit s B None"
        by simp
    next
      fix u s1 out
      assume head:
          "Some (u, s1) \<in> set_dist (execute ?prog s)"
        and tail:
          "out \<in>
            set_dist
              (execute
                (ntimes ?prog n \<bind> (\<lambda>xs. return (u # xs))) s1)"
        and hit: "?Head out"
      have u_eq: "u = ()"
        by (cases u) simp
      from hit obtain ys0 t0 where out_some: "out = Some (ys0, t0)"
        by (cases out) auto
      from tail[unfolded out_some] obtain results t where
        tail_rounds:
          "Some (results, t) \<in> set_dist (execute (ntimes ?prog n) s1)"
        and out_ret:
          "Some (ys0, t0) \<in> set_dist (execute (return (u # results)) t)"
        by (rule set_dist_bindE)
      have out_eq: "out = Some (u # results, t)"
        using out_ret out_some
        by simp
      from hit obtain raw x where lookup_t:
          "fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s) x) = Some raw"
        and raw_in: "index (to_nat raw) \<in> B"
        using out_eq by auto
      have counter_s1: "PQueryCounter s1 = Suc (PQueryCounter s)"
        using verifier_query_round_program_outcome[OF head[unfolded u_eq]]
        by blast
      have past: "PQueryCounter s < PQueryCounter s1"
        using counter_s1 by simp
      have lookup_s1:
        "fmlookup (HashMap s1)
          (QueryIndexChallenge (PQueryCounter s) x) = Some raw"
        using ntimes_verifier_query_round_program_preserves_past_query_lookup
            [OF past tail_rounds, of x]
          lookup_t
        by simp
      show "query_round_any_index_set_hit s B (Some (u, s1))"
        unfolding query_round_any_index_set_hit_def
        using lookup_s1 raw_in u_eq by blast
    qed
  qed
  have tail_bound:
    "wp_event (ntimes ?prog (Suc n)) ?Tail s \<le> nnreal n * ?C"
  proof -
    show ?thesis
      unfolding ntimes.simps
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?Tail None"
        by simp
    next
      fix u s1
      assume head:
        "Some (u, s1) \<in> set_dist (execute ?prog s)"
      have u_eq: "u = ()"
        by (cases u) simp
      have future_s1: "query_future_fresh s1"
        by (rule verifier_query_round_program_preserves_query_future_fresh
            [OF Suc.prems head[unfolded u_eq]])
      have counter_s1: "PQueryCounter s1 = Suc (PQueryCounter s)"
        using verifier_query_round_program_outcome[OF head[unfolded u_eq]]
        by blast
      have tail_induct:
        "wp_event (ntimes ?prog n)
          (query_rounds_any_index_set_hit s1 B n) s1 \<le>
          nnreal n * ?C"
        by (rule Suc.IH[OF future_s1])
      show "wp_event
          (ntimes ?prog n \<bind> (\<lambda>xs. return (u # xs))) ?Tail s1
          \<le> nnreal n * ?C"
      proof (rule wp_event_bind_bound_by_head_event[OF tail_induct])
        show "?Tail None \<Longrightarrow> query_rounds_any_index_set_hit s1 B n None"
          by simp
      next
        fix results t out
        assume tail_rounds:
            "Some (results, t) \<in>
              set_dist (execute (ntimes ?prog n) s1)"
          and ret:
            "out \<in> set_dist (execute (return (u # results)) t)"
          and hit: "?Tail out"
        have out_eq: "out = Some (u # results, t)"
          using ret
          unfolding set_dist_def return.rep_eq dist_return_def
            dist_delta_dist delta_map_def
          by simp
        from hit obtain i x raw where i_bound: "i < n"
          and lookup:
            "fmlookup (HashMap t)
              (QueryIndexChallenge (PQueryCounter s + Suc i) x) =
                Some raw"
          and raw_in: "index (to_nat raw) \<in> B"
          using out_eq by auto
        have key_eq:
          "Suc (PQueryCounter s + i) = PQueryCounter s1 + i"
          using counter_s1 by presburger
        have lookup':
          "fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s1 + i) x) = Some raw"
          using lookup key_eq by simp
        show "query_rounds_any_index_set_hit s1 B n (Some (results, t))"
          unfolding query_rounds_any_index_set_hit_def
          apply (rule exI[where x=results])
          apply (rule exI[where x=t])
          apply (rule exI[where x=i])
          apply (rule exI[where x=x])
          apply (rule exI[where x=raw])
          using i_bound lookup' raw_in by simp
      qed
    qed
  qed
  have "wp_event (ntimes ?prog (Suc n)) ?Q s \<le>
      wp_event (ntimes ?prog (Suc n))
        (\<lambda>out. ?Head out \<or> ?Tail out) s"
    by (rule wp_event_mono) (use split_hit in blast)
  also have "... \<le> wp_event (ntimes ?prog (Suc n)) ?Head s +
      wp_event (ntimes ?prog (Suc n)) ?Tail s"
    by (rule wp_event_union_bound)
  also have "... \<le> ?C + nnreal n * ?C"
    by (intro add_mono head_bound tail_bound)
  also have "... = nnreal (Suc n) * ?C"
    by (simp add: algebra_simps)
  finally show ?case .
qed

lemma wp_ntimes_verifier_query_round_program_any_index_set_query_error_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and envelope:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n)
      (query_rounds_any_index_set_hit s B n) s \<le>
      nnreal n * query_error_bound"
proof -
  have base:
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n)
      (query_rounds_any_index_set_hit s B n) s \<le>
      nnreal n *
        (nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size)"
    by (rule wp_ntimes_verifier_query_round_program_any_index_set_bound
        [OF future raw_bound subset])
  have mono:
    "nnreal n *
        (nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size) \<le>
      nnreal n * query_error_bound"
    by (rule mult_left_mono) (use envelope in simp_all)
  show ?thesis
    by (rule order_trans[OF base mono])
qed

lemma wp_verifier_after_composition_fri_query_rounds_any_index_set_bound:
  assumes future: "query_future_fresh t"
    and counter: "PQueryCounter t = PQueryCounter s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
  shows
    "wp_event (verifier_after_composition_fri header)
      (query_rounds_any_index_set_hit s B rounds) t \<le>
      nnreal rounds *
        (nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size)"
proof -
  obtain fr f_fl f_final as dg fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg, fl)"
    by (cases header) auto
  have after_eq:
    "verifier_after_composition_fri header =
      (read \<bind>
        (\<lambda>final.
          ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds))"
    unfolding header_eq verifier_after_composition_fri_def by simp
  show ?thesis
    unfolding after_eq
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> query_rounds_any_index_set_hit s B rounds None"
      unfolding query_rounds_any_index_set_hit_def by simp
  next
    fix final query_state
    assume read_final:
      "Some (final, query_state) \<in> set_dist (execute read t)"
    have future_query: "query_future_fresh query_state"
      by (rule read_preserves_query_future_fresh[OF future read_final])
    from read_outcome[OF read_final] obtain rest where
      counter_query_t: "PQueryCounter query_state = PQueryCounter t"
      by blast
    have counter_query: "PQueryCounter query_state = PQueryCounter s"
      using counter_query_t counter by simp
    have event_imp:
      "\<And>out. query_rounds_any_index_set_hit s B rounds out \<Longrightarrow>
        query_rounds_any_index_set_hit query_state B rounds out"
      using counter_query
      unfolding query_rounds_any_index_set_hit_def by auto
    have "wp_event
        (ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds)
        (query_rounds_any_index_set_hit s B rounds) query_state \<le>
      wp_event
        (ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds)
        (query_rounds_any_index_set_hit query_state B rounds) query_state"
      by (rule wp_event_mono) (rule event_imp)
    also have "... \<le>
        nnreal rounds *
          (nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size)"
      by (rule wp_ntimes_verifier_query_round_program_any_index_set_bound
          [OF future_query raw_bound subset])
    finally show
      "wp_event
        (ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds)
        (query_rounds_any_index_set_hit s B rounds) query_state \<le>
      nnreal rounds *
        (nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size)" .
  qed
qed

lemma wp_verify_monad_query_rounds_any_index_set_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
  shows
    "wp_event verify_monad (query_rounds_any_index_set_hit s B rounds) s \<le>
      nnreal rounds *
        (nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size)"
  unfolding verify_monad_composition_fri_decomposition
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> query_rounds_any_index_set_hit s B rounds None"
    unfolding query_rounds_any_index_set_hit_def by simp
next
  fix header t
  assume prefix:
    "Some (header, t) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
  obtain fr f_fl f_final as dg fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg, fl)"
    by (cases header) auto
  have future_t: "query_future_fresh t"
    by (rule verifier_composition_fri_prefix_preserves_query_future_fresh
        [OF future prefix])
  have counter_t: "PQueryCounter t = PQueryCounter s"
    using verifier_composition_fri_prefix_outcome[OF prefix[unfolded header_eq]]
    by simp
  show
    "wp_event (verifier_after_composition_fri header)
      (query_rounds_any_index_set_hit s B rounds) t \<le>
      nnreal rounds *
        (nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size)"
    by (rule
        wp_verifier_after_composition_fri_query_rounds_any_index_set_bound
        [OF future_t counter_t raw_bound subset])
qed

lemma wp_verify_monad_query_rounds_any_index_set_query_error_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and envelope:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event verify_monad (query_rounds_any_index_set_hit s B rounds) s \<le>
      nnreal rounds * query_error_bound"
proof -
  have base:
    "wp_event verify_monad (query_rounds_any_index_set_hit s B rounds) s \<le>
      nnreal rounds *
        (nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size)"
    by (rule wp_verify_monad_query_rounds_any_index_set_bound
        [OF future raw_bound subset])
  have mono:
    "nnreal rounds *
        (nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size) \<le>
      nnreal rounds * query_error_bound"
    by (rule mult_left_mono) (use envelope in simp_all)
  show ?thesis
    by (rule order_trans[OF base mono])
qed

lemma wp_verify_monad_query_header_rounds_any_index_set_bound:
  fixes C :: prob
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots final.
        B fr f_fri_roots f_final as dg composition_fri_roots final
          \<subseteq> query_sample_space"
    and bound:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots final.
        nnreal
          (query_raw_preimage_card_envelope
            (card
              (B fr f_fri_roots f_final as dg composition_fri_roots final))) /
          nnreal size \<le> C"
  shows
    "wp_event verify_monad (query_header_rounds_any_index_set_hit s B) s \<le>
      nnreal rounds * C"
  unfolding verify_monad_composition_fri_decomposition
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> query_header_rounds_any_index_set_hit s B None"
    unfolding query_header_rounds_any_index_set_hit_def
      query_rounds_any_index_set_hit_def
    by auto
next
  fix header prefix_state
  assume prefix:
    "Some (header, prefix_state) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
  obtain fr f_fl f_final as dg fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg, fl)"
    by (cases header) auto
  have prefix_res:
    "length f_fl = ceil_log clength \<and>
     length as = length spec \<and>
     length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s =
       [fr] @ map snd f_fl @ [f_final] @ as @ [dg] @
       map snd fl @ PTranscript prefix_state \<and>
     PQueryCounter prefix_state = PQueryCounter s"
    using verifier_composition_fri_prefix_outcome
        [OF prefix[unfolded header_eq]]
    by simp
  have future_prefix: "query_future_fresh prefix_state"
    by (rule verifier_composition_fri_prefix_preserves_query_future_fresh
        [OF future prefix])
  have after_eq:
    "verifier_after_composition_fri header =
      (read \<bind>
        (\<lambda>final.
          ntimes (verifier_query_round_program fr f_fl f_final as fl final)
            rounds))"
    unfolding header_eq verifier_after_composition_fri_def by simp
  show
    "wp_event (verifier_after_composition_fri header)
      (query_header_rounds_any_index_set_hit s B) prefix_state \<le>
      nnreal rounds * C"
    unfolding after_eq
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> query_header_rounds_any_index_set_hit s B None"
      unfolding query_header_rounds_any_index_set_hit_def
        query_rounds_any_index_set_hit_def
      by auto
  next
    fix final query_state
    assume read_final:
      "Some (final, query_state) \<in> set_dist (execute read prefix_state)"
    from read_outcome[OF read_final] obtain rest where
      tr_prefix: "PTranscript prefix_state = final # rest"
      and tr_query: "PTranscript query_state = rest"
      and query_counter:
        "PQueryCounter query_state = PQueryCounter prefix_state"
      by blast
    have future_query: "query_future_fresh query_state"
      by (rule read_preserves_query_future_fresh[OF future_prefix read_final])
    have counter_query: "PQueryCounter query_state = PQueryCounter s"
      using prefix_res query_counter by simp
    have header_prefix:
      "verifier_header_transcript s fr (map snd f_fl) f_final as dg
        (map snd fl) final (PTranscript query_state)"
      using prefix_res tr_prefix tr_query
      unfolding verifier_header_transcript_def verifier_header_messages_def
      by simp
    let ?B = "B fr (map snd f_fl) f_final as dg (map snd fl) final"
    let ?prog = "verifier_query_round_program fr f_fl f_final as fl final"
    have base:
      "wp_event (ntimes ?prog rounds)
        (query_rounds_any_index_set_hit query_state ?B rounds)
        query_state \<le>
        nnreal rounds *
          (nnreal (query_raw_preimage_card_envelope (card ?B)) / nnreal size)"
      by (rule wp_ntimes_verifier_query_round_program_any_index_set_bound
          [OF future_query raw_bound subset])
    have base_C:
      "wp_event (ntimes ?prog rounds)
        (query_rounds_any_index_set_hit query_state ?B rounds)
        query_state \<le> nnreal rounds * C"
    proof -
      have "nnreal rounds *
          (nnreal (query_raw_preimage_card_envelope (card ?B)) / nnreal size) \<le>
        nnreal rounds * C"
        by (rule mult_left_mono) (use bound in simp_all)
      then show ?thesis
        by (rule order_trans[OF base])
    qed
    show
      "wp_event
        (ntimes ?prog rounds)
        (query_header_rounds_any_index_set_hit s B) query_state \<le>
        nnreal rounds * C"
    proof (rule order_trans[OF _ base_C])
      show
        "wp_event
          (ntimes ?prog rounds)
          (query_header_rounds_any_index_set_hit s B) query_state \<le>
        wp_event
          (ntimes ?prog rounds)
          (query_rounds_any_index_set_hit query_state ?B rounds) query_state"
      proof (rule wp_event_mono_on_support)
        fix out
        assume out_support:
            "out \<in> set_dist (execute (ntimes ?prog rounds) query_state)"
          and hit: "query_header_rounds_any_index_set_hit s B out"
        from hit obtain fr' f_fri_roots' f_final' as' dg'
            composition_fri_roots' final' rest' where
          header_hit:
            "verifier_header_transcript s fr' f_fri_roots' f_final' as' dg'
              composition_fri_roots' final' rest'"
          and round_hit:
            "query_rounds_any_index_set_hit s
              (B fr' f_fri_roots' f_final' as' dg'
                composition_fri_roots' final')
              rounds out"
          unfolding query_header_rounds_any_index_set_hit_def by blast
        have eqs:
          "fr' = fr \<and>
           f_fri_roots' = map snd f_fl \<and>
           f_final' = f_final \<and>
           as' = as \<and>
           dg' = dg \<and>
           composition_fri_roots' = map snd fl \<and>
           final' = final"
          using verifier_header_transcript_unique[OF header_prefix header_hit]
          by simp
        have round_hit_s:
          "query_rounds_any_index_set_hit s ?B rounds out"
          using round_hit eqs by simp
        show
          "query_rounds_any_index_set_hit query_state ?B rounds out"
          using round_hit_s counter_query
          unfolding query_rounds_any_index_set_hit_def by auto
      qed
    qed
  qed
qed

lemma wp_query_index_round_set_hit_bound_via_supported_header_union:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and union_bound:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots final.
        nnreal
          (query_raw_preimage_card_envelope
            (card
              (query_header_supported_union_good_sets s good_sets fr
                f_fri_roots f_final as dg composition_fri_roots final))) /
          nnreal size \<le> query_error_bound"
  shows
    "wp_event verify_monad (query_index_round_set_hit s good_sets) s \<le>
      nnreal rounds * query_error_bound"
proof -
  have header_bound:
    "wp_event verify_monad
      (query_header_rounds_any_index_set_hit s
        (query_header_supported_union_good_sets s good_sets)) s \<le>
      nnreal rounds * query_error_bound"
    by (rule wp_verify_monad_query_header_rounds_any_index_set_bound
        [OF future raw_bound])
      (use query_header_supported_union_good_sets_subset union_bound in
        simp_all)
  have "wp_event verify_monad (query_index_round_set_hit s good_sets) s \<le>
      wp_event verify_monad
        (query_header_rounds_any_index_set_hit s
          (query_header_supported_union_good_sets s good_sets)) s"
    by (rule wp_event_mono_on_support)
      (rule query_index_round_set_hit_imp_query_header_supported_rounds_hit)
  also have "... \<le> nnreal rounds * query_error_bound"
    by (rule header_bound)
  finally show ?thesis .
qed

lemma verifier_initial_query_rounds_any_index_set_error_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and envelope:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event verify_monad
      (query_rounds_any_index_set_hit (verifier_initial_state tr) B rounds)
      (verifier_initial_state tr) \<le>
      nnreal rounds * query_error_bound"
  by (rule wp_verify_monad_query_rounds_any_index_set_query_error_bound
      [OF verifier_initial_query_future_fresh raw_bound subset envelope])

definition query_index_freshness_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "query_index_freshness_assumption s \<longleftrightarrow>
      (\<forall>good_sets.
        (\<forall>trace_table composition_table as.
          good_sets trace_table composition_table as \<subseteq> query_sample_space) \<longrightarrow>
        (\<forall>trace_table composition_table as.
          nnreal
            (query_raw_preimage_card_envelope
              (card (good_sets trace_table composition_table as))) /
            nnreal size \<le> query_error_bound) \<longrightarrow>
        wp_event verify_monad (query_index_set_hit s good_sets) s \<le>
          nnreal rounds * query_error_bound)"

definition query_index_round_freshness_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "query_index_round_freshness_assumption s \<longleftrightarrow>
      (\<forall>good_sets.
        (\<forall>trace_table composition_table as.
          good_sets trace_table composition_table as \<subseteq> query_sample_space) \<longrightarrow>
        (\<forall>trace_table composition_table as.
          nnreal
            (query_raw_preimage_card_envelope
              (card (good_sets trace_table composition_table as))) /
            nnreal size \<le> query_error_bound) \<longrightarrow>
        wp_event verify_monad (query_index_round_set_hit s good_sets) s \<le>
          nnreal rounds * query_error_bound)"

lemma query_index_freshness_from_round_freshness:
  assumes fresh_round: "query_index_round_freshness_assumption s"
  shows "query_index_freshness_assumption s"
  unfolding query_index_freshness_assumption_def
proof (intro allI impI)
  fix good_sets :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
  assume subset:
      "\<forall>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and frac:
      "\<forall>trace_table composition_table as.
        nnreal
          (query_raw_preimage_card_envelope
            (card (good_sets trace_table composition_table as))) /
          nnreal size \<le> query_error_bound"
  have "wp_event verify_monad (query_index_set_hit s good_sets) s \<le>
      wp_event verify_monad (query_index_round_set_hit s good_sets) s"
    by (rule wp_event_mono) (rule query_index_set_hit_imp_round_set_hit)
  also have "... \<le> nnreal rounds * query_error_bound"
    using fresh_round subset frac
    unfolding query_index_round_freshness_assumption_def by blast
  finally show "wp_event verify_monad (query_index_set_hit s good_sets) s \<le>
      nnreal rounds * query_error_bound" .
qed

lemma query_index_round_freshness_if_no_query_supported_pairwise_merkle_bad:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and no_bad: "\<not> query_supported_pairwise_merkle_bad s"
  shows "query_index_round_freshness_assumption s"
  unfolding query_index_round_freshness_assumption_def
proof (intro allI impI)
  fix good_sets :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
  assume subset:
      "\<forall>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and bounded:
      "\<forall>trace_table composition_table as.
        nnreal
          (query_raw_preimage_card_envelope
            (card (good_sets trace_table composition_table as))) /
          nnreal size \<le> query_error_bound"
  have union_bound:
    "\<And>fr f_fri_roots f_final as dg composition_fri_roots final.
      nnreal
        (query_raw_preimage_card_envelope
          (card
            (query_header_supported_union_good_sets s good_sets fr f_fri_roots
              f_final as dg composition_fri_roots final))) /
      nnreal size \<le> query_error_bound"
    by (rule
        query_header_supported_union_good_sets_fraction_bound_if_no_global_pairwise_merkle_bad
        [OF no_bad])
      (use subset bounded in blast)+
  show "wp_event verify_monad (query_index_round_set_hit s good_sets) s \<le>
      nnreal rounds * query_error_bound"
    by (rule wp_query_index_round_set_hit_bound_via_supported_header_union
        [OF future raw_bound union_bound])
qed

lemma query_index_freshness_if_no_query_supported_pairwise_merkle_bad:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and no_bad: "\<not> query_supported_pairwise_merkle_bad s"
  shows "query_index_freshness_assumption s"
  by (rule query_index_freshness_from_round_freshness)
    (rule query_index_round_freshness_if_no_query_supported_pairwise_merkle_bad
      [OF future raw_bound no_bad])

lemma verifier_initial_query_index_freshness_if_no_query_supported_pairwise_merkle_bad:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and no_bad:
      "\<not> query_supported_pairwise_merkle_bad (verifier_initial_state tr)"
  shows "query_index_freshness_assumption (verifier_initial_state tr)"
  by (rule query_index_freshness_if_no_query_supported_pairwise_merkle_bad)
    (use raw_bound no_bad in simp_all)


lemma query_index_freshness_rounds_zero_obstruction:
  assumes rounds_zero: "rounds = 0"
    and outcome: "out \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
  shows "\<not> query_index_freshness_assumption s"
proof
  assume fresh: "query_index_freshness_assumption s"
  let ?good_sets = "\<lambda>_ _ _. {}"
  have hit: "query_index_set_hit s ?good_sets out"
    by (rule query_index_set_hit_vacuous_if_rounds_zero
        [OF rounds_zero bound])
  have positive:
    "0 < wp_event verify_monad (query_index_set_hit s ?good_sets) s"
    by (rule wp_event_pos_of_support
        [where out=out and m=verify_monad and s=s
          and P="query_index_set_hit s ?good_sets", OF outcome hit])
  have subset:
    "\<And>trace_table composition_table as.
      ?good_sets trace_table composition_table as \<subseteq> query_sample_space"
    by simp
  have envelope:
    "\<And>trace_table composition_table as.
      nnreal
        (query_raw_preimage_card_envelope
          (card (?good_sets trace_table composition_table as))) /
        nnreal size \<le> query_error_bound"
    unfolding query_raw_preimage_card_envelope_def by simp
  have zero_bound:
    "wp_event verify_monad (query_index_set_hit s ?good_sets) s \<le> 0"
    using fresh subset envelope rounds_zero
    unfolding query_index_freshness_assumption_def by simp
  have zero:
    "wp_event verify_monad (query_index_set_hit s ?good_sets) s = 0"
    by (rule antisym[OF zero_bound]) simp
  show False
    using positive zero by simp
qed

lemma query_bad_imp_query_index_set_hit:
  assumes "query_bad s out"
  shows "query_index_set_hit s query_sampling_success_space out"
proof -
  from assms obtain trace_table composition_table as query_idxs
    where bound:
        "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
      and trace_low: "trace_table_low_degree trace_table"
      and composition_low:
        "composition_table_low_degree maxDegree composition_table"
      and not_all:
        "\<not> all_queries_consistent trace_table composition_table as"
    unfolding query_bad_def by blast
  have miss:
    "query_samples_miss_disagreements trace_table composition_table as query_idxs"
    by (rule accepted_with_bound_tables_query_samples_miss_if_not_all_consistent
        [OF bound not_all])
  have success_space:
    "query_sampling_success_space trace_table composition_table as =
      query_agreement_indices trace_table composition_table as"
    using trace_low composition_low not_all
    unfolding query_sampling_success_space_def by simp
  have samples:
    "set query_idxs \<subseteq>
      query_sampling_success_space trace_table composition_table as"
    using miss unfolding query_samples_miss_disagreements_def success_space by simp
  show ?thesis
    unfolding query_index_set_hit_def
    using bound samples by blast
qed

lemma query_bad_imp_query_index_round_set_hit:
  assumes "query_bad s out"
  shows "query_index_round_set_hit s query_sampling_success_space out"
  by (rule query_index_set_hit_imp_round_set_hit)
    (rule query_bad_imp_query_index_set_hit[OF assms])

lemma query_bad_bound_from_phase4B:
  assumes fresh: "query_index_freshness_assumption s"
  shows "wp_event verify_monad (query_bad s) s \<le>
    nnreal rounds * query_error_bound"
proof -
  have hit_bound:
    "wp_event verify_monad
      (query_index_set_hit s query_sampling_success_space) s \<le>
        nnreal rounds * query_error_bound"
    using fresh query_sampling_success_space_subset
      query_sampling_success_space_envelope_fraction_bound
    unfolding query_index_freshness_assumption_def
    by blast
  have "wp_event verify_monad (query_bad s) s \<le>
      wp_event verify_monad
        (query_index_set_hit s query_sampling_success_space) s"
    by (rule wp_event_mono) (rule query_bad_imp_query_index_set_hit)
  also have "... \<le> nnreal rounds * query_error_bound"
    by (rule hit_bound)
  finally show ?thesis .
qed

lemma accepted_bound_trace_low_degree_or_trace_fri_bad:
  assumes bound:
    "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
  shows "trace_table_low_degree trace_table \<or> trace_fri_bad s out"
proof (cases "trace_table_low_degree trace_table")
  case True
  then show ?thesis by simp
next
  case False
  then have "trace_fri_bad s out"
    unfolding trace_fri_bad_def using bound by blast
  then show ?thesis by simp
qed

lemma accepted_bound_composition_low_degree_or_composition_fri_bad:
  assumes bound:
    "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
    and trace_low: "trace_table_low_degree trace_table"
  shows "composition_table_low_degree maxDegree composition_table \<or>
    composition_fri_bad s out"
proof (cases "composition_table_low_degree maxDegree composition_table")
  case True
  then show ?thesis by simp
next
  case False
  then have "composition_fri_bad s out"
    unfolding composition_fri_bad_def using bound trace_low by blast
  then show ?thesis by simp
qed

lemma accepted_bound_all_queries_consistent_or_query_bad:
  assumes bound:
    "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
    and trace_low: "trace_table_low_degree trace_table"
    and composition_low: "composition_table_low_degree maxDegree composition_table"
  shows "all_queries_consistent trace_table composition_table as \<or>
    query_bad s out"
proof (cases "all_queries_consistent trace_table composition_table as")
  case True
  then show ?thesis by simp
next
  case False
  then have "query_bad s out"
    unfolding query_bad_def using bound trace_low composition_low by blast
  then show ?thesis by simp
qed

lemma accepted_bound_composition_bad_if_globally_consistent:
  assumes false_statement: "\<not> exists_valid_trace"
    and bound:
      "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
    and trace_low: "trace_table_low_degree trace_table"
    and composition_low: "composition_table_low_degree maxDegree composition_table"
    and all_queries: "all_queries_consistent trace_table composition_table as"
  shows "composition_bad s out"
proof -
  from trace_low obtain f where
    deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    unfolding trace_table_low_degree_def by blast
  have violated: "violated_constraints f \<noteq> {}"
    by (rule false_statement_violated_constraints[OF false_statement deg_f])
  have len_as: "length as = length spec"
    using accepted_with_tables_shapes(3)
      [OF accepted_with_bound_tables_imp_accepted_with_tables[OF bound]]
    by simp
  have hide_if_bounds:
    "common_denominator_degree_bounds f as \<Longrightarrow>
      random_combination_common_denominator_hides_violations f as"
    by (rule random_combination_common_denominator_hides_from_queries
        [OF len_as false_statement deg_f trace_table composition_low all_queries])
  show ?thesis
    unfolding composition_bad_def composition_degree_bad_def
      composition_randomization_bad_def composition_bad_context_def
    using bound deg_f trace_table violated composition_low all_queries hide_if_bounds
    by blast
qed

lemma accepted_bound_table_partition:
  assumes false_statement: "\<not> exists_valid_trace"
    and bound:
      "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
  shows
    "composition_bad s out \<or> trace_fri_bad s out \<or>
      composition_fri_bad s out \<or> query_bad s out"
proof -
  from accepted_bound_trace_low_degree_or_trace_fri_bad[OF bound]
  consider
      (trace_low) "trace_table_low_degree trace_table"
    | (trace_bad) "trace_fri_bad s out"
    by blast
  then show ?thesis
  proof cases
    case trace_bad
    then show ?thesis by blast
  next
    case trace_low
    from accepted_bound_composition_low_degree_or_composition_fri_bad
      [OF bound trace_low]
    consider
        (composition_low) "composition_table_low_degree maxDegree composition_table"
      | (composition_bad) "composition_fri_bad s out"
      by blast
    then show ?thesis
    proof cases
      case composition_bad
      then show ?thesis by blast
    next
      case composition_low
      from accepted_bound_all_queries_consistent_or_query_bad
        [OF bound trace_low composition_low]
      consider
          (all_queries) "all_queries_consistent trace_table composition_table as"
        | (query_bad) "query_bad s out"
        by blast
      then show ?thesis
      proof cases
        case query_bad
        then show ?thesis by blast
      next
        case all_queries
        have "composition_bad s out"
          by (rule accepted_bound_composition_bad_if_globally_consistent
              [OF false_statement bound trace_low composition_low all_queries])
        then show ?thesis by blast
      qed
    qed
  qed
qed

lemma composition_randomization_bad_imp_alpha_bad_set_hit:
  assumes bad: "composition_randomization_bad s out"
  shows "alpha_bad_set_hit s composition_trace_bad_alpha_space out"
proof -
  from bad obtain trace_table composition_table as query_idxs f where
    ctx:
      "composition_bad_context s out trace_table composition_table as query_idxs f"
    and bounds: "common_denominator_degree_bounds f as"
    and hides: "random_combination_common_denominator_hides_violations f as"
    unfolding composition_randomization_bad_def by blast
  have bound:
    "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
    using ctx unfolding composition_bad_context_def by blast
  have deg_f: "degree f < clength"
    using ctx unfolding composition_bad_context_def by blast
  have trace_table: "trace_table = map (poly f) eval_domain"
    using ctx unfolding composition_bad_context_def by blast
  have violated: "violated_constraints f \<noteq> {}"
    using ctx unfolding composition_bad_context_def by blast
  have len_as: "length as = length spec"
    using accepted_with_tables_shapes(3)
      [OF accepted_with_bound_tables_imp_accepted_with_tables[OF bound]] .
  have as_in:
    "as \<in> common_denominator_hiding_alpha_space f"
    using len_as hides
    unfolding common_denominator_hiding_alpha_space_def alpha_space_def
    by simp
  have witness_eq: "low_degree_trace_witness trace_table = f"
    by (rule low_degree_trace_witness_eq[OF deg_f trace_table])
  have "as \<in> composition_trace_bad_alpha_space trace_table"
    using deg_f trace_table violated bounds as_in
    unfolding composition_trace_bad_alpha_space_def witness_eq
    by simp
  then show ?thesis
    using bound unfolding alpha_bad_set_hit_def by blast
qed

lemma composition_randomization_bad_bound_from_alpha_freshness:
  assumes fresh: "alpha_challenge_freshness_assumption s"
  shows "wp_event verify_monad (composition_randomization_bad s) s \<le>
    composition_error_bound"
proof -
  have hit_bound:
    "wp_event verify_monad
      (alpha_bad_set_hit s composition_trace_bad_alpha_space) s \<le>
        composition_error_bound"
    using fresh composition_trace_bad_alpha_space_subset_alpha_space
      composition_trace_bad_alpha_space_fraction_bound_alpha_space
    unfolding alpha_challenge_freshness_assumption_def
    by blast
  have "wp_event verify_monad (composition_randomization_bad s) s \<le>
      wp_event verify_monad
        (alpha_bad_set_hit s composition_trace_bad_alpha_space) s"
    by (rule wp_event_mono)
      (rule composition_randomization_bad_imp_alpha_bad_set_hit)
  also have "... \<le> composition_error_bound"
    by (rule hit_bound)
  finally show ?thesis .
qed

lemma composition_randomization_bad_bound_via_header_union:
  assumes future: "alpha_future_fresh s"
    and union_bound:
      "\<And>fr f_fri_roots f_final.
        nnreal
          (card
            (alpha_header_union_bad_sets s
              composition_trace_bad_alpha_space fr f_fri_roots f_final)) /
          nnreal (card alpha_space) \<le> composition_error_bound"
  shows "wp_event verify_monad (composition_randomization_bad s) s \<le>
    composition_error_bound"
proof -
  have hit_bound:
    "wp_event verify_monad
      (alpha_bad_set_hit s composition_trace_bad_alpha_space) s \<le>
        composition_error_bound"
    by (rule wp_alpha_bad_set_hit_bound_via_header_union[OF future])
      (use composition_trace_bad_alpha_space_subset_alpha_space union_bound in
        simp_all)
  have "wp_event verify_monad (composition_randomization_bad s) s \<le>
      wp_event verify_monad
        (alpha_bad_set_hit s composition_trace_bad_alpha_space) s"
    by (rule wp_event_mono)
      (rule composition_randomization_bad_imp_alpha_bad_set_hit)
  also have "... \<le> composition_error_bound"
    by (rule hit_bound)
  finally show ?thesis .
qed

lemma composition_randomization_bad_bound_via_supported_header_union:
  assumes future: "alpha_future_fresh s"
    and union_bound:
      "\<And>fr f_fri_roots f_final.
        nnreal
          (card
            (alpha_header_supported_union_bad_sets s
              composition_trace_bad_alpha_space fr f_fri_roots f_final)) /
          nnreal (card alpha_space) \<le> composition_error_bound"
  shows "wp_event verify_monad (composition_randomization_bad s) s \<le>
    composition_error_bound"
proof -
  have hit_bound:
    "wp_event verify_monad
      (alpha_bad_set_hit s composition_trace_bad_alpha_space) s \<le>
        composition_error_bound"
    by (rule wp_alpha_bad_set_hit_bound_via_supported_header_union[OF future])
      (use composition_trace_bad_alpha_space_subset_alpha_space union_bound in
        simp_all)
  have "wp_event verify_monad (composition_randomization_bad s) s \<le>
      wp_event verify_monad
        (alpha_bad_set_hit s composition_trace_bad_alpha_space) s"
    by (rule wp_event_mono)
      (rule composition_randomization_bad_imp_alpha_bad_set_hit)
  also have "... \<le> composition_error_bound"
    by (rule hit_bound)
  finally show ?thesis .
qed

lemma composition_randomization_bad_bound_if_alpha_header_candidate_unique:
  assumes future: "alpha_future_fresh s"
    and unique:
      "\<And>fr f_fri_roots f_final.
        \<exists>trace_table.
          alpha_header_trace_table_candidates s fr f_fri_roots f_final \<subseteq>
            {trace_table}"
  shows "wp_event verify_monad (composition_randomization_bad s) s \<le>
    composition_error_bound"
  by (rule composition_randomization_bad_bound_via_header_union[OF future])
    (rule composition_trace_alpha_header_union_fraction_bound_if_unique_candidate
      [OF unique])

lemma composition_randomization_bad_bound_if_alpha_header_supported_candidate_unique:
  assumes future: "alpha_future_fresh s"
    and unique:
      "\<And>fr f_fri_roots f_final.
        \<exists>trace_table.
          alpha_header_supported_trace_table_candidates s fr f_fri_roots
            f_final \<subseteq> {trace_table}"
  shows "wp_event verify_monad (composition_randomization_bad s) s \<le>
    composition_error_bound"
  by (rule composition_randomization_bad_bound_via_supported_header_union
      [OF future])
    (rule
      composition_trace_alpha_header_supported_union_fraction_bound_if_unique_candidate
      [OF unique])

lemma composition_randomization_bad_bound_if_no_alpha_supported_pairwise_merkle_bad:
  assumes future: "alpha_future_fresh s"
    and no_bad: "\<not> alpha_supported_pairwise_merkle_bad s"
  shows "wp_event verify_monad (composition_randomization_bad s) s \<le>
    composition_error_bound"
proof (rule composition_randomization_bad_bound_if_alpha_header_supported_candidate_unique
    [OF future])
  fix fr f_fri_roots f_final
  show
    "\<exists>trace_table.
      alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final
        \<subseteq> {trace_table}"
    by (rule alpha_header_supported_candidate_unique_if_no_global_pairwise_merkle_bad
        [OF no_bad])
qed

lemma composition_degree_bad_false:
  assumes wf: "spec_degree_wellformed"
  shows "\<not> composition_degree_bad s out"
  using common_denominator_degree_bounds_from_spec_degree_wellformed[OF wf]
  unfolding composition_degree_bad_def composition_bad_context_def
  by blast

lemma composition_degree_bad_bound:
  assumes wf: "spec_degree_wellformed"
  shows "wp_event verify_monad (composition_degree_bad s) s \<le> 0"
proof -
  have "composition_degree_bad s =
      (\<lambda>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option. False)"
    by (rule ext) (simp add: composition_degree_bad_false[OF wf])
  then show ?thesis
    unfolding wp_event_def wp_def dist_expect_def by simp
qed

lemma composition_bad_bound_from_phase4A:
  assumes wf: "spec_degree_wellformed"
    and alpha_fresh: "alpha_challenge_freshness_assumption s"
  shows "wp_event verify_monad (composition_bad s) s \<le> composition_error_bound"
proof -
  have degree_bound:
    "wp_event verify_monad (composition_degree_bad s) s \<le> 0"
    by (rule composition_degree_bad_bound[OF wf])
  have randomization_bound:
    "wp_event verify_monad (composition_randomization_bad s) s \<le>
      composition_error_bound"
    by (rule composition_randomization_bad_bound_from_alpha_freshness[OF alpha_fresh])
  have "wp_event verify_monad (composition_bad s) s =
      wp_event verify_monad
        (\<lambda>out. composition_degree_bad s out \<or>
          composition_randomization_bad s out) s"
    unfolding composition_bad_def by simp
  also have "... \<le>
      wp_event verify_monad (composition_degree_bad s) s +
      wp_event verify_monad (composition_randomization_bad s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> 0 + composition_error_bound"
    by (intro add_mono degree_bound randomization_bound)
  finally show ?thesis by simp
qed

end

end
