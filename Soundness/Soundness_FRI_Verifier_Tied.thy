(*  Title:      Stark/Soundness_FRI_Verifier_Tied.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Verifier_Tied
  imports
    Soundness_FRI_Zero_Round_Target
    Soundness_Query_Transcript_Openings
begin

text \<open>
  Verifier-tied FRI partial-candidate events.

  Broad reachable partial-candidate events allow the candidate table to be
  compatible with sampled authenticated openings whose indices are not tied to
  the FRI opening transcript.  This theory introduces narrower internal events
  where the candidate openings use the same query indices as the verifier's FRI
  transcript.  The protocol and public soundness statement are unchanged.
\<close>

context soundness
begin

lemma partial_authenticated_tables_values_unique_if_clean:
  assumes table:
      "partial_authenticated_table rt len openings s"
    and table':
      "partial_authenticated_table rt len openings' s"
    and clean: "\<not> hash_map_output_collision s"
    and first: "opening \<in> set openings"
    and second: "opening' \<in> set openings'"
    and same_index: "opening_index opening = opening_index opening'"
  shows "opening_value opening = opening_value opening'"
proof -
  have combined:
    "partial_authenticated_table rt len (openings @ openings') s"
    using table table'
    unfolding partial_authenticated_table_def by auto
  show ?thesis
    by (rule partial_authenticated_table_values_unique_if_clean[
        OF combined clean])
      (use first second same_index in auto)
qed

lemma verifier_query_round_after_index_zero_trace_final_opening:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes empty_trace: "f_fl = []"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
  obtains idx openings where
    "idx = index (to_nat raw)"
    and "map opening_index openings = powers_scaled idx"
    and "partial_authenticated_table fr (scale * clength) openings t"
    and "opening_value (hd openings) = f_final"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist
          (execute
            (mfold (?idx, hd fv, clength * scale, 1)
              (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have trace_out:
    "f_out = (?idx, hd fv, clength * scale, 1)"
    and s2_eq: "s2 = s1"
    using trace_fri empty_trace
    unfolding receive_query_commits_def by simp_all
  have hd_fv: "hd fv = f_final"
    using assert_trace unfolding assert_def trace_out
    by (cases "hd fv = f_final") (auto simp: throw_no_outcome)
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def trace_out hd_fv by simp
  have idx_in: "?idx \<in> query_sample_space"
    using index_less_query_sample_space
    unfolding query_sample_space_def by simp
  from check_decommit_on_query_authenticated_openings
      [OF idx_in query_decommit]
  obtain openings where len_openings:
      "length openings = length (powers_scaled ?idx)"
    and values_openings: "map opening_value openings = fv"
    and idx_openings: "map opening_index openings = powers_scaled ?idx"
    and table_s1:
      "partial_authenticated_table fr (scale * clength) openings s1"
    by blast
  from receive_query_commits_layers_outcome[OF comp_fri]
  obtain comp_layer_chunks comp_fri_chunk where s3_s4: "s3 \<le> s4"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  have s1_t: "s1 \<le> t"
    using s3_s4 unfolding s3_eq s2_eq t_eq .
  have table_t:
    "partial_authenticated_table fr (scale * clength) openings t"
    by (rule partial_authenticated_table_mono[OF table_s1 s1_t])
  have openings_nonempty: "openings \<noteq> []"
    using len_openings powers_pos unfolding powers_scaled_def by auto
  have hd_value: "opening_value (hd openings) = hd fv"
    using values_openings openings_nonempty
    by (cases openings; cases fv) simp_all
  show ?thesis
    by (rule that[OF refl idx_openings table_t])
      (simp add: hd_value hd_fv)
qed

lemma verifier_query_round_program_zero_trace_final_opening:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes empty_trace: "f_fl = []"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  shows "\<exists>raw idx openings.
    idx = index (to_nat raw) \<and>
    map opening_index openings = powers_scaled idx \<and>
    partial_authenticated_table fr (scale * clength) openings t \<and>
    opening_value (hd openings) = f_final"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and after:
      "Some ((), t) \<in>
        set_dist
          (execute
              (verifier_query_round_after_index_program
                fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  from verifier_query_round_after_index_zero_trace_final_opening
      [OF empty_trace after]
  show ?thesis
    by blast
qed

lemma trace_zero_round_checked_candidate_from_verified_openings_if_no_merkle:
  fixes final_state :: "('f, 'a) protocol_channel_scheme"
  assumes partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and no_merkle:
      "\<not> partial_merkle_inconsistency_bad s (Some (result, final_state))"
    and query_sample:
      "\<And>idx. idx \<in> set query_idxs \<Longrightarrow> idx \<in> query_sample_space"
    and verifier_openings:
      "\<And>i. i < rounds \<Longrightarrow>
        \<exists>openings.
          map opening_index openings = powers_scaled (query_idxs ! i) \<and>
          partial_authenticated_table fr (scale * clength) openings
            final_state \<and>
          opening_value (hd openings) = final"
  shows
    "trace_zero_round_final_checked_candidate s
      (Some (result, final_state)) fr query_idxs trace_openings
      trace_table final"
proof -
  have final_values:
    "\<And>i. i < rounds \<Longrightarrow>
      opening_value (hd (trace_openings ! i)) = final"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have candidate_indices:
      "map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
      by (rule accepted_with_partial_trace_openings_shapes(3)
          [OF partial i_bound])
    have candidate_table:
      "partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
      using partial i_bound
      unfolding accepted_with_partial_trace_openings_def by blast
    from verifier_openings[OF i_bound]
    obtain openings where verified_indices:
        "map opening_index openings = powers_scaled (query_idxs ! i)"
      and verified_table:
        "partial_authenticated_table fr (scale * clength) openings
          final_state"
      and verified_value: "opening_value (hd openings) = final"
      by blast
    have candidate_nonempty: "trace_openings ! i \<noteq> []"
    proof -
      have "map opening_index (trace_openings ! i) \<noteq> []"
        using candidate_indices powers_pos unfolding powers_scaled_def by simp
      then show ?thesis by auto
    qed
    have verified_nonempty: "openings \<noteq> []"
    proof -
      have "map opening_index openings \<noteq> []"
        using verified_indices powers_pos unfolding powers_scaled_def by simp
      then show ?thesis by auto
    qed
    let ?candidate = "hd (trace_openings ! i)"
    let ?verified = "hd openings"
    have candidate_in: "?candidate \<in> set (trace_openings ! i)"
      using candidate_nonempty by simp
    have verified_in: "?verified \<in> set openings"
      using verified_nonempty by simp
    have same_index:
      "opening_index ?candidate = opening_index ?verified"
    proof -
      have "opening_index ?candidate =
          hd (map opening_index (trace_openings ! i))"
        using candidate_nonempty by (cases "trace_openings ! i") auto
      also have "... = hd (powers_scaled (query_idxs ! i))"
        using candidate_indices by simp
      also have "... = hd (map opening_index openings)"
        using verified_indices by simp
      also have "... = opening_index ?verified"
        using verified_nonempty by (cases openings) auto
      finally show ?thesis .
    qed
    have candidate_auth:
      "authenticated_opening_in final_state ?candidate"
      using candidate_table candidate_in
      unfolding partial_authenticated_table_def by blast
    have verified_auth:
      "authenticated_opening_in final_state ?verified"
      using verified_table verified_in
      unfolding partial_authenticated_table_def by blast
    have same_root:
      "opening_root ?candidate = opening_root ?verified"
      using candidate_table verified_table candidate_in verified_in
      unfolding partial_authenticated_table_def by auto
    have same_length:
      "opening_length ?candidate = opening_length ?verified"
      using candidate_table verified_table candidate_in verified_in
      unfolding partial_authenticated_table_def by auto
    show "opening_value ?candidate = final"
    proof (rule ccontr)
      assume neq_final: "opening_value ?candidate \<noteq> final"
      have diff:
        "opening_value ?candidate \<noteq> opening_value ?verified"
        using neq_final verified_value by simp
      have "partial_merkle_inconsistency_bad s
          (Some (result, final_state))"
        unfolding partial_merkle_inconsistency_bad_def
        by (intro conjI exI)
          (use partial candidate_auth verified_auth same_root same_length
            same_index diff in
            \<open>auto simp: accepted_with_partial_trace_openings_def\<close>)
      then show False
        using no_merkle by contradiction
    qed
  qed
  show ?thesis
    unfolding trace_zero_round_final_checked_candidate_def
    using partial candidate query_sample final_values by blast
qed

definition trace_fri_bad_with_verifier_tied_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_verifier_tied_partial_candidate s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table)"

definition trace_fri_bad_with_header_tied_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_header_tied_partial_candidate s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table)"

lemma trace_fri_bad_with_header_tied_imp_verifier_tied:
  assumes "trace_fri_bad_with_header_tied_partial_candidate s out"
  shows "trace_fri_bad_with_verifier_tied_partial_candidate s out"
  using assms
  unfolding trace_fri_bad_with_header_tied_partial_candidate_def
    trace_fri_bad_with_verifier_tied_partial_candidate_def
  by blast

lemma accepted_fri_opening_transcript_query_idx_in_sample_space:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      query_idxs trace_round_layers composition_round_layers"
    and idx_in: "idx \<in> set query_idxs"
  shows "idx \<in> query_sample_space"
  using fri_openings idx_in index_less_query_sample_space
  unfolding accepted_fri_opening_transcript_def query_sample_space_def by auto

definition trace_fri_header_tied_zero_round_final_obstruction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_zero_round_final_obstruction s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      length trace_bs = 0 \<and>
      \<not> fri_final_constant_consistent trace_table trace_final)"

lemma trace_fri_header_tied_zero_round_final_obstruction_imp_checked_or_merkle:
  assumes obstruction:
    "trace_fri_header_tied_zero_round_final_obstruction s out"
  shows
    "trace_fri_zero_round_checked_final_obstruction s out \<or>
     partial_merkle_inconsistency_bad s out"
proof -
  from obstruction obtain trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and zero_rounds: "length trace_bs = 0"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
    unfolding trace_fri_header_tied_zero_round_final_obstruction_def
    by blast
  from fri_openings obtain result final_state fr0 f_fl as0 fl query_state
      raw_idxs query_chunks where out_eq:
      "out = Some (result, final_state)"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and trace_bs_eq: "trace_bs = map fst f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and composition_bs_eq: "composition_bs = map fst fl"
    and header0:
      "verifier_header_transcript s fr0 trace_roots trace_final as0 dg
        composition_roots composition_final (PTranscript query_state)"
    and query_state_eq:
      "PState query_state =
        verifier_header_state s fr0 trace_roots trace_final as0 dg
          composition_roots composition_final"
    and query_counter_eq:
      "PQueryCounter query_state = PQueryCounter s"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr0 f_fl trace_final as0 fl
                composition_final)
              rounds)
            query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "fri_query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (fri_query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    unfolding accepted_fri_opening_transcript_def by blast
  have f_fl_empty: "f_fl = []"
    using zero_rounds trace_bs_eq by simp
  have trace_roots_empty: "trace_roots = []"
    using trace_roots_eq f_fl_empty by simp
  have header_eqs:
    "fr0 = fr \<and>
     as0 = as \<and>
     PTranscript query_state = rest"
    using verifier_header_transcript_unique[OF header0 header] by simp
  have query_out_empty:
    "Some (result, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr [] trace_final as fl
              composition_final)
            rounds)
          query_state)"
    using query_out f_fl_empty header_eqs by simp
  have query_chunk_empty:
    "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (fri_query_idxs ! i)
        [] (map snd fl) (query_chunks ! i)"
    using query_chunk trace_roots_empty composition_roots_eq by simp
  show ?thesis
  proof (cases "partial_merkle_inconsistency_bad s out")
    case True
    then show ?thesis by simp
  next
    case False
    have no_merkle:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
      using False out_eq by simp
    have verifier_openings:
      "\<And>i. i < rounds \<Longrightarrow>
        \<exists>openings.
          map opening_index openings =
            powers_scaled (fri_query_idxs ! i) \<and>
          partial_authenticated_table fr (scale * clength) openings
            final_state \<and>
          opening_value (hd openings) = trace_final"
    proof -
      fix i
      assume i_bound: "i < rounds"
      show
        "\<exists>openings.
          map opening_index openings =
            powers_scaled (fri_query_idxs ! i) \<and>
          partial_authenticated_table fr (scale * clength) openings
            final_state \<and>
          opening_value (hd openings) = trace_final"
      proof (rule
          ntimes_verifier_query_rounds_selected_zero_trace_final_opening_at
          [OF query_out_empty i_bound len_raw query_idxs_eq len_query_chunks
            transcript_query query_chunk_empty replay_lookup])
        fix verified_openings
        assume
          "map opening_index verified_openings =
            powers_scaled (fri_query_idxs ! i)"
          "partial_authenticated_table fr (scale * clength)
            verified_openings final_state"
          "opening_value (hd verified_openings) = trace_final"
        then show
          "\<exists>openings.
            map opening_index openings =
              powers_scaled (fri_query_idxs ! i) \<and>
            partial_authenticated_table fr (scale * clength) openings
              final_state \<and>
            opening_value (hd openings) = trace_final"
          by blast
      qed
    qed
    have query_sample:
      "\<And>idx. idx \<in> set fri_query_idxs \<Longrightarrow> idx \<in> query_sample_space"
      by (rule accepted_fri_opening_transcript_query_idx_in_sample_space
          [OF fri_openings])
    have partial_some:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr fri_query_idxs trace_openings"
      using partial out_eq by simp
    have checked:
      "trace_zero_round_final_checked_candidate s
        (Some (result, final_state)) fr fri_query_idxs trace_openings
        trace_table trace_final"
      by (rule trace_zero_round_checked_candidate_from_verified_openings_if_no_merkle
          [OF partial_some candidate no_merkle query_sample verifier_openings])
    have "trace_fri_zero_round_checked_final_obstruction s out"
      unfolding trace_fri_zero_round_checked_final_obstruction_def out_eq
      by (intro exI conjI)
        (use fri_openings[unfolded out_eq] zero_rounds checked not_final
          in simp_all)
    then show ?thesis by simp
  qed
qed

definition composition_fri_bad_with_verifier_tied_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_bad_with_verifier_tied_partial_candidate s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table)"

definition trace_fri_bad_with_verifier_tied_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_verifier_tied_sampled_layer_chain s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table doms layers.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers)"

definition composition_fri_bad_with_verifier_tied_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_bad_with_verifier_tied_sampled_layer_chain s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table doms layers.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers)"

definition trace_fri_verifier_tied_missing_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_verifier_tied_missing_sampled_layer_chain s out \<longleftrightarrow>
    trace_fri_bad_with_verifier_tied_partial_candidate s out \<and>
    \<not> trace_fri_bad_with_verifier_tied_sampled_layer_chain s out"

definition composition_fri_verifier_tied_missing_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_missing_sampled_layer_chain s out
    \<longleftrightarrow>
    composition_fri_bad_with_verifier_tied_partial_candidate s out \<and>
    \<not> composition_fri_bad_with_verifier_tied_sampled_layer_chain s out"

definition trace_fri_verifier_tied_reduction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "trace_fri_verifier_tied_reduction s \<longleftrightarrow>
    wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_partial_candidate s) s \<le>
      trace_fri_error"

definition composition_fri_verifier_tied_reduction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_reduction s \<longleftrightarrow>
    wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s \<le>
      composition_fri_error"

definition soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
      s out \<longleftrightarrow>
    composition_bad_with_partial_candidates s out \<or>
    trace_fri_bad_with_header_tied_partial_candidate s out \<or>
    composition_fri_bad_with_verifier_tied_partial_candidate s out \<or>
    query_bad_with_aligned_transcript_partial_candidates s out"

definition soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle
      s out \<longleftrightarrow>
    partial_merkle_inconsistency_bad s out \<or>
    soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
      s out"

lemma accepted_fri_opening_transcript_obtains_aligned_partial_openings:
  assumes fri_openings:
    "accepted_fri_opening_transcript s (Some (result, final_state))
      trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final query_idxs trace_round_layers
      composition_round_layers"
    and comp_nonempty: "composition_roots \<noteq> []"
  obtains fr as rest trace_openings composition_openings where
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    "accepted_with_partial_initial_openings_aligned_transcript_consistent s
      (Some (result, final_state)) fr trace_roots trace_final as dg
      composition_roots composition_final query_idxs trace_openings
      composition_openings"
proof -
  from fri_openings obtain result' final_state' fr f_fl as fl query_state
      raw_idxs query_chunks where out_eq:
      "Some (result, final_state) = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and comp_roots_eq: "composition_roots = map snd fl"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final (PTranscript query_state)"
    and query_state_state:
      "PState query_state =
        verifier_header_state s fr trace_roots trace_final as dg
          composition_roots composition_final"
    and query_state_counter:
      "PQueryCounter query_state = PQueryCounter s"
    and query_out:
      "Some (result', final_state') \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl trace_final as fl
                composition_final)
              rounds)
            query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state'"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge
            (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
          Some (raw_idxs ! i)"
    unfolding accepted_fri_opening_transcript_def by blast
  obtain b composition_root fl_tail where fl_eq:
    "fl = (b, composition_root) # fl_tail"
    using comp_nonempty comp_roots_eq by (cases fl) auto
  have f_roots: "map snd f_fl = trace_roots"
    using trace_roots_eq by simp
  have comp_roots: "map snd fl = composition_roots"
    using comp_roots_eq by simp
  have result_eq: "result' = result"
    and final_state_eq: "final_state' = final_state"
    using out_eq by simp_all
  have query_out':
    "Some (result, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl trace_final as fl
              composition_final)
            rounds)
          query_state)"
    using query_out result_eq final_state_eq by simp
  have transcript_query':
    "PTranscript query_state =
      List.concat query_chunks @ PTranscript final_state"
    using transcript_query final_state_eq by simp
  have query_chunk':
    "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (query_idxs ! i)
        (map snd f_fl) (map snd fl) (query_chunks ! i)"
    using query_chunk trace_roots_eq comp_roots_eq by simp
  have replay_lookup':
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge
          (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    using replay_lookup final_state_eq by simp
  from
    query_rounds_replay_accepted_with_partial_initial_openings_aligned_transcript_consistent
      [OF header comp_nonempty fl_eq f_roots comp_roots refl
        query_state_state query_state_counter query_out' len_raw query_idxs_eq
        len_query_chunks transcript_query' query_chunk' replay_lookup']
  obtain trace_openings composition_openings where partial:
    "accepted_with_partial_initial_openings_aligned_transcript_consistent s
      (Some (result, final_state)) fr trace_roots trace_final as dg
      composition_roots composition_final query_idxs trace_openings
      composition_openings"
    by blast
  show ?thesis
    by (rule that[OF header partial])
qed

lemma accepted_fri_opening_transcript_obtains_aligned_partial_candidates_or_partial_merkle:
  assumes fri_openings:
    "accepted_fri_opening_transcript s (Some (result, final_state))
      trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final query_idxs trace_round_layers
      composition_round_layers"
    and comp_nonempty: "composition_roots \<noteq> []"
  shows
    "partial_merkle_inconsistency_bad s (Some (result, final_state)) \<or>
     (\<exists>fr as rest trace_openings composition_openings trace_table
        composition_table.
        verifier_header_transcript s fr trace_roots trace_final as dg
          composition_roots composition_final rest \<and>
        accepted_with_partial_initial_openings_aligned s
          (Some (result, final_state)) fr trace_roots trace_final as dg
          composition_roots composition_final query_idxs trace_openings
          composition_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings)"
proof (cases
    "partial_merkle_inconsistency_bad s (Some (result, final_state))")
  case True
  then show ?thesis by simp
next
  case no_merkle: False
  from accepted_fri_opening_transcript_obtains_aligned_partial_openings
      [OF fri_openings comp_nonempty]
  obtain fr as rest trace_openings composition_openings where header:
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    and partial:
    "accepted_with_partial_initial_openings_aligned_transcript_consistent s
      (Some (result, final_state)) fr trace_roots trace_final as dg
      composition_roots composition_final query_idxs trace_openings
      composition_openings"
    by blast
  have aligned:
    "accepted_with_partial_initial_openings_aligned s
      (Some (result, final_state)) fr trace_roots trace_final as dg
      composition_roots composition_final query_idxs trace_openings
      composition_openings"
    using partial
    by (blast dest:
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        accepted_with_partial_initial_openings_aligned_consistent_imp_aligned)
  obtain trace_table composition_table where trace_candidate:
    "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
    "partial_composition_table_candidate composition_table
      composition_openings"
    using
      accepted_with_partial_initial_openings_aligned_candidates_if_no_partial_merkle_bad
        [OF aligned no_merkle]
    by blast
  show ?thesis
    by (intro disjI2 exI conjI)
      (rule header, rule aligned, rule trace_candidate,
        rule composition_candidate)
qed

lemma accepted_verifier_tied_aligned_transcript_partial_candidate_partition:
  assumes false_statement: "\<not> exists_valid_trace"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final query_idxs trace_round_layers
        composition_round_layers"
    and partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent s
        out fr trace_roots trace_final as fri_dg composition_roots
        composition_final
        query_idxs trace_openings composition_openings"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
  shows
    "soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
      s out"
proof (cases "trace_table_low_degree trace_table")
  case False
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent s out fr
      trace_roots trace_final as fri_dg composition_roots composition_final query_idxs
      trace_openings composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  have aligned0:
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final query_idxs
      trace_openings composition_openings"
    by (rule accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
        [OF aligned])
  have trace_partial:
    "accepted_with_partial_trace_openings s out fr query_idxs
      trace_openings"
    by (rule accepted_with_partial_initial_openings_aligned_shapes(3)
        [OF aligned0])
  have "trace_fri_bad_with_header_tied_partial_candidate s out"
    unfolding trace_fri_bad_with_header_tied_partial_candidate_def
    by (intro exI conjI)
      (rule fri_openings, rule header, rule trace_partial,
        rule trace_candidate, rule False)
  then show ?thesis
    unfolding
      soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_def
    by blast
next
  case True
  note trace_low = True
  show ?thesis
  proof (cases "composition_table_low_degree maxDegree composition_table")
    case False
    have aligned:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        trace_roots trace_final as fri_dg composition_roots composition_final query_idxs
        trace_openings composition_openings"
      by (rule
          accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
          [OF partial])
    have aligned0:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final query_idxs
        trace_openings composition_openings"
      by (rule
          accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
          [OF aligned])
    have "composition_fri_bad_with_verifier_tied_partial_candidate s out"
      unfolding composition_fri_bad_with_verifier_tied_partial_candidate_def
      by (intro exI conjI)
        (rule fri_openings, rule aligned0, rule trace_candidate,
          rule composition_candidate, rule trace_low, rule False)
    then show ?thesis
      unfolding
        soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_def
      by blast
  next
    case True
    note composition_low = True
    show ?thesis
    proof (cases "all_queries_consistent trace_table composition_table as")
      case False
      have "query_bad_with_aligned_transcript_partial_candidates s out"
        unfolding query_bad_with_aligned_transcript_partial_candidates_def
        using partial trace_candidate composition_candidate trace_low
          composition_low False
        by blast
      then show ?thesis
        unfolding
          soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_def
        by blast
    next
      case True
      note all_queries = True
      from trace_low obtain f where
        deg_f: "degree f < clength"
        and trace_table_eq: "trace_table = map (poly f) eval_domain"
        unfolding trace_table_low_degree_def by blast
      have violated: "violated_constraints f \<noteq> {}"
        by (rule false_statement_violated_constraints
            [OF false_statement deg_f])
      have aligned:
        "accepted_with_partial_initial_openings_aligned_consistent s out fr
          trace_roots trace_final as fri_dg composition_roots composition_final query_idxs
          trace_openings composition_openings"
        by (rule
            accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
            [OF partial])
      have "composition_bad_with_partial_candidates s out"
        unfolding composition_bad_with_partial_candidates_def
        using accepted_with_partial_initial_openings_aligned_consistent_imp_unaligned
            [OF aligned]
          trace_candidate composition_candidate deg_f trace_table_eq
          violated composition_low all_queries
        by blast
      then show ?thesis
        unfolding
          soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_def
        by blast
    qed
  qed
qed

lemma accepted_fri_opening_transcript_verifier_tied_partition_with_partial_merkle:
  assumes false_statement: "\<not> exists_valid_trace"
    and fri_openings:
      "accepted_fri_opening_transcript s (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final query_idxs trace_round_layers
        composition_round_layers"
    and comp_nonempty: "composition_roots \<noteq> []"
  shows
    "soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle
      s (Some (result, final_state))"
proof -
  from accepted_fri_opening_transcript_obtains_aligned_partial_openings
      [OF fri_openings comp_nonempty]
  obtain fr as rest trace_openings composition_openings where header:
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    and partial:
    "accepted_with_partial_initial_openings_aligned_transcript_consistent s
      (Some (result, final_state)) fr trace_roots trace_final as dg
      composition_roots composition_final query_idxs trace_openings
      composition_openings"
    by blast
  show ?thesis
  proof (cases
      "partial_merkle_inconsistency_bad s (Some (result, final_state))")
    case True
    then show ?thesis
      unfolding
        soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle_def
      by simp
  next
    case False
    have aligned:
      "accepted_with_partial_initial_openings_aligned s
        (Some (result, final_state)) fr trace_roots trace_final as dg
        composition_roots composition_final query_idxs trace_openings
        composition_openings"
      using partial
      by (blast dest:
          accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
          accepted_with_partial_initial_openings_aligned_consistent_imp_aligned)
    from accepted_with_partial_initial_openings_aligned_candidates_if_no_partial_merkle_bad
        [OF aligned False]
    obtain trace_table composition_table where trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
      and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
      by blast
    have bad:
      "soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
        s (Some (result, final_state))"
      by (rule accepted_verifier_tied_aligned_transcript_partial_candidate_partition
          [OF false_statement fri_openings partial header trace_candidate
            composition_candidate])
    then show ?thesis
      unfolding
        soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle_def
      by simp
  qed
qed

lemma accepted_fri_opening_transcript_headerE:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
  obtains fr as rest where
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
  using fri_openings
  unfolding accepted_fri_opening_transcript_def
  by blast

lemma accepted_partition_soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle_or_empty_header:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
  shows
    "soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle
        s out \<or>
     soundness_bad_event_partial_candidate_empty_header s out"
proof -
  from acc obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  from verify_monad_accepted_fri_opening_transcript[OF supp[unfolded out_eq]]
  obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final query_idxs trace_round_layers
      composition_round_layers
  where fri_openings:
    "accepted_fri_opening_transcript s (Some (result, final_state))
      trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final query_idxs trace_round_layers
      composition_round_layers"
    by blast
  show ?thesis
  proof (cases "composition_roots = []")
    case False
    have
      "soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle
        s (Some (result, final_state))"
      by (rule
          accepted_fri_opening_transcript_verifier_tied_partition_with_partial_merkle
          [OF false_statement fri_openings False])
    then show ?thesis
      unfolding out_eq by simp
  next
    case True
    note comp_empty = True
    from accepted_fri_opening_transcript_headerE[OF fri_openings]
    obtain fr as rest where header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
      by blast
    show ?thesis
    proof (cases
        "partial_merkle_inconsistency_bad s (Some (result, final_state))")
      case True
      then have
        "soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle
          s (Some (result, final_state))"
        unfolding
          soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle_def
        by simp
      then show ?thesis
        unfolding out_eq by simp
    next
      case False
      from verify_monad_accepted_with_partial_trace_openings_for_header
          [OF supp[unfolded out_eq] header]
      obtain trace_query_idxs trace_openings where trace_partial:
        "accepted_with_partial_trace_openings s
          (Some (result, final_state)) fr trace_query_idxs trace_openings"
        by blast
      obtain trace_table where trace_candidate:
        "partial_trace_table_candidate trace_table trace_openings"
        using
          accepted_with_partial_trace_openings_candidate_if_no_partial_merkle_bad
          [OF trace_partial False]
        by blast
      have accepted_out: "accepted (Some (result, final_state))"
        by (rule accepted_with_partial_trace_openings_imp_accepted
            [OF trace_partial])
      let ?composition_table = "replicate (scale * clength) composition_final"
      have empty_partial:
        "accepted_with_empty_composition_header_candidates s
          (Some (result, final_state)) fr trace_roots trace_final as dg
          composition_final trace_query_idxs trace_openings trace_table
          ?composition_table"
        unfolding accepted_with_empty_composition_header_candidates_def
        by (intro conjI exI[of _ rest])
          (use accepted_out header comp_empty trace_partial trace_candidate
            in simp_all)
      have "soundness_bad_event_partial_candidate_empty_header s
          (Some (result, final_state))"
        by (rule accepted_empty_composition_header_candidate_partition
            [OF false_statement empty_partial])
      then show ?thesis
        unfolding out_eq by simp
    qed
  qed
qed

lemma soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_union_bound:
  assumes comp_bound:
      "wp_event verify_monad
        (composition_bad_with_partial_candidates s) s \<le>
        composition_error"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
        trace_fri_error'"
    and comp_fri_bound:
      "wp_event verify_monad
        (composition_fri_bad_with_verifier_tied_partial_candidate s) s \<le>
        composition_fri_error'"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_aligned_transcript_partial_candidates s) s \<le>
        query_error"
  shows
    "wp_event verify_monad
      (soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
        s) s \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
proof -
  have "wp_event verify_monad
      (soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
        s) s \<le>
      wp_event verify_monad
        (composition_bad_with_partial_candidates s) s +
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s +
      wp_event verify_monad
        (composition_fri_bad_with_verifier_tied_partial_candidate s) s +
      wp_event verify_monad
        (query_bad_with_aligned_transcript_partial_candidates s) s"
    unfolding
      soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_def
    by (rule wp_event_union_bound4)
  also have "... \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
    by (intro add_mono comp_bound trace_fri_bound comp_fri_bound
        query_bound)
  finally show ?thesis .
qed

lemma soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle_union_bound:
  assumes merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le>
        merkle_error"
    and comp_bound:
      "wp_event verify_monad
        (composition_bad_with_partial_candidates s) s \<le>
        composition_error"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
        trace_fri_error'"
    and comp_fri_bound:
      "wp_event verify_monad
        (composition_fri_bad_with_verifier_tied_partial_candidate s) s \<le>
        composition_fri_error'"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_aligned_transcript_partial_candidates s) s \<le>
        query_error"
  shows
    "wp_event verify_monad
      (soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle
        s) s \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
proof -
  have partial_bound:
    "wp_event verify_monad
      (soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
        s) s \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
    by (rule
        soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  have "wp_event verify_monad
      (soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle
        s) s \<le>
      wp_event verify_monad (partial_merkle_inconsistency_bad s) s +
      wp_event verify_monad
        (soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
          s) s"
    unfolding
      soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle_def
    by (rule wp_event_union_bound)
  also have "... \<le>
      merkle_error +
      (composition_error + trace_fri_error' + composition_fri_error' +
        query_error)"
    by (intro add_mono merkle_bound partial_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_data_state_verifier_tied_aligned_transcript_partial_candidate_union_bound:
  assumes comp_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_error"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_partial_candidate)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_verifier_tied_partial_candidate)
        adversary_initial_state \<le> composition_fri_error'"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_aligned_transcript_partial_candidates)
        adversary_initial_state \<le> query_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate)
      adversary_initial_state \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?comp = "?E composition_bad_with_partial_candidates"
  let ?trace = "?E trace_fri_bad_with_header_tied_partial_candidate"
  let ?comp_fri =
    "?E composition_fri_bad_with_verifier_tied_partial_candidate"
  let ?query = "?E query_bad_with_aligned_transcript_partial_candidates"
  let ?partial =
    "?E soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate"
  have "wp_event ?M ?partial adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?comp out \<or> ?trace out \<or> ?comp_fri out \<or>
          ?query out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?comp adversary_initial_state +
      wp_event ?M ?trace adversary_initial_state +
      wp_event ?M ?comp_fri adversary_initial_state +
      wp_event ?M ?query adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
    by (intro add_mono comp_bound trace_fri_bound comp_fri_bound
        query_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle_union_bound:
  assumes merkle_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state \<le> merkle_error"
    and comp_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_error"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_partial_candidate)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_verifier_tied_partial_candidate)
        adversary_initial_state \<le> composition_fri_error'"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_aligned_transcript_partial_candidates)
        adversary_initial_state \<le> query_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle)
      adversary_initial_state \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
proof -
  have partial_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate)
      adversary_initial_state \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
    by (rule
        checked_staged_security_with_data_state_verifier_tied_aligned_transcript_partial_candidate_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?merkle = "?E partial_merkle_inconsistency_bad"
  let ?partial =
    "?E soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate"
  let ?with_merkle =
    "?E soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle"
  have "wp_event ?M ?with_merkle adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?merkle out \<or> ?partial out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?merkle adversary_initial_state +
      wp_event ?M ?partial adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      merkle_error +
      (composition_error + trace_fri_error' + composition_fri_error' +
        query_error)"
    by (intro add_mono merkle_bound partial_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_soundness_from_verifier_tied_aligned_transcript_partial_candidate_and_empty_header_bounds:
  fixes partial_candidate_error empty_header_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and partial_candidate_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle)
        adversary_initial_state \<le> partial_candidate_error"
    and empty_header_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_partial_candidate_empty_header)
        adversary_initial_state \<le> empty_header_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    partial_candidate_error + empty_header_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?partial =
    "?E soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle"
  let ?empty = "?E soundness_bad_event_partial_candidate_empty_header"
  let ?bad = "\<lambda>out. ?partial out \<or> ?empty out"
  have accepted_bad:
    "wp_event ?M accepted adversary_initial_state \<le>
      wp_event ?M ?bad adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?M adversary_initial_state)"
      and acc: "accepted out"
    show "?bad out"
    proof (cases out)
      case None
      then show ?thesis
        using acc unfolding accepted_def by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      have verifier:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        using checked_staged_security_experiment_with_data_state_outcomeE
          [OF support[unfolded out_eq]]
        by blast
      have verifier_acc: "accepted (Some (result, final_state))"
        unfolding accepted_def by simp
      have local_bad:
        "soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle
            ?s (Some (result, final_state)) \<or>
         soundness_bad_event_partial_candidate_empty_header ?s
            (Some (result, final_state))"
        by (rule
            accepted_partition_soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle_or_empty_header
            [OF false_statement verifier verifier_acc])
      then show ?thesis
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
    qed
  qed
  have bad_bound:
    "wp_event ?M ?bad adversary_initial_state \<le>
      partial_candidate_error + empty_header_error"
  proof -
    have "wp_event ?M ?bad adversary_initial_state \<le>
        wp_event ?M ?partial adversary_initial_state +
        wp_event ?M ?empty adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le> partial_candidate_error + empty_header_error"
      by (intro add_mono partial_candidate_bound empty_header_bound)
    finally show ?thesis .
  qed
  have staged_bound:
    "wp_event (checked_staged_security_experiment A) accepted
      adversary_initial_state \<le>
      partial_candidate_error + empty_header_error"
    unfolding checked_staged_security_experiment_acceptance_with_data_state
    by (rule order_trans[OF accepted_bad bad_bound])
  show ?thesis
  proof -
    have
      "wp_event (checked_staged_security_experiment A)
        (\<lambda>out. \<not> Option.is_none out) adversary_initial_state =
       wp_event (checked_staged_security_experiment A) accepted
        adversary_initial_state"
      unfolding wp_event_def accepted_def
      by (rule arg_cong[where
        f="\<lambda>Q. wp (checked_staged_security_experiment A) Q
          adversary_initial_state"])
        (rule ext, simp)
    then show ?thesis
      unfolding checked_staged_adversary_acceptance_probability_def
      using staged_bound by simp
  qed
qed

lemma checked_staged_soundness_from_verifier_tied_aligned_transcript_partial_candidate_components_and_empty_header_bound:
  fixes merkle_error composition_error trace_fri_error'
    composition_fri_error' query_error empty_header_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and merkle_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state \<le> merkle_error"
    and comp_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_error"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_partial_candidate)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_verifier_tied_partial_candidate)
        adversary_initial_state \<le> composition_fri_error'"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_aligned_transcript_partial_candidates)
        adversary_initial_state \<le> query_error"
    and empty_header_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          soundness_bad_event_partial_candidate_empty_header)
        adversary_initial_state \<le> empty_header_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    merkle_error + composition_error + trace_fri_error' +
    composition_fri_error' + query_error + empty_header_error"
proof -
  have partial_candidate_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle)
      adversary_initial_state \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
    by (rule
        checked_staged_security_with_data_state_verifier_tied_aligned_transcript_partial_candidate_with_partial_merkle_union_bound
        [OF merkle_bound comp_bound trace_fri_bound comp_fri_bound
          query_bound])
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      (merkle_error + composition_error + trace_fri_error' +
        composition_fri_error' + query_error) + empty_header_error"
    by (rule
        checked_staged_soundness_from_verifier_tied_aligned_transcript_partial_candidate_and_empty_header_bounds
        [OF false_statement partial_candidate_bound empty_header_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma trace_fri_bad_with_verifier_tied_partial_candidateE:
  assumes
    "trace_fri_bad_with_verifier_tied_partial_candidate s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "\<not> trace_table_low_degree trace_table"
  using assms
  unfolding trace_fri_bad_with_verifier_tied_partial_candidate_def
  by blast

lemma composition_fri_bad_with_verifier_tied_partial_candidateE:
  assumes
    "composition_fri_bad_with_verifier_tied_partial_candidate s out"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final fri_query_idxs
      trace_openings composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "trace_table_low_degree trace_table"
    "\<not> composition_table_low_degree maxDegree composition_table"
proof -
  obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table
  where fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    and aligned:
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final fri_query_idxs
      trace_openings composition_openings"
    and trace_cand:
    "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
    "partial_composition_table_candidate composition_table
      composition_openings"
    and trace_low:
      "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    using assms
    unfolding composition_fri_bad_with_verifier_tied_partial_candidate_def
    by metis
  show ?thesis
    by (rule that[OF fri_openings aligned trace_cand comp_cand trace_low
          comp_not_low])
qed

lemma trace_fri_bad_with_verifier_tied_imp_reachable_partial_candidate:
  assumes
    "trace_fri_bad_with_verifier_tied_partial_candidate s out"
  shows "trace_fri_bad_with_reachable_partial_candidate s out"
proof (rule trace_fri_bad_with_verifier_tied_partial_candidateE[OF assms])
  fix trace_roots trace_bs trace_final dg composition_roots
    composition_bs composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr trace_openings trace_table
  assume partial:
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    and cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
  show ?thesis
    unfolding trace_fri_bad_with_reachable_partial_candidate_def
    by (intro exI conjI; (rule partial | rule cand | rule not_low))
qed

lemma composition_fri_bad_with_verifier_tied_imp_reachable_partial_candidate:
  assumes
    "composition_fri_bad_with_verifier_tied_partial_candidate s out"
  shows "composition_fri_bad_with_reachable_partial_candidate s out"
proof (rule
    composition_fri_bad_with_verifier_tied_partial_candidateE[OF assms])
  fix trace_roots trace_bs trace_final fri_dg composition_roots
    composition_bs composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr as trace_openings composition_openings
    trace_table composition_table
  assume aligned:
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final fri_query_idxs
      trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
  have unaligned:
    "accepted_with_partial_initial_openings s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final
      fri_query_idxs trace_openings fri_query_idxs composition_openings"
    by (rule accepted_with_partial_initial_openings_aligned_imp_unaligned
        [OF aligned])
  show ?thesis
    unfolding composition_fri_bad_with_reachable_partial_candidate_def
    by (intro exI conjI; (rule unaligned | rule trace_cand |
          rule comp_cand | rule trace_low | rule comp_not_low))
qed

lemma trace_fri_bad_with_verifier_tied_partial_candidate_None[simp]:
  "\<not> trace_fri_bad_with_verifier_tied_partial_candidate s None"
  unfolding trace_fri_bad_with_verifier_tied_partial_candidate_def
    accepted_fri_opening_transcript_def
  by simp

lemma composition_fri_bad_with_verifier_tied_partial_candidate_None[simp]:
  "\<not> composition_fri_bad_with_verifier_tied_partial_candidate s None"
  unfolding composition_fri_bad_with_verifier_tied_partial_candidate_def
    accepted_fri_opening_transcript_def
  by simp

lemma trace_fri_verifier_tied_imp_sampled_or_missing_layer_chain:
  assumes "trace_fri_bad_with_verifier_tied_partial_candidate s out"
  shows
    "trace_fri_bad_with_verifier_tied_sampled_layer_chain s out \<or>
     trace_fri_verifier_tied_missing_sampled_layer_chain s out"
  using assms
  unfolding trace_fri_verifier_tied_missing_sampled_layer_chain_def
  by blast

lemma composition_fri_verifier_tied_imp_sampled_or_missing_layer_chain:
  assumes "composition_fri_bad_with_verifier_tied_partial_candidate s out"
  shows
    "composition_fri_bad_with_verifier_tied_sampled_layer_chain s out \<or>
     composition_fri_verifier_tied_missing_sampled_layer_chain s out"
  using assms
  unfolding composition_fri_verifier_tied_missing_sampled_layer_chain_def
  by blast

lemma wp_trace_fri_verifier_tied_bound_from_sampled_and_missing:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_missing_sampled_layer_chain s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_partial_candidate s) s \<le> R + M"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_partial_candidate s) s \<le>
    wp_event verify_monad
      (\<lambda>out. trace_fri_bad_with_verifier_tied_sampled_layer_chain s out \<or>
        trace_fri_verifier_tied_missing_sampled_layer_chain s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_verifier_tied_imp_sampled_or_missing_layer_chain)
  also have "... \<le>
    wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_sampled_layer_chain s) s +
    wp_event verify_monad
      (trace_fri_verifier_tied_missing_sampled_layer_chain s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (rule add_mono[OF sampled_bound missing_bound])
  finally show ?thesis .
qed

lemma wp_composition_fri_verifier_tied_bound_from_sampled_and_missing:
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_missing_sampled_layer_chain s) s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s \<le>
      R + M"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s \<le>
    wp_event verify_monad
      (\<lambda>out.
        composition_fri_bad_with_verifier_tied_sampled_layer_chain s out \<or>
        composition_fri_verifier_tied_missing_sampled_layer_chain s out) s"
    by (rule wp_event_mono)
      (rule composition_fri_verifier_tied_imp_sampled_or_missing_layer_chain)
  also have "... \<le>
    wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s +
    wp_event verify_monad
      (composition_fri_verifier_tied_missing_sampled_layer_chain s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (rule add_mono[OF sampled_bound missing_bound])
  finally show ?thesis .
qed

definition trace_fri_verifier_tied_sampled_layer_assignment_obstruction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_verifier_tied_sampled_layer_assignment_obstruction s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_layer_assignment_obstruction
        trace_table_low_degree trace_table (clength - 1) trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers)"

definition trace_fri_verifier_tied_sampled_assignment_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_verifier_tied_sampled_assignment_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_assignment_conflict trace_table trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers)"

definition trace_fri_verifier_tied_zero_round_final_obstruction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_verifier_tied_zero_round_final_obstruction s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      length trace_bs = 0 \<and>
      \<not> fri_final_constant_consistent trace_table trace_final)"

definition composition_fri_verifier_tied_sampled_layer_assignment_obstruction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_sampled_layer_assignment_obstruction s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_layer_assignment_obstruction
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers)"

definition composition_fri_verifier_tied_sampled_assignment_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_sampled_assignment_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_assignment_conflict composition_table
        composition_roots composition_bs composition_final fri_query_idxs
        composition_round_layers)"

definition composition_fri_verifier_tied_zero_round_final_obstruction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_zero_round_final_obstruction s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      length composition_bs = 0 \<and>
      \<not> fri_final_constant_consistent composition_table
        composition_final)"

lemma trace_fri_header_tied_zero_round_final_obstruction_imp_verifier_tied:
  assumes "trace_fri_header_tied_zero_round_final_obstruction s out"
  shows "trace_fri_verifier_tied_zero_round_final_obstruction s out"
  using assms
  unfolding trace_fri_header_tied_zero_round_final_obstruction_def
    trace_fri_verifier_tied_zero_round_final_obstruction_def
  by blast

lemma composition_fri_verifier_tied_zero_round_final_obstruction_false:
  "\<not> composition_fri_verifier_tied_zero_round_final_obstruction s out"
proof
  assume obstruction:
    "composition_fri_verifier_tied_zero_round_final_obstruction s out"
  then obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table
  where fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    and aligned:
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final fri_query_idxs
      trace_openings composition_openings"
    and zero: "length composition_bs = 0"
    unfolding composition_fri_verifier_tied_zero_round_final_obstruction_def
    by blast
  have nonempty: "composition_roots \<noteq> []"
    by (rule accepted_with_partial_initial_openings_aligned_shapes(1)
        [OF aligned])
  have "composition_roots = []"
    using accepted_fri_opening_transcript_shapes(4)[OF fri_openings] zero
    by simp
  then show False
    using nonempty by simp
qed

lemma wp_composition_fri_verifier_tied_zero_round_final_obstruction_zero:
  "wp_event verify_monad
    (composition_fri_verifier_tied_zero_round_final_obstruction s) s = 0"
  unfolding wp_event_def wp_def dist_expect_def
  by (simp add:
      composition_fri_verifier_tied_zero_round_final_obstruction_false)

lemma trace_fri_verifier_tied_assignment_obstruction_imp_conflict_or_zero:
  assumes obstruction:
    "trace_fri_verifier_tied_sampled_layer_assignment_obstruction s out"
  shows
    "trace_fri_verifier_tied_sampled_assignment_conflict s out \<or>
     trace_fri_verifier_tied_zero_round_final_obstruction s out"
proof -
  obtain trace_roots trace_bs' trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table
  where fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs'
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and partial:
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and generic:
    "generic_fri_sampled_layer_assignment_obstruction
      trace_table_low_degree trace_table (clength - 1) trace_roots
      trace_bs' trace_final fri_query_idxs trace_round_layers"
    using obstruction
    unfolding trace_fri_verifier_tied_sampled_layer_assignment_obstruction_def
    by blast
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have trace_rounds_le: "length trace_bs' \<le> N"
  proof -
    have len: "length trace_bs' = ceil_log clength"
      using accepted_fri_opening_transcript_shapes(1,2)[OF fri_openings]
      by simp
    have "clength \<le> clength * scale"
      using scale_pos by simp
    also have "... = 2 ^ N"
      by (rule eval_power)
    finally have "ceil_log clength \<le> N"
      by (rule ceil_log_le_power)
    then show ?thesis
      using len by simp
  qed
  have query_bounds':
    "\<And>round_idx. round_idx < length fri_query_idxs \<Longrightarrow>
      fri_query_idxs ! round_idx < clength * scale"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length fri_query_idxs"
    have "fri_query_idxs ! round_idx \<in> set fri_query_idxs"
      using round_bound by simp
    then show "fri_query_idxs ! round_idx < clength * scale"
      by (rule accepted_fri_opening_transcript_query_idx_bound
          [OF fri_openings])
  qed
  have split:
    "generic_fri_sampled_assignment_conflict trace_table trace_roots
        trace_bs' trace_final fri_query_idxs trace_round_layers \<or>
      length trace_bs' = 0 \<and>
        \<not> fri_final_constant_consistent trace_table trace_final"
    by (rule
        generic_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final
          [OF generic query_bounds' eval_power trace_rounds_le])
  then show ?thesis
  proof
    assume conflict:
      "generic_fri_sampled_assignment_conflict trace_table trace_roots
        trace_bs' trace_final fri_query_idxs trace_round_layers"
    then show ?thesis
      unfolding trace_fri_verifier_tied_sampled_assignment_conflict_def
      by (intro disjI1 exI conjI)
        (rule fri_openings, rule partial, rule cand, rule not_low,
          rule conflict)
  next
    assume zero:
      "length trace_bs' = 0 \<and>
        \<not> fri_final_constant_consistent trace_table trace_final"
    then show ?thesis
      unfolding trace_fri_verifier_tied_zero_round_final_obstruction_def
      by (intro disjI2 exI conjI)
        (rule fri_openings, rule partial, rule cand, rule not_low,
          simp_all)
  qed
qed

lemma composition_fri_verifier_tied_assignment_obstruction_imp_conflict_or_zero_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and obstruction:
      "composition_fri_verifier_tied_sampled_layer_assignment_obstruction
        s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict s out \<or>
     composition_fri_verifier_tied_zero_round_final_obstruction s out"
proof -
  obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table
  where fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    and aligned:
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final fri_query_idxs
      trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and generic:
      "generic_fri_sampled_layer_assignment_obstruction
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers"
    using obstruction
    unfolding
      composition_fri_verifier_tied_sampled_layer_assignment_obstruction_def
    by metis
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  obtain result final_state where out_eq: "out = Some (result, final_state)"
    using fri_openings unfolding accepted_fri_opening_transcript_def by blast
  have outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using support out_eq by simp
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs fri_dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF fri_openings]
      out_eq by simp
  have degree_bound: "to_nat fri_dg \<le> maxDegree"
    by (rule verify_monad_accepted_fri_challenges_degree_bound
        [OF outcome challenges])
  have composition_rounds_le: "length composition_bs \<le> N"
  proof -
    have len: "length composition_bs = ceil_log (to_nat fri_dg + 1)"
      using accepted_fri_opening_transcript_shapes(3,4)[OF fri_openings]
      by simp
    have "to_nat fri_dg + 1 \<le> clength * scale"
      using degree_bound maxDegree_less_eval_domain by linarith
    also have "... = 2 ^ N"
      by (rule eval_power)
    finally have "ceil_log (to_nat fri_dg + 1) \<le> N"
      by (rule ceil_log_le_power)
    then show ?thesis
      using len by simp
  qed
  have query_bounds:
    "\<And>round_idx. round_idx < length fri_query_idxs \<Longrightarrow>
      fri_query_idxs ! round_idx < clength * scale"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length fri_query_idxs"
    have "fri_query_idxs ! round_idx \<in> set fri_query_idxs"
      using round_bound by simp
    then show "fri_query_idxs ! round_idx < clength * scale"
      by (rule accepted_fri_opening_transcript_query_idx_bound
          [OF fri_openings])
  qed
  have split:
    "generic_fri_sampled_assignment_conflict composition_table
        composition_roots composition_bs composition_final fri_query_idxs
        composition_round_layers \<or>
      length composition_bs = 0 \<and>
        \<not> fri_final_constant_consistent composition_table
          composition_final"
    by (rule
        generic_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final
          [OF generic query_bounds eval_power composition_rounds_le])
  then show ?thesis
  proof
    assume conflict:
      "generic_fri_sampled_assignment_conflict composition_table
        composition_roots composition_bs composition_final fri_query_idxs
        composition_round_layers"
    then show ?thesis
      unfolding
        composition_fri_verifier_tied_sampled_assignment_conflict_def
      by (intro disjI1 exI conjI)
        (rule fri_openings, rule aligned, rule trace_cand, rule comp_cand,
          rule trace_low, rule comp_not_low, rule conflict)
  next
    assume zero:
      "length composition_bs = 0 \<and>
        \<not> fri_final_constant_consistent composition_table
          composition_final"
    then show ?thesis
      unfolding
        composition_fri_verifier_tied_zero_round_final_obstruction_def
      by (intro disjI2 exI conjI)
        (rule fri_openings, rule aligned, rule trace_cand, rule comp_cand,
          rule trace_low, rule comp_not_low, simp_all)
  qed
qed

lemma trace_fri_verifier_tied_missing_sampled_imp_assignment_obstruction:
  assumes missing:
    "trace_fri_verifier_tied_missing_sampled_layer_chain s out"
  shows
    "trace_fri_verifier_tied_sampled_layer_assignment_obstruction s out"
proof -
  have bad:
    "trace_fri_bad_with_verifier_tied_partial_candidate s out"
    and not_sampled:
      "\<not> trace_fri_bad_with_verifier_tied_sampled_layer_chain s out"
    using missing
    unfolding trace_fri_verifier_tied_missing_sampled_layer_chain_def
    by blast+
  from trace_fri_bad_with_verifier_tied_partial_candidateE[OF bad]
  obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table
  where fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and partial:
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    by blast
  have partial_generic:
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
    by (rule accepted_fri_opening_transcript_trace_generic_partial_evidence
        [OF fri_openings])
  have no_chain:
    "\<And>doms layers. \<not>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
  proof
    fix doms layers
    assume chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
    have "trace_fri_bad_with_verifier_tied_sampled_layer_chain s out"
      unfolding trace_fri_bad_with_verifier_tied_sampled_layer_chain_def
      by (intro exI conjI)
        (rule fri_openings, rule partial, rule cand, rule not_low,
          rule chain)
    then show False
      using not_sampled by contradiction
  qed
  have obstruction:
    "generic_fri_sampled_layer_assignment_obstruction
      trace_table_low_degree trace_table (clength - 1) trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers"
    unfolding generic_fri_sampled_layer_assignment_obstruction_def
    using partial_generic no_chain by blast
  show ?thesis
    unfolding trace_fri_verifier_tied_sampled_layer_assignment_obstruction_def
    by (intro exI conjI)
      (rule fri_openings, rule partial, rule cand, rule not_low,
        rule obstruction)
qed

lemma composition_fri_verifier_tied_missing_sampled_imp_assignment_obstruction:
  assumes missing:
    "composition_fri_verifier_tied_missing_sampled_layer_chain s out"
  shows
    "composition_fri_verifier_tied_sampled_layer_assignment_obstruction s out"
proof -
  have bad:
    "composition_fri_bad_with_verifier_tied_partial_candidate s out"
    and not_sampled:
      "\<not> composition_fri_bad_with_verifier_tied_sampled_layer_chain s out"
    using missing
    unfolding composition_fri_verifier_tied_missing_sampled_layer_chain_def
    by blast+
  from composition_fri_bad_with_verifier_tied_partial_candidateE[OF bad]
  obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table
  where fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    and aligned:
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final fri_query_idxs
      trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    by metis
  have partial_generic:
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) composition_roots composition_bs composition_final
      fri_query_idxs composition_round_layers"
    by (rule
        accepted_fri_opening_transcript_composition_generic_partial_evidence
        [OF fri_openings])
  have no_chain:
    "\<And>doms layers. \<not>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms
        layers"
  proof
    fix doms layers
    assume chain:
      "generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms
        layers"
    have "composition_fri_bad_with_verifier_tied_sampled_layer_chain s out"
      unfolding composition_fri_bad_with_verifier_tied_sampled_layer_chain_def
      by (intro exI conjI)
        (rule fri_openings, rule aligned, rule trace_cand, rule comp_cand,
          rule trace_low, rule comp_not_low, rule chain)
    then show False
      using not_sampled by contradiction
  qed
  have obstruction:
    "generic_fri_sampled_layer_assignment_obstruction
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) composition_roots composition_bs composition_final
      fri_query_idxs composition_round_layers"
    unfolding generic_fri_sampled_layer_assignment_obstruction_def
    using partial_generic no_chain by blast
  show ?thesis
    unfolding
      composition_fri_verifier_tied_sampled_layer_assignment_obstruction_def
    by (intro exI conjI)
      (rule fri_openings, rule aligned, rule trace_cand, rule comp_cand,
        rule trace_low, rule comp_not_low, rule obstruction)
qed

lemma wp_trace_fri_verifier_tied_missing_sampled_bound_from_assignment_obstruction:
  assumes obstruction_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_layer_assignment_obstruction s) s
      \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_verifier_tied_missing_sampled_layer_chain s) s \<le> M"
proof -
  have "wp_event verify_monad
      (trace_fri_verifier_tied_missing_sampled_layer_chain s) s \<le>
    wp_event verify_monad
      (trace_fri_verifier_tied_sampled_layer_assignment_obstruction s) s"
    by (rule wp_event_mono)
      (rule trace_fri_verifier_tied_missing_sampled_imp_assignment_obstruction)
  also have "... \<le> M"
    by (rule obstruction_bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_verifier_tied_missing_sampled_bound_from_assignment_obstruction:
  assumes obstruction_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_layer_assignment_obstruction s) s
      \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_missing_sampled_layer_chain s) s \<le> M"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_missing_sampled_layer_chain s) s \<le>
    wp_event verify_monad
      (composition_fri_verifier_tied_sampled_layer_assignment_obstruction s) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_missing_sampled_imp_assignment_obstruction)
  also have "... \<le> M"
    by (rule obstruction_bound)
  finally show ?thesis .
qed

lemma wp_trace_fri_verifier_tied_bound_from_sampled_and_assignment_obstruction:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and obstruction_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_layer_assignment_obstruction s) s
      \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_partial_candidate s) s \<le> R + M"
  by (rule wp_trace_fri_verifier_tied_bound_from_sampled_and_missing
      [OF sampled_bound
        wp_trace_fri_verifier_tied_missing_sampled_bound_from_assignment_obstruction
          [OF obstruction_bound]])

lemma wp_composition_fri_verifier_tied_bound_from_sampled_and_assignment_obstruction:
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and obstruction_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_layer_assignment_obstruction s) s
      \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s \<le>
      R + M"
  by (rule wp_composition_fri_verifier_tied_bound_from_sampled_and_missing
      [OF sampled_bound
        wp_composition_fri_verifier_tied_missing_sampled_bound_from_assignment_obstruction
          [OF obstruction_bound]])

lemma trace_fri_bad_with_verifier_tied_partial_candidates_staged_bound:
  assumes verifier_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_verifier_tied_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> C"
  by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    (simp_all add: verifier_bound)

lemma composition_fri_bad_with_verifier_tied_partial_candidates_staged_bound:
  assumes verifier_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_bad_with_verifier_tied_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> C"
  by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    (simp_all add: verifier_bound)

lemma wp_trace_fri_verifier_tied_assignment_obstruction_bound_from_conflict_and_zero:
  assumes conflict_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_zero_round_final_obstruction s) s \<le> Z"
  shows
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_layer_assignment_obstruction s) s
      \<le> C + Z"
proof -
  have "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_layer_assignment_obstruction s) s
    \<le> wp_event verify_monad
      (\<lambda>out. trace_fri_verifier_tied_sampled_assignment_conflict s out \<or>
        trace_fri_verifier_tied_zero_round_final_obstruction s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_verifier_tied_assignment_obstruction_imp_conflict_or_zero)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_verifier_tied_sampled_assignment_conflict s) s +
      wp_event verify_monad
        (trace_fri_verifier_tied_zero_round_final_obstruction s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> C + Z"
    by (rule add_mono[OF conflict_bound zero_bound])
  finally show ?thesis .
qed

lemma wp_composition_fri_verifier_tied_assignment_obstruction_bound_from_conflict_and_zero:
  assumes conflict_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_zero_round_final_obstruction s) s \<le> Z"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_layer_assignment_obstruction s) s
      \<le> C + Z"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_layer_assignment_obstruction s) s
    \<le> wp_event verify_monad
      (\<lambda>out. composition_fri_verifier_tied_sampled_assignment_conflict s out \<or>
        composition_fri_verifier_tied_zero_round_final_obstruction s out) s"
    by (rule wp_event_mono_on_support)
      (rule
        composition_fri_verifier_tied_assignment_obstruction_imp_conflict_or_zero_on_support)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict s) s +
      wp_event verify_monad
        (composition_fri_verifier_tied_zero_round_final_obstruction s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> C + Z"
    by (rule add_mono[OF conflict_bound zero_bound])
  finally show ?thesis .
qed

lemma wp_composition_fri_verifier_tied_assignment_obstruction_bound_from_conflict:
  assumes conflict_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_layer_assignment_obstruction s) s
      \<le> C"
proof -
  have zero_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_zero_round_final_obstruction s) s \<le> 0"
    by (subst wp_composition_fri_verifier_tied_zero_round_final_obstruction_zero)
      simp
  have "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_layer_assignment_obstruction s) s
      \<le> C + 0"
    by (rule
        wp_composition_fri_verifier_tied_assignment_obstruction_bound_from_conflict_and_zero
        [OF conflict_bound zero_bound])
  then show ?thesis
    by simp
qed

lemma wp_trace_fri_verifier_tied_bound_from_sampled_conflict_and_zero:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and conflict_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_zero_round_final_obstruction s) s \<le> Z"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_partial_candidate s) s
      \<le> R + (C + Z)"
  by (rule
      wp_trace_fri_verifier_tied_bound_from_sampled_and_assignment_obstruction
        [OF sampled_bound
          wp_trace_fri_verifier_tied_assignment_obstruction_bound_from_conflict_and_zero
            [OF conflict_bound zero_bound]])

lemma wp_composition_fri_verifier_tied_bound_from_sampled_conflict_and_zero:
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and conflict_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_zero_round_final_obstruction s) s \<le> Z"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s
      \<le> R + (C + Z)"
  by (rule
      wp_composition_fri_verifier_tied_bound_from_sampled_and_assignment_obstruction
        [OF sampled_bound
      wp_composition_fri_verifier_tied_assignment_obstruction_bound_from_conflict_and_zero
            [OF conflict_bound zero_bound]])

lemma wp_composition_fri_verifier_tied_bound_from_sampled_conflict:
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and conflict_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s
      \<le> R + C"
  by (rule
      wp_composition_fri_verifier_tied_bound_from_sampled_and_assignment_obstruction
        [OF sampled_bound
          wp_composition_fri_verifier_tied_assignment_obstruction_bound_from_conflict
            [OF conflict_bound]])

lemma trace_fri_verifier_tied_reductionD:
  assumes "trace_fri_verifier_tied_reduction s"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_partial_candidate s) s \<le>
      trace_fri_error"
  using assms unfolding trace_fri_verifier_tied_reduction_def by simp

lemma composition_fri_verifier_tied_reductionD:
  assumes "composition_fri_verifier_tied_reduction s"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s \<le>
      composition_fri_error"
  using assms unfolding composition_fri_verifier_tied_reduction_def by simp

lemma trace_fri_verifier_tied_reduction_from_sampled_conflict_and_zero:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and conflict_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_zero_round_final_obstruction s) s \<le> Z"
    and total_bound: "R + (C + Z) \<le> trace_fri_error"
  shows "trace_fri_verifier_tied_reduction s"
  unfolding trace_fri_verifier_tied_reduction_def
  by (rule order_trans[
      OF wp_trace_fri_verifier_tied_bound_from_sampled_conflict_and_zero
        [OF sampled_bound conflict_bound zero_bound] total_bound])

lemma composition_fri_verifier_tied_reduction_from_sampled_conflict_and_zero:
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and conflict_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_zero_round_final_obstruction s) s \<le> Z"
    and total_bound: "R + (C + Z) \<le> composition_fri_error"
  shows "composition_fri_verifier_tied_reduction s"
  unfolding composition_fri_verifier_tied_reduction_def
  by (rule order_trans[
      OF wp_composition_fri_verifier_tied_bound_from_sampled_conflict_and_zero
        [OF sampled_bound conflict_bound zero_bound] total_bound])

lemma composition_fri_verifier_tied_reduction_from_sampled_conflict:
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and conflict_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
    and total_bound: "R + C \<le> composition_fri_error"
  shows "composition_fri_verifier_tied_reduction s"
  unfolding composition_fri_verifier_tied_reduction_def
  by (rule order_trans[
      OF wp_composition_fri_verifier_tied_bound_from_sampled_conflict
        [OF sampled_bound conflict_bound] total_bound])

lemma trace_fri_zero_round_checked_final_obstruction_imp_verifier_tied:
  assumes
    "trace_fri_zero_round_checked_final_obstruction s out"
  shows "trace_fri_bad_with_verifier_tied_partial_candidate s out"
proof (rule trace_fri_zero_round_checked_final_obstruction_not_trace_low_degree
    [OF assms])
  fix trace_roots trace_bs trace_final dg composition_roots composition_bs
    composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr trace_openings trace_table
  assume fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and checked:
    "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
      trace_openings trace_table trace_final"
    and not_low: "\<not> trace_table_low_degree trace_table"
  have partial:
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    using checked unfolding trace_zero_round_final_checked_candidate_def
    by simp
  have cand:
    "partial_trace_table_candidate trace_table trace_openings"
    using checked unfolding trace_zero_round_final_checked_candidate_def
    by simp
  show ?thesis
    unfolding trace_fri_bad_with_verifier_tied_partial_candidate_def
    by (intro exI conjI)
      (rule fri_openings, rule partial, rule cand, rule not_low)
qed

lemma trace_fri_zero_round_checked_final_obstruction_mono_verifier_tied:
  "wp_event verify_monad (trace_fri_zero_round_checked_final_obstruction s) s \<le>
    wp_event verify_monad
      (trace_fri_bad_with_verifier_tied_partial_candidate s) s"
  by (rule wp_event_mono)
    (rule trace_fri_zero_round_checked_final_obstruction_imp_verifier_tied)

end

end
