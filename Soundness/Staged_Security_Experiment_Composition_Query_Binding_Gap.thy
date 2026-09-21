(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Binding_Gap.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Binding_Gap
  imports
    Staged_Security_Experiment_Composition_Query_Header_Rounds
    Staged_Security_Experiment_Composition_Query_Current
begin

text \<open>
  Candidate-binding gap for the query-prefix composition route.

  The dynamic header-supported query target is small only for candidates that
  are already visible in the prefix oracle state.  This layer isolates the
  remaining proof obligation: if a later authenticated candidate pair is not in
  that prefix candidate set, the gap must be charged to Merkle/collision side
  events in the next proof layer.
\<close>

context soundness
begin

lemma checked_staged_query_prefix_candidate_pair_hit_imp_header_supported_target_hit:
  assumes candidate:
      "(trace_table, composition_table) \<in>
        query_header_supported_partial_table_candidates prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)"
    and hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state))"
  shows
      "checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_header_supported_query_target
        (Some (((prefix, prefix_state), raw), raw_state))"
proof -
  have subset:
    "staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table prefix prefix_state \<subseteq>
      staged_query_prefix_header_supported_query_target prefix prefix_state"
    unfolding
      staged_query_prefix_candidate_pair_query_target_from_prefix_def
      staged_query_prefix_header_supported_query_target_def
      query_header_supported_partial_union_good_sets_def
    using candidate query_sampling_success_space_subset by auto
  show ?thesis
  using hit subset
  unfolding checked_staged_query_prefix_dynamic_index_hit_def
  by auto
qed

definition query_header_supported_single_round_partial_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> ('f list \<times> 'f list) set"
where
  "query_header_supported_single_round_partial_table_candidates s fr
      f_fri_roots f_final as dg composition_fri_roots final i =
    {(trace_table, composition_table).
      composition_fri_roots \<noteq> [] \<and>
      (\<exists>trace_openings composition_openings rest.
        partial_authenticated_table fr (scale * clength)
          trace_openings s \<and>
        partial_authenticated_table (hd composition_fri_roots)
          (scale * clength) composition_openings s \<and>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<and>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest)}"

lemma query_header_supported_single_round_partial_table_candidatesI:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and trace_auth:
      "partial_authenticated_table fr (scale * clength)
        trace_openings s"
    and comp_auth:
      "partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) composition_openings s"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  shows
    "(trace_table, composition_table) \<in>
      query_header_supported_single_round_partial_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots final i"
  unfolding query_header_supported_single_round_partial_table_candidates_def
  using assms by blast

lemma query_header_supported_single_round_partial_table_candidate_notin_contradicts:
  assumes notin:
      "(trace_table, composition_table) \<notin>
        query_header_supported_single_round_partial_table_candidates s fr
          f_fri_roots f_final as dg composition_fri_roots final i"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and trace_auth:
      "partial_authenticated_table fr (scale * clength)
        trace_openings s"
    and comp_auth:
      "partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) composition_openings s"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  shows False
  using notin
    query_header_supported_single_round_partial_table_candidatesI
      [OF comp_nonempty trace_auth comp_auth trace_candidate
        comp_candidate header]
  by contradiction

definition staged_query_prefix_single_round_header_supported_query_target
  :: "nat \<Rightarrow> 'f staged_query_prefix_data \<Rightarrow>
      'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_single_round_header_supported_query_target i prefix
      prefix_state =
    {idx.
      \<exists>trace_table composition_table.
        (trace_table, composition_table) \<in>
          query_header_supported_single_round_partial_table_candidates
            prefix_state
            (sqp_trace_root prefix)
            (sqp_trace_fri_roots prefix)
            (sqp_trace_final prefix)
            (sqp_alphas prefix)
            (sqp_degree prefix)
            (sqp_composition_fri_roots prefix)
            (sqp_composition_final prefix)
            i \<and>
        idx \<in>
          staged_query_prefix_candidate_pair_query_target_from_prefix
            trace_table composition_table prefix prefix_state}"

lemma checked_staged_query_prefix_candidate_pair_hit_imp_single_round_header_target_hit:
  assumes candidate:
      "(trace_table, composition_table) \<in>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i"
    and hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state))"
  shows
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_single_round_header_supported_query_target i)
        (Some (((prefix, prefix_state), raw), raw_state))"
proof -
  have idx_in:
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table prefix prefix_state"
    using hit unfolding checked_staged_query_prefix_dynamic_index_hit_def
    by simp
  have
    "index (to_nat raw) \<in>
      staged_query_prefix_single_round_header_supported_query_target i
        prefix prefix_state"
    unfolding staged_query_prefix_single_round_header_supported_query_target_def
    by (intro CollectI exI[of _ trace_table]
        exI[of _ composition_table])
      (use candidate idx_in in simp)
  then show ?thesis
    unfolding checked_staged_query_prefix_dynamic_index_hit_def
    by simp
qed

lemma query_header_supported_partial_table_candidatesI_from_partials:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  shows
    "(trace_table, composition_table) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
proof -
  have body:
    "composition_fri_roots \<noteq> [] \<and>
      (\<exists>out trace_query_idxs composition_query_idxs trace_openings
          composition_openings rest.
        out \<in> set_dist (execute verify_monad s) \<and>
        accepted_with_partial_trace_openings s out fr trace_query_idxs
          trace_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        accepted_with_partial_composition_openings s out
          (hd composition_fri_roots) composition_query_idxs
          composition_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest)"
    using comp_nonempty outcome trace_partial trace_candidate comp_partial
      comp_candidate header
    by blast
  show ?thesis
    unfolding query_header_supported_partial_table_candidates_def
    using body by simp
qed

lemma query_header_supported_partial_table_candidate_notin_contradicts_partials:
  assumes notin:
      "(trace_table, composition_table) \<notin>
        query_header_supported_partial_table_candidates s fr f_fri_roots
          f_final as dg composition_fri_roots final"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  shows False
  using notin
    query_header_supported_partial_table_candidatesI_from_partials
      [OF comp_nonempty outcome trace_partial trace_candidate comp_partial
        comp_candidate header]
  by contradiction

lemma query_header_supported_partial_table_candidate_notin_no_accepted_partials:
  assumes notin:
      "(trace_table, composition_table) \<notin>
        query_header_supported_partial_table_candidates s fr f_fri_roots
          f_final as dg composition_fri_roots final"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
  shows
    "\<not> (\<exists>result final_state trace_query_idxs composition_query_idxs rest.
      Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
      accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings \<and>
      accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings \<and>
      verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest)"
proof
  assume
    "\<exists>result final_state trace_query_idxs composition_query_idxs rest.
      Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
      accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings \<and>
      accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings \<and>
      verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  then obtain result final_state trace_query_idxs composition_query_idxs rest
    where outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
      and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
      and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
      and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    by blast
  show False
    by (rule query_header_supported_partial_table_candidate_notin_contradicts_partials
        [OF notin comp_nonempty outcome trace_partial trace_candidate
        comp_partial comp_candidate header])
qed

lemma accepted_with_partial_trace_openings_single_round_update_other_empty:
  assumes partial:
      "accepted_with_partial_trace_openings s out fr query_idxs
        ((replicate rounds []) [i := trace_openings])"
    and j_bound: "j < rounds"
    and j_ne: "j \<noteq> i"
  shows "powers_scaled (query_idxs ! j) = []"
proof -
  have indices:
    "map opening_index (((replicate rounds []) [i := trace_openings]) ! j) =
      powers_scaled (query_idxs ! j)"
    using accepted_with_partial_trace_openings_shapes(3)[OF partial j_bound]
    .
  have "((replicate rounds []) [i := trace_openings]) ! j = []"
    using j_bound j_ne by simp
  then show ?thesis
    using indices by simp
qed

lemma accepted_with_partial_composition_openings_single_round_update_other_false:
  assumes partial:
      "accepted_with_partial_composition_openings s out composition_root
        query_idxs ((replicate rounds []) [i := composition_openings])"
    and j_bound: "j < rounds"
    and j_ne: "j \<noteq> i"
  shows False
proof -
  have indices:
    "map opening_index (((replicate rounds []) [i := composition_openings]) ! j) =
      [query_idxs ! j, fri_sibling_index (scale * clength) (query_idxs ! j)]"
    using
      accepted_with_partial_composition_openings_shapes(3)
        [OF partial j_bound]
    .
  have "((replicate rounds []) [i := composition_openings]) ! j = []"
    using j_bound j_ne by simp
  then show False
    using indices by simp
qed

lemma query_header_supported_partial_opening_witnesses_pullback_or_path_output:
  assumes witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses s fr f_fri_roots
          f_final as dg composition_fri_roots final"
  shows
    "(partial_authenticated_table fr (scale * clength) trace_openings s \<and>
      partial_authenticated_table (hd composition_fri_roots) (scale * clength)
        composition_openings s) \<or>
     (\<exists>witness_state. \<exists>opn \<in> set trace_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state fr (scale * clength)
          (opening_index opn) (opening_value opn) (opening_path opn))
        s witness_state) \<or>
     (\<exists>witness_state. \<exists>opn \<in> set composition_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state (hd composition_fri_roots)
          (scale * clength) (opening_index opn) (opening_value opn)
          (opening_path opn))
        s witness_state)"
proof -
  from witness obtain result witness_state rest where outcome:
      "Some (result, witness_state) \<in> set_dist (execute verify_monad s)"
    and trace_table:
      "partial_authenticated_table fr (scale * clength) trace_openings
        witness_state"
    and comp_table:
      "partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) composition_openings witness_state"
    by (elim query_header_supported_partial_opening_witnessesE)
  have ext: "s \<le> witness_state"
    by (rule verify_monad_hash_extends[OF outcome])
  have trace_pull:
    "partial_authenticated_table fr (scale * clength) trace_openings s \<or>
     (\<exists>opn \<in> set trace_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state fr (scale * clength)
          (opening_index opn) (opening_value opn) (opening_path opn))
        s witness_state)"
    by (rule partial_authenticated_table_pullback_or_new_output_hit
        [OF ext trace_table])
  have comp_pull:
    "partial_authenticated_table (hd composition_fri_roots) (scale * clength)
        composition_openings s \<or>
     (\<exists>opn \<in> set composition_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state (hd composition_fri_roots)
          (scale * clength) (opening_index opn) (opening_value opn)
          (opening_path opn))
        s witness_state)"
    by (rule partial_authenticated_table_pullback_or_new_output_hit
        [OF ext comp_table])
  from trace_pull comp_pull show ?thesis by blast
qed

lemma query_header_supported_single_round_candidate_from_witness_or_path_output:
  assumes witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses s fr f_fri_roots
          f_final as dg composition_fri_roots final"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
  shows
    "(trace_table, composition_table) \<in>
      query_header_supported_single_round_partial_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots final i \<or>
     (\<exists>witness_state. \<exists>opn \<in> set trace_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state fr (scale * clength)
          (opening_index opn) (opening_value opn) (opening_path opn))
        s witness_state) \<or>
     (\<exists>witness_state. \<exists>opn \<in> set composition_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state (hd composition_fri_roots)
          (scale * clength) (opening_index opn) (opening_value opn)
          (opening_path opn))
        s witness_state)"
proof -
  from witness obtain result witness_state rest where comp_nonempty:
      "composition_fri_roots \<noteq> []"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    by (elim query_header_supported_partial_opening_witnessesE)
  have pull:
    "(partial_authenticated_table fr (scale * clength) trace_openings s \<and>
      partial_authenticated_table (hd composition_fri_roots) (scale * clength)
        composition_openings s) \<or>
     (\<exists>witness_state. \<exists>opn \<in> set trace_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state fr (scale * clength)
          (opening_index opn) (opening_value opn) (opening_path opn))
        s witness_state) \<or>
     (\<exists>witness_state. \<exists>opn \<in> set composition_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state (hd composition_fri_roots)
          (scale * clength) (opening_index opn) (opening_value opn)
          (opening_path opn))
        s witness_state)"
    by (rule query_header_supported_partial_opening_witnesses_pullback_or_path_output
        [OF witness])
  then show ?thesis
  proof
    assume auths:
      "partial_authenticated_table fr (scale * clength) trace_openings s \<and>
       partial_authenticated_table (hd composition_fri_roots) (scale * clength)
        composition_openings s"
    have candidate:
      "(trace_table, composition_table) \<in>
        query_header_supported_single_round_partial_table_candidates s fr
          f_fri_roots f_final as dg composition_fri_roots final i"
      by (rule query_header_supported_single_round_partial_table_candidatesI
          [OF comp_nonempty _ _ trace_candidate comp_candidate header])
        (use auths in simp_all)
    then show ?thesis by simp
  next
    assume
      "(\<exists>witness_state. \<exists>opn\<in>set trace_openings.
          hash_map_new_output_hit
           (merkle_path_target_roots witness_state fr (scale * clength)
             (opening_index opn) (opening_value opn) (opening_path opn))
           s witness_state) \<or>
       (\<exists>witness_state. \<exists>opn\<in>set composition_openings.
          hash_map_new_output_hit
           (merkle_path_target_roots witness_state (hd composition_fri_roots)
             (scale * clength) (opening_index opn) (opening_value opn)
             (opening_path opn))
           s witness_state)"
    then show ?thesis by simp
  qed
qed

lemma query_header_supported_single_round_candidate_notin_imp_path_output:
  assumes witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses s fr f_fri_roots
          f_final as dg composition_fri_roots final"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and notin:
      "(trace_table, composition_table) \<notin>
        query_header_supported_single_round_partial_table_candidates s fr
          f_fri_roots f_final as dg composition_fri_roots final i"
  shows
    "(\<exists>witness_state. \<exists>opn \<in> set trace_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state fr (scale * clength)
          (opening_index opn) (opening_value opn) (opening_path opn))
        s witness_state) \<or>
     (\<exists>witness_state. \<exists>opn \<in> set composition_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state (hd composition_fri_roots)
          (scale * clength) (opening_index opn) (opening_value opn)
          (opening_path opn))
        s witness_state)"
  using query_header_supported_single_round_candidate_from_witness_or_path_output
    [OF witness trace_candidate comp_candidate] notin
  by blast

definition checked_staged_security_with_query_prefix_header_supported_query_target_hit_at
where
  "checked_staged_security_with_query_prefix_header_supported_query_target_hit_at
      i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state), continuation),
        final_state) \<Rightarrow>
        checked_staged_query_prefix_dynamic_index_hit
          staged_query_prefix_header_supported_query_target
          (Some (((prefix, prefix_state), raw), raw_state)))"

definition checked_staged_security_with_query_prefix_candidate_binding_gap_at
where
  "checked_staged_security_with_query_prefix_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
          trace_openings composition_openings i out \<and>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<and>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<and>
        (trace_table, composition_table) \<notin>
          query_header_supported_partial_table_candidates prefix_state
            (sqp_trace_root prefix)
            (sqp_trace_fri_roots prefix)
            (sqp_trace_final prefix)
            (sqp_alphas prefix)
            (sqp_degree prefix)
            (sqp_composition_fri_roots prefix)
            (sqp_composition_final prefix))"

definition checked_staged_security_with_query_prefix_candidate_binding_gap_side
where
  "checked_staged_security_with_query_prefix_candidate_binding_gap_side
      trace_openings composition_openings trace_table composition_table i out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<and>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<and>
        (trace_table, composition_table) \<notin>
          query_header_supported_partial_table_candidates prefix_state
            (sqp_trace_root prefix)
            (sqp_trace_fri_roots prefix)
            (sqp_trace_final prefix)
            (sqp_alphas prefix)
            (sqp_degree prefix)
            (sqp_composition_fri_roots prefix)
            (sqp_composition_final prefix))"

definition checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
where
  "checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out
      \<longleftrightarrow>
    checked_staged_security_with_query_prefix_candidate_binding_gap_side
      trace_openings composition_openings trace_table composition_table i out \<and>
    checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
      trace_openings composition_openings i out"

lemma checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_imp_current_prefix_authenticated:
  assumes gap:
    "checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
      i out"
  using gap
  unfolding
    checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at_def
    checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_def
  by blast

lemma checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_bound_from_dynamic_target:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event (checked_staged_query_prefix_receive_with_state A i)
        (checked_staged_query_prefix_dynamic_index_hit
          staged_query_prefix_prefix_authenticated_opening_target)
        adversary_initial_state \<le> B"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le> B"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_imp_current_prefix_authenticated)
  have current_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i)
      adversary_initial_state \<le> B"
    by (rule
        checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_dynamic_target
        [OF wf controlled i_bound prefix_bound])
  show ?thesis
    by (rule order_trans[OF event_le current_bound])
qed

lemma checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_bound_from_trace_indices:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_frac:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (query_raw_preimage_card_envelope
            (card
              (staged_query_prefix_prefix_authenticated_trace_indices prefix
                prefix_state))) /
          nnreal size \<le> query_error_bound"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have current_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_trace_indices
        [OF wf controlled i_bound trace_frac])
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_imp_current_prefix_authenticated)
  show ?thesis
    by (rule order_trans[OF event_le current_bound])
qed

lemma checked_staged_security_with_query_prefix_candidate_binding_gap_iff_fixed_header_component:
  "checked_staged_security_with_query_prefix_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out
    \<longleftrightarrow>
   checked_staged_security_with_query_prefix_fixed_header_component
      (checked_staged_security_with_query_prefix_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
  unfolding
    checked_staged_security_with_query_prefix_candidate_binding_gap_at_def
    checked_staged_security_with_query_prefix_candidate_binding_gap_side_def
    checked_staged_security_with_query_prefix_fixed_header_component_def
  by (cases out) (auto split: prod.splits)

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_imp_header_target_or_binding_gap:
  assumes hit:
    "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table
        (sqp_alphas prefix)"
  shows
    "checked_staged_security_with_query_prefix_header_supported_query_target_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  from hit have opening_target:
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state"
    by (rule
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hitE)
  have opening_subset:
    "staged_query_prefix_candidate_opening_query_target_from_prefix
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      i prefix prefix_state \<subseteq>
     staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
      composition_table prefix prefix_state"
    by (rule
        staged_query_prefix_candidate_opening_query_target_from_prefix_subset_candidate_pair_from_prefix
        [OF trace_candidate comp_candidate trace_low comp_low not_all])
  have pair_target_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
    using opening_target opening_subset
    unfolding checked_staged_query_prefix_dynamic_index_hit_def by auto
  show ?thesis
  proof (cases
      "(trace_table, composition_table) \<in>
        query_header_supported_partial_table_candidates prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)")
    case True
    have header_target:
      "checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_header_supported_query_target
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_pair_hit_imp_header_supported_target_hit
          [OF True pair_target_hit])
    have
      "checked_staged_security_with_query_prefix_header_supported_query_target_hit_at
        i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_header_supported_query_target_hit_at_def
      using header_target by simp
    then show ?thesis by simp
  next
    case False
    have
      "checked_staged_security_with_query_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_candidate_binding_gap_at_def
      using hit trace_candidate comp_candidate False by simp
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_candidate_binding_gap_imp_header_authenticated:
  assumes gap:
    "checked_staged_security_with_query_prefix_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i out"
  using gap
  unfolding checked_staged_security_with_query_prefix_candidate_binding_gap_at_def
  by (cases out) (auto split: prod.splits)

lemma checked_staged_security_with_query_prefix_candidate_binding_gap_current_imp_prefix_gap_or_opening_path_output_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and current:
      "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        (checked_staged_security_with_query_prefix_candidate_binding_gap_side
          trace_openings composition_openings trace_table composition_table i)
        trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out \<or>
     checked_staged_security_with_query_prefix_opening_path_output_hit
      trace_openings composition_openings out"
proof -
  have side:
    "checked_staged_security_with_query_prefix_candidate_binding_gap_side
      trace_openings composition_openings trace_table composition_table i out"
    and current_hit:
    "checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i out"
    using current
    unfolding
      checked_staged_security_with_query_prefix_fixed_current_authenticated_component_def
      checked_staged_security_with_query_prefix_fixed_header_component_def
    by simp_all
  have split:
    "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out"
    by (rule
        checked_staged_security_with_query_prefix_fixed_current_authenticated_component_imp_prefix_or_path_output_on_support
        [OF wf controlled i_bound support current])
  then show ?thesis
  proof
    assume prefix:
      "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i out"
    have
      "checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i out"
      unfolding
        checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at_def
      using side prefix by simp
    then show ?thesis by simp
  next
    assume
      "checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out"
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_candidate_binding_gap_imp_current_or_path_output_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and gap:
      "checked_staged_security_with_query_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
      (checked_staged_security_with_query_prefix_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
proof -
  have fixed:
    "checked_staged_security_with_query_prefix_fixed_header_component
      (checked_staged_security_with_query_prefix_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
    using gap
    unfolding
      checked_staged_security_with_query_prefix_candidate_binding_gap_iff_fixed_header_component
    .
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_imp_current_or_witness_path_output_on_support
        [OF wf controlled i_bound support fixed])
qed

lemma checked_staged_security_with_query_prefix_candidate_binding_gap_imp_prefix_gap_or_path_outputs_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and gap:
      "checked_staged_security_with_query_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i out \<or>
     checked_staged_security_with_query_prefix_opening_path_output_hit
      trace_openings composition_openings out \<or>
     checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
proof -
  have split:
    "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
      (checked_staged_security_with_query_prefix_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i out"
    by (rule
        checked_staged_security_with_query_prefix_candidate_binding_gap_imp_current_or_path_output_on_support
        [OF wf controlled i_bound support gap])
  then show ?thesis
  proof
    assume current:
      "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        (checked_staged_security_with_query_prefix_candidate_binding_gap_side
          trace_openings composition_openings trace_table composition_table i)
        trace_openings composition_openings i out"
    have
      "checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i out \<or>
       checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out"
      by (rule
          checked_staged_security_with_query_prefix_candidate_binding_gap_current_imp_prefix_gap_or_opening_path_output_on_support
          [OF wf controlled i_bound support current])
    then show ?thesis by blast
  next
    assume
      "checked_staged_security_with_query_prefix_header_witness_path_output_hit
        (checked_staged_security_with_query_prefix_candidate_binding_gap_side
          trace_openings composition_openings trace_table composition_table i)
        trace_openings composition_openings i out"
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_candidate_binding_gap_bound_from_prefix_target_and_path_outputs:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event (checked_staged_query_prefix_receive_with_state A i)
        (checked_staged_query_prefix_dynamic_index_hit
          staged_query_prefix_prefix_authenticated_opening_target)
        adversary_initial_state \<le> P"
    and opening_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_opening_path_output_hit
          trace_openings composition_openings)
        adversary_initial_state \<le> Q"
    and witness_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          (checked_staged_security_with_query_prefix_candidate_binding_gap_side
            trace_openings composition_openings trace_table composition_table i)
          trace_openings composition_openings i)
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le> P + Q + R"
proof -
  let ?m =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?prefix =
    "checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_at
      trace_openings composition_openings trace_table composition_table i"
  let ?open_path =
    "checked_staged_security_with_query_prefix_opening_path_output_hit
      trace_openings composition_openings"
  let ?witness_path =
    "checked_staged_security_with_query_prefix_header_witness_path_output_hit
      (checked_staged_security_with_query_prefix_candidate_binding_gap_side
        trace_openings composition_openings trace_table composition_table i)
      trace_openings composition_openings i"
  have event_le:
    "wp_event ?m
      (checked_staged_security_with_query_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
     wp_event ?m
      (\<lambda>out. ?prefix out \<or> ?open_path out \<or> ?witness_path out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_candidate_binding_gap_imp_prefix_gap_or_path_outputs_on_support
        [OF wf controlled i_bound])
  have union_le:
    "wp_event ?m
      (\<lambda>out. ?prefix out \<or> ?open_path out \<or> ?witness_path out)
      adversary_initial_state \<le>
     wp_event ?m ?prefix adversary_initial_state +
     (wp_event ?m ?open_path adversary_initial_state +
      wp_event ?m ?witness_path adversary_initial_state)"
  proof -
    have
      "wp_event ?m
        (\<lambda>out. ?prefix out \<or> ?open_path out \<or> ?witness_path out)
        adversary_initial_state \<le>
       wp_event ?m ?prefix adversary_initial_state +
       wp_event ?m
        (\<lambda>out. ?open_path out \<or> ?witness_path out)
        adversary_initial_state"
      by (rule wp_event_union_bound)
    also have
      "... \<le>
       wp_event ?m ?prefix adversary_initial_state +
       (wp_event ?m ?open_path adversary_initial_state +
        wp_event ?m ?witness_path adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis .
  qed
  have prefix_gap_bound:
    "wp_event ?m ?prefix adversary_initial_state \<le> P"
    by (rule
        checked_staged_security_with_query_prefix_prefix_candidate_binding_gap_bound_from_dynamic_target
        [OF wf controlled i_bound prefix_bound])
  have sum_bound:
    "wp_event ?m ?prefix adversary_initial_state +
      (wp_event ?m ?open_path adversary_initial_state +
       wp_event ?m ?witness_path adversary_initial_state) \<le> P + Q + R"
  proof -
    have path_sum_bound:
      "wp_event ?m ?open_path adversary_initial_state +
       wp_event ?m ?witness_path adversary_initial_state \<le> Q + R"
      by (rule add_mono[OF opening_path_bound witness_path_bound])
    have
      "wp_event ?m ?prefix adversary_initial_state +
        (wp_event ?m ?open_path adversary_initial_state +
         wp_event ?m ?witness_path adversary_initial_state) \<le> P + (Q + R)"
      by (rule add_mono[OF prefix_gap_bound path_sum_bound])
    then show ?thesis
      by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF event_le order_trans[OF union_le sum_bound]])
qed

lemma checked_staged_security_with_query_prefix_candidate_binding_gap_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_candidate_binding_gap_at
        trace_openings composition_openings trace_table composition_table i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_query_prefix_candidate_binding_gap_imp_header_authenticated)
  have header_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
    by (rule
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_bound_from_budgets
        [OF wf controlled i_bound])
  show ?thesis
    by (rule order_trans[OF event_le header_bound])
qed

definition checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at
  :: "nat \<Rightarrow> 'f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at
      i A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (\<exists>prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            staged_query_prefix_header_supported_query_target
            (Some (((prefix, prefix_state), raw), raw_state))))"

definition checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
  :: "nat \<Rightarrow> 'f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
      i A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (\<exists>prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_single_round_header_supported_query_target i)
            (Some (((prefix, prefix_state), raw), raw_state))))"

text \<open>
  The preceding actual-alpha event is a diagnostic compatibility predicate:
  it existentially ranges over query-prefix branches.  It should not be bounded
  directly from query-prefix target budgets unless a separate projection lemma
  is proved.  Bounded public-route arguments should keep the event at the
  query-prefix data-state layer, or use an explicitly aligned actual-alpha
  predicate whose query-prefix output is fixed by the run.
\<close>

definition checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_at
  :: "nat \<Rightarrow> 'f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_at
      i A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (\<exists>trace_table composition_table prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_candidate_pair_query_target_from_prefix
              trace_table composition_table)
            (Some (((prefix, prefix_state), raw), raw_state)) \<and>
          (trace_table, composition_table) \<notin>
            query_header_supported_partial_table_candidates prefix_state
              (sqp_trace_root prefix)
              (sqp_trace_fri_roots prefix)
              (sqp_trace_final prefix)
              (sqp_alphas prefix)
              (sqp_degree prefix)
              (sqp_composition_fri_roots prefix)
              (sqp_composition_final prefix)))"

definition checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
  :: "nat \<Rightarrow> 'f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
      i A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (\<exists>trace_table composition_table prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_candidate_pair_query_target_from_prefix
              trace_table composition_table)
            (Some (((prefix, prefix_state), raw), raw_state)) \<and>
          (trace_table, composition_table) \<notin>
            query_header_supported_single_round_partial_table_candidates
              prefix_state
              (sqp_trace_root prefix)
              (sqp_trace_fri_roots prefix)
              (sqp_trace_final prefix)
              (sqp_alphas prefix)
              (sqp_degree prefix)
              (sqp_composition_fri_roots prefix)
              (sqp_composition_final prefix)
              i))"

definition checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
  :: "nat \<Rightarrow> 'f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
      i A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (\<exists>trace_openings composition_openings trace_table composition_table
            prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          (trace_openings, composition_openings) \<in>
            query_header_supported_partial_opening_witnesses
              (verifier_state_from_adversary attacker_state
                (staged_proof_transcript data))
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              (staged_alphas data)
              (staged_degree data)
              (staged_composition_fri_roots data)
              (staged_composition_final data) \<and>
          partial_trace_table_candidate trace_table
            ((replicate rounds []) [i := trace_openings]) \<and>
          partial_composition_table_candidate composition_table
            ((replicate rounds []) [i := composition_openings]) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_candidate_pair_query_target_from_prefix
              trace_table composition_table)
            (Some (((prefix, prefix_state), raw), raw_state)) \<and>
          (trace_table, composition_table) \<notin>
            query_header_supported_single_round_partial_table_candidates
              prefix_state
              (sqp_trace_root prefix)
              (sqp_trace_fri_roots prefix)
              (sqp_trace_final prefix)
              (sqp_alphas prefix)
              (sqp_degree prefix)
              (sqp_composition_fri_roots prefix)
              (sqp_composition_final prefix)
              i))"

text \<open>
  This witness variant has the same diagnostic status: the authenticated
  openings are carried, but the query-prefix branch is still existential in the
  actual-alpha output.  Use the same-run query-prefix witness-gap predicates for
  probability bounds.
\<close>

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_imp_gap:
  assumes gap:
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
      i A out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
      i A out"
proof (cases out)
  case None
  then show ?thesis
    using gap
    unfolding
      checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix alpha_prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed) (auto split: prod.splits)
  from gap obtain trace_openings composition_openings trace_table
      composition_table prefix prefix_state raw raw_state where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state))"
    and notin:
      "(trace_table, composition_table) \<notin>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at_def
    by auto
  have body:
    "\<exists>trace_table composition_table prefix prefix_state raw raw_state.
      Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<and>
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state)) \<and>
      (trace_table, composition_table) \<notin>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i"
    by (intro exI[of _ trace_table] exI[of _ composition_table]
        exI[of _ prefix] exI[of _ prefix_state]
        exI[of _ raw] exI[of _ raw_state])
      (use builder prefix_receive target_hit notin in simp)
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at_def
    using body by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witnessE:
  assumes gap:
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains trace_openings composition_openings trace_table composition_table
      prefix prefix_state raw raw_state where
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
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
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [i := trace_openings])"
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [i := composition_openings])"
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
    "(trace_table, composition_table) \<notin>
      query_header_supported_single_round_partial_table_candidates
        prefix_state
        (sqp_trace_root prefix)
        (sqp_trace_fri_roots prefix)
        (sqp_trace_final prefix)
        (sqp_alphas prefix)
        (sqp_degree prefix)
        (sqp_composition_fri_roots prefix)
        (sqp_composition_final prefix)
        i"
proof -
  have body:
    "\<exists>trace_openings composition_openings trace_table composition_table
        prefix prefix_state raw raw_state.
      Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<and>
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      (trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<and>
      partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings]) \<and>
      partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings]) \<and>
      checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state)) \<and>
      (trace_table, composition_table) \<notin>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i"
    using gap
    unfolding
      checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at_def
    by simp
  then obtain trace_openings composition_openings trace_table composition_table
      prefix prefix_state raw raw_state where
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
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
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [i := trace_openings])"
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [i := composition_openings])"
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
    "(trace_table, composition_table) \<notin>
      query_header_supported_single_round_partial_table_candidates
        prefix_state
        (sqp_trace_root prefix)
        (sqp_trace_fri_roots prefix)
        (sqp_trace_final prefix)
        (sqp_alphas prefix)
        (sqp_degree prefix)
        (sqp_composition_fri_roots prefix)
        (sqp_composition_final prefix)
        i"
    by blast
  then show ?thesis
    by (rule that)
qed

definition checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at
  :: "nat \<Rightarrow> 'f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at
      i A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (\<exists>trace_openings composition_openings trace_table composition_table
            prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          (trace_openings, composition_openings) \<in>
            query_header_supported_partial_opening_witnesses
              (verifier_state_from_adversary attacker_state
                (staged_proof_transcript data))
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              (staged_alphas data)
              (staged_degree data)
              (staged_composition_fri_roots data)
              (staged_composition_final data) \<and>
          partial_trace_table_candidate trace_table
            ((replicate rounds []) [i := trace_openings]) \<and>
          partial_composition_table_candidate composition_table
            ((replicate rounds []) [i := composition_openings]) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_candidate_pair_query_target_from_prefix
              trace_table composition_table)
            (Some (((prefix, prefix_state), raw), raw_state)) \<and>
          (trace_table, composition_table) \<notin>
            query_header_supported_partial_table_candidates prefix_state
              (sqp_trace_root prefix)
              (sqp_trace_fri_roots prefix)
              (sqp_trace_final prefix)
              (sqp_alphas prefix)
              (sqp_degree prefix)
              (sqp_composition_fri_roots prefix)
              (sqp_composition_final prefix)))"

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_imp_gap:
  assumes gap:
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at
      i A out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_at
      i A out"
  using gap
proof (cases out)
  case None
  then show ?thesis
    using gap
    unfolding
      checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix alpha_prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed) (auto split: prod.splits)
  have gap_body:
    "\<exists>trace_openings composition_openings trace_table composition_table
        prefix prefix_state raw raw_state.
      Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<and>
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      (trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<and>
      partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings]) \<and>
      partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings]) \<and>
      checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state)) \<and>
      (trace_table, composition_table) \<notin>
        query_header_supported_partial_table_candidates prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)"
    using gap
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at_def
    by simp
  from gap_body
  obtain trace_openings composition_openings trace_table composition_table
      prefix prefix_state raw raw_state where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state))"
    and notin:
      "(trace_table, composition_table) \<notin>
        query_header_supported_partial_table_candidates prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)"
    by blast
  have body:
    "\<exists>trace_table composition_table prefix prefix_state raw raw_state.
      Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<and>
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state)) \<and>
      (trace_table, composition_table) \<notin>
        query_header_supported_partial_table_candidates prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)"
    by (intro exI[of _ trace_table] exI[of _ composition_table]
        exI[of _ prefix] exI[of _ prefix_state]
        exI[of _ raw] exI[of _ raw_state])
      (use builder prefix_receive target_hit notin in simp)
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_at_def
    using body by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witnessE:
  assumes gap:
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains trace_openings composition_openings trace_table composition_table
      prefix prefix_state raw raw_state where
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
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
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [i := trace_openings])"
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [i := composition_openings])"
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
    "(trace_table, composition_table) \<notin>
      query_header_supported_partial_table_candidates prefix_state
        (sqp_trace_root prefix)
        (sqp_trace_fri_roots prefix)
        (sqp_trace_final prefix)
        (sqp_alphas prefix)
        (sqp_degree prefix)
        (sqp_composition_fri_roots prefix)
        (sqp_composition_final prefix)"
proof -
  have body:
    "\<exists>trace_openings composition_openings trace_table composition_table
        prefix prefix_state raw raw_state.
      Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<and>
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      (trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<and>
      partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings]) \<and>
      partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings]) \<and>
      checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state)) \<and>
      (trace_table, composition_table) \<notin>
        query_header_supported_partial_table_candidates prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)"
    using gap
    unfolding
      checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at_def
    by simp
  then obtain trace_openings composition_openings trace_table composition_table
      prefix prefix_state raw raw_state where
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
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
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [i := trace_openings])"
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [i := composition_openings])"
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
    "(trace_table, composition_table) \<notin>
      query_header_supported_partial_table_candidates prefix_state
        (sqp_trace_root prefix)
        (sqp_trace_fri_roots prefix)
        (sqp_trace_final prefix)
        (sqp_alphas prefix)
        (sqp_degree prefix)
        (sqp_composition_fri_roots prefix)
        (sqp_composition_final prefix)"
    by blast
  then show ?thesis
    by (rule that)
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_imp_single_round_header_target_or_gap:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
      A trace_table composition_table i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  from
    checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE
      [OF hit]
  obtain prefix prefix_state raw raw_state where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE
        [OF hit])
  show ?thesis
  proof (cases
      "(trace_table, composition_table) \<in>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i")
    case True
    have single_round_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_single_round_header_supported_query_target i)
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_pair_hit_imp_single_round_header_target_hit
          [OF True target_hit])
    have
      "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    proof -
      have inner:
        "\<exists>prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_single_round_header_supported_query_target i)
            (Some (((prefix, prefix_state), raw), raw_state))"
        by (intro exI[of _ prefix] exI[of _ prefix_state]
            exI[of _ raw] exI[of _ raw_state])
          (use builder prefix_receive single_round_hit in simp)
      show ?thesis
        unfolding
          checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at_def
        using inner by simp
    qed
    then show ?thesis by simp
  next
    case False
    have
      "checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    proof -
      have inner:
        "\<exists>trace_table composition_table prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_candidate_pair_query_target_from_prefix
              trace_table composition_table)
            (Some (((prefix, prefix_state), raw), raw_state)) \<and>
          (trace_table, composition_table) \<notin>
            query_header_supported_single_round_partial_table_candidates
              prefix_state
              (sqp_trace_root prefix)
              (sqp_trace_fri_roots prefix)
              (sqp_trace_final prefix)
              (sqp_alphas prefix)
              (sqp_degree prefix)
              (sqp_composition_fri_roots prefix)
              (sqp_composition_final prefix)
              i"
        by (intro exI[of _ trace_table] exI[of _ composition_table]
            exI[of _ prefix] exI[of _ prefix_state]
            exI[of _ raw] exI[of _ raw_state])
          (use builder prefix_receive target_hit False in simp)
      show ?thesis
        unfolding
          checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_at_def
        using inner by simp
    qed
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_with_witness_imp_single_round_header_target_or_gap_witness:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
      A trace_table composition_table i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
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
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
  shows
    "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  from
    checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE
      [OF hit]
  obtain prefix prefix_state raw raw_state where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE
        [OF hit])
  show ?thesis
  proof (cases
      "(trace_table, composition_table) \<in>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          i")
    case True
    have single_round_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_single_round_header_supported_query_target i)
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_pair_hit_imp_single_round_header_target_hit
          [OF True target_hit])
    have
      "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    proof -
      have inner:
        "\<exists>prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_single_round_header_supported_query_target i)
            (Some (((prefix, prefix_state), raw), raw_state))"
        by (intro exI[of _ prefix] exI[of _ prefix_state]
            exI[of _ raw] exI[of _ raw_state])
          (use builder prefix_receive single_round_hit in simp)
      show ?thesis
        unfolding
          checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at_def
        using inner by simp
    qed
    then show ?thesis by simp
  next
    case False
    have
      "checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    proof -
      have inner:
        "\<exists>trace_openings composition_openings trace_table composition_table
            prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          (trace_openings, composition_openings) \<in>
            query_header_supported_partial_opening_witnesses
              (verifier_state_from_adversary attacker_state
                (staged_proof_transcript data))
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              (staged_alphas data)
              (staged_degree data)
              (staged_composition_fri_roots data)
              (staged_composition_final data) \<and>
          partial_trace_table_candidate trace_table
            ((replicate rounds []) [i := trace_openings]) \<and>
          partial_composition_table_candidate composition_table
            ((replicate rounds []) [i := composition_openings]) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_candidate_pair_query_target_from_prefix
              trace_table composition_table)
            (Some (((prefix, prefix_state), raw), raw_state)) \<and>
          (trace_table, composition_table) \<notin>
            query_header_supported_single_round_partial_table_candidates
              prefix_state
              (sqp_trace_root prefix)
              (sqp_trace_fri_roots prefix)
              (sqp_trace_final prefix)
              (sqp_alphas prefix)
              (sqp_degree prefix)
              (sqp_composition_fri_roots prefix)
              (sqp_composition_final prefix)
              i"
        by (intro exI[of _ trace_openings] exI[of _ composition_openings]
            exI[of _ trace_table] exI[of _ composition_table]
            exI[of _ prefix] exI[of _ prefix_state]
            exI[of _ raw] exI[of _ raw_state])
          (use builder prefix_receive witness trace_candidate comp_candidate
            target_hit False in simp)
      show ?thesis
        unfolding
          checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at_def
        using inner by simp
    qed
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_with_witness_imp_header_target_or_binding_gap_witness:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
      A trace_table composition_table i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
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
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
  shows
    "checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  from
    checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE
      [OF hit]
  obtain prefix prefix_state raw raw_state where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE
        [OF hit])
  show ?thesis
  proof (cases
      "(trace_table, composition_table) \<in>
        query_header_supported_partial_table_candidates prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)")
    case True
    have header_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_header_supported_query_target
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_pair_hit_imp_header_supported_target_hit
          [OF True target_hit])
    have
      "checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    proof -
      have inner:
        "\<exists>prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            staged_query_prefix_header_supported_query_target
            (Some (((prefix, prefix_state), raw), raw_state))"
        by (intro exI[of _ prefix] exI[of _ prefix_state]
            exI[of _ raw] exI[of _ raw_state])
          (use builder prefix_receive header_hit in simp)
      show ?thesis
        unfolding
          checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at_def
        using inner by simp
    qed
    then show ?thesis by simp
  next
    case False
    have
      "checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    proof -
      have inner:
        "\<exists>trace_openings composition_openings trace_table composition_table
            prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          (trace_openings, composition_openings) \<in>
            query_header_supported_partial_opening_witnesses
              (verifier_state_from_adversary attacker_state
                (staged_proof_transcript data))
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              (staged_alphas data)
              (staged_degree data)
              (staged_composition_fri_roots data)
              (staged_composition_final data) \<and>
          partial_trace_table_candidate trace_table
            ((replicate rounds []) [i := trace_openings]) \<and>
          partial_composition_table_candidate composition_table
            ((replicate rounds []) [i := composition_openings]) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_candidate_pair_query_target_from_prefix
              trace_table composition_table)
            (Some (((prefix, prefix_state), raw), raw_state)) \<and>
          (trace_table, composition_table) \<notin>
            query_header_supported_partial_table_candidates prefix_state
              (sqp_trace_root prefix)
              (sqp_trace_fri_roots prefix)
              (sqp_trace_final prefix)
              (sqp_alphas prefix)
              (sqp_degree prefix)
              (sqp_composition_fri_roots prefix)
              (sqp_composition_final prefix)"
        by (intro exI[of _ trace_openings] exI[of _ composition_openings]
            exI[of _ trace_table] exI[of _ composition_table]
            exI[of _ prefix] exI[of _ prefix_state]
            exI[of _ raw] exI[of _ raw_state])
          (use builder prefix_receive witness trace_candidate comp_candidate
            target_hit False in simp)
      show ?thesis
        unfolding
          checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at_def
        using inner by simp
    qed
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_imp_partial_merkle_or_header_target_or_binding_gap_witness:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    and i_bound: "i < rounds"
    and trace_low:
      "\<And>trace_openings composition_openings trace_table
          composition_table.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        trace_table_low_degree trace_table"
    and comp_low:
      "\<And>trace_openings composition_openings trace_table
          composition_table.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>trace_openings composition_openings trace_table
          composition_table prefix prefix_state.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "(\<exists>result' final_state'.
      partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result', final_state'))) \<or>
     checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from
    checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_candidates_or_partial_merkle_bad
      [OF hit i_bound]
  show ?thesis
  proof
    assume
      "\<exists>result' final_state'.
        partial_merkle_inconsistency_bad ?s (Some (result', final_state'))"
    then show ?thesis by simp
  next
    assume candidates:
      "\<exists>trace_openings composition_openings trace_table
          composition_table.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses ?s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<and>
        checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
          A
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i
          (Some (((((alpha_prefix, alpha_prefix_state), data),
            attacker_state), result), final_state)) \<and>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<and>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings])"
    then obtain trace_openings composition_openings trace_table
        composition_table where witness:
        "(trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses ?s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)"
      and opening_hit:
        "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
          A
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i
          (Some (((((alpha_prefix, alpha_prefix_state), data),
            attacker_state), result), final_state))"
      and trace_candidate:
        "partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings])"
      and comp_candidate:
        "partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings])"
      by blast
    have pair_hit:
      "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
        A trace_table composition_table i
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix_imp_candidate_pair_query_hit_from_prefix
          [OF opening_hit trace_candidate comp_candidate
            trace_low[OF witness trace_candidate comp_candidate]
            comp_low[OF witness trace_candidate comp_candidate]])
        (rule not_all[OF witness trace_candidate comp_candidate])
    have
      "checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state)) \<or>
       checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_witness_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_with_witness_imp_header_target_or_binding_gap_witness
          [OF pair_hit witness trace_candidate comp_candidate])
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_imp_partial_merkle_or_single_round_header_target_or_gap_witness:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    and i_bound: "i < rounds"
    and trace_low:
      "\<And>trace_openings composition_openings trace_table
          composition_table.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        trace_table_low_degree trace_table"
    and comp_low:
      "\<And>trace_openings composition_openings trace_table
          composition_table.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>trace_openings composition_openings trace_table
          composition_table prefix prefix_state.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "(\<exists>result' final_state'.
      partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result', final_state'))) \<or>
     checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from
    checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_candidates_or_partial_merkle_bad
      [OF hit i_bound]
  show ?thesis
  proof
    assume
      "\<exists>result' final_state'.
        partial_merkle_inconsistency_bad ?s (Some (result', final_state'))"
    then show ?thesis by simp
  next
    assume candidates:
      "\<exists>trace_openings composition_openings trace_table
          composition_table.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses ?s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<and>
        checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
          A
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i
          (Some (((((alpha_prefix, alpha_prefix_state), data),
            attacker_state), result), final_state)) \<and>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<and>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings])"
    then obtain trace_openings composition_openings trace_table
        composition_table where witness:
        "(trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses ?s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)"
      and opening_hit:
        "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
          A
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i
          (Some (((((alpha_prefix, alpha_prefix_state), data),
            attacker_state), result), final_state))"
      and trace_candidate:
        "partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings])"
      and comp_candidate:
        "partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings])"
      by blast
    have pair_hit:
      "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
        A trace_table composition_table i
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix_imp_candidate_pair_query_hit_from_prefix
          [OF opening_hit trace_candidate comp_candidate
            trace_low[OF witness trace_candidate comp_candidate]
            comp_low[OF witness trace_candidate comp_candidate]])
        (rule not_all[OF witness trace_candidate comp_candidate])
    have
      "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state)) \<or>
       checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_with_witness_imp_single_round_header_target_or_gap_witness
          [OF pair_hit witness trace_candidate comp_candidate])
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_imp_header_target_or_binding_gap:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
      A trace_table composition_table i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  from
    checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE
      [OF hit]
  obtain prefix prefix_state raw raw_state where
    i_bound: "i < rounds"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE
        [OF hit])
  show ?thesis
  proof (cases
      "(trace_table, composition_table) \<in>
        query_header_supported_partial_table_candidates prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)")
    case True
    have header_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_header_supported_query_target
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_pair_hit_imp_header_supported_target_hit
          [OF True target_hit])
    have
      "checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    proof -
      have inner:
        "\<exists>prefix prefix_state raw raw_state.
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            staged_query_prefix_header_supported_query_target
            (Some (((prefix, prefix_state), raw), raw_state))"
        by (intro exI[of _ prefix] exI[of _ prefix_state]
            exI[of _ raw] exI[of _ raw_state])
          (use prefix_receive header_hit in simp)
      show ?thesis
        unfolding
          checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at_def
        using builder inner by simp
    qed
    then show ?thesis by simp
  next
    case False
    have
      "checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    proof -
      have inner:
        "\<exists>trace_table composition_table prefix prefix_state raw raw_state.
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_candidate_pair_query_target_from_prefix
              trace_table composition_table)
            (Some (((prefix, prefix_state), raw), raw_state)) \<and>
          (trace_table, composition_table) \<notin>
            query_header_supported_partial_table_candidates prefix_state
              (sqp_trace_root prefix)
              (sqp_trace_fri_roots prefix)
              (sqp_trace_final prefix)
              (sqp_alphas prefix)
              (sqp_degree prefix)
              (sqp_composition_fri_roots prefix)
              (sqp_composition_final prefix)"
        by (intro exI[of _ trace_table] exI[of _ composition_table]
            exI[of _ prefix] exI[of _ prefix_state]
            exI[of _ raw] exI[of _ raw_state])
          (use prefix_receive target_hit False in simp)
      show ?thesis
        unfolding
          checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_at_def
        using builder inner by simp
    qed
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_imp_partial_merkle_or_header_target_or_binding_gap:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    and i_bound: "i < rounds"
    and trace_low:
      "\<And>trace_openings composition_openings trace_table
          composition_table.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        trace_table_low_degree trace_table"
    and comp_low:
      "\<And>trace_openings composition_openings trace_table
          composition_table.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>trace_openings composition_openings trace_table
          composition_table prefix prefix_state.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<Longrightarrow>
        partial_trace_table_candidate trace_table
          ((replicate rounds []) [i := trace_openings]) \<Longrightarrow>
        partial_composition_table_candidate composition_table
          ((replicate rounds []) [i := composition_openings]) \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "(\<exists>result' final_state'.
      partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result', final_state'))) \<or>
     checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_at
      i A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  have base:
    "(\<exists>result' final_state'.
      partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result', final_state'))) \<or>
     (\<exists>trace_table composition_table.
      checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
        A trace_table composition_table i
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state)))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_at_imp_partial_merkle_or_candidate_pair
        [OF hit i_bound trace_low comp_low not_all])
  then show ?thesis
  proof
    assume
      "\<exists>result' final_state'.
        partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (Some (result', final_state'))"
    then show ?thesis by simp
  next
    assume
      "\<exists>trace_table composition_table.
        checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
          A trace_table composition_table i
          (Some (((((alpha_prefix, alpha_prefix_state), data),
            attacker_state), result), final_state))"
    then obtain trace_table composition_table where pair_hit:
      "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
        A trace_table composition_table i
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state))"
      by blast
    have
      "checked_staged_security_with_actual_alpha_prefix_header_supported_query_target_hit_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state)) \<or>
       checked_staged_security_with_actual_alpha_prefix_query_prefix_candidate_binding_gap_at
        i A
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_imp_header_target_or_binding_gap
          [OF pair_hit])
    then show ?thesis by simp
  qed
qed

end

end
