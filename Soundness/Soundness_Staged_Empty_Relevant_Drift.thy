(*  Title:      Stark/Soundness_Staged_Empty_Relevant_Drift.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Empty_Relevant_Drift
  imports Soundness_Staged_Relevant_Drift
begin

text \<open>
  Empty-header-specific relevant-drift packaging.

  This theory is kept downstream of the broader relevant-drift layer so that
  the latter remains focused on reusable drift decompositions.
\<close>

context soundness
begin

definition checked_staged_security_with_actual_alpha_prefix_witnessed_sparse_cross_bad
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_witnessed_sparse_cross_bad
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>fr f_fri_roots f_final trace_table final_state
              trace_openings trace_table' final_state' trace_openings'.
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table final_state
                trace_openings \<and>
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table' final_state'
                trace_openings' \<and>
              trace_table \<noteq> trace_table' \<and>
              \<not> partial_openings_cross_cover_all_indices trace_openings
                trace_openings'))"

definition checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>fr f_fri_roots f_final trace_table final_state
              trace_openings trace_table' final_state' trace_openings'.
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table final_state
                trace_openings \<and>
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table' final_state'
                trace_openings' \<and>
              trace_table \<noteq> trace_table' \<and>
              (merkle_hash_value_conflict final_state final_state' \<or>
               hash_map_output_collision
                (merkle_hash_state_merge final_state final_state'))))"

definition checked_staged_security_with_actual_alpha_prefix_witnessed_local_collision_bad
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_witnessed_local_collision_bad
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>fr f_fri_roots f_final trace_table final_state
              trace_openings.
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table final_state
                trace_openings \<and>
              hash_map_output_collision final_state))"

definition checked_staged_security_with_actual_alpha_prefix_witnessed_coupling_bad
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_witnessed_coupling_bad
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>fr f_fri_roots f_final trace_table final_state
              trace_openings trace_table' final_state' trace_openings'.
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table final_state
                trace_openings \<and>
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table' final_state'
                trace_openings' \<and>
              trace_table \<noteq> trace_table' \<and>
              merkle_hash_pairwise_coupling_bad final_state final_state'))"

lemma checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad_split:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_witnessed_local_collision_bad
      out \<or>
     checked_staged_security_with_actual_alpha_prefix_witnessed_coupling_bad
      out"
proof (cases out)
  case None
  then show ?thesis
    using assms
    unfolding
      checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state data attacker_state result final_state0
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state0)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from assms obtain fr f_fri_roots f_final trace_table final_state
      trace_openings trace_table' final_state' trace_openings' where
    witness:
      "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
        f_fri_roots f_final trace_table final_state trace_openings"
    and witness':
      "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
        f_fri_roots f_final trace_table' final_state' trace_openings'"
    and distinct: "trace_table \<noteq> trace_table'"
    and pair_bad:
      "merkle_hash_value_conflict final_state final_state' \<or>
       hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad_def
      Let_def
    by auto
  have split:
    "hash_map_output_collision final_state \<or>
     hash_map_output_collision final_state' \<or>
     merkle_hash_pairwise_coupling_bad final_state final_state'"
    by (rule merkle_hash_pairwise_bad_imp_local_collision_or_coupling_bad
        [OF pair_bad])
  then show ?thesis
  proof
    assume collision: "hash_map_output_collision final_state"
    have
      "checked_staged_security_with_actual_alpha_prefix_witnessed_local_collision_bad
        out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_witnessed_local_collision_bad_def
        Let_def
      apply simp
      apply (intro exI conjI)
       apply (rule witness)
      apply (rule collision)
      done
    then show ?thesis by simp
  next
    assume rest:
      "hash_map_output_collision final_state' \<or>
       merkle_hash_pairwise_coupling_bad final_state final_state'"
    then show ?thesis
    proof
      assume collision': "hash_map_output_collision final_state'"
      have
        "checked_staged_security_with_actual_alpha_prefix_witnessed_local_collision_bad
          out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_witnessed_local_collision_bad_def
        Let_def
        apply simp
        apply (intro exI conjI)
         apply (rule witness')
        apply (rule collision')
        done
      then show ?thesis by simp
    next
      assume coupling:
        "merkle_hash_pairwise_coupling_bad final_state final_state'"
      have
        "checked_staged_security_with_actual_alpha_prefix_witnessed_coupling_bad
          out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_witnessed_coupling_bad_def
        Let_def
        apply simp
        apply (intro exI conjI)
           apply (rule witness)
          apply (rule witness')
         apply (rule distinct)
        apply (rule coupling)
        done
      then show ?thesis by simp
    qed
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad_le_local_or_coupling:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witnessed_local_collision_bad
    adversary_initial_state +
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witnessed_coupling_bad
    adversary_initial_state"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?H =
    checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
  let ?L =
    checked_staged_security_with_actual_alpha_prefix_witnessed_local_collision_bad
  let ?C =
    checked_staged_security_with_actual_alpha_prefix_witnessed_coupling_bad
  have "wp_event ?M ?H adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?L out \<or> ?C out) adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad_split)
  also have "... \<le>
      wp_event ?M ?L adversary_initial_state +
      wp_event ?M ?C adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad_split:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_witnessed_sparse_cross_bad
      out \<or>
     checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
      out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad_def
    checked_staged_security_with_actual_alpha_prefix_witnessed_sparse_cross_bad_def
    checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad_def
    alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad_def
    alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad_def
    Let_def
  by (auto split: option.splits prod.splits; blast)

lemma checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad_le_sparse_or_merkle_side:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witnessed_sparse_cross_bad
    adversary_initial_state +
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
    adversary_initial_state"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?W =
    checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
  let ?S =
    checked_staged_security_with_actual_alpha_prefix_witnessed_sparse_cross_bad
  let ?H =
    checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
  have "wp_event ?M ?W adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?S out \<or> ?H out) adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad_split)
  also have "... \<le>
      wp_event ?M ?S adversary_initial_state +
      wp_event ?M ?H adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

definition empty_header_partial_trace_candidate_nonunique
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "empty_header_partial_trace_candidate_nonunique s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      \<not> (\<exists>trace_table0.
        partial_trace_table_candidates trace_openings \<subseteq>
          {trace_table0}))"

lemma composition_alpha_partial_opening_union_hit_with_empty_header_split:
  assumes hit:
    "composition_alpha_partial_opening_union_hit_with_empty_header s out"
  shows
    "composition_alpha_bad_set_hit_with_empty_composition_header_candidates
        s out \<or>
     empty_header_partial_trace_candidate_nonunique s out"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table where partial:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and as_union:
      "as \<in> partial_trace_opening_alpha_union_bad_sets trace_openings"
    using hit
    unfolding composition_alpha_partial_opening_union_hit_with_empty_header_def
    by blast
  from as_union obtain trace_table' where candidate':
      "trace_table' \<in> partial_trace_table_candidates trace_openings"
    and as_bad': "as \<in> composition_trace_bad_alpha_space trace_table'"
    unfolding partial_trace_opening_alpha_union_bad_sets_def by blast
  have candidate:
    "trace_table \<in> partial_trace_table_candidates trace_openings"
    using partial
    unfolding accepted_with_empty_composition_header_candidates_def
      partial_trace_table_candidates_def
    by simp
  show ?thesis
  proof (cases
      "\<exists>trace_table0.
        partial_trace_table_candidates trace_openings \<subseteq>
          {trace_table0}")
    case True
    then obtain trace_table0 where subset:
      "partial_trace_table_candidates trace_openings \<subseteq>
        {trace_table0}"
      by blast
    have trace_eq: "trace_table = trace_table0"
      using subset candidate by blast
    have trace'_eq: "trace_table' = trace_table0"
      using subset candidate' by blast
    have "as \<in> composition_trace_bad_alpha_space trace_table"
      using as_bad' trace_eq trace'_eq by simp
    then have
      "composition_alpha_bad_set_hit_with_empty_composition_header_candidates
        s out"
      unfolding
        composition_alpha_bad_set_hit_with_empty_composition_header_candidates_def
      using partial by blast
    then show ?thesis by simp
  next
    case False
    have "empty_header_partial_trace_candidate_nonunique s out"
      unfolding empty_header_partial_trace_candidate_nonunique_def
      using partial False by blast
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_nonunique_imp_witnessed_cross_or_merkle_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and nonunique:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        empty_header_partial_trace_candidate_nonunique out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
      out"
proof (cases out)
  case None
  then show ?thesis
    using nonunique
    unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state),
          result), final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have verifier:
    "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    using support
    unfolding out_eq
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have local_nonunique:
    "empty_header_partial_trace_candidate_nonunique ?s
      (Some (result, final_state))"
    using nonunique
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      Let_def
    by simp
  then obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table where empty:
      "accepted_with_empty_composition_header_candidates ?s
        (Some (result, final_state)) fr f_fri_roots f_final as dg final
        trace_query_idxs trace_openings trace_table composition_table"
    and not_unique_partial:
      "\<not> (\<exists>trace_table0.
        partial_trace_table_candidates trace_openings \<subseteq>
          {trace_table0})"
    unfolding empty_header_partial_trace_candidate_nonunique_def
    by blast
  from empty obtain rest where header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg []
        final rest"
    and trace_partial:
      "accepted_with_partial_trace_openings ?s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    unfolding accepted_with_empty_composition_header_candidates_def
    by blast
  have partial_subset:
    "partial_trace_table_candidates trace_openings \<subseteq>
      alpha_header_supported_partial_trace_table_candidates ?s fr f_fri_roots
        f_final"
  proof
    fix trace_table'
    assume
      "trace_table' \<in> partial_trace_table_candidates trace_openings"
    then have candidate':
      "partial_trace_table_candidate trace_table' trace_openings"
      unfolding partial_trace_table_candidates_def by simp
    show
      "trace_table' \<in>
        alpha_header_supported_partial_trace_table_candidates ?s fr
          f_fri_roots f_final"
      unfolding alpha_header_supported_partial_trace_table_candidates_def
      by (intro CollectI exI[of _ "Some (result, final_state)"]
          exI[of _ trace_query_idxs] exI[of _ trace_openings]
          exI[of _ as] exI[of _ dg] exI[of _ "[]"]
          exI[of _ final] exI[of _ rest] conjI)
        (use verifier trace_partial candidate' header in simp_all)
  qed
  have not_unique_header:
    "\<not> (\<exists>trace_table0.
      alpha_header_supported_partial_trace_table_candidates ?s fr
        f_fri_roots f_final \<subseteq> {trace_table0})"
  proof
    assume
      "\<exists>trace_table0.
        alpha_header_supported_partial_trace_table_candidates ?s fr
          f_fri_roots f_final \<subseteq> {trace_table0}"
    then obtain trace_table0 where header_subset:
      "alpha_header_supported_partial_trace_table_candidates ?s fr
        f_fri_roots f_final \<subseteq> {trace_table0}"
      by blast
    have
      "partial_trace_table_candidates trace_openings \<subseteq>
        {trace_table0}"
      using partial_subset header_subset by blast
    then show False
      using not_unique_partial by blast
  qed
  have not_unique_witnessed:
    "\<not> (\<exists>trace_table0.
      alpha_header_supported_witnessed_partial_trace_table_candidates ?s fr
        f_fri_roots f_final \<subseteq> {trace_table0})"
    using not_unique_header
    by (simp add: alpha_header_supported_witnessed_candidates_eq_candidates)
  have
    "alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
      ?s fr f_fri_roots f_final"
    by (rule
        alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad_if_not_singleton
        [OF not_unique_witnessed])
  then have
    "alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad ?s"
    unfolding
      alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad_def
    by blast
  then show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad_def
      Let_def
    by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_nonunique_le_witnessed_cross_or_merkle:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_partial_trace_candidate_nonunique)
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
    adversary_initial_state"
  by (rule wp_event_mono_on_support)
    (rule
      checked_staged_security_with_actual_alpha_prefix_empty_header_nonunique_imp_witnessed_cross_or_merkle_on_support)

definition checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
    out \<longleftrightarrow>
    checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
      composition_trace_bad_alpha_space out \<and>
    checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header out"

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_le_fixed_or_nonunique:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
    adversary_initial_state +
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_partial_trace_candidate_nonunique)
    adversary_initial_state"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?fixed =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates"
  let ?nonunique =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_partial_trace_candidate_nonunique"
  have event_le:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?fixed out \<or> ?nonunique out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_def
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        split: option.splits prod.splits
        dest:
          composition_alpha_partial_opening_union_hit_with_empty_header_split)
  also have "... \<le>
      wp_event ?M ?fixed adversary_initial_state +
      wp_event ?M ?nonunique adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_le_fixed_or_witnessed_cross:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
    adversary_initial_state +
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
    adversary_initial_state"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?fixed =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates"
  let ?nonunique =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_partial_trace_candidate_nonunique"
  have base:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
      adversary_initial_state \<le>
     wp_event ?M ?fixed adversary_initial_state +
     wp_event ?M ?nonunique adversary_initial_state"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_le_fixed_or_nonunique)
  have nonunique_bound:
    "wp_event ?M ?nonunique adversary_initial_state \<le>
     wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
      adversary_initial_state"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_nonunique_le_witnessed_cross_or_merkle)
  show ?thesis
    by (rule order_trans[OF base])
      (intro add_mono order_refl nonunique_bound)
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_bound_from_fixed_and_witnessed_cross:
  assumes fixed_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
      adversary_initial_state \<le> F + X"
  by (rule order_trans[
      OF
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_le_fixed_or_witnessed_cross])
    (intro add_mono fixed_bound cross_bound)

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_bound_from_fixed_and_nonunique:
  assumes fixed_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and nonunique_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          empty_header_partial_trace_candidate_nonunique)
        adversary_initial_state \<le> N"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
      adversary_initial_state \<le> F + N"
  by (rule order_trans[
      OF
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_le_fixed_or_nonunique])
    (intro add_mono fixed_bound nonunique_bound)

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_le_relevant_drift:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
    adversary_initial_state"
  by (rule wp_event_mono)
    (auto simp:
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_def
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_def)

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_bound_from_relevant_drift:
  assumes drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
      adversary_initial_state \<le> D"
  by (rule order_trans[
      OF
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_le_relevant_drift
        drift_bound])

lemma checked_staged_security_with_actual_alpha_prefix_fixed_empty_alpha_hit_imp_prefix_or_not_prefix_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and fixed_hit:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_bad_set_hit_with_empty_composition_header_candidates
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space out"
proof (cases out)
  case None
  then show ?thesis
    using fixed_hit
    unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state),
          result), final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have verify_out:
    "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    using support
    unfolding out_eq
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have local_fixed:
    "composition_alpha_bad_set_hit_with_empty_composition_header_candidates ?s
      (Some (result, final_state))"
    using fixed_hit
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      Let_def
    by simp
  then obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table rest where empty:
      "accepted_with_empty_composition_header_candidates ?s
        (Some (result, final_state)) fr f_fri_roots f_final as dg final
        trace_query_idxs trace_openings trace_table composition_table"
    and header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg []
        final rest"
    and trace_partial:
      "accepted_with_partial_trace_openings ?s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and as_bad:
      "as \<in> composition_trace_bad_alpha_space trace_table"
    unfolding
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates_def
      accepted_with_empty_composition_header_candidates_def
    by blast
  from verify_monad_accepted_transcript_shape[OF verify_out]
  obtain as' query_idxs where shape':
    "accepted_transcript_shape ?s (Some (result, final_state)) as'
      query_idxs"
    by blast
  from shape' obtain result' final_state' fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where out_shape:
      "Some (result, final_state) = Some (result', final_state')"
    and header':
      "verifier_header_transcript ?s fr' f_fri_roots' f_final' as' dg'
        composition_fri_roots' final' rest'"
    by (elim accepted_transcript_shape_header_query_extraction)
  have as'_eq: "as' = as"
    using verifier_header_transcript_unique[OF header' header] by simp
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as
      query_idxs"
    using shape' as'_eq by simp
  have header_union:
    "as \<in>
      alpha_header_supported_partial_union_bad_sets ?s
        composition_trace_bad_alpha_space fr f_fri_roots f_final"
  proof -
    have candidate:
      "trace_table \<in>
        alpha_header_supported_partial_trace_table_candidates ?s fr
          f_fri_roots f_final"
      unfolding alpha_header_supported_partial_trace_table_candidates_def
      by (intro CollectI exI[of _ "Some (result, final_state)"]
          exI[of _ trace_query_idxs] exI[of _ trace_openings]
          exI[of _ as] exI[of _ dg] exI[of _ "[]"]
          exI[of _ final] exI[of _ rest] conjI)
        (use verify_out trace_partial trace_candidate header in simp_all)
    show ?thesis
      unfolding alpha_header_supported_partial_union_bad_sets_def
      using candidate as_bad
        composition_trace_bad_alpha_space_subset_alpha_space[of trace_table]
      by auto
  qed
  have builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  proof -
    have data_support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
          [OF support[unfolded out_eq]])
    from checked_staged_security_experiment_with_data_state_outcomeE
        [OF data_support]
    show ?thesis
      by blast
  qed
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  have prefix_root_eq: "staged_trace_root data = fst prefix"
    using support out_eq
    unfolding checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
      checked_staged_transcript_with_alpha_prefix_program_def
      checked_staged_after_alpha_prefix_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have as_eq: "as = staged_alphas data"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  have fr_eq: "fr = staged_trace_root data"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  show ?thesis
  proof (cases
      "as \<in> alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space fr")
    case True
    have
      "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_def
        Let_def
      using True as_eq fr_eq prefix_root_eq by simp
    then show ?thesis by simp
  next
    case not_prefix: False
    have not_bound:
      "alpha_header_partial_candidate_not_prefix_bound prefix_state ?s fr
        f_fri_roots f_final"
      by (rule alpha_header_partial_union_hit_not_prefix_hit_imp_not_prefix_bound
          [OF header_union not_prefix])
    have
      "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space out"
      unfolding out_eq
      by (rule
          checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_boundI
          [OF refl shape header header_union not_prefix not_bound])
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_fixed_empty_alpha_hit_le_prefix_or_not_prefix:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Fixed =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates"
  let ?Prefix =
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
      composition_trace_bad_alpha_space"
  let ?NotPrefix =
    "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
      composition_trace_bad_alpha_space"
  have event_le:
    "wp_event ?M ?Fixed adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Prefix out \<or> ?NotPrefix out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_actual_alpha_prefix_fixed_empty_alpha_hit_imp_prefix_or_not_prefix_on_support
        [OF wf controlled])
  also have "... \<le>
      wp_event ?M ?Prefix adversary_initial_state +
      wp_event ?M ?NotPrefix adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_imp_prefix_prequery_or_empty_relevant_drift_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
        out"
proof -
  have partial:
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      composition_trace_bad_alpha_space out"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_partial_alpha_hit_imp_partial_header_bad_set_hit_on_support
        [OF support hit])
  have fresh_or_prequery:
    "checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space out"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_imp_fresh_or_prequery
        [OF partial])
  then show ?thesis
  proof
    assume fresh:
      "checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
        composition_trace_bad_alpha_space out"
    have prefix_or_drift:
      "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space out \<or>
       checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space out"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit_imp_prefix_or_drift
          [OF fresh])
    then show ?thesis
    proof
      assume
        "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space out"
      then show ?thesis by simp
    next
      assume drift:
        "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space out"
      have
        "checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
          out"
        unfolding
          checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_def
        using drift hit by simp
      then show ?thesis by simp
    qed
  next
    assume
      "checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space out"
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_bound_from_empty_relevant_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
        adversary_initial_state \<le> D"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Prefix =
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
      composition_trace_bad_alpha_space"
  let ?Prequery =
    "checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
      composition_trace_bad_alpha_space"
  let ?Drift =
    "checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift"
  let ?Hit =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header"
  let ?P =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  let ?Q =
    "staged_phase_relation_error size
      (staged_alpha_search_queries budgets 0)"
  have transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets
        [OF wf controlled])
  have prefix_bound:
    "wp_event ?M ?Prefix adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have prequery_bound:
    "wp_event ?M ?Prequery adversary_initial_state \<le> ?Q"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_vector_alpha_prequery_accounting
        [OF wf controlled])
  have "wp_event ?M ?Hit adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?Prefix out \<or> ?Prequery out \<or> ?Drift out \<or> False)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (use
        checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_imp_prefix_prequery_or_empty_relevant_drift_on_support
          [of _ A] in blast)
  also have "... \<le>
      wp_event ?M ?Prefix adversary_initial_state +
      wp_event ?M ?Prequery adversary_initial_state +
      wp_event ?M ?Drift adversary_initial_state +
      wp_event ?M (\<lambda>_. False) adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le> ?P + ?Q + D + 0"
    by (intro add_mono prefix_bound prequery_bound drift_bound)
      (simp add: wp_event_def wp_def dist_expect_def)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_data_state_empty_header_composition_randomization_bound_from_empty_relevant_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
        adversary_initial_state \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?random =
    "staged_security_with_data_state_verifier_event
      composition_randomization_bad_with_empty_composition_header_candidates"
  let ?alpha =
    "staged_security_with_data_state_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header"
  have alpha_projected:
    "wp_event ?M ?alpha adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
      adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection)
  have alpha_bound:
    "wp_event ?M ?alpha adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D"
    unfolding alpha_projected
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_alpha_hit_bound_from_empty_relevant_drift_and_budgets
        [OF wf controlled drift_bound])
  have "wp_event ?M ?random adversary_initial_state \<le>
      wp_event ?M ?alpha adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_alpha_bad_set_hit_with_empty_header_imp_partial_opening_union_hit
          composition_randomization_bad_with_empty_composition_header_candidates_imp_alpha_hit
        split: option.splits prod.splits)
  also have "... \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D"
    by (rule alpha_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_empty_header_bad_event_bound_from_empty_relevant_drift_trace_fri_and_query:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
        adversary_initial_state \<le> D"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> empty_query_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?degree =
    "?E composition_degree_bad_with_empty_composition_header_candidates"
  let ?random =
    "?E composition_randomization_bad_with_empty_composition_header_candidates"
  let ?trace =
    "?E trace_fri_bad_with_empty_composition_header_candidates"
  let ?query =
    "?E query_bad_with_empty_composition_header_candidates"
  let ?bad = "?E soundness_bad_event_partial_candidate_empty_header"
  have degree_false: "?degree = (\<lambda>out. False)"
    by (rule ext)
      (auto simp: staged_security_with_data_state_verifier_event_def
        composition_degree_bad_with_empty_composition_header_candidates_false
        split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    unfolding degree_false wp_event_def wp_def dist_expect_def by simp
  have random_bound:
    "wp_event ?M ?random adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D"
    by (rule
        checked_staged_security_with_data_state_empty_header_composition_randomization_bound_from_empty_relevant_drift_and_budgets
        [OF wf controlled drift_bound])
  have "wp_event ?M ?bad adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?degree out \<or> ?random out \<or> ?trace out \<or>
          ?query out)
        adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume bad: "?bad out"
    show "?degree out \<or> ?random out \<or> ?trace out \<or> ?query out"
    proof (cases out)
      case None
      then show ?thesis
        using bad
        unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      have local_bad:
        "soundness_bad_event_partial_candidate_empty_header ?s
          (Some (result, final_state))"
        using bad
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
      then consider
          (comp)
            "composition_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state))"
        | (trace)
            "trace_fri_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state))"
        | (query)
            "query_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state))"
        unfolding soundness_bad_event_partial_candidate_empty_header_def
        by blast
      then show ?thesis
      proof cases
        case comp
        then have comp_split:
          "composition_degree_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state)) \<or>
           composition_randomization_bad_with_empty_composition_header_candidates
              ?s (Some (result, final_state))"
          by (rule
              composition_bad_with_empty_composition_header_candidates_split
              [OF false_statement])
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          using comp_split by (auto split: option.splits prod.splits)
      next
        case trace
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          by simp
      next
        case query
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          by simp
      qed
    qed
  qed
  also have "... \<le>
      wp_event ?M ?degree adversary_initial_state +
      wp_event ?M ?random adversary_initial_state +
      wp_event ?M ?trace adversary_initial_state +
      wp_event ?M ?query adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le>
      0 +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        D) +
      trace_fri_error + empty_query_error"
    by (intro add_mono degree_bound random_bound trace_fri_bound query_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_current_query_prefix_rounds_from_empty_relevant_drift_current_empty:
  fixes trace_fri_error' composition_fri_error' D empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_fri_error'"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error)"
proof -
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_aligned_partial_candidate_randomization_bound_from_query_prefix_current_rounds
        [OF wf controlled round_bound])
  have current_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds
        [OF round_bound wf controlled])
  have query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_current_partial_opening_hit
          current_query_bound])
      (use wf controlled in simp_all)
  have merkle_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
  have empty_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> empty_query_error"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_empty_query_bad_le_current_empty_opening_hit_at_zero[
          OF wf controlled] current_empty_bound])
  have empty_header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_empty_relevant_drift_trace_fri_and_query
        [OF false_statement wf controlled drift_bound empty_trace_fri_bound
          empty_query_bound])
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds. C i) +
      trace_fri_error' + composition_fri_error' +
      (\<Sum>i<rounds. C i) +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        D + trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
  then show ?thesis .
qed

lemma checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_structured_query_from_empty_relevant_drift_current_empty:
  fixes trace_fri_error' composition_fri_error' D empty_query_error
      header_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_fri_error'"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and header_query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
          A)
        adversary_initial_state \<le> header_query_error"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error' + composition_fri_error' +
    header_query_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error)"
proof -
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_aligned_partial_candidate_randomization_bound_from_query_prefix_current_rounds
        [OF wf controlled round_bound])
  have query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> header_query_error"
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_header_authenticated_candidate_opening_query_hit_from_prefix
        [OF wf controlled header_query_bound])
  have merkle_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
  have empty_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> empty_query_error"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_empty_query_bad_le_current_empty_opening_hit_at_zero[
          OF wf controlled] current_empty_bound])
  have empty_header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_empty_relevant_drift_trace_fri_and_query
        [OF false_statement wf controlled drift_bound empty_trace_fri_bound
          empty_query_bound])
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      (hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
        (\<Sum>i<rounds. C i) + trace_fri_error' +
        composition_fri_error' + header_query_error) +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        D + trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_current_query_prefix_rounds_from_empty_relevant_drift_current_empty_single_query_charge:
  fixes trace_fri_error' composition_fri_error' D empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_fri_error'"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error' + composition_fri_error' +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error)"
proof -
  have current_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds
        [OF round_bound wf controlled])
  have merkle_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
  have empty_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> empty_query_error"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_empty_query_bad_le_current_empty_opening_hit_at_zero[
          OF wf controlled] current_empty_bound])
  have empty_header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      D + trace_fri_error + empty_query_error"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_empty_relevant_drift_trace_fri_and_query
        [OF false_statement wf controlled drift_bound empty_trace_fri_bound
          empty_query_bound])
  have partial_candidate_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_aligned_transcript_partial_candidate_with_aligned_randomization_and_merkle)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds. C i) + trace_fri_error' + composition_fri_error'"
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_partial_candidate_aligned_randomization_with_merkle_current_query_union_bound
        [OF wf controlled merkle_bound current_query_bound trace_fri_bound
          comp_fri_bound])
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      (hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
        (\<Sum>i<rounds. C i) + trace_fri_error' +
        composition_fri_error') +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        D + trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_partial_candidate_aligned_randomization_and_empty_header_bounds
        [OF false_statement partial_candidate_bound empty_header_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

end

end
