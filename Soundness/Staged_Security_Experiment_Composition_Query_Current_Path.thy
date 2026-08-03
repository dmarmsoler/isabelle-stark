(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Current_Path.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Current_Path
  imports Staged_Security_Experiment_Composition_Query_Current
begin

text \<open>
  Structured current-query Merkle path-output events.

  The broad @{term checked_staged_security_with_query_prefix_current_path_output_hit_at}
  event intentionally forgets why the path was relevant.  This layer keeps the
  authenticated-opening root, length, and final-state authentication evidence,
  so later Merkle/candidate arguments can distinguish ordinary verifier hashing
  from candidate drift.
\<close>

context soundness
begin

definition checked_staged_security_with_query_prefix_transcript_hit
where
  "checked_staged_security_with_query_prefix_transcript_hit out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        hash_map_output_values
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) \<inter>
          set (staged_proof_transcript data) \<noteq> {} \<or>
        hash_map_new_output_hit (set (staged_proof_transcript data))
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          final_state)"

definition checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
where
  "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
      i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        (\<exists>opn :: 'f authenticated_opening.
          opening_root opn = staged_trace_root data \<and>
          opening_length opn = scale * clength \<and>
          authenticated_opening_in final_state opn \<and>
          hash_map_new_output_hit
            (merkle_path_target_roots final_state
              (staged_trace_root data)
              (scale * clength)
              (opening_index opn)
              (opening_value opn)
              (opening_path opn))
            prefix_state final_state))"

definition checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
where
  "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
      i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        staged_composition_fri_roots data \<noteq> [] \<and>
        (\<exists>opn :: 'f authenticated_opening.
          opening_root opn = hd (staged_composition_fri_roots data) \<and>
          opening_length opn = scale * clength \<and>
          authenticated_opening_in final_state opn \<and>
          hash_map_new_output_hit
            (merkle_path_target_roots final_state
          (hd (staged_composition_fri_roots data))
          (scale * clength)
          (opening_index opn)
          (opening_value opn)
          (opening_path opn))
            prefix_state final_state))"

lemma checked_staged_security_with_query_prefix_structured_path_hit_imp_transcript_hit_on_support:
  assumes i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out \<or>
       checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i out"
  shows "checked_staged_security_with_query_prefix_transcript_hit out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_query_prefix_current_trace_path_output_hit_at_def
      checked_staged_security_with_query_prefix_current_composition_path_output_hit_at_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
    "out =
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)"
    by (cases packed) (auto split: prod.splits)
  have mapped_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i \<bind>
            (\<lambda>packed. return (snd packed)))
          adversary_initial_state)"
    unfolding out_eq
    by (rule set_dist_bindI[OF support[unfolded out_eq]]) simp
  have projection:
    "checked_staged_security_experiment_with_query_prefix_data_state A i \<bind>
        (\<lambda>packed. return (snd packed)) =
      checked_staged_security_experiment_with_data_state A"
    by (rule checked_staged_security_experiment_with_query_prefix_data_state_projection
        [OF i_bound])
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    using mapped_support unfolding projection .
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  have verifier:
    "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  have transcript_split:
    "hash_map_output_values ?s \<inter> set (staged_proof_transcript data)
        \<noteq> {} \<or>
     hash_map_new_output_hit (set (staged_proof_transcript data))
        ?s final_state"
    by (rule verify_monad_trace_root_target_preexisting_or_new[OF verifier])
      simp
  show ?thesis
    unfolding out_eq checked_staged_security_with_query_prefix_transcript_hit_def
    using transcript_split by simp
qed

lemma checked_staged_security_with_query_prefix_transcript_hit_bound_from_data_state:
  assumes i_bound: "i < rounds"
    and pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      checked_staged_security_with_query_prefix_transcript_hit
      adversary_initial_state \<le> P + R"
proof -
  let ?E =
    "\<lambda>out.
      staged_security_with_data_state_transcript_pre_hit out \<or>
      staged_security_with_data_state_transcript_new_hit out"
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow> ?E None
    | Some (packed, t) \<Rightarrow> ?E (Some (snd packed, t))"
  have projected_eq:
    "?projected = checked_staged_security_with_query_prefix_transcript_hit"
    unfolding
      checked_staged_security_with_query_prefix_transcript_hit_def
      staged_security_with_data_state_transcript_pre_hit_def
      staged_security_with_data_state_transcript_new_hit_def
    by (rule ext) (auto split: option.splits prod.splits)
  have projection:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      ?E
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      checked_staged_security_with_query_prefix_transcript_hit
      adversary_initial_state"
    using
        checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound, of A ?E]
    unfolding projected_eq .
  have union_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      ?E
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state"
    by (rule wp_event_union_bound)
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      ?E
      adversary_initial_state \<le> P + R"
    by (rule order_trans[OF union_bound])
      (intro add_mono pre_bound new_bound)
  then show ?thesis
    unfolding projection .
qed

lemma checked_staged_security_with_query_prefix_current_trace_path_output_hit_at_bound_from_transcript:
  assumes i_bound: "i < rounds"
    and pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
      adversary_initial_state \<le> P + R"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      checked_staged_security_with_query_prefix_transcript_hit
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state A i)
              adversary_initial_state)"
      and hit:
        "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i out"
    show "checked_staged_security_with_query_prefix_transcript_hit out"
      by (rule
          checked_staged_security_with_query_prefix_structured_path_hit_imp_transcript_hit_on_support
          [OF i_bound support])
        (use hit in simp)
  qed
  have transcript_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      checked_staged_security_with_query_prefix_transcript_hit
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_query_prefix_transcript_hit_bound_from_data_state
        [OF i_bound pre_bound new_bound])
  show ?thesis
    by (rule order_trans[OF event_le transcript_bound])
qed

lemma checked_staged_security_with_query_prefix_current_composition_path_output_hit_at_bound_from_transcript:
  assumes i_bound: "i < rounds"
    and pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
      adversary_initial_state \<le> P + R"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      checked_staged_security_with_query_prefix_transcript_hit
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state A i)
              adversary_initial_state)"
      and hit:
        "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i out"
    show "checked_staged_security_with_query_prefix_transcript_hit out"
      by (rule
          checked_staged_security_with_query_prefix_structured_path_hit_imp_transcript_hit_on_support
          [OF i_bound support])
        (use hit in simp)
  qed
  have transcript_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      checked_staged_security_with_query_prefix_transcript_hit
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_query_prefix_transcript_hit_bound_from_data_state
        [OF i_bound pre_bound new_bound])
  show ?thesis
    by (rule order_trans[OF event_le transcript_bound])
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_imp_prefix_or_structured_path_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i out"
  shows
    "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_def
      checked_staged_security_with_query_prefix_authenticated_opening_hit_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
    "out =
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)"
    by (cases packed) (auto split: prod.splits)
  from hit obtain trace_openings composition_openings where current:
    "checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i out"
    unfolding checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_def
    by blast
  have ext: "prefix_state \<le> final_state"
    using support unfolding out_eq
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_prefix_extends_final
        [OF wf controlled i_bound])
  have comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    and trace_table:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and comp_table:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings final_state"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
    using current unfolding out_eq
      checked_staged_security_with_query_prefix_authenticated_opening_hit_def
    by simp_all
  have trace_pullback:
    "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings prefix_state \<or>
     (\<exists>opn \<in> set trace_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots final_state (staged_trace_root data)
          (scale * clength)
          (opening_index opn)
          (opening_value opn)
          (opening_path opn)) prefix_state final_state)"
    by (rule partial_authenticated_table_pullback_or_new_output_hit
        [OF ext trace_table])
  then show ?thesis
  proof
    assume trace_prefix:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings prefix_state"
    have comp_pullback:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
          (scale * clength) composition_openings prefix_state \<or>
       (\<exists>opn \<in> set composition_openings.
        hash_map_new_output_hit
          (merkle_path_target_roots final_state
            (hd (staged_composition_fri_roots data))
            (scale * clength)
            (opening_index opn)
            (opening_value opn)
            (opening_path opn)) prefix_state final_state)"
      by (rule partial_authenticated_table_pullback_or_new_output_hit
          [OF ext comp_table])
    then show ?thesis
    proof
      assume comp_prefix:
        "partial_authenticated_table (hd (staged_composition_fri_roots data))
          (scale * clength) composition_openings prefix_state"
      have
        "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
          i out"
        unfolding out_eq
          checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_def
          checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_def
        using comp_nonempty trace_prefix comp_prefix consistent by auto
      then show ?thesis by simp
    next
      assume comp_path:
        "\<exists>opn \<in> set composition_openings.
          hash_map_new_output_hit
            (merkle_path_target_roots final_state
              (hd (staged_composition_fri_roots data))
              (scale * clength)
              (opening_index opn)
              (opening_value opn)
              (opening_path opn)) prefix_state final_state"
      then obtain opn where opn_in: "opn \<in> set composition_openings"
        and path_hit:
          "hash_map_new_output_hit
            (merkle_path_target_roots final_state
              (hd (staged_composition_fri_roots data))
              (scale * clength)
              (opening_index opn)
              (opening_value opn)
              (opening_path opn)) prefix_state final_state"
        by blast
      have auth: "authenticated_opening_in final_state opn"
        using comp_table opn_in
        unfolding partial_authenticated_table_def by blast
      have root_eq:
        "opening_root opn = hd (staged_composition_fri_roots data)"
        using comp_table opn_in
        unfolding partial_authenticated_table_def by blast
      have len_eq: "opening_length opn = scale * clength"
        using comp_table opn_in
        unfolding partial_authenticated_table_def by blast
      have
        "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i out"
        unfolding out_eq
          checked_staged_security_with_query_prefix_current_composition_path_output_hit_at_def
        using comp_nonempty auth root_eq len_eq path_hit by auto
      then show ?thesis by simp
    qed
  next
    assume trace_path:
      "\<exists>opn \<in> set trace_openings.
        hash_map_new_output_hit
          (merkle_path_target_roots final_state (staged_trace_root data)
            (scale * clength)
            (opening_index opn)
            (opening_value opn)
            (opening_path opn)) prefix_state final_state"
    then obtain opn where opn_in: "opn \<in> set trace_openings"
      and path_hit:
        "hash_map_new_output_hit
          (merkle_path_target_roots final_state (staged_trace_root data)
            (scale * clength)
            (opening_index opn)
            (opening_value opn)
            (opening_path opn)) prefix_state final_state"
      by blast
    have auth: "authenticated_opening_in final_state opn"
      using trace_table opn_in
      unfolding partial_authenticated_table_def by blast
    have root_eq: "opening_root opn = staged_trace_root data"
      using trace_table opn_in
      unfolding partial_authenticated_table_def by blast
    have len_eq: "opening_length opn = scale * clength"
      using trace_table opn_in
      unfolding partial_authenticated_table_def by blast
    have
      "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out"
      unfolding out_eq
        checked_staged_security_with_query_prefix_current_trace_path_output_hit_at_def
      using auth root_eq len_eq path_hit by auto
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_candidate_pair_or_structured_path_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_authenticated_opening_hit
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
    "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?out =
    "Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state)"
  have ext: "prefix_state \<le> final_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_prefix_extends_final
        [OF wf controlled i_bound support])
  have alphas_eq: "staged_alphas data = sqp_alphas prefix"
    by (rule checked_staged_security_with_query_prefix_data_state_alphas_eq
        [OF support])
  have comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    and trace_table_final:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and comp_table_final:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings final_state"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
    using hit
    unfolding checked_staged_security_with_query_prefix_authenticated_opening_hit_def
    by simp_all
  have trace_pullback:
    "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings prefix_state \<or>
     (\<exists>opn \<in> set trace_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots final_state (staged_trace_root data)
          (scale * clength) (opening_index opn) (opening_value opn)
          (opening_path opn)) prefix_state final_state)"
    by (rule partial_authenticated_table_pullback_or_new_output_hit
        [OF ext trace_table_final])
  then show ?thesis
  proof
    assume trace_prefix:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings prefix_state"
    have comp_pullback:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
          (scale * clength) composition_openings prefix_state \<or>
       (\<exists>opn \<in> set composition_openings.
        hash_map_new_output_hit
          (merkle_path_target_roots final_state
            (hd (staged_composition_fri_roots data))
            (scale * clength) (opening_index opn) (opening_value opn)
            (opening_path opn)) prefix_state final_state)"
      by (rule partial_authenticated_table_pullback_or_new_output_hit
          [OF ext comp_table_final])
    then show ?thesis
    proof
      assume comp_prefix:
        "partial_authenticated_table (hd (staged_composition_fri_roots data))
          (scale * clength) composition_openings prefix_state"
      have opening_target:
        "index (to_nat raw) \<in>
          staged_query_prefix_candidate_opening_query_target_from_prefix
            ((replicate rounds []) [i := trace_openings])
            ((replicate rounds []) [i := composition_openings])
            i prefix prefix_state"
        unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
        by (rule partial_query_success_indices_atI,
            rule partial_query_round_consistent_single_roundI
              [OF i_bound])
          (use consistent alphas_eq in simp)
      have opening_subset:
        "staged_query_prefix_candidate_opening_query_target_from_prefix
            ((replicate rounds []) [i := trace_openings])
            ((replicate rounds []) [i := composition_openings])
            i prefix prefix_state \<subseteq>
         staged_query_prefix_candidate_pair_query_target_from_prefix
            trace_table composition_table prefix prefix_state"
        by (rule
            staged_query_prefix_candidate_opening_query_target_from_prefix_subset_candidate_pair_from_prefix
            [OF trace_candidate comp_candidate trace_low comp_low not_all])
      have pair_hit:
        "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
          trace_table composition_table ?out"
        unfolding
          checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_def
          checked_staged_security_with_query_prefix_dynamic_index_hit_def
          checked_staged_query_prefix_dynamic_index_hit_def
        using opening_target opening_subset by auto
      then show ?thesis by simp
    next
      assume comp_path:
        "\<exists>opn \<in> set composition_openings.
          hash_map_new_output_hit
            (merkle_path_target_roots final_state
              (hd (staged_composition_fri_roots data))
              (scale * clength) (opening_index opn) (opening_value opn)
              (opening_path opn)) prefix_state final_state"
      then obtain opn where opn_in: "opn \<in> set composition_openings"
        and path_hit:
          "hash_map_new_output_hit
            (merkle_path_target_roots final_state
              (hd (staged_composition_fri_roots data))
              (scale * clength) (opening_index opn) (opening_value opn)
              (opening_path opn)) prefix_state final_state"
        by blast
      have auth: "authenticated_opening_in final_state opn"
        using comp_table_final opn_in
        unfolding partial_authenticated_table_def by blast
      have root_eq:
        "opening_root opn = hd (staged_composition_fri_roots data)"
        using comp_table_final opn_in
        unfolding partial_authenticated_table_def by blast
      have len_eq: "opening_length opn = scale * clength"
        using comp_table_final opn_in
        unfolding partial_authenticated_table_def by blast
      have
        "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i ?out"
        unfolding
          checked_staged_security_with_query_prefix_current_composition_path_output_hit_at_def
        using comp_nonempty auth root_eq len_eq path_hit by auto
      then show ?thesis by simp
    qed
  next
    assume trace_path:
      "\<exists>opn \<in> set trace_openings.
        hash_map_new_output_hit
          (merkle_path_target_roots final_state (staged_trace_root data)
            (scale * clength) (opening_index opn) (opening_value opn)
            (opening_path opn)) prefix_state final_state"
    then obtain opn where opn_in: "opn \<in> set trace_openings"
      and path_hit:
        "hash_map_new_output_hit
          (merkle_path_target_roots final_state (staged_trace_root data)
            (scale * clength) (opening_index opn) (opening_value opn)
            (opening_path opn)) prefix_state final_state"
      by blast
    have auth: "authenticated_opening_in final_state opn"
      using trace_table_final opn_in
      unfolding partial_authenticated_table_def by blast
    have root_eq: "opening_root opn = staged_trace_root data"
      using trace_table_final opn_in
      unfolding partial_authenticated_table_def by blast
    have len_eq: "opening_length opn = scale * clength"
      using trace_table_final opn_in
      unfolding partial_authenticated_table_def by blast
    have
      "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i ?out"
      unfolding
        checked_staged_security_with_query_prefix_current_trace_path_output_hit_at_def
      using auth root_eq len_eq path_hit by auto
    then show ?thesis by simp
  qed
qed

definition staged_query_prefix_inconsistent_candidate_pair_query_target
where
  "staged_query_prefix_inconsistent_candidate_pair_query_target
      trace_table composition_table prefix prefix_state =
    (if all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)
     then {}
     else staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table prefix prefix_state)"

lemma staged_query_prefix_inconsistent_candidate_pair_query_target_bound:
  assumes trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
  shows
    "staged_query_prefix_inconsistent_candidate_pair_query_target
        trace_table composition_table prefix prefix_state
      \<subseteq> query_sample_space \<and>
     nnreal
      (card
        (staged_query_prefix_inconsistent_candidate_pair_query_target
          trace_table composition_table prefix prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof (cases
    "all_queries_consistent trace_table composition_table (sqp_alphas prefix)")
  case True
  then show ?thesis
    unfolding staged_query_prefix_inconsistent_candidate_pair_query_target_def
    by simp
next
  case False
  have subset:
    "staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
        composition_table prefix prefix_state \<subseteq> query_sample_space"
    by (rule staged_query_prefix_candidate_pair_query_target_from_prefix_subset)
  have frac:
    "nnreal
      (card
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table prefix prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
    by (rule
        staged_query_prefix_candidate_pair_query_target_from_prefix_fraction_bound
        [OF trace_low comp_low False])
  show ?thesis
    unfolding staged_query_prefix_inconsistent_candidate_pair_query_target_def
    using False subset frac by simp
qed

lemma checked_staged_security_with_query_prefix_inconsistent_candidate_pair_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
        (staged_query_prefix_inconsistent_candidate_pair_query_target
          trace_table composition_table))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
  by (rule
      checked_staged_security_with_query_prefix_dynamic_index_hit_bound_from_fraction
      [OF wf controlled i_bound])
    (use
      staged_query_prefix_inconsistent_candidate_pair_query_target_bound
        [OF trace_low comp_low] in blast)

lemma checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_imp_inconsistent_target:
  assumes hit:
      "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
        trace_table composition_table
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table
        (sqp_alphas prefix)"
  shows
    "checked_staged_security_with_query_prefix_dynamic_index_hit
      (staged_query_prefix_inconsistent_candidate_pair_query_target
        trace_table composition_table)
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
  using hit not_all
  unfolding
    checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_def
    checked_staged_security_with_query_prefix_dynamic_index_hit_def
    checked_staged_query_prefix_dynamic_index_hit_def
    staged_query_prefix_inconsistent_candidate_pair_query_target_def
  by simp

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_bound_from_candidate_pair_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>prefix prefix_state raw raw_state data attacker_state result
          final_state.
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
    and pair_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
          trace_table composition_table)
        adversary_initial_state \<le> P"
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le> P + T + C"
proof -
  let ?M =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Pair =
    "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
      trace_table composition_table"
  let ?Trace =
    "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
      i"
  let ?Comp =
    "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
      i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Pair out \<or> ?Trace out \<or> ?Comp out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit:
      "checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i out"
    show "?Pair out \<or> ?Trace out \<or> ?Comp out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_query_prefix_authenticated_opening_hit_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
        "out =
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      have support_some:
        "Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
          set_dist (execute ?M adversary_initial_state)"
        using support out_eq by simp
      show ?thesis
        unfolding out_eq
        by (rule
            checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_candidate_pair_or_structured_path_on_support
            [OF wf controlled i_bound support_some])
          (use hit[unfolded out_eq] trace_candidate comp_candidate
            trace_low comp_low not_all[OF support_some] in simp_all)
    qed
  qed
  have union_le:
    "wp_event ?M (\<lambda>out. ?Pair out \<or> ?Trace out \<or> ?Comp out)
      adversary_initial_state \<le>
     wp_event ?M ?Pair adversary_initial_state +
     (wp_event ?M ?Trace adversary_initial_state +
      wp_event ?M ?Comp adversary_initial_state)"
  proof -
    have
      "wp_event ?M (\<lambda>out. ?Pair out \<or> ?Trace out \<or> ?Comp out)
        adversary_initial_state \<le>
       wp_event ?M ?Pair adversary_initial_state +
       wp_event ?M (\<lambda>out. ?Trace out \<or> ?Comp out)
        adversary_initial_state"
      by (rule wp_event_union_bound)
    also have
      "... \<le>
       wp_event ?M ?Pair adversary_initial_state +
       (wp_event ?M ?Trace adversary_initial_state +
        wp_event ?M ?Comp adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis .
  qed
  have sum_bound:
    "wp_event ?M ?Pair adversary_initial_state +
      (wp_event ?M ?Trace adversary_initial_state +
       wp_event ?M ?Comp adversary_initial_state) \<le> P + T + C"
  proof -
    have path_sum:
      "wp_event ?M ?Trace adversary_initial_state +
       wp_event ?M ?Comp adversary_initial_state \<le> T + C"
      by (rule add_mono[OF trace_path_bound composition_path_bound])
    have
      "wp_event ?M ?Pair adversary_initial_state +
        (wp_event ?M ?Trace adversary_initial_state +
         wp_event ?M ?Comp adversary_initial_state) \<le> P + (T + C)"
      by (rule add_mono[OF pair_bound path_sum])
    then show ?thesis
      by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF event_le order_trans[OF union_le sum_bound]])
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_bound_from_inconsistent_candidate_pair_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all_on_hit:
      "\<And>prefix prefix_state raw raw_state data attacker_state result
          final_state.
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        checked_staged_security_with_query_prefix_authenticated_opening_hit
          trace_openings composition_openings i
          (Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + T + C"
proof -
  let ?M =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Pair =
    "checked_staged_security_with_query_prefix_dynamic_index_hit
      (staged_query_prefix_inconsistent_candidate_pair_query_target
        trace_table composition_table)"
  let ?Trace =
    "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
      i"
  let ?Comp =
    "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
      i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Pair out \<or> ?Trace out \<or> ?Comp out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit:
      "checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i out"
    show "?Pair out \<or> ?Trace out \<or> ?Comp out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_query_prefix_authenticated_opening_hit_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
        "out =
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      have support_some:
        "Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
          set_dist (execute ?M adversary_initial_state)"
        using support out_eq by simp
      have not_all:
        "\<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
        by (rule not_all_on_hit[OF support_some])
          (use hit out_eq in simp)
      have split:
        "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
            trace_table composition_table
            (Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state)) \<or>
         checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
            i
            (Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state)) \<or>
         checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
            i
            (Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state))"
        by (rule
            checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_candidate_pair_or_structured_path_on_support
            [OF wf controlled i_bound support_some])
          (use hit[unfolded out_eq] trace_candidate comp_candidate
            trace_low comp_low not_all in simp_all)
      then show ?thesis
      proof
        assume pair:
          "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
            trace_table composition_table
            (Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state))"
        have "?Pair
            (Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state))"
          by (rule
              checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_imp_inconsistent_target
              [OF pair not_all])
        then show ?thesis
          unfolding out_eq by simp
      next
        assume
          "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
            i
            (Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state)) \<or>
           checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
            i
            (Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state))"
        then show ?thesis
          unfolding out_eq by simp
      qed
    qed
  qed
  have pair_bound:
    "wp_event ?M ?Pair adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_inconsistent_candidate_pair_hit_bound
        [OF wf controlled i_bound trace_low comp_low])
  have union_le:
    "wp_event ?M (\<lambda>out. ?Pair out \<or> ?Trace out \<or> ?Comp out)
      adversary_initial_state \<le>
     wp_event ?M ?Pair adversary_initial_state +
     (wp_event ?M ?Trace adversary_initial_state +
      wp_event ?M ?Comp adversary_initial_state)"
  proof -
    have
      "wp_event ?M (\<lambda>out. ?Pair out \<or> ?Trace out \<or> ?Comp out)
        adversary_initial_state \<le>
       wp_event ?M ?Pair adversary_initial_state +
       wp_event ?M (\<lambda>out. ?Trace out \<or> ?Comp out)
        adversary_initial_state"
      by (rule wp_event_union_bound)
    also have
      "... \<le>
       wp_event ?M ?Pair adversary_initial_state +
       (wp_event ?M ?Trace adversary_initial_state +
        wp_event ?M ?Comp adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis .
  qed
  have sum_bound:
    "wp_event ?M ?Pair adversary_initial_state +
      (wp_event ?M ?Trace adversary_initial_state +
       wp_event ?M ?Comp adversary_initial_state) \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      (T + C)"
    by (intro add_mono pair_bound add_mono trace_path_bound
        composition_path_bound)
  have rhs_eq:
    "(staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      (T + C) =
     staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + T + C"
    by (simp add: add.assoc)
  have bound:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      (T + C)"
    by (rule order_trans[OF event_le order_trans[OF union_le sum_bound]])
  show ?thesis
    using bound rhs_eq by simp
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_bound_from_candidate_pair_budgets_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
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
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + T + C"
proof -
  have pair_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
        trace_table composition_table)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_bound_from_budgets
        [OF wf controlled i_bound trace_low comp_low not_all])
  have not_all_support:
    "\<And>prefix prefix_state raw raw_state data attacker_state result
        final_state.
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state
              A i)
            adversary_initial_state) \<Longrightarrow>
      \<not> all_queries_consistent trace_table composition_table
        (sqp_alphas prefix)"
  proof -
    fix prefix prefix_state raw raw_state data attacker_state result final_state
    assume support:
      "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state
              A i)
            adversary_initial_state)"
    have head:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
      using support
      unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    have prefix_support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
      by (rule checked_staged_query_prefix_receive_with_state_prefix_support
          [OF head])
    show
      "\<not> all_queries_consistent trace_table composition_table
        (sqp_alphas prefix)"
      by (rule not_all[OF prefix_support])
  qed
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_authenticated_opening_hit_bound_from_candidate_pair_and_structured_paths
        [OF wf controlled i_bound trace_candidate comp_candidate trace_low
          comp_low not_all_support pair_bound trace_path_bound
          composition_path_bound])
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
        adversary_initial_state \<le> P"
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le> P + T + C"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Prefix =
    "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i"
  let ?Trace =
    "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i"
  let ?Composition =
    "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Prefix out \<or> ?Trace out \<or> ?Composition out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_imp_prefix_or_structured_path_on_support
        [OF wf controlled i_bound])
  have first_union:
    "wp_event ?M (\<lambda>out. ?Prefix out \<or> ?Trace out \<or> ?Composition out)
      adversary_initial_state \<le>
     wp_event ?M ?Prefix adversary_initial_state +
     wp_event ?M (\<lambda>out. ?Trace out \<or> ?Composition out)
      adversary_initial_state"
    by (rule wp_event_union_bound)
  have second_union:
    "wp_event ?M (\<lambda>out. ?Trace out \<or> ?Composition out)
      adversary_initial_state \<le>
     wp_event ?M ?Trace adversary_initial_state +
     wp_event ?M ?Composition adversary_initial_state"
    by (rule wp_event_union_bound)
  have path_sum_bound:
    "wp_event ?M (\<lambda>out. ?Trace out \<or> ?Composition out)
      adversary_initial_state \<le> T + C"
    by (rule order_trans[OF second_union])
      (intro add_mono trace_path_bound composition_path_bound)
  have sum_bound:
    "wp_event ?M ?Prefix adversary_initial_state +
     wp_event ?M (\<lambda>out. ?Trace out \<or> ?Composition out)
      adversary_initial_state \<le> P + (T + C)"
    by (intro add_mono prefix_bound path_sum_bound)
  have union_sum_bound:
    "wp_event ?M (\<lambda>out. ?Prefix out \<or> ?Trace out \<or> ?Composition out)
      adversary_initial_state \<le> P + T + C"
    by (rule order_trans[OF first_union])
      (use sum_bound in \<open>simp add: add.assoc\<close>)
  show ?thesis
    by (rule order_trans[OF event_le])
      (rule union_sum_bound)
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_prefix_target_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event (checked_staged_query_prefix_receive_with_state A i)
          (checked_staged_query_prefix_dynamic_index_hit
            staged_query_prefix_prefix_authenticated_opening_target)
          adversary_initial_state \<le> P i"
    and trace_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
          adversary_initial_state \<le> T i"
    and composition_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
          adversary_initial_state \<le> C i"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. P i + T i + C i)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_prefix_current_rounds
    [OF wf controlled])
  fix i
  assume i_bound: "i < rounds"
  have prefix_hit_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
      adversary_initial_state \<le> P i"
    by (rule
        checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_dynamic_target
        [OF wf controlled i_bound prefix_bound[OF i_bound]])
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le> P i + T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_structured_paths
        [OF wf controlled i_bound prefix_hit_bound trace_path_bound[OF i_bound]
          composition_path_bound[OF i_bound]])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_trace_indices_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_frac:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (card
            (staged_query_prefix_prefix_authenticated_trace_indices prefix
              prefix_state)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
    and trace_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
          adversary_initial_state \<le> T i"
    and composition_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
          adversary_initial_state \<le> C i"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound + T i + C i)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_prefix_target_and_structured_paths
    [OF wf controlled _ trace_path_bound composition_path_bound])
  fix i
  assume i_bound: "i < rounds"
  show "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
  proof (rule
      checked_staged_query_prefix_prefix_authenticated_target_hit_bound_from_trace_indices
      [OF wf controlled i_bound])
    fix prefix prefix_state
    assume support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    show
      "nnreal
        (card
          (staged_query_prefix_prefix_authenticated_trace_indices prefix
            prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      by (rule trace_frac[OF i_bound support])
  qed
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_trace_indices_structured_paths_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_frac:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (card
            (staged_query_prefix_prefix_authenticated_trace_indices prefix
              prefix_state)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
    and trace_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
          adversary_initial_state \<le> T i"
    and composition_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
          adversary_initial_state \<le> C i"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound + T i + C i) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  let ?Q =
    "(\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + T i + C i)"
  have query_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> ?Q"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_trace_indices_and_structured_paths
        [OF wf controlled trace_frac trace_path_bound composition_path_bound])
  have without_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le> 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_bound
        [OF wf controlled])
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> ?Q + 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_query_and_without_query
        [OF query_bound without_bound])
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (?Q + 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_composition_candidate_drift_and_budgets
        [OF wf controlled drift_bound])
  then show ?thesis
    by simp
qed

end

end
