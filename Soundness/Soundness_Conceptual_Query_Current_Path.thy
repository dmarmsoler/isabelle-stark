(*  Title:      Stark/Soundness_Conceptual_Query_Current_Path.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Conceptual_Query_Current_Path
  imports
    Soundness_Conceptual_Query_Current
    Staged_Security_Experiment_Composition_Query_Current_Path
begin

text \<open>
  Integration of conceptual prefix-query targets with the existing structured
  current-query path split.
\<close>

context soundness
begin

definition checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
where
  "checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
      i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i out \<and>
    checked_staged_security_with_query_prefix_conceptual_context_residual_at
      out"

definition checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
where
  "checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
      trace_default composition_default i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i out \<and>
    checked_staged_security_with_query_prefix_conceptual_default_context_residual_at
      trace_default composition_default out"

definition checked_staged_security_with_query_prefix_candidate_pair_default_agreement_gap
where
  "checked_staged_security_with_query_prefix_candidate_pair_default_agreement_gap
      trace_table composition_table out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        \<not> query_prefix_candidate_defaults_agree_with_authenticated_values
          trace_table composition_table prefix prefix_state)"

definition checked_staged_security_with_query_prefix_candidate_pair_sampled_default_agreement_gap
where
  "checked_staged_security_with_query_prefix_candidate_pair_sampled_default_agreement_gap
      trace_table composition_table out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        \<not> query_prefix_candidate_defaults_agree_at_query trace_table
          composition_table (index (to_nat raw)) prefix prefix_state)"

definition checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
where
  "checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
      trace_table composition_table i out \<longleftrightarrow>
    (\<exists>trace_openings composition_openings.
      checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i out \<and>
      partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings]) \<and>
      partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings]))"

lemma checked_staged_security_with_query_prefix_candidate_pair_hit_imp_conceptual_default_or_agreement_gap:
  assumes hit:
      "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
        trace_table composition_table
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and trace_len: "length trace_table = scale * clength"
    and composition_len: "length composition_table = scale * clength"
  shows
    "checked_staged_security_with_query_prefix_conceptual_default_target_hit
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_candidate_pair_default_agreement_gap
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof (cases
    "query_prefix_candidate_defaults_agree_with_authenticated_values
      trace_table composition_table prefix prefix_state")
  case True
  have subset:
    "staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
        composition_table prefix prefix_state \<subseteq>
     staged_query_prefix_conceptual_default_query_target trace_table
        composition_table prefix prefix_state"
    by (rule
        staged_query_prefix_candidate_pair_query_target_from_prefix_subset_conceptual_default_if_prefix_agrees
        [OF clean trace_len composition_len True])
  have
    "checked_staged_security_with_query_prefix_conceptual_default_target_hit
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    using hit subset
    unfolding
      checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_def
      checked_staged_security_with_query_prefix_conceptual_default_target_hit_def
      checked_staged_security_with_query_prefix_dynamic_index_hit_def
      checked_staged_query_prefix_dynamic_index_hit_def
    by auto
  then show ?thesis by simp
next
  case False
  then have
    "checked_staged_security_with_query_prefix_candidate_pair_default_agreement_gap
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    unfolding
      checked_staged_security_with_query_prefix_candidate_pair_default_agreement_gap_def
    by simp
  then show ?thesis by simp
qed

lemma checked_staged_security_with_query_prefix_candidate_pair_hit_imp_conceptual_default_or_sampled_agreement_gap:
  assumes hit:
      "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
        trace_table composition_table
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
    and trace_len: "length trace_table = scale * clength"
    and composition_len: "length composition_table = scale * clength"
    and default_trace_low:
      "trace_table_low_degree
        (query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_table)"
    and default_composition_low:
      "composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_table)"
    and default_not_all:
      "\<not> all_queries_consistent
        (query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_table)
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_table)
        (sqp_alphas prefix)"
  shows
    "checked_staged_security_with_query_prefix_conceptual_default_target_hit
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_candidate_pair_sampled_default_agreement_gap
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof (cases
    "query_prefix_candidate_defaults_agree_at_query trace_table
      composition_table (index (to_nat raw)) prefix prefix_state")
  case True
  have raw_hit:
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
        composition_table prefix prefix_state"
    using hit
    unfolding
      checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_def
      checked_staged_security_with_query_prefix_dynamic_index_hit_def
      checked_staged_query_prefix_dynamic_index_hit_def
    by simp
  have default_raw_hit:
    "index (to_nat raw) \<in>
      staged_query_prefix_conceptual_default_query_target trace_table
        composition_table prefix prefix_state"
    by (rule
        query_prefix_candidate_pair_query_hit_imp_conceptual_default_if_agrees_at_query
        [OF raw_hit trace_len composition_len True default_trace_low
          default_composition_low default_not_all])
  have
    "checked_staged_security_with_query_prefix_conceptual_default_target_hit
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    unfolding
      checked_staged_security_with_query_prefix_conceptual_default_target_hit_def
      checked_staged_security_with_query_prefix_dynamic_index_hit_def
      checked_staged_query_prefix_dynamic_index_hit_def
    using default_raw_hit by simp
  then show ?thesis by simp
next
  case False
  then have
    "checked_staged_security_with_query_prefix_candidate_pair_sampled_default_agreement_gap
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    unfolding
      checked_staged_security_with_query_prefix_candidate_pair_sampled_default_agreement_gap_def
    by simp
  then show ?thesis by simp
qed

lemma checked_staged_security_with_query_prefix_candidate_pair_hit_imp_conceptual_default_if_final_merkle_bound:
  assumes hit:
      "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
        trace_table composition_table
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
    and prefix_clean: "\<not> hash_map_output_collision prefix_state"
    and final_clean: "\<not> hash_map_output_collision final_state"
    and ext: "prefix_state \<le> final_state"
    and trace_bind:
      "merkle_root_binds_table (sqp_trace_root prefix) trace_table
        final_state"
    and composition_bind:
      "merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
        composition_table final_state"
    and trace_len: "length trace_table = scale * clength"
    and composition_len: "length composition_table = scale * clength"
  shows
    "checked_staged_security_with_query_prefix_conceptual_default_target_hit
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  have subset:
    "staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
        composition_table prefix prefix_state \<subseteq>
     staged_query_prefix_conceptual_default_query_target trace_table
        composition_table prefix prefix_state"
    by (rule
        staged_query_prefix_candidate_pair_query_target_from_prefix_subset_conceptual_default_if_final_merkle_bound
        [OF prefix_clean final_clean ext trace_bind composition_bind trace_len
          composition_len])
  show ?thesis
    using hit subset
    unfolding
      checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_def
      checked_staged_security_with_query_prefix_conceptual_default_target_hit_def
      checked_staged_security_with_query_prefix_dynamic_index_hit_def
      checked_staged_query_prefix_dynamic_index_hit_def
    by auto
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_conceptual_default_or_residual_or_structured_path_on_support:
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
  shows
    "checked_staged_security_with_query_prefix_conceptual_default_target_hit
      trace_table composition_table
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
      trace_table composition_table i
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
  have current_hit:
    "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i ?out"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_atI
        [OF hit])
  show ?thesis
  proof (cases
      "\<not> hash_map_output_collision prefix_state \<and>
       trace_table_low_degree
        (query_prefix_trace_conceptual_table_with_default prefix
          prefix_state trace_table) \<and>
       composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_table) \<and>
       \<not> all_queries_consistent
        (query_prefix_trace_conceptual_table_with_default prefix
          prefix_state trace_table)
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_table)
        (sqp_alphas prefix)")
    case False
    then have
      "checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_table composition_table i ?out"
      unfolding
        checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_def
        checked_staged_security_with_query_prefix_conceptual_default_context_residual_at_def
      using current_hit by simp
    then show ?thesis by simp
  next
    case True
    then have clean:
        "\<not> hash_map_output_collision prefix_state"
      and default_trace_low:
        "trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_table)"
      and default_composition_low:
        "composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_table)"
      and default_not_all:
        "\<not> all_queries_consistent
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_table)
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_table)
          (sqp_alphas prefix)"
      by blast+
    have ext: "prefix_state \<le> final_state"
      by (rule
          checked_staged_security_experiment_with_query_prefix_data_state_prefix_extends_final
          [OF wf controlled i_bound support])
    have alphas_eq: "staged_alphas data = sqp_alphas prefix"
      by (rule checked_staged_security_with_query_prefix_data_state_alphas_eq
          [OF support])
    have trace_root_eq: "staged_trace_root data = sqp_trace_root prefix"
      using support
      unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
        checked_staged_after_query_prefix_receive_with_verifier_def
        checked_staged_after_query_prefix_receive_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    have composition_roots_eq:
      "staged_composition_fri_roots data = sqp_composition_fri_roots prefix"
      using support
      unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
        checked_staged_after_query_prefix_receive_with_verifier_def
        checked_staged_after_query_prefix_receive_def
      by (auto elim!: set_dist_bindE split: prod.splits)
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
      assume trace_prefix_staged:
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
        assume comp_prefix_staged:
          "partial_authenticated_table (hd (staged_composition_fri_roots data))
            (scale * clength) composition_openings prefix_state"
        have trace_prefix:
          "partial_authenticated_table (sqp_trace_root prefix)
            (scale * clength) trace_openings prefix_state"
          using trace_prefix_staged trace_root_eq by simp
        have composition_prefix:
          "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
            (scale * clength) composition_openings prefix_state"
          using comp_prefix_staged composition_roots_eq by simp
        have consistent_prefix:
          "partial_query_openings_consistent trace_openings
            composition_openings (sqp_alphas prefix) (index (to_nat raw))"
          using consistent alphas_eq by simp
        have target:
          "index (to_nat raw) \<in>
            staged_query_prefix_conceptual_default_query_target trace_table
              composition_table prefix prefix_state"
          by (rule
              query_prefix_current_openings_imp_conceptual_default_query_target
              [OF clean i_bound trace_prefix composition_prefix
                consistent_prefix trace_candidate comp_candidate
                default_trace_low default_composition_low default_not_all])
        have
          "checked_staged_security_with_query_prefix_conceptual_default_target_hit
            trace_table composition_table ?out"
          unfolding
            checked_staged_security_with_query_prefix_conceptual_default_target_hit_def
            checked_staged_security_with_query_prefix_dynamic_index_hit_def
            checked_staged_query_prefix_dynamic_index_hit_def
          using target by simp
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
qed

lemma checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_imp_conceptual_default_or_residual_or_structured_path_on_support:
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
      "checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i out"
  shows
    "checked_staged_security_with_query_prefix_conceptual_default_target_hit
        trace_table composition_table out \<or>
     checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_table composition_table i out \<or>
     checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_def
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
  from hit[unfolded out_eq
      checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_def]
  obtain trace_openings composition_openings where opening_hit:
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
    by blast
  have support':
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    using support unfolding out_eq .
  show ?thesis
    unfolding out_eq
    by (rule
        checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_conceptual_default_or_residual_or_structured_path_on_support
        [OF wf controlled i_bound support' opening_hit trace_candidate
          comp_candidate])
qed

lemma checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_imp_current:
  assumes
    "checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
      i out"
  shows
    "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i out"
  using assms
  unfolding
    checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_def
  by simp

lemma checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_imp_residual:
  assumes
    "checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
      i out"
  shows
    "checked_staged_security_with_query_prefix_conceptual_context_residual_at
      out"
  using assms
  unfolding
    checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_def
  by simp

definition checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at
where
  "checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at
      i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        hash_map_output_collision prefix_state)"

definition checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
where
  "checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
      i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        \<not> trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state) \<or>
        \<not> composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table prefix prefix_state) \<or>
        all_queries_consistent
          (query_prefix_trace_conceptual_table prefix prefix_state)
          (query_prefix_composition_conceptual_table prefix prefix_state)
          (sqp_alphas prefix))"

definition checked_staged_security_with_query_prefix_conceptual_trace_low_degree_bad_at
where
  "checked_staged_security_with_query_prefix_conceptual_trace_low_degree_bad_at
      i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
      i out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        \<not> trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state))"

definition checked_staged_security_with_query_prefix_conceptual_composition_low_degree_bad_at
where
  "checked_staged_security_with_query_prefix_conceptual_composition_low_degree_bad_at
      i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
      i out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        \<not> composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table prefix prefix_state))"

definition checked_staged_security_with_query_prefix_conceptual_alpha_bad_set_hit_at
where
  "checked_staged_security_with_query_prefix_conceptual_alpha_bad_set_hit_at
      i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
      i out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        sqp_alphas prefix \<in>
          composition_trace_bad_alpha_space
            (query_prefix_trace_conceptual_table prefix prefix_state))"

lemma checked_staged_query_prefix_with_state_alphas_length:
  assumes support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
  shows "length (sqp_alphas prefix) = length spec"
proof -
  from support have prefix_out:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_challenge_prefix_program A i)
          adversary_initial_state)"
    unfolding checked_staged_query_prefix_with_state_def
    by (auto elim!: set_dist_bindE)
  from prefix_out obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4
      s5 as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 query_start query_chunks where
    alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s5)"
    and prefix_eq:
      "prefix =
        \<lparr>sqp_trace_root = fr,
         sqp_trace_fri_roots = trace_roots,
         sqp_trace_fri_challenges = trace_bs,
         sqp_trace_final = trace_final,
         sqp_alphas = as,
         sqp_degree = dg,
         sqp_composition_fri_roots = composition_roots,
         sqp_composition_fri_challenges = composition_bs,
         sqp_composition_final = composition_final,
         sqp_query_chunks = query_chunks\<rparr>"
    using prefix_out
    by (elim checked_staged_query_challenge_prefix_program_outcomeE)
  have "length as = length spec"
    using staged_alpha_program_alignment[OF alpha_out] by simp
  then show ?thesis
    unfolding prefix_eq by simp
qed

lemma checked_staged_security_with_query_prefix_data_state_prefix_support:
  assumes support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
  shows
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
proof -
  from support have receive_support:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  then show ?thesis
    by (rule checked_staged_query_prefix_receive_with_state_prefix_support)
qed

lemma checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at_cases_on_support:
  assumes false_statement: "\<not> exists_valid_trace"
    and support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
        i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "\<not> trace_table_low_degree
      (query_prefix_trace_conceptual_table prefix prefix_state) \<or>
     \<not> composition_table_low_degree maxDegree
      (query_prefix_composition_conceptual_table prefix prefix_state) \<or>
     sqp_alphas prefix \<in>
      composition_trace_bad_alpha_space
        (query_prefix_trace_conceptual_table prefix prefix_state)"
proof -
  let ?trace = "query_prefix_trace_conceptual_table prefix prefix_state"
  let ?composition =
    "query_prefix_composition_conceptual_table prefix prefix_state"
  from hit have residual:
    "\<not> trace_table_low_degree ?trace \<or>
     \<not> composition_table_low_degree maxDegree ?composition \<or>
     all_queries_consistent ?trace ?composition (sqp_alphas prefix)"
    unfolding
      checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at_def
    by simp
  show ?thesis
  proof (cases "trace_table_low_degree ?trace")
    case False
    then show ?thesis by simp
  next
    case trace_low: True
    show ?thesis
    proof (cases "composition_table_low_degree maxDegree ?composition")
      case False
      then show ?thesis by simp
    next
      case composition_low: True
      from residual trace_low composition_low have all_queries:
        "all_queries_consistent ?trace ?composition (sqp_alphas prefix)"
        by simp
      have prefix_support:
        "Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state)"
        by (rule
            checked_staged_security_with_query_prefix_data_state_prefix_support
            [OF support])
      have alpha_len: "length (sqp_alphas prefix) = length spec"
        by (rule checked_staged_query_prefix_with_state_alphas_length
            [OF prefix_support])
      have
        "sqp_alphas prefix \<in>
          composition_trace_bad_alpha_space ?trace"
        by (rule low_degree_all_queries_consistent_imp_composition_trace_bad_alpha_space
            [OF false_statement alpha_len trace_low composition_low
              all_queries])
      then show ?thesis by simp
    qed
  qed
qed

lemma checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at_split_on_support:
  assumes false_statement: "\<not> exists_valid_trace"
    and support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
        i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "checked_staged_security_with_query_prefix_conceptual_trace_low_degree_bad_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_conceptual_composition_low_degree_bad_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_conceptual_alpha_bad_set_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
  using
    checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at_cases_on_support
      [OF false_statement support hit] hit
  unfolding
    checked_staged_security_with_query_prefix_conceptual_trace_low_degree_bad_at_def
    checked_staged_security_with_query_prefix_conceptual_composition_low_degree_bad_at_def
    checked_staged_security_with_query_prefix_conceptual_alpha_bad_set_hit_at_def
  by simp

lemma checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at_bound_from_split:
  assumes false_statement: "\<not> exists_valid_trace"
    and trace_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_trace_low_degree_bad_at
          i)
        adversary_initial_state \<le> T"
    and composition_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_composition_low_degree_bad_at
          i)
        adversary_initial_state \<le> C"
    and alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_alpha_bad_set_hit_at
          i)
        adversary_initial_state \<le> P"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
        i)
      adversary_initial_state \<le> T + C + P"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Trace =
    "checked_staged_security_with_query_prefix_conceptual_trace_low_degree_bad_at
      i"
  let ?Composition =
    "checked_staged_security_with_query_prefix_conceptual_composition_low_degree_bad_at
      i"
  let ?Alpha =
    "checked_staged_security_with_query_prefix_conceptual_alpha_bad_set_hit_at
      i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
        i)
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Trace out \<or> ?Composition out \<or> ?Alpha out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit:
      "checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
        i out"
    show "?Trace out \<or> ?Composition out \<or> ?Alpha out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
        "out =
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      have support':
        "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist (execute ?M adversary_initial_state)"
        using support unfolding out_eq .
      have hit':
        "checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
          i
          (Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state))"
        using hit unfolding out_eq .
      show ?thesis
        unfolding out_eq
        by (rule
            checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at_split_on_support
            [OF false_statement support' hit'])
    qed
  qed
  also have "... \<le>
      wp_event ?M ?Trace adversary_initial_state +
      wp_event ?M ?Composition adversary_initial_state +
      wp_event ?M ?Alpha adversary_initial_state"
  proof -
    have "... \<le>
        wp_event ?M ?Trace
          adversary_initial_state +
        wp_event ?M (\<lambda>out. ?Composition out \<or> ?Alpha out)
          adversary_initial_state"
      by (rule wp_event_union_bound
          [where P = ?Trace
            and Q = "\<lambda>out. ?Composition out \<or> ?Alpha out"])
    also have "... \<le>
        wp_event ?M ?Trace adversary_initial_state +
        (wp_event ?M ?Composition adversary_initial_state +
          wp_event ?M ?Alpha adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  also have "... \<le> T + C + P"
    by (intro add_mono trace_bound composition_bound alpha_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_split:
  assumes
    "checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
      i out"
  shows
    "checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at
      i out \<or>
     checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
      i out"
  using assms
  unfolding
    checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_def
    checked_staged_security_with_query_prefix_conceptual_context_residual_at_def
    checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at_def
    checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at_def
  by (cases out) (auto split: prod.splits)

lemma checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at
        i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
proof -
  have i_le: "i \<le> rounds"
    using i_bound by simp
  have prefix_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      checked_staged_query_prefix_hash_map_output_collision
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    by (rule checked_staged_query_prefix_hash_map_output_collision_bound
        [OF wf controlled i_le])
  show ?thesis
  proof (rule
      checked_staged_security_experiment_with_query_prefix_data_state_bound_by_prefix
        [OF prefix_bound])
    show
      "checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at
        i None \<Longrightarrow>
       checked_staged_query_prefix_hash_map_output_collision None"
      unfolding
        checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at_def
        checked_staged_query_prefix_hash_map_output_collision_def
      by simp
  next
    fix prefix_out t out
    assume
      "Some (prefix_out, t) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
      and cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>prefix_state.
                checked_staged_after_query_prefix_receive_with_verifier A i
                  prefix_out \<bind>
                (\<lambda>result. return ((prefix_out, prefix_state), result))))
            t)"
      and event:
      "checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at
        i out"
    show
      "checked_staged_query_prefix_hash_map_output_collision
        (Some (prefix_out, t))"
      using cont event
      unfolding
        checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at_def
        checked_staged_query_prefix_hash_map_output_collision_def
      by (auto elim!: set_dist_bindE split: option.splits prod.splits)
  qed
qed

lemma checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_imp_prefix_collision_on_support:
  assumes default_context:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default) \<and>
        \<not> all_queries_consistent
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default)
          (sqp_alphas prefix)"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_default composition_default i out"
  shows
    "checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at
      i out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_def
      checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_def
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
  have support':
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    using support unfolding out_eq .
  have prefix_support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_query_prefix_data_state_prefix_support
        [OF support'])
  have ctxt_fact:
    "trace_table_low_degree
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default) \<and>
     composition_table_low_degree maxDegree
      (query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_default) \<and>
     \<not> all_queries_consistent
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default)
      (query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_default)
      (sqp_alphas prefix)"
    by (rule default_context[OF prefix_support])
  from hit ctxt_fact have collision: "hash_map_output_collision prefix_state"
    unfolding out_eq
      checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_def
      checked_staged_security_with_query_prefix_conceptual_default_context_residual_at_def
    by auto
  have current_hit:
    "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i out"
    using hit
    unfolding
      checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_def
    by simp
  show ?thesis
    unfolding
      checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at_def
    using current_hit collision out_eq by simp
qed

lemma checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_bound_from_context:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and default_context:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default) \<and>
        \<not> all_queries_consistent
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default)
          (sqp_alphas prefix)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_default composition_default i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_default composition_default i)
      adversary_initial_state \<le>
     wp_event ?M
      (checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at
        i)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_imp_prefix_collision_on_support
        [OF default_context])
  also have "... \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at_bound
        [OF wf controlled i_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_bound_from_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and algebraic_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
          i)
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
        i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + R"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Collision =
    "checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at
      i"
  let ?Algebraic =
    "checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
      i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at i)
      adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?Collision out \<or> ?Algebraic out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_split)
  have union_bound:
    "wp_event ?M (\<lambda>out. ?Collision out \<or> ?Algebraic out)
      adversary_initial_state \<le>
      wp_event ?M ?Collision adversary_initial_state +
      wp_event ?M ?Algebraic adversary_initial_state"
    by (rule wp_event_union_bound)
  have collision_bound:
    "wp_event ?M ?Collision adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_context_prefix_collision_hit_at_bound
        [OF wf controlled i_bound])
  have sum_bound:
    "wp_event ?M ?Collision adversary_initial_state +
      wp_event ?M ?Algebraic adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + R"
    by (intro add_mono collision_bound algebraic_bound)
  show ?thesis
    by (rule order_trans[OF event_le order_trans[OF union_bound sum_bound]])
qed

lemma checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_bound_from_current:
  assumes current_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i)
      adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
        i)
      adversary_initial_state \<le> C"
  by (rule order_trans[OF _ current_bound])
    (rule wp_event_mono,
      rule checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_imp_current)

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_imp_conceptual_or_residual_or_structured_path_on_support:
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
    "checked_staged_security_with_query_prefix_conceptual_target_hit out \<or>
     checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i out"
proof -
  have split:
    "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i out"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_imp_prefix_or_structured_path_on_support
        [OF wf controlled i_bound support hit])
  then show ?thesis
  proof
    assume prefix:
      "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i out"
    have
      "checked_staged_security_with_query_prefix_conceptual_target_hit out \<or>
       checked_staged_security_with_query_prefix_conceptual_context_residual_at
        out"
      by (rule
          checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_imp_conceptual_or_residual_on_support
          [OF wf controlled i_bound support prefix])
    then show ?thesis
      unfolding
        checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_def
      using hit by blast
  next
    assume
      "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out \<or>
       checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i out"
    then show ?thesis by blast
  qed
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_imp_conceptual_default_or_residual_or_structured_path_on_support:
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
    "checked_staged_security_with_query_prefix_conceptual_default_target_hit
        trace_default composition_default out \<or>
     checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_default composition_default i out \<or>
     checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i out"
proof -
  have split:
    "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i out"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_imp_prefix_or_structured_path_on_support
        [OF wf controlled i_bound support hit])
  then show ?thesis
  proof
    assume prefix:
      "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i out"
    have
      "checked_staged_security_with_query_prefix_conceptual_default_target_hit
          trace_default composition_default out \<or>
       checked_staged_security_with_query_prefix_conceptual_default_context_residual_at
          trace_default composition_default out"
      by (rule
          checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_imp_conceptual_default_or_residual_on_support
          [OF wf controlled i_bound support prefix])
    then show ?thesis
      unfolding
        checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_def
      using hit by blast
  next
    assume
      "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out \<or>
       checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i out"
    then show ?thesis by blast
  qed
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_residual_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and residual_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
          i)
        adversary_initial_state \<le> R"
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
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R + T + C"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Conceptual =
    "checked_staged_security_with_query_prefix_conceptual_target_hit"
  let ?Residual =
    "checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
      i"
  let ?Trace =
    "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i"
  let ?Composition =
    "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
     wp_event ?M
      (\<lambda>out. ?Conceptual out \<or> ?Residual out \<or> ?Trace out \<or>
        ?Composition out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_imp_conceptual_or_residual_or_structured_path_on_support
        [OF wf controlled i_bound])
  have conceptual_bound:
    "wp_event ?M ?Conceptual adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule checked_staged_security_with_query_prefix_conceptual_target_hit_bound
        [OF wf controlled i_bound])
  have union_bound:
    "wp_event ?M
      (\<lambda>out. ?Conceptual out \<or> ?Residual out \<or> ?Trace out \<or>
        ?Composition out)
      adversary_initial_state \<le>
     wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state +
     wp_event ?M ?Trace adversary_initial_state +
     wp_event ?M ?Composition adversary_initial_state"
    by (rule wp_event_union_bound4)
  have sum_bound:
    "wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state +
     wp_event ?M ?Trace adversary_initial_state +
     wp_event ?M ?Composition adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      R + T + C"
    by (intro add_mono conceptual_bound residual_bound trace_path_bound
        composition_path_bound)
  have event_bound:
    "wp_event ?M
      (\<lambda>out. ?Conceptual out \<or> ?Residual out \<or> ?Trace out \<or>
        ?Composition out)
      adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      R + T + C"
    by (rule order_trans[OF union_bound sum_bound])
  show ?thesis
    by (rule order_trans[OF event_le])
      (use event_bound in \<open>simp add: algebra_simps\<close>)
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_residual_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and residual_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
          trace_default composition_default i)
        adversary_initial_state \<le> R"
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
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R + T + C"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Conceptual =
    "checked_staged_security_with_query_prefix_conceptual_default_target_hit
      trace_default composition_default"
  let ?Residual =
    "checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
      trace_default composition_default i"
  let ?Trace =
    "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i"
  let ?Composition =
    "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
     wp_event ?M
      (\<lambda>out. ?Conceptual out \<or> ?Residual out \<or> ?Trace out \<or>
        ?Composition out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_imp_conceptual_default_or_residual_or_structured_path_on_support
        [OF wf controlled i_bound])
  have conceptual_bound:
    "wp_event ?M ?Conceptual adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_default_target_hit_bound
        [OF wf controlled i_bound])
  have union_bound:
    "wp_event ?M
      (\<lambda>out. ?Conceptual out \<or> ?Residual out \<or> ?Trace out \<or>
        ?Composition out)
      adversary_initial_state \<le>
     wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state +
     wp_event ?M ?Trace adversary_initial_state +
     wp_event ?M ?Composition adversary_initial_state"
    by (rule wp_event_union_bound4)
  have sum_bound:
    "wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state +
     wp_event ?M ?Trace adversary_initial_state +
     wp_event ?M ?Composition adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      R + T + C"
    by (intro add_mono conceptual_bound residual_bound trace_path_bound
        composition_path_bound)
  have event_bound:
    "wp_event ?M
      (\<lambda>out. ?Conceptual out \<or> ?Residual out \<or> ?Trace out \<or>
        ?Composition out)
      adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      R + T + C"
    by (rule order_trans[OF union_bound sum_bound])
  show ?thesis
    by (rule order_trans[OF event_le])
      (use event_bound in \<open>simp add: algebra_simps\<close>)
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_context_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and default_context:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default) \<and>
        \<not> all_queries_consistent
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default)
          (sqp_alphas prefix)"
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
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
proof -
  have residual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_default composition_default i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_bound_from_context
        [OF wf controlled i_bound default_context])
  have bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_residual_and_structured_paths
        [OF wf controlled i_bound residual_bound trace_path_bound
          composition_path_bound])
  show ?thesis
    using bound by simp
qed

lemma checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_bound_from_conceptual_default_residual_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and residual_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
          trace_table composition_table i)
        adversary_initial_state \<le> R"
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
      (checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R + T + C"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Conceptual =
    "checked_staged_security_with_query_prefix_conceptual_default_target_hit
      trace_table composition_table"
  let ?Residual =
    "checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
      trace_table composition_table i"
  let ?Trace =
    "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i"
  let ?Composition =
    "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
     wp_event ?M
      (\<lambda>out. ?Conceptual out \<or> ?Residual out \<or> ?Trace out \<or>
        ?Composition out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_imp_conceptual_default_or_residual_or_structured_path_on_support
        [OF wf controlled i_bound])
  have conceptual_bound:
    "wp_event ?M ?Conceptual adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_default_target_hit_bound
        [OF wf controlled i_bound])
  have union_bound:
    "wp_event ?M
      (\<lambda>out. ?Conceptual out \<or> ?Residual out \<or> ?Trace out \<or>
        ?Composition out)
      adversary_initial_state \<le>
     wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state +
     wp_event ?M ?Trace adversary_initial_state +
     wp_event ?M ?Composition adversary_initial_state"
    by (rule wp_event_union_bound4)
  have sum_bound:
    "wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state +
     wp_event ?M ?Trace adversary_initial_state +
     wp_event ?M ?Composition adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      R + T + C"
    by (intro add_mono conceptual_bound residual_bound trace_path_bound
        composition_path_bound)
  have event_bound:
    "wp_event ?M
      (\<lambda>out. ?Conceptual out \<or> ?Residual out \<or> ?Trace out \<or>
        ?Composition out)
      adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      R + T + C"
    by (rule order_trans[OF union_bound sum_bound])
  show ?thesis
    by (rule order_trans[OF event_le])
      (use event_bound in \<open>simp add: algebra_simps\<close>)
qed

lemma checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_bound_from_conceptual_default_context_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and default_context:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_table) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_table) \<and>
        \<not> all_queries_consistent
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_table)
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_table)
          (sqp_alphas prefix)"
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
      (checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
proof -
  have residual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_bound_from_context
        [OF wf controlled i_bound default_context])
  have bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
    by (rule
        checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_bound_from_conceptual_default_residual_and_structured_paths
        [OF wf controlled i_bound residual_bound trace_path_bound
          composition_path_bound])
  show ?thesis
    using bound by simp
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_algebraic_residual_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and algebraic_residual_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
          i)
        adversary_initial_state \<le> R"
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
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      R + T + C"
proof -
  have residual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
        i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + R"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_bound_from_split
        [OF wf controlled i_bound algebraic_residual_bound])
  have bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      (hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + R) + T + C"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_residual_and_structured_paths
        [OF wf controlled i_bound residual_bound trace_path_bound
          composition_path_bound])
  show ?thesis
    using bound by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_residual_split_and_structured_paths:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_low_degree_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_trace_low_degree_bad_at
          i)
        adversary_initial_state \<le> LT"
    and composition_low_degree_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_composition_low_degree_bad_at
          i)
        adversary_initial_state \<le> LC"
    and alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_alpha_bad_set_hit_at
          i)
        adversary_initial_state \<le> A'"
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
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      (LT + LC + A') + T + C"
proof -
  have residual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
        i)
      adversary_initial_state \<le> LT + LC + A'"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at_bound_from_split
        [OF false_statement trace_low_degree_bound
          composition_low_degree_bound alpha_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_algebraic_residual_and_structured_paths
        [OF wf controlled i_bound residual_bound trace_path_bound
          composition_path_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_conceptual_residual_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and residual_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
            i)
          adversary_initial_state \<le> R i"
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
        query_error_bound + R i + T i + C i)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_prefix_current_rounds
    [OF wf controlled])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R i + T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_residual_and_structured_paths
        [OF wf controlled i_bound residual_bound[OF i_bound]
          trace_path_bound[OF i_bound] composition_path_bound[OF i_bound]])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_conceptual_default_residual_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and residual_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
            trace_default composition_default i)
          adversary_initial_state \<le> R i"
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
        query_error_bound + R i + T i + C i)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_prefix_current_rounds
    [OF wf controlled])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R i + T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_residual_and_structured_paths
        [OF wf controlled i_bound residual_bound[OF i_bound]
          trace_path_bound[OF i_bound] composition_path_bound[OF i_bound]])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_conceptual_default_context_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and default_context:
      "\<And>i prefix prefix_state. i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default) \<and>
        \<not> all_queries_consistent
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default)
          (sqp_alphas prefix)"
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
        query_error_bound +
        hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1) +
        T i + C i)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_prefix_current_rounds
    [OF wf controlled])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_context_and_structured_paths
        [OF wf controlled i_bound _ trace_path_bound[OF i_bound]
          composition_path_bound[OF i_bound]])
      (rule default_context[OF i_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_conceptual_algebraic_residual_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and algebraic_residual_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_conceptual_context_algebraic_residual_hit_at
            i)
          adversary_initial_state \<le> R i"
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
        query_error_bound +
        hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1) +
        R i + T i + C i)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_prefix_current_rounds
    [OF wf controlled])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      R i + T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_algebraic_residual_and_structured_paths
        [OF wf controlled i_bound algebraic_residual_bound[OF i_bound]
          trace_path_bound[OF i_bound] composition_path_bound[OF i_bound]])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_conceptual_residual_split_and_structured_paths:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_low_degree_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_conceptual_trace_low_degree_bad_at
            i)
          adversary_initial_state \<le> LT i"
    and composition_low_degree_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_conceptual_composition_low_degree_bad_at
            i)
          adversary_initial_state \<le> LC i"
    and alpha_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_conceptual_alpha_bad_set_hit_at
            i)
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
      adversary_initial_state \<le>
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound +
        hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1) +
        (LT i + LC i + P i) + T i + C i)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_prefix_current_rounds
    [OF wf controlled])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      (LT i + LC i + P i) + T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_residual_split_and_structured_paths
        [OF false_statement wf controlled i_bound
          trace_low_degree_bound[OF i_bound]
          composition_low_degree_bound[OF i_bound]
          alpha_bound[OF i_bound]
          trace_path_bound[OF i_bound]
          composition_path_bound[OF i_bound]])
qed

lemma checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_trivial_bound:
  "wp_event
    (checked_staged_security_experiment_with_query_prefix_data_state A i)
    (checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at
      i)
    adversary_initial_state \<le> 1"
  by (rule wp_event_le_1)

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_trivial_residual_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
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
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + 1 + T + C"
  by (rule
      checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_residual_and_structured_paths
      [OF wf controlled i_bound
        checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_trivial_bound
        trace_path_bound composition_path_bound])

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_conceptual_trivial_residual_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
        query_error_bound + 1 + T i + C i)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_conceptual_residual_and_structured_paths
    [OF wf controlled _ trace_path_bound composition_path_bound])
  fix i
  assume "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at i)
      adversary_initial_state \<le> 1"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_context_residual_hit_at_trivial_bound)
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_conceptual_and_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and conceptual_context:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> hash_map_output_collision prefix_state \<and>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table prefix prefix_state) \<and>
        \<not> all_queries_consistent
          (query_prefix_trace_conceptual_table prefix prefix_state)
          (query_prefix_composition_conceptual_table prefix prefix_state)
          (sqp_alphas prefix)"
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
  show
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_query_prefix_prefix_authenticated_target_hit_bound_from_conceptual
        [OF wf controlled i_bound])
      (rule conceptual_context[OF i_bound])
qed

end

end
