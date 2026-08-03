(*  Title:      Stark/Soundness_Staged_Candidate_Query.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Candidate_Query
  imports
    Soundness_Staged_Query
    Soundness_Staged_Partial_Query
begin

text \<open>
  Candidate-indexed dynamic query-prefix targets.

  These targets are narrower than the old global partial-opening fixed cover:
  they are parameterized by one fixed trace/composition candidate pair and the
  authenticated openings extracted for that pair.  This is the shape needed
  for the composition candidate-drift query case, where the target must be
  chosen before the query-index challenge is sampled.
\<close>

context soundness
begin

definition staged_query_prefix_candidate_opening_query_target
  :: "'f authenticated_opening list list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow>
      'f list \<Rightarrow> nat \<Rightarrow>
      'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_candidate_opening_query_target trace_openings
      composition_openings as i prefix prefix_state =
    partial_query_success_indices_at trace_openings composition_openings as i"

definition staged_query_prefix_candidate_pair_query_target
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
      'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_candidate_pair_query_target trace_table
      composition_table as prefix prefix_state =
    query_sampling_success_space trace_table composition_table as"

definition staged_query_prefix_candidate_opening_query_target_from_prefix
  :: "'f authenticated_opening list list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow>
      nat \<Rightarrow> 'f staged_query_prefix_data \<Rightarrow>
      'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_candidate_opening_query_target_from_prefix
      trace_openings composition_openings i prefix prefix_state =
    partial_query_success_indices_at trace_openings composition_openings
      (sqp_alphas prefix) i"

definition staged_query_prefix_candidate_pair_query_target_from_prefix
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f staged_query_prefix_data \<Rightarrow>
      'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
      composition_table prefix prefix_state =
    query_sampling_success_space trace_table composition_table
      (sqp_alphas prefix)"

definition checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit
where
  "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit A
      trace_table composition_table out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state) \<Rightarrow>
        (\<exists>i prefix prefix_state raw raw_state.
          i < rounds \<and>
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (staged_query_prefix_candidate_pair_query_target trace_table
              composition_table (staged_alphas data))
            (Some (((prefix, prefix_state), raw), raw_state))))"

definition checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit
where
  "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
      trace_openings composition_openings as i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state) \<Rightarrow>
        as = staged_alphas data \<and>
        i < rounds \<and>
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
            (staged_query_prefix_candidate_opening_query_target
              trace_openings composition_openings as i)
            (Some (((prefix, prefix_state), raw), raw_state))))"

lemma staged_query_prefix_candidate_opening_query_target_subset:
  "staged_query_prefix_candidate_opening_query_target trace_openings
      composition_openings as i prefix prefix_state \<subseteq> query_sample_space"
  unfolding staged_query_prefix_candidate_opening_query_target_def
  by (rule partial_query_success_indices_at_subset)

lemma staged_query_prefix_candidate_pair_query_target_subset:
  "staged_query_prefix_candidate_pair_query_target trace_table
      composition_table as prefix prefix_state \<subseteq> query_sample_space"
  unfolding staged_query_prefix_candidate_pair_query_target_def
  by (rule query_sampling_success_space_subset)

lemma staged_query_prefix_candidate_opening_query_target_from_prefix_subset:
  "staged_query_prefix_candidate_opening_query_target_from_prefix
      trace_openings composition_openings i prefix prefix_state \<subseteq>
    query_sample_space"
  unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
  by (rule partial_query_success_indices_at_subset)

lemma staged_query_prefix_candidate_pair_query_target_from_prefix_subset:
  "staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
      composition_table prefix prefix_state \<subseteq> query_sample_space"
  unfolding staged_query_prefix_candidate_pair_query_target_from_prefix_def
  by (rule query_sampling_success_space_subset)

lemma staged_query_prefix_candidate_opening_query_target_subset_candidate_pair:
  assumes trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "staged_query_prefix_candidate_opening_query_target trace_openings
      composition_openings as i prefix prefix_state \<subseteq>
     staged_query_prefix_candidate_pair_query_target trace_table
      composition_table as prefix prefix_state"
  unfolding staged_query_prefix_candidate_opening_query_target_def
    staged_query_prefix_candidate_pair_query_target_def
  by (rule partial_query_success_indices_at_subset_query_sampling_success_space
      [OF trace_candidate comp_candidate trace_low comp_low not_all])

lemma staged_query_prefix_candidate_opening_query_target_from_prefix_subset_candidate_pair_from_prefix:
  assumes trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table
        (sqp_alphas prefix)"
  shows
    "staged_query_prefix_candidate_opening_query_target_from_prefix
      trace_openings composition_openings i prefix prefix_state \<subseteq>
     staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
      composition_table prefix prefix_state"
  unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
    staged_query_prefix_candidate_pair_query_target_from_prefix_def
  by (rule partial_query_success_indices_at_subset_query_sampling_success_space
      [OF trace_candidate comp_candidate trace_low comp_low not_all])

lemma checked_staged_query_prefix_dynamic_index_hit_mono:
  assumes subset: "\<And>prefix prefix_state. A prefix prefix_state \<subseteq>
      B prefix prefix_state"
    and hit:
      "checked_staged_query_prefix_dynamic_index_hit A
        (Some (((prefix, prefix_state), raw), raw_state))"
  shows
    "checked_staged_query_prefix_dynamic_index_hit B
      (Some (((prefix, prefix_state), raw), raw_state))"
  using subset hit
  unfolding checked_staged_query_prefix_dynamic_index_hit_def by auto

lemma partial_trace_table_candidate_single_round_from_all_rounds:
  assumes cand: "partial_trace_table_candidate trace_table trace_openingss"
    and i_bound: "i < rounds"
  shows
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [i := trace_openingss ! i])"
proof -
  have len_table: "length trace_table = scale * clength"
    using cand unfolding partial_trace_table_candidate_def by simp
  have agrees:
    "table_agrees_with_authenticated_openings trace_table
      (scale * clength) (trace_openingss ! i)"
    using cand i_bound unfolding partial_trace_table_candidate_def by blast
  show ?thesis
    by (rule partial_trace_table_candidate_single_roundI
        [OF i_bound len_table agrees])
qed

lemma partial_composition_table_candidate_single_round_from_all_rounds:
  assumes cand:
      "partial_composition_table_candidate composition_table
        composition_openingss"
    and i_bound: "i < rounds"
  shows
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [i := composition_openingss ! i])"
proof -
  have len_table: "length composition_table = scale * clength"
    using cand unfolding partial_composition_table_candidate_def by simp
  have agrees:
    "table_agrees_with_authenticated_openings composition_table
      (scale * clength) (composition_openingss ! i)"
    using cand i_bound unfolding partial_composition_table_candidate_def
    by blast
  show ?thesis
    by (rule partial_composition_table_candidate_single_roundI
        [OF i_bound len_table agrees])
qed

lemma staged_query_prefix_candidate_opening_query_target_single_roundI:
  assumes i_bound: "i < rounds"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        as idx"
  shows
    "idx \<in>
      staged_query_prefix_candidate_opening_query_target
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        as i prefix prefix_state"
  unfolding staged_query_prefix_candidate_opening_query_target_def
  by (rule partial_query_success_indices_atI,
      rule partial_query_round_consistent_single_roundI
        [OF i_bound consistent])

lemma checked_staged_query_prefix_candidate_opening_target_single_round_hitI:
  assumes i_bound: "i < rounds"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        as (index (to_nat raw))"
  shows
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        as i)
      (Some (((prefix, prefix_state), raw), raw_state))"
proof -
  have "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        as i prefix prefix_state"
    by (rule staged_query_prefix_candidate_opening_query_target_single_roundI
        [OF i_bound consistent])
  then show ?thesis
    unfolding checked_staged_query_prefix_dynamic_index_hit_def by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hitI:
  assumes as_eq: "as = staged_alphas data"
    and i_bound: "i < rounds"
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
        (staged_query_prefix_candidate_opening_query_target
          trace_openings composition_openings as i)
        (Some (((prefix, prefix_state), raw), raw_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
      trace_openings composition_openings as i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
proof -
  have body:
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
        (staged_query_prefix_candidate_opening_query_target
          trace_openings composition_openings as i)
        (Some (((prefix, prefix_state), raw), raw_state))"
    by (intro exI[of _ prefix] exI[of _ prefix_state]
        exI[of _ raw] exI[of _ raw_state])
      (use builder prefix_receive target_hit in simp)
  show ?thesis
    unfolding
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_def
    using as_eq i_bound body by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hitI_from_raw:
  assumes as_eq: "as = staged_alphas data"
    and i_bound: "i < rounds"
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
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        as (index (to_nat raw))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      as i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
proof -
  have target_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        as i)
      (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule checked_staged_query_prefix_candidate_opening_target_single_round_hitI
        [OF i_bound consistent])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hitI
        [OF as_eq i_bound builder prefix_receive target_hit])
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hitI_from_prefix_receive:
  assumes i_bound: "i < rounds"
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
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      (staged_alphas data) i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
  by (rule
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hitI_from_raw
      [OF refl i_bound builder prefix_receive consistent])

definition checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
where
  "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix A
      trace_openings composition_openings i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state) \<Rightarrow>
        i < rounds \<and>
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
            (staged_query_prefix_candidate_opening_query_target_from_prefix
              trace_openings composition_openings i)
            (Some (((prefix, prefix_state), raw), raw_state))))"

definition checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
where
  "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix A
      trace_table composition_table i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state) \<Rightarrow>
        i < rounds \<and>
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
            (staged_query_prefix_candidate_pair_query_target_from_prefix
              trace_table composition_table)
            (Some (((prefix, prefix_state), raw), raw_state))))"

lemma checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefixI:
  assumes i_bound: "i < rounds"
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
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i)
        (Some (((prefix, prefix_state), raw), raw_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix A
      trace_openings composition_openings i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
proof -
  have body:
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
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i)
        (Some (((prefix, prefix_state), raw), raw_state))"
    by (intro exI[of _ prefix] exI[of _ prefix_state]
        exI[of _ raw] exI[of _ raw_state])
      (use builder prefix_receive target_hit in simp)
  show ?thesis
    unfolding
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix_def
    using i_bound body by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefixE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix A
      trace_openings composition_openings i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains prefix prefix_state raw raw_state where
    "i < rounds"
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        trace_openings composition_openings i)
      (Some (((prefix, prefix_state), raw), raw_state))"
  using hit
proof -
  have body:
    "i < rounds \<and>
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
          (staged_query_prefix_candidate_opening_query_target_from_prefix
            trace_openings composition_openings i)
          (Some (((prefix, prefix_state), raw), raw_state)))"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix_def
    by simp
  then obtain prefix prefix_state raw raw_state where
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
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i)
        (Some (((prefix, prefix_state), raw), raw_state))"
    by blast
  show ?thesis
    by (rule that[OF i_bound builder prefix_receive target_hit])
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixI:
  assumes i_bound: "i < rounds"
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
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix A
      trace_table composition_table i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
proof -
  have body:
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
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table)
        (Some (((prefix, prefix_state), raw), raw_state))"
    by (intro exI[of _ prefix] exI[of _ prefix_state]
        exI[of _ raw] exI[of _ raw_state])
      (use builder prefix_receive target_hit in simp)
  show ?thesis
    unfolding
      checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_def
    using i_bound body by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix A
      trace_table composition_table i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains prefix prefix_state raw raw_state where
    "i < rounds"
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
  using hit
proof -
  have body:
    "i < rounds \<and>
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
          (staged_query_prefix_candidate_pair_query_target_from_prefix
            trace_table composition_table)
          (Some (((prefix, prefix_state), raw), raw_state)))"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_def
    by simp
  then obtain prefix prefix_state raw raw_state where
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
    by blast
  show ?thesis
    by (rule that[OF i_bound builder prefix_receive target_hit])
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix_imp_candidate_pair_query_hit_from_prefix:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix A
      trace_openings composition_openings i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
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
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix A
      trace_table composition_table i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  from checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefixE
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
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i)
        (Some (((prefix, prefix_state), raw), raw_state))"
    by blast
  have prefix_support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
    by (rule checked_staged_query_prefix_receive_with_state_prefix_support
        [OF prefix_receive])
  have pair_target_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
        composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
  proof -
    have subset:
      "staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i prefix prefix_state \<subseteq>
       staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
          composition_table prefix prefix_state"
      by (rule
        staged_query_prefix_candidate_opening_query_target_from_prefix_subset_candidate_pair_from_prefix
        [OF trace_candidate comp_candidate trace_low comp_low
          not_all[OF prefix_support]])
    show ?thesis
      using target_hit subset
      unfolding checked_staged_query_prefix_dynamic_index_hit_def by auto
  qed
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixI
        [OF i_bound builder prefix_receive pair_target_hit])
qed

lemma checked_staged_query_prefix_candidate_opening_target_from_prefix_single_round_hitI:
  assumes i_bound: "i < rounds"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (sqp_alphas prefix) (index (to_nat raw))"
  shows
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i)
      (Some (((prefix, prefix_state), raw), raw_state))"
proof -
  have "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state"
    unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
    by (rule partial_query_success_indices_atI,
        rule partial_query_round_consistent_single_roundI
          [OF i_bound consistent])
  then show ?thesis
    unfolding checked_staged_query_prefix_dynamic_index_hit_def by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefixI_from_prefix_receive:
  assumes i_bound: "i < rounds"
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
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
proof -
  have consistent_prefix:
    "partial_query_openings_consistent trace_openings composition_openings
      (sqp_alphas prefix) (index (to_nat raw))"
    using consistent alphas_eq by simp
  have target_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i)
      (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule
        checked_staged_query_prefix_candidate_opening_target_from_prefix_single_round_hitI
        [OF i_bound consistent_prefix])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefixI
        [OF i_bound builder prefix_receive target_hit])
qed

lemma checked_staged_query_prefix_candidate_pair_target_hitI:
  assumes hit:
    "index (to_nat raw) \<in>
      query_sampling_success_space trace_table composition_table as"
  shows
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target trace_table
        composition_table as)
      (Some (((prefix, prefix_state), raw), raw_state))"
  using hit
  unfolding checked_staged_query_prefix_dynamic_index_hit_def
    staged_query_prefix_candidate_pair_query_target_def
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hitI:
  assumes i_bound: "i < rounds"
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
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table (staged_alphas data))
        (Some (((prefix, prefix_state), raw), raw_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit A
      trace_table composition_table
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
proof -
  have body:
    "\<exists>i prefix prefix_state raw raw_state.
      i < rounds \<and>
      Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<and>
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table (staged_alphas data))
        (Some (((prefix, prefix_state), raw), raw_state))"
    by (intro exI[of _ i] exI[of _ prefix] exI[of _ prefix_state]
        exI[of _ raw] exI[of _ raw_state])
      (use i_bound builder prefix_receive target_hit in simp)
  show ?thesis
    unfolding
      checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_def
    using body by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_imp_candidate_pair_query_hit:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
      trace_openings composition_openings as i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit A
      trace_table composition_table
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  obtain prefix prefix_state raw raw_state where
    as_eq: "as = staged_alphas data"
    and i_bound: "i < rounds"
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
        (staged_query_prefix_candidate_opening_query_target
          trace_openings composition_openings as i)
        (Some (((prefix, prefix_state), raw), raw_state))"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_def
    by auto
  have pair_target_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target trace_table
        composition_table as)
      (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule checked_staged_query_prefix_dynamic_index_hit_mono
        [OF _ target_hit])
      (rule
        staged_query_prefix_candidate_opening_query_target_subset_candidate_pair
        [OF trace_candidate comp_candidate trace_low comp_low not_all])
  have pair_target_hit':
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target trace_table
        composition_table (staged_alphas data))
      (Some (((prefix, prefix_state), raw), raw_state))"
    using pair_target_hit as_eq by simp
  show ?thesis
    by (rule checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hitI
        [OF i_bound builder prefix_receive pair_target_hit'])
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hitI_from_raw:
  assumes i_bound: "i < rounds"
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
    and target_raw:
      "index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (staged_alphas data)"
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit A
      trace_table composition_table
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
proof -
  have target_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target trace_table
        composition_table (staged_alphas data))
      (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule checked_staged_query_prefix_candidate_pair_target_hitI
        [OF target_raw])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hitI
        [OF i_bound builder prefix_receive target_hit])
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hitE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit A
      trace_table composition_table
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
  obtains i prefix prefix_state raw raw_state where
    "i < rounds"
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target trace_table
        composition_table (staged_alphas data))
      (Some (((prefix, prefix_state), raw), raw_state))"
  using hit
proof -
  have body:
    "\<exists>i prefix prefix_state raw raw_state.
      i < rounds \<and>
      Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<and>
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table (staged_alphas data))
        (Some (((prefix, prefix_state), raw), raw_state))"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_def
    by simp
  then obtain i prefix prefix_state raw raw_state where
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
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table (staged_alphas data))
        (Some (((prefix, prefix_state), raw), raw_state))"
    by blast
  show ?thesis
    by (rule that[OF i_bound builder prefix_receive target_hit])
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_rawE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit A
      trace_table composition_table
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state), result),
        final_state))"
  obtains i prefix prefix_state raw raw_state where
    "i < rounds"
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "index (to_nat raw) \<in>
      query_sampling_success_space trace_table composition_table
        (staged_alphas data)"
proof -
  from checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hitE
      [OF hit]
  obtain i prefix prefix_state raw raw_state where
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
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table (staged_alphas data))
        (Some (((prefix, prefix_state), raw), raw_state))"
    by blast
  have raw_hit:
    "index (to_nat raw) \<in>
      query_sampling_success_space trace_table composition_table
        (staged_alphas data)"
    using target_hit
    unfolding checked_staged_query_prefix_dynamic_index_hit_def
      staged_query_prefix_candidate_pair_query_target_def
    by simp
  show ?thesis
    by (rule that[OF i_bound builder prefix_receive raw_hit])
qed

lemma staged_query_prefix_candidate_pair_query_target_fraction_bound:
  assumes trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "nnreal
      (card
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table as prefix prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
  unfolding staged_query_prefix_candidate_pair_query_target_def
  by (rule query_sampling_success_space_fraction_bound_query_sample_space)

lemma staged_query_prefix_candidate_opening_query_target_fraction_bound:
  assumes trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "nnreal
      (card
        (staged_query_prefix_candidate_opening_query_target trace_openings
          composition_openings as i prefix prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
  unfolding staged_query_prefix_candidate_opening_query_target_def
  by (rule partial_query_success_indices_at_fraction_bound_if_candidate_low_degree
      [OF trace_candidate comp_candidate trace_low comp_low not_all])

lemma staged_query_prefix_candidate_opening_query_target_from_prefix_fraction_bound:
  assumes trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table
        (sqp_alphas prefix)"
  shows
    "nnreal
      (card
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i prefix prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
  unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
  by (rule partial_query_success_indices_at_fraction_bound_if_candidate_low_degree
      [OF trace_candidate comp_candidate trace_low comp_low not_all])

lemma staged_query_prefix_candidate_pair_query_target_from_prefix_fraction_bound:
  assumes trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table
        (sqp_alphas prefix)"
  shows
    "nnreal
      (card
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table prefix prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
  unfolding staged_query_prefix_candidate_pair_query_target_from_prefix_def
  by (rule query_sampling_success_space_fraction_bound_query_sample_space)

lemma checked_staged_query_prefix_candidate_opening_target_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_opening_query_target
          trace_openings composition_openings as i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        (staged_query_prefix_candidate_opening_query_target
          trace_openings composition_openings as i))
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_candidate_opening_target_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target
          trace_openings composition_openings as i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target
          trace_openings composition_openings as i))
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_opening_query_target
          trace_openings composition_openings as i))
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    have subset:
      "staged_query_prefix_candidate_opening_query_target trace_openings
          composition_openings as i prefix prefix_state \<subseteq>
        query_sample_space"
      by (rule staged_query_prefix_candidate_opening_query_target_subset)
    have frac:
      "nnreal
        (card
          (staged_query_prefix_candidate_opening_query_target
            trace_openings composition_openings as i prefix prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      by (rule staged_query_prefix_candidate_opening_query_target_fraction_bound
          [OF trace_candidate comp_candidate trace_low comp_low not_all])
    show
      "staged_query_prefix_candidate_opening_query_target trace_openings
          composition_openings as i prefix prefix_state \<subseteq>
        query_sample_space \<and>
       nnreal
        (card
          (staged_query_prefix_candidate_opening_query_target
            trace_openings composition_openings as i prefix prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      using subset frac by blast
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_opening_query_target
          trace_openings composition_openings as i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
    by (rule checked_staged_query_prefix_candidate_opening_target_prehit_bound
        [OF wf controlled i_bound])
  have tail:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_opening_query_target
          trace_openings composition_openings as i))
      adversary_initial_state + query_error_bound \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (intro add_mono prehit_bound order_refl)
  show ?thesis
    by (rule order_trans[OF hit_bound tail])
qed

lemma checked_staged_query_prefix_candidate_opening_target_from_prefix_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_candidate_opening_target_from_prefix_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
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
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    have subset:
      "staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i prefix prefix_state \<subseteq>
        query_sample_space"
      by (rule staged_query_prefix_candidate_opening_query_target_from_prefix_subset)
    have frac:
      "nnreal
        (card
          (staged_query_prefix_candidate_opening_query_target_from_prefix
            trace_openings composition_openings i prefix prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      by (rule
          staged_query_prefix_candidate_opening_query_target_from_prefix_fraction_bound
          [OF trace_candidate comp_candidate trace_low comp_low not_all[OF support]])
    show
      "staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i prefix prefix_state \<subseteq>
        query_sample_space \<and>
       nnreal
        (card
          (staged_query_prefix_candidate_opening_query_target_from_prefix
            trace_openings composition_openings i prefix prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      using subset frac by blast
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_query_prefix_candidate_opening_target_from_prefix_prehit_bound
        [OF wf controlled i_bound])
  have tail:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state + query_error_bound \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (intro add_mono prehit_bound order_refl)
  show ?thesis
    by (rule order_trans[OF hit_bound tail])
qed

lemma checked_staged_query_prefix_candidate_pair_target_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table as))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table as))
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_candidate_pair_target_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table as))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table as))
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table as))
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    have subset:
      "staged_query_prefix_candidate_pair_query_target trace_table
          composition_table as prefix prefix_state \<subseteq>
        query_sample_space"
      by (rule staged_query_prefix_candidate_pair_query_target_subset)
    have frac:
      "nnreal
        (card
          (staged_query_prefix_candidate_pair_query_target trace_table
            composition_table as prefix prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      by (rule staged_query_prefix_candidate_pair_query_target_fraction_bound
          [OF trace_low comp_low not_all])
    show
      "staged_query_prefix_candidate_pair_query_target trace_table
          composition_table as prefix prefix_state \<subseteq>
        query_sample_space \<and>
       nnreal
        (card
          (staged_query_prefix_candidate_pair_query_target trace_table
            composition_table as prefix prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      using subset frac by blast
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table as))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
    by (rule checked_staged_query_prefix_candidate_pair_target_prehit_bound
        [OF wf controlled i_bound])
  have tail:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_pair_query_target trace_table
          composition_table as))
      adversary_initial_state + query_error_bound \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (intro add_mono prehit_bound order_refl)
  show ?thesis
    by (rule order_trans[OF hit_bound tail])
qed

lemma checked_staged_query_prefix_candidate_pair_target_from_prefix_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table))
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_candidate_pair_target_from_prefix_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
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
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table))
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table))
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    have subset:
      "staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table prefix prefix_state \<subseteq>
        query_sample_space"
      by (rule staged_query_prefix_candidate_pair_query_target_from_prefix_subset)
    have frac:
      "nnreal
        (card
          (staged_query_prefix_candidate_pair_query_target_from_prefix
            trace_table composition_table prefix prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      by (rule
          staged_query_prefix_candidate_pair_query_target_from_prefix_fraction_bound)
        (use trace_low comp_low not_all[OF support] in simp_all)
    show
      "staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table prefix prefix_state \<subseteq>
        query_sample_space \<and>
       nnreal
        (card
          (staged_query_prefix_candidate_pair_query_target_from_prefix
            trace_table composition_table prefix prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      using subset frac by blast
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_query_prefix_candidate_pair_target_from_prefix_prehit_bound
        [OF wf controlled i_bound])
  have tail:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table))
      adversary_initial_state + query_error_bound \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (intro add_mono prehit_bound order_refl)
  show ?thesis
    by (rule order_trans[OF hit_bound tail])
qed

lemma checked_staged_query_prefix_candidate_pair_target_from_prefix_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
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
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_query_prefix_candidate_pair_target_from_prefix_hit_bound
        [OF raw_bound wf controlled _ trace_low comp_low not_all])
      (use i_bound in simp)
qed

end

end
