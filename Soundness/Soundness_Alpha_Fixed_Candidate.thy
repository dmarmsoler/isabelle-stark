(*  Title:      Stark/Soundness_Alpha_Fixed_Candidate.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Alpha_Fixed_Candidate
  imports Soundness_Conceptual_Query_Current_Alpha_Clean
begin

text \<open>
  Fixed-trace-table alpha targets.

  This layer records the sound probability component that is available when a
  trace table has already been fixed before the alpha challenge is sampled.
  It deliberately does not claim that sampled Merkle openings determine such a
  table.
\<close>

context soundness
begin

definition staged_alpha_prefix_fixed_trace_prequery_hit
  :: "'f list \<Rightarrow>
      (('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_alpha_prefix_fixed_trace_prequery_hit trace_table out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (_, prefix_state) \<Rightarrow>
          (\<exists>as \<in> composition_trace_bad_alpha_space trace_table.
            alpha_vector_prequeried_in_state prefix_state as
              (length spec)))"

definition staged_alpha_prefix_fixed_trace_prequery_relation
  :: "'f staged_adversary \<Rightarrow> 'f protocol_channel \<Rightarrow>
      'f list \<Rightarrow> 'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "staged_alpha_prefix_fixed_trace_prequery_relation A s trace_table x y
      \<longleftrightarrow>
      (\<exists>prefix prefix_state as i.
        Some (prefix, prefix_state) \<in>
          set_dist (execute (staged_alpha_prefix_program A) s) \<and>
        as \<in> composition_trace_bad_alpha_space trace_table \<and>
        i < length spec \<and>
        i < length as \<and>
        x = alpha_challenge_key_at prefix_state i as \<and>
        y = as ! i)"

definition checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried
  :: "'f list \<Rightarrow>
      (((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
        'f protocol_channel) \<times> 'f staged_proof_data) \<times>
       'f protocol_channel) option \<Rightarrow>
      bool"
  where
    "checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried
      trace_table out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((prefix, prefix_state), data), _) \<Rightarrow>
          staged_alphas data \<in> composition_trace_bad_alpha_space trace_table \<and>
          \<not> alpha_vector_prequeried_in_state prefix_state
            (staged_alphas data) (length spec))"

definition checked_staged_transcript_fixed_trace_alpha_prequery_hit
  :: "'f list \<Rightarrow>
      (((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
        'f protocol_channel) \<times> 'f staged_proof_data) \<times>
       'f protocol_channel) option \<Rightarrow>
      bool"
  where
    "checked_staged_transcript_fixed_trace_alpha_prequery_hit trace_table out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((prefix, prefix_state), data), _) \<Rightarrow>
          staged_alphas data \<in> composition_trace_bad_alpha_space trace_table \<and>
          alpha_vector_prequeried_in_state prefix_state
            (staged_alphas data) (length spec))"

definition checked_staged_transcript_fixed_trace_alpha_bad
  :: "'f list \<Rightarrow>
      (((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
        'f protocol_channel) \<times> 'f staged_proof_data) \<times>
       'f protocol_channel) option \<Rightarrow>
      bool"
  where
    "checked_staged_transcript_fixed_trace_alpha_bad trace_table out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((prefix, prefix_state), data), _) \<Rightarrow>
          staged_alphas data \<in> composition_trace_bad_alpha_space trace_table)"

lemma staged_alpha_prefix_fixed_trace_prequery_hit_imp_relation_hit:
  assumes empty: "HashMap s = fmempty"
    and support:
      "Some (prefix, prefix_state) \<in>
        set_dist (execute (staged_alpha_prefix_program A) s)"
    and hit:
      "staged_alpha_prefix_fixed_trace_prequery_hit trace_table
        (Some (prefix, prefix_state))"
  shows
    "hash_relation_hit_event
      (staged_alpha_prefix_fixed_trace_prequery_relation A s trace_table)
      s (Some (prefix, prefix_state))"
proof -
  from hit obtain as i where member:
      "as \<in> composition_trace_bad_alpha_space trace_table"
    and i_bound: "i < length spec"
    and i_len: "i < length as"
    and lookup:
      "fmlookup (HashMap prefix_state)
        (alpha_challenge_key_at prefix_state i as) = Some (as ! i)"
    unfolding staged_alpha_prefix_fixed_trace_prequery_hit_def
      alpha_vector_prequeried_in_state_def
    by auto
  have initial_none:
    "fmlookup (HashMap s) (alpha_challenge_key_at prefix_state i as) =
      None"
    using empty by simp
  have relation:
    "staged_alpha_prefix_fixed_trace_prequery_relation A s trace_table
      (alpha_challenge_key_at prefix_state i as) (as ! i)"
    unfolding staged_alpha_prefix_fixed_trace_prequery_relation_def
    using support member i_bound i_len by blast
  have hit_relation:
    "hash_relation_hit
      (staged_alpha_prefix_fixed_trace_prequery_relation A s trace_table)
      s prefix_state"
    unfolding hash_relation_hit_def
    using initial_none lookup relation by blast
  show ?thesis
    unfolding hash_relation_hit_event_def using hit_relation by simp
qed

lemma staged_alpha_prefix_fixed_trace_prequery_hit_bound_by_relation_hit:
  assumes empty: "HashMap s = fmempty"
  shows
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_fixed_trace_prequery_hit trace_table) s \<le>
     wp_event (staged_alpha_prefix_program A)
      (hash_relation_hit_event
        (staged_alpha_prefix_fixed_trace_prequery_relation A s trace_table)
        s) s"
proof (rule wp_event_mono_on_support)
  fix out
  assume support: "out \<in> set_dist (execute (staged_alpha_prefix_program A) s)"
    and hit: "staged_alpha_prefix_fixed_trace_prequery_hit trace_table out"
  show
    "hash_relation_hit_event
      (staged_alpha_prefix_fixed_trace_prequery_relation A s trace_table)
      s out"
  proof (cases out)
    case None
    then show ?thesis
      using hit unfolding staged_alpha_prefix_fixed_trace_prequery_hit_def
      by simp
  next
    case (Some result)
    then obtain prefix prefix_state where out_eq:
      "out = Some (prefix, prefix_state)"
      by (cases result) auto
    show ?thesis
      unfolding out_eq
      by (rule staged_alpha_prefix_fixed_trace_prequery_hit_imp_relation_hit
          [OF empty])
        (use support hit out_eq in simp_all)
  qed
qed

lemma staged_alpha_prefix_fixed_trace_prequery_relation_fiber_bound_size:
  "card
    {y. staged_alpha_prefix_fixed_trace_prequery_relation A s trace_table x y}
    \<le> size"
proof -
  have subset:
    "{y. staged_alpha_prefix_fixed_trace_prequery_relation A s trace_table x y}
      \<subseteq> (UNIV :: 'f set)"
    by simp
  have finite_field: "finite (UNIV :: 'f set)"
    by simp
  have "card
      {y. staged_alpha_prefix_fixed_trace_prequery_relation A s trace_table x y}
      \<le> card (UNIV :: 'f set)"
    by (rule card_mono[OF finite_field subset])
  also have "... = size"
    using size_card by simp
  finally show ?thesis .
qed

lemma staged_alpha_prefix_fixed_trace_prequery_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_fixed_trace_prequery_hit trace_table)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  have prehit_le_relation:
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_fixed_trace_prequery_hit trace_table)
      adversary_initial_state \<le>
     wp_event (staged_alpha_prefix_program A)
      (hash_relation_hit_event
        (staged_alpha_prefix_fixed_trace_prequery_relation A
          adversary_initial_state trace_table)
        adversary_initial_state)
      adversary_initial_state"
    by (rule staged_alpha_prefix_fixed_trace_prequery_hit_bound_by_relation_hit)
      (simp add: adversary_initial_state_def)
  also have "... \<le>
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
  proof -
    have program:
      "hash_relation_program
        (staged_alpha_prefix_fixed_trace_prequery_relation A
          adversary_initial_state trace_table)
        size (staged_alpha_search_queries budgets 0)
        (staged_alpha_prefix_program A)"
      by (rule hash_relation_program_staged_alpha_prefix_program
          [OF wf controlled])
        (rule staged_alpha_prefix_fixed_trace_prequery_relation_fiber_bound_size)
    show ?thesis
      using program
      unfolding hash_relation_program_def hash_relation_budget_def
        staged_phase_relation_error_def
      by blast
  qed
  finally show ?thesis .
qed

lemma checked_staged_after_alpha_prefix_fixed_trace_alpha_bad_excluding_prequeried_bound:
  shows
    "wp_event (checked_staged_after_alpha_prefix_program A prefix)
      (\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (data, _) \<Rightarrow>
          staged_alphas data \<in>
            composition_trace_bad_alpha_space trace_table \<and>
          \<not> alpha_vector_prequeried_in_state s
            (staged_alphas data) (length spec))
      s \<le> composition_error_bound"
proof -
  let ?B = "composition_trace_bad_alpha_space trace_table"
  have bound:
    "wp_event (checked_staged_after_alpha_prefix_program A prefix)
      (\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (data, _) \<Rightarrow>
          staged_alphas data \<in> ?B \<and>
          \<not> alpha_vector_prequeried_in_state s
            (staged_alphas data) (length spec))
      s \<le> nnreal (card ?B) / nnreal (CARD('f) ^ length spec)"
    by (rule
        checked_staged_after_alpha_prefix_program_alpha_list_bound_excluding_prequeried
        [OF composition_trace_bad_alpha_space_subset_alpha_space])
  also have "... \<le> composition_error_bound"
    using composition_trace_bad_alpha_space_fraction_bound_alpha_space
      [of trace_table]
    by simp
  finally show ?thesis .
qed

lemma checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried_bound:
  shows
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried
        trace_table)
      adversary_initial_state \<le> composition_error_bound"
  unfolding checked_staged_transcript_with_alpha_prefix_program_def
proof (rule wp_event_bind_bound_by_cont)
  show
    "\<not> checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried
      trace_table None"
    unfolding
      checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried_def
    by simp
next
  fix prefix prefix_state
  assume prefix_out:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
  let ?Q =
    "checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried
      trace_table"
  have get_eq:
    "wp_event
      (get \<bind>
        (\<lambda>prefix_state'.
          checked_staged_after_alpha_prefix_program A prefix \<bind>
            (\<lambda>data. return ((prefix, prefix_state'), data))))
      ?Q prefix_state =
      wp_event
        (checked_staged_after_alpha_prefix_program A prefix \<bind>
          (\<lambda>data. return ((prefix, prefix_state), data)))
        ?Q
        prefix_state"
    unfolding wp_event_def by (simp add: wpsimps)
  have return_eq:
    "wp_event
      (checked_staged_after_alpha_prefix_program A prefix \<bind>
        (\<lambda>data. return ((prefix, prefix_state), data)))
      ?Q prefix_state =
      wp_event (checked_staged_after_alpha_prefix_program A prefix)
        (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (data, _) \<Rightarrow>
            staged_alphas data \<in>
              composition_trace_bad_alpha_space trace_table \<and>
            \<not> alpha_vector_prequeried_in_state prefix_state
              (staged_alphas data) (length spec))
        prefix_state"
    apply (subst wp_event_bind_return_map)
    unfolding
      checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried_def
    by simp
  show
    "wp_event
      (get \<bind>
        (\<lambda>prefix_state.
          checked_staged_after_alpha_prefix_program A prefix \<bind>
            (\<lambda>data. return ((prefix, prefix_state), data))))
      ?Q prefix_state \<le> composition_error_bound"
    unfolding get_eq return_eq
    by (rule
        checked_staged_after_alpha_prefix_fixed_trace_alpha_bad_excluding_prequeried_bound)
qed

lemma checked_staged_transcript_fixed_trace_alpha_prequery_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_fixed_trace_alpha_prequery_hit trace_table)
      adversary_initial_state \<le>
     staged_phase_relation_error size
      (staged_alpha_search_queries budgets 0)"
  unfolding checked_staged_transcript_with_alpha_prefix_program_def
proof (rule wp_event_bind_bound_by_head_event)
  show
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_fixed_trace_prequery_hit trace_table)
      adversary_initial_state
    \<le> staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule staged_alpha_prefix_fixed_trace_prequery_hit_bound
        [OF wf controlled])
next
  show
    "checked_staged_transcript_fixed_trace_alpha_prequery_hit trace_table
      None \<Longrightarrow>
     staged_alpha_prefix_fixed_trace_prequery_hit trace_table None"
    unfolding checked_staged_transcript_fixed_trace_alpha_prequery_hit_def
      staged_alpha_prefix_fixed_trace_prequery_hit_def
    by simp
next
  fix prefix prefix_state out
  assume prefix_out:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
    and cont:
    "out \<in>
      set_dist
        (execute
          (get \<bind>
            (\<lambda>prefix_state.
              checked_staged_after_alpha_prefix_program A prefix \<bind>
              (\<lambda>data. return ((prefix, prefix_state), data))))
          prefix_state)"
    and hit:
    "checked_staged_transcript_fixed_trace_alpha_prequery_hit trace_table
      out"
  from hit cont show
    "staged_alpha_prefix_fixed_trace_prequery_hit trace_table
      (Some (prefix, prefix_state))"
    unfolding checked_staged_transcript_fixed_trace_alpha_prequery_hit_def
      staged_alpha_prefix_fixed_trace_prequery_hit_def
    by (auto elim!: set_dist_bindE split: option.splits prod.splits)
qed

lemma checked_staged_transcript_fixed_trace_alpha_bad_split:
  assumes hit:
    "checked_staged_transcript_fixed_trace_alpha_bad trace_table out"
  shows
    "checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried
      trace_table out \<or>
     checked_staged_transcript_fixed_trace_alpha_prequery_hit trace_table out"
  using hit
  unfolding checked_staged_transcript_fixed_trace_alpha_bad_def
    checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried_def
    checked_staged_transcript_fixed_trace_alpha_prequery_hit_def
  by (auto split: option.splits prod.splits)

lemma checked_staged_transcript_fixed_trace_alpha_bad_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_fixed_trace_alpha_bad trace_table)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  let ?M = "checked_staged_transcript_with_alpha_prefix_program A"
  let ?Fresh =
    "checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried
      trace_table"
  let ?Pre =
    "checked_staged_transcript_fixed_trace_alpha_prequery_hit trace_table"
  have event_le:
    "wp_event ?M
      (checked_staged_transcript_fixed_trace_alpha_bad trace_table)
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Fresh out \<or> ?Pre out)
      adversary_initial_state"
    by (rule wp_event_mono) (rule checked_staged_transcript_fixed_trace_alpha_bad_split)
  also have "... \<le>
      wp_event ?M ?Fresh adversary_initial_state +
      wp_event ?M ?Pre adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (intro add_mono
        checked_staged_transcript_fixed_trace_alpha_bad_excluding_prequeried_bound
        checked_staged_transcript_fixed_trace_alpha_prequery_bound
        wf controlled)
  finally show ?thesis .
qed

end

end
