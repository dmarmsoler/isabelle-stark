(*  Title:      Stark/Staged_Security_Experiment_Composition_Partial.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Partial
  imports
    Staged_Security_Experiment_Composition_Branch
    Soundness_Reductions_Composition
begin

text \<open>
  Partial-candidate composition reductions for the staged security experiment.

  This layer avoids treating verifier-side Merkle subtree recomputation as a
  rare event.  Instead, it lifts the verifier-local reduction from composition
  alpha badness to a partial-header candidate event plus hash collision.
\<close>

context soundness
begin

definition checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      bad_sets out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, final_state) \<Rightarrow>
          (let packed = fst (fst x);
               data = snd packed;
               attacker_state = snd (fst x);
               result = snd x;
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in alpha_header_list_set_hit s
             (alpha_header_supported_partial_union_bad_sets s bad_sets)
             (Some (result, final_state))))"

definition checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
      bad_sets out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, final_state) \<Rightarrow>
          (let packed = fst (fst x);
               prefix_state = snd (fst packed);
               data = snd packed;
               attacker_state = snd (fst x);
               result = snd x;
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in alpha_header_list_set_hit s
             (alpha_header_supported_partial_union_bad_sets s bad_sets)
             (Some (result, final_state)) \<and>
             alpha_vector_prequeried_in_state prefix_state
              (staged_alphas data) (length spec)))"

definition checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
      bad_sets out \<longleftrightarrow>
      checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        bad_sets out \<and>
      (case out of
        None \<Rightarrow> False
      | Some (x, _) \<Rightarrow>
          (let packed = fst (fst x);
               prefix_state = snd (fst packed);
               data = snd packed
           in \<not> alpha_vector_prequeried_in_state prefix_state
              (staged_alphas data) (length spec)))"

definition checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
      bad_sets out \<longleftrightarrow>
      checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
        bad_sets out \<and>
      \<not> checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        bad_sets out"

definition checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      out \<longleftrightarrow>
      checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad out \<and>
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
        composition_trace_bad_alpha_space out"

definition staged_alpha_prefix_partial_header_prequery_hit
  :: "'f staged_adversary \<Rightarrow> ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_alpha_prefix_partial_header_prequery_hit A bad_sets out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (prefix, prefix_state) \<Rightarrow>
          (\<exists>data attacker_state result final_state.
            Some (((((prefix, prefix_state), data), attacker_state),
              result), final_state) \<in>
              set_dist
                (execute
                  (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
                    A)
                  adversary_initial_state) \<and>
            checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
              bad_sets
              (Some (((((prefix, prefix_state), data), attacker_state),
                result), final_state))))"

definition staged_alpha_prefix_partial_header_prequery_relation
  :: "'f staged_adversary \<Rightarrow> 'f protocol_channel \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "staged_alpha_prefix_partial_header_prequery_relation A s bad_sets x y
      \<longleftrightarrow>
      (\<exists>prefix prefix_state data attacker_state result final_state i.
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
                A) s) \<and>
        checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
          bad_sets
          (Some (((((prefix, prefix_state), data), attacker_state), result),
            final_state)) \<and>
        i < length spec \<and>
        i < length (staged_alphas data) \<and>
        x = alpha_challenge_key_at prefix_state i (staged_alphas data) \<and>
        y = staged_alphas data ! i)"

lemma staged_alpha_prefix_partial_header_prequery_relation_fiber_bound_size:
  "card
    {y. staged_alpha_prefix_partial_header_prequery_relation A s bad_sets x y}
    \<le> size"
proof -
  have subset:
    "{y. staged_alpha_prefix_partial_header_prequery_relation A s bad_sets x y}
      \<subseteq> (UNIV :: 'f set)"
    by simp
  have finite_field: "finite (UNIV :: 'f set)"
    by simp
  have "card
      {y. staged_alpha_prefix_partial_header_prequery_relation A s bad_sets x y}
      \<le> card (UNIV :: 'f set)"
    by (rule card_mono[OF finite_field subset])
  also have "... = size"
    using size_card by simp
  finally show ?thesis .
qed

lemma staged_alpha_prefix_partial_header_prequery_hit_imp_relation_hit:
  assumes empty: "HashMap s = fmempty"
    and support:
      "Some (prefix, prefix_state) \<in>
        set_dist (execute (staged_alpha_prefix_program A) s)"
    and hit:
      "staged_alpha_prefix_partial_header_prequery_hit A bad_sets
        (Some (prefix, prefix_state))"
    and init: "s = adversary_initial_state"
  shows
    "hash_relation_hit_event
      (staged_alpha_prefix_partial_header_prequery_relation A s bad_sets)
      s (Some (prefix, prefix_state))"
proof -
  from hit obtain data attacker_state result final_state where full_support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and prehit:
      "checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        bad_sets
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
    unfolding staged_alpha_prefix_partial_header_prequery_hit_def by auto
  from prehit obtain i where
    i_bound: "i < length spec"
    and i_len: "i < length (staged_alphas data)"
    and lookup:
      "fmlookup (HashMap prefix_state)
        (alpha_challenge_key_at prefix_state i (staged_alphas data)) =
        Some (staged_alphas data ! i)"
    unfolding
      checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit_def
      alpha_vector_prequeried_in_state_def
    by (auto simp: Let_def)
  have initial_none:
    "fmlookup (HashMap s)
      (alpha_challenge_key_at prefix_state i (staged_alphas data)) = None"
    using empty by simp
  have relation:
    "staged_alpha_prefix_partial_header_prequery_relation A s bad_sets
      (alpha_challenge_key_at prefix_state i (staged_alphas data))
      (staged_alphas data ! i)"
    unfolding staged_alpha_prefix_partial_header_prequery_relation_def
    using full_support prehit i_bound i_len init by blast
  have
    "hash_relation_hit
      (staged_alpha_prefix_partial_header_prequery_relation A s bad_sets)
      s prefix_state"
    unfolding hash_relation_hit_def
    by (intro exI[of _ "alpha_challenge_key_at prefix_state i
          (staged_alphas data)"]
        exI[of _ "staged_alphas data ! i"] conjI)
      (use initial_none lookup relation in simp_all)
  then show ?thesis
    unfolding hash_relation_hit_event_def by simp
qed

lemma staged_alpha_prefix_partial_header_prequery_hit_bound_by_relation_hit:
  assumes init: "s = adversary_initial_state"
  shows
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_partial_header_prequery_hit A bad_sets) s \<le>
     wp_event (staged_alpha_prefix_program A)
      (hash_relation_hit_event
        (staged_alpha_prefix_partial_header_prequery_relation A s bad_sets) s)
      s"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in> set_dist (execute (staged_alpha_prefix_program A) s)"
    and hit:
      "staged_alpha_prefix_partial_header_prequery_hit A bad_sets out"
  show
    "hash_relation_hit_event
      (staged_alpha_prefix_partial_header_prequery_relation A s bad_sets) s
      out"
  proof (cases out)
    case None
    then show ?thesis
      using hit unfolding staged_alpha_prefix_partial_header_prequery_hit_def
      by simp
  next
    case (Some packed)
    then obtain prefix prefix_state where out_eq:
      "out = Some (prefix, prefix_state)"
      by (cases packed) simp
    show ?thesis
      unfolding out_eq
      by (rule staged_alpha_prefix_partial_header_prequery_hit_imp_relation_hit
          [OF _ _ _ init])
        (use support hit out_eq init in
          \<open>simp_all add: adversary_initial_state_def\<close>)
  qed
qed

lemma staged_alpha_prefix_partial_header_prequery_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_partial_header_prequery_hit A bad_sets)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  have prehit_le_relation:
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_partial_header_prequery_hit A bad_sets)
      adversary_initial_state \<le>
     wp_event (staged_alpha_prefix_program A)
      (hash_relation_hit_event
        (staged_alpha_prefix_partial_header_prequery_relation A
          adversary_initial_state bad_sets) adversary_initial_state)
      adversary_initial_state"
    by (rule staged_alpha_prefix_partial_header_prequery_hit_bound_by_relation_hit)
      simp
  also have "... \<le>
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
  proof -
    have program:
      "hash_relation_program
        (staged_alpha_prefix_partial_header_prequery_relation A
          adversary_initial_state bad_sets)
        size (staged_alpha_search_queries budgets 0)
        (staged_alpha_prefix_program A)"
      by (rule hash_relation_program_staged_alpha_prefix_program
          [OF wf controlled])
        (rule
          staged_alpha_prefix_partial_header_prequery_relation_fiber_bound_size)
    show ?thesis
      using program
      unfolding hash_relation_program_def hash_relation_budget_def
        staged_phase_relation_error_def
      by blast
  qed
  finally show ?thesis .
qed

lemma checked_staged_security_experiment_with_actual_alpha_prefix_data_stateI:
  assumes prefix:
      "Some (prefix, prefix_state) \<in>
        set_dist
          (execute (staged_alpha_prefix_program A) adversary_initial_state)"
    and after:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_after_alpha_prefix_program A prefix)
            prefix_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
  shows
    "Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
proof -
  have transcript:
    "Some (((prefix, prefix_state), data), attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_with_alpha_prefix_program A)
          adversary_initial_state)"
    unfolding checked_staged_transcript_with_alpha_prefix_program_def
    apply (rule_tac x=prefix and t=prefix_state in set_dist_bindI)
     apply (rule prefix)
    apply (rule_tac x=prefix_state and t=prefix_state in set_dist_bindI)
     apply simp
    apply (rule_tac x=data and t=attacker_state in set_dist_bindI)
     apply (rule after)
    apply simp
    done
  show ?thesis
    unfolding
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    apply (rule_tac x="((prefix, prefix_state), data)" and
        t=attacker_state in set_dist_bindI)
     apply (rule transcript)
    apply (rule_tac x=attacker_state and t=attacker_state in set_dist_bindI)
     apply simp
    apply (rule_tac x="()" and
        t="verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)" in set_dist_bindI)
     apply simp
    apply (rule_tac x=result and t=final_state in set_dist_bindI)
     apply (rule verifier)
    apply simp
    done
qed

lemma checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit_bound_from_prefix:
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        bad_sets)
      adversary_initial_state \<le>
     wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_partial_header_prequery_hit A bad_sets)
      adversary_initial_state"
  unfolding checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    checked_staged_transcript_with_alpha_prefix_program_def
    sm_bind_assoc
  apply (rule wp_event_bind_bound_by_head_event
      [where P = "staged_alpha_prefix_partial_header_prequery_hit A bad_sets"])
    apply simp
   apply (simp add:
      checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit_def
      staged_alpha_prefix_partial_header_prequery_hit_def)
  apply (auto simp:
      checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit_def
      staged_alpha_prefix_partial_header_prequery_hit_def Let_def
      elim!: set_dist_bindE
      intro!: set_dist_bindI
        checked_staged_security_experiment_with_actual_alpha_prefix_data_stateI
      split: option.splits prod.splits)
  apply (rule_tac x=bi in exI)
  apply (rule_tac x=bj in exI)
  apply (rule_tac x=bk in exI)
  apply (rule_tac x=x2a in exI)
  apply (intro conjI)
    apply (rule checked_staged_security_experiment_with_actual_alpha_prefix_data_stateI)
      apply assumption
     apply assumption
    apply assumption
   apply assumption
  apply assumption
  done

lemma checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        bad_sets)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  have
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        bad_sets)
      adversary_initial_state \<le>
     wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_partial_header_prequery_hit A bad_sets)
      adversary_initial_state"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit_bound_from_prefix)
  also have "... \<le>
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule staged_alpha_prefix_partial_header_prequery_hit_bound
        [OF wf controlled])
  finally show ?thesis .
qed

text \<open>
  Vector-valued, prefix-state-dependent accounting for future alpha challenge
  keys.  The bad vector set may be selected from the concrete verifier/header
  state reached after the alpha prefix; the bound is derived from the existing
  relation-budget interface for the prefix program, not from a freshness
  assumption.
\<close>

lemma checked_staged_security_with_actual_alpha_prefix_vector_alpha_prequery_accounting:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        bad_sets)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
  by (rule
      checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit_bound
      [OF wf controlled])

lemma checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_imp_fresh_or_prequery:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      bad_sets out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
      bad_sets out \<or>
     checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
      bad_sets out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_def
    checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit_def
    checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit_def
  by (auto simp: Let_def split: option.splits prod.splits)

lemma checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_bound_from_fresh_and_prequery:
  assumes fresh_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
          bad_sets)
        adversary_initial_state \<le> F"
    and prequery_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
          bad_sets)
        adversary_initial_state \<le> P"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        bad_sets)
      adversary_initial_state \<le> F + P"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Bad =
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      bad_sets"
  let ?Fresh =
    "checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
      bad_sets"
  let ?Pre =
    "checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
      bad_sets"
  have "wp_event ?M ?Bad adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?Fresh out \<or> ?Pre out) adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_imp_fresh_or_prequery)
  also have "... \<le>
      wp_event ?M ?Fresh adversary_initial_state +
      wp_event ?M ?Pre adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> F + P"
    by (intro add_mono fresh_bound prequery_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_bound_from_fresh_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fresh_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
          bad_sets)
        adversary_initial_state \<le> F"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        bad_sets)
      adversary_initial_state \<le>
      F + staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  have prequery_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        bad_sets)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_vector_alpha_prequery_accounting
        [OF wf controlled])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_bound_from_fresh_and_prequery
        [OF fresh_bound prequery_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit_imp_prefix_or_drift:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
      bad_sets out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit bad_sets
      out \<or>
     checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
      bad_sets out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_def
  by blast

lemma checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit_bound_from_prefix_and_drift:
  assumes prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          bad_sets)
        adversary_initial_state \<le> P"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          bad_sets)
        adversary_initial_state \<le> D"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
        bad_sets)
      adversary_initial_state \<le> P + D"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Fresh =
    "checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
      bad_sets"
  let ?Prefix =
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit bad_sets"
  let ?Drift =
    "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
      bad_sets"
  have "wp_event ?M ?Fresh adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?Prefix out \<or> ?Drift out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit_imp_prefix_or_drift)
  also have "... \<le>
      wp_event ?M ?Prefix adversary_initial_state +
      wp_event ?M ?Drift adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> P + D"
    by (intro add_mono prefix_bound drift_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_imp_branch_tree_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and drift:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      out"
proof -
  have random_bad:
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad out"
    using drift
    unfolding
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
    by simp
  have not_prefix:
    "\<not> checked_staged_security_with_actual_alpha_prefix_bad_set_hit
      composition_trace_bad_alpha_space out"
    using drift
    unfolding
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_def
    by simp
  have split:
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space out \<or>
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
        out"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_imp_prefix_or_branch_tree_on_support
        [OF wf controlled support random_bad])
  then show ?thesis
    using not_prefix by blast
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_branch_tree:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and branch_tree_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
        adversary_initial_state \<le> T"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> T"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  have "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le>
    wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_imp_branch_tree_on_support
        [OF wf controlled])
  then show ?thesis
    by (rule order_trans[OF _ branch_tree_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_bound_from_prefix_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          bad_sets)
        adversary_initial_state \<le> P"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          bad_sets)
        adversary_initial_state \<le> D"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        bad_sets)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  have fresh_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit
        bad_sets)
      adversary_initial_state \<le> P + D"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit_bound_from_prefix_and_drift
        [OF prefix_bound drift_bound])
  have
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        bad_sets)
      adversary_initial_state \<le>
      (P + D) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_bound_from_fresh_and_budgets
        [OF wf controlled fresh_bound])
  then show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_imp_partial_header_or_collision_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and bad:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_verifier_event
        hash_map_output_collision_bad out"
proof (cases out)
  case None
  then show ?thesis
    using bad
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
  have random_bad:
    "composition_randomization_bad ?s (Some (result, final_state))"
    using bad
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      Let_def
    by simp
  have alpha_bad:
    "alpha_bad_set_hit ?s composition_trace_bad_alpha_space
      (Some (result, final_state))"
    by (rule composition_randomization_bad_imp_alpha_bad_set_hit
        [OF random_bad])
  have split:
    "alpha_header_list_set_hit ?s
        (alpha_header_supported_partial_union_bad_sets ?s
          composition_trace_bad_alpha_space)
        (Some (result, final_state)) \<or>
     hash_map_output_collision_bad ?s (Some (result, final_state))"
    by (rule alpha_bad_set_hit_imp_partial_union_or_collision
        [OF verify_out alpha_bad
          composition_trace_bad_alpha_space_subset_alpha_space])
  then show ?thesis
  proof
    assume partial:
      "alpha_header_list_set_hit ?s
        (alpha_header_supported_partial_union_bad_sets ?s
          composition_trace_bad_alpha_space)
        (Some (result, final_state))"
    have
      "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        composition_trace_bad_alpha_space out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_def
        Let_def
      using partial by simp
    then show ?thesis by simp
  next
    assume collision:
      "hash_map_output_collision_bad ?s (Some (result, final_state))"
    have
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        hash_map_output_collision_bad out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        Let_def
      using collision by simp
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_imp_prefix_prequery_drift_or_collision_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and bad:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
        out \<or>
     checked_staged_security_with_actual_alpha_prefix_verifier_event
        hash_map_output_collision_bad out"
proof -
  have partial_or_collision:
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        composition_trace_bad_alpha_space out \<or>
     checked_staged_security_with_actual_alpha_prefix_verifier_event
        hash_map_output_collision_bad out"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_imp_partial_header_or_collision_on_support
        [OF support bad])
  then show ?thesis
  proof
    assume partial:
      "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        composition_trace_bad_alpha_space out"
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
          "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
            out"
          unfolding
            checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
          using bad drift by simp
        then show ?thesis by simp
      qed
    next
      assume
        "checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
          composition_trace_bad_alpha_space out"
      then show ?thesis by simp
    qed
  next
    assume
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        hash_map_output_collision_bad out"
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_bound_from_prefix_prequery_drift_and_collision:
  assumes prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and prequery_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> Q"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
        adversary_initial_state \<le> D"
    and collision_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad)
      adversary_initial_state \<le> P + Q + D + C"
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
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift"
  let ?Collision =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      hash_map_output_collision_bad"
  let ?Random =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad"
  have "wp_event ?M ?Random adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?Prefix out \<or> ?Prequery out \<or> ?Drift out \<or>
          ?Collision out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_imp_prefix_prequery_drift_or_collision_on_support)
  also have "... \<le>
      wp_event ?M ?Prefix adversary_initial_state +
      wp_event ?M ?Prequery adversary_initial_state +
      wp_event ?M ?Drift adversary_initial_state +
      wp_event ?M ?Collision adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le> P + Q + D + C"
    by (intro add_mono prefix_bound prequery_bound drift_bound
        collision_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_bound_from_partial_header_and_collision:
  assumes partial_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and collision_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad)
      adversary_initial_state \<le> P + C"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Partial =
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      composition_trace_bad_alpha_space"
  let ?Collision =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      hash_map_output_collision_bad"
  let ?Random =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad"
  have "wp_event ?M ?Random adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?Partial out \<or> ?Collision out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_imp_partial_header_or_collision_on_support)
  also have "... \<le>
      wp_event ?M ?Partial adversary_initial_state +
      wp_event ?M ?Collision adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> P + C"
    by (intro add_mono partial_bound collision_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_partial_header_and_collision:
  assumes partial_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and collision_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le> P + C"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?degree =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_degree_bad"
  let ?random =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad"
  let ?bad =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_bad"
  have projected:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state =
     wp_event ?M ?bad adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection)
  have event_eq: "?bad = (\<lambda>out. ?degree out \<or> ?random out)"
    by (rule ext)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        composition_bad_def split: option.splits prod.splits)
  have degree_false: "?degree = (\<lambda>out. False)"
    by (rule ext)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        composition_degree_bad_false[OF spec_degree_wellformed_from_spec_query_margin]
        split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    unfolding degree_false wp_event_def wp_def dist_expect_def by simp
  have random_bound:
    "wp_event ?M ?random adversary_initial_state \<le> P + C"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_bound_from_partial_header_and_collision
        [OF partial_bound collision_bound])
  have "wp_event ?M ?bad adversary_initial_state \<le>
      wp_event ?M ?degree adversary_initial_state +
      wp_event ?M ?random adversary_initial_state"
    unfolding event_eq by (rule wp_event_union_bound)
  also have "... \<le> 0 + (P + C)"
    by (intro add_mono degree_bound random_bound)
  finally show ?thesis
    unfolding projected by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_hash_map_output_collision_bad_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have data_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  then show ?thesis
    using
      checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection
        [of A hash_map_output_collision_bad]
    by simp
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_partial_header_and_controlled_collision:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and partial_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      P +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have collision_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_partial_header_and_collision
        [OF partial_bound collision_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_partial_header_candidate_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  let ?Prefix =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  have transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?Prefix"
    by (rule
        checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets
        [OF wf controlled])
  have prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?Prefix"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have partial_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      ?Prefix + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_bound_from_prefix_drift_and_budgets
        [OF wf controlled prefix_bound drift_bound])
  have
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      (?Prefix + D +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0)) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_partial_header_and_controlled_collision
        [OF wf controlled partial_bound])
  then show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_partial_prequery_branch_tree_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and branch_tree_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
        adversary_initial_state \<le> T"
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
      T +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Prefix =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  let ?Pre =
    "staged_phase_relation_error size
      (staged_alpha_search_queries budgets 0)"
  let ?Coll =
    "hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget)"
  have transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?Prefix"
    by (rule
        checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets
        [OF wf controlled])
  have prefix_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?Prefix"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have prequery_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_partial_header_prequery_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?Pre"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_vector_alpha_prequery_accounting
        [OF wf controlled])
  have drift_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> T"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_branch_tree
        [OF wf controlled branch_tree_bound])
  have collision_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state \<le> ?Coll"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  let ?degree =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_degree_bad"
  let ?random =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad"
  let ?bad =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_bad"
  have projected:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state =
     wp_event ?M ?bad adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection)
  have event_eq: "?bad = (\<lambda>out. ?degree out \<or> ?random out)"
    by (rule ext)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        composition_bad_def split: option.splits prod.splits)
  have degree_false: "?degree = (\<lambda>out. False)"
    by (rule ext)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        composition_degree_bad_false[OF spec_degree_wellformed_from_spec_query_margin]
        split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    unfolding degree_false wp_event_def wp_def dist_expect_def by simp
  have random_bound:
    "wp_event ?M ?random adversary_initial_state \<le>
      ?Prefix + ?Pre + T + ?Coll"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_bound_from_prefix_prequery_drift_and_collision
        [OF prefix_bound prequery_bound drift_bound collision_bound])
  have "wp_event ?M ?bad adversary_initial_state \<le>
      wp_event ?M ?degree adversary_initial_state +
      wp_event ?M ?random adversary_initial_state"
    unfolding event_eq by (rule wp_event_union_bound)
  also have "... \<le> 0 + (?Prefix + ?Pre + T + ?Coll)"
    by (intro add_mono degree_bound random_bound)
  finally show ?thesis
    unfolding projected by (simp add: add.assoc)
qed

end

end
