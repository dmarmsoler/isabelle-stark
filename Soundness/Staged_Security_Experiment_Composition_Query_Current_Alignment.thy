(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Current_Alignment.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Current_Alignment
  imports Staged_Security_Experiment_Composition_Query_Current
begin

text \<open>
  Query-prefix alignment facts for the current-final-state composition-query
  route.  This theory is intentionally narrow so that the already large
  current-query projection theory does not grow past the project size
  threshold.
\<close>

context soundness
begin

lemma checked_staged_security_experiment_with_query_prefix_data_state_outcomeI:
  assumes prefix_receive:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    and after:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive A i
              ((prefix, prefix_state), raw))
            raw_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
  shows
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
proof -
  have with_verifier:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive_with_verifier A i
            ((prefix, prefix_state), raw))
          raw_state)"
    unfolding checked_staged_after_query_prefix_receive_with_verifier_def
    apply (rule_tac x=data and t=attacker_state in set_dist_bindI)
     apply (rule after)
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
  show ?thesis
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
    apply (rule set_dist_bindI[OF prefix_receive])
    apply (rule_tac x=raw_state and t=raw_state in set_dist_bindI)
     apply simp
    apply (rule_tac x="((data, attacker_state), result)" and
        t=final_state in set_dist_bindI)
     apply (rule with_verifier)
    apply simp
    done
qed

lemma checked_staged_after_query_prefix_receive_alphas:
  assumes after:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive A i
            ((prefix, prefix_state), raw))
          raw_state)"
  shows "staged_alphas data = sqp_alphas prefix"
  using after
  unfolding checked_staged_after_query_prefix_receive_def Let_def
  by (auto elim!: set_dist_bindE split: prod.splits)

lemma checked_staged_security_with_actual_alpha_prefix_support_query_prefix_data_stateE:
  assumes i_bound: "i < rounds"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
  obtains prefix prefix_state raw raw_state where
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist (execute verify_monad ?s)"
    by blast
  from checked_staged_transcript_program_query_prefix_receive_cont_support
      [OF i_bound builder]
  obtain prefix prefix_state raw raw_state where prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and after:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive A i
              ((prefix, prefix_state), raw))
            raw_state)"
    by blast
  have qprefix_support:
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    by (rule checked_staged_security_experiment_with_query_prefix_data_state_outcomeI
        [OF prefix_receive after verifier])
  show ?thesis
    by (rule that[OF qprefix_support])
qed

lemma checked_staged_security_with_actual_alpha_prefix_support_query_prefix_data_state_alphasE:
  assumes i_bound: "i < rounds"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
  obtains prefix prefix_state raw raw_state where
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    "sqp_alphas prefix = staged_alphas data"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist (execute verify_monad ?s)"
    by blast
  from checked_staged_transcript_program_query_prefix_receive_cont_support
      [OF i_bound builder]
  obtain prefix prefix_state raw raw_state where prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and after:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive A i
              ((prefix, prefix_state), raw))
            raw_state)"
    by blast
  have qprefix_support:
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    by (rule checked_staged_security_experiment_with_query_prefix_data_state_outcomeI
        [OF prefix_receive after verifier])
  have alphas_eq: "sqp_alphas prefix = staged_alphas data"
    using checked_staged_after_query_prefix_receive_alphas[OF after]
    by simp
  show ?thesis
    by (rule that[OF qprefix_support alphas_eq])
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_success_query_prefix_hitE:
  assumes i_bound: "i < rounds"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and success:
      "\<And>prefix prefix_state raw raw_state.
        Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        sqp_alphas prefix = staged_alphas data \<Longrightarrow>
        index (to_nat raw) \<in>
          query_sampling_success_space trace_table composition_table
            (staged_alphas data)"
  obtains prefix prefix_state raw raw_state where
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    "checked_staged_security_with_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  from checked_staged_security_with_actual_alpha_prefix_support_query_prefix_data_state_alphasE
      [OF i_bound support]
  obtain prefix prefix_state raw raw_state where qprefix_support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    by blast
  have hit:
    "checked_staged_security_with_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    using success[OF qprefix_support alphas_eq] alphas_eq
    unfolding
      checked_staged_security_with_query_prefix_dynamic_index_hit_def
      checked_staged_query_prefix_dynamic_index_hit_def
      staged_query_prefix_candidate_pair_query_target_from_prefix_def
    by simp
  show ?thesis
    by (rule that[OF qprefix_support hit])
qed

lemma checked_staged_actual_alpha_prefix_current_query_partial_opening_hit_at_imp_query_prefix_current_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "staged_security_with_data_state_current_query_partial_opening_hit_at i
        (Some (((data, attacker_state), result), final_state))"
  obtains prefix prefix_state raw raw_state where
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  have decomp:
    "checked_staged_transcript_program A =
      checked_staged_query_prefix_receive_with_state A i \<bind>
        checked_staged_after_query_prefix_receive A i"
    by (rule checked_staged_transcript_program_query_prefix_receive_decomp
        [OF i_bound])
  from builder[unfolded decomp]
  obtain prefix_out raw_state where prefix_receive:
      "Some (prefix_out, raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and after:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive A i prefix_out)
            raw_state)"
    by (elim set_dist_bindE)
  obtain prefix prefix_state raw where prefix_out_eq:
      "prefix_out = ((prefix, prefix_state), raw)"
    by (cases prefix_out) auto
  have qprefix_support:
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    by (rule checked_staged_security_experiment_with_query_prefix_data_state_outcomeI)
      (use prefix_receive after verifier prefix_out_eq in simp_all)
  have qprefix_hit:
    "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    by (rule
        staged_security_with_data_state_current_query_partial_opening_hit_at_imp_query_prefix_current_on_support
        [OF wf controlled i_bound qprefix_support hit])
  show ?thesis
    by (rule that[OF qprefix_support qprefix_hit])
qed

definition checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at
  :: "nat \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at
      i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        staged_security_with_data_state_current_query_partial_opening_hit_at i
          (Some (((data, attacker_state), result), final_state)))"

definition checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
      out \<longleftrightarrow>
    (\<exists>i \<in> {..<rounds}.
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at
        i out)"

lemma checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_imp_query_prefix_current_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at
        i out"
  shows
    "\<exists>prefix prefix_state raw raw_state data attacker_state result final_state.
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state) \<and>
      checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix alpha_prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed) (auto split: prod.splits)
  have data_hit:
    "staged_security_with_data_state_current_query_partial_opening_hit_at i
      (Some (((data, attacker_state), result), final_state))"
    using hit
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_def
    by simp
  have support_some:
    "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
      result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
    using support out_eq by simp
  from checked_staged_actual_alpha_prefix_current_query_partial_opening_hit_at_imp_query_prefix_current_on_support
      [OF wf controlled i_bound support_some data_hit]
  obtain prefix prefix_state raw raw_state where qsupport:
      "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and qhit:
      "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
    by blast
  show ?thesis
    using qsupport qhit by blast
qed

lemma checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_bound_from_query_prefix_current:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and query_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le> Q"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_query_partial_opening_hit_at i)
      adversary_initial_state"
  proof -
    have
      "wp_event
        (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_query_partial_opening_hit_at i)
        adversary_initial_state =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
          \<bind> (\<lambda>x. return (?project x)))
        (staged_security_with_data_state_current_query_partial_opening_hit_at i)
        adversary_initial_state"
      using
        checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
        [of A]
      by simp
    also have "... =
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        (checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state"
    proof -
      have pred_eq:
        "(\<lambda>out. case out of
          None \<Rightarrow>
            staged_security_with_data_state_current_query_partial_opening_hit_at
              i None
        | Some (x, t) \<Rightarrow>
            staged_security_with_data_state_current_query_partial_opening_hit_at
              i (Some (?project x, t))) =
        checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at
          i"
        by (rule ext)
          (simp add:
            checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_def
            staged_security_with_data_state_current_query_partial_opening_hit_at_def
            split: option.splits prod.splits)
      show ?thesis
        by (subst wp_event_bind_return_map) (simp add: pred_eq)
    qed
    finally show ?thesis
      by simp
  qed
  have data_bound:
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le> Q"
    by (rule order_trans
        [OF
          checked_staged_security_with_data_state_current_query_partial_opening_hit_at_le_query_prefix_current
          query_prefix_bound])
      (use wf controlled i_bound in simp_all)
  show ?thesis
    unfolding projection by (rule data_bound)
qed

lemma checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_bound_from_query_prefix_current_rounds:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
proof -
  have round_le:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        (checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le> C i"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_bound_from_query_prefix_current
        [OF wf controlled _ round_bound])
  have
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
      adversary_initial_state \<le>
    wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. \<exists>i \<in> {..<rounds}.
        checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at
          i out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (simp add:
        checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_def)
  also have "... \<le> (\<Sum>i<rounds. C i)"
    by (rule wp_event_finite_UN_bound)
      (simp_all add: round_le)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_projection:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
    adversary_initial_state =
   wp_event
    (checked_staged_security_experiment_with_data_state A)
    staged_security_with_data_state_current_query_partial_opening_hit
    adversary_initial_state"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
        \<bind> (\<lambda>x. return (?project x)))
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state"
    using
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
      [of A]
    by simp
  also have "... =
    wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
      adversary_initial_state"
  proof -
    have pred_eq:
      "(\<lambda>out. case out of
        None \<Rightarrow>
          staged_security_with_data_state_current_query_partial_opening_hit
            None
      | Some (x, t) \<Rightarrow>
          staged_security_with_data_state_current_query_partial_opening_hit
            (Some (?project x, t))) =
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit"
      by (rule ext)
        (auto simp:
          checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_def
          checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_def
          staged_security_with_data_state_current_query_partial_opening_hit_def
          staged_security_with_data_state_current_query_partial_opening_hit_at_def
          split: option.splits prod.splits)
    show ?thesis
      by (subst wp_event_bind_return_map) (simp add: pred_eq)
  qed
  finally show ?thesis
    by simp
qed

lemma checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_actual_alpha_current_query:
  assumes bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
      adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> Q"
  using bound
  unfolding
    checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_projection
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_current_query_partial_opening_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_def
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix alpha_prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed) (auto split: prod.splits)
  have support_some:
    "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
      result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
    using support out_eq by simp
  have hit_some:
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    using hit out_eq by simp
  have data_hit:
    "staged_security_with_data_state_current_query_partial_opening_hit
      (Some (((data, attacker_state), result), final_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_data_state_current_partial_opening_hit_on_support
        [OF wf controlled support_some hit_some])
  then obtain i where i_bound: "i < rounds"
    and round_hit:
      "staged_security_with_data_state_current_query_partial_opening_hit_at i
        (Some (((data, attacker_state), result), final_state))"
    unfolding staged_security_with_data_state_current_query_partial_opening_hit_def
    by blast
  have actual_round:
    "checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at
      i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    using round_hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_def
    by simp
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_def
    using i_bound actual_round by blast
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_actual_alpha_current_query:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and current_query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> Q"
  by (rule order_trans[
      OF _ current_query_bound])
    (rule wp_event_mono_on_support,
      rule checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_current_query_partial_opening_hit_on_support
        [OF wf controlled])

lemma checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_aligned_transcript_classification_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state))"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at
        i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
  shows
    "trace_fri_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     composition_fri_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     query_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     (\<exists>trace_table composition_table trace_openings_i
        composition_openings_i.
      partial_trace_table_candidate trace_table
        (trace_openings[i := trace_openings_i]) \<and>
      partial_composition_table_candidate composition_table
        (composition_openings[i := composition_openings_i]) \<and>
      trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as)"
proof -
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  have data_hit:
    "staged_security_with_data_state_current_query_partial_opening_hit_at i
      (Some (((data, attacker_state), result), final_state))"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_def
    by simp
  show ?thesis
    by (rule
        staged_security_with_data_state_current_query_partial_opening_hit_at_aligned_transcript_classification_on_support
        [OF wf controlled data_support partial no_bad data_hit])
qed

lemma checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_aligned_transcript_classification_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state))"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
  shows
    "trace_fri_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     composition_fri_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     query_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     (\<exists>i trace_table composition_table trace_openings_i
        composition_openings_i.
      i < rounds \<and>
      partial_trace_table_candidate trace_table
        (trace_openings[i := trace_openings_i]) \<and>
      partial_composition_table_candidate composition_table
        (composition_openings[i := composition_openings_i]) \<and>
      trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as)"
proof -
  from hit obtain i where i_bound: "i < rounds"
    and round_hit:
      "checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at
        i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    unfolding
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_def
    by blast
  have classified:
    "trace_fri_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     composition_fri_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     query_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     (\<exists>trace_table composition_table trace_openings_i
        composition_openings_i.
      partial_trace_table_candidate trace_table
        (trace_openings[i := trace_openings_i]) \<and>
      partial_composition_table_candidate composition_table
        (composition_openings[i := composition_openings_i]) \<and>
      trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_at_aligned_transcript_classification_on_support
        [OF wf controlled support partial no_bad round_hit])
  then show ?thesis
    using i_bound by blast
qed

lemma checked_staged_actual_alpha_prefix_query_prefix_receive_alignment_from_final_lookup:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and final_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
  obtains prefix prefix_state raw_state where
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "sqp_alphas prefix = staged_alphas data"
    "sqp_query_chunks prefix = take i (staged_query_chunks data)"
    "PQueryCounter prefix_state = i"
    "PState prefix_state =
      state_after_query_chunks
        (staged_query_start_hash data) (staged_query_chunks data) i"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  show ?thesis
  proof (rule checked_staged_transcript_program_query_prefix_receive_support
      [OF wf controlled i_bound builder])
    fix prefix prefix_state raw' raw_state
    assume prefix_receive:
        "Some (((prefix, prefix_state), raw'), raw_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_receive_with_state A i)
              adversary_initial_state)"
      and alphas_eq: "sqp_alphas prefix = staged_alphas data"
      and chunks_eq:
        "sqp_query_chunks prefix = take i (staged_query_chunks data)"
      and counter_eq: "PQueryCounter prefix_state = i"
      and state_eq:
        "PState prefix_state =
          state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i"
      and raw_ext: "raw_state \<le> attacker_state"
      and raw_lookup:
        "fmlookup (HashMap raw_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data) (staged_query_chunks data) i)) =
          Some raw'"
    have raw_ext_s: "raw_state \<le> ?s"
      by (rule hash_extends_verifier_state_from_adversary_right[OF raw_ext])
    have s_ext_final: "?s \<le> final_state"
      by (rule verify_monad_hash_extends[OF verifier])
    have raw_ext_final: "raw_state \<le> final_state"
      by (rule hash_ext_trans[OF raw_ext_s s_ext_final])
    have final_lookup_raw':
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw'"
      by (rule hash_extension_lookup[OF raw_lookup raw_ext_final])
    have raw_eq: "raw' = raw"
      using final_lookup final_lookup_raw' by simp
    have prefix_receive_raw:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
      using prefix_receive raw_eq by simp
    show ?thesis
      by (rule that[OF prefix_receive_raw alphas_eq chunks_eq counter_eq
            state_eq])
  qed
qed

end

end
