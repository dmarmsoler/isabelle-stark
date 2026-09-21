(*  Title:      Stark/Soundness_FRI_State_Dependent_Query_Product.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_State_Dependent_Query_Product
  imports Soundness_FRI_Prechallenge_Query_Product
begin

text \<open>
  Query-list products for a target family selected after the checked transcript
  builder has finished.  This is the fresh-path half of the prefix-conditioned
  argument: each realized builder output may select its own small target family,
  without taking a union over all reachable outputs.
\<close>

context soundness
begin

definition staged_security_with_data_state_dependent_query_index_list_path_fresh
  where
  "staged_security_with_data_state_dependent_query_index_list_path_fresh Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((data, attacker_state), result), final_state) \<Rightarrow>
        staged_security_with_data_state_query_index_list_path_fresh
          (Q data attacker_state)
          (Some (((data, attacker_state), result), final_state)))"

lemma staged_security_with_data_state_dependent_query_index_list_path_fresh_None[simp]:
  "\<not> staged_security_with_data_state_dependent_query_index_list_path_fresh Q None"
  unfolding staged_security_with_data_state_dependent_query_index_list_path_fresh_def
  by simp

lemma checked_staged_security_with_data_state_dependent_query_index_list_path_fresh_product_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<Longrightarrow>
        Q data attacker_state \<subseteq> fri_query_index_list_space"
    and card_bound:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<Longrightarrow>
        card (Q data attacker_state) \<le> N"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_dependent_query_index_list_path_fresh Q)
      adversary_initial_state \<le>
      nnreal N *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof -
  let ?P =
    "staged_security_with_data_state_dependent_query_index_list_path_fresh Q"
  have none: "\<not> ?P None"
    by simp
  have cont_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (\<lambda>out.
          ?P
            (case out of
              None \<Rightarrow> None
            | Some (result, final_state) \<Rightarrow>
                Some (((data, attacker_state), result), final_state)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        \<le> nnreal N *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
  proof -
    fix data attacker_state
    assume builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    let ?Q = "Q data attacker_state"
    let ?R = "(nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    have local:
      "wp_event verify_monad
        (\<lambda>out.
          staged_security_with_data_state_query_index_list_path_fresh ?Q
            (case out of
              None \<Rightarrow> None
            | Some (result, final_state) \<Rightarrow>
                Some (((data, attacker_state), result), final_state)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        \<le> nnreal (card ?Q) * ?R"
      by (rule
          verify_monad_query_index_list_path_fresh_product_bound_after_builder
            [OF wf controlled subset[OF builder] builder])
    have event_eq:
      "(\<lambda>out.
          ?P
            (case out of
              None \<Rightarrow> None
            | Some (result, final_state) \<Rightarrow>
                Some (((data, attacker_state), result), final_state))) =
       (\<lambda>out.
          staged_security_with_data_state_query_index_list_path_fresh ?Q
            (case out of
              None \<Rightarrow> None
            | Some (result, final_state) \<Rightarrow>
                Some (((data, attacker_state), result), final_state)))"
      unfolding staged_security_with_data_state_dependent_query_index_list_path_fresh_def
      by (rule ext) (auto split: option.splits prod.splits)
    have cast_bound: "nnreal (card ?Q) \<le> nnreal N"
      using card_bound[OF builder] by simp
    have product_bound: "nnreal (card ?Q) * ?R \<le> nnreal N * ?R"
      by (rule mult_right_mono[OF cast_bound]) simp
    show
      "wp_event verify_monad
        (\<lambda>out.
          ?P
            (case out of
              None \<Rightarrow> None
            | Some (result, final_state) \<Rightarrow>
                Some (((data, attacker_state), result), final_state)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        \<le> nnreal N * ?R"
      unfolding event_eq
      by (rule order_trans[OF local product_bound])
  qed
  show ?thesis
    by (rule checked_staged_security_with_data_state_bound_from_data_cont
        [OF none cont_bound])
qed

lemma checked_staged_security_with_data_state_dependent_base_agreement_path_fresh_product_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_low:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree (trace_table data attacker_state)"
    and trace'_low:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree (trace_table' data attacker_state)"
    and distinct:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<Longrightarrow>
        trace_table data attacker_state \<noteq>
          trace_table' data attacker_state"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_dependent_query_index_list_path_fresh
        (\<lambda>data attacker_state.
          trace_table_base_agreement_query_lists
            (trace_table data attacker_state)
            (trace_table' data attacker_state)))
      adversary_initial_state \<le>
      nnreal (clength ^ rounds) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof (rule
    checked_staged_security_with_data_state_dependent_query_index_list_path_fresh_product_bound
      [OF wf controlled])
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  show
    "trace_table_base_agreement_query_lists
        (trace_table data attacker_state)
        (trace_table' data attacker_state)
      \<subseteq> fri_query_index_list_space"
    by (rule trace_table_base_agreement_query_lists_subset)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  have agreement_le:
    "card
        (trace_table_base_agreement_indices
          (trace_table data attacker_state)
          (trace_table' data attacker_state))
      \<le> clength"
    using trace_table_base_agreement_indices_card_bound
        [OF trace_low[OF builder] trace'_low[OF builder]
          distinct[OF builder]]
    by simp
  show
    "card
        (trace_table_base_agreement_query_lists
          (trace_table data attacker_state)
          (trace_table' data attacker_state))
      \<le> clength ^ rounds"
    unfolding card_trace_table_base_agreement_query_lists
    by (rule power_mono[OF agreement_le]) simp
qed

end

end
