(*  Title:      Stark/Soundness_Aligned_Partial_Query_Prefix.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Aligned_Partial_Query_Prefix
  imports
    Soundness_Aligned_Partial_Query_Transcript
    Soundness_Staged_Candidate_Query
    Soundness_Staged_Transcript
begin

text \<open>
  Bridge aligned partial-query evidence to prefix-local staged query targets.

  The lemmas here are deterministic: they say that, once a verifier query
  index is replayed to a prefix receive and the prefix alphas agree with the
  accepted transcript, the aligned partial-candidate query evidence produces a
  hit in the existing prefix-local target.  Probability bounds remain in the
  staged prefix-target layer.
\<close>

context soundness
begin

definition checked_staged_security_experiment_with_query_prefix_data_state
  where
    "checked_staged_security_experiment_with_query_prefix_data_state A i =
      checked_staged_query_prefix_receive_with_state A i \<bind>
        (\<lambda>prefix_out. get \<bind>
        (\<lambda>prefix_state.
          checked_staged_after_query_prefix_receive_with_verifier A i
            prefix_out \<bind>
          (\<lambda>out. return ((prefix_out, prefix_state), out))))"

lemma checked_staged_security_experiment_with_query_prefix_data_state_projection:
  assumes i_bound: "i < rounds"
  shows
    "checked_staged_security_experiment_with_query_prefix_data_state A i \<bind>
        (\<lambda>packed. return (snd packed)) =
      checked_staged_security_experiment_with_data_state A"
  unfolding
    checked_staged_security_experiment_with_query_prefix_data_state_def
    checked_staged_security_experiment_with_data_state_query_prefix_receive_decomp
      [OF i_bound]
  by (simp add: sm_bind_assoc get_bind_const)

lemma checked_staged_security_experiment_with_query_prefix_data_state_projection_event:
  assumes i_bound: "i < rounds"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A) E
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out. case out of
        None \<Rightarrow> E None
      | Some (packed, t) \<Rightarrow> E (Some (snd packed, t)))
      adversary_initial_state"
proof -
  have
    "wp_event (checked_staged_security_experiment_with_data_state A) E
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i \<bind>
        (\<lambda>packed. return (snd packed)))
      E adversary_initial_state"
    using
      checked_staged_security_experiment_with_query_prefix_data_state_projection
        [OF i_bound, of A]
    by simp
  also have "... =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out. case out of
        None \<Rightarrow> E None
      | Some (packed, t) \<Rightarrow> E (Some (snd packed, t)))
      adversary_initial_state"
    by (rule wp_event_bind_return_map)
  finally show ?thesis .
qed

lemma checked_staged_security_experiment_with_query_prefix_data_state_imp_data_state_support:
  assumes i_bound: "i < rounds"
    and outcome:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state)
        \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
  shows
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
proof -
  from outcome obtain t where prefix_receive:
      "Some (((prefix, prefix_state), raw), t) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and t_eq: "t = raw_state"
    and cont:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive_with_verifier A i
              ((prefix, prefix_state), raw))
            raw_state)"
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have data_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive A i
            ((prefix, prefix_state), raw))
          raw_state)"
    by (rule checked_staged_after_query_prefix_receive_with_verifier_outcome(1)
        [OF cont])
  have verifier:
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    by (rule checked_staged_after_query_prefix_receive_with_verifier_outcome(2)
        [OF cont])
  have builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    unfolding checked_staged_transcript_program_query_prefix_receive_decomp
      [OF i_bound]
    apply (rule_tac x="((prefix, prefix_state), raw)" and
        t=raw_state in set_dist_bindI)
     apply (rule prefix_receive[unfolded t_eq])
    apply (rule data_out)
    done
  show ?thesis
    by (rule checked_staged_security_experiment_with_data_state_outcomeI
        [OF builder verifier])
qed

lemma checked_staged_security_experiment_with_query_prefix_data_state_bound_by_prefix:
  assumes prefix_bound:
      "wp_event (checked_staged_query_prefix_receive_with_state A i) P
        adversary_initial_state \<le> B"
    and none_imp: "Q None \<Longrightarrow> P None"
    and cont_imp:
      "\<And>prefix_out t out.
        Some (prefix_out, t) \<in>
          set_dist
            (execute (checked_staged_query_prefix_receive_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        out \<in>
          set_dist
            (execute
              (get \<bind>
                (\<lambda>prefix_state.
                  checked_staged_after_query_prefix_receive_with_verifier A i
                    prefix_out \<bind>
                  (\<lambda>result. return ((prefix_out, prefix_state), result))))
              t) \<Longrightarrow>
        Q out \<Longrightarrow> P (Some (prefix_out, t))"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      Q adversary_initial_state \<le> B"
  unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
  by (rule wp_event_bind_bound_by_head_event
      [OF prefix_bound none_imp cont_imp])

definition checked_staged_security_with_query_prefix_dynamic_index_hit
  where
    "checked_staged_security_with_query_prefix_dynamic_index_hit T out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((((prefix_pack, raw), raw_state), result), final_state)) \<Rightarrow>
          checked_staged_query_prefix_dynamic_index_hit T
            (Some ((prefix_pack, raw), raw_state)))"

definition checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
  where
    "checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
        trace_table composition_table out \<longleftrightarrow>
      checked_staged_security_with_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table) out"

lemma checked_staged_security_with_query_prefix_dynamic_index_hit_bound:
  assumes prefix_bound:
      "wp_event (checked_staged_query_prefix_receive_with_state A i)
        (checked_staged_query_prefix_dynamic_index_hit T)
        adversary_initial_state \<le> B"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit T)
      adversary_initial_state \<le> B"
proof (rule
    checked_staged_security_experiment_with_query_prefix_data_state_bound_by_prefix
      [OF prefix_bound])
  show
    "checked_staged_security_with_query_prefix_dynamic_index_hit T None \<Longrightarrow>
      checked_staged_query_prefix_dynamic_index_hit T None"
    unfolding checked_staged_security_with_query_prefix_dynamic_index_hit_def
    by simp
next
  fix prefix_out t out
  assume head:
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
  assume hit:
    "checked_staged_security_with_query_prefix_dynamic_index_hit T out"
  show
    "checked_staged_query_prefix_dynamic_index_hit T
      (Some (prefix_out, t))"
    using cont hit
    unfolding checked_staged_security_with_query_prefix_dynamic_index_hit_def
    by (auto elim!: set_dist_bindE split: option.splits prod.splits)
qed

lemma checked_staged_query_prefix_dynamic_index_hit_bound_from_fraction:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and target_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        T prefix prefix_state \<subseteq> query_sample_space \<and>
        nnreal
          (query_raw_preimage_card_envelope
            (card (T prefix prefix_state))) /
          nnreal size \<le> C"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit T)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + C"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit T)
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit T)
      adversary_initial_state + C"
    by (rule
        checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
        [OF raw_bound target_bound])
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit T)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
  proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
    show "HashMap adversary_initial_state = fmempty"
      by (simp add: adversary_initial_state_def)
    show "hash_relation_program
        (checked_staged_query_prefix_dynamic_index_prehit_relation A i
          adversary_initial_state T)
        size (staged_query_search_queries budgets i + 1)
        (checked_staged_query_prefix_receive_with_state A i)"
      by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
          [OF wf controlled])
        (use i_bound in simp_all,
          rule checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
  qed
  show ?thesis
    by (rule order_trans[OF hit_bound])
      (intro add_mono prehit_bound order_refl)
qed

lemma checked_staged_security_with_query_prefix_dynamic_index_hit_bound_from_fraction:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and target_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        T prefix prefix_state \<subseteq> query_sample_space \<and>
        nnreal
          (query_raw_preimage_card_envelope
            (card (T prefix prefix_state))) /
          nnreal size \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit T)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + C"
  by (rule checked_staged_security_with_query_prefix_dynamic_index_hit_bound,
      rule checked_staged_query_prefix_dynamic_index_hit_bound_from_fraction
        [OF wf controlled i_bound target_bound])

lemma checked_staged_security_with_query_prefix_candidate_opening_target_from_prefix_hit_bound:
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
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
  by (rule checked_staged_security_with_query_prefix_dynamic_index_hit_bound,
      rule checked_staged_query_prefix_candidate_opening_target_from_prefix_hit_bound
        [OF raw_bound wf controlled i_bound trace_candidate comp_candidate
          trace_low comp_low not_all])

lemma checked_staged_security_with_query_prefix_candidate_opening_target_from_prefix_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_candidate_opening_target_from_prefix_hit_bound
        [OF raw_bound wf controlled _ trace_candidate comp_candidate trace_low
          comp_low not_all])
      (use i_bound in simp)
qed

lemma checked_staged_security_with_query_prefix_candidate_pair_target_from_prefix_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_pair_query_target_from_prefix
          trace_table composition_table))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
  by (rule checked_staged_security_with_query_prefix_dynamic_index_hit_bound,
      rule checked_staged_query_prefix_candidate_pair_target_from_prefix_hit_bound
        [OF raw_bound wf controlled i_bound trace_low comp_low not_all])

lemma checked_staged_security_with_query_prefix_candidate_pair_target_from_prefix_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
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
        checked_staged_security_with_query_prefix_candidate_pair_target_from_prefix_hit_bound
        [OF raw_bound wf controlled _ trace_low comp_low not_all])
      (use i_bound in simp)
qed

lemma checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> all_queries_consistent trace_table composition_table
          (sqp_alphas prefix)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit
        trace_table composition_table)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
  unfolding
    checked_staged_security_with_query_prefix_candidate_pair_from_prefix_hit_def
  by (rule
      checked_staged_security_with_query_prefix_candidate_pair_target_from_prefix_hit_bound_from_budgets
      [OF wf controlled i_bound trace_low comp_low not_all])

lemma powers_scaled_eq_imp_eq:
  assumes "powers_scaled idx = powers_scaled idx'"
  shows "idx = idx'"
proof -
  have left: "powers_scaled idx ! 0 = idx"
    unfolding powers_scaled_def using powers_pos by simp
  have right: "powers_scaled idx' ! 0 = idx'"
    unfolding powers_scaled_def using powers_pos by simp
  show ?thesis
    using assms left right by metis
qed

lemma partial_query_success_indices_at_card_le_one:
  "card (partial_query_success_indices_at trace_openings
      composition_openings as i) \<le> Suc 0"
proof -
  have finite_target:
    "finite (partial_query_success_indices_at trace_openings
      composition_openings as i)"
    by (rule finite_subset[OF partial_query_success_indices_at_subset
          finite_query_sample_space])
  have pairwise:
    "\<forall>idx \<in> partial_query_success_indices_at trace_openings
        composition_openings as i.
      \<forall>idx' \<in> partial_query_success_indices_at trace_openings
        composition_openings as i.
        idx = idx'"
  proof (intro ballI)
    fix idx idx'
    assume idx_in:
        "idx \<in> partial_query_success_indices_at trace_openings
          composition_openings as i"
      and idx'_in:
        "idx' \<in> partial_query_success_indices_at trace_openings
          composition_openings as i"
    have idx_indices:
      "map opening_index (trace_openings ! i) = powers_scaled idx"
      using idx_in
      unfolding partial_query_success_indices_at_def
        partial_query_round_consistent_def
      by simp
    have idx'_indices:
      "map opening_index (trace_openings ! i) = powers_scaled idx'"
      using idx'_in
      unfolding partial_query_success_indices_at_def
        partial_query_round_consistent_def
      by simp
    have "powers_scaled idx = powers_scaled idx'"
      using idx_indices idx'_indices by simp
    then show "idx = idx'"
      by (rule powers_scaled_eq_imp_eq)
  qed
  show ?thesis
    using card_le_Suc0_iff_eq[OF finite_target] pairwise by simp
qed

lemma prob_divide_right_mono:
  assumes "(a::prob) \<le> b"
  shows "a / c \<le> b / c"
  using assms
  apply transfer
  by (simp add: divide_right_mono)

lemma partial_query_success_indices_at_singleton_fraction_bound:
  "nnreal
      (query_raw_preimage_card_envelope
        (card
          (partial_query_success_indices_at trace_openings
            composition_openings as i))) /
    nnreal size \<le>
    nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have card_le:
    "card
      (partial_query_success_indices_at trace_openings composition_openings
        as i) \<le> 1"
    using partial_query_success_indices_at_card_le_one by simp
  have envelope_le:
    "query_raw_preimage_card_envelope
      (card
        (partial_query_success_indices_at trace_openings composition_openings
          as i)) \<le>
     query_raw_preimage_card_envelope 1"
    by (rule query_raw_preimage_card_envelope_mono[OF card_le])
  show ?thesis
    by (rule nnreal_nat_divide_right_mono[OF envelope_le])
qed

lemma staged_query_prefix_candidate_opening_query_target_from_prefix_singleton_fraction_bound:
  "nnreal
      (query_raw_preimage_card_envelope
        (card
          (staged_query_prefix_candidate_opening_query_target_from_prefix
            trace_openings composition_openings i prefix prefix_state))) /
    nnreal size \<le>
    nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
  unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
  by (rule partial_query_success_indices_at_singleton_fraction_bound)

lemma checked_staged_query_prefix_candidate_opening_target_from_prefix_singleton_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
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
      adversary_initial_state +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
  proof (rule checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    show
      "staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i prefix prefix_state \<subseteq>
        query_sample_space \<and>
       nnreal
        (query_raw_preimage_card_envelope
          (card
            (staged_query_prefix_candidate_opening_query_target_from_prefix
              trace_openings composition_openings i prefix prefix_state))) /
        nnreal size
        \<le> nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
      using
        staged_query_prefix_candidate_opening_query_target_from_prefix_subset
        staged_query_prefix_candidate_opening_query_target_from_prefix_singleton_fraction_bound
      by blast
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
    by (rule checked_staged_query_prefix_candidate_opening_target_from_prefix_prehit_bound
        [OF wf controlled i_bound])
  have tail:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
    by (intro add_mono prehit_bound order_refl)
  show ?thesis
    by (rule order_trans[OF hit_bound tail])
qed

lemma checked_staged_security_with_query_prefix_candidate_opening_target_from_prefix_singleton_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
  by (rule checked_staged_security_with_query_prefix_dynamic_index_hit_bound,
      rule
        checked_staged_query_prefix_candidate_opening_target_from_prefix_singleton_hit_bound
        [OF raw_bound wf controlled i_bound])

lemma checked_staged_security_with_query_prefix_candidate_opening_target_from_prefix_singleton_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          trace_openings composition_openings i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_candidate_opening_target_from_prefix_singleton_hit_bound
        [OF raw_bound wf controlled])
      (use i_bound in simp)
qed

definition checked_staged_security_with_actual_query_prefix_candidate_opening_hit
where
  "checked_staged_security_with_actual_query_prefix_candidate_opening_hit
      trace_openings composition_openings i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        trace_openings composition_openings i) out"

lemma checked_staged_security_with_actual_query_prefix_candidate_opening_hitE:
  assumes hit:
    "checked_staged_security_with_actual_query_prefix_candidate_opening_hit
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
  obtains
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        trace_openings composition_openings i prefix prefix_state"
  using hit
  unfolding
    checked_staged_security_with_actual_query_prefix_candidate_opening_hit_def
    checked_staged_security_with_query_prefix_dynamic_index_hit_def
    checked_staged_query_prefix_dynamic_index_hit_def
  by simp

lemma checked_staged_security_with_actual_query_prefix_candidate_opening_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
  unfolding
    checked_staged_security_with_actual_query_prefix_candidate_opening_hit_def
  by (rule
      checked_staged_security_with_query_prefix_candidate_opening_target_from_prefix_singleton_hit_bound
      [OF raw_bound wf controlled i_bound])

lemma checked_staged_security_with_actual_query_prefix_candidate_opening_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
  unfolding
    checked_staged_security_with_actual_query_prefix_candidate_opening_hit_def
  by (rule
      checked_staged_security_with_query_prefix_candidate_opening_target_from_prefix_singleton_hit_bound_from_budgets
      [OF wf controlled i_bound])

lemma checked_staged_security_with_data_state_bound_by_actual_query_prefix_candidate_opening_hit:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and event_imp:
      "\<And>out.
        (case out of
          None \<Rightarrow> E None
        | Some (packed, t) \<Rightarrow> E (Some (snd packed, t))) \<Longrightarrow>
        checked_staged_security_with_actual_query_prefix_candidate_opening_hit
          trace_openings composition_openings i out"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A) E
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have projection:
    "wp_event (checked_staged_security_experiment_with_data_state A) E
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out. case out of
        None \<Rightarrow> E None
      | Some (packed, t) \<Rightarrow> E (Some (snd packed, t)))
      adversary_initial_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound])
  have lifted_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out. case out of
        None \<Rightarrow> E None
      | Some (packed, t) \<Rightarrow> E (Some (snd packed, t)))
      adversary_initial_state \<le>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
          trace_openings composition_openings i)
        adversary_initial_state"
    by (rule wp_event_mono) (use event_imp in blast)
  have fixed_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
    by (rule
        checked_staged_security_with_actual_query_prefix_candidate_opening_hit_bound
        [OF raw_bound wf controlled])
      (use i_bound in simp)
  show ?thesis
    unfolding projection
    by (rule order_trans[OF lifted_bound fixed_bound])
qed

lemma checked_staged_security_with_data_state_bound_by_actual_query_prefix_candidate_opening_hit_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and event_imp:
      "\<And>out.
        (case out of
          None \<Rightarrow> E None
        | Some (packed, t) \<Rightarrow> E (Some (snd packed, t))) \<Longrightarrow>
        checked_staged_security_with_actual_query_prefix_candidate_opening_hit
          trace_openings composition_openings i out"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A) E
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_bound_by_actual_query_prefix_candidate_opening_hit
        [OF raw_bound wf controlled i_bound event_imp])
qed

lemma checked_staged_security_with_query_prefix_data_state_bound_by_actual_query_prefix_candidate_opening_hit:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and event_imp:
      "\<And>out. E out \<Longrightarrow>
        checked_staged_security_with_actual_query_prefix_candidate_opening_hit
          trace_openings composition_openings i out"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      E adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      E adversary_initial_state \<le>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
          trace_openings composition_openings i)
        adversary_initial_state"
    by (rule wp_event_mono) (rule event_imp)
  have fixed_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
    by (rule
        checked_staged_security_with_actual_query_prefix_candidate_opening_hit_bound
        [OF raw_bound wf controlled])
      (use i_bound in simp)
  show ?thesis
    by (rule order_trans[OF event_le fixed_bound])
qed

lemma checked_staged_security_with_query_prefix_data_state_bound_by_actual_query_prefix_candidate_opening_hit_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and event_imp:
      "\<And>out. E out \<Longrightarrow>
        checked_staged_security_with_actual_query_prefix_candidate_opening_hit
          trace_openings composition_openings i out"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      E adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_data_state_bound_by_actual_query_prefix_candidate_opening_hit
        [OF raw_bound wf controlled i_bound event_imp])
qed

lemma checked_staged_query_prefix_with_state_alpha_prefix_support:
  assumes outcome:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
  obtains alpha_prefix alpha_prefix_state where
    "alpha_prefix =
      (sqp_trace_root prefix, sqp_trace_fri_roots prefix,
        sqp_trace_fri_challenges prefix, sqp_trace_final prefix)"
    "Some (alpha_prefix, alpha_prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
proof -
  from outcome obtain prefix_out prefix_state' where prefix_program_out:
    "Some (prefix_out, prefix_state') \<in>
      set_dist
        (execute (checked_staged_query_challenge_prefix_program A i)
          adversary_initial_state)"
    and prefix_eq0: "prefix_out = prefix"
    unfolding checked_staged_query_prefix_with_state_def
    by (auto elim!: set_dist_bindE dest!: get_bind_return_state_outcome)
  obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5 as
      s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 query_start query_chunks where
    fr_out:
      "Some (fr, s1) \<in>
        set_dist (execute (trace_root_stage A) adversary_initial_state)"
    and record_fr:
      "Some ((), s2) \<in> set_dist (execute (record_staged_message fr) s1)"
    and trace_fri:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and trace_final_out:
      "Some (trace_final, s4) \<in>
        set_dist (execute (trace_final_stage A trace_bs) s3)"
    and record_trace_final:
      "Some ((), s5) \<in>
        set_dist (execute (record_staged_message trace_final) s4)"
    and alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s5)"
    and degree_out:
      "Some (dg, s7) \<in> set_dist (execute (degree_stage A as) s6)"
    and record_degree:
      "Some ((), s8) \<in>
        set_dist (execute (record_staged_message dg) s7)"
    and assert_degree:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert (ceil_log (to_nat dg + 1) \<le>
              ceil_log (maxDegree + 1))) s8)"
    and comp_fri:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s9)"
    and comp_final:
      "Some (composition_final, s11) \<in>
        set_dist
          (execute (composition_final_stage A dg composition_bs) s10)"
    and record_comp_final:
      "Some ((), query_start) \<in>
        set_dist (execute (record_staged_message composition_final) s11)"
    and query_prefix:
      "Some (query_chunks, prefix_state') \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              0 i) query_start)"
    and prefix_out_eq:
      "prefix_out =
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
    by (rule checked_staged_query_challenge_prefix_program_outcomeE[
        OF prefix_program_out])
  have prefix_eq:
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
    using prefix_eq0 prefix_out_eq by simp
  let ?alpha_prefix = "(fr, trace_roots, trace_bs, trace_final)"
  have alpha_prefix_out:
    "Some (?alpha_prefix, s5) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
  proof -
    have after_record_final:
      "Some (?alpha_prefix, s5) \<in>
        set_dist
          (execute
            (record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))
            s4)"
      by (rule_tac x="()" and t=s5 in set_dist_bindI)
        (rule record_trace_final, simp)
    have after_final:
      "Some (?alpha_prefix, s5) \<in>
        set_dist
          (execute
            (trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))
            s3)"
      by (rule_tac x=trace_final and t=s4 in set_dist_bindI)
        (rule trace_final_out, rule after_record_final)
    have after_trace:
      "Some (?alpha_prefix, s5) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
              (\<lambda>(trace_roots, trace_bs).
                trace_final_stage A trace_bs \<bind>
                (\<lambda>trace_final.
                  record_staged_message trace_final \<bind>
                  (\<lambda>_. return
                    (fr, trace_roots, trace_bs, trace_final)))))
            s2)"
      apply (rule_tac x="(trace_roots, trace_bs)" and t=s3
          in set_dist_bindI)
       apply (rule trace_fri)
      apply (simp add: after_final)
      done
    have after_record_root:
      "Some (?alpha_prefix, s5) \<in>
        set_dist
          (execute
            (record_staged_message fr \<bind>
              (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
                (\<lambda>(trace_roots, trace_bs).
                  trace_final_stage A trace_bs \<bind>
                  (\<lambda>trace_final.
                    record_staged_message trace_final \<bind>
                    (\<lambda>_. return
                      (fr, trace_roots, trace_bs, trace_final))))))
            s1)"
      by (rule_tac x="()" and t=s2 in set_dist_bindI)
        (rule record_fr, rule after_trace)
    show ?thesis
      unfolding staged_alpha_prefix_program_def
      apply (rule_tac x=fr and t=s1 in set_dist_bindI)
       apply (rule fr_out)
      apply (rule after_record_root)
      done
  qed
  show ?thesis
    by (rule that[OF _ alpha_prefix_out]) (simp add: prefix_eq)
qed

lemma checked_staged_security_with_query_prefix_data_state_alpha_prefix_support:
  assumes outcome:
    "Some (((((prefix, prefix_state), raw), raw_state), result), final_state)
      \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
  obtains alpha_prefix alpha_prefix_state where
    "alpha_prefix =
      (sqp_trace_root prefix, sqp_trace_fri_roots prefix,
        sqp_trace_fri_challenges prefix, sqp_trace_final prefix)"
    "Some (alpha_prefix, alpha_prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
proof -
  from outcome obtain t where prefix_receive:
    "Some (((prefix, prefix_state), raw), t) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    and t_eq: "t = raw_state"
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
    by (auto elim!: set_dist_bindE)
  have prefix_support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
    by (rule checked_staged_query_prefix_receive_with_state_prefix_support)
      (use prefix_receive t_eq in simp)
  show ?thesis
    by (rule
        checked_staged_query_prefix_with_state_alpha_prefix_support
          [OF prefix_support])
      (rule that)
qed

lemma checked_staged_security_with_query_prefix_data_state_alphas_eq:
  assumes outcome:
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)
      \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
  shows "staged_alphas data = sqp_alphas prefix"
  using outcome
  unfolding
    checked_staged_security_experiment_with_query_prefix_data_state_def
    checked_staged_after_query_prefix_receive_with_verifier_def
    checked_staged_after_query_prefix_receive_def
  by (auto elim!: set_dist_bindE split: prod.splits)

definition checked_staged_security_with_query_prefix_authenticated_opening_hit
where
  "checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        staged_composition_fri_roots data \<noteq> [] \<and>
        partial_authenticated_table (staged_trace_root data)
          (scale * clength) trace_openings final_state \<and>
        partial_authenticated_table (hd (staged_composition_fri_roots data))
          (scale * clength) composition_openings final_state \<and>
        partial_query_openings_consistent trace_openings composition_openings
          (staged_alphas data) (index (to_nat raw)))"

definition checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
where
  "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
      trace_openings composition_openings i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        staged_composition_fri_roots data \<noteq> [] \<and>
        partial_authenticated_table (staged_trace_root data)
          (scale * clength) trace_openings prefix_state \<and>
        partial_authenticated_table (hd (staged_composition_fri_roots data))
          (scale * clength) composition_openings prefix_state \<and>
        partial_query_openings_consistent trace_openings composition_openings
          (staged_alphas data) (index (to_nat raw)))"

definition checked_staged_security_with_query_prefix_opening_path_output_hit
where
  "checked_staged_security_with_query_prefix_opening_path_output_hit
      trace_openings composition_openings out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        (\<exists>opening \<in> set trace_openings \<union> set composition_openings.
          hash_map_new_output_hit
            (merkle_path_target_roots final_state
              (opening_root opening)
              (opening_length opening)
              (opening_index opening)
              (opening_value opening)
              (opening_path opening))
            prefix_state final_state))"

lemma checked_staged_security_with_query_prefix_opening_path_output_hitE:
  assumes hit:
    "checked_staged_security_with_query_prefix_opening_path_output_hit
      trace_openings composition_openings out"
  obtains prefix prefix_state raw raw_state data attacker_state result
      final_state opn where
    "out = Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state)"
    "opn \<in> set trace_openings \<union> set composition_openings"
    "hash_map_new_output_hit
      (merkle_path_target_roots final_state
        (opening_root opn)
        (opening_length opn)
        (opening_index opn)
        (opening_value opn)
        (opening_path opn))
      prefix_state final_state"
    "finite
      (merkle_path_target_roots final_state
        (opening_root opn)
        (opening_length opn)
        (opening_index opn)
        (opening_value opn)
        (opening_path opn))"
    "card
      (merkle_path_target_roots final_state
        (opening_root opn)
        (opening_length opn)
        (opening_index opn)
        (opening_value opn)
        (opening_path opn)) \<le> Suc (length (opening_path opn))"
  using hit
  unfolding checked_staged_security_with_query_prefix_opening_path_output_hit_def
  by (cases out)
    (auto intro: that card_merkle_path_target_roots_le split: prod.splits)

lemma checked_staged_security_experiment_with_query_prefix_data_state_prefix_extends_final:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and outcome:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state)
        \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
  shows "prefix_state \<le> final_state"
proof -
  from outcome obtain t where head_support:
    "Some (((prefix, prefix_state), raw), t) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    and t_eq: "t = raw_state"
    and cont_support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive_with_verifier A i
              ((prefix, prefix_state), raw))
            raw_state)"
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have head:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    using head_support t_eq by simp
  have recv:
    "Some (raw, raw_state) \<in>
      set_dist (execute receive_query_index_challenge prefix_state)"
    by (rule checked_staged_query_prefix_receive_with_state_receive_support
        [OF head])
  have prefix_ext_raw: "prefix_state \<le> raw_state"
    by (rule receive_query_index_challenge_extends[OF recv])
  have data_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive A i
            ((prefix, prefix_state), raw))
          raw_state)"
    by (rule
        checked_staged_after_query_prefix_receive_with_verifier_outcome(1)
        [OF cont_support])
  have verifier_out:
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    by (rule
        checked_staged_after_query_prefix_receive_with_verifier_outcome(2)
        [OF cont_support])
  have raw_ext_attacker: "raw_state \<le> attacker_state"
    by (rule checked_staged_after_query_prefix_receive_extends
        [OF wf controlled i_bound data_out])
  have attacker_ext_verifier:
    "attacker_state \<le>
      verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
  proof -
    have "attacker_state \<le> attacker_state"
      unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    then show ?thesis
      by (rule hash_extends_verifier_state_from_adversary_right)
  qed
  have verifier_ext_final:
    "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data) \<le>
      final_state"
    by (rule verify_monad_hash_extends[OF verifier_out])
  have raw_ext_final: "raw_state \<le> final_state"
    by (rule hash_ext_trans[OF raw_ext_attacker])
      (rule hash_ext_trans[OF attacker_ext_verifier verifier_ext_final])
  show ?thesis
    by (rule hash_ext_trans[OF prefix_ext_raw raw_ext_final])
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_prefix_or_path_output_hit:
  assumes ext: "prefix_state \<le> final_state"
    and hit:
      "checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
proof -
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
    using hit
    unfolding checked_staged_security_with_query_prefix_authenticated_opening_hit_def
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
      then have
        "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
          trace_openings composition_openings i
          (Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state))"
        using comp_nonempty trace_prefix consistent
        unfolding
          checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_def
        by simp
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
      have root_eq:
        "opening_root opn = hd (staged_composition_fri_roots data)"
        using comp_table opn_in
        unfolding partial_authenticated_table_def by blast
      have len_eq: "opening_length opn = scale * clength"
        using comp_table opn_in
        unfolding partial_authenticated_table_def by blast
      have
        "checked_staged_security_with_query_prefix_opening_path_output_hit
          trace_openings composition_openings
          (Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state))"
      proof -
        have path_hit':
          "hash_map_new_output_hit
            (merkle_path_target_roots final_state
              (opening_root opn)
              (opening_length opn)
              (opening_index opn)
              (opening_value opn)
              (opening_path opn)) prefix_state final_state"
          using path_hit root_eq len_eq by simp
        show ?thesis
          unfolding
            checked_staged_security_with_query_prefix_opening_path_output_hit_def
          using opn_in path_hit' by auto
      qed
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
    have root_eq: "opening_root opn = staged_trace_root data"
      using trace_table opn_in
      unfolding partial_authenticated_table_def by blast
    have len_eq: "opening_length opn = scale * clength"
      using trace_table opn_in
      unfolding partial_authenticated_table_def by blast
    have
      "checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
    proof -
      have path_hit':
        "hash_map_new_output_hit
          (merkle_path_target_roots final_state
            (opening_root opn)
            (opening_length opn)
            (opening_index opn)
            (opening_value opn)
            (opening_path opn)) prefix_state final_state"
        using path_hit root_eq len_eq by simp
      show ?thesis
        unfolding checked_staged_security_with_query_prefix_opening_path_output_hit_def
        using opn_in path_hit' by auto
    qed
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_prefix_or_path_output_hit_on_support:
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
      "checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding checked_staged_security_with_query_prefix_authenticated_opening_hit_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
    "out =
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)"
    by (cases packed, auto split: prod.splits)
  have ext: "prefix_state \<le> final_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_prefix_extends_final
          [OF wf controlled i_bound])
      (use support out_eq in simp)
  show ?thesis
    unfolding out_eq
    by (rule
        checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_prefix_or_path_output_hit
          [OF ext])
      (use hit out_eq in simp)
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_le_actual_query_prefix_hit:
  assumes i_bound: "i < rounds"
  shows
  "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i)
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
      "checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i out"
  show
    "checked_staged_security_with_actual_query_prefix_candidate_opening_hit
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings]) i out"
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
      by (cases packed, auto split: prod.splits)
    have alphas_eq: "staged_alphas data = sqp_alphas prefix"
      by (rule checked_staged_security_with_query_prefix_data_state_alphas_eq)
        (use support out_eq in simp)
    have consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (sqp_alphas prefix) (index (to_nat raw))"
      using hit alphas_eq
      unfolding out_eq
        checked_staged_security_with_query_prefix_authenticated_opening_hit_def
      by simp
    have target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i)
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_opening_target_from_prefix_single_round_hitI)
        (use i_bound consistent in simp_all)
    show ?thesis
      unfolding out_eq
        checked_staged_security_with_actual_query_prefix_candidate_opening_hit_def
        checked_staged_security_with_query_prefix_dynamic_index_hit_def
      using target_hit by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have actual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
    by (rule checked_staged_security_with_actual_query_prefix_candidate_opening_hit_bound
        [OF raw_bound wf controlled])
      (use i_bound in simp)
  show ?thesis
    by (rule order_trans[
        OF checked_staged_security_with_query_prefix_authenticated_opening_hit_le_actual_query_prefix_hit
          actual_bound])
      (use i_bound in simp)
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_authenticated_opening_hit_bound
        [OF raw_bound wf controlled i_bound])
qed

lemma checked_staged_security_with_query_prefix_data_state_bound_by_query_prefix_authenticated_opening_hit:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and event_imp:
      "\<And>out. E out \<Longrightarrow>
        checked_staged_security_with_query_prefix_authenticated_opening_hit
          trace_openings composition_openings i out"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      E adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      E adversary_initial_state \<le>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_authenticated_opening_hit
          trace_openings composition_openings i)
        adversary_initial_state"
    by (rule wp_event_mono) (rule event_imp)
  have fixed_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
    by (rule checked_staged_security_with_query_prefix_authenticated_opening_hit_bound
        [OF raw_bound wf controlled i_bound])
  show ?thesis
    by (rule order_trans[OF event_le fixed_bound])
qed

lemma checked_staged_security_with_query_prefix_data_state_bound_by_query_prefix_authenticated_opening_hit_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and event_imp:
      "\<And>out. E out \<Longrightarrow>
        checked_staged_security_with_query_prefix_authenticated_opening_hit
          trace_openings composition_openings i out"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      E adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_data_state_bound_by_query_prefix_authenticated_opening_hit
        [OF raw_bound wf controlled i_bound event_imp])
qed

lemma checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_le_actual_query_prefix_hit:
  assumes i_bound: "i < rounds"
  shows
  "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i)
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
      "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i out"
  show
    "checked_staged_security_with_actual_query_prefix_candidate_opening_hit
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings]) i out"
  proof (cases out)
    case None
    then show ?thesis
      using hit
      unfolding
        checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_def
      by simp
  next
    case (Some packed)
    then obtain prefix prefix_state raw raw_state data attacker_state result
        final_state where out_eq:
      "out =
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state)"
      by (cases packed, auto split: prod.splits)
    have alphas_eq: "staged_alphas data = sqp_alphas prefix"
      by (rule checked_staged_security_with_query_prefix_data_state_alphas_eq)
        (use support out_eq in simp)
    have consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (sqp_alphas prefix) (index (to_nat raw))"
      using hit alphas_eq
      unfolding out_eq
        checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_def
      by simp
    have target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i)
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_opening_target_from_prefix_single_round_hitI)
        (use i_bound consistent in simp_all)
    show ?thesis
      unfolding out_eq
        checked_staged_security_with_actual_query_prefix_candidate_opening_hit_def
        checked_staged_security_with_query_prefix_dynamic_index_hit_def
      using target_hit by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have actual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
    by (rule checked_staged_security_with_actual_query_prefix_candidate_opening_hit_bound
        [OF raw_bound wf controlled])
      (use i_bound in simp)
  show ?thesis
    by (rule order_trans[
        OF checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_le_actual_query_prefix_hit
          actual_bound])
      (use i_bound in simp)
qed

lemma checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_bound
        [OF raw_bound wf controlled i_bound])
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_bound_from_prefix_and_path_output:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
          trace_openings composition_openings i)
        adversary_initial_state \<le> P"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_opening_path_output_hit
          trace_openings composition_openings)
        adversary_initial_state \<le> path_error"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le> P + path_error"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out.
        checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
          trace_openings composition_openings i out \<or>
        checked_staged_security_with_query_prefix_opening_path_output_hit
          trace_openings composition_openings out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_prefix_or_path_output_hit_on_support
          [OF wf controlled i_bound])
  have union_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out.
        checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
          trace_openings composition_openings i out \<or>
        checked_staged_security_with_query_prefix_opening_path_output_hit
          trace_openings composition_openings out)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings)
      adversary_initial_state"
    by (rule wp_event_union_bound)
  have sum_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings)
      adversary_initial_state \<le> P + path_error"
    by (intro add_mono prefix_bound path_bound)
  show ?thesis
    by (rule order_trans[OF event_le])
      (rule order_trans[OF union_bound sum_bound])
qed

lemma checked_staged_security_with_query_prefix_authenticated_opening_hit_bound_from_path_output:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_opening_path_output_hit
          trace_openings composition_openings)
        adversary_initial_state \<le> path_error"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size + path_error"
proof -
  have prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
    by (rule checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_bound
        [OF raw_bound wf controlled i_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_authenticated_opening_hit_bound_from_prefix_and_path_output
          [OF wf controlled i_bound prefix_bound path_bound])
qed

lemma accepted_with_partial_initial_openings_aligned_consistent_prefix_target_hit:
  assumes partial:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings"
    and i_bound: "i < rounds"
    and idx_eq: "query_idxs ! i = index (to_nat raw)"
    and alphas_eq: "as = sqp_alphas prefix"
  shows
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        trace_openings composition_openings i)
      (Some (((prefix, prefix_state), raw), raw_state))"
proof -
  have success:
    "query_idxs ! i \<in>
      partial_query_success_indices_at trace_openings composition_openings
        as i"
    by (rule
        accepted_with_partial_initial_openings_aligned_consistent_success_index
        [OF partial i_bound])
  have "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        trace_openings composition_openings i prefix prefix_state"
    using success idx_eq alphas_eq
    unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
    by simp
  then show ?thesis
    unfolding checked_staged_query_prefix_dynamic_index_hit_def by simp
qed

lemma query_bad_with_aligned_partial_candidates_prefix_target_hitE:
  assumes bad: "query_bad_with_aligned_partial_candidates s out"
    and i_bound: "i < rounds"
    and idx_eq: "query_idxs ! i = index (to_nat raw)"
    and alphas_eq: "as = sqp_alphas prefix"
    and partial:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  obtains
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        trace_openings composition_openings i)
      (Some (((prefix, prefix_state), raw), raw_state))"
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (staged_query_prefix_candidate_opening_query_target_from_prefix
            trace_openings composition_openings i prefix prefix_state))) /
      nnreal size \<le> query_error_bound"
proof -
  have hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        trace_openings composition_openings i)
      (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule
        accepted_with_partial_initial_openings_aligned_consistent_prefix_target_hit
        [OF partial i_bound idx_eq alphas_eq])
  have not_all_prefix:
    "\<not> all_queries_consistent trace_table composition_table
      (sqp_alphas prefix)"
    using not_all alphas_eq by simp
  have fraction:
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (staged_query_prefix_candidate_opening_query_target_from_prefix
            trace_openings composition_openings i prefix prefix_state))) /
      nnreal size \<le> query_error_bound"
    by (rule
        staged_query_prefix_candidate_opening_query_target_from_prefix_fraction_bound
        [OF trace_candidate comp_candidate trace_low comp_low not_all_prefix])
  show ?thesis
    by (rule that[OF hit fraction])
qed

lemma accepted_with_partial_initial_openings_aligned_consistent_candidate_opening_hit_from_prefix:
  assumes partial:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings"
    and i_bound: "i < rounds"
    and idx_eq: "query_idxs ! i = index (to_nat raw)"
    and alphas_eq: "as = sqp_alphas prefix"
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
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A trace_openings composition_openings i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  have target_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        trace_openings composition_openings i)
      (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule
        accepted_with_partial_initial_openings_aligned_consistent_prefix_target_hit
        [OF partial i_bound idx_eq alphas_eq])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefixI
        [OF i_bound builder prefix_receive target_hit])
qed

lemma accepted_with_partial_initial_openings_aligned_transcript_consistent_candidate_opening_hit_from_prefix:
  assumes partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent s
        out fr f_fri_roots f_final as dg composition_fri_roots final
        query_idxs trace_openings composition_openings"
    and i_bound: "i < rounds"
    and idx_eq: "query_idxs ! i = index (to_nat raw)"
    and alphas_eq: "as = sqp_alphas prefix"
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
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A trace_openings composition_openings i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent s out fr
      f_fri_roots f_final as dg composition_fri_roots final query_idxs
      trace_openings composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  show ?thesis
    by (rule
        accepted_with_partial_initial_openings_aligned_consistent_candidate_opening_hit_from_prefix
        [OF aligned i_bound idx_eq alphas_eq builder prefix_receive])
qed

lemma query_bad_with_aligned_partial_candidates_candidate_opening_hit_from_prefixE:
  assumes bad: "query_bad_with_aligned_partial_candidates s out"
    and i_bound: "i < rounds"
    and idx_eq: "query_idxs ! i = index (to_nat raw)"
    and alphas_eq: "as = sqp_alphas prefix"
    and partial:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        f_fri_roots f_final as dg composition_fri_roots final query_idxs
        trace_openings composition_openings"
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
  obtains
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A trace_openings composition_openings i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  have hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A trace_openings composition_openings i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by (rule
        accepted_with_partial_initial_openings_aligned_consistent_candidate_opening_hit_from_prefix
        [OF partial i_bound idx_eq alphas_eq builder prefix_receive])
  show ?thesis
    by (rule that[OF hit])
qed

lemma query_bad_with_aligned_transcript_partial_candidates_candidate_opening_hit_from_prefixE:
  assumes bad: "query_bad_with_aligned_transcript_partial_candidates s out"
    and i_bound: "i < rounds"
    and idx_eq: "query_idxs ! i = index (to_nat raw)"
    and alphas_eq: "as = sqp_alphas prefix"
    and partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent s
        out fr f_fri_roots f_final as dg composition_fri_roots final
        query_idxs trace_openings composition_openings"
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
  obtains
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A trace_openings composition_openings i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  have hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A trace_openings composition_openings i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_candidate_opening_hit_from_prefix
        [OF partial i_bound idx_eq alphas_eq builder prefix_receive])
  show ?thesis
    by (rule that[OF hit])
qed

lemma partial_candidate_query_witness_candidate_opening_hit_from_prefix:
  assumes partial:
      "accepted_with_partial_initial_openings s out fr f_fri_roots f_final as
        dg composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
    and i_bound: "i < rounds"
    and alphas_eq: "as = sqp_alphas prefix"
    and consistent:
      "partial_query_openings_consistent (trace_openings ! i)
        (composition_openings ! i) as (index (to_nat raw))"
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
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A ((replicate rounds []) [i := trace_openings ! i])
        ((replicate rounds []) [i := composition_openings ! i]) i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  have target_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings ! i])
        ((replicate rounds []) [i := composition_openings ! i])
        i)
      (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule
        checked_staged_query_prefix_candidate_opening_target_from_prefix_single_round_hitI)
      (use i_bound consistent alphas_eq in simp_all)
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefixI
        [OF i_bound builder prefix_receive target_hit])
qed

lemma query_bad_with_partial_candidates_witness_candidate_opening_hit_from_prefix:
  assumes bad: "query_bad_with_partial_candidates s out"
    and partial:
      "accepted_with_partial_initial_openings s out fr f_fri_roots f_final as
        dg composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
    and i_bound: "i < rounds"
    and alphas_eq: "as = sqp_alphas prefix"
    and consistent:
      "partial_query_openings_consistent (trace_openings ! i)
        (composition_openings ! i) as (index (to_nat raw))"
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
  shows
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A ((replicate rounds []) [i := trace_openings ! i])
        ((replicate rounds []) [i := composition_openings ! i]) i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  by (rule partial_candidate_query_witness_candidate_opening_hit_from_prefix
      [OF partial trace_candidate comp_candidate trace_low comp_low not_all
        i_bound alphas_eq consistent builder prefix_receive])

end

end
