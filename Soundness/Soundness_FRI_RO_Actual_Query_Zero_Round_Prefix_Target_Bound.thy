(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Zero_Round_Prefix_Target_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Zero_Round_Prefix_Target_Bound
  imports Soundness_FRI_RO_Actual_Query_Zero_Round_State_Relation
begin

text \<open>
  Exact random-oracle accounting for the zero-round trace-root prefix target.
  The prefix contains the trace-root attacker stage and one domain-separated
  transcript absorption; the target remains fixed for the rest of the run.
\<close>

context soundness
begin

definition ro_zero_round_first_root_prefix_hash_query_budget_for
where
  "ro_zero_round_first_root_prefix_hash_query_budget_for budgets =
    trace_root_budget budgets + 1"

lemma hash_range_budget_ro_staged_first_trace_fri_root_prefix_program_zero:
  assumes zero: "ceil_log clength = 0"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (ro_zero_round_first_root_prefix_hash_query_budget_for budgets)
      (ro_staged_first_trace_fri_root_prefix_program A)"
proof -
  have root:
    "hash_range_budget (trace_root_budget budgets) (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have after_root:
    "\<And>fr. hash_range_budget (1 + (0 + 0))
      (ro_record_staged_message fr \<bind>
        (\<lambda>_. get \<bind>
          (\<lambda>prefix_state. return ((fr, [], fr), prefix_state))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_record_staged_message,
       rule hash_range_budget_bind,
       rule hash_range_budget_get,
       rule hash_range_budget_return)
  have whole:
    "hash_range_budget
      (trace_root_budget budgets + (1 + (0 + 0)))
      (ro_staged_first_trace_fri_root_prefix_program A)"
    unfolding ro_staged_first_trace_fri_root_prefix_program_def zero
    apply (simp only: nat.case)
    apply (rule hash_range_budget_bind)
     apply (rule root)
    apply (rule after_root)
    done
  show ?thesis
    using whole
    unfolding ro_zero_round_first_root_prefix_hash_query_budget_for_def
    by simp
qed

definition ro_zero_round_first_root_prefix_merkle_targets
where
  "ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state =
    (if hash_map_output_collision prefix_state then {}
     else merkle_prefix_path_targets {fst prefix} prefix_state)"

lemma ro_staged_first_trace_fri_root_prefix_zero_target_card_bound:
  assumes zero: "ceil_log clength = 0"
    and controlled: "staged_adversary_controlled budgets A"
    and head:
      "Some ((prefix, prefix_state), t) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
  shows
    "card
      (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
      \<le> 1 + 2 *
          ro_zero_round_first_root_prefix_hash_query_budget_for budgets"
proof -
  obtain fr where prefix_eq: "prefix = (fr, [], fr)"
    and state_eq: "prefix_state = t"
    using head
    unfolding ro_staged_first_trace_fri_root_prefix_program_def zero
    by (auto elim!: set_dist_bindE)
  have range:
    "hash_range_budget
      (ro_zero_round_first_root_prefix_hash_query_budget_for budgets)
      (ro_staged_first_trace_fri_root_prefix_program A)"
    by (rule
      hash_range_budget_ro_staged_first_trace_fri_root_prefix_program_zero[
        OF zero controlled])
  have output_values_initial:
    "card (hash_map_output_values prefix_state) \<le>
      card (hash_map_output_values adversary_initial_state) +
        ro_zero_round_first_root_prefix_hash_query_budget_for budgets"
    using range head state_eq
    unfolding hash_range_budget_def
    by blast
  have output_values_bound:
    "card (hash_map_output_values prefix_state) \<le>
      ro_zero_round_first_root_prefix_hash_query_budget_for budgets"
    using output_values_initial by simp
  show ?thesis
  proof (cases "hash_map_output_collision prefix_state")
    case True
    then show ?thesis
      unfolding ro_zero_round_first_root_prefix_merkle_targets_def prefix_eq
      by simp
  next
    case False
    have targets:
      "card (merkle_prefix_path_targets {fr} prefix_state) \<le>
        card {fr} + 2 * card (hash_map_output_values prefix_state)"
      by (rule card_merkle_prefix_path_targets_le_if_no_collision)
        (simp_all add: False)
    have doubled:
      "2 * card (hash_map_output_values prefix_state) \<le>
        2 * ro_zero_round_first_root_prefix_hash_query_budget_for budgets"
      by (rule mult_left_mono[OF output_values_bound]) simp
    have
      "card (merkle_prefix_path_targets {fr} prefix_state) \<le>
        1 + 2 *
          ro_zero_round_first_root_prefix_hash_query_budget_for budgets"
      by (rule order_trans[OF targets])
        (use doubled in simp)
    then show ?thesis
      unfolding ro_zero_round_first_root_prefix_merkle_targets_def prefix_eq
      by simp
  qed
qed


definition ro_checked_staged_zero_after_first_root_header_hash_query_budget_for
where
  "ro_checked_staged_zero_after_first_root_header_hash_query_budget_for budgets =
    trace_final_budget budgets +
      (1 +
        (2 * length spec +
          (degree_budget budgets +
            (1 +
              ((sum_list (composition_fri_budgets budgets) +
                  2 * ceil_log (maxDegree + 1)) +
                (composition_final_budget budgets + (1 + 0)))))))"

lemma hash_target_program_ro_checked_staged_after_first_root_zero_header:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (ro_checked_staged_zero_after_first_root_header_hash_query_budget_for
        budgets)
      (ro_checked_staged_after_first_trace_fri_root_prefix_program
        A prefix)"
proof -
  let ?trace_final = "trace_final_budget budgets"
  let ?alpha = "2 * length spec"
  let ?degree = "degree_budget budgets"
  let ?composition_fri =
    "sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  have trace_final_program:
    "hash_target_program B ?trace_final (trace_final_stage A [])"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have alpha_program:
    "hash_target_program B ?alpha
      (ro_staged_alpha_program (length spec))"
    by (rule hash_target_program_ro_staged_alpha_program)
  have degree_program:
    "\<And>as. hash_target_program B ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have composition_fri_program:
    "\<And>dg. hash_target_program B ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule
      hash_target_program_guarded_ro_staged_composition_fri_program[
        OF wf controlled])
  have composition_final_program:
    "\<And>dg bs. hash_target_program B ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  obtain fr trace_bs first_root where prefix_eq:
    "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  show ?thesis
    unfolding prefix_eq
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def zero
      ro_checked_staged_zero_after_first_root_header_hash_query_budget_for_def
      Let_def split_def
    apply (simp only: nat.case prod.sel)
    apply (rule hash_target_program_bind)
     apply (rule trace_final_program)
    subgoal for trace_final
      apply (rule hash_target_program_bind)
       apply (rule hash_target_program_ro_record_staged_message)
      subgoal
        apply (rule hash_target_program_bind)
         apply (rule alpha_program)
        subgoal for as
          apply (rule hash_target_program_bind)
           apply (rule degree_program)
          subgoal for dg
            apply (rule hash_target_program_bind)
             apply (rule hash_target_program_ro_record_staged_message)
            subgoal
              apply (subst sm_bind_assoc[symmetric])
              apply (rule hash_target_program_bind)
               apply (rule composition_fri_program)
              subgoal for composition_pair
                apply (cases composition_pair)
                apply (rule hash_target_program_bind)
                 apply (rule composition_final_program)
                subgoal for composition_final
                  apply (rule hash_target_program_bind)
                   apply (rule hash_target_program_ro_record_staged_message)
                  apply (rule hash_target_program_return)
                  done
                done
              done
            done
          done
        done
      done
    done
qed


lemma ro_checked_staged_after_first_trace_fri_root_prefix_program_zero_output_lengths:
  assumes zero: "ceil_log clength = 0"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              prefix)
            s)"
  shows
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
      length (staged_composition_fri_roots data) \<le>
        ceil_log (maxDegree + 1)"
proof -
  obtain fr trace_bs first_root where prefix_eq:
    "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  from outcome obtain trace_final as dg s5 s6
      composition_roots composition_bs s7 composition_final where    assert_out:
      "Some ((), s6) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))
            s5)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s7) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])
            s6)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = [],
         staged_trace_fri_challenges = [],
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = []\<rparr>"
    using outcome
    unfolding prefix_eq
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def zero
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
  have composition_exact:
    "length composition_roots = ceil_log (to_nat dg + 1)"
    using ro_staged_composition_fri_program_output_lengths[OF composition_out]
    by blast
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
      "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  show ?thesis
    using zero data_eq composition_exact round_bound by simp
qed

definition
  ro_checked_staged_zero_after_first_root_with_query_hash_query_budget_for
where
  "ro_checked_staged_zero_after_first_root_with_query_hash_query_budget_for
      budgets =
    ro_checked_staged_zero_after_first_root_header_hash_query_budget_for
        budgets +
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)"

lemma
  hash_target_program_ro_checked_staged_zero_after_first_root_with_query_witnesses:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (ro_checked_staged_zero_after_first_root_with_query_hash_query_budget_for
        budgets)
      (ro_checked_staged_after_first_root_with_query_witnesses_program
        A prefix_with_state)"
proof -
  let ?header =
    "ro_checked_staged_zero_after_first_root_header_hash_query_budget_for
      budgets"
  let ?query =
    "sum_list (query_opening_budgets budgets) + rounds +
      rounds * ro_checked_query_round_transcript_bound"
  have header:
    "hash_target_program B ?header
      (ro_checked_staged_after_first_trace_fri_root_prefix_program A
        (fst prefix_with_state))"
    by (rule
      hash_target_program_ro_checked_staged_after_first_root_zero_header[
        OF zero wf controlled])
  have whole:
    "hash_target_program B (?header + (0 + (?query + 0)))
      (ro_checked_staged_after_first_root_with_query_witnesses_program
        A prefix_with_state)"
    unfolding ro_checked_staged_after_first_root_with_query_witnesses_program_def
  proof (rule hash_target_program_bind_on_outcomes[OF header])
    fix s data t
    assume out:
      "Some (data, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              (fst prefix_with_state))
            s)"
    have lengths:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
        length (staged_composition_fri_roots data) \<le>
          ceil_log (maxDegree + 1)"
      by (rule
        ro_checked_staged_after_first_trace_fri_root_prefix_program_zero_output_lengths[
          OF zero out])
    show
      "hash_target_program B (0 + (?query + 0))
        (get \<bind>
          (\<lambda>query_start.
            ro_checked_staged_query_program_with_witnesses A
                (staged_trace_fri_roots data)
                (staged_composition_fri_roots data)
                query_start 0 rounds \<bind>
              (\<lambda>(raws, query_states, query_chunks).
                return
                  (prefix_with_state,
                    data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                    query_start, raws, query_states))))"
      apply (rule hash_target_program_bind)
       apply (rule hash_target_program_get)
      subgoal for query_start
        apply (rule hash_target_program_bind)
         apply (rule
          hash_target_program_ro_checked_staged_query_program_with_witnesses_closed[
            OF wf controlled conjunct1[OF lengths] conjunct2[OF lengths]])
        subgoal for query_result
          by (cases query_result)
            (simp add: hash_target_program_return)
        done
      done
  qed
  show ?thesis
    using whole
    unfolding
      ro_checked_staged_zero_after_first_root_with_query_hash_query_budget_for_def
    by simp
qed


definition ro_checked_staged_zero_round_prefix_merkle_target_hit
where
  "ro_checked_staged_zero_round_prefix_merkle_target_hit out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        hash_map_new_output_hit
          (ro_zero_round_first_root_prefix_merkle_targets
            prefix prefix_state)
          prefix_state attacker_state)"

definition ro_checked_staged_zero_round_prefix_merkle_target_error
where
  "ro_checked_staged_zero_round_prefix_merkle_target_error budgets =
    nnreal
      (ro_checked_staged_zero_after_first_root_with_query_hash_query_budget_for
          budgets *
        (1 + 2 *
          ro_zero_round_first_root_prefix_hash_query_budget_for budgets)) /
      nnreal size"

lemma wp_ro_checked_staged_zero_round_prefix_merkle_target_hit_bound:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_zero_round_prefix_merkle_target_hit
      adversary_initial_state
    \<le> ro_checked_staged_zero_round_prefix_merkle_target_error budgets"
proof -
  let ?M = "ro_staged_first_trace_fri_root_prefix_program A"
  let ?K =
    "ro_checked_staged_after_first_root_with_query_witnesses_program A"
  let ?E = "ro_checked_staged_zero_round_prefix_merkle_target_hit"
  let ?n =
    "ro_checked_staged_zero_after_first_root_with_query_hash_query_budget_for
      budgets"
  have decomposition:
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A = ?M \<bind> ?K"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_prefix_decomposition)
  show ?thesis
    unfolding decomposition
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_by_target_budget[
        where
          B="\<lambda>prefix_with_state t.
            ro_zero_round_first_root_prefix_merkle_targets
              (fst prefix_with_state) (snd prefix_with_state)" and
          n="?n" and
          C="ro_checked_staged_zero_round_prefix_merkle_target_error budgets"])
    show "\<not> ?E None"
      unfolding ro_checked_staged_zero_round_prefix_merkle_target_hit_def
      by simp
  next
    fix prefix_with_state t out
    assume head:
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
      and out_support: "out \<in> set_dist (execute (?K prefix_with_state) t)"
      and event: "?E out"
    obtain prefix prefix_state where prefix_with_state_eq:
      "prefix_with_state = (prefix, prefix_state)"
      by (cases prefix_with_state) simp
    have state_eq: "t = prefix_state"
      using head
      unfolding prefix_with_state_eq
        ro_staged_first_trace_fri_root_prefix_program_def zero
      by (auto elim!: set_dist_bindE)
    show
      "hash_new_output_hit_event
        (ro_zero_round_first_root_prefix_merkle_targets
          (fst prefix_with_state) (snd prefix_with_state))
        t out"
      using event out_support state_eq
      unfolding prefix_with_state_eq
        ro_checked_staged_zero_round_prefix_merkle_target_hit_def
        hash_new_output_hit_event_def
        ro_checked_staged_after_first_root_with_query_witnesses_program_def
      by (cases out)
        (auto elim!: set_dist_bindE split: prod.splits)
  next
    fix prefix_with_state t
    assume head:
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
    show
      "hash_target_budget
        (ro_zero_round_first_root_prefix_merkle_targets
          (fst prefix_with_state) (snd prefix_with_state))
        ?n (?K prefix_with_state)"
      by (rule hash_target_program_budget)
        (rule
          hash_target_program_ro_checked_staged_zero_after_first_root_with_query_witnesses[
            OF zero wf controlled])
  next
    fix prefix_with_state t
    assume head:
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
    obtain prefix prefix_state where prefix_with_state_eq:
      "prefix_with_state = (prefix, prefix_state)"
      by (cases prefix_with_state) simp
    have card_bound:
      "card
          (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
        \<le> 1 + 2 *
          ro_zero_round_first_root_prefix_hash_query_budget_for budgets"
      by (rule
        ro_staged_first_trace_fri_root_prefix_zero_target_card_bound[
          OF zero controlled])
        (use head prefix_with_state_eq in simp)
    have numerator_bound:
      "?n * card
          (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
        \<le> ?n *
          (1 + 2 *
            ro_zero_round_first_root_prefix_hash_query_budget_for budgets)"
      by (rule mult_left_mono[OF card_bound]) simp
    show
      "hash_target_budget_value
          (ro_zero_round_first_root_prefix_merkle_targets
            (fst prefix_with_state) (snd prefix_with_state))
          ?n
        \<le> ro_checked_staged_zero_round_prefix_merkle_target_error budgets"
      unfolding prefix_with_state_eq hash_target_budget_value_def
        ro_checked_staged_zero_round_prefix_merkle_target_error_def
      apply (simp only: fst_conv snd_conv)
      apply (rule nnreal_nat_divide_right_mono)
      apply (rule numerator_bound)
      done
  qed
qed


definition ro_checked_staged_zero_after_first_root_security_program
where
  "ro_checked_staged_zero_after_first_root_security_program
      A prefix_with_state =
    do {
      (prefix_with_state, data, query_start, raws, query_states) \<leftarrow>
        ro_checked_staged_after_first_root_with_query_witnesses_program
          A prefix_with_state;
      attacker_state \<leftarrow> get;
      put
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data));
      result \<leftarrow> ro_verify_monad;
      return
        (((prefix_with_state, data, query_start, raws, query_states),
            attacker_state), result)
    }"

definition
  ro_checked_staged_zero_after_first_root_security_hash_query_budget_for
where
  "ro_checked_staged_zero_after_first_root_security_hash_query_budget_for
      budgets =
    ro_checked_staged_zero_after_first_root_with_query_hash_query_budget_for
        budgets +
      ro_verifier_hash_query_budget"

lemma
  ro_absorb_checked_staged_security_experiment_with_first_root_zero_prefix_decomposition:
  "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      A =
    ro_staged_first_trace_fri_root_prefix_program A \<bind>
      ro_checked_staged_zero_after_first_root_security_program A"
  unfolding
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
    ro_checked_staged_zero_after_first_root_security_program_def
    ro_checked_staged_transcript_program_with_first_root_prefix_decomposition
    ro_checked_staged_after_first_root_with_query_witnesses_program_def
  by (simp add: sm_bind_assoc split_def)

lemma
  hash_target_program_ro_checked_staged_zero_after_first_root_security:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (ro_checked_staged_zero_after_first_root_security_hash_query_budget_for
        budgets)
      (ro_checked_staged_zero_after_first_root_security_program
        A prefix_with_state)"
proof -
  let ?head =
    "ro_checked_staged_zero_after_first_root_with_query_hash_query_budget_for
      budgets"
  have head:
    "hash_target_program B ?head
      (ro_checked_staged_after_first_root_with_query_witnesses_program
        A prefix_with_state)"
    by (rule
      hash_target_program_ro_checked_staged_zero_after_first_root_with_query_witnesses[
        OF zero wf controlled])
  have whole:
    "hash_target_program B
      (?head + (ro_verifier_hash_query_budget + 0))
      (ro_checked_staged_zero_after_first_root_security_program
        A prefix_with_state)"
    unfolding ro_checked_staged_zero_after_first_root_security_program_def
  proof (rule hash_target_program_bind_on_outcomes[OF head])
    fix s packed t
    assume
      "Some (packed, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_root_with_query_witnesses_program
              A prefix_with_state)
            s)"
    obtain packed_prefix data query_start raws query_states where packed_eq:
      "packed = (packed_prefix, data, query_start, raws, query_states)"
      by (cases packed) auto
    have continuation:
      "hash_target_program B
        (0 + (ro_verifier_hash_query_budget + 0))
        (ro_checked_verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>attacker_state.
            ro_verify_monad \<bind>
              (\<lambda>result.
                return
                  (((packed_prefix, data, query_start, raws, query_states),
                      attacker_state), result))))"
      by (rule hash_target_program_bind)
        (rule
          hash_target_program_ro_checked_verifier_state_transfer_with_saved,
         rule hash_target_program_bind,
         rule hash_target_program_ro_verify_monad,
         rule hash_target_program_return)
    show
      "hash_target_program B (ro_verifier_hash_query_budget + 0)
        (case packed of
          (prefix_with_state, data, query_start, raws, query_states) \<Rightarrow>
            get \<bind>
            (\<lambda>attacker_state.
              put
                (verifier_state_from_adversary attacker_state
                  (staged_proof_transcript data)) \<bind>
              (\<lambda>_. ro_verify_monad \<bind>
                (\<lambda>result.
                  return
                    (((prefix_with_state, data, query_start, raws,
                        query_states), attacker_state), result)))))"
      using continuation
      unfolding packed_eq
        ro_checked_verifier_state_transfer_with_saved_def
      by (simp add: sm_bind_assoc)
  qed
  show ?thesis    using whole
    unfolding
      ro_checked_staged_zero_after_first_root_security_hash_query_budget_for_def
    by simp
qed

definition
  ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit
where
  "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        hash_map_new_output_hit
          (ro_zero_round_first_root_prefix_merkle_targets
            prefix prefix_state)
          prefix_state final_state)"

definition
  ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
where
  "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
      budgets =
    nnreal
      (ro_checked_staged_zero_after_first_root_security_hash_query_budget_for
          budgets *
        (1 + 2 *
          ro_zero_round_first_root_prefix_hash_query_budget_for budgets)) /
      nnreal size"

lemma
  wp_ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit_bound:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit
      adversary_initial_state
    \<le> ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
        budgets"
proof -
  let ?M = "ro_staged_first_trace_fri_root_prefix_program A"
  let ?K =
    "ro_checked_staged_zero_after_first_root_security_program A"
  let ?E =
    "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit"
  let ?n =
    "ro_checked_staged_zero_after_first_root_security_hash_query_budget_for
      budgets"
  have decomposition:
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A = ?M \<bind> ?K"
    by (rule
      ro_absorb_checked_staged_security_experiment_with_first_root_zero_prefix_decomposition)
  show ?thesis
    unfolding decomposition
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_by_target_budget[
        where
          B="\<lambda>prefix_with_state t.
            ro_zero_round_first_root_prefix_merkle_targets
              (fst prefix_with_state) (snd prefix_with_state)" and
          n="?n" and
          C="ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
            budgets"])
    show "\<not> ?E None"
      unfolding
        ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit_def
      by simp
  next
    fix prefix_with_state t out
    assume head:
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
      and out_support: "out \<in> set_dist (execute (?K prefix_with_state) t)"
      and event: "?E out"
    obtain prefix prefix_state where prefix_with_state_eq:
      "prefix_with_state = (prefix, prefix_state)"
      by (cases prefix_with_state) simp
    have state_eq: "t = prefix_state"
      using head
      unfolding prefix_with_state_eq
        ro_staged_first_trace_fri_root_prefix_program_def zero
      by (auto elim!: set_dist_bindE)
    show
      "hash_new_output_hit_event
        (ro_zero_round_first_root_prefix_merkle_targets
          (fst prefix_with_state) (snd prefix_with_state))
        t out"
      using event out_support state_eq
      unfolding prefix_with_state_eq
        ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit_def
        hash_new_output_hit_event_def
        ro_checked_staged_zero_after_first_root_security_program_def
        ro_checked_staged_after_first_root_with_query_witnesses_program_def
      by (cases out)
        (auto elim!: set_dist_bindE split: prod.splits)
  next
    fix prefix_with_state t
    assume
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
    show
      "hash_target_budget
        (ro_zero_round_first_root_prefix_merkle_targets
          (fst prefix_with_state) (snd prefix_with_state))
        ?n (?K prefix_with_state)"
      by (rule hash_target_program_budget)
        (rule
          hash_target_program_ro_checked_staged_zero_after_first_root_security[
            OF zero wf controlled])
  next
    fix prefix_with_state t
    assume head:
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
    obtain prefix prefix_state where prefix_with_state_eq:
      "prefix_with_state = (prefix, prefix_state)"
      by (cases prefix_with_state) simp
    have card_bound:
      "card
          (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
        \<le> 1 + 2 *
          ro_zero_round_first_root_prefix_hash_query_budget_for budgets"
      by (rule
        ro_staged_first_trace_fri_root_prefix_zero_target_card_bound[
          OF zero controlled])
        (use head prefix_with_state_eq in simp)
    have numerator_bound:
      "?n * card
          (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
        \<le> ?n *
          (1 + 2 *
            ro_zero_round_first_root_prefix_hash_query_budget_for budgets)"
      by (rule mult_left_mono[OF card_bound]) simp
    show
      "hash_target_budget_value
          (ro_zero_round_first_root_prefix_merkle_targets
            (fst prefix_with_state) (snd prefix_with_state))
          ?n
        \<le> ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
            budgets"
      unfolding prefix_with_state_eq hash_target_budget_value_def
        ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error_def
      apply (simp only: fst_conv snd_conv)
      apply (rule nnreal_nat_divide_right_mono)
      apply (rule numerator_bound)
      done
  qed
qed

end
end
