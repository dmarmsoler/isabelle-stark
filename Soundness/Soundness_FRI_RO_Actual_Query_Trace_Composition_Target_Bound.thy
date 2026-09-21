(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Trace_Composition_Target_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Target_Bound
  imports
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Obstruction_Classification
begin

context soundness
begin

definition
  ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
where
  "ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
      out \<longleftrightarrow>
    \<not> final_hash_collision_event out \<and>
    ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
      out"

definition
  ro_absorb_checked_staged_trace_composition_prefix_target_error
    :: "staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_trace_composition_prefix_target_error budgets =
    (let q = ro_absorb_checked_staged_security_hash_query_budget_for budgets;
         tail =
           sum_list (query_opening_budgets budgets) + rounds +
             rounds * ro_checked_query_round_transcript_bound +
             ro_verifier_hash_query_budget
     in nnreal (tail * (1 + 2 * q)) / nnreal size)"

lemma
  hash_target_program_ro_absorb_checked_staged_query_and_verifier_tail:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    and composition_len:
      "length (staged_composition_fri_roots data) \<le>
        ceil_log (maxDegree + 1)"
  shows
    "hash_target_program B
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound +
        ro_verifier_hash_query_budget)
      (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          ro_checked_verifier_state_transfer_with_saved
              (staged_proof_transcript
                (data\<lparr>staged_query_chunks := query_chunks\<rparr>)) \<bind>
            (\<lambda>attacker_state.
              ro_verify_monad \<bind>
                (\<lambda>result.
                  return
                    (((prefix_with_state,
                        data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                        query_start, raws, query_states),
                      attacker_state), result)))))"
proof -
  let ?query =
    "sum_list (query_opening_budgets budgets) + rounds +
      rounds * ro_checked_query_round_transcript_bound"
  have query:
      "hash_target_program B ?query
        (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds)"
    by (rule
      hash_target_program_ro_checked_staged_query_program_with_witnesses_closed[
        OF wf controlled trace_len composition_len])
  have continuation:
      "\<And>raws query_states query_chunks.
        hash_target_program B
          (0 + (ro_verifier_hash_query_budget + 0))
          (ro_checked_verifier_state_transfer_with_saved
              (staged_proof_transcript
                (data\<lparr>staged_query_chunks := query_chunks\<rparr>)) \<bind>
            (\<lambda>attacker_state.
              ro_verify_monad \<bind>
                (\<lambda>result.
                  return
                    (((prefix_with_state,
                        data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                        query_start, raws, query_states),
                      attacker_state), result))))"
    by (rule hash_target_program_bind,
        rule hash_target_program_ro_checked_verifier_state_transfer_with_saved,
        rule hash_target_program_bind,
        rule hash_target_program_ro_verify_monad,
        rule hash_target_program_return)
  show ?thesis
    apply (rule hash_target_program_bind[OF query])
    apply (auto split: prod.splits)
    apply (rule continuation[simplified])
    done
qed


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_bound:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
      adversary_initial_state
    \<le> ro_absorb_checked_staged_trace_composition_prefix_target_error budgets"
proof -
  let ?M = "ro_checked_staged_first_root_query_head_program A"
  let ?K =
    "\<lambda>((prefix, prefix_state), data, query_start).
      ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          ro_checked_verifier_state_transfer_with_saved
              (staged_proof_transcript
                (data\<lparr>staged_query_chunks := query_chunks\<rparr>)) \<bind>
            (\<lambda>attacker_state.
              ro_verify_monad \<bind>
                (\<lambda>result.
                  return
                    (((((prefix, prefix_state),
                        data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                        query_start, raws, query_states),
                      attacker_state), result)))))"
  let ?E =
    "ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit"
  let ?B =
    "\<lambda>((prefix, prefix_state), data, query_start) t.
      ro_actual_query_composition_prefix_targets
        (ro_query_head_data data) query_start"
  let ?tail =
    "sum_list (query_opening_budgets budgets) + rounds +
      rounds * ro_checked_query_round_transcript_bound +
      ro_verifier_hash_query_budget"
  let ?q =
    "ro_absorb_checked_staged_security_hash_query_budget_for budgets"
  have decomposition:
      "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A = ?M \<bind> ?K"
    unfolding
      ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
      ro_checked_verifier_state_transfer_with_saved_def
    by (simp add: sm_bind_assoc split_def)
  show ?thesis
    unfolding decomposition
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_conditional[
        where B="?B" and n="?tail" and
          C="ro_absorb_checked_staged_trace_composition_prefix_target_error
            budgets"])
    show "\<not> ?E None"
      unfolding
        ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
        ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
        final_hash_collision_event_def
      by simp
  next
    fix x t out
    assume head:
        "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
      and tail_support: "out \<in> set_dist (execute (?K x) t)"
      and event: "?E out"
    obtain prefix prefix_state data query_start where x_eq:
        "x = ((prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have state_eq: "t = query_start"
      using head
      unfolding x_eq ro_checked_staged_first_root_query_head_program_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    show "hash_new_output_hit_event (?B x t) t out"
      using event tail_support
      unfolding x_eq state_eq
        ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
        ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
        hash_new_output_hit_event_def
        ro_query_head_data_def
        ro_actual_query_composition_prefix_targets_def
      by (cases out)
        (auto elim!: set_dist_bindE split: prod.splits)
  next
    fix x t
    assume head:
      "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
    obtain prefix prefix_state data query_start where x_eq:
        "x = ((prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have lengths:
        "length (staged_trace_fri_roots data) = ceil_log clength \<and>
          length (staged_composition_fri_roots data) \<le>
            ceil_log (maxDegree + 1)"
      using
        ro_checked_staged_first_root_query_head_program_output_lengths[
          OF nonempty head[unfolded x_eq]]
      by blast
    have program:
        "hash_target_program
          (ro_actual_query_composition_prefix_targets
            (ro_query_head_data data) query_start)
          ?tail (?K x)"
      unfolding x_eq
      apply (simp only: prod.case)
      apply (rule
        hash_target_program_ro_absorb_checked_staged_query_and_verifier_tail[
          OF wf controlled conjunct1[OF lengths] conjunct2[OF lengths]])
      done
    show "hash_target_budget (?B x t) ?tail (?K x)"
      unfolding x_eq
      apply (simp only: prod.case)
      apply (rule hash_target_program_budget)
      using program unfolding x_eq
      by (simp only: prod.case)
  next
    fix x t
    assume head:
        "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
      and witness:
        "\<exists>out \<in> set_dist (execute (?K x) t). ?E out"
    obtain prefix prefix_state data query_start where x_eq:
        "x = ((prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    from witness obtain out where
        tail_support: "out \<in> set_dist (execute (?K x) t)"
      and event: "?E out"
      by blast
    obtain raws query_states query_chunks attacker_state result final_state
        where out_eq:
          "out =
            Some
              (((((prefix, prefix_state),
                  data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                  query_start, raws, query_states),
                attacker_state), result), final_state)"
      using tail_support event
      unfolding x_eq
        ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
        ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
      by (cases out)
        (auto elim!: set_dist_bindE split: prod.splits)

    have bind_support:
        "out \<in> set_dist (execute (?M \<bind> ?K) adversary_initial_state)"
      apply (rule set_dist_bindI)
      apply (rule head)
      apply (rule tail_support)
      done
    have full_support:
        "out \<in>
          set_dist
            (execute
              (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
                A)
              adversary_initial_state)"
      using bind_support unfolding decomposition .

    have full_support':
        "Some
          (((((prefix, prefix_state),
              data\<lparr>staged_query_chunks := query_chunks\<rparr>,
              query_start, raws, query_states),
            attacker_state), result), final_state) \<in>
          set_dist
            (execute
              (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
                A)
              adversary_initial_state)"
      using full_support unfolding out_eq .

    have first_projected:
        "Some
          ((((data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                query_start, raws, query_states),
              attacker_state), result), final_state) \<in>
          set_dist
            (execute
              (ro_absorb_checked_staged_security_experiment_with_query_witnesses
                A)
              adversary_initial_state)"
    proof -
      have mapped:
          "Some
            ((((data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                  query_start, raws, query_states),
                attacker_state), result), final_state) \<in>
            set_dist
              (execute
                (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
                    A \<bind>
                  (\<lambda>(((prefix_with_state, data, query_start, raws, query_states),
                        attacker_state), result).
                    return
                      (((data, query_start, raws, query_states),
                          attacker_state), result)))
                adversary_initial_state)"
        apply (rule set_dist_bindI)
        apply (rule full_support')
        apply simp
        done
      show ?thesis
        using mapped
        unfolding
          ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection[
            OF nonempty, of A]
        .
    qed

    have witness_projected:
        "Some
          (((data\<lparr>staged_query_chunks := query_chunks\<rparr>,
              attacker_state), result), final_state) \<in>
          set_dist
            (execute
              (ro_absorb_checked_staged_security_experiment_with_data_state A)
              adversary_initial_state)"
    proof -
      have mapped:
          "Some
            (((data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                attacker_state), result), final_state) \<in>
            set_dist
              (execute
                (ro_absorb_checked_staged_security_experiment_with_query_witnesses
                    A \<bind>
                  (\<lambda>(((data, query_start, raws, query_states),
                        attacker_state), result).
                    return ((data, attacker_state), result)))
                adversary_initial_state)"
        by (rule set_dist_bindI[OF first_projected]) simp
      show ?thesis
        using mapped
        unfolding
          ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection
        .
    qed

    have base_support:
        "Some (result, final_state) \<in>
          set_dist
            (execute
              (ro_absorb_checked_staged_security_experiment A)
              adversary_initial_state)"
    proof -
      have mapped:
          "Some (result, final_state) \<in>
            set_dist
              (execute
                (ro_absorb_checked_staged_security_experiment_with_data_state A \<bind>
                  (\<lambda>x. return (snd x)))
                adversary_initial_state)"
        by (rule set_dist_bindI[OF witness_projected]) simp
      show ?thesis
        using mapped
        unfolding
          ro_absorb_checked_staged_security_experiment_with_data_state_projection
        .
    qed

    have final_clean: "\<not> hash_map_output_collision final_state"
      using event
      unfolding out_eq
        ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
        final_hash_collision_event_def
      by simp
    have output_bound:
        "card (hash_map_output_values final_state) \<le> ?q"
    proof -
      have raw:
          "card (hash_map_output_values final_state) \<le>
            card (hash_map_output_values adversary_initial_state) + ?q"
        using
          hash_range_budget_ro_absorb_checked_staged_security_experiment[
            OF wf controlled]
          base_support
        unfolding hash_range_budget_def
        by blast
      have initial_empty:
          "hash_map_output_values adversary_initial_state = {}"
        unfolding adversary_initial_state_def hash_map_output_values_def
        by simp
      show ?thesis using raw initial_empty by simp
    qed
    have final_domain:
        "card (fmdom' (HashMap final_state)) \<le> ?q"
      by (rule order_trans[
            OF card_fmdom_le_hash_map_output_values_if_no_collision[
              OF final_clean] output_bound])

    have lengths:
        "length (staged_trace_fri_roots data) = ceil_log clength \<and>
          length (staged_composition_fri_roots data) \<le>
            ceil_log (maxDegree + 1)"
      using
        ro_checked_staged_first_root_query_head_program_output_lengths[
          OF nonempty head[unfolded x_eq]]
      by blast
    have tail_program:
        "hash_target_program ({} :: 'f set) ?tail (?K x)"
      unfolding x_eq
      apply (simp only: prod.case)
      apply (rule
        hash_target_program_ro_absorb_checked_staged_query_and_verifier_tail[
          OF wf controlled conjunct1[OF lengths] conjunct2[OF lengths]])
      done
    have state_eq: "t = query_start"
      using head
      unfolding x_eq ro_checked_staged_first_root_query_head_program_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    have query_start_final: "query_start \<le> final_state"
      using tail_program tail_support
      unfolding state_eq out_eq hash_target_program_def
        hash_extension_preserving_def
      by blast
    have dom_subset:
        "fmdom' (HashMap query_start) \<subseteq>
          fmdom' (HashMap final_state)"
    proof
      fix key
      assume old: "key \<in> fmdom' (HashMap query_start)"
      then obtain v where lookup:
          "fmlookup (HashMap query_start) key = Some v"
        by (auto simp: fmlookup_dom'_iff)
      have extension:
          "fmlookup (HashMap query_start) key = None \<or>
           fmlookup (HashMap query_start) key =
             fmlookup (HashMap final_state) key"
        using query_start_final
        unfolding less_eq_hash_ext_def less_eq_fmap_def
        by blast
      have lookup_new:
          "fmlookup (HashMap final_state) key = Some v"
        using lookup extension by auto
      show "key \<in> fmdom' (HashMap final_state)"
        using lookup_new by (simp add: fmlookup_dom'_iff)
    qed
    have query_start_domain:
        "card (fmdom' (HashMap query_start)) \<le> ?q"
      by (rule order_trans[
            OF card_mono[OF finite_fmdom' dom_subset] final_domain])

    have target_card:
        "card (?B x t) \<le> 1 + 2 * ?q"
    proof -
      have
          "card
            (ro_actual_query_composition_prefix_targets
              (ro_query_head_data data) query_start)
          \<le> 1 + 2 * card (fmdom' (HashMap query_start))"
        by (rule ro_actual_query_composition_prefix_targets_card_bound)
      also have "... \<le> 1 + 2 * ?q"
        using query_start_domain by simp
      finally show ?thesis
        unfolding x_eq
        by simp
    qed
    show
        "hash_target_budget_value (?B x t) ?tail \<le>
          ro_absorb_checked_staged_trace_composition_prefix_target_error
            budgets"
      unfolding hash_target_budget_value_def
        ro_absorb_checked_staged_trace_composition_prefix_target_error_def
        Let_def
      apply (rule nnreal_nat_divide_right_mono)
      using target_card
      by (rule mult_left_mono) simp
  qed
qed



lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_le_clean_trace_composition_obstruction_union:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le>
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        (\<lambda>out.
          final_hash_collision_event out \<or>
          ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
            ro_actual_query_trace_composition_good_query_lists out \<or>
          ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
            out)
        adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and accepted_out: "accepted out"
  show
      "final_hash_collision_event out \<or>
       ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
         ro_actual_query_trace_composition_good_query_lists out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
         out"
  proof (cases "final_hash_collision_event out")
    case True
    then show ?thesis by simp
  next
    case False
    have classified:
        "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
            ro_actual_query_trace_composition_good_query_lists out \<or>
         ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
           out \<or>
         ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
           out \<or>
         ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
           out \<or>
         ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
           out \<or>
         ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
           out"
      by (rule
        ro_absorb_checked_staged_security_with_first_root_clean_trace_composition_classification[
          OF wf controlled nonempty accepted_out support False])
    show ?thesis
      using classified False
      unfolding
        ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
      by blast
  qed
qed
end
end
