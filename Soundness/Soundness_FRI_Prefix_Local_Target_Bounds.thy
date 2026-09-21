theory Soundness_FRI_Prefix_Local_Target_Bounds
 imports "Stark.Soundness_FRI_Query_Head_Range"
   "Stark.Soundness_FRI_RO_Actual_Query_Trace_Composition_Target_Bound"
   "Stark.Soundness_FRI_Conditioned_Explicit_Residual_Query_Phase_Target"
begin
section \<open>Prefix-local bounds for the existing clean target events\<close>
text \<open>
  Both target sets are fixed at query start, so only the actual query-head
  range is needed for their cardinality bounds. Their joint clean-and-hit
  events, tail budgets and support guards are unchanged. The probability
  lemmas apply to nonempty trace FRI; the MCA regime supplies that guard
  internally and preserves the previous zero-round fallback.
\<close>

lemma prefix_local_target_budget_credit:
 fixes h t c f :: nat
 shows "nnreal (t*(c+2*(h+t))) / nnreal f =
   nnreal (t*(c+2*h)) / nnreal f + nnreal (2*t^2) / nnreal f"
 by (simp add: add_divide_nnreal[symmetric] power2_eq_square algebra_simps)

context soundness
begin

definition ro_absorb_checked_staged_local_composition_prefix_target_error
  :: "staged_budgets \<Rightarrow> prob"
where
 "ro_absorb_checked_staged_local_composition_prefix_target_error budgets =
   (let h = ro_checked_staged_query_head_hash_query_budget_for budgets;
        tail = sum_list (query_opening_budgets budgets) + rounds +
          rounds * ro_checked_query_round_transcript_bound + ro_verifier_hash_query_budget
    in nnreal (tail * (1 + 2*h)) / nnreal size)"

definition ro_checked_staged_local_query_phase_target_error
  :: "staged_budgets \<Rightarrow> prob"
where
 "ro_checked_staged_local_query_phase_target_error budgets =
   (let h = ro_checked_staged_query_head_hash_query_budget_for budgets;
        tail = sum_list (query_opening_budgets budgets) + rounds +
          rounds * ro_checked_query_round_transcript_bound
    in nnreal (tail * (ceil_log clength + ceil_log (maxDegree+1) + 2*h)) / nnreal size)"

lemma
  wp_ro_absorb_checked_staged_clean_composition_prefix_target_hit_local_bound:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
      adversary_initial_state
    \<le> ro_absorb_checked_staged_local_composition_prefix_target_error budgets"
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
    "ro_checked_staged_query_head_hash_query_budget_for budgets"
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
          C="ro_absorb_checked_staged_local_composition_prefix_target_error
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

    have final_clean: "\<not> hash_map_output_collision final_state"
      using event
      unfolding out_eq
        ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
        final_hash_collision_event_def
      by simp
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
    have query_start_domain:
        "card (fmdom' (HashMap query_start)) \<le> ?q"
      by (rule ro_checked_staged_clean_query_start_domain_budget[
        OF nonempty wf controlled head[unfolded x_eq] query_start_final final_clean])

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
          ro_absorb_checked_staged_local_composition_prefix_target_error
            budgets"
      unfolding hash_target_budget_value_def
        ro_absorb_checked_staged_local_composition_prefix_target_error_def
        Let_def
      apply (rule nnreal_nat_divide_right_mono)
      using target_card
      by (rule mult_left_mono) simp
  qed
qed


text \<open>
  The following credit is an exact difference between error expressions, not
  a probability lower bound or an execution-realization claim. It is purely
  arithmetic and does not need the guards of the event probability lemmas.
\<close>

definition ro_prefix_local_target_saving :: "staged_budgets \<Rightarrow> prob"
where
 "ro_prefix_local_target_saving budgets =
   (let tail = sum_list (query_opening_budgets budgets) + rounds +
          rounds * ro_checked_query_round_transcript_bound
    in nnreal (2*(tail+ro_verifier_hash_query_budget)^2) / nnreal size +
       nnreal (2*tail^2) / nnreal size)"

lemma ro_composition_prefix_target_error_local_credit:
 "ro_absorb_checked_staged_trace_composition_prefix_target_error budgets =
   ro_absorb_checked_staged_local_composition_prefix_target_error budgets +
   nnreal (2*(sum_list (query_opening_budgets budgets) + rounds +
       rounds * ro_checked_query_round_transcript_bound +
       ro_verifier_hash_query_budget)^2) / nnreal size"
 unfolding ro_absorb_checked_staged_trace_composition_prefix_target_error_def
   ro_absorb_checked_staged_local_composition_prefix_target_error_def
   ro_absorb_checked_staged_security_hash_query_budget_for_def
   ro_checked_staged_query_head_plus_tail_budget[symmetric] Let_def
 by (auto simp: add_divide_nnreal[symmetric] power2_eq_square algebra_simps)


lemma wp_ro_checked_staged_query_phase_builder_merkle_target_hit_local_bound:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      ro_query_head_dependent_fri_builder_merkle_target_hit
      adversary_initial_state
    \<le> ro_checked_staged_local_query_phase_target_error budgets"
proof -
  let ?M = "ro_checked_staged_first_root_query_head_program A"
  let ?K =
    "\<lambda>(prefix_with_state, data, query_start).
      ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          return
            (prefix_with_state,
              data\<lparr>staged_query_chunks := query_chunks\<rparr>,
              query_start, raws, query_states))"
  let ?E = "ro_query_head_dependent_fri_builder_merkle_target_hit"
  let ?B =
    "\<lambda>(prefix_with_state, data, query_start) t.
      fri_checked_builder_merkle_targets
        (ro_query_head_data data) query_start"
  let ?tail =
    "sum_list (query_opening_budgets budgets) + rounds +
      rounds * ro_checked_query_round_transcript_bound"
  let ?q = "ro_checked_staged_query_head_hash_query_budget_for budgets"
  have decomposition:
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
      A = ?M \<bind> ?K"
    unfolding
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
    by (simp add: sm_bind_assoc split_def)
  show ?thesis
    unfolding decomposition
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_conditional[
        where B="?B" and n="?tail" and
          C="ro_checked_staged_local_query_phase_target_error
            budgets"])
    show "\<not> ?E None"
      unfolding ro_query_head_dependent_fri_builder_merkle_target_hit_def
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
      by (rule ro_checked_staged_first_root_query_head_program_state[
            OF head[unfolded x_eq]])
    show "hash_new_output_hit_event (?B x t) t out"
      using event tail_support
      unfolding x_eq state_eq
        ro_query_head_dependent_fri_builder_merkle_target_hit_def
        hash_new_output_hit_event_def ro_query_head_data_def
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
        ro_checked_staged_first_root_query_head_program_output_lengths_all_rounds[
          OF head[unfolded x_eq]]
      by blast
    have query_target:
      "hash_target_program
        (fri_checked_builder_merkle_targets
          (ro_query_head_data data) query_start)
        ?tail
        (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds)"
      by (rule
        hash_target_program_ro_checked_staged_query_program_with_witnesses_closed[
          OF wf controlled conjunct1[OF lengths] conjunct2[OF lengths]])
    have program_explicit:
      "hash_target_program
        (fri_checked_builder_merkle_targets
          (ro_query_head_data data) query_start)
        (?tail + 0)
        (ro_checked_staged_query_program_with_witnesses A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)
            query_start 0 rounds \<bind>
          (\<lambda>(raws, query_states, query_chunks).
            return
              ((prefix, prefix_state),
                data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                query_start, raws, query_states)))"
      apply (rule hash_target_program_bind[OF query_target])
      by (auto simp: hash_target_program_return split: prod.splits)
    have budget_explicit:
      "hash_target_budget
        (fri_checked_builder_merkle_targets
          (ro_query_head_data data) query_start)
        ?tail
        (ro_checked_staged_query_program_with_witnesses A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)
            query_start 0 rounds \<bind>
          (\<lambda>(raws, query_states, query_chunks).
            return
              ((prefix, prefix_state),
                data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                query_start, raws, query_states)))"
      by (rule hash_target_program_budget)
        (use program_explicit in simp)
    show "hash_target_budget (?B x t) ?tail (?K x)"
      using budget_explicit
      unfolding x_eq
      by simp
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
    obtain raws query_states query_chunks attacker_state where out_eq:
      "out =
        Some ((((prefix, prefix_state),
          data\<lparr>staged_query_chunks := query_chunks\<rparr>,
          query_start, raws, query_states), attacker_state))"
      using tail_support event
      unfolding x_eq
        ro_query_head_dependent_fri_builder_merkle_target_hit_def
      by (cases out)
        (auto elim!: set_dist_bindE split: prod.splits)
    have bind_support:
      "out \<in> set_dist (execute (?M \<bind> ?K) adversary_initial_state)"
      apply (rule set_dist_bindI)
       apply (rule head)
      apply (rule tail_support)
      done
    have full_support:
      "Some ((((prefix, prefix_state),
          data\<lparr>staged_query_chunks := query_chunks\<rparr>,
          query_start, raws, query_states), attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
      using bind_support unfolding decomposition out_eq .
    have clean: "\<not> hash_map_output_collision attacker_state"
      using event unfolding out_eq
        ro_query_head_dependent_fri_builder_merkle_target_hit_def
      by simp
    have query_start_ext: "query_start \<le> attacker_state"
      using
        ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
          OF wf controlled full_support]
      by blast
    have domain_start:
      "card (fmdom' (HashMap query_start)) \<le> ?q"
      by (rule ro_checked_staged_clean_query_start_domain_budget[
        OF nonempty wf controlled head[unfolded x_eq] query_start_ext clean])
    have lengths:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_composition_fri_roots data) \<le>
         ceil_log (maxDegree + 1)"
      using
        ro_checked_staged_first_root_query_head_program_output_lengths_all_rounds[
          OF head[unfolded x_eq]]
      by blast
    have target_card:
      "card (?B x t) \<le>
        ceil_log clength + ceil_log (maxDegree + 1) + 2 * ?q"
      unfolding x_eq
      apply (simp only: prod.case)
      apply (rule fri_checked_builder_merkle_targets_card_bound_from_head[
        where data="ro_query_head_data data" and s=query_start and q="?q"])
        using lengths apply (simp add: ro_query_head_data_def)
       using lengths apply (simp add: ro_query_head_data_def)
      using domain_start apply simp
      done
    show
      "hash_target_budget_value (?B x t) ?tail \<le>
        ro_checked_staged_local_query_phase_target_error budgets"
      unfolding hash_target_budget_value_def
        ro_checked_staged_local_query_phase_target_error_def
        Let_def
      apply (rule nnreal_nat_divide_right_mono)
      using target_card
      by (rule mult_left_mono) simp
  qed
qed

lemma ro_query_phase_target_error_local_credit:
 "ro_checked_staged_conditioned_residual_query_phase_target_error budgets =
   ro_checked_staged_local_query_phase_target_error budgets +
   nnreal (2*(sum_list (query_opening_budgets budgets) + rounds +
       rounds * ro_checked_query_round_transcript_bound)^2) / nnreal size"
 unfolding ro_checked_staged_conditioned_residual_query_phase_target_error_def
   ro_checked_staged_local_query_phase_target_error_def
   ro_checked_staged_query_head_plus_tail_budget[symmetric] Let_def
 by (rule prefix_local_target_budget_credit)

lemma ro_local_target_errors_add_saving:
 "ro_absorb_checked_staged_local_composition_prefix_target_error budgets +
   ro_checked_staged_local_query_phase_target_error budgets +
   ro_prefix_local_target_saving budgets =
   ro_absorb_checked_staged_trace_composition_prefix_target_error budgets +
   ro_checked_staged_conditioned_residual_query_phase_target_error budgets"
 by (simp add: ro_composition_prefix_target_error_local_credit
   ro_query_phase_target_error_local_credit ro_prefix_local_target_saving_def
   Let_def algebra_simps)

lemma ro_local_composition_prefix_target_error_le:
 "ro_absorb_checked_staged_local_composition_prefix_target_error budgets \<le>
   ro_absorb_checked_staged_trace_composition_prefix_target_error budgets"
 by (simp add: ro_composition_prefix_target_error_local_credit)

lemma ro_local_query_phase_target_error_le:
 "ro_checked_staged_local_query_phase_target_error budgets \<le>
   ro_checked_staged_conditioned_residual_query_phase_target_error budgets"
 by (simp add: ro_query_phase_target_error_local_credit)

end

end
