theory Soundness_FRI_Conditioned_Explicit_Residual_Query_Phase_Target
  imports
    Stark.Soundness_FRI_Conditioned_Explicit_Residual_Complete_List_Classification
    Stark.Soundness_FRI_Conditioned_Explicit_Residual_Actual_Product_Zero
begin

context soundness
begin

definition ro_query_head_dependent_fri_builder_merkle_target_hit
where
  "ro_query_head_dependent_fri_builder_merkle_target_hit out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        \<not> hash_map_output_collision attacker_state \<and>
        hash_map_new_output_hit
          (fri_checked_builder_merkle_targets
            (ro_query_head_data data) query_start)
          query_start attacker_state)"

definition ro_checked_staged_conditioned_residual_query_phase_target_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_residual_query_phase_target_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets;
         tail = sum_list (query_opening_budgets budgets) + rounds +
           rounds * ro_checked_query_round_transcript_bound
     in nnreal
          (tail *
            (ceil_log clength + ceil_log (maxDegree + 1) + 2 * q)) /
        nnreal size)"

lemma wp_ro_checked_staged_query_phase_builder_merkle_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      ro_query_head_dependent_fri_builder_merkle_target_hit
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_residual_query_phase_target_error budgets"
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
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
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
          C="ro_checked_staged_conditioned_residual_query_phase_target_error
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
    have map_bound:
      "card (fmdom' (HashMap attacker_state)) \<le> ?q"
      by (rule
        ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds[
          OF wf controlled full_support clean])
    have dom_subset:
      "fmdom' (HashMap query_start) \<subseteq>
        fmdom' (HashMap attacker_state)"
    proof
      fix key
      assume key_old: "key \<in> fmdom' (HashMap query_start)"
      then obtain v where lookup_old:
        "fmlookup (HashMap query_start) key = Some v"
        by (auto simp: fmlookup_dom'_iff)
      have extension:
        "fmlookup (HashMap query_start) key = None \<or>
         fmlookup (HashMap query_start) key =
           fmlookup (HashMap attacker_state) key"
        using query_start_ext
        unfolding less_eq_hash_ext_def less_eq_fmap_def
        by blast
      have lookup_new:
        "fmlookup (HashMap attacker_state) key = Some v"
        using extension lookup_old by auto
      show "key \<in> fmdom' (HashMap attacker_state)"
        using lookup_new by (simp add: fmlookup_dom'_iff)
    qed
    have domain_start:
      "card (fmdom' (HashMap query_start)) \<le> ?q"
    proof -
      have
        "card (fmdom' (HashMap query_start)) \<le>
          card (fmdom' (HashMap attacker_state))"
        by (rule card_mono[OF finite_fmdom' dom_subset])
      then show ?thesis using map_bound by simp
    qed
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
        ro_checked_staged_conditioned_residual_query_phase_target_error budgets"
      unfolding hash_target_budget_value_def
        ro_checked_staged_conditioned_residual_query_phase_target_error_def
        Let_def
      apply (rule nnreal_nat_divide_right_mono)
      using target_card
      by (rule mult_left_mono) simp
  qed
qed

end
end
