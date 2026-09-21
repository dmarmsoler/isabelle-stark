theory FS_Prefix_Target_Accounting
 imports "Stark.FS_Prefix_Witness_Replay"
   "Stark.Soundness_FRI_Prefix_Local_Target_Bounds"
begin

section \<open>Replay-aware bounds at the actual saved query prefix\<close>

text \<open>Condition on a supported head retaining the producer source as ghost data.
  Targets are fixed at the actual saved query-start state, not before the
  adaptive producer runs. Fixed-source continuations retain all internal query
  and verifier hashes. Clean later states imply the prefix domain bound.
  Neither event nor the original staged callback allowances are changed.\<close>

context soundness
begin

definition fs_composition_prefix_error where
 "fs_composition_prefix_error Q =
   nnreal((fs_prefix_tail_budget+ro_verifier_hash_query_budget)*
     (1+2*fs_prefix_head_budget Q))/nnreal size"

definition fs_query_phase_error where
 "fs_query_phase_error Q =
   nnreal(fs_prefix_tail_budget*(ceil_log clength+ceil_log(maxDegree+1)+
     2*fs_prefix_head_budget Q))/nnreal size"

lemma fs_compiled_composition_prefix_bound:
  assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          (fs_compile_replay A P))
      ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
      adversary_initial_state
    \<le> fs_composition_prefix_error Q"
proof -
  let ?M = "fs_source_query_head A P"
  let ?K =
    "\<lambda>(source, (prefix, prefix_state), data, query_start).
      ro_checked_staged_query_program_with_witnesses (fs_fixed_transcript_staged_adversary A source)
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
    "\<lambda>(source, (prefix, prefix_state), data, query_start) t.
      ro_actual_query_composition_prefix_targets
        (ro_query_head_data data) query_start"
  let ?tail =
    "fs_prefix_tail_budget + ro_verifier_hash_query_budget"
  let ?q =
    "fs_prefix_head_budget Q"
  have decomposition:
      "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          (fs_compile_replay A P) = ?M \<bind> ?K"
    apply (subst fs_prefix_security_witness_elimination[OF fixed])
    unfolding fs_source_query_head_def
      ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
      ro_checked_verifier_state_transfer_with_saved_def
    by (simp add: sm_bind_assoc split_def)
  show ?thesis
    unfolding decomposition
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_conditional[
        where B="?B" and n="?tail" and
          C="fs_composition_prefix_error Q"])
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
    obtain source prefix prefix_state data query_start where x_eq:
        "x = (source, (prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have projected_head: "Some (((prefix,prefix_state),data,query_start),t) \<in>
      set_dist(execute(ro_checked_staged_first_root_query_head_program
        (fs_compile_replay A P))adversary_initial_state)"
      using fs_source_query_head_projection[OF fixed head[unfolded x_eq]] by simp
    have state_eq: "t = query_start"
      by (rule ro_checked_staged_first_root_query_head_program_state[OF projected_head])
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
    obtain source prefix prefix_state data query_start where x_eq:
        "x = (source, (prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have projected_head: "Some (((prefix,prefix_state),data,query_start),t) \<in>
      set_dist(execute(ro_checked_staged_first_root_query_head_program
        (fs_compile_replay A P))adversary_initial_state)"
      using fs_source_query_head_projection[OF fixed head[unfolded x_eq]] by simp
    have lengths:
        "length (staged_trace_fri_roots data) = ceil_log clength \<and>
          length (staged_composition_fri_roots data) \<le>
            ceil_log (maxDegree + 1)"
      using
        ro_checked_staged_first_root_query_head_program_output_lengths[
          OF nonempty projected_head]
      by blast
    have program:
        "hash_target_program
          (ro_actual_query_composition_prefix_targets
            (ro_query_head_data data) query_start)
          ?tail (?K x)"
      unfolding x_eq
      apply (simp only: prod.case)
      apply (rule
        fs_prefix_fixed_query_verifier_target[
          OF conjunct1[OF lengths] conjunct2[OF lengths]])
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
    obtain source prefix prefix_state data query_start where x_eq:
        "x = (source, (prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have projected_head: "Some (((prefix,prefix_state),data,query_start),t) \<in>
      set_dist(execute(ro_checked_staged_first_root_query_head_program
        (fs_compile_replay A P))adversary_initial_state)"
      using fs_source_query_head_projection[OF fixed head[unfolded x_eq]] by simp
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
          OF nonempty projected_head]
      by blast
    have tail_program:
        "hash_target_program ({} :: 'f set) ?tail (?K x)"
      unfolding x_eq
      apply (simp only: prod.case)
      apply (rule
        fs_prefix_fixed_query_verifier_target[
          OF conjunct1[OF lengths] conjunct2[OF lengths]])
      done
    have state_eq: "t = query_start"
      by (rule ro_checked_staged_first_root_query_head_program_state[OF projected_head])
    have query_start_final: "query_start \<le> final_state"
      using tail_program tail_support
      unfolding state_eq out_eq hash_target_program_def
        hash_extension_preserving_def
      by blast
    have query_start_domain:
        "card (fmdom' (HashMap query_start)) \<le> ?q"
      by (rule fs_prefix_head_domain[
        OF fixed bound nonempty projected_head query_start_final final_clean])

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
          fs_composition_prefix_error Q"
      unfolding hash_target_budget_value_def
        fs_composition_prefix_error_def
        Let_def
      apply (rule nnreal_nat_divide_right_mono)
      using target_card
      by (rule mult_left_mono) simp
  qed
qed


lemma fs_compiled_query_phase_bound:
  assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
      (fs_compile_replay A P))
      ro_query_head_dependent_fri_builder_merkle_target_hit
      adversary_initial_state
    \<le> fs_query_phase_error Q"
proof -
  have wf: "staged_budget_wellformed(fs_replay_budgets Q)"
    by (rule fs_replay_budgets_wellformed)
  have controlled: "staged_adversary_controlled (fs_replay_budgets Q) (fs_compile_replay A P)"
    by (rule fs_compile_replay_controlled[OF bound fixed])
  let ?M = "fs_source_query_head A P"
  let ?K =
    "\<lambda>(source, prefix_with_state, data, query_start).
      ro_checked_staged_query_program_with_witnesses (fs_fixed_transcript_staged_adversary A source)
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
    "\<lambda>(source, prefix_with_state, data, query_start) t.
      fri_checked_builder_merkle_targets
        (ro_query_head_data data) query_start"
  let ?tail =
    "fs_prefix_tail_budget"
  let ?q = "fs_prefix_head_budget Q"
  have decomposition:
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
      (fs_compile_replay A P) = ?M \<bind> ?K"
    apply (subst fs_prefix_witness_builder_elimination[OF fixed])
    unfolding fs_source_query_head_def
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
    by (simp add: sm_bind_assoc split_def)
  show ?thesis
    unfolding decomposition
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_conditional[
        where B="?B" and n="?tail" and
          C="fs_query_phase_error Q"])
    show "\<not> ?E None"
      unfolding ro_query_head_dependent_fri_builder_merkle_target_hit_def
      by simp
  next
    fix x t out
    assume head:
      "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
      and tail_support: "out \<in> set_dist (execute (?K x) t)"
      and event: "?E out"
    obtain source prefix prefix_state data query_start where x_eq:
      "x = (source, (prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have projected_head: "Some (((prefix,prefix_state),data,query_start),t) \<in>
      set_dist(execute(ro_checked_staged_first_root_query_head_program
        (fs_compile_replay A P))adversary_initial_state)"
      using fs_source_query_head_projection[OF fixed head[unfolded x_eq]] by simp
    have state_eq: "t = query_start"
      by (rule ro_checked_staged_first_root_query_head_program_state[
            OF projected_head])
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
    obtain source prefix prefix_state data query_start where x_eq:
      "x = (source, (prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have projected_head: "Some (((prefix,prefix_state),data,query_start),t) \<in>
      set_dist(execute(ro_checked_staged_first_root_query_head_program
        (fs_compile_replay A P))adversary_initial_state)"
      using fs_source_query_head_projection[OF fixed head[unfolded x_eq]] by simp
    have lengths:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_composition_fri_roots data) \<le>
         ceil_log (maxDegree + 1)"
      using
        ro_checked_staged_first_root_query_head_program_output_lengths_all_rounds[
          OF projected_head]
      by blast
    have query_target:
      "hash_target_program
        (fri_checked_builder_merkle_targets
          (ro_query_head_data data) query_start)
        ?tail
        (ro_checked_staged_query_program_with_witnesses (fs_fixed_transcript_staged_adversary A source)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds)"
      by (rule
        fs_prefix_fixed_query_target[
          OF conjunct1[OF lengths] conjunct2[OF lengths]])
    have program_explicit:
      "hash_target_program
        (fri_checked_builder_merkle_targets
          (ro_query_head_data data) query_start)
        (?tail + 0)
        (ro_checked_staged_query_program_with_witnesses (fs_fixed_transcript_staged_adversary A source)
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
        (ro_checked_staged_query_program_with_witnesses (fs_fixed_transcript_staged_adversary A source)
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
    obtain source prefix prefix_state data query_start where x_eq:
      "x = (source, (prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have projected_head: "Some (((prefix,prefix_state),data,query_start),t) \<in>
      set_dist(execute(ro_checked_staged_first_root_query_head_program
        (fs_compile_replay A P))adversary_initial_state)"
      using fs_source_query_head_projection[OF fixed head[unfolded x_eq]] by simp
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
      (fs_compile_replay A P))
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
      by (rule fs_prefix_head_domain[
        OF fixed bound nonempty projected_head query_start_ext clean])
    have lengths:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_composition_fri_roots data) \<le>
         ceil_log (maxDegree + 1)"
      using
        ro_checked_staged_first_root_query_head_program_output_lengths_all_rounds[
          OF projected_head]
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
        fs_query_phase_error Q"
      unfolding hash_target_budget_value_def
        fs_query_phase_error_def
        Let_def
      apply (rule nnreal_nat_divide_right_mono)
      using target_card
      by (rule mult_left_mono) simp
  qed
qed



lemma fs_query_head_budget_le_replay:
 "fs_prefix_head_budget Q \<le>
   ro_checked_staged_query_head_hash_query_budget_for(fs_replay_budgets Q)"
 unfolding fs_prefix_head_budget_def ro_checked_staged_query_head_hash_query_budget_for_def
   fs_replay_budgets_def
 by (simp add: sum_list_replicate; arith)

lemma fs_query_tail_budget_le_replay:
 "fs_prefix_tail_budget \<le> sum_list(query_opening_budgets(fs_replay_budgets Q))+
   rounds+rounds*ro_checked_query_round_transcript_bound"
 by (simp add: fs_prefix_tail_budget_def)

lemma fs_composition_prefix_error_le_replay:
 "fs_composition_prefix_error Q \<le>
   ro_absorb_checked_staged_local_composition_prefix_target_error(fs_replay_budgets Q)"
 unfolding fs_composition_prefix_error_def
   ro_absorb_checked_staged_local_composition_prefix_target_error_def Let_def
 apply (rule nnreal_nat_divide_right_mono)
 apply (rule mult_le_mono)
 using fs_query_tail_budget_le_replay[of Q] fs_query_head_budget_le_replay[of Q]
 by simp_all

lemma fs_query_phase_error_le_replay:
 "fs_query_phase_error Q \<le>
   ro_checked_staged_local_query_phase_target_error(fs_replay_budgets Q)"
 unfolding fs_query_phase_error_def
   ro_checked_staged_local_query_phase_target_error_def Let_def
 apply (rule nnreal_nat_divide_right_mono)
 apply (rule mult_le_mono[OF fs_query_tail_budget_le_replay])
 using fs_query_head_budget_le_replay[of Q] by simp

end
ML \<open>
  val checked = @{thms soundness.fs_compiled_composition_prefix_bound
    soundness.fs_compiled_query_phase_bound
    soundness.fs_query_head_budget_le_replay soundness.fs_query_tail_budget_le_replay
    soundness.fs_composition_prefix_error_le_replay soundness.fs_query_phase_error_le_replay};
  if forall (null o Thm.hyps_of) checked andalso null (Thm_Deps.all_oracles checked)
  then () else error "Unexpected prefix target proof dependency";
\<close>
end
