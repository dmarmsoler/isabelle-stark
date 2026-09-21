
theory FS_Challenge_Accounting
 imports FS_Builder_Witness_Accounting Soundness_RO_Drift_Per_Key
   Soundness_FRI_Correlated_Agreement_Adaptive_Charging
   Soundness_FRI_Robust_Decoded_Alpha_Pivot
begin

section \<open>Per-key, replay-aware MCA and alpha relation charges\<close>

text \<open>All old drift activations are retained. Supported clean builder
  outcomes permit recapping the unchanged relations at the single-run builder
  budget. The two MCA bounds are joint clean-and-bad probabilities, not
  conditional probabilities. The alpha relation alone is not the complete
  decoded-alpha event.\<close>

context soundness
begin

lemma fs_per_key_bounded_transition:
 assumes fresh: "fmlookup M x=None"
   and direct: "card {y. hash_state_relation_direct_activation R M x y}\<le>b"
   and subset: "{y. hash_state_relation_drift_activation R M x y}\<subseteq>T"
   and finite: "finite T" and cap: "card T\<le>2*card(fmdom' M)+2"
 shows "card {y. hash_state_relation_transition (conditioned_fri_relation_bounded L R)
   M (fmupd x y M)} \<le> b+(2*L+2)"
proof (rule conditioned_fri_bounded_transition_fiber_card_bound[OF fresh])
 show "card(fmdom' M)\<le>L \<Longrightarrow> card {y. hash_state_relation_direct_activation R M x y}\<le>b"
   by (rule direct)
 assume domain: "card(fmdom' M)\<le>L"
 have "card {y. hash_state_relation_drift_activation R M x y}\<le>card T"
   by (rule card_mono[OF finite subset])
 then show "card {y. hash_state_relation_drift_activation R M x y}\<le>2*L+2"
   using cap domain by linarith
qed

lemma fs_trace_per_key_transition:
 assumes fresh: "fmlookup M x=None" and ep: "clength*scale=2^N"
   and fit: "Suc(ceil_log clength)\<le>N"
   and rate: "4*fri_padded_degree_bound(clength-1)\<le>clength*scale"
 shows "card {y. hash_state_relation_transition
   (conditioned_fri_relation_bounded L mca_conditioned_trace_fri_bad_challenge_relation)
   M (fmupd x y M)} \<le> fri_mca_direct_cap+(2*L+2)"
 by (rule fs_per_key_bounded_transition[OF fresh
   mca_conditioned_trace_fri_bad_challenge_relation_direct_fiber_card_bound[OF ep fit rate]
   _ finite_conditioned_fri_relation_drift_targets conditioned_drift_card])
   (use mca_conditioned_trace_fri_bad_challenge_relation_drift_activation_imp_target[OF fresh]
     in blast)

lemma fs_composition_per_key_transition:
 assumes fresh: "fmlookup M x=None" and ep: "clength*scale=2^N"
   and fit: "Suc(ceil_log(Suc maxDegree))\<le>N"
   and rate: "4*fri_padded_degree_bound maxDegree\<le>clength*scale"
 shows "card {y. hash_state_relation_transition
   (conditioned_fri_relation_bounded L mca_conditioned_composition_fri_bad_challenge_relation)
   M (fmupd x y M)} \<le> fri_mca_direct_cap+(2*L+2)"
 by (rule fs_per_key_bounded_transition[OF fresh
   mca_conditioned_composition_fri_bad_challenge_relation_direct_fiber_card_bound[OF ep fit rate]
   _ finite_conditioned_fri_relation_drift_targets conditioned_drift_card])
   (use mca_conditioned_composition_fri_bad_challenge_relation_drift_activation_imp_target[OF fresh]
     in blast)

lemma fs_alpha_per_key_transition:
 assumes fresh: "fmlookup M x=None"
 shows "card {y. hash_state_relation_transition
   (conditioned_fri_relation_bounded L robust_alpha_pivot_absorbed_query_relation)
   M (fmupd x y M)} \<le> 1+(2*L+2)"
 by (rule fs_per_key_bounded_transition[OF fresh
   robust_alpha_pivot_absorbed_query_relation_direct_fiber_card_bound
   _ finite_alpha_pivot_relation_drift_targets alpha_drift_card])
   (use robust_alpha_pivot_absorbed_query_relation_drift_activation_imp_target[OF fresh]
     in blast)

lemma fs_builder_bounded_recap:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and outcome: "Some (((prefix,prefix_state),data,query_start,raws,query_states),t)
     \<in>set_dist(execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
       (fs_compile_replay A P)) adversary_initial_state)"
   and clean: "\<not>hash_map_output_collision t"
   and old: "hash_state_relation_transition (conditioned_fri_relation_bounded L R)
     (HashMap adversary_initial_state) (HashMap t)"
 shows "hash_state_relation_transition
   (conditioned_fri_relation_bounded (fs_builder_fresh_budget Q) R)
   (HashMap adversary_initial_state) (HashMap t)"
proof (rule conditioned_relation_active_imp_bounded_initial_transition)
 show "\<exists>x y. hash_state_relation_active R (HashMap t) x y"
   using old unfolding hash_state_relation_transition_def
     hash_state_relation_active_def conditioned_fri_relation_bounded_def by blast
 show "card(fmdom'(HashMap t))\<le>fs_builder_fresh_budget Q"
   by (rule fs_builder_witness_domain[OF fixed bound outcome clean])
qed

lemma fs_compiled_trace_relation:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and ep: "clength*scale=2^N" and fit: "Suc(ceil_log clength)\<le>N"
   and rate: "4*fri_padded_degree_bound(clength-1)\<le>clength*scale"
 shows "wp_event
   (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses(fs_compile_replay A P))
   (hash_state_relation_transition_event
     (conditioned_fri_relation_bounded (fs_builder_fresh_budget Q)
       mca_conditioned_trace_fri_bad_challenge_relation)
     (HashMap adversary_initial_state))
   adversary_initial_state \<le>
     nnreal(fs_builder_fresh_budget Q*(fri_mca_direct_cap+(2*fs_builder_fresh_budget Q+2)))/nnreal size"
 by (rule fs_builder_witness_relation[OF fixed bound])
   (rule fs_trace_per_key_transition[OF _ ep fit rate])

lemma fs_compiled_composition_relation:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and ep: "clength*scale=2^N" and fit: "Suc(ceil_log(Suc maxDegree))\<le>N"
   and rate: "4*fri_padded_degree_bound maxDegree\<le>clength*scale"
 shows "wp_event
   (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses(fs_compile_replay A P))
   (hash_state_relation_transition_event
     (conditioned_fri_relation_bounded (fs_builder_fresh_budget Q)
       mca_conditioned_composition_fri_bad_challenge_relation)
     (HashMap adversary_initial_state))
   adversary_initial_state \<le>
     nnreal(fs_builder_fresh_budget Q*(fri_mca_direct_cap+(2*fs_builder_fresh_budget Q+2)))/nnreal size"
 by (rule fs_builder_witness_relation[OF fixed bound])
   (rule fs_composition_per_key_transition[OF _ ep fit rate])

lemma fs_compiled_alpha_relation:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
 shows "wp_event
   (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses(fs_compile_replay A P))
   (hash_state_relation_transition_event
     (conditioned_fri_relation_bounded (fs_builder_fresh_budget Q)
       robust_alpha_pivot_absorbed_query_relation)
     (HashMap adversary_initial_state))
   adversary_initial_state \<le>
     nnreal(fs_builder_fresh_budget Q*(1+(2*fs_builder_fresh_budget Q+2)))/nnreal size"
 by (rule fs_builder_witness_relation[OF fixed bound])
   (rule fs_alpha_per_key_transition)

lemma fs_compiled_trace_mca_bad:
  assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
    and ep: "clength * scale = 2 ^ N"
    and fit: "Suc (ceil_log clength) \<le> N"
    and rate: "4 * fri_padded_degree_bound (clength - 1) \<le> clength * scale"
  defines "q \<equiv> fs_builder_fresh_budget Q"
  shows "wp_event
    (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses (fs_compile_replay A P))
    (\<lambda>out. case out of None \<Rightarrow> False
      | Some ((prefix_with_state, data, query_start, raws, query_states), state) \<Rightarrow>
        fri_mca_trace_builder_bad data state)
    adversary_initial_state \<le>
      nnreal (q * (fri_mca_direct_cap + (2*q+2))) / nnreal size"
proof -
  have wf: "staged_budget_wellformed(fs_replay_budgets Q)"
    by (rule fs_replay_budgets_wellformed)
  have controlled: "staged_adversary_controlled(fs_replay_budgets Q) (fs_compile_replay A P)"
    by (rule fs_compile_replay_controlled[OF bound fixed])
  let ?m = "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses (fs_compile_replay A P)"
  let ?R = "conditioned_fri_relation_bounded q
    mca_conditioned_trace_fri_bad_challenge_relation"
  let ?E = "\<lambda>out. case out of None \<Rightarrow> False
    | Some ((prefix_with_state, data, query_start, raws, query_states), state) \<Rightarrow>
      fri_mca_trace_builder_bad data state"
  have mono: "wp_event ?m ?E adversary_initial_state \<le>
    wp_event ?m (hash_state_relation_transition_event ?R
      (HashMap adversary_initial_state)) adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?m adversary_initial_state)"
      and event: "?E out"
    obtain prefix prefix_state data query_start raws query_states state where
      out: "out = Some (((prefix, prefix_state), data, query_start, raws, query_states), state)"
      and bad: "fri_mca_trace_builder_bad data state"
      using event by (cases out) auto
    have hit: "\<exists>j < length (staged_trace_fri_roots data).
      staged_trace_fri_challenges data ! j \<in>
        fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j
          state (staged_trace_fri_roots data ! j)"
      using bad unfolding fri_mca_trace_builder_bad_def fri_mca_chain_bad_event_def by auto
    have "hash_state_relation_transition ?R (HashMap adversary_initial_state) (HashMap state)"
      unfolding q_def
      apply (rule fs_builder_bounded_recap[OF fixed bound support[unfolded out]])
       apply (use bad in \<open>fastforce simp: fri_mca_trace_builder_bad_def fri_mca_composition_builder_bad_def\<close>)
      by (rule checked_builder_trace_mca_online_bad_imp_bounded_relation_transition[
        OF wf controlled support[unfolded out] _ _ hit])
        (use bad in \<open>auto simp: fri_mca_trace_builder_bad_def\<close>)
    then show "hash_state_relation_transition_event ?R (HashMap adversary_initial_state) out"
      unfolding out hash_state_relation_transition_event_def by simp
  qed
  also have "wp_event ?m (hash_state_relation_transition_event ?R
      (HashMap adversary_initial_state)) adversary_initial_state \<le>
    nnreal (q * (fri_mca_direct_cap + (2*q+2))) / nnreal size"
    unfolding q_def by (rule
      fs_compiled_trace_relation[
        OF fixed bound ep fit rate])
  finally show ?thesis .
qed

lemma fs_compiled_composition_mca_bad:
  assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
    and ep: "clength * scale = 2 ^ N"
    and fit: "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and rate: "4 * fri_padded_degree_bound maxDegree \<le> clength * scale"
  defines "q \<equiv> fs_builder_fresh_budget Q"
  shows "wp_event
    (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses (fs_compile_replay A P))
    (\<lambda>out. case out of None \<Rightarrow> False
      | Some ((prefix_with_state, data, query_start, raws, query_states), state) \<Rightarrow>
        fri_mca_composition_builder_bad data state)
    adversary_initial_state \<le>
      nnreal (q * (fri_mca_direct_cap + (2*q+2))) / nnreal size"
proof -
  have wf: "staged_budget_wellformed(fs_replay_budgets Q)"
    by (rule fs_replay_budgets_wellformed)
  have controlled: "staged_adversary_controlled(fs_replay_budgets Q) (fs_compile_replay A P)"
    by (rule fs_compile_replay_controlled[OF bound fixed])
  let ?m = "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses (fs_compile_replay A P)"
  let ?R = "conditioned_fri_relation_bounded q
    mca_conditioned_composition_fri_bad_challenge_relation"
  let ?E = "\<lambda>out. case out of None \<Rightarrow> False
    | Some ((prefix_with_state, data, query_start, raws, query_states), state) \<Rightarrow>
      fri_mca_composition_builder_bad data state"
  have mono: "wp_event ?m ?E adversary_initial_state \<le>
    wp_event ?m (hash_state_relation_transition_event ?R
      (HashMap adversary_initial_state)) adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?m adversary_initial_state)"
      and event: "?E out"
    obtain prefix prefix_state data query_start raws query_states state where
      out: "out = Some (((prefix, prefix_state), data, query_start, raws, query_states), state)"
      and bad: "fri_mca_composition_builder_bad data state"
      using event by (cases out) auto
    have hit: "\<exists>j < length (staged_composition_fri_roots data).
      staged_composition_fri_challenges data ! j \<in>
        fri_mca_online_bad_challenges (to_nat (staged_degree data)) (fri_mca_quarter_radii j) j
          state (staged_composition_fri_roots data ! j)"
      using bad unfolding fri_mca_composition_builder_bad_def fri_mca_chain_bad_event_def by auto
    have "hash_state_relation_transition ?R (HashMap adversary_initial_state) (HashMap state)"
      unfolding q_def
      apply (rule fs_builder_bounded_recap[OF fixed bound support[unfolded out]])
       apply (use bad in \<open>fastforce simp: fri_mca_trace_builder_bad_def fri_mca_composition_builder_bad_def\<close>)
      by (rule checked_builder_composition_mca_online_bad_imp_bounded_relation_transition[
        OF wf controlled support[unfolded out] _ _ _ hit])
        (use bad in \<open>auto simp: fri_mca_composition_builder_bad_def\<close>)
    then show "hash_state_relation_transition_event ?R (HashMap adversary_initial_state) out"
      unfolding out hash_state_relation_transition_event_def by simp
  qed
  also have "wp_event ?m (hash_state_relation_transition_event ?R
      (HashMap adversary_initial_state)) adversary_initial_state \<le>
    nnreal (q * (fri_mca_direct_cap + (2*q+2))) / nnreal size"
    unfolding q_def by (rule
      fs_compiled_composition_relation[
        OF fixed bound ep fit rate])
  finally show ?thesis .
qed

end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then () else error "Unexpected challenge accounting dependency")
    @{thms soundness.fs_compiled_trace_mca_bad soundness.fs_compiled_composition_mca_bad
      soundness.fs_compiled_alpha_relation soundness.fs_builder_bounded_recap};
\<close>
end
