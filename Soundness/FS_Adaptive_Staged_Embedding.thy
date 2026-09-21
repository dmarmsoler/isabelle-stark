(* Title: Stark/FS_Adaptive_Staged_Embedding.thy
   License: BSD-3-Clause *)

theory FS_Adaptive_Staged_Embedding
  imports FS_Staged_Replay_Composition FS_Full_Transcript_Reconstruction
    FS_Private_Randomness_Normalization
begin

section \<open>Adaptive Fiat--Shamir producer integration\<close>

text \<open>The compiler replays one fixed private program at every callback and uses
  the already checked guarded transcript selectors. Later query keys may depend
  on all earlier oracle answers. Exact replay holds on every extension of the
  first run's actual map, including maps extended by protocol operations.

  For a fixed program, the complete existing staged experiment has exactly the
  original Fiat--Shamir acceptance probability. General private sampling is
  represented by an oracle-independent mixture of whole compiled staged records.
  One normalized program is shared by every callback; it is not sampled anew
  per callback. This semantic existence construction is not an efficient
  enumeration of private strategies or a new shared-state attacker interface.

  The stronger observable theorem ignores only the final transcript field,
  because staged serialization omits unused suffixes. Malformed transcripts,
  failure, collisions and every oracle answer remain in scope. Each callback
  has all-state allowance Q, but replayed calls are still charged. No total
  allowance translation, new public soundness bound or numerical profile is
  derived in this layer.\<close>

context soundness
begin

lemma fs_fixed_callbacks_extend:
  "fs_callbacks_extend(fs_fixed_transcript_staged_adversary A source)"
  unfolding fs_callbacks_extend_def
  by (auto intro: controlled_ro_program_extension[OF fs_fixed_transcript_callbacks_controlled(1)]
    controlled_ro_program_extension[OF fs_fixed_transcript_callbacks_controlled(2)]
    controlled_ro_program_extension[OF fs_fixed_transcript_callbacks_controlled(3)]
    controlled_ro_program_extension[OF fs_fixed_transcript_callbacks_controlled(4)]
    controlled_ro_program_extension[OF fs_fixed_transcript_callbacks_controlled(5)]
    controlled_ro_program_extension[OF fs_fixed_transcript_callbacks_controlled(6)]
    controlled_ro_program_extension[OF fs_fixed_transcript_callbacks_controlled(7)])

definition fs_compile_replay ::
  "'f staged_adversary \<Rightarrow> ('f,'f list) fs_program \<Rightarrow> 'f staged_adversary" where
  "fs_compile_replay A P = fs_replay_staged P (fs_fixed_transcript_staged_adversary A)"

lemma fs_compile_replay_elimination:
  assumes "fs_fixed P"
  shows "wp(ro_absorb_checked_staged_security_experiment(fs_compile_replay A P)) F s =
    wp(fs_run P \<bind> (\<lambda>source. ro_absorb_checked_staged_security_experiment
      (fs_fixed_transcript_staged_adversary A source))) F s"
  unfolding fs_compile_replay_def
  by (rule fs_replay_staged_elimination[OF assms]) (rule fs_fixed_callbacks_extend)

lemma fs_producer_initial_fields:
  assumes bound: "fs_query_bound q P"
    and out: "Some(source,t)\<in>set_dist(execute(fs_run P)(verifier_state_from_adversary base []))"
  shows "t=verifier_state_from_adversary t []"
  using controlled_ro_program_preserves_protocol_fields[OF fs_run_controlled[OF bound],
    unfolded protocol_fields_preserving_def, rule_format, OF out]
  by (cases t) (simp add: verifier_state_from_adversary_def)

theorem fs_compile_replay_wp:
  assumes fixed: "fs_fixed P" and bound: "fs_query_bound q P"
    and obs: "fs_ignores_transcript F"
  shows "wp(ro_absorb_checked_staged_security_experiment(fs_compile_replay A P)) F
      (verifier_state_from_adversary base []) =
    wp(fs_security_experiment P) F (verifier_state_from_adversary base [])"
proof -
  have point: "wp(ro_absorb_checked_staged_security_experiment
      (fs_fixed_transcript_staged_adversary A source)) F t =
    wp(verifier_state_transfer source \<bind> (\<lambda>_. ro_verify_monad)) F t"
    if out: "Some(source,t)\<in>set_dist
      (execute(fs_run P)(verifier_state_from_adversary base []))" for source t
  proof -
    have fields: "t=verifier_state_from_adversary t []"
      by (rule fs_producer_initial_fields[OF bound out])
    note replay = fs_fixed_transcript_full_reconstruction_wp[OF obs, where A=A
      and source=source and base=t]
    show ?thesis using replay
      by (subst (1) fields)
        (simp add: verifier_state_transfer_def wp_bind wp_get wp_put)
  qed
  show ?thesis
    unfolding fs_compile_replay_elimination[OF fixed] fs_security_experiment_def
    apply (simp only: wp_bind)
    apply (rule fs_wp_cong_on_support)
    using point[unfolded wp_bind] by (auto split: option.splits prod.splits)
qed

corollary fs_compile_replay_acceptance:
  assumes "fs_fixed P" "fs_query_bound q P"
  shows "wp_event(ro_absorb_checked_staged_security_experiment(fs_compile_replay A P))
    accepted adversary_initial_state = fs_acceptance_probability P"
  using fs_compile_replay_wp[OF assms, where A=A and base=adversary_initial_state
    and F="\<lambda>out. if accepted out then 1 else 0"]
  by (simp add: fs_ignores_transcript_def accepted_def fs_acceptance_probability_def
    wp_event_def verifier_state_from_adversary_def adversary_initial_state_def)

definition fs_compiled_mixture where
  "fs_compiled_mixture A P = lift(\<lambda>_. fs_normalize P) \<bind>
    (\<lambda>T. ro_absorb_checked_staged_security_experiment(fs_compile_replay A T))"

theorem fs_compiled_mixture_wp:
  assumes bound: "fs_query_bound q P" and obs: "fs_ignores_transcript F"
  shows "wp(fs_compiled_mixture A P) F (verifier_state_from_adversary base []) =
    wp(fs_security_experiment P) F (verifier_state_from_adversary base [])"
proof -
  have "wp(fs_compiled_mixture A P) F (verifier_state_from_adversary base []) =
    dist_expect(fs_normalize P)
      (\<lambda>T. wp(fs_security_experiment T) F (verifier_state_from_adversary base []))"
    unfolding fs_compiled_mixture_def wp_bind wp_lift option.case prod.case
    by (rule fs_expect_cong, rule fs_compile_replay_wp)
      (auto intro: fs_normalize_fixed fs_normalize_bound[OF bound] obs)
  also have "... = wp(fs_security_experiment P) F (verifier_state_from_adversary base [])"
    unfolding fs_security_experiment_def by (rule fs_normalize_follow_wp)
  finally show ?thesis .
qed

corollary fs_compiled_mixture_acceptance:
  assumes "fs_query_bound q P"
  shows "wp_event(fs_compiled_mixture A P) accepted adversary_initial_state =
    fs_acceptance_probability P"
  using fs_compiled_mixture_wp[OF assms, where A=A and base=adversary_initial_state
    and F="\<lambda>out. if accepted out then 1 else 0"]
  by (simp add: fs_ignores_transcript_def accepted_def fs_acceptance_probability_def
    wp_event_def verifier_state_from_adversary_def adversary_initial_state_def)

corollary fs_compiled_staged_acceptance_mixture:
  assumes "fs_query_bound q P"
  shows "dist_expect(fs_normalize P)
    (\<lambda>T. wp_event(ro_absorb_checked_staged_security_experiment(fs_compile_replay A T))
      accepted adversary_initial_state) = fs_acceptance_probability P"
  using fs_compiled_mixture_acceptance[OF assms, where A=A]
  by (simp add: fs_compiled_mixture_def wp_event_def wp_bind wp_lift)

lemma fs_compile_replay_callbacks_controlled:
  assumes bound: "fs_query_bound q P" and fixed: "fs_fixed P"
  shows "controlled_ro_program q (trace_root_stage(fs_compile_replay A P))"
    and "controlled_ro_program q (trace_fri_root_stage(fs_compile_replay A P) i bs)"
    and "controlled_ro_program q (trace_final_stage(fs_compile_replay A P) bs)"
    and "controlled_ro_program q (degree_stage(fs_compile_replay A P) as)"
    and "controlled_ro_program q (composition_fri_root_stage(fs_compile_replay A P) dg i bs)"
    and "controlled_ro_program q (composition_final_stage(fs_compile_replay A P) dg bs)"
    and "controlled_ro_program q (query_opening_stage(fs_compile_replay A P) i raw)"
  unfolding fs_compile_replay_def fs_replay_staged_def
  by (auto intro!: fs_fixed_controlled_cont[OF bound fixed, where r=0, simplified]
    intro: fs_fixed_transcript_callbacks_controlled)

lemma fs_compiled_staged_bound_suffices:
  assumes bound: "fs_query_bound q P"
    and staged: "\<And>T. fs_fixed T \<Longrightarrow> fs_query_bound q T \<Longrightarrow>
      wp_event(ro_absorb_checked_staged_security_experiment(fs_compile_replay A T))
        accepted adversary_initial_state \<le> epsilon"
  shows "fs_acceptance_probability P \<le> epsilon"
proof -
  have "dist_expect(fs_normalize P)
    (\<lambda>T. wp_event(ro_absorb_checked_staged_security_experiment(fs_compile_replay A T))
      accepted adversary_initial_state) \<le> epsilon"
    by (rule fs_expect_le_const, rule staged)
      (auto intro: fs_normalize_fixed fs_normalize_bound[OF bound])
  then show ?thesis by (simp only: fs_compiled_staged_acceptance_mixture[OF bound])
qed

end

ML \<open>
  val checked = @{thms soundness.fs_above_eq_refl soundness.fs_above_eqD
    soundness.fs_above_eq_bind soundness.fs_above_replay
    soundness.fs_challenges_extend soundness.fs_assert_extends soundness.fs_records_extend
    soundness.fs_alphas_extend soundness.fs_trace_loop_extend soundness.fs_composition_loop_extend
    soundness.fs_queries_extend soundness.fs_trace_loop_above_eq
    soundness.fs_composition_loop_above_eq soundness.fs_queries_above_eq
    soundness.fs_builder_above_eq soundness.fs_above_eq_follow soundness.fs_experiment_above_eq
    soundness.fs_replay_staged_above_eq soundness.fs_trace_loop_root_update
    soundness.fs_composition_loop_root_update soundness.fs_queries_root_update
    soundness.fs_replay_staged_first soundness.fs_callbacks_above_eq_root
    soundness.fs_replay_staged_elimination soundness.fs_fixed_callbacks_extend
    soundness.fs_compile_replay_elimination soundness.fs_producer_initial_fields
    soundness.fs_compile_replay_wp soundness.fs_compile_replay_acceptance
    soundness.fs_compiled_mixture_wp soundness.fs_compiled_mixture_acceptance
    soundness.fs_compiled_staged_acceptance_mixture
    soundness.fs_compile_replay_callbacks_controlled soundness.fs_compiled_staged_bound_suffices};
  List.app (fn th =>
    if null(Thm.hyps_of th) andalso null(Thm_Deps.all_oracles [th])
    then () else error "Unexpected adaptive replay proof dependency") checked;
  writeln("Adaptive replay checked conclusions: " ^ Int.toString(length checked));
  if Thm.nprems_of @{thm soundness.fs_compile_replay_acceptance} = 3
    andalso Thm.nprems_of @{thm soundness.fs_compiled_mixture_acceptance} = 2
  then () else error "Unexpected adaptive acceptance premise count";
\<close>
end
