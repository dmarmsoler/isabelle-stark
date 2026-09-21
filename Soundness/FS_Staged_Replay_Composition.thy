(* Title: Stark/FS_Staged_Replay_Composition.thy
   License: BSD-3-Clause *)

theory FS_Staged_Replay_Composition
  imports FS_Fixed_Randomness_Replay
begin

section \<open>Replay composition through the actual staged experiment\<close>

text \<open>The relation below compares computations on every extension of a fixed
  oracle map. Its bind rule uses actual supported map extensions and retains
  failure mass. Induction through the unchanged staged drivers makes this
  relation applicable to all seven callback positions.

  A fixed program retains arbitrary oracle-answer-dependent continuations. The
  first producer run is executed, not assumed; after each supported outcome,
  later replays return the same result on every extending map. This eliminates
  later replays semantically, not operationally: their oracle calls still count.
  No new oracle, protocol premise or staged interface is introduced.\<close>

context soundness
begin

definition fs_above_eq where
  "fs_above_eq t m n \<longleftrightarrow> (\<forall>u F. t\<le>u \<longrightarrow> wp m F u = wp n F u)"

lemma fs_above_eq_refl: "fs_above_eq t m m"
  by (simp add: fs_above_eq_def)

lemma fs_above_eqD:
  "fs_above_eq t m n \<Longrightarrow> t\<le>u \<Longrightarrow> wp m F u = wp n F u"
  by (simp add: fs_above_eq_def)

lemma fs_above_eq_bind:
  assumes eq: "fs_above_eq t m n"
    and ext: "hash_extension_preserving n"
    and tail: "\<And>x. fs_above_eq t (k x) (l x)"
  shows "fs_above_eq t (m \<bind> k) (n \<bind> l)"
proof (unfold fs_above_eq_def, intro allI impI)
  fix u F assume tu: "t\<le>u"
  have cont: "wp(k x) F v = wp(l x) F v"
    if out: "Some(x,v)\<in>set_dist(execute n u)" for x v
  proof -
    have uv: "u\<le>v" using ext out
      unfolding hash_extension_preserving_def by blast
    have tv: "t\<le>v" by (rule hash_ext_trans[OF tu uv])
    show ?thesis by (rule fs_above_eqD[OF tail tv])
  qed
  show "wp (m \<bind> k) F u = wp (n \<bind> l) F u"
    apply (simp only: wp_bind fs_above_eqD[OF eq tu])
    apply (rule fs_wp_cong_on_support)
    using cont by (auto split: option.splits prod.splits)
qed

lemma fs_above_replay:
  assumes "replayable_ro m" "Some(x,t)\<in>set_dist(execute m s)"
  shows "fs_above_eq t (m \<bind> k) (k x)"
  using assms unfolding fs_above_eq_def replayable_ro_def
  by (simp add: wp_bind)

lemma fs_challenges_extend:
  "hash_extension_preserving receive_trace_fri_challenge"
  "hash_extension_preserving receive_composition_fri_challenge"
  "hash_extension_preserving receive_alpha_challenge"
  "hash_extension_preserving receive_query_index_challenge"
  unfolding hash_extension_preserving_def
  using receive_trace_fri_challenge_extends receive_composition_fri_challenge_extends
    receive_alpha_challenge_extends receive_query_index_challenge_extends by blast+

lemma fs_assert_extends: "hash_extension_preserving (assert b)"
  by (cases b) (simp_all add: assert_def hash_extension_preserving_return
    hash_extension_preserving_def throw_no_outcome hash_ext_refl)

lemma fs_records_extend: "hash_extension_preserving (ro_record_staged_messages xs)"
  unfolding ro_record_staged_messages_def
  by (induction xs)
    (auto intro!: hash_extension_preserving_bind
      intro: fs_record_extends hash_extension_preserving_return)

lemma fs_alphas_extend: "hash_extension_preserving (ro_staged_alpha_program n)"
  by (induction n)
    (auto intro!: hash_extension_preserving_bind
      intro: fs_record_extends hash_extension_preserving_return fs_challenges_extend)

lemma fs_trace_loop_extend:
  assumes "\<And>i bs. hash_extension_preserving (trace_fri_root_stage B i bs)"
  shows "hash_extension_preserving (ro_staged_trace_fri_program B i n bs)"
  by (induction n arbitrary: i bs)
    (auto simp: split_def intro!: hash_extension_preserving_bind
      intro: assms fs_record_extends hash_extension_preserving_return fs_challenges_extend)

lemma fs_composition_loop_extend:
  assumes "\<And>i bs. hash_extension_preserving (composition_fri_root_stage B dg i bs)"
  shows "hash_extension_preserving (ro_staged_composition_fri_program B dg i n bs)"
  by (induction n arbitrary: i bs)
    (auto simp: split_def intro!: hash_extension_preserving_bind
      intro: assms fs_record_extends hash_extension_preserving_return fs_challenges_extend)

lemma fs_queries_extend:
  assumes "\<And>i raw. hash_extension_preserving (query_opening_stage B i raw)"
  shows "hash_extension_preserving (ro_checked_staged_query_program B rs crs i n)"
  by (induction n arbitrary: i)
    (auto simp: Let_def intro!: hash_extension_preserving_bind
      intro: assms fs_assert_extends fs_records_extend
        hash_extension_preserving_return fs_challenges_extend)

lemma fs_trace_loop_above_eq:
  assumes cb: "\<And>i bs. fs_above_eq t (trace_fri_root_stage A i bs) (trace_fri_root_stage B i bs)"
    and ext: "\<And>i bs. hash_extension_preserving (trace_fri_root_stage B i bs)"
  shows "fs_above_eq t (ro_staged_trace_fri_program A i n bs)
    (ro_staged_trace_fri_program B i n bs)"
  by (induction n arbitrary: i bs)
    (auto simp: split_def intro!: fs_above_eq_bind
      intro: cb ext fs_above_eq_refl fs_record_extends fs_challenges_extend
        fs_trace_loop_extend hash_extension_preserving_return)

lemma fs_composition_loop_above_eq:
  assumes cb: "\<And>i bs. fs_above_eq t (composition_fri_root_stage A dg i bs)
    (composition_fri_root_stage B dg i bs)"
    and ext: "\<And>i bs. hash_extension_preserving (composition_fri_root_stage B dg i bs)"
  shows "fs_above_eq t (ro_staged_composition_fri_program A dg i n bs)
    (ro_staged_composition_fri_program B dg i n bs)"
  by (induction n arbitrary: i bs)
    (auto simp: split_def intro!: fs_above_eq_bind
      intro: cb ext fs_above_eq_refl fs_record_extends fs_challenges_extend
        fs_composition_loop_extend hash_extension_preserving_return)

lemma fs_queries_above_eq:
  assumes cb: "\<And>i raw. fs_above_eq t (query_opening_stage A i raw)
    (query_opening_stage B i raw)"
    and ext: "\<And>i raw. hash_extension_preserving (query_opening_stage B i raw)"
  shows "fs_above_eq t (ro_checked_staged_query_program A rs crs i n)
    (ro_checked_staged_query_program B rs crs i n)"
  by (induction n arbitrary: i)
    (auto simp: Let_def intro!: fs_above_eq_bind
      intro: cb ext fs_above_eq_refl fs_records_extend fs_assert_extends
        fs_challenges_extend fs_queries_extend hash_extension_preserving_return)

definition fs_callbacks_above_eq where
  "fs_callbacks_above_eq t A B \<longleftrightarrow>
    fs_above_eq t (trace_root_stage A) (trace_root_stage B) \<and>
    (\<forall>i bs. fs_above_eq t (trace_fri_root_stage A i bs) (trace_fri_root_stage B i bs)) \<and>
    (\<forall>bs. fs_above_eq t (trace_final_stage A bs) (trace_final_stage B bs)) \<and>
    (\<forall>as. fs_above_eq t (degree_stage A as) (degree_stage B as)) \<and>
    (\<forall>dg i bs. fs_above_eq t (composition_fri_root_stage A dg i bs)
      (composition_fri_root_stage B dg i bs)) \<and>
    (\<forall>dg bs. fs_above_eq t (composition_final_stage A dg bs) (composition_final_stage B dg bs)) \<and>
    (\<forall>i raw. fs_above_eq t (query_opening_stage A i raw) (query_opening_stage B i raw))"

definition fs_callbacks_extend where
  "fs_callbacks_extend B \<longleftrightarrow>
    hash_extension_preserving (trace_root_stage B) \<and>
    (\<forall>i bs. hash_extension_preserving (trace_fri_root_stage B i bs)) \<and>
    (\<forall>bs. hash_extension_preserving (trace_final_stage B bs)) \<and>
    (\<forall>as. hash_extension_preserving (degree_stage B as)) \<and>
    (\<forall>dg i bs. hash_extension_preserving (composition_fri_root_stage B dg i bs)) \<and>
    (\<forall>dg bs. hash_extension_preserving (composition_final_stage B dg bs)) \<and>
    (\<forall>i raw. hash_extension_preserving (query_opening_stage B i raw))"

lemma fs_builder_above_eq:
  assumes eq: "fs_callbacks_above_eq t A B" and ext: "fs_callbacks_extend B"
  shows "fs_above_eq t (ro_checked_staged_transcript_program A)
    (ro_checked_staged_transcript_program B)"
  using eq ext unfolding fs_callbacks_above_eq_def fs_callbacks_extend_def
    ro_checked_staged_transcript_program_def
  by (auto simp: Let_def split_def intro!: fs_above_eq_bind
    intro: fs_above_eq_refl fs_record_extends fs_alphas_extend fs_assert_extends
      fs_trace_loop_above_eq fs_trace_loop_extend
      fs_composition_loop_above_eq fs_composition_loop_extend
      fs_queries_above_eq fs_queries_extend hash_extension_preserving_return)

lemma fs_above_eq_follow:
  assumes "fs_above_eq t m n"
  shows "fs_above_eq t (m \<bind> k) (n \<bind> k)"
  using assms by (simp add: fs_above_eq_def wp_bind)

lemma fs_experiment_above_eq:
  assumes "fs_callbacks_above_eq t A B" "fs_callbacks_extend B"
  shows "fs_above_eq t (ro_absorb_checked_staged_security_experiment A)
    (ro_absorb_checked_staged_security_experiment B)"
  unfolding ro_absorb_checked_staged_security_experiment_def
  by (rule fs_above_eq_follow) (rule fs_builder_above_eq[OF assms])

definition fs_replay_staged where
  "fs_replay_staged P family =
    \<lparr>trace_root_stage=fs_run P \<bind> (\<lambda>x. trace_root_stage(family x)),
     trace_fri_root_stage=\<lambda>i bs. fs_run P \<bind> (\<lambda>x. trace_fri_root_stage(family x) i bs),
     trace_final_stage=\<lambda>bs. fs_run P \<bind> (\<lambda>x. trace_final_stage(family x) bs),
     degree_stage=\<lambda>as. fs_run P \<bind> (\<lambda>x. degree_stage(family x) as),
     composition_fri_root_stage=\<lambda>dg i bs. fs_run P \<bind>
       (\<lambda>x. composition_fri_root_stage(family x) dg i bs),
     composition_final_stage=\<lambda>dg bs. fs_run P \<bind>
       (\<lambda>x. composition_final_stage(family x) dg bs),
     query_opening_stage=\<lambda>i raw. fs_run P \<bind> (\<lambda>x. query_opening_stage(family x) i raw)\<rparr>"

lemma fs_replay_staged_above_eq:
  assumes "fs_fixed P" "Some(x,t)\<in>set_dist(execute(fs_run P)s)"
  shows "fs_callbacks_above_eq t (fs_replay_staged P family) (family x)"
  unfolding fs_callbacks_above_eq_def fs_replay_staged_def
  by (auto intro: fs_above_replay[OF fs_fixed_replayable[OF assms(1)] assms(2)])

lemma fs_trace_loop_root_update:
  "ro_staged_trace_fri_program (A\<lparr>trace_root_stage:=m\<rparr>) i n bs =
    ro_staged_trace_fri_program A i n bs"
  by (induction n arbitrary: i bs) (simp_all add: split_def)

lemma fs_composition_loop_root_update:
  "ro_staged_composition_fri_program (A\<lparr>trace_root_stage:=m\<rparr>) dg i n bs =
    ro_staged_composition_fri_program A dg i n bs"
  by (induction n arbitrary: i bs) (simp_all add: split_def)

lemma fs_queries_root_update:
  "ro_checked_staged_query_program (A\<lparr>trace_root_stage:=m\<rparr>) rs crs i n =
    ro_checked_staged_query_program A rs crs i n"
  by (induction n arbitrary: i) (simp_all add: Let_def)

lemma fs_replay_staged_first:
  "ro_absorb_checked_staged_security_experiment(fs_replay_staged P family) =
    (fs_run P \<bind> (\<lambda>x. ro_absorb_checked_staged_security_experiment
      ((fs_replay_staged P family)\<lparr>trace_root_stage:=trace_root_stage(family x)\<rparr>)))"
proof -
  have root: "trace_root_stage(fs_replay_staged P family) =
    (fs_run P \<bind> (\<lambda>x. trace_root_stage(family x)))"
    by (simp add: fs_replay_staged_def)
  show ?thesis
    by (simp add: ro_absorb_checked_staged_security_experiment_def
      ro_checked_staged_transcript_program_def root sm_bind_assoc
      fs_trace_loop_root_update fs_composition_loop_root_update fs_queries_root_update)
qed

lemma fs_callbacks_above_eq_root:
  assumes "fs_callbacks_above_eq t A B"
  shows "fs_callbacks_above_eq t (A\<lparr>trace_root_stage:=trace_root_stage B\<rparr>) B"
  using assms by (simp add: fs_callbacks_above_eq_def fs_above_eq_refl)

lemma fs_replay_staged_elimination:
  assumes fixed: "fs_fixed P" and ext: "\<And>x. fs_callbacks_extend(family x)"
  shows "wp(ro_absorb_checked_staged_security_experiment(fs_replay_staged P family)) F s =
    wp(fs_run P \<bind> (\<lambda>x. ro_absorb_checked_staged_security_experiment(family x))) F s"
proof -
  have point: "wp(ro_absorb_checked_staged_security_experiment
      ((fs_replay_staged P family)\<lparr>trace_root_stage:=trace_root_stage(family x)\<rparr>)) F t =
    wp(ro_absorb_checked_staged_security_experiment(family x)) F t"
    if out: "Some(x,t)\<in>set_dist(execute(fs_run P)s)" for x t
    by (rule fs_above_eqD[OF _ hash_ext_refl],
        rule fs_experiment_above_eq[OF _ ext])
      (rule fs_callbacks_above_eq_root[OF fs_replay_staged_above_eq[OF fixed out]])
  show ?thesis
    apply (subst fs_replay_staged_first)
    apply (simp only: wp_bind)
    apply (rule fs_wp_cong_on_support)
    using point by (auto split: option.splits prod.splits)
qed

end
end
