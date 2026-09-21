(* Title: Stark/FS_Fixed_Randomness_Replay.thy
   License: BSD-3-Clause *)

theory FS_Fixed_Randomness_Replay
  imports FS_Staged_Allowance_Audit RO_Honest_Replay_Primitives
begin

section \<open>Bounded fixed-randomness replay pilot\<close>

text \<open>
  Fixing private randomness does not fix oracle answers: every query continuation
  below remains an arbitrary function of its answer. The fixed-program predicate
  excludes further private sampling but permits failure. Independent finite seed
  mixtures are handled explicitly below. No general normalization of interleaved
  private sampling into such a mixture is claimed in this pilot.

  Replay is proved against extensions of the completed oracle map, using the
  existing replay infrastructure. Two actual callback types are connected
  across the unchanged message-absorption operation. This is a prefix pilot, not
  a full FS-to-staged accepting-transcript reduction or a public security bound.
\<close>

inductive fs_fixed :: "('f,'a) fs_program \<Rightarrow> bool"
where
  Return: "fs_fixed (FS_Return x)"
| Fail: "fs_fixed FS_Fail"
| Query: "(\<And>y. fs_fixed (k y)) \<Longrightarrow> fs_fixed (FS_Query key k)"

context soundness
begin

subsection \<open>Replay of adaptive computations and their call counters\<close>

lemma fs_fixed_extends:
  assumes "fs_fixed P"
  shows "hash_extension_preserving (fs_run P)"
  using assms
proof (induction rule: fs_fixed.induct)
  case (Return x)
  then show ?case by (simp add: hash_extension_preserving_return)
next
  case Fail
  then show ?case
    by (simp add: hash_extension_preserving_def throw_no_outcome)
next
  case (Query k key)
  then show ?case
    by (simp only: fs_run.simps)
      (auto intro: hash_extension_preserving_bind hash_extension_preserving_hash)
qed

lemma fs_fixed_replayable:
  assumes "fs_fixed P"
  shows "replayable_ro (fs_run P)"
  using assms
proof (induction rule: fs_fixed.induct)
  case (Return x)
  then show ?case by (simp add: replayable_ro_return)
next
  case Fail
  then show ?case by (simp add: replayable_ro_def throw_no_outcome)
next
  case (Query k key)
  have ext: "hash_extension_preserving (fs_run (k y))" for y
    by (rule fs_fixed_extends) (rule Query.hyps)
  show ?case
    by (simp only: fs_run.simps)
      (rule replayable_ro_bind[OF replayable_ro_hash Query.IH ext])
qed

lemma fs_fixed_count_extends:
  assumes "fs_fixed P"
  shows "hash_extension_preserving (fs_count_run P)"
  using assms
proof (induction rule: fs_fixed.induct)
  case (Return x)
  then show ?case by (simp add: hash_extension_preserving_return)
next
  case Fail
  then show ?case by (simp add: hash_extension_preserving_def throw_no_outcome)
next
  case (Query k key)
  show ?case
    by (simp only: fs_count_run.simps)
      (auto intro!: hash_extension_preserving_bind
        intro: hash_extension_preserving_hash hash_extension_preserving_return Query.IH)
qed

lemma fs_fixed_count_replayable:
  assumes "fs_fixed P"
  shows "replayable_ro (fs_count_run P)"
  using assms
proof (induction rule: fs_fixed.induct)
  case (Return x)
  then show ?case by (simp add: replayable_ro_return)
next
  case Fail
  then show ?case by (simp add: replayable_ro_def throw_no_outcome)
next
  case (Query k key)
  have ext: "hash_extension_preserving (fs_count_run (k y))" for y
    by (rule fs_fixed_count_extends) (rule Query.hyps)
  show ?case
    by (simp only: fs_count_run.simps)
      (auto intro!: replayable_ro_bind hash_extension_preserving_bind
        intro: replayable_ro_hash replayable_ro_return Query.IH
          hash_extension_preserving_return hash_extension_preserving_hash ext)
qed

lemma fs_fixed_exact_replay:
  assumes "fs_fixed P"
    "Some ((x,n),t) \<in> set_dist (execute (fs_count_run P) s)" "t \<le> u"
  shows "wp (fs_count_run P) F u = F (Some ((x,n),u))"
  using fs_fixed_count_replayable[OF assms(1)] assms(2,3)
  unfolding replayable_ro_def by blast

subsection \<open>Failure-aware probability identity across oracle-map extensions\<close>

lemma fs_wp_cong_on_support:
  assumes "\<And>out. out \<in> set_dist (execute m s) \<Longrightarrow> F out = F' out"
  shows "wp m F s = wp m F' s"
  by (intro antisym; rule wp_mono_on_support) (use assms in auto)

lemma fs_replay_after_extension:
  fixes m :: "('a, 'f protocol_channel) state_monad"
  assumes replay: "replayable_ro m"
    and out: "Some (x,t) \<in> set_dist (execute m s)"
    and ext: "hash_extension_preserving gap"
  shows "wp (gap \<bind> (\<lambda>z. m \<bind> (\<lambda>y. k z y))) F t =
    wp (gap \<bind> (\<lambda>z. k z x)) F t"
proof (simp only: wp_bind, rule fs_wp_cong_on_support)
  fix out'
  assume "out' \<in> set_dist (execute gap t)"
  then show "(case out' of None \<Rightarrow> F None | Some (z,u) \<Rightarrow>
      wp m (\<lambda>res. case res of None \<Rightarrow> F None
        | Some (y,v) \<Rightarrow> wp (k z y) F v) u) =
    (case out' of None \<Rightarrow> F None | Some (z,u) \<Rightarrow> wp (k z x) F u)"
    using ext replay out
    unfolding hash_extension_preserving_def replayable_ro_def
    by (cases out') (auto split: prod.splits)
qed

lemma fs_two_replays_wp:
  fixes m :: "('a, 'f protocol_channel) state_monad"
  assumes replay: "replayable_ro m"
    and ext: "\<And>x. hash_extension_preserving (gap (f x))"
  shows "wp (m \<bind> (\<lambda>x. gap (f x) \<bind> (\<lambda>_.
      m \<bind> (\<lambda>y. return (f x,select_second y))))) F s =
    wp (m \<bind> (\<lambda>x. gap (f x) \<bind> (\<lambda>_.
      return (f x,select_second x)))) F s"
proof (subst (1 2) wp_bind, rule fs_wp_cong_on_support)
  fix out
  assume out: "out \<in> set_dist (execute m s)"
  show "(case out of None \<Rightarrow> F None | Some (x,t) \<Rightarrow>
      wp (gap (f x) \<bind> (\<lambda>_. m \<bind> (\<lambda>y. return (f x,select_second y)))) F t) =
    (case out of None \<Rightarrow> F None | Some (x,t) \<Rightarrow>
      wp (gap (f x) \<bind> (\<lambda>_. return (f x,select_second x))) F t)"
    using out fs_replay_after_extension[OF replay _ ext]
    by (cases out) auto
qed

subsection \<open>Projected callbacks and all-state declared allowances\<close>

lemma fs_throw_bind:
  "(throw \<bind> k) = throw"
  apply (rule execute_inject[THEN iffD1], rule ext, rule dist_inject[THEN iffD1])
  apply (simp only: sm_bind.rep_eq throw.rep_eq dist_throw_def
    dist_bind.rep_eq dist_delta_dist o_def)
  apply (subst map_bind_delta_left)
  by (auto simp: bind_cont_map_def delta_map_def)

lemma fs_fixed_controlled_cont:
  assumes bound: "fs_query_bound q P"
    and fixed: "fs_fixed P"
    and cont: "\<And>x. controlled_ro_program r (tail x)"
  shows "controlled_ro_program (q+r) (fs_run P \<bind> tail)"
  using bound fixed cont
proof (induction arbitrary: r tail rule: fs_query_bound.induct)
  case (Return q x)
  have base: "controlled_ro_program r (tail x)" by (rule Return.prems(2))
  have le: "r \<le> q+r" by simp
  show ?case
    by (simp only: fs_run.simps sm_bind_return_left)
      (rule controlled_ro_program.Weaken[OF base le])
next
  case (Fail q)
  then show ?case
    by (simp add: fs_throw_bind) (auto intro: controlled_ro_program.Weaken)
next
  case (Query q k key)
  have fixed_k: "fs_fixed (k y)" for y using Query.prems(1)
    by (cases rule: fs_fixed.cases) simp_all
  show ?case
    by (simp add: sm_bind_assoc)
      (auto intro: Query.IH[OF fixed_k Query.prems(2)])
next
  case (Sample q k d)
  from Sample.prems(1) show ?case by (cases rule: fs_fixed.cases)
qed

definition fs_replay_callback where
  "fs_replay_callback P select = fs_run P \<bind> (\<lambda>x. return (select x))"

lemma fs_replay_callback_controlled:
  assumes "fs_query_bound q P" "fs_fixed P"
  shows "controlled_ro_program q (fs_replay_callback P select)"
  using fs_fixed_controlled_cont[OF assms, of 0 "\<lambda>x. return (select x)"]
  unfolding fs_replay_callback_def by auto

definition fs_two_callbacks where
  "fs_two_callbacks P select_first select_second gap =
    fs_replay_callback P select_first \<bind> (\<lambda>a. gap a \<bind> (\<lambda>_.
    fs_replay_callback P select_second \<bind> (\<lambda>b. return (a,b))))"

lemma fs_two_callbacks_wp:
  assumes fixed: "fs_fixed P"
    and ext: "\<And>x. hash_extension_preserving (gap (select_first x))"
  shows "wp (fs_two_callbacks P select_first select_second gap) F s =
    wp (fs_run P \<bind> (\<lambda>x. gap (select_first x) \<bind> (\<lambda>_.
      return (select_first x,select_second x)))) F s"
  unfolding fs_two_callbacks_def fs_replay_callback_def
  by (simp add: sm_bind_assoc)
    (rule fs_two_replays_wp[OF fs_fixed_replayable[OF fixed]]; rule ext)

lemma fs_record_extends:
  "hash_extension_preserving (ro_record_staged_message a)"
  unfolding hash_extension_preserving_def
  using ro_record_staged_message_hash_extends_query_counter by auto

lemma fs_two_actual_callbacks_wp:
  assumes "fs_fixed P"
  shows "wp (fs_two_callbacks P select_first select_second ro_record_staged_message) F s =
    wp (fs_run P \<bind> (\<lambda>x. ro_record_staged_message (select_first x) \<bind>
      (\<lambda>_. return (select_first x,select_second x)))) F s"
  by (rule fs_two_callbacks_wp[OF assms]) (rule fs_record_extends)

lemma fs_two_callback_allowances:
  assumes "fs_query_bound q P" "fs_fixed P"
  shows "controlled_ro_program q (fs_replay_callback P select_first)"
    and "controlled_ro_program q (fs_replay_callback P select_second)"
    and "sum_list [q,q] = 2*q"
  using fs_replay_callback_controlled[OF assms] by simp_all

definition fs_replay_pair_attacker where
  "fs_replay_pair_attacker P select_first select_second A =
    A\<lparr>trace_root_stage := fs_replay_callback P select_first,
      trace_fri_root_stage := (\<lambda>i bs. fs_replay_callback P select_second)\<rparr>"

lemma fs_replay_pair_actual_prefix:
  "trace_root_stage (fs_replay_pair_attacker P select_first select_second A) \<bind>
     (\<lambda>a. ro_record_staged_message a \<bind> (\<lambda>_.
       trace_fri_root_stage (fs_replay_pair_attacker P select_first select_second A) 0 [] \<bind>
         (\<lambda>b. return (a,b)))) =
    fs_two_callbacks P select_first select_second ro_record_staged_message"
  unfolding fs_replay_pair_attacker_def fs_two_callbacks_def by simp

subsection \<open>Oracle-independent finite private-seed mixtures\<close>

lemma fs_independent_seed_two_callbacks:
  assumes fixed: "\<And>seed. fs_fixed (family seed)"
    and ext: "\<And>x. hash_extension_preserving (gap x)"
  shows "dist_expect d (\<lambda>seed.
      wp (fs_two_callbacks (family seed) select_first select_second gap) F s) =
    wp (lift (\<lambda>_. d) \<bind> (\<lambda>seed.
      fs_run (family seed) \<bind> (\<lambda>x. gap (select_first x) \<bind>
        (\<lambda>_. return (select_first x,select_second x))))) F s"
  by (simp add: wp_bind wp_lift fs_two_callbacks_wp[OF fixed] ext)

lemma fs_independent_seed_bound:
  assumes "\<And>seed. seed \<in> set_dist d \<Longrightarrow>
    wp (fs_two_callbacks (family seed) select_first select_second gap) F s \<le> epsilon"
  shows "dist_expect d (\<lambda>seed.
    wp (fs_two_callbacks (family seed) select_first select_second gap) F s) \<le> epsilon"
proof -
  have "wp (lift (\<lambda>_. d))
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some (seed,t) \<Rightarrow>
      wp (fs_two_callbacks (family seed) select_first select_second gap) F t) s \<le> epsilon"
    by (rule wp_le_const_on_support)
      (use assms in \<open>auto simp: lift.rep_eq lift_dist_def set_dist_dist_map\<close>)
  then show ?thesis by (simp add: wp_lift)
qed

subsection \<open>Exact repeated-call accounting and erasure\<close>

definition fs_two_callbacks_count where
  "fs_two_callbacks_count P select_first select_second gap =
    fs_count_run P \<bind> (\<lambda>(x,n). gap (select_first x) \<bind> (\<lambda>_.
      fs_count_run P \<bind> (\<lambda>(y,k). return ((select_first x,select_second y),n+k))))"

lemma fs_two_callbacks_exact_count_wp:
  assumes fixed: "fs_fixed P"
    and ext: "\<And>x. hash_extension_preserving (gap x)"
  shows "wp (fs_two_callbacks_count P select_first select_second gap) F s =
    wp (fs_count_run P \<bind> (\<lambda>(x,n). gap (select_first x) \<bind>
      (\<lambda>_. return ((select_first x,select_second x),2*n)))) F s"
proof -
  let ?Post = "\<lambda>out. case out of None \<Rightarrow> F None
    | Some ((xn,yk),u) \<Rightarrow>
        F (Some (((select_first (fst xn),select_second (fst yk)),snd xn+snd yk),u))"
  have eq: "wp (fs_count_run P \<bind> (\<lambda>xn.
      gap (select_first (fst xn)) \<bind> (\<lambda>_. fs_count_run P \<bind>
        (\<lambda>yk. return (xn,yk))))) ?Post s =
    wp (fs_count_run P \<bind> (\<lambda>xn.
      gap (select_first (fst xn)) \<bind> (\<lambda>_. return (xn,xn)))) ?Post s"
    using fs_two_replays_wp[where m="fs_count_run P" and f=id and select_second=id
      and gap="\<lambda>xn. gap (select_first (fst xn))" and F="?Post" and s=s,
      OF fs_fixed_count_replayable[OF fixed]]
    by (simp add: ext)
  show ?thesis using eq
    unfolding fs_two_callbacks_count_def
    by (simp add: wp_bind wp_return case_prod_unfold numeral_2_eq_2
      split: option.splits)
qed

lemma fs_count_run_bind_erases:
  "(fs_count_run P \<bind> (\<lambda>xn. tail (fst xn))) = fs_run P \<bind> tail"
  using arg_cong[OF fs_count_run_erases[of P], of "\<lambda>m. m \<bind> tail"]
  by (simp add: sm_bind_assoc split_def)

lemma fs_two_callbacks_count_erases:
  "(fs_two_callbacks_count P select_first select_second gap \<bind>
    (\<lambda>(pair,n). return pair)) = fs_two_callbacks P select_first select_second gap"
  unfolding fs_two_callbacks_count_def fs_two_callbacks_def fs_replay_callback_def
  by (simp only: fs_count_run_erases[symmetric] sm_bind_assoc split_def
    sm_bind_return_left fst_conv)

subsection \<open>Adaptive examples and explicit scope checks\<close>

definition fs_adaptive_pair where
  "fs_adaptive_pair key next =
    FS_Query key (\<lambda>y. FS_Query (next y) (\<lambda>z. FS_Return [y,z]))"

lemma fs_adaptive_pair_fixed:
  "fs_fixed (fs_adaptive_pair key next)"
  unfolding fs_adaptive_pair_def by (auto intro: fs_fixed.intros)

lemma fs_adaptive_pair_bound:
  "fs_query_bound 2 (fs_adaptive_pair key next)"
  unfolding fs_adaptive_pair_def numeral_2_eq_2 by (auto intro: fs_query_bound.intros)

lemma fs_adaptive_pair_count:
  "fs_count_run (fs_adaptive_pair key next) =
    (hash key \<bind> (\<lambda>y. hash (next y) \<bind> (\<lambda>z. return ([y,z],2))))"
  by (simp add: fs_adaptive_pair_def sm_bind_assoc numeral_2_eq_2)

lemma fs_adaptive_two_callbacks_four_calls:
  "wp (fs_two_callbacks_count (fs_adaptive_pair key next)
      hd last ro_record_staged_message) F s =
    wp (hash key \<bind> (\<lambda>y. hash (next y) \<bind> (\<lambda>z.
      ro_record_staged_message y \<bind> (\<lambda>_. return ((y,z),4))))) F s"
  using fs_two_callbacks_exact_count_wp[OF fs_adaptive_pair_fixed,
    where gap=ro_record_staged_message and select_first=hd and select_second=last and F=F and s=s]
  by (simp add: fs_record_extends fs_adaptive_pair_count sm_bind_assoc)

lemma fs_seed_program_two_callbacks:
  assumes fixed: "\<And>seed. fs_fixed (family seed)"
    and ext: "\<And>x. hash_extension_preserving (gap x)"
  shows "dist_expect d (\<lambda>seed.
      wp (fs_two_callbacks (family seed) select_first select_second gap) F s) =
    wp (fs_run (fs_sample_nat d family) \<bind> (\<lambda>x.
      gap (select_first x) \<bind> (\<lambda>_. return (select_first x,select_second x)))) F s"
  by (simp add: wp_bind fs_sample_nat_wp fs_two_callbacks_wp[OF fixed] ext)

lemma fs_seed_query_cap:
  assumes "\<And>seed. fs_query_bound q (family seed)"
  shows "fs_query_bound q (fs_sample_nat d family)"
  by (rule fs_sample_nat_bound[OF assms])

lemma fs_two_callbacks_actual_controls:
  assumes "fs_query_bound q P" "fs_fixed P"
  shows "controlled_ro_program q
      (trace_root_stage (fs_replay_pair_attacker P select_first select_second A))"
    and "\<And>i bs. controlled_ro_program q
      (trace_fri_root_stage (fs_replay_pair_attacker P select_first select_second A) i bs)"
  using fs_replay_callback_controlled[OF assms]
  unfolding fs_replay_pair_attacker_def by simp_all

lemma fs_retained_answer_replay_calls:
  "wp (fs_two_callbacks_count (FS_Query key (\<lambda>y. FS_Return [y,y]))
      hd last ro_record_staged_message) F s =
    wp (hash key \<bind> (\<lambda>y. ro_record_staged_message y \<bind>
      (\<lambda>_. return ((y,y),2)))) F s"
proof -
  have fixed: "fs_fixed (FS_Query key (\<lambda>y. FS_Return [y,y]))"
    by (auto intro: fs_fixed.intros)
  show ?thesis
    using fs_two_callbacks_exact_count_wp[OF fixed,
      where gap=ro_record_staged_message and select_first=hd and select_second=last and F=F and s=s]
    by (simp add: fs_record_extends fs_retained_answer_count sm_bind_assoc)
qed

lemma fs_two_callbacks_supported_call_bound:
  assumes bound: "fs_query_bound q P"
    and out: "Some ((pair,n),t) \<in>
      set_dist (execute (fs_two_callbacks_count P select_first select_second gap) s)"
  shows "n \<le> 2*q"
  using out unfolding fs_two_callbacks_count_def
  by (auto elim!: set_dist_bindE
      dest!: fs_supported_call_bound[OF bound]; arith)

text \<open>
  The count-erasure equation is unconditional. The successful two-replay count
  is exactly twice the original count for fixed programs, whereas the generic
  supported-call upper bound also covers private-sampling programs. Failed runs
  remain failed; no assertion that aborting runs return a count is made.

  The independent-seed results concern a distribution of fixed staged records,
  selected independently of the oracle. They do not provide an internal shared
  random store in the staged record. The full accepting-transcript bridge,
  arbitrary-private-sampling normalization, and global allowance f(Q) remain open.
\<close>

end

ML \<open>
  val fs_replay_checked = @{thms soundness.fs_fixed_extends
    soundness.fs_fixed_replayable
    soundness.fs_fixed_count_extends
    soundness.fs_fixed_count_replayable
    soundness.fs_fixed_exact_replay
    soundness.fs_wp_cong_on_support
    soundness.fs_replay_after_extension
    soundness.fs_two_replays_wp
    soundness.fs_throw_bind
    soundness.fs_fixed_controlled_cont
    soundness.fs_replay_callback_controlled
    soundness.fs_two_callbacks_wp
    soundness.fs_record_extends
    soundness.fs_two_actual_callbacks_wp
    soundness.fs_two_callback_allowances
    soundness.fs_replay_pair_actual_prefix
    soundness.fs_independent_seed_two_callbacks
    soundness.fs_independent_seed_bound
    soundness.fs_two_callbacks_exact_count_wp
    soundness.fs_count_run_bind_erases
    soundness.fs_two_callbacks_count_erases
    soundness.fs_adaptive_pair_fixed
    soundness.fs_adaptive_pair_bound
    soundness.fs_adaptive_pair_count
    soundness.fs_adaptive_two_callbacks_four_calls
    soundness.fs_seed_program_two_callbacks
    soundness.fs_seed_query_cap
    soundness.fs_two_callbacks_actual_controls
    soundness.fs_retained_answer_replay_calls
    soundness.fs_two_callbacks_supported_call_bound};
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then ()
    else error "Unexpected fixed-replay proof dependency") fs_replay_checked;
  writeln ("Fixed-replay checked conclusions: " ^ Int.toString (length fs_replay_checked));
\<close>

end
