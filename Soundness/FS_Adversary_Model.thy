(* Title: Stark/FS_Adversary_Model.thy
   License: BSD-3-Clause *)

theory FS_Adversary_Model
  imports Controlled_RO Staged_Security_Experiment_RO_Checked
begin

section \<open>Query-bounded full-transcript random-oracle computations\<close>

text \<open>
  This is a classical, terminating oracle-program model over the existing
  finite-support probability semantics. Query and private-sampling continuations
  may retain all earlier answers and randomness; there is no protocol-stage
  partition. Each query constructor costs one, including cached repetitions.
  The path relation includes abort paths and overapproximates oracle support.
  Counting execution records successful counts and erases to the same monad,
  preserving failure as well.

  For full-transcript results, private choices use field lists. Natural private
  choices embed by list length, with an exact weakest-precondition identity
  below. No new oracle, verifier, locale premise or public soundness premise is
  introduced. This model does not add quantum queries or countably supported
  computations to the underlying probability infrastructure.
\<close>

datatype ('f, 'a) fs_program =
    FS_Return 'a
  | FS_Fail
  | FS_Query "'f protocol_hash_input" "'f \<Rightarrow> ('f, 'a) fs_program"
  | FS_Sample "'a dist" "'a \<Rightarrow> ('f, 'a) fs_program"

inductive fs_query_bound :: "nat \<Rightarrow> ('f, 'a) fs_program \<Rightarrow> bool"
where
  Return: "fs_query_bound q (FS_Return x)"
| Fail: "fs_query_bound q FS_Fail"
| Query: "(\<And>y. fs_query_bound q (k y)) \<Longrightarrow>
    fs_query_bound (Suc q) (FS_Query key k)"
| Sample: "(\<And>i. fs_query_bound q (k i)) \<Longrightarrow>
    fs_query_bound q (FS_Sample d k)"


inductive fs_path_count :: "('f, 'a) fs_program \<Rightarrow> nat \<Rightarrow> bool"
where
  Return: "fs_path_count (FS_Return x) 0"
| Fail: "fs_path_count FS_Fail 0"
| Query: "fs_path_count (k y) n \<Longrightarrow>
    fs_path_count (FS_Query key k) (Suc n)"
| Sample: "i \<in> set_dist d \<Longrightarrow> fs_path_count (k i) n \<Longrightarrow>
    fs_path_count (FS_Sample d k) n"

lemma fs_all_paths_bounded:
  assumes "fs_query_bound q P" "fs_path_count P n"
  shows "n \<le> q"
  using assms
  by (induction arbitrary: n rule: fs_query_bound.induct)
    (auto elim: fs_path_count.cases)

context soundness
begin

primrec fs_run :: "('f, 'a) fs_program \<Rightarrow> ('a, 'f protocol_channel) state_monad"
where
  "fs_run (FS_Return x) = return x"
| "fs_run FS_Fail = throw"
| "fs_run (FS_Query key k) = hash key \<bind> (\<lambda>y. fs_run (k y))"
| "fs_run (FS_Sample d k) = lift (\<lambda>_. d) \<bind> (\<lambda>i. fs_run (k i))"

lemma fs_run_controlled:
  assumes "fs_query_bound q P"
  shows "controlled_ro_program q (fs_run P)"
  using assms
proof (induction rule: fs_query_bound.induct)
  case (Return q x)
  then show ?case by (auto intro: controlled_ro_program.Weaken)
next
  case (Fail q)
  then show ?case by (auto intro: controlled_ro_program.Weaken)
next
  case (Query q k key)
  then show ?case by auto
next
  case (Sample q k d)
  have "controlled_ro_program (0+q)
    (lift (\<lambda>_. d) \<bind> (\<lambda>i. fs_run (k i)))"
    by (rule controlled_ro_program.Bind) (use Sample.IH in auto)
  then show ?case by simp
qed


primrec fs_count_run ::
  "('f, 'a) fs_program \<Rightarrow> ('a \<times> nat, 'f protocol_channel) state_monad"
where
  "fs_count_run (FS_Return x) = return (x,0)"
| "fs_count_run FS_Fail = throw"
| "fs_count_run (FS_Query key k) =
    hash key \<bind> (\<lambda>y. fs_count_run (k y) \<bind>
      (\<lambda>(x,n). return (x,Suc n)))"
| "fs_count_run (FS_Sample d k) =
    lift (\<lambda>_. d) \<bind> (\<lambda>i. fs_count_run (k i))"

lemma fs_count_run_erases:
  "fs_count_run P \<bind> (\<lambda>(x,n). return x) = fs_run P"
  apply (induction P)
  apply (simp_all add: sm_bind_assoc split_def)
  apply (rule execute_inject[THEN iffD1], rule ext, rule dist_inject[THEN iffD1])
  apply (simp only: sm_bind.rep_eq throw.rep_eq dist_throw_def
    dist_bind.rep_eq dist_delta_dist o_def)
  apply (subst map_bind_delta_left)
  by (auto simp: bind_cont_map_def delta_map_def)

lemma fs_supported_call_bound:
  assumes "fs_query_bound q P"
    "Some ((x,n),t) \<in> set_dist (execute (fs_count_run P) s)"
  shows "n \<le> q"
  using assms
  by (induction arbitrary: x n t s rule: fs_query_bound.induct)
    (auto simp: throw_no_outcome elim!: set_dist_bindE)

lemma fs_run_admissible:
  assumes "fs_query_bound q P"
  shows "admissible_adversary q (fs_run P)"
  using controlled_ro_program_admissible[OF fs_run_controlled[OF assms]]
  unfolding admissible_adversary_def controlled_ro_admissible_def by simp

lemma fs_repeated_query_count:
  "fs_count_run (FS_Query key (\<lambda>y. FS_Query key (\<lambda>z. FS_Return [y,z]))) =
    (hash key \<bind> (\<lambda>y. hash key \<bind> (\<lambda>z. return ([y,z],2))))"
  by (simp add: sm_bind_assoc numeral_2_eq_2)


lemma fs_retained_answer_one_call:
  "fs_query_bound 1 (FS_Query key (\<lambda>y. FS_Return [y,y]))"
  unfolding One_nat_def
  by (rule fs_query_bound.Query) (rule fs_query_bound.Return)

lemma fs_retained_answer_count:
  "fs_count_run (FS_Query key (\<lambda>y. FS_Return [y,y])) =
    (hash key \<bind> (\<lambda>y. return ([y,y],1)))"
  by (simp add: sm_bind_assoc)

lemma fs_query_bound_weaken:
  assumes "fs_query_bound q P" "q \<le> r"
  shows "fs_query_bound r P"
  using assms
  apply (induction arbitrary: r rule: fs_query_bound.induct)
  apply (auto intro: fs_query_bound.intros)
  subgoal for q k key r
    by (cases r) (auto intro: fs_query_bound.Query)
  done


subsection \<open>Private natural choices and the unchanged final verifier\<close>

definition fs_sample_nat ::
  "nat dist \<Rightarrow> (nat \<Rightarrow> ('f, 'f list) fs_program) \<Rightarrow>
    ('f, 'f list) fs_program"
where
  "fs_sample_nat d k = FS_Sample (dist_map (\<lambda>n. replicate n 0) d)
    (\<lambda>xs. k (length xs))"

lemma fs_sample_nat_bound:
  assumes "\<And>n. fs_query_bound q (k n)"
  shows "fs_query_bound q (fs_sample_nat d k)"
  unfolding fs_sample_nat_def by (auto intro: fs_query_bound.Sample assms)

lemma fs_sample_nat_wp:
  "wp (fs_run (fs_sample_nat d k)) F s =
    dist_expect d (\<lambda>n. wp (fs_run (k n)) F s)"
  by (simp add: fs_sample_nat_def wp_bind wp_lift dist_expect_map)

definition fs_verify_after ::
  "'f semantic_adversary \<Rightarrow> (unit list, 'f protocol_channel) state_monad"
where
  "fs_verify_after A = A \<bind> (\<lambda>tr.
    verifier_state_transfer tr \<bind> (\<lambda>_. ro_verify_monad))"

lemma staged_fs_verifier_factorization:
  "ro_absorb_checked_staged_security_experiment A =
    fs_verify_after (ro_checked_staged_transcript_program A \<bind>
      (\<lambda>data. return (staged_proof_transcript data)))"
  by (simp add: ro_absorb_checked_staged_security_experiment_def
    fs_verify_after_def verifier_state_transfer_def sm_bind_assoc)

definition fs_security_experiment ::
  "('f, 'f list) fs_program \<Rightarrow> (unit list, 'f protocol_channel) state_monad"
where
  "fs_security_experiment P = fs_run P \<bind> (\<lambda>tr.
    verifier_state_transfer tr \<bind> (\<lambda>_. ro_verify_monad))"

definition fs_acceptance_probability :: "('f, 'f list) fs_program \<Rightarrow> prob"
where
  "fs_acceptance_probability P = wp_event (fs_security_experiment P)
    (\<lambda>out. \<not> Option.is_none out) adversary_initial_state"


text \<open>
  The factorization above identifies the shared final verifier. The later
  \<^verbatim>\<open>FS_Adaptive_Staged_Embedding\<close> theory proves acceptance transport for adaptive
  producers, including private randomness. \<^verbatim>\<open>FS_Replay_Allowance\<close> supplies the
  replay compiler's sufficient declared allowance. That allowance is not the
  original producer's query count; subsequent accounting theories distinguish
  operational replay costs from charges in the acceptance-probability bound.
\<close>

end
end
