(* Title: Stark/FS_Staged_Allowance_Audit.thy
   License: BSD-3-Clause *)

theory FS_Staged_Allowance_Audit
  imports FS_Adversary_Model
begin

section \<open>Local obstacles to a cost-preserving staged embedding\<close>

text \<open>
  These are interface and accounting facts, not an impossibility theorem for
  every acceptance-dominating reduction. A maximum over execution paths does
  not commute with a sum of fixed per-slot allowances. Zero-allowance controlled
  programs cannot observe cached answers, even on states where the key is
  present. Thus free replay from the oracle map is not a valid justification
  for preserving a conventional attacker's total query budget.
  The two-output oracle program in the imported model is a local retained-state
  example, not an authenticated accepting STARK execution.
\<close>

subsection \<open>Joint path costs and fixed coordinate envelopes\<close>

lemma fs_branch_allocation_total:
  "sum_list (if b then [Q,0] else [0,Q]) = (Q::nat)"
  by simp

lemma fs_branch_static_envelopes:
  fixes Q a b :: nat
  assumes "\<forall>c. (if c then Q else 0) \<le> a"
    "\<forall>c. (if c then 0 else Q) \<le> b"
  shows "2*Q \<le> a+b"
proof -
  have "Q \<le> a" using assms(1)[rule_format, of True] by simp
  moreover have "Q \<le> b" using assms(2)[rule_format, of False] by simp
  ultimately show ?thesis by arith
qed


context soundness
begin

subsection \<open>Zero allowance cannot recover cached oracle information\<close>

lemma controlled_zero_observation:
  assumes "controlled_ro_program q m" "q=0"
  shows "wp m (\<lambda>out. F (map_option fst out)) s =
    wp m (\<lambda>out. F (map_option fst out)) t"
  using assms
proof (induction arbitrary: F s t rule: controlled_ro_program.induct)
  case (Return x)
  then show ?case by (simp add: wpsimps)
next
  case Fail
  then show ?case by (simp add: wpsimps)
next
  case (Sample d)
  then show ?case by (simp add: wpsimps)
next
  case (Query q k key)
  then show ?case by simp
next
  case (Bind q m r k)
  have q0: "q=0" and r0: "r=0" using Bind.prems by auto
  have cont: "wp (k x) (\<lambda>out. F (map_option fst out)) u =
      wp (k x) (\<lambda>out. F (map_option fst out)) t" for x u
    using Bind.IH(2) r0 by blast
  let ?G = "\<lambda>z. case z of None \<Rightarrow> F None
    | Some x \<Rightarrow> wp (k x) (\<lambda>out. F (map_option fst out)) t"
  have eq: "wp m (\<lambda>out. ?G (map_option fst out)) s =
      wp m (\<lambda>out. ?G (map_option fst out)) t"
    using Bind.IH(1)[OF q0] .
  have post: "(\<lambda>out. case out of None \<Rightarrow> F None
      | Some (x,u) \<Rightarrow> wp (k x) (\<lambda>out. F (map_option fst out)) u) =
      (\<lambda>out. ?G (map_option fst out))"
  proof (rule ext)
    fix out
    show "(case out of None \<Rightarrow> F None
        | Some (x,u) \<Rightarrow> wp (k x) (\<lambda>out. F (map_option fst out)) u) =
      ?G (map_option fst out)"
    proof (cases out)
      case None
      then show ?thesis by simp
    next
      case (Some xu)
      obtain x u where xu: "xu=(x,u)" by (cases xu) simp
      show ?thesis using cont[of x u] by (simp only: Some xu option.map option.case prod.case fst_conv)
    qed
  qed
  show ?case by (simp only: wp_bind option.map post) (rule eq)
next
  case (Weaken q m r)
  have "q=0" using Weaken.hyps(2) Weaken.prems by simp
  then show ?case by (rule Weaken.IH)
qed

lemma controlled_zero_cannot_recover_cached:
  fixes m :: "('f, 'f protocol_channel) state_monad"
  assumes zero: "controlled_ro_program 0 m"
  shows "\<not> (\<forall>s y. fmlookup (HashMap s) key = Some y \<longrightarrow>
    wp m (\<lambda>out. if map_option fst out = Some y then 1 else 0) s = 1)"
proof
  assume recovery: "\<forall>s y. fmlookup (HashMap s) key = Some y \<longrightarrow>
    wp m (\<lambda>out. if map_option fst out = Some y then 1 else 0) s = 1"
  let ?s = "adversary_initial_state\<lparr>HashMap := fmupd key 0 fmempty\<rparr>"
  let ?t = "adversary_initial_state\<lparr>HashMap := fmupd key 1 fmempty\<rparr>"
  have p0: "wp m (\<lambda>out. if map_option fst out = Some 0 then 1 else 0) ?s = 1"
    using recovery by simp
  have p1: "wp m (\<lambda>out. if map_option fst out = Some 1 then 1 else 0) ?t = 1"
    using recovery by simp
  have zero_at_t: "wp m (\<lambda>out. if map_option fst out = Some 0 then 1 else 0) ?t = 1"
    using controlled_zero_observation[OF zero refl, of
      "\<lambda>z. if z=Some 0 then 1 else 0" ?s ?t] p0 by simp
  have disjoint: "wp m (\<lambda>out. if map_option fst out = Some 0 then 1 else 0) ?t +
    wp m (\<lambda>out. if map_option fst out = Some 1 then 1 else 0) ?t \<le> 1"
  proof -
    have sum: "wp m (\<lambda>out. if map_option fst out=Some 0 then 1 else 0) ?t +
        wp m (\<lambda>out. if map_option fst out=Some 1 then 1 else 0) ?t =
        wp m (\<lambda>out. (if map_option fst out=Some 0 then 1 else 0) +
          (if map_option fst out=Some 1 then 1 else 0)) ?t"
      by (simp add: wp_def dist_expect_def sum.distrib algebra_simps)
    show ?thesis unfolding sum
      by (rule wp_le_const_on_support) auto
  qed
  show False using disjoint zero_at_t p1 by simp
qed

lemma hash_has_no_zero_controlled_allowance:
  "\<not> controlled_ro_program 0 (hash key :: ('f, 'f protocol_channel) state_monad)"
proof
  assume h: "controlled_ro_program 0 (hash key :: ('f, 'f protocol_channel) state_monad)"
  have recovery: "\<forall>s y. fmlookup (HashMap s) key = Some y \<longrightarrow>
    wp (hash key) (\<lambda>out. if map_option fst out = Some y then 1 else 0) s = 1"
    by (simp add: wp_hash hash_dist_def option_default_dist_def)
  show False using controlled_zero_cannot_recover_cached[OF h] recovery by blast
qed


end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then writeln ("FS interface checked: " ^ fst (Thm.get_name_hint th))
    else error "Unexpected FS interface proof dependency")
    @{thms fs_all_paths_bounded fs_branch_allocation_total fs_branch_static_envelopes
      soundness.fs_run_controlled soundness.fs_count_run_erases
      soundness.fs_supported_call_bound soundness.fs_run_admissible
      soundness.fs_repeated_query_count soundness.fs_query_bound_weaken
      soundness.fs_retained_answer_one_call soundness.fs_retained_answer_count
      soundness.controlled_zero_observation soundness.controlled_zero_cannot_recover_cached
      soundness.hash_has_no_zero_controlled_allowance soundness.fs_sample_nat_bound
      soundness.fs_sample_nat_wp soundness.staged_fs_verifier_factorization};
\<close>

end
