(* Title: Stark/FS_Replay_Allowance.thy
   License: BSD-3-Clause *)

theory FS_Replay_Allowance
  imports FS_Adaptive_Staged_Embedding
begin

section \<open>Allowance of the actual adaptive replay compiler\<close>

text \<open>Each actual callback replays the whole fixed program. Repeated cached
  oracle calls are still calls. This wellformed allocation gives every declared
  position its already proved all-state allowance Q and reserves maximum
  composition depth. Its total is an equality for this sufficient allocation,
  not a minimal allowance or an exact full-execution call count. Failure, shorter
  depth and programs using fewer than Q calls can consume less.

  Private normalization preserves the cap for each supported fixed program.
  The original producer has total cap Q; the compiled producer need not.
  No verifier, transcript, sampler, protocol or budget predicate is changed.\<close>

context soundness
begin

definition fs_replay_budgets :: "nat \<Rightarrow> staged_budgets" where
  "fs_replay_budgets Q = \<lparr>trace_root_budget=Q,
    trace_fri_budgets=replicate (ceil_log clength) Q,
    trace_final_budget=Q, degree_budget=Q,
    composition_fri_budgets=replicate (ceil_log (maxDegree+1)) Q,
    composition_final_budget=Q, query_opening_budgets=replicate rounds Q\<rparr>"

lemma fs_replay_budgets_wellformed:
  "staged_budget_wellformed (fs_replay_budgets Q)"
  by (simp add: staged_budget_wellformed_def fs_replay_budgets_def)

lemma fs_replay_total_allowance:
  "staged_attacker_query_budget (fs_replay_budgets Q) =
    (ceil_log clength + ceil_log (maxDegree+1) + rounds + 4)*Q"
  by (simp add: staged_attacker_query_budget_def fs_replay_budgets_def
    sum_list_replicate algebra_simps)

lemma fs_compile_replay_controlled:
  assumes bound: "fs_query_bound Q P" and fixed: "fs_fixed P"
  shows "staged_adversary_controlled (fs_replay_budgets Q) (fs_compile_replay A P)"
  unfolding staged_adversary_controlled_def fs_replay_budgets_def
  by (auto intro: fs_compile_replay_callbacks_controlled[OF bound fixed])

lemma fs_normalized_replay_controlled:
  assumes bound: "fs_query_bound Q P" and member: "T\<in>set_dist(fs_normalize P)"
  shows "staged_adversary_controlled (fs_replay_budgets Q) (fs_compile_replay A T)"
  by (rule fs_compile_replay_controlled)
    (use member in \<open>auto intro: fs_normalize_bound[OF bound] fs_normalize_fixed\<close>)

end

ML \<open>
  List.app (fn th =>
    if null(Thm.hyps_of th) andalso null(Thm_Deps.all_oracles [th])
    then () else error "Unexpected replay allowance dependency")
    @{thms soundness.fs_replay_budgets_wellformed soundness.fs_replay_total_allowance
      soundness.fs_compile_replay_controlled soundness.fs_normalized_replay_controlled};
\<close>
end
