(* Title: Stark/FS_Probability_Accounting.thy
   License: BSD-3-Clause *)

theory FS_Probability_Accounting
  imports FS_Replay_Allowance Staged_Security_Experiment_RO_Verifier_Budgets
begin

section \<open>Direct Fiat--Shamir experiment accounting\<close>

text \<open>The producer runs once in the conventional experiment. Its output may
  depend on every prior oracle answer: the verifier continuation bounds below
  are uniform in that output. These are probability-accounting bounds, not
  smaller all-state allowances for the unchanged staged replay compiler.\<close>

context soundness
begin

definition fs_direct_hash_budget :: "nat \<Rightarrow> nat" where
  "fs_direct_hash_budget Q = Q + ro_verifier_hash_query_budget"

lemma fs_direct_range_budget:
  assumes "fs_query_bound Q P"
  shows "hash_range_budget (fs_direct_hash_budget Q) (fs_security_experiment P)"
  unfolding fs_direct_hash_budget_def fs_security_experiment_def
  by (rule hash_range_budget_bind)
    (rule controlled_ro_program_range[OF fs_run_controlled[OF assms]],
     rule hash_range_budget_ro_verifier_after_adversary)

lemma fs_direct_collision_budget:
  assumes "fs_query_bound Q P"
  shows "hash_collision_budget (fs_direct_hash_budget Q) (fs_security_experiment P)"
  unfolding fs_direct_hash_budget_def fs_security_experiment_def
  by (rule hash_collision_budget_bind)
    (rule controlled_ro_program_range[OF fs_run_controlled[OF assms]],
     rule controlled_ro_program_collision[OF fs_run_controlled[OF assms]],
     rule hash_range_budget_ro_verifier_after_adversary,
     rule hash_collision_budget_ro_verifier_after_adversary)

lemma fs_direct_target_program:
  assumes "fs_query_bound Q P"
  shows "hash_target_program B (fs_direct_hash_budget Q) (fs_security_experiment P)"
  unfolding fs_direct_hash_budget_def fs_security_experiment_def
  by (rule hash_target_program_bind)
    (rule controlled_ro_program_target[OF fs_run_controlled[OF assms]],
     rule hash_target_program_ro_verifier_after_adversary)

lemma fs_direct_new_collision:
  assumes "fs_query_bound Q P"
  shows "wp_event (fs_security_experiment P)
    (hash_new_collision_event adversary_initial_state) adversary_initial_state \<le>
      hash_collision_budget_value 0 (fs_direct_hash_budget Q)"
proof -
  have at_state:
    "wp_event (fs_security_experiment P)
      (hash_new_collision_event adversary_initial_state) adversary_initial_state \<le>
      hash_collision_budget_value (card(hash_map_output_values adversary_initial_state))
        (fs_direct_hash_budget Q)"
    using fs_direct_collision_budget[OF assms, unfolded hash_collision_budget_def, rule_format,
      of adversary_initial_state] adversary_initial_state_no_output_collision by blast
  show ?thesis using at_state by simp
qed

lemma fs_direct_fixed_target:
  assumes "fs_query_bound Q P"
  shows "wp_event (fs_security_experiment P)
    (hash_new_output_hit_event B adversary_initial_state) adversary_initial_state \<le>
      hash_target_budget_value B (fs_direct_hash_budget Q)"
  using fs_direct_target_program[OF assms]
  unfolding hash_target_program_def hash_target_budget_def by blast

end
end

