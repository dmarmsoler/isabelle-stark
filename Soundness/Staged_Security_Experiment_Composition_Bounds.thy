(*  Title:      Stark/Staged_Security_Experiment_Composition_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Bounds
  imports Staged_Security_Experiment_Composition_Tree_Output
begin

text \<open>
  Budget-level composition corollaries for the staged security experiment.

  This layer consumes the actual-alpha-prefix prequery accounting theorem and
  exposes the remaining composition side condition as the tree-output event
  only.  The tree-output event is still Merkle/candidate proof work; the
  alpha-key prequery accounting itself is derived from the current staged
  oracle-budget interface.
\<close>

context soundness
begin

lemma checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_tree_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and tree_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_tree_output_hit
        adversary_initial_state \<le> T"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      T"
proof -
  let ?P =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  have transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets
        [OF wf controlled])
  have prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le> ?P + T"
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_and_tree
        [OF wf controlled prefix_bound tree_bound])
  then show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_data_alpha_prefix_tree_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and data_tree_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A)
        adversary_initial_state \<le> T"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      T"
proof -
  have actual_tree_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_tree_output_hit
      adversary_initial_state \<le> T"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_tree_output_hit_bound_from_data_state
        [OF wf controlled data_tree_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_tree_and_budgets
        [OF wf controlled actual_tree_bound])
qed

end

end
