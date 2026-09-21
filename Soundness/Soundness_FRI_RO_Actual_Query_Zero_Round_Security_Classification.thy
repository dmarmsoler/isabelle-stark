(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Zero_Round_Security_Classification.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Zero_Round_Security_Classification
  imports Soundness_FRI_RO_Actual_Query_Zero_Round_Prequery_Bound
begin

text \<open>
  Security-experiment classification for the zero trace-FRI-round branch.
  The trace root is fixed by its domain-separated absorption before the
  remaining header and query challenges.  This layer retains partial openings:
  it classifies accepted executions without reconstructing a complete table.
\<close>

context soundness
begin


definition
  ro_absorb_checked_staged_security_zero_round_trace_low_degree
where
  "ro_absorb_checked_staged_security_zero_round_trace_low_degree out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        trace_table_low_degree
          (ro_actual_query_zero_round_trace_table data prefix_state))"

lemma
  ro_absorb_checked_staged_security_clean_zero_round_trace_classification:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and accepted_out: "accepted out"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and clean: "\<not> final_hash_collision_event out"
  shows
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_zero_round_bad_query_lists out \<or>
     ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit out \<or>
     ro_absorb_checked_staged_security_zero_round_trace_low_degree out"
proof -
  from accepted_out obtain full where out_eq: "out = Some full"
    unfolding accepted_def by (cases out) auto
  obtain prefix prefix_state data query_start raws query_states
      attacker_state result final_state where
    full_eq:
      "full =
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state)"
    by (cases full) (auto split: prod.splits)
  have outcome:
      "Some
          (((((prefix, prefix_state), data, query_start, raws, query_states),
              attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    using support out_eq full_eq by simp
  from
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_outcomeE[
      OF outcome]
  have builder_out:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and verifier_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    by blast+
  have final_clean: "\<not> hash_map_output_collision final_state"
    using clean
    unfolding out_eq full_eq final_hash_collision_event_def
    by simp
  from ro_checked_staged_transcript_program_with_first_root_zero_fields[
      OF zero wf controlled builder_out]
  obtain fr where
    prefix_eq: "prefix = (fr, [], fr)"
    and trace_root_eq: "staged_trace_root data = fr"
    and prefix_query_ext: "prefix_state \<le> query_start"
    and query_attacker_ext: "query_start \<le> attacker_state"
    by blast
  have prefix_attacker_ext: "prefix_state \<le> attacker_state"
    by (rule hash_ext_trans[OF prefix_query_ext query_attacker_ext])
  have attacker_verifier_ext:
      "attacker_state \<le>
        verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
    by (rule hash_extends_verifier_state_from_adversary_right)
      (rule hash_ext_refl)
  have verifier_preserving: "hash_extension_preserving ro_verify_monad"
    by (rule hash_target_program_extension)
      (rule hash_target_program_ro_verify_monad)
  have verifier_final_ext:
      "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data) \<le> final_state"
    using verifier_preserving verifier_out
    unfolding hash_extension_preserving_def by blast  have prefix_final_ext: "prefix_state \<le> final_state"
    by (rule hash_ext_trans[OF prefix_attacker_ext])
      (rule hash_ext_trans[OF attacker_verifier_ext verifier_final_ext])
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_final_ext])
    with final_clean show False by contradiction
  qed
  have agreement_or_target:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_actual_query_zero_round_trace_query_lists data prefix_state \<or>
       hash_map_new_output_hit
         (ro_actual_query_zero_round_trace_merkle_targets data prefix_state)
         prefix_state final_state"
    by (rule
      ro_absorb_checked_staged_zero_round_actual_query_agreement_or_target[
        OF zero wf controlled builder_out verifier_out final_clean])
  then show ?thesis  proof
    assume agreement:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_actual_query_zero_round_trace_query_lists data prefix_state"
    show ?thesis
    proof (cases
        "trace_table_low_degree
          (ro_actual_query_zero_round_trace_table data prefix_state)")
      case True
      have
        "ro_absorb_checked_staged_security_zero_round_trace_low_degree out"
        using True
        unfolding out_eq full_eq
          ro_absorb_checked_staged_security_zero_round_trace_low_degree_def
        by simp
      then show ?thesis by simp
    next
      case False
      have bad_member:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_actual_query_zero_round_bad_query_lists
              prefix prefix_state (ro_query_head_data data) query_start"
        using agreement False
        unfolding ro_actual_query_zero_round_bad_query_lists_def
          ro_actual_query_zero_round_trace_query_lists_def
          ro_actual_query_zero_round_trace_indices_def
          ro_actual_query_zero_round_trace_table_def
          ro_query_head_data_def
        by simp
      have
        "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
          ro_actual_query_zero_round_bad_query_lists out"
        using bad_member
        unfolding out_eq full_eq
          ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
          ro_query_head_dependent_actual_query_index_list_hit_def
        by simp
      then show ?thesis by simp
    qed
  next
    assume target:
      "hash_map_new_output_hit
        (ro_actual_query_zero_round_trace_merkle_targets data prefix_state)
        prefix_state final_state"
    have target':
        "hash_map_new_output_hit
          (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
          prefix_state final_state"
      using target prefix_eq trace_root_eq prefix_clean
      unfolding ro_actual_query_zero_round_trace_merkle_targets_def
        ro_zero_round_first_root_prefix_merkle_targets_def
      by simp
    have
      "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit
        out"
      using target'
      unfolding out_eq full_eq
        ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit_def
      by simp
    then show ?thesis by simp
  qed
qed


lemma
  wp_ro_absorb_checked_staged_security_zero_round_bad_actual_query_bound:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
          ro_actual_query_zero_round_bad_query_lists)
        adversary_initial_state
      \<le> ro_checked_staged_zero_round_bad_actual_query_error budgets"
  by (rule order_trans[
        OF
          wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
          wp_ro_checked_staged_zero_round_bad_actual_query_bound[
            OF zero wf controlled]])

end
end
