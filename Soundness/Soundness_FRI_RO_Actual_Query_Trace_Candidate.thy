theory Soundness_FRI_RO_Actual_Query_Trace_Candidate
  imports Soundness_FRI_RO_Actual_Query_Obstruction_Collapse
begin

text \<open>
  The first trace-FRI table, rather than the prover's unrestricted trace-root
  table, is the trace polynomial candidate used by the algebraic soundness
  argument.  Accepted authenticated openings transfer the actually queried
  trace values to this candidate.  Thus neither non-low-degree trace-root
  tables nor equality of the two complete conceptual tables is a bad event.
\<close>

context soundness
begin

definition
  ro_absorb_checked_staged_security_with_first_root_trace_candidate_ready
where
  "ro_absorb_checked_staged_security_with_first_root_trace_candidate_ready
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          first_trace_fri_root_prefix_base_agreement_query_lists
            prefix prefix_state)"


lemma
  ro_absorb_checked_staged_security_with_first_root_clean_trace_candidate_classification:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
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
    "ro_absorb_checked_staged_security_with_first_root_trace_candidate_ready
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
       out"
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
  have base_or_target:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          first_trace_fri_root_prefix_base_agreement_query_lists
            prefix prefix_state \<or>
       hash_map_new_output_hit
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
          prefix_state final_state"
    by (rule
        ro_absorb_checked_staged_first_root_actual_query_base_agreement_or_target[
          OF wf controlled nonempty builder_out verifier_out final_clean])
  then show ?thesis
  proof
    assume base:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        first_trace_fri_root_prefix_base_agreement_query_lists
          prefix prefix_state"
    show ?thesis
    proof (cases
        "trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state)")
      case True
      have ready:
          "ro_absorb_checked_staged_security_with_first_root_trace_candidate_ready
            out"
        unfolding out_eq full_eq
          ro_absorb_checked_staged_security_with_first_root_trace_candidate_ready_def
        using True base by simp
      then show ?thesis by simp
    next
      case False
      have first_event:
          "ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
            out"
        unfolding out_eq full_eq
          ro_absorb_checked_staged_security_with_first_root_first_not_low_degree_def
        using False by simp
      have reduced:
          "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
             out \<or>
           ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
             out"
        by (rule
            ro_absorb_checked_staged_security_with_first_root_clean_first_not_low_degree_obstruction_collapsed[
              OF wf controlled nonempty support first_event clean])
      then show ?thesis by simp
    qed
  next
    assume target:
      "hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state"
    have event:
        "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
          out"
      unfolding out_eq full_eq
        ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def
      using target by simp
    then show ?thesis by simp
  qed
qed


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_le_trace_candidate_union:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le>
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        (\<lambda>out.
          final_hash_collision_event out \<or>
          ro_absorb_checked_staged_security_with_first_root_trace_candidate_ready
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
            out)
        adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and accepted_out: "accepted out"
  show
      "final_hash_collision_event out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_candidate_ready
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
         out"
  proof (cases "final_hash_collision_event out")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis
      using
        ro_absorb_checked_staged_security_with_first_root_clean_trace_candidate_classification[
          OF wf controlled nonempty accepted_out support False]
      by simp
  qed
qed

end
end
