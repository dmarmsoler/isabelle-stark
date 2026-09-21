theory Soundness_FRI_RO_Actual_Query_Obstruction_Reduction
  imports Soundness_FRI_RO_Actual_Query_Joint_Evidence
begin

context soundness
begin

lemma generic_fri_recorded_accepted_obstruction_reduction:
  fixes final_state :: "('f, 'a) protocol_channel_scheme"
  assumes partial:
      "generic_fri_partial_evidence low_degree candidate_table degree_bound
        roots challenges final_value query_idxs round_layers"
    and chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and authenticated:
      "generic_fri_recorded_chunks_authenticated roots query_idxs
        round_layers final_state"
    and candidate_bad: "\<not> low_degree candidate_table"
    and challenges_nonempty: "0 < length challenges"
    and query_bounds:
      "\<And>round_idx. round_idx < length query_idxs \<Longrightarrow>
        query_idxs ! round_idx < clength * scale"
    and eval_power: "clength * scale = 2 ^ N"
    and rounds_bound: "length challenges \<le> N"
  shows
    "generic_fri_sampled_query_candidate_evidence low_degree
       (Not \<circ> low_degree) candidate_table degree_bound roots challenges
       final_value query_idxs round_layers
       (generic_fri_sampled_assignment_layers candidate_table roots
         challenges final_value query_idxs round_layers) \<or>
     generic_fri_sampled_base_opening_conflict candidate_table roots
       challenges query_idxs round_layers \<or>
     partial_merkle_inconsistency_bad s (Some (result, final_state))"
proof (cases
    "generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers")
  case True
  from
    generic_fri_recorded_chain_assignment_conflict_imp_base_or_partial_merkle[
      OF chain authenticated True]
  show ?thesis by blast
next
  case False
  have sampled:
      "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
        degree_bound roots challenges final_value query_idxs round_layers
        (fri_canonical_domains (length challenges))
        (generic_fri_sampled_assignment_layers candidate_table roots
          challenges final_value query_idxs round_layers)"
    by (rule generic_fri_sampled_assignment_layer_chain_evidence[
          OF partial False challenges_nonempty query_bounds eval_power
            rounds_bound])
  have canonical:
      "generic_fri_canonical_sampled_layer_chain_evidence low_degree
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers
        (generic_fri_sampled_assignment_layers candidate_table roots
          challenges final_value query_idxs round_layers)"
    using sampled
    unfolding generic_fri_canonical_sampled_layer_chain_evidence_def .
  have bad: "(Not \<circ> low_degree) candidate_table"
    using candidate_bad by simp
  have
      "generic_fri_sampled_query_candidate_evidence low_degree
        (Not \<circ> low_degree) candidate_table degree_bound roots challenges
        final_value query_idxs round_layers
        (generic_fri_sampled_assignment_layers candidate_table roots
          challenges final_value query_idxs round_layers)"
    using canonical bad
    unfolding generic_fri_sampled_query_candidate_evidence_def
    by blast
  then show ?thesis by simp
qed





lemma generic_fri_recorded_accepted_obstruction_reduction_or_zero_round:
  fixes final_state :: "('f, 'a) protocol_channel_scheme"
  assumes partial:
      "generic_fri_partial_evidence low_degree candidate_table degree_bound
        roots challenges final_value query_idxs round_layers"
    and chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and authenticated:
      "generic_fri_recorded_chunks_authenticated roots query_idxs
        round_layers final_state"
    and candidate_bad: "\<not> low_degree candidate_table"
    and query_bounds:
      "\<And>round_idx. round_idx < length query_idxs \<Longrightarrow>
        query_idxs ! round_idx < clength * scale"
    and eval_power: "clength * scale = 2 ^ N"
    and rounds_bound: "length challenges \<le> N"
  shows
    "generic_fri_sampled_query_candidate_evidence low_degree
       (Not \<circ> low_degree) candidate_table degree_bound roots challenges
       final_value query_idxs round_layers
       (generic_fri_sampled_assignment_layers candidate_table roots
         challenges final_value query_idxs round_layers) \<or>
     generic_fri_sampled_base_opening_conflict candidate_table roots
       challenges query_idxs round_layers \<or>
     partial_merkle_inconsistency_bad s (Some (result, final_state)) \<or>
     (length challenges = 0 \<and>
       \<not> fri_final_constant_consistent candidate_table final_value)"
proof (cases
    "generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers")
  case True
  from
    generic_fri_recorded_chain_assignment_conflict_imp_base_or_partial_merkle[
      OF chain authenticated True]
  show ?thesis by blast
next
  case False
  show ?thesis
  proof (cases "0 < length challenges")
    case True
    have sampled:
        "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
          degree_bound roots challenges final_value query_idxs round_layers
          (fri_canonical_domains (length challenges))
          (generic_fri_sampled_assignment_layers candidate_table roots
            challenges final_value query_idxs round_layers)"
      by (rule generic_fri_sampled_assignment_layer_chain_evidence[
            OF partial False True query_bounds eval_power rounds_bound])
    have canonical:
        "generic_fri_canonical_sampled_layer_chain_evidence low_degree
          candidate_table degree_bound roots challenges final_value query_idxs
          round_layers
          (generic_fri_sampled_assignment_layers candidate_table roots
            challenges final_value query_idxs round_layers)"
      using sampled
      unfolding generic_fri_canonical_sampled_layer_chain_evidence_def .
    have bad: "(Not \<circ> low_degree) candidate_table"
      using candidate_bad by simp
    have
        "generic_fri_sampled_query_candidate_evidence low_degree
          (Not \<circ> low_degree) candidate_table degree_bound roots challenges
          final_value query_idxs round_layers
          (generic_fri_sampled_assignment_layers candidate_table roots
            challenges final_value query_idxs round_layers)"
      using canonical bad
      unfolding generic_fri_sampled_query_candidate_evidence_def
      by blast
    then show ?thesis by simp
  next
    case False
    then have challenges_empty: "length challenges = 0"
      by simp
    show ?thesis
    proof (cases "fri_final_constant_consistent candidate_table final_value")
      case True
      have sampled:
          "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
            degree_bound roots challenges final_value query_idxs round_layers
            (fri_canonical_domains (length challenges))
            (generic_fri_sampled_assignment_layers candidate_table roots
              challenges final_value query_idxs round_layers)"
        by (rule
            generic_fri_sampled_assignment_layer_chain_evidence_zero_round[
              OF partial challenges_empty True])
      have canonical:
          "generic_fri_canonical_sampled_layer_chain_evidence low_degree
            candidate_table degree_bound roots challenges final_value
            query_idxs round_layers
            (generic_fri_sampled_assignment_layers candidate_table roots
              challenges final_value query_idxs round_layers)"
        using sampled
        unfolding generic_fri_canonical_sampled_layer_chain_evidence_def .
      have bad: "(Not \<circ> low_degree) candidate_table"
        using candidate_bad by simp
      have
          "generic_fri_sampled_query_candidate_evidence low_degree
            (Not \<circ> low_degree) candidate_table degree_bound roots challenges
            final_value query_idxs round_layers
            (generic_fri_sampled_assignment_layers candidate_table roots
              challenges final_value query_idxs round_layers)"
        using canonical bad
        unfolding generic_fri_sampled_query_candidate_evidence_def
        by blast
      then show ?thesis by simp
    next
      case False
      then show ?thesis
        using challenges_empty by blast
    qed
  qed
qed
lemma
  ro_absorb_checked_staged_first_root_actual_query_first_not_low_degree_obstruction:
  fixes final_state :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and builder_out:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and verifier_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and clean: "\<not> hash_map_output_collision final_state"
    and candidate_bad:
      "\<not> trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
  shows
    "\<exists>f_fl f_final trace_round_layers.
      map fst f_fl = staged_trace_fri_challenges data \<and>
      map snd f_fl = staged_trace_fri_roots data \<and>
      (generic_fri_sampled_query_candidate_evidence trace_table_low_degree
         (Not \<circ> trace_table_low_degree)
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (clength - 1) (map snd f_fl) (map fst f_fl) f_final
         (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers
         (generic_fri_sampled_assignment_layers
           (first_trace_fri_root_prefix_first_table prefix prefix_state)
           (map snd f_fl) (map fst f_fl) f_final
           (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers) \<or>
       generic_fri_sampled_base_opening_conflict
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (map snd f_fl) (map fst f_fl)
         (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers \<or>
       partial_merkle_inconsistency_bad
         (verifier_state_from_adversary attacker_state
           (staged_proof_transcript data))
         (Some (results, final_state)))"
proof -
  from
    ro_absorb_checked_staged_first_root_actual_query_joint_fri_evidence[
      OF wf controlled nonempty builder_out verifier_out clean,
      where composition_table="[]"]
  obtain f_fl fl f_final final trace_round_layers
      composition_round_layers where
    trace_challenges_eq:
      "map fst f_fl = staged_trace_fri_challenges data"
    and trace_roots_eq:
      "map snd f_fl = staged_trace_fri_roots data"
    and composition_challenges_eq:
      "map fst fl = staged_composition_fri_challenges data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and f_fl_nonempty: "f_fl \<noteq> []"
    and trace_partial:
      "generic_fri_partial_evidence trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (clength - 1) (map snd f_fl) (map fst f_fl) f_final
        (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    and composition_partial:
      "generic_fri_partial_evidence
        (composition_table_low_degree (to_nat (staged_degree data))) []
        (to_nat (staged_degree data)) (map snd fl) (map fst fl) final
        (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    and trace_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd f_fl) (map fst f_fl) f_final
        (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    and composition_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd fl) (map fst fl) final
        (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    and trace_authenticated:
      "generic_fri_recorded_chunks_authenticated
        (map snd f_fl) (map (\<lambda>raw. index (to_nat raw)) raws)
        trace_round_layers final_state"
    and composition_authenticated:
      "generic_fri_recorded_chunks_authenticated
        (map snd fl) (map (\<lambda>raw. index (to_nat raw)) raws)
        composition_round_layers final_state"
    and raw_bound:
      "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
    .

  let ?query_idxs = "map (\<lambda>raw. index (to_nat raw)) raws"
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have query_bounds:
      "\<And>round_idx. round_idx < length ?query_idxs \<Longrightarrow>
        ?query_idxs ! round_idx < clength * scale"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length ?query_idxs"
    have raw_at: "raws ! round_idx \<in> set raws"
      using round_bound by simp
    show "?query_idxs ! round_idx < clength * scale"
      using raw_bound raw_at round_bound by simp
  qed
  have challenges_nonempty: "0 < length (map fst f_fl)"
    using f_fl_nonempty by simp
  have rounds_bound: "length (map fst f_fl) \<le> N"
  proof -
    have original_out:
        "Some (data, attacker_state) \<in>
          set_dist
            (execute (ro_checked_staged_transcript_program A)
              adversary_initial_state)"
      by (rule
          ro_checked_staged_transcript_program_with_first_root_projection_outcome[
            OF nonempty builder_out])
    have shape:
        "length (staged_trace_fri_roots data) = ceil_log clength"
      using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
      by simp
    have clength_bound: "clength \<le> clength * scale"
      using scale_pos by simp
    have ceil_bound: "ceil_log clength \<le> N"
      by (rule ceil_log_le_power)
        (use clength_bound eval_power in simp)
    have challenge_len: "length (map fst f_fl) = ceil_log clength"
    proof -
      have pair_lengths:
          "length (map fst f_fl) = length (map snd f_fl)"
        by simp
      show ?thesis
        using pair_lengths trace_roots_eq shape by simp
    qed
    show ?thesis
      using challenge_len ceil_bound by simp
  qed

  have obstruction:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
         (Not \<circ> trace_table_low_degree)
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (clength - 1) (map snd f_fl) (map fst f_fl) f_final
         ?query_idxs trace_round_layers
         (generic_fri_sampled_assignment_layers
           (first_trace_fri_root_prefix_first_table prefix prefix_state)
           (map snd f_fl) (map fst f_fl) f_final
           ?query_idxs trace_round_layers) \<or>
       generic_fri_sampled_base_opening_conflict
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (map snd f_fl) (map fst f_fl) ?query_idxs trace_round_layers \<or>
       partial_merkle_inconsistency_bad
         (verifier_state_from_adversary attacker_state
           (staged_proof_transcript data))
         (Some (results, final_state))"
    by (rule generic_fri_recorded_accepted_obstruction_reduction[
          OF trace_partial trace_chain trace_authenticated candidate_bad
            challenges_nonempty query_bounds eval_power rounds_bound])
  show ?thesis
    using trace_challenges_eq trace_roots_eq obstruction by blast
qed


lemma
  ro_absorb_checked_staged_first_root_actual_query_composition_not_low_degree_obstruction:
  fixes composition_table :: "'f list"
    and final_state :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and builder_out:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and verifier_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and clean: "\<not> hash_map_output_collision final_state"
    and candidate_bad:
      "\<not> composition_table_low_degree maxDegree composition_table"
  shows
    "\<exists>fl final composition_round_layers.
      map fst fl = staged_composition_fri_challenges data \<and>
      map snd fl = staged_composition_fri_roots data \<and>
      (generic_fri_sampled_query_candidate_evidence
         (composition_table_low_degree (to_nat (staged_degree data)))
         (Not \<circ>
           composition_table_low_degree (to_nat (staged_degree data)))
         composition_table (to_nat (staged_degree data))
         (map snd fl) (map fst fl) final
         (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers
         (generic_fri_sampled_assignment_layers composition_table
           (map snd fl) (map fst fl) final
           (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers) \<or>
       generic_fri_sampled_base_opening_conflict composition_table
         (map snd fl) (map fst fl)
         (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers \<or>
       partial_merkle_inconsistency_bad
         (verifier_state_from_adversary attacker_state
           (staged_proof_transcript data))
         (Some (results, final_state)) \<or>
       (length (map fst fl) = 0 \<and>
         \<not> fri_final_constant_consistent composition_table final))"
proof -
  from
    ro_absorb_checked_staged_first_root_actual_query_joint_fri_evidence[
      OF wf controlled nonempty builder_out verifier_out clean,
      where composition_table=composition_table]
  obtain f_fl fl f_final final trace_round_layers
      composition_round_layers where
    trace_challenges_eq:
      "map fst f_fl = staged_trace_fri_challenges data"
    and trace_roots_eq:
      "map snd f_fl = staged_trace_fri_roots data"
    and composition_challenges_eq:
      "map fst fl = staged_composition_fri_challenges data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and f_fl_nonempty: "f_fl \<noteq> []"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and trace_partial:
      "generic_fri_partial_evidence trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (clength - 1) (map snd f_fl) (map fst f_fl) f_final
        (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    and composition_partial:
      "generic_fri_partial_evidence
        (composition_table_low_degree (to_nat (staged_degree data)))
        composition_table (to_nat (staged_degree data))
        (map snd fl) (map fst fl) final
        (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    and trace_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd f_fl) (map fst f_fl) f_final
        (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    and composition_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd fl) (map fst fl) final
        (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    and trace_authenticated:
      "generic_fri_recorded_chunks_authenticated
        (map snd f_fl) (map (\<lambda>raw. index (to_nat raw)) raws)
        trace_round_layers final_state"
    and composition_authenticated:
      "generic_fri_recorded_chunks_authenticated
        (map snd fl) (map (\<lambda>raw. index (to_nat raw)) raws)
        composition_round_layers final_state"
    and raw_bound:
      "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
    .

  let ?query_idxs = "map (\<lambda>raw. index (to_nat raw)) raws"
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have query_bounds:
      "\<And>round_idx. round_idx < length ?query_idxs \<Longrightarrow>
        ?query_idxs ! round_idx < clength * scale"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length ?query_idxs"
    have raw_at: "raws ! round_idx \<in> set raws"
      using round_bound by simp
    show "?query_idxs ! round_idx < clength * scale"
      using raw_bound raw_at round_bound by simp
  qed
  have candidate_bad_current:
      "\<not> composition_table_low_degree (to_nat (staged_degree data))
        composition_table"
    by (rule composition_table_not_low_degree_mono[
          OF degree_bound candidate_bad])
  have rounds_bound: "length (map fst fl) \<le> N"
  proof -
    have original_out:
        "Some (data, attacker_state) \<in>
          set_dist
            (execute (ro_checked_staged_transcript_program A)
              adversary_initial_state)"
      by (rule
          ro_checked_staged_transcript_program_with_first_root_projection_outcome[
            OF nonempty builder_out])
    have shape:
        "length (staged_composition_fri_roots data) =
           ceil_log (to_nat (staged_degree data) + 1) \<and>
         ceil_log (to_nat (staged_degree data) + 1) \<le>
           ceil_log (maxDegree + 1)"
      using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
      by blast
    have max_degree_bound: "maxDegree + 1 \<le> clength * scale"
      using maxDegree_less_eval_domain by linarith
    have ceil_bound: "ceil_log (maxDegree + 1) \<le> N"
      by (rule ceil_log_le_power)
        (use max_degree_bound eval_power in simp)
    have challenge_len:
        "length (map fst fl) =
          ceil_log (to_nat (staged_degree data) + 1)"
    proof -
      have pair_lengths:
          "length (map fst fl) = length (map snd fl)"
        by simp
      show ?thesis
        using pair_lengths composition_roots_eq shape by simp
    qed
    show ?thesis
      using challenge_len shape ceil_bound by linarith
  qed

  have obstruction:
      "generic_fri_sampled_query_candidate_evidence
         (composition_table_low_degree (to_nat (staged_degree data)))
         (Not \<circ>
           composition_table_low_degree (to_nat (staged_degree data)))
         composition_table (to_nat (staged_degree data))
         (map snd fl) (map fst fl) final ?query_idxs
         composition_round_layers
         (generic_fri_sampled_assignment_layers composition_table
           (map snd fl) (map fst fl) final ?query_idxs
           composition_round_layers) \<or>
       generic_fri_sampled_base_opening_conflict composition_table
         (map snd fl) (map fst fl) ?query_idxs composition_round_layers \<or>
       partial_merkle_inconsistency_bad
         (verifier_state_from_adversary attacker_state
           (staged_proof_transcript data))
         (Some (results, final_state)) \<or>
       (length (map fst fl) = 0 \<and>
         \<not> fri_final_constant_consistent composition_table final)"
    by (rule
        generic_fri_recorded_accepted_obstruction_reduction_or_zero_round[
          OF composition_partial composition_chain composition_authenticated
            candidate_bad_current query_bounds eval_power rounds_bound])
  show ?thesis
    using composition_challenges_eq composition_roots_eq obstruction by blast
qed
end
end
