(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Zero_Round_Prequery_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Zero_Round_Prequery_Bound
  imports Soundness_FRI_RO_Actual_Query_Zero_Round_Prefix_Target_Bound
begin

text \<open>
  Closed prequery accounting for the zero trace-FRI branch.  The query family
  is fixed by the absorbed trace root and verifier header; sampled partial
  openings are related to that prefix table only through the explicit Merkle
  target event.
\<close>

context soundness
begin

lemma zero_round_prequery_bad_imp_budgeted_relation_transition:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and prequery:
      "ro_query_head_dependent_query_start_prequery_hit
        ro_actual_query_zero_round_bad_query_lists
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values attacker_state"
    and no_merkle:
      "\<not> hash_map_new_output_hit
        (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
        prefix_state attacker_state"
  shows
    "hash_state_relation_transition
      (zero_round_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have outcome_props:
    "length raws = rounds \<and>
      length query_states = rounds \<and>
      length (staged_query_chunks data) = rounds \<and>
      query_start \<le> attacker_state \<and>
      (\<forall>j < rounds.
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raws ! j))"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled outcome])
  have witness_out:
    "Some ((data, query_start, raws, query_states), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_query_witnesses A)
          adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_witnesses_projection_outcome_all_rounds[
        OF outcome])
  have witness_props:
    "length raws = rounds \<and>
      length query_states = rounds \<and>
      length (staged_query_chunks data) = rounds \<and>
      query_start \<le> attacker_state \<and>
      PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
      (\<forall>j < rounds.
        query_states ! j \<le> attacker_state \<and>
        PQueryCounter (query_states ! j) =
          PQueryCounter query_start + j \<and>
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raws ! j) \<and>
        verifier_query_round_chunk
          (index (to_nat (raws ! j)))
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)) \<and>
      (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
    by (rule
      ro_checked_staged_transcript_program_with_query_witnesses_outcome[
        OF wf controlled witness_out])
  have prequery_props:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_actual_query_zero_round_bad_query_lists
          prefix prefix_state (ro_query_head_data data) query_start \<and>
      (\<exists>j < rounds.
        fmlookup (HashMap query_start)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raws ! j))"
    using prequery
    unfolding ro_query_head_dependent_query_start_prequery_hit_def
    by simp
  then obtain j where
    raws_in:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_actual_query_zero_round_bad_query_lists
          prefix prefix_state (ro_query_head_data data) query_start"
    and j_bound: "j < rounds"
    and lookup_start:
      "fmlookup (HashMap query_start)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raws ! j)"
    by blast
  from ro_checked_staged_transcript_program_with_first_root_zero_fields[
      OF zero wf controlled outcome]
  obtain fr where zero_fields:
    "prefix = (fr, [], fr) \<and>
      staged_trace_root data = fr \<and>
      staged_trace_fri_roots data = [] \<and>
      staged_trace_fri_challenges data = [] \<and>
      prefix_state \<le> query_start \<and>
      query_start \<le> attacker_state \<and>
      PQueryCounter query_start = 0"
    by blast
  have prefix_query: "prefix_state \<le> query_start"
    using zero_fields by blast
  have query_attacker: "query_start \<le> attacker_state"
    using zero_fields by blast
  have prefix_le: "prefix_state \<le> attacker_state"
    by (rule hash_ext_trans[OF prefix_query query_attacker])
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision attacker_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_le])
    with clean show False by contradiction
  qed
  have no_merkle_actual:
    "\<not> hash_map_new_output_hit
      (ro_actual_query_zero_round_trace_merkle_targets data prefix_state)
      prefix_state attacker_state"
    using no_merkle prefix_clean zero_fields
    unfolding ro_zero_round_first_root_prefix_merkle_targets_def
      ro_actual_query_zero_round_trace_merkle_targets_def
    by simp  from ro_checked_staged_transcript_zero_round_header_query_prefix_chain[
      OF zero wf controlled outcome clean j_bound]
  obtain header_fr where header_props:
    "prefix = (header_fr, [], header_fr) \<and>
      staged_trace_root data = header_fr \<and>
      staged_trace_fri_roots data = [] \<and>
      ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state)
        (verifier_header_messages
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data))
        (PState query_start) \<and>
      ro_absorb_lookup_chain attacker_state
        (PState query_start)
        (List.concat (take j (staged_query_chunks data)))
        (PState (query_states ! j))"
    by blast
  have original_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (ro_checked_staged_transcript_program A)
          adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have shape:
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
      length (staged_trace_fri_challenges data) = ceil_log clength \<and>
      length (staged_alphas data) = length spec \<and>
      length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1) \<and>
      length (staged_composition_fri_challenges data) =
        ceil_log (to_nat (staged_degree data) + 1) \<and>
      ceil_log (to_nat (staged_degree data) + 1) \<le>
        ceil_log (maxDegree + 1) \<and>
      length (staged_query_chunks data) = rounds"
    by (rule ro_checked_staged_transcript_program_outcome_shape[OF original_out])
  have map_bound:
    "card (fmdom' (HashMap attacker_state)) \<le>
      ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds[
        OF wf controlled outcome clean])
  have counter_j: "PQueryCounter (query_states ! j) = j"
    using witness_props zero_fields j_bound by simp
  have lookup_final:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j))) =
      Some (raws ! j)"
  proof -
    have lifted:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raws ! j)"
      by (rule hash_extension_lookup[OF lookup_start])
        (use zero_fields in simp)
    show ?thesis
      using lifted counter_j by simp
  qed
  have active:
    "hash_state_relation_active
      (zero_round_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j)))
      (raws ! j)"
    by (rule zero_round_absorbed_query_relation_bounded_activeI[
      OF map_bound clean no_initial])
      (use zero_fields header_props shape outcome_props raws_in j_bound
        lookup_final no_merkle_actual prefix_le in auto)
  have inactive_initial:
    "\<not> hash_state_relation_active
      (zero_round_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state)
      (QueryIndexChallenge j (PState (query_states ! j)))
      (raws ! j)"
    unfolding hash_state_relation_active_def adversary_initial_state_def
    by simp
  show ?thesis
    unfolding hash_state_relation_transition_def
    using active inactive_initial by blast
qed


definition ro_checked_staged_zero_round_prequery_side_event
where
  "ro_checked_staged_zero_round_prequery_side_event budgets out \<longleftrightarrow>
    final_hash_collision_event out \<or>
    hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state out \<or>
    ro_checked_staged_zero_round_prefix_merkle_target_hit out \<or>
    hash_state_relation_transition_event
      (zero_round_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state) out"

lemma ro_checked_staged_zero_round_prequery_some_imp_side_event:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and prequery:
      "ro_query_head_dependent_query_start_prequery_hit
        ro_actual_query_zero_round_bad_query_lists
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
  shows
    "ro_checked_staged_zero_round_prequery_side_event budgets
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
proof -
  show ?thesis
  proof (cases "hash_map_output_collision attacker_state")
    case True
    then show ?thesis
      unfolding ro_checked_staged_zero_round_prequery_side_event_def
        final_hash_collision_event_def
      by simp
  next
    case clean: False
    show ?thesis
    proof (cases
        "PState adversary_initial_state \<in>
          hash_map_output_values attacker_state")
      case True
      then obtain x where final_lookup:
        "fmlookup (HashMap attacker_state) x =
          Some (PState adversary_initial_state)"
        unfolding hash_map_output_values_def by blast
      have initial_lookup:
        "fmlookup (HashMap adversary_initial_state) x = None"
        unfolding adversary_initial_state_def by simp
      have initial_hit:
        "hash_map_new_output_hit {PState adversary_initial_state}
          adversary_initial_state attacker_state"
        unfolding hash_map_new_output_hit_def
        using initial_lookup final_lookup by blast
      then show ?thesis
        unfolding ro_checked_staged_zero_round_prequery_side_event_def
          hash_new_output_hit_event_def
        by simp
    next
      case no_initial: False
      show ?thesis
      proof (cases
          "hash_map_new_output_hit
            (ro_zero_round_first_root_prefix_merkle_targets
              prefix prefix_state)
            prefix_state attacker_state")
        case True
        then show ?thesis
          unfolding ro_checked_staged_zero_round_prequery_side_event_def
            ro_checked_staged_zero_round_prefix_merkle_target_hit_def
          by simp
      next
        case no_merkle: False
        have relation:
          "hash_state_relation_transition
            (zero_round_absorbed_query_relation_bounded
              (ro_checked_staged_transcript_hash_query_budget_for budgets))
            (HashMap adversary_initial_state)
            (HashMap attacker_state)"
          by (rule zero_round_prequery_bad_imp_budgeted_relation_transition[
            OF zero wf controlled outcome prequery clean no_initial no_merkle])
        then show ?thesis
          unfolding ro_checked_staged_zero_round_prequery_side_event_def
            hash_state_relation_transition_event_def
          by simp
      qed
    qed
  qed
qed

lemma ro_checked_staged_zero_round_prequery_imp_side_event:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and prequery:
      "ro_query_head_dependent_query_start_prequery_hit
        ro_actual_query_zero_round_bad_query_lists out"
  shows "ro_checked_staged_zero_round_prequery_side_event budgets out"
proof (cases out)
  case None
  then show ?thesis
    using prequery
    unfolding ro_query_head_dependent_query_start_prequery_hit_def
    by simp
next
  case (Some packed)
  obtain prefix prefix_state data query_start raws query_states
      attacker_state where packed_eq:
    "packed =
      (((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)"
    by (cases packed) (auto split: prod.splits)
  have outcome:
    "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          adversary_initial_state)"
    using support unfolding Some packed_eq .
  have prequery':
    "ro_query_head_dependent_query_start_prequery_hit
      ro_actual_query_zero_round_bad_query_lists
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
    using prequery unfolding Some packed_eq .
  show ?thesis
    unfolding Some packed_eq
    by (rule ro_checked_staged_zero_round_prequery_some_imp_side_event[
      OF zero wf controlled outcome prequery'])
qed

definition ro_checked_staged_zero_round_prequery_error
where
  "ro_checked_staged_zero_round_prequery_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in hash_collision_budget_value 0 q +
       nnreal q / nnreal size +
       ro_checked_staged_zero_round_prefix_merkle_target_error budgets +
       nnreal
         (q *
           (query_raw_preimage_card_envelope
               (query_sample_space_size - 1) +
             (5 * q + 2))) /
         nnreal size)"

lemma wp_ro_checked_staged_zero_round_prequery_bound:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_start_prequery_hit
        ro_actual_query_zero_round_bad_query_lists)
      adversary_initial_state
    \<le> ro_checked_staged_zero_round_prequery_error budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Prequery =
    "ro_query_head_dependent_query_start_prequery_hit
      ro_actual_query_zero_round_bad_query_lists"
  let ?Collision = "final_hash_collision_event"
  let ?Initial =
    "hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state"
  let ?Merkle = "ro_checked_staged_zero_round_prefix_merkle_target_hit"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?Relation =
    "hash_state_relation_transition_event
      (zero_round_absorbed_query_relation_bounded ?q)
      (HashMap adversary_initial_state)"
  have event_le:
    "wp_event ?M ?Prequery adversary_initial_state \<le>
      wp_event ?M
        (ro_checked_staged_zero_round_prequery_side_event budgets)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and prequery: "?Prequery out"
    show "ro_checked_staged_zero_round_prequery_side_event budgets out"
      by (rule ro_checked_staged_zero_round_prequery_imp_side_event[
        OF zero wf controlled support prequery])
  qed
  have union:
    "wp_event ?M
        (ro_checked_staged_zero_round_prequery_side_event budgets)
        adversary_initial_state
      \<le> wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Initial adversary_initial_state +
        wp_event ?M ?Merkle adversary_initial_state +
        wp_event ?M ?Relation adversary_initial_state"
    unfolding ro_checked_staged_zero_round_prequery_side_event_def
    by (rule wp_event_union_bound4)
  have collision:
    "wp_event ?M ?Collision adversary_initial_state \<le>
      hash_collision_budget_value 0 ?q"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_collision_bound_all_rounds[
        OF wf controlled])
  have initial:
    "wp_event ?M ?Initial adversary_initial_state \<le>
      nnreal ?q / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_initial_target_bound_all_rounds[
        OF wf controlled])
  have merkle:
    "wp_event ?M ?Merkle adversary_initial_state \<le>
      ro_checked_staged_zero_round_prefix_merkle_target_error budgets"
    by (rule wp_ro_checked_staged_zero_round_prefix_merkle_target_hit_bound[
      OF zero wf controlled])
  have relation:
    "wp_event ?M ?Relation adversary_initial_state \<le>
      nnreal
        (?q *
          (query_raw_preimage_card_envelope
              (query_sample_space_size - 1) +
            (5 * ?q + 2))) /
        nnreal size"
    by (rule wp_ro_checked_staged_transcript_zero_round_bounded_relation[
      OF wf controlled])
  show ?thesis
    apply (rule order_trans[OF event_le])
    apply (rule order_trans[OF union])
    unfolding ro_checked_staged_zero_round_prequery_error_def Let_def
    apply (intro add_mono)
       apply (rule collision)
      apply (rule initial)
     apply (rule merkle)
    apply (rule relation)
    done
qed


lemma
  wp_ro_checked_staged_transcript_program_zero_round_bad_query_fresh_bound:
  assumes zero: "ceil_log clength = 0"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_index_list_fresh_hit
        ro_actual_query_zero_round_bad_query_lists)
      s
    \<le> nnreal ((query_sample_space_size - 1) ^ rounds) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof (rule
    wp_ro_checked_staged_transcript_query_head_dependent_fresh_bound)
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  show
    "ro_actual_query_zero_round_bad_query_lists
        prefix prefix_state data query_start
      \<subseteq> fri_query_index_list_space"
    by (rule ro_actual_query_zero_round_bad_query_lists_subset)
next
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  show
    "card
        (ro_actual_query_zero_round_bad_query_lists
          prefix prefix_state data query_start)
      \<le> (query_sample_space_size - 1) ^ rounds"
    by (rule ro_actual_query_zero_round_bad_query_lists_card_bound[OF zero])
qed

lemma ro_checked_staged_first_root_query_head_program_zero_output_lengths:
  assumes zero: "ceil_log clength = 0"
    and outcome:
      "Some (((prefix, prefix_state), data, query_start), t) \<in>
        set_dist
          (execute (ro_checked_staged_first_root_query_head_program A) s)"
  shows
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
      length (staged_composition_fri_roots data) \<le>
        ceil_log (maxDegree + 1)"
proof -
  from outcome obtain prefix_final where after:
    "Some (data, query_start) \<in>
      set_dist
        (execute
          (ro_checked_staged_after_first_trace_fri_root_prefix_program A
            prefix)
          prefix_final)"
    unfolding ro_checked_staged_first_root_query_head_program_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  show ?thesis
    by (rule
      ro_checked_staged_after_first_trace_fri_root_prefix_program_zero_output_lengths[
        OF zero after])
qed

lemma wp_ro_checked_staged_zero_round_bad_query_phase_relation_bound:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_phase_relation_hit A
        ro_actual_query_zero_round_bad_query_lists)
      adversary_initial_state
    \<le> hash_relation_budget_value
      (rounds *
        (query_raw_preimage_card_envelope
          (query_sample_space_size - 1)))
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)"
proof (rule wp_ro_query_head_dependent_query_phase_relation_hit_bound[
    OF wf controlled])
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "query_index_raw_list_relation_fiber_bound
        (ro_actual_query_zero_round_bad_query_lists
          prefix prefix_state data query_start)
      \<le> rounds *
        (query_raw_preimage_card_envelope
          (query_sample_space_size - 1))"
    by (rule
      ro_actual_query_zero_round_bad_query_lists_relation_fiber_bound[
        OF zero])
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show "length (staged_trace_fri_roots data) = ceil_log clength"
    using
      ro_checked_staged_first_root_query_head_program_zero_output_lengths[
        OF zero head]
    by blast
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "length (staged_composition_fri_roots data) \<le>
      ceil_log (maxDegree + 1)"
    using
      ro_checked_staged_first_root_query_head_program_zero_output_lengths[
        OF zero head]
    by blast
qed

definition ro_checked_staged_zero_round_bad_actual_query_error
where
  "ro_checked_staged_zero_round_bad_actual_query_error budgets =
    nnreal ((query_sample_space_size - 1) ^ rounds) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds +
    ro_checked_staged_zero_round_prequery_error budgets +
    hash_relation_budget_value
      (rounds *
        (query_raw_preimage_card_envelope
          (query_sample_space_size - 1)))
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)"

lemma wp_ro_checked_staged_zero_round_bad_actual_query_bound:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_zero_round_bad_query_lists)
      adversary_initial_state
    \<le> ro_checked_staged_zero_round_bad_actual_query_error budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Q = "ro_actual_query_zero_round_bad_query_lists"
  let ?Fresh =
    "ro_query_head_dependent_query_index_list_fresh_hit ?Q"
  let ?Prequery =
    "ro_query_head_dependent_query_start_prequery_hit ?Q"
  let ?Relation =
    "ro_query_head_dependent_query_phase_relation_hit A ?Q"
  have split:
    "wp_event ?M
        (ro_query_head_dependent_actual_query_index_list_hit ?Q)
        adversary_initial_state
      \<le> wp_event ?M ?Fresh adversary_initial_state +
        wp_event ?M ?Prequery adversary_initial_state +
        wp_event ?M ?Relation adversary_initial_state"
    by (rule wp_ro_query_head_dependent_actual_query_index_list_hit_split[
      OF wf controlled])
  have fresh:
    "wp_event ?M ?Fresh adversary_initial_state \<le>
      nnreal ((query_sample_space_size - 1) ^ rounds) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule
      wp_ro_checked_staged_transcript_program_zero_round_bad_query_fresh_bound[
        OF zero])
  have prequery:
    "wp_event ?M ?Prequery adversary_initial_state \<le>
      ro_checked_staged_zero_round_prequery_error budgets"
    by (rule wp_ro_checked_staged_zero_round_prequery_bound[
      OF zero wf controlled])
  have relation:
    "wp_event ?M ?Relation adversary_initial_state \<le>
      hash_relation_budget_value
        (rounds *
          (query_raw_preimage_card_envelope
            (query_sample_space_size - 1)))
        (sum_list (query_opening_budgets budgets) + rounds +
          rounds * ro_checked_query_round_transcript_bound)"
    by (rule
      wp_ro_checked_staged_zero_round_bad_query_phase_relation_bound[
        OF zero wf controlled])
  show ?thesis
    by (rule order_trans[OF split])
      (use fresh prequery relation in
        \<open>simp add:
          ro_checked_staged_zero_round_bad_actual_query_error_def add_mono\<close>)
qed

end
end

