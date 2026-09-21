theory Soundness_FRI_RO_Actual_Query_Zero_Round_Alpha_Pivot_Bound
  imports
    Soundness_FRI_RO_Actual_Query_Zero_Round_Composition_Query_Bound
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Closed_Bound
begin

text \<open>
  Zero trace-FRI-round algebraic closure through the generalized absorbed
  alpha-pivot state relation.
\<close>

context soundness
begin

definition
  ro_checked_staged_zero_round_trace_composition_all_queries_consistent
where
  "ro_checked_staged_zero_round_trace_composition_all_queries_consistent
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        trace_table_low_degree
          (ro_actual_query_zero_round_trace_table data prefix_state) \<and>
        composition_table_low_degree maxDegree
          (ro_actual_query_composition_candidate data query_start) \<and>
        all_queries_consistent
          (ro_actual_query_zero_round_trace_table data prefix_state)
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data))"

lemma zero_round_trace_composition_bad_alpha_imp_alpha_pivot_relation_transition:
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
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values attacker_state"
    and no_trace_merkle:
      "\<not> hash_map_new_output_hit
        (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
        prefix_state attacker_state"
    and as_bad:
      "staged_alphas data \<in>
        composition_trace_bad_alpha_space
          (ro_actual_query_zero_round_trace_table data prefix_state)"
  shows
    "hash_state_relation_transition
      (alpha_pivot_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
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
  have prefix_ext: "prefix_state \<le> attacker_state"
    by (rule hash_ext_trans[OF prefix_query query_attacker])
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
       length (staged_alphas data) = length spec"
    using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
    by blast
  have trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    and alpha_len: "length (staged_alphas data) = length spec"
    using shape by blast+
  from ro_checked_staged_transcript_program_alpha_lookup_chain[
      OF wf controlled original_out]
  obtain alpha_start alpha_final where
    prealpha_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state)
        ([staged_trace_root data] @
          staged_trace_fri_roots data @
          [staged_trace_final data])
        alpha_start"
    and alpha_chain:
      "ro_alpha_lookup_prefix (HashMap attacker_state)
        (PAlphaCounter adversary_initial_state)
        alpha_start (staged_alphas data) alpha_final"
    by blast
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision attacker_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_ext])
    then show False using clean by contradiction
  qed
  have no_trace_merkle':
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {staged_trace_root data} prefix_state)
        prefix_state attacker_state"
    using no_trace_merkle prefix_clean zero_fields
    unfolding ro_zero_round_first_root_prefix_merkle_targets_def
    by simp
  let ?final = "channel_for_hash_map (HashMap attacker_state)"
  have final_map: "HashMap ?final = HashMap attacker_state"
    unfolding channel_for_hash_map_def by simp
  have final_attacker:
      "conceptual_table ?final (staged_trace_root data) (scale * clength) =
       conceptual_table attacker_state (staged_trace_root data)
         (scale * clength)"
    by (rule conceptual_table_cong_hash_map[OF final_map])
  have attacker_prefix:
      "conceptual_table attacker_state (staged_trace_root data)
          (scale * clength) =
       conceptual_table prefix_state (staged_trace_root data)
          (scale * clength)"
    by (rule conceptual_table_prefix_stable_if_no_target[
      OF prefix_ext no_trace_merkle'])
  have trace_table_eq:
      "alpha_pivot_trace_table (HashMap attacker_state)
          (staged_trace_root data) (staged_trace_fri_roots data) =
       ro_actual_query_zero_round_trace_table data prefix_state"
    unfolding ro_actual_query_zero_round_trace_table_def
    using zero_fields final_attacker attacker_prefix
    by (simp add: alpha_pivot_trace_table_empty)
  have as_bad_final:
      "staged_alphas data \<in>
        composition_trace_bad_alpha_space
          (alpha_pivot_trace_table (HashMap attacker_state)
            (staged_trace_root data) (staged_trace_fri_roots data))"
    using as_bad trace_table_eq by simp
  have violated:
      "violated_constraints
        (low_degree_trace_witness
          (alpha_pivot_trace_table (HashMap attacker_state)
            (staged_trace_root data) (staged_trace_fri_roots data))) \<noteq> {}"
    by (rule composition_trace_bad_alpha_space_violated[OF as_bad_final])
  let ?pivot =
    "composition_alpha_pivot
      (low_degree_trace_witness
        (alpha_pivot_trace_table (HashMap attacker_state)
          (staged_trace_root data) (staged_trace_fri_roots data)))"
  have pivot_spec: "?pivot < length spec"
    by (rule composition_alpha_pivot_bound[OF violated])
  have pivot_bound: "?pivot < length (staged_alphas data)"
    using pivot_spec alpha_len by simp
  from ro_alpha_lookup_prefix_take_lookup[OF alpha_chain pivot_bound]
  obtain pivot_state where
    alpha_prefix:
      "ro_alpha_lookup_prefix (HashMap attacker_state)
        (PAlphaCounter adversary_initial_state)
        alpha_start (take ?pivot (staged_alphas data)) pivot_state"
    and pivot_lookup:
      "fmlookup (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state) =
        Some (staged_alphas data ! ?pivot)"
    by blast
  have pivot_member:
      "staged_alphas data ! ?pivot \<in>
        composition_trace_bad_alpha_pivot_values
          (alpha_pivot_trace_table (HashMap attacker_state)
            (staged_trace_root data) (staged_trace_fri_roots data))
          (take ?pivot (staged_alphas data))"
    by (rule
      composition_trace_bad_alpha_pivot_value_member[OF as_bad_final])
  have prefix_length:
      "length (take ?pivot (staged_alphas data)) = ?pivot"
    using pivot_bound by simp
  have prealpha_final:
      "ro_absorb_lookup_chain ?final
        (PState adversary_initial_state)
        ([staged_trace_root data] @ staged_trace_fri_roots data @
          [staged_trace_final data])
        alpha_start"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule prealpha_chain)
  have clean_final: "\<not> hash_map_output_collision ?final"
    using clean final_map
    unfolding hash_map_output_collision_def by simp
  have no_initial_final:
      "PState adversary_initial_state \<notin> hash_map_output_values ?final"
    using no_initial final_map
    unfolding hash_map_output_values_def by simp
  have relation:
      "alpha_pivot_absorbed_query_relation
        (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding alpha_pivot_absorbed_query_relation_def Let_def
  proof (intro conjI)
    show "\<not> hash_map_output_collision ?final"
      by (rule clean_final)
    show "PState adversary_initial_state \<notin> hash_map_output_values ?final"
      by (rule no_initial_final)
    show
      "\<exists>fr trace_roots trace_final alpha_start' alpha_prefix pivot_state'.
        length trace_roots = ceil_log clength \<and>
        ro_absorb_lookup_chain ?final
          (PState adversary_initial_state)
          ([fr] @ trace_roots @ [trace_final]) alpha_start' \<and>
        ro_alpha_lookup_prefix (HashMap attacker_state)
          (PAlphaCounter adversary_initial_state)
          alpha_start' alpha_prefix pivot_state' \<and>
        length alpha_prefix =
          composition_alpha_pivot
            (low_degree_trace_witness
              (alpha_pivot_trace_table
                (HashMap attacker_state) fr trace_roots)) \<and>
        AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state =
          AlphaChallenge
            (PAlphaCounter adversary_initial_state + length alpha_prefix)
            pivot_state' \<and>
        staged_alphas data ! ?pivot \<in>
          composition_trace_bad_alpha_pivot_values
            (alpha_pivot_trace_table
              (HashMap attacker_state) fr trace_roots)
            alpha_prefix"
    proof (rule exI[of _ "staged_trace_root data"],
        rule exI[of _ "staged_trace_fri_roots data"],
        rule exI[of _ "staged_trace_final data"],
        rule exI[of _ alpha_start],
        rule exI[of _ "take ?pivot (staged_alphas data)"],
        rule exI[of _ pivot_state],
        intro conjI)
      show "length (staged_trace_fri_roots data) = ceil_log clength"
        by (rule trace_len)
      show
        "ro_absorb_lookup_chain ?final
          (PState adversary_initial_state)
          ([staged_trace_root data] @ staged_trace_fri_roots data @
            [staged_trace_final data]) alpha_start"
        by (rule prealpha_final)
      show
        "ro_alpha_lookup_prefix (HashMap attacker_state)
          (PAlphaCounter adversary_initial_state) alpha_start
          (take ?pivot (staged_alphas data)) pivot_state"
        by (rule alpha_prefix)
      show
        "length (take ?pivot (staged_alphas data)) =
          composition_alpha_pivot
            (low_degree_trace_witness
              (alpha_pivot_trace_table (HashMap attacker_state)
                (staged_trace_root data) (staged_trace_fri_roots data)))"
        using prefix_length by simp
      show
        "AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot) pivot_state =
         AlphaChallenge
          (PAlphaCounter adversary_initial_state +
            length (take ?pivot (staged_alphas data))) pivot_state"
        using prefix_length by simp
      show
        "staged_alphas data ! ?pivot \<in>
          composition_trace_bad_alpha_pivot_values
            (alpha_pivot_trace_table (HashMap attacker_state)
              (staged_trace_root data) (staged_trace_fri_roots data))
            (take ?pivot (staged_alphas data))"
        by (rule pivot_member)
    qed
  qed
  have map_bound:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds[
        OF wf controlled outcome clean])
  have bounded_relation:
      "alpha_pivot_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding alpha_pivot_absorbed_query_relation_bounded_def
    using map_bound relation by simp
  have active:
      "hash_state_relation_active
        (alpha_pivot_absorbed_query_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets))
        (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding hash_state_relation_active_def
    using pivot_lookup bounded_relation by simp
  have inactive_initial:
      "\<not> hash_state_relation_active
        (alpha_pivot_absorbed_query_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets))
        (HashMap adversary_initial_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding hash_state_relation_active_def adversary_initial_state_def
    by simp
  show ?thesis
    unfolding hash_state_relation_transition_def
    using active inactive_initial by blast
qed

definition ro_checked_staged_zero_round_alpha_pivot_side_event
where
  "ro_checked_staged_zero_round_alpha_pivot_side_event budgets out \<longleftrightarrow>
    final_hash_collision_event out \<or>
    hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state out \<or>
    ro_checked_staged_zero_round_prefix_merkle_target_hit out \<or>
    hash_state_relation_transition_event
      (alpha_pivot_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state) out"

definition ro_checked_staged_zero_round_alpha_pivot_error
where
  "ro_checked_staged_zero_round_alpha_pivot_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in hash_collision_budget_value 0 q +
       nnreal q / nnreal size +
       ro_checked_staged_zero_round_prefix_merkle_target_error budgets +
       nnreal (q * (1 + (6 * q + 2))) / nnreal size)"

lemma ro_checked_staged_zero_round_all_queries_consistent_some_imp_alpha_pivot_side_event:
  assumes false_statement: "\<not> exists_valid_trace"
    and zero: "ceil_log clength = 0"
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
    and all_consistent:
      "ro_checked_staged_zero_round_trace_composition_all_queries_consistent
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
  shows
    "ro_checked_staged_zero_round_alpha_pivot_side_event budgets
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
proof -
  have low_and_consistent:
      "trace_table_low_degree
          (ro_actual_query_zero_round_trace_table data prefix_state) \<and>
       composition_table_low_degree maxDegree
          (ro_actual_query_composition_candidate data query_start) \<and>
       all_queries_consistent
          (ro_actual_query_zero_round_trace_table data prefix_state)
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data)"
    using all_consistent
    unfolding
      ro_checked_staged_zero_round_trace_composition_all_queries_consistent_def
    by simp
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have alpha_len: "length (staged_alphas data) = length spec"
    using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
    by blast
  have as_bad:
      "staged_alphas data \<in>
        composition_trace_bad_alpha_space
          (ro_actual_query_zero_round_trace_table data prefix_state)"
    by (rule
      low_degree_all_queries_consistent_imp_composition_trace_bad_alpha_space[
        OF false_statement alpha_len])
      (use low_and_consistent in blast)+
  show ?thesis
  proof (cases "hash_map_output_collision attacker_state")
    case True
    then show ?thesis
      unfolding ro_checked_staged_zero_round_alpha_pivot_side_event_def
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
        unfolding ro_checked_staged_zero_round_alpha_pivot_side_event_def
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
          unfolding ro_checked_staged_zero_round_alpha_pivot_side_event_def
            ro_checked_staged_zero_round_prefix_merkle_target_hit_def
          by simp
      next
        case no_merkle: False
        have relation:
            "hash_state_relation_transition
              (alpha_pivot_absorbed_query_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets))
              (HashMap adversary_initial_state)
              (HashMap attacker_state)"
          by (rule
            zero_round_trace_composition_bad_alpha_imp_alpha_pivot_relation_transition[
              OF zero wf controlled outcome clean no_initial no_merkle as_bad])
        then show ?thesis
          unfolding ro_checked_staged_zero_round_alpha_pivot_side_event_def
            hash_state_relation_transition_event_def
          by simp
      qed
    qed
  qed
qed

lemma ro_checked_staged_zero_round_all_queries_consistent_imp_alpha_pivot_side_event:
  assumes false_statement: "\<not> exists_valid_trace"
    and zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and all_consistent:
      "ro_checked_staged_zero_round_trace_composition_all_queries_consistent out"
  shows
    "ro_checked_staged_zero_round_alpha_pivot_side_event budgets out"
proof (cases out)
  case None
  then show ?thesis
    using all_consistent
    unfolding
      ro_checked_staged_zero_round_trace_composition_all_queries_consistent_def
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
  have all_consistent':
      "ro_checked_staged_zero_round_trace_composition_all_queries_consistent
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
    using all_consistent unfolding Some packed_eq .
  show ?thesis
    unfolding Some packed_eq
    by (rule
      ro_checked_staged_zero_round_all_queries_consistent_some_imp_alpha_pivot_side_event[
        OF false_statement zero wf controlled outcome all_consistent'])
qed

lemma wp_ro_checked_staged_zero_round_all_queries_consistent_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_zero_round_trace_composition_all_queries_consistent
      adversary_initial_state
    \<le> ro_checked_staged_zero_round_alpha_pivot_error budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?All =
    "ro_checked_staged_zero_round_trace_composition_all_queries_consistent"
  let ?Collision = "final_hash_collision_event"
  let ?Initial =
    "hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state"
  let ?Merkle = "ro_checked_staged_zero_round_prefix_merkle_target_hit"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?Relation =
    "hash_state_relation_transition_event
      (alpha_pivot_absorbed_query_relation_bounded ?q)
      (HashMap adversary_initial_state)"
  have event_le:
      "wp_event ?M ?All adversary_initial_state \<le>
        wp_event ?M
          (ro_checked_staged_zero_round_alpha_pivot_side_event budgets)
          adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?M adversary_initial_state)"
      and all_consistent: "?All out"
    show "ro_checked_staged_zero_round_alpha_pivot_side_event budgets out"
      by (rule
        ro_checked_staged_zero_round_all_queries_consistent_imp_alpha_pivot_side_event[
          OF false_statement zero wf controlled support all_consistent])
  qed
  have union:
      "wp_event ?M
          (ro_checked_staged_zero_round_alpha_pivot_side_event budgets)
          adversary_initial_state
        \<le> wp_event ?M ?Collision adversary_initial_state +
          wp_event ?M ?Initial adversary_initial_state +
          wp_event ?M ?Merkle adversary_initial_state +
          wp_event ?M ?Relation adversary_initial_state"
    unfolding ro_checked_staged_zero_round_alpha_pivot_side_event_def
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
        nnreal (?q * (1 + (6 * ?q + 2))) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_alpha_pivot_bounded_relation_all_rounds[
        OF wf controlled])
  show ?thesis
    apply (rule order_trans[OF event_le])
    apply (rule order_trans[OF union])
    unfolding ro_checked_staged_zero_round_alpha_pivot_error_def Let_def
    apply (intro add_mono)
       apply (rule collision)
      apply (rule initial)
     apply (rule merkle)
    apply (rule relation)
    done
qed

lemma wp_ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent_le:
  "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent
      s
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_zero_round_trace_composition_all_queries_consistent
      s"
  unfolding
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
proof (rule wp_event_bind_bound_by_head_event)
  show
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_zero_round_trace_composition_all_queries_consistent s
    \<le> wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_zero_round_trace_composition_all_queries_consistent s"
    by simp
next
  show
    "ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent
        None \<Longrightarrow>
      ro_checked_staged_zero_round_trace_composition_all_queries_consistent
        None"
    unfolding
      ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent_def
      ro_checked_staged_zero_round_trace_composition_all_queries_consistent_def
    by simp
next
  fix x t out
  assume head:
    "Some (x, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          s)"
  obtain prefix_with_state data query_start raws query_states where x_eq:
      "x = (prefix_with_state, data, query_start, raws, query_states)"
    by (cases x) auto
  assume tail:
    "out \<in>
      set_dist
        (execute
          (case x of
            (prefix_with_state, data, query_start, raws, query_states) \<Rightarrow>
              get \<bind>
              (\<lambda>attacker_state.
                put
                  (verifier_state_from_adversary attacker_state
                    (staged_proof_transcript data)) \<bind>
                (\<lambda>_. ro_verify_monad \<bind>
                  (\<lambda>result.
                    return
                      (((prefix_with_state, data, query_start, raws,
                          query_states), attacker_state), result)))))
          t)"
    and all_consistent:
      "ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent
        out"
  show
    "ro_checked_staged_zero_round_trace_composition_all_queries_consistent
      (Some (x, t))"
    using tail all_consistent
    unfolding x_eq
      ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent_def
      ro_checked_staged_zero_round_trace_composition_all_queries_consistent_def
    by (auto simp: wpsimps elim!: set_dist_bindE
        split: option.splits prod.splits)
qed

lemma wp_ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent
      adversary_initial_state
    \<le> ro_checked_staged_zero_round_alpha_pivot_error budgets"
  by (rule order_trans[
    OF
      wp_ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent_le
      wp_ro_checked_staged_zero_round_all_queries_consistent_bound[
        OF false_statement zero wf controlled]])

end
end
