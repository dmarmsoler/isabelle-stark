theory Soundness_FRI_RO_Actual_Query_Zero_Round_Composition_Query_Bound
  imports
    Soundness_FRI_RO_Actual_Query_Zero_Round_Composition_Classification
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Prequery_Closed_Bound
begin

text \<open>
  Exact product and adaptive-prequery accounting for the sampled
  trace/composition agreement event in the zero trace-FRI-round branch.
\<close>

context soundness
begin

lemma ro_actual_query_trace_composition_good_query_lists_zero_round:
  assumes zero: "ceil_log clength = 0"
    and prefix: "prefix = (fr, [], fr)"
    and trace_root: "staged_trace_root data = fr"
  shows
    "ro_actual_query_trace_composition_good_query_lists
        prefix prefix_state data query_start =
      ro_actual_query_zero_round_trace_composition_good_query_lists
        data prefix_state query_start"
  unfolding
    ro_actual_query_zero_round_trace_composition_good_query_lists_def
    ro_actual_query_trace_composition_good_query_lists_def
    ro_actual_query_zero_round_trace_composition_accepted_query_lists_def
    ro_actual_query_trace_composition_accepted_query_lists_def
    ro_actual_query_zero_round_trace_composition_accepted_indices_def
    ro_actual_query_trace_composition_accepted_indices_def
    ro_actual_query_zero_round_trace_table_def
    first_trace_fri_root_prefix_first_table_def
    trace_composition_accepted_indices_def
    query_agreement_indices_def
    trace_table_base_agreement_indices_def
  using zero prefix trace_root
  by auto

lemma zero_round_trace_composition_good_prequery_imp_budgeted_relation_transition:
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
        ro_actual_query_zero_round_trace_composition_good_query_lists_for
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values attacker_state"
    and no_trace_merkle:
      "\<not> hash_map_new_output_hit
        (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
        prefix_state attacker_state"
    and no_composition_merkle:
      "\<not> hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets
          (ro_query_head_data data) query_start)
        query_start attacker_state"
  shows
    "hash_state_relation_transition
      (trace_composition_absorbed_query_relation_bounded
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
        ro_actual_query_zero_round_trace_composition_good_query_lists_for
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
    raws_in_zero:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_actual_query_zero_round_trace_composition_good_query_lists
          (ro_query_head_data data) prefix_state query_start"
    and j_bound: "j < rounds"
    and lookup_start:
      "fmlookup (HashMap query_start)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raws ! j)"
    unfolding
      ro_actual_query_zero_round_trace_composition_good_query_lists_for_def
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
  have prefix_attacker: "prefix_state \<le> attacker_state"
    by (rule hash_ext_trans[OF prefix_query query_attacker])
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision attacker_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_attacker])
    with clean show False by contradiction
  qed
  have no_first_trace_merkle:
      "\<not> hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state attacker_state"
    using no_trace_merkle prefix_clean zero_fields
    unfolding ro_zero_round_first_root_prefix_merkle_targets_def
      first_trace_fri_root_prefix_merkle_targets_def
    by simp
  from ro_checked_staged_transcript_zero_round_header_query_prefix_chain[
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
    show ?thesis using lifted counter_j by simp
  qed
  have raws_in_generic:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_actual_query_trace_composition_good_query_lists
          prefix prefix_state (ro_query_head_data data) query_start"
  proof -
    have family_eq:
        "ro_actual_query_trace_composition_good_query_lists
            prefix prefix_state (ro_query_head_data data) query_start =
          ro_actual_query_zero_round_trace_composition_good_query_lists
            (ro_query_head_data data) prefix_state query_start"
      apply (rule
        ro_actual_query_trace_composition_good_query_lists_zero_round[
          OF zero])
       apply (use zero_fields in simp)
      using zero_fields
      unfolding ro_query_head_data_def
      by simp
    show ?thesis using raws_in_zero family_eq by simp
  qed
  have prefix_selector:
      "prefix =
        (staged_trace_root data, [],
          trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data))"
    using zero_fields
    by (simp add: trace_composition_header_trace_root_empty)
  have active:
      "hash_state_relation_active
        (trace_composition_absorbed_query_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets))
        (HashMap attacker_state)
        (QueryIndexChallenge j (PState (query_states ! j)))
        (raws ! j)"
    by (rule trace_composition_absorbed_query_relation_bounded_activeI[
      OF map_bound clean no_initial prefix_attacker query_attacker
        prefix_selector no_first_trace_merkle no_composition_merkle])
      (use shape header_props outcome_props raws_in_generic j_bound lookup_final
        in auto)
  have inactive_initial:
      "\<not> hash_state_relation_active
        (trace_composition_absorbed_query_relation_bounded
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

lemma wp_ro_checked_staged_trace_composition_prefix_target_hit_bound_zero_round:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_trace_composition_clean_composition_prefix_target_hit
      adversary_initial_state
    \<le> ro_checked_staged_trace_composition_prefix_target_error budgets"
proof -
  let ?M = "ro_checked_staged_first_root_query_head_program A"
  let ?K =
    "\<lambda>((prefix, prefix_state), data, query_start).
      ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          return
            (((prefix, prefix_state),
              data\<lparr>staged_query_chunks := query_chunks\<rparr>,
              query_start, raws, query_states)))"
  let ?E =
    "ro_checked_staged_trace_composition_clean_composition_prefix_target_hit"
  let ?B =
    "\<lambda>((prefix, prefix_state), data, query_start) t.
      ro_actual_query_composition_prefix_targets
        (ro_query_head_data data) query_start"
  let ?tail =
    "sum_list (query_opening_budgets budgets) + rounds +
      rounds * ro_checked_query_round_transcript_bound"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have decomposition:
      "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A =
        ?M \<bind> ?K"
    unfolding
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
    by (simp add: split_def)
  show ?thesis
    unfolding decomposition
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_conditional[
        where B="?B" and n="?tail" and
          C="ro_checked_staged_trace_composition_prefix_target_error budgets"])
    show "\<not> ?E None"
      unfolding
        ro_checked_staged_trace_composition_clean_composition_prefix_target_hit_def
      by simp
  next
    fix x t out
    assume head:
        "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
      and tail_support: "out \<in> set_dist (execute (?K x) t)"
      and event: "?E out"
    obtain prefix prefix_state data query_start where x_eq:
        "x = ((prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have state_eq: "t = query_start"
      using head
      unfolding x_eq ro_checked_staged_first_root_query_head_program_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    show "hash_new_output_hit_event (?B x t) t out"
      using event tail_support
      unfolding x_eq state_eq
        ro_checked_staged_trace_composition_clean_composition_prefix_target_hit_def
        hash_new_output_hit_event_def
      by (cases out)
        (auto elim!: set_dist_bindE split: prod.splits)
  next
    fix x t
    assume head:
      "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
    obtain prefix prefix_state data query_start where x_eq:
        "x = ((prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have lengths:
        "length (staged_trace_fri_roots data) = ceil_log clength \<and>
          length (staged_composition_fri_roots data) \<le>
            ceil_log (maxDegree + 1)"
      using
        ro_checked_staged_first_root_query_head_program_zero_output_lengths[
          OF zero head[unfolded x_eq]]
      by blast
    have query_target:
        "hash_target_program
          (ro_actual_query_composition_prefix_targets
            (ro_query_head_data data) query_start)
          ?tail
          (ro_checked_staged_query_program_with_witnesses A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)
            query_start 0 rounds)"
      by (rule
        hash_target_program_ro_checked_staged_query_program_with_witnesses_closed[
          OF wf controlled conjunct1[OF lengths] conjunct2[OF lengths]])
    have program_explicit:
        "hash_target_program
          (ro_actual_query_composition_prefix_targets
            (ro_query_head_data data) query_start)
          (?tail + 0)
          (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data)
              query_start 0 rounds \<bind>
            (\<lambda>(raws, query_states, query_chunks).
              return
                ((prefix, prefix_state),
                  data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                  query_start, raws, query_states)))"
      apply (rule hash_target_program_bind[OF query_target])
      by (auto simp: hash_target_program_return split: prod.splits)
    have budget_explicit:
        "hash_target_budget
          (ro_actual_query_composition_prefix_targets
            (ro_query_head_data data) query_start)
          ?tail
          (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data)
              query_start 0 rounds \<bind>
            (\<lambda>(raws, query_states, query_chunks).
              return
                ((prefix, prefix_state),
                  data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                  query_start, raws, query_states)))"
      by (rule hash_target_program_budget)
        (use program_explicit in simp)
    show "hash_target_budget (?B x t) ?tail (?K x)"
      using budget_explicit
      unfolding x_eq
      by simp
  next
    fix x t
    assume head:
        "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
      and witness:
        "\<exists>out \<in> set_dist (execute (?K x) t). ?E out"
    obtain prefix prefix_state data query_start where x_eq:
        "x = ((prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    from witness obtain out where
      tail_support: "out \<in> set_dist (execute (?K x) t)"
      and event: "?E out"
      by blast
    from event obtain packed attacker_state where out_eq:
        "out = Some (packed, attacker_state)"
      and clean: "\<not> hash_map_output_collision attacker_state"
      unfolding
        ro_checked_staged_trace_composition_clean_composition_prefix_target_hit_def
      by (cases out) (auto split: prod.splits)
    obtain prefix' prefix_state' data' query_start' raws query_states
        where packed_eq:
        "packed =
          ((prefix', prefix_state'), data', query_start', raws, query_states)"
      by (cases packed) (auto split: prod.splits)
    have full_support:
        "Some
          (((prefix', prefix_state'), data', query_start', raws, query_states),
            attacker_state) \<in>
          set_dist
            (execute
              (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
                A)
              adversary_initial_state)"
    proof -
      have bound:
          "out \<in>
            set_dist
              (execute (?M \<bind> ?K) adversary_initial_state)"
        by (rule set_dist_bindI[OF head])
          (rule tail_support)
      show ?thesis
        using bound
        unfolding decomposition out_eq packed_eq
        by simp
    qed
    have outcome_props: "query_start' \<le> attacker_state"
      using
        ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
          OF wf controlled full_support]
      by blast
    have return_fields:
        "prefix' = prefix \<and> prefix_state' = prefix_state \<and>
          query_start' = query_start \<and>
          ro_query_head_data data' = ro_query_head_data data"
      using tail_support
      unfolding x_eq out_eq packed_eq
      by (auto elim!: set_dist_bindE split: prod.splits)
    have query_start_ext: "query_start \<le> attacker_state"
      using outcome_props return_fields by simp
    have map_bound:
        "card (fmdom' (HashMap attacker_state)) \<le> ?q"
      by (rule
        ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds[
          OF wf controlled full_support clean])
    have dom_subset:
        "fmdom' (HashMap query_start) \<subseteq>
          fmdom' (HashMap attacker_state)"
    proof
      fix key
      assume key_old: "key \<in> fmdom' (HashMap query_start)"
      then obtain v where lookup_old:
          "fmlookup (HashMap query_start) key = Some v"
        by (auto simp: fmlookup_dom'_iff)
      have extension:
          "fmlookup (HashMap query_start) key = None \<or>
            fmlookup (HashMap query_start) key =
              fmlookup (HashMap attacker_state) key"
        using query_start_ext
        unfolding less_eq_hash_ext_def less_eq_fmap_def
        by blast
      have lookup_new:
          "fmlookup (HashMap attacker_state) key = Some v"
        using extension lookup_old by auto
      show "key \<in> fmdom' (HashMap attacker_state)"
        using lookup_new by (simp add: fmlookup_dom'_iff)
    qed
    have domain_start:
        "card (fmdom' (HashMap query_start)) \<le> ?q"
    proof -
      have
          "card (fmdom' (HashMap query_start)) \<le>
            card (fmdom' (HashMap attacker_state))"
        by (rule card_mono[OF finite_fmdom' dom_subset])
      then show ?thesis using map_bound by simp
    qed
    have target_card:
        "card (?B x t) \<le> 1 + 2 * ?q"
    proof -
      have
          "card
            (ro_actual_query_composition_prefix_targets
              (ro_query_head_data data) query_start)
          \<le> 1 + 2 * card (fmdom' (HashMap query_start))"
        by (rule ro_actual_query_composition_prefix_targets_card_bound)
      also have "... \<le> 1 + 2 * ?q"
        using domain_start by simp
      finally show ?thesis
        unfolding x_eq
        by simp
    qed
    show
        "hash_target_budget_value (?B x t) ?tail \<le>
          ro_checked_staged_trace_composition_prefix_target_error budgets"
      unfolding hash_target_budget_value_def
        ro_checked_staged_trace_composition_prefix_target_error_def Let_def
      apply (rule nnreal_nat_divide_right_mono)
      using target_card
      by (rule mult_left_mono) simp
  qed
qed

definition ro_checked_staged_zero_round_trace_composition_good_prequery_side_event
where
  "ro_checked_staged_zero_round_trace_composition_good_prequery_side_event
      budgets out \<longleftrightarrow>
    final_hash_collision_event out \<or>
    hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state out \<or>
    ro_checked_staged_zero_round_prefix_merkle_target_hit out \<or>
    ro_checked_staged_trace_composition_clean_composition_prefix_target_hit out \<or>
    hash_state_relation_transition_event
      (trace_composition_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state) out"

lemma ro_checked_staged_zero_round_trace_composition_good_prequery_some_imp_side_event:
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
        ro_actual_query_zero_round_trace_composition_good_query_lists_for
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
  shows
    "ro_checked_staged_zero_round_trace_composition_good_prequery_side_event
      budgets
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
proof -
  show ?thesis
  proof (cases "hash_map_output_collision attacker_state")
    case True
    then show ?thesis
      unfolding
        ro_checked_staged_zero_round_trace_composition_good_prequery_side_event_def
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
        unfolding
          ro_checked_staged_zero_round_trace_composition_good_prequery_side_event_def
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
          unfolding
            ro_checked_staged_zero_round_trace_composition_good_prequery_side_event_def
            ro_checked_staged_zero_round_prefix_merkle_target_hit_def
          by simp
      next
        case no_trace_merkle: False
        show ?thesis
        proof (cases
            "hash_map_new_output_hit
              (ro_actual_query_composition_prefix_targets
                (ro_query_head_data data) query_start)
              query_start attacker_state")
          case True
          then show ?thesis
            unfolding
              ro_checked_staged_zero_round_trace_composition_good_prequery_side_event_def
              ro_checked_staged_trace_composition_clean_composition_prefix_target_hit_def
            using clean by simp
        next
          case no_composition_merkle: False
          have relation:
              "hash_state_relation_transition
                (trace_composition_absorbed_query_relation_bounded
                  (ro_checked_staged_transcript_hash_query_budget_for budgets))
                (HashMap adversary_initial_state)
                (HashMap attacker_state)"
            by (rule
              zero_round_trace_composition_good_prequery_imp_budgeted_relation_transition[
                OF zero wf controlled outcome prequery clean no_initial
                  no_trace_merkle no_composition_merkle])
          then show ?thesis
            unfolding
              ro_checked_staged_zero_round_trace_composition_good_prequery_side_event_def
              hash_state_relation_transition_event_def
            by simp
        qed
      qed
    qed
  qed
qed

lemma ro_checked_staged_zero_round_trace_composition_good_prequery_imp_side_event:
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
        ro_actual_query_zero_round_trace_composition_good_query_lists_for out"
  shows
    "ro_checked_staged_zero_round_trace_composition_good_prequery_side_event
      budgets out"
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
        ro_actual_query_zero_round_trace_composition_good_query_lists_for
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
    using prequery unfolding Some packed_eq .
  show ?thesis
    unfolding Some packed_eq
    by (rule
      ro_checked_staged_zero_round_trace_composition_good_prequery_some_imp_side_event[
        OF zero wf controlled outcome prequery'])
qed

definition ro_checked_staged_zero_round_trace_composition_good_prequery_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_zero_round_trace_composition_good_prequery_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in hash_collision_budget_value 0 q +
       nnreal q / nnreal size +
       ro_checked_staged_zero_round_prefix_merkle_target_error budgets +
       ro_checked_staged_trace_composition_prefix_target_error budgets +
       nnreal
         (q *
           (query_raw_preimage_card_envelope query_agreement_bound +
             (5 * q + 2))) /
         nnreal size)"

lemma wp_ro_checked_staged_zero_round_trace_composition_good_prequery_bound:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_start_prequery_hit
        ro_actual_query_zero_round_trace_composition_good_query_lists_for)
      adversary_initial_state
    \<le> ro_checked_staged_zero_round_trace_composition_good_prequery_error
        budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Prequery =
    "ro_query_head_dependent_query_start_prequery_hit
      ro_actual_query_zero_round_trace_composition_good_query_lists_for"
  let ?Collision = "final_hash_collision_event"
  let ?Initial =
    "hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state"
  let ?TraceTarget = "ro_checked_staged_zero_round_prefix_merkle_target_hit"
  let ?CompositionTarget =
    "ro_checked_staged_trace_composition_clean_composition_prefix_target_hit"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?Relation =
    "hash_state_relation_transition_event
      (trace_composition_absorbed_query_relation_bounded ?q)
      (HashMap adversary_initial_state)"
  have event_le:
      "wp_event ?M ?Prequery adversary_initial_state \<le>
        wp_event ?M
          (ro_checked_staged_zero_round_trace_composition_good_prequery_side_event
            budgets)
          adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?M adversary_initial_state)"
      and prequery: "?Prequery out"
    show
      "ro_checked_staged_zero_round_trace_composition_good_prequery_side_event
        budgets out"
      by (rule
        ro_checked_staged_zero_round_trace_composition_good_prequery_imp_side_event[
          OF zero wf controlled support prequery])
  qed
  have union4:
      "wp_event ?M
          (ro_checked_staged_zero_round_trace_composition_good_prequery_side_event
            budgets)
          adversary_initial_state
        \<le> wp_event ?M ?Collision adversary_initial_state +
          wp_event ?M ?Initial adversary_initial_state +
          wp_event ?M ?TraceTarget adversary_initial_state +
          wp_event ?M
            (\<lambda>out. ?CompositionTarget out \<or> ?Relation out)
            adversary_initial_state"
    unfolding
      ro_checked_staged_zero_round_trace_composition_good_prequery_side_event_def
    by (rule wp_event_union_bound4)
  have union2:
      "wp_event ?M
          (\<lambda>out. ?CompositionTarget out \<or> ?Relation out)
          adversary_initial_state
        \<le> wp_event ?M ?CompositionTarget adversary_initial_state +
          wp_event ?M ?Relation adversary_initial_state"
    by (rule wp_event_union_bound)
  have union:
      "wp_event ?M
          (ro_checked_staged_zero_round_trace_composition_good_prequery_side_event
            budgets)
          adversary_initial_state
        \<le> wp_event ?M ?Collision adversary_initial_state +
          wp_event ?M ?Initial adversary_initial_state +
          wp_event ?M ?TraceTarget adversary_initial_state +
          wp_event ?M ?CompositionTarget adversary_initial_state +
          wp_event ?M ?Relation adversary_initial_state"
    apply (rule order_trans[OF union4])
    using union2
    by (simp add: add_mono add.assoc)
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
  have trace_target:
      "wp_event ?M ?TraceTarget adversary_initial_state \<le>
        ro_checked_staged_zero_round_prefix_merkle_target_error budgets"
    by (rule wp_ro_checked_staged_zero_round_prefix_merkle_target_hit_bound[
      OF zero wf controlled])
  have composition_target:
      "wp_event ?M ?CompositionTarget adversary_initial_state \<le>
        ro_checked_staged_trace_composition_prefix_target_error budgets"
    by (rule
      wp_ro_checked_staged_trace_composition_prefix_target_hit_bound_zero_round[
        OF zero wf controlled])
  have relation:
      "wp_event ?M ?Relation adversary_initial_state \<le>
        nnreal
          (?q *
            (query_raw_preimage_card_envelope query_agreement_bound +
              (5 * ?q + 2))) /
          nnreal size"
  proof -
    have bound:
        "wp_event ?M ?Relation adversary_initial_state \<le>
          nnreal
            (?q *
              (query_raw_preimage_card_envelope
                  trace_composition_query_index_bound +
                (5 * ?q + 2))) /
            nnreal size"
      by (rule
        wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_trace_composition_bounded_relation_all_rounds[
          OF wf controlled])
    have powers_one: "powers = 1"
      by (rule ceil_log_clength_zero_imp_powers_one[OF zero])
    show ?thesis
      using bound powers_one
      unfolding trace_composition_query_index_bound_def
      by simp
  qed
  show ?thesis
    apply (rule order_trans[OF event_le])
    apply (rule order_trans[OF union])
    unfolding
      ro_checked_staged_zero_round_trace_composition_good_prequery_error_def
      Let_def
    apply (intro add_mono)
        apply (rule collision)
       apply (rule initial)
      apply (rule trace_target)
     apply (rule composition_target)
    apply (rule relation)
    done
qed

lemma wp_ro_checked_staged_transcript_program_zero_round_trace_composition_good_query_fresh_bound:
  "wp_event
    (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
      A)
    (ro_query_head_dependent_query_index_list_fresh_hit
      ro_actual_query_zero_round_trace_composition_good_query_lists_for)
    s
  \<le> nnreal (query_agreement_bound ^ rounds) *
    (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof (rule
    wp_ro_checked_staged_transcript_query_head_dependent_fresh_bound)
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  show
    "ro_actual_query_zero_round_trace_composition_good_query_lists_for
        prefix prefix_state data query_start
      \<subseteq> fri_query_index_list_space"
    by (rule
      ro_actual_query_zero_round_trace_composition_good_query_lists_for_subset)
next
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  show
    "card
        (ro_actual_query_zero_round_trace_composition_good_query_lists_for
          prefix prefix_state data query_start)
      \<le> query_agreement_bound ^ rounds"
    by (rule
      ro_actual_query_zero_round_trace_composition_good_query_lists_for_card_bound)
qed

lemma wp_ro_checked_staged_zero_round_trace_composition_good_query_phase_relation_bound:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_phase_relation_hit A
        ro_actual_query_zero_round_trace_composition_good_query_lists_for)
      adversary_initial_state
    \<le> hash_relation_budget_value
      (rounds *
        (query_raw_preimage_card_envelope query_agreement_bound))
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
        (ro_actual_query_zero_round_trace_composition_good_query_lists_for
          prefix prefix_state data query_start)
      \<le> rounds *
        (query_raw_preimage_card_envelope query_agreement_bound)"
    by (rule
      ro_actual_query_zero_round_trace_composition_good_query_lists_for_relation_fiber_bound)
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

definition ro_checked_staged_zero_round_trace_composition_good_actual_query_error
where
  "ro_checked_staged_zero_round_trace_composition_good_actual_query_error
      budgets =
    nnreal (query_agreement_bound ^ rounds) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds +
    ro_checked_staged_zero_round_trace_composition_good_prequery_error budgets +
    hash_relation_budget_value
      (rounds *
        (query_raw_preimage_card_envelope query_agreement_bound))
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)"

lemma wp_ro_checked_staged_zero_round_trace_composition_good_actual_query_bound:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_zero_round_trace_composition_good_query_lists_for)
      adversary_initial_state
    \<le> ro_checked_staged_zero_round_trace_composition_good_actual_query_error
        budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Q =
    "ro_actual_query_zero_round_trace_composition_good_query_lists_for"
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
        nnreal (query_agreement_bound ^ rounds) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule
      wp_ro_checked_staged_transcript_program_zero_round_trace_composition_good_query_fresh_bound)
  have prequery:
      "wp_event ?M ?Prequery adversary_initial_state \<le>
        ro_checked_staged_zero_round_trace_composition_good_prequery_error
          budgets"
    by (rule
      wp_ro_checked_staged_zero_round_trace_composition_good_prequery_bound[
        OF zero wf controlled])
  have relation:
      "wp_event ?M ?Relation adversary_initial_state \<le>
        hash_relation_budget_value
          (rounds *
            (query_raw_preimage_card_envelope query_agreement_bound))
          (sum_list (query_opening_budgets budgets) + rounds +
            rounds * ro_checked_query_round_transcript_bound)"
    by (rule
      wp_ro_checked_staged_zero_round_trace_composition_good_query_phase_relation_bound[
        OF zero wf controlled])
  show ?thesis
    by (rule order_trans[OF split])
      (use fresh prequery relation in
        \<open>simp add:
          ro_checked_staged_zero_round_trace_composition_good_actual_query_error_def
          add_mono\<close>)
qed

lemma wp_ro_absorb_checked_staged_security_zero_round_trace_composition_good_actual_query_bound:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_zero_round_trace_composition_good_query_lists_for)
      adversary_initial_state
    \<le> ro_checked_staged_zero_round_trace_composition_good_actual_query_error
        budgets"
  by (rule order_trans[
    OF
      wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
      wp_ro_checked_staged_zero_round_trace_composition_good_actual_query_bound[
        OF zero wf controlled]])

lemma ro_trace_composition_header_query_lists_zero_round:
  assumes zero: "ceil_log clength = 0"
  shows
    "ro_trace_composition_header_query_lists M
        fr [] trace_final as dg composition_roots composition_final =
      ro_actual_query_zero_round_trace_composition_good_query_lists
        (ro_trace_composition_header_data fr [] trace_final as dg
          composition_roots composition_final)
        (channel_for_hash_map M) (channel_for_hash_map M)"
  unfolding ro_trace_composition_header_query_lists_def
    ro_actual_query_zero_round_trace_composition_good_query_lists_def
    ro_actual_query_trace_composition_good_query_lists_def
    ro_actual_query_zero_round_trace_composition_accepted_query_lists_def
    ro_actual_query_trace_composition_accepted_query_lists_def
    ro_actual_query_zero_round_trace_composition_accepted_indices_def
    ro_actual_query_trace_composition_accepted_indices_def
    ro_actual_query_zero_round_trace_table_def
    trace_composition_header_trace_root_def
    first_trace_fri_root_prefix_first_table_def
    trace_composition_accepted_indices_def
    query_agreement_indices_def
    trace_table_base_agreement_indices_def
  by auto

lemma ro_trace_composition_header_query_lists_zero_round_card_bound:
  assumes zero: "ceil_log clength = 0"
  shows
    "card
      (ro_trace_composition_header_query_lists M
        fr [] trace_final as dg composition_roots composition_final)
      \<le> query_agreement_bound ^ rounds"
  unfolding ro_trace_composition_header_query_lists_zero_round[OF zero]
  by (rule
      ro_actual_query_zero_round_trace_composition_good_query_lists_card_bound)

lemma ro_trace_composition_header_query_lists_zero_round_position_card_bound:
  assumes zero: "ceil_log clength = 0"
    and i_bound: "i < rounds"
  shows
    "card
      (query_index_raw_list_position_values
        (ro_trace_composition_header_query_lists M
          fr [] trace_final as dg composition_roots composition_final)
        i)
      \<le> query_raw_preimage_card_envelope query_agreement_bound"
proof -
  let ?data =
    "ro_trace_composition_header_data fr [] trace_final as dg
      composition_roots composition_final"
  let ?Q =
    "ro_actual_query_zero_round_trace_composition_good_query_lists
      ?data (channel_for_hash_map M) (channel_for_hash_map M)"
  let ?indices =
    "ro_actual_query_zero_round_trace_composition_accepted_indices
      ?data (channel_for_hash_map M) (channel_for_hash_map M)"
  have Q_eq:
      "ro_trace_composition_header_query_lists M
          fr [] trace_final as dg composition_roots composition_final = ?Q"
    by (rule ro_trace_composition_header_query_lists_zero_round[OF zero])
  show ?thesis
  proof (cases
      "trace_table_low_degree
        (ro_actual_query_zero_round_trace_table
          ?data (channel_for_hash_map M)) \<and>
       composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate
          ?data (channel_for_hash_map M)) \<and>
       \<not> all_queries_consistent
        (ro_actual_query_zero_round_trace_table
          ?data (channel_for_hash_map M))
        (ro_actual_query_composition_candidate
          ?data (channel_for_hash_map M))
        (staged_alphas ?data)")
    case True
    have family_eq: "?Q = query_index_lists_over ?indices"
      unfolding
        ro_actual_query_zero_round_trace_composition_good_query_lists_def
        ro_actual_query_zero_round_trace_composition_accepted_query_lists_def
      using True by simp
    have pos_subset:
        "query_index_raw_list_position_values ?Q i
          \<subseteq> query_index_raw_preimage ?indices"
      unfolding family_eq
      by (rule
          query_index_raw_list_position_values_query_index_lists_over_subset[
            OF i_bound])
    have card_le:
        "card (query_index_raw_list_position_values ?Q i)
          \<le> card (query_index_raw_preimage ?indices)"
      by (rule card_mono[OF _ pos_subset]) simp
    have raw_card:
        "card (query_index_raw_preimage ?indices) \<le>
          query_raw_preimage_card_envelope (card ?indices)"
      by (rule card_query_index_raw_preimage_le_query_envelope)
        (rule
          ro_actual_query_zero_round_trace_composition_accepted_indices_subset)
    have indices_bound: "card ?indices \<le> query_agreement_bound"
      unfolding
        ro_actual_query_zero_round_trace_composition_accepted_indices_def
      by (rule query_agreement_indices_card_bound)
        (use True in blast)+
    have envelope_bound:
        "query_raw_preimage_card_envelope (card ?indices) \<le>
          query_raw_preimage_card_envelope query_agreement_bound"
      by (rule query_raw_preimage_card_envelope_mono[OF indices_bound])
    show ?thesis
      unfolding Q_eq
      by (rule order_trans[OF card_le])
        (rule order_trans[OF raw_card envelope_bound])
  next
    case False
    have Q_empty: "?Q = {}"
      unfolding
        ro_actual_query_zero_round_trace_composition_good_query_lists_def
      by (rule if_not_P) (use False in simp)
    show ?thesis
      unfolding Q_eq Q_empty query_index_raw_list_position_values_def
        query_index_raw_list_preimage_def
      by simp
  qed
qed

lemma trace_composition_query_index_bound_zero_round:
  assumes zero: "ceil_log clength = 0"
  shows
    "trace_composition_query_index_bound = query_agreement_bound"
proof -
  have powers_one: "powers = 1"
    by (rule ceil_log_clength_zero_imp_powers_one[OF zero])
  show ?thesis
    unfolding trace_composition_query_index_bound_def
    using powers_one
    by simp
qed

lemma trace_composition_absorbed_query_relation_zero_round_direct_fiber_card_bound:
  assumes zero: "ceil_log clength = 0"
  shows
    "card {y.
      hash_state_relation_direct_activation
        trace_composition_absorbed_query_relation M x y}
      \<le> query_raw_preimage_card_envelope query_agreement_bound"
  using trace_composition_absorbed_query_relation_direct_fiber_card_bound[
    of M x]
  unfolding trace_composition_query_index_bound_zero_round[OF zero]
  .

lemma wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_trace_composition_bounded_relation_zero_round:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  defines
    "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (trace_composition_absorbed_query_relation_bounded q)
          (HashMap adversary_initial_state))
        adversary_initial_state
      \<le>
      nnreal
        (q *
          (query_raw_preimage_card_envelope query_agreement_bound +
            (5 * q + 2))) /
        nnreal size"
  using
    wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_trace_composition_bounded_relation_all_rounds[
      OF wf controlled, folded q_def]
  unfolding trace_composition_query_index_bound_zero_round[OF zero]
  .

end
end
