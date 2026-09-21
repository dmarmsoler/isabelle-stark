(*  Title:      Stark/Soundness_FRI_First_Root_RO_Prequery_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Prequery_Bound
  imports Soundness_FRI_First_Root_RO_Prequery_Bridge
begin

text \<open>
  Parameter-facing closure of the first-root query split.  The prefix-selected
  agreement family is empty unless both conceptual tables are low degree and
  distinct, so its exact product and relation-fiber bounds are unconditional.
\<close>

context soundness
begin

definition first_trace_fri_root_prefix_good_agreement_query_lists
  :: "('f \<times> 'f list \<times> 'f) \<Rightarrow> 'f protocol_channel \<Rightarrow> nat list set"
where
  "first_trace_fri_root_prefix_good_agreement_query_lists prefix prefix_state =
    (if
      trace_table_low_degree
        (first_trace_fri_root_prefix_trace_table prefix prefix_state) \<and>
      trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
      first_trace_fri_root_prefix_trace_table prefix prefix_state \<noteq>
        first_trace_fri_root_prefix_first_table prefix prefix_state
     then first_trace_fri_root_prefix_base_agreement_query_lists
       prefix prefix_state
     else {})"

lemma first_trace_fri_root_prefix_good_agreement_query_lists_memberD:
  assumes member:
    "xs \<in> first_trace_fri_root_prefix_good_agreement_query_lists
      prefix prefix_state"
  shows
    "trace_table_low_degree
        (first_trace_fri_root_prefix_trace_table prefix prefix_state) \<and>
      trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
      first_trace_fri_root_prefix_trace_table prefix prefix_state \<noteq>
        first_trace_fri_root_prefix_first_table prefix prefix_state \<and>
      xs \<in> first_trace_fri_root_prefix_base_agreement_query_lists
        prefix prefix_state"
  using member
  unfolding first_trace_fri_root_prefix_good_agreement_query_lists_def
  by (auto split: if_splits)

lemma first_trace_fri_root_prefix_good_agreement_query_lists_subset:
  "first_trace_fri_root_prefix_good_agreement_query_lists
      prefix prefix_state
    \<subseteq> fri_query_index_list_space"
  unfolding first_trace_fri_root_prefix_good_agreement_query_lists_def
  using first_trace_fri_root_prefix_base_agreement_query_lists_subset[
    of prefix prefix_state]
  by auto

lemma first_trace_fri_root_prefix_good_agreement_query_lists_card_bound:
  "card
      (first_trace_fri_root_prefix_good_agreement_query_lists
        prefix prefix_state)
    \<le> clength ^ rounds"
  unfolding first_trace_fri_root_prefix_good_agreement_query_lists_def
  by (auto intro:
    first_trace_fri_root_prefix_base_agreement_query_lists_card_bound)

lemma first_trace_fri_root_prefix_good_agreement_relation_fiber_bound:
  "query_index_raw_list_relation_fiber_bound
      (first_trace_fri_root_prefix_good_agreement_query_lists
        prefix prefix_state)
    \<le> rounds * query_raw_preimage_card_envelope clength"
proof -
  let ?good =
    "trace_table_low_degree
        (first_trace_fri_root_prefix_trace_table prefix prefix_state) \<and>
      trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
      first_trace_fri_root_prefix_trace_table prefix prefix_state \<noteq>
        first_trace_fri_root_prefix_first_table prefix prefix_state"
  show ?thesis
  proof (cases ?good)
    case True
    have family_eq:
      "first_trace_fri_root_prefix_good_agreement_query_lists
          prefix prefix_state =
        first_trace_fri_root_prefix_base_agreement_query_lists
          prefix prefix_state"
      using True
      unfolding first_trace_fri_root_prefix_good_agreement_query_lists_def
      by simp
    show ?thesis
      unfolding family_eq
      by (rule
        first_trace_fri_root_prefix_base_agreement_relation_fiber_bound)
        (use True in blast)+
  next
    case False
    have not_good:
      "\<not> (trace_table_low_degree
          (first_trace_fri_root_prefix_trace_table prefix prefix_state) \<and>
        trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
        first_trace_fri_root_prefix_trace_table prefix prefix_state \<noteq>
          first_trace_fri_root_prefix_first_table prefix prefix_state)"
      using False by blast
    have family_eq:
      "first_trace_fri_root_prefix_good_agreement_query_lists
          prefix prefix_state = {}"
      unfolding first_trace_fri_root_prefix_good_agreement_query_lists_def
      by (rule if_not_P[OF not_good])
    show ?thesis
      unfolding family_eq query_index_raw_list_relation_fiber_bound_def
        query_index_raw_list_position_values_def
        query_index_raw_list_preimage_def
      by simp
  qed
qed

lemma wp_ro_checked_staged_transcript_program_with_first_root_good_agreement_fresh_bound:
  "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_checked_staged_first_root_dependent_query_index_list_fresh_hit
        first_trace_fri_root_prefix_good_agreement_query_lists)
      s
    \<le> nnreal (clength ^ rounds) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof (rule
    wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_dependent_fresh_bound)
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  show
    "first_trace_fri_root_prefix_good_agreement_query_lists
        prefix prefix_state
      \<subseteq> fri_query_index_list_space"
    by (rule first_trace_fri_root_prefix_good_agreement_query_lists_subset)
next
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  show
    "card
        (first_trace_fri_root_prefix_good_agreement_query_lists
          prefix prefix_state)
      \<le> clength ^ rounds"
    by (rule first_trace_fri_root_prefix_good_agreement_query_lists_card_bound)
qed


definition ro_checked_staged_first_root_prefix_merkle_target_hit
where
  "ro_checked_staged_first_root_prefix_merkle_target_hit out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        hash_map_new_output_hit
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
          prefix_state attacker_state)"

lemma ro_checked_staged_first_root_good_prequery_some_imp_side_event:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and prequery:
      "ro_checked_staged_first_root_dependent_query_start_prequery_hit
        first_trace_fri_root_prefix_good_agreement_query_lists
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
  shows
    "final_hash_collision_event
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state))) \<or>
      hash_new_output_hit_event {PState adversary_initial_state}
        adversary_initial_state
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state))) \<or>
      ro_checked_staged_first_root_prefix_merkle_target_hit
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state))) \<or>
      hash_state_relation_transition_event
        (first_root_absorbed_query_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets))
        (HashMap adversary_initial_state)
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
proof -
  have member:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
      first_trace_fri_root_prefix_good_agreement_query_lists
        prefix prefix_state"
    using prequery
    unfolding
      ro_checked_staged_first_root_dependent_query_start_prequery_hit_def
    by simp
  have fields:
    "trace_table_low_degree
        (first_trace_fri_root_prefix_trace_table prefix prefix_state) \<and>
      trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
      first_trace_fri_root_prefix_trace_table prefix prefix_state \<noteq>
        first_trace_fri_root_prefix_first_table prefix prefix_state \<and>
      map (\<lambda>raw. index (to_nat raw)) raws \<in>
        first_trace_fri_root_prefix_base_agreement_query_lists
          prefix prefix_state"
    by (rule
      first_trace_fri_root_prefix_good_agreement_query_lists_memberD[OF member])
  have base_prequery:
    "ro_checked_staged_first_root_dependent_query_start_prequery_hit
      first_trace_fri_root_prefix_base_agreement_query_lists
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
    using prequery fields
    unfolding
      ro_checked_staged_first_root_dependent_query_start_prequery_hit_def
    by simp
  show ?thesis
  proof (cases "hash_map_output_collision attacker_state")
    case True
    then show ?thesis
      unfolding final_hash_collision_event_def by simp
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
        unfolding hash_new_output_hit_event_def by simp
    next
      case no_initial: False
      show ?thesis
      proof (cases
          "hash_map_new_output_hit
            (first_trace_fri_root_prefix_merkle_targets
              prefix prefix_state)
            prefix_state attacker_state")
        case True
        then show ?thesis
          unfolding
            ro_checked_staged_first_root_prefix_merkle_target_hit_def
          by simp
      next
        case no_merkle: False
        have relation:
          "hash_state_relation_transition
            (first_root_absorbed_query_relation_bounded
              (ro_checked_staged_transcript_hash_query_budget_for budgets))
            (HashMap adversary_initial_state)
            (HashMap attacker_state)"
          by (rule first_root_prequery_good_imp_budgeted_relation_transition[
            OF wf controlled nonempty outcome base_prequery
              conjunct1[OF fields]
              conjunct1[OF conjunct2[OF fields]]
              conjunct1[OF conjunct2[OF conjunct2[OF fields]]]
              clean no_initial no_merkle])
        then show ?thesis
          unfolding hash_state_relation_transition_event_def by simp
      qed
    qed
  qed
qed


lemma ro_checked_staged_transcript_program_with_first_root_final_state_event:

  assumes nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t)
        s =
      wp_event
        (ro_checked_staged_transcript_program A)
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t)
        s"
proof -
  let ?enriched =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?witnesses =
    "ro_checked_staged_transcript_program_with_query_witnesses A"
  let ?first =
    "\<lambda>(prefix_with_state, data, query_start, raws, query_states).
      return (data, query_start, raws, query_states)"
  let ?second =
    "\<lambda>(data, query_start, raws, query_states). return data"
  have first: "?enriched \<bind> ?first = ?witnesses"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_projection[
        OF nonempty])
  have second:
    "?witnesses \<bind> ?second = ro_checked_staged_transcript_program A"
    by (rule
      ro_checked_staged_transcript_program_with_query_witnesses_projection)
  have projection:
    "?enriched \<bind>
        (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
          return data) =
      ro_checked_staged_transcript_program A"
  proof -
    have
      "?enriched \<bind>
          (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
            return data) =
        (?enriched \<bind> ?first) \<bind> ?second"
      by (simp add: sm_bind_assoc split_def)
    also have "... = ?witnesses \<bind> ?second"
      by (simp only: first)
    also have "... = ro_checked_staged_transcript_program A"
      by (rule second)
    finally show ?thesis .
  qed
  have event_map:
    "(\<lambda>out. case out of
        None \<Rightarrow> False
      | Some
          ((((prefix, prefix_state), data, query_start, raws, query_states), t)) \<Rightarrow>
          P t) =
      (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t)"
    by (rule ext) (auto split: option.splits prod.splits)
  have
    "wp_event
        (ro_checked_staged_transcript_program A)
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t)
        s =
      wp_event
        (?enriched \<bind>
          (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
            return data))
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t)
        s"
    using projection by simp
  also have "... =
      wp_event ?enriched
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t) s"
  proof -
    let ?E = "\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t"
    have map_eq:
      "(\<lambda>(prefix_with_state, data, query_start, raws, query_states).
          return data) =
        (\<lambda>x. return (fst (snd x)))"
      by (rule ext) (auto split: prod.splits)
    have exact:
      "wp_event
          (?enriched \<bind>
            (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
              return data))
          ?E s =
        wp_event ?enriched
          (\<lambda>out. case out of
            None \<Rightarrow> ?E None
          | Some (x, t) \<Rightarrow> ?E (Some (fst (snd x), t)))
          s"
      unfolding map_eq
      by (simp add: wp_event_bind_return_map split: option.splits prod.splits)
    have pred_eq:
      "(\<lambda>out. case out of
          None \<Rightarrow> ?E None
        | Some (x, t) \<Rightarrow> ?E (Some (fst (snd x), t))) = ?E"
      by (rule ext) (auto split: option.splits prod.splits)
    show ?thesis
      using exact unfolding pred_eq .
  qed
  finally show ?thesis by simp
qed


lemma ro_checked_staged_transcript_program_with_first_root_final_state_event_all_rounds:
  "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t)
      s =
    wp_event
      (ro_checked_staged_transcript_program A)
      (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t)
      s"
proof -
  let ?enriched =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?witnesses =
    "ro_checked_staged_transcript_program_with_query_witnesses A"
  let ?first =
    "\<lambda>(prefix_with_state, data, query_start, raws, query_states).
      return (data, query_start, raws, query_states)"
  let ?second =
    "\<lambda>(data, query_start, raws, query_states). return data"
  have first: "?enriched \<bind> ?first = ?witnesses"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_projection_all_rounds)
  have second:
    "?witnesses \<bind> ?second = ro_checked_staged_transcript_program A"
    by (rule
      ro_checked_staged_transcript_program_with_query_witnesses_projection)
  have projection:
    "?enriched \<bind>
        (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
          return data) =
      ro_checked_staged_transcript_program A"
  proof -
    have
      "?enriched \<bind>
          (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
            return data) =
        (?enriched \<bind> ?first) \<bind> ?second"
      by (simp add: sm_bind_assoc split_def)
    also have "... = ?witnesses \<bind> ?second"
      by (simp only: first)
    also have "... = ro_checked_staged_transcript_program A"
      by (rule second)
    finally show ?thesis .
  qed
  have event_map:
    "(\<lambda>out. case out of
        None \<Rightarrow> False
      | Some
          ((((prefix, prefix_state), data, query_start, raws, query_states), t)) \<Rightarrow>
          P t) =
      (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t)"
    by (rule ext) (auto split: option.splits prod.splits)
  have
    "wp_event
        (ro_checked_staged_transcript_program A)
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t)
        s =
      wp_event
        (?enriched \<bind>
          (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
            return data))
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t)
        s"
    using projection by simp
  also have "... =
      wp_event ?enriched
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t) s"
  proof -
    let ?E = "\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow> P t"
    have map_eq:
      "(\<lambda>(prefix_with_state, data, query_start, raws, query_states).
          return data) =
        (\<lambda>x. return (fst (snd x)))"
      by (rule ext) (auto split: prod.splits)
    have exact:
      "wp_event
          (?enriched \<bind>
            (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
              return data))
          ?E s =
        wp_event ?enriched
          (\<lambda>out. case out of
            None \<Rightarrow> ?E None
          | Some (x, t) \<Rightarrow> ?E (Some (fst (snd x), t)))
          s"
      unfolding map_eq
      by (simp add: wp_event_bind_return_map split: option.splits prod.splits)
    have pred_eq:
      "(\<lambda>out. case out of
          None \<Rightarrow> ?E None
        | Some (x, t) \<Rightarrow> ?E (Some (fst (snd x), t))) = ?E"
      by (rule ext) (auto split: option.splits prod.splits)
    show ?thesis
      using exact unfolding pred_eq .
  qed
  finally show ?thesis by simp
qed


lemma wp_ro_checked_staged_transcript_program_with_first_root_collision_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        final_hash_collision_event
        adversary_initial_state
      \<le> hash_collision_budget_value 0 q"
proof -
  have projection:
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        final_hash_collision_event
        adversary_initial_state =
      wp_event
        (ro_checked_staged_transcript_program A)
        final_hash_collision_event
        adversary_initial_state"
    using
      ro_checked_staged_transcript_program_with_first_root_final_state_event[
        OF nonempty, where P=hash_map_output_collision]
    unfolding final_hash_collision_event_def
    by simp
  have budget:
    "hash_collision_budget q
      (ro_checked_staged_transcript_program A)"
    unfolding q_def
    by (rule hash_collision_budget_ro_checked_staged_transcript_program[
      OF wf controlled])
  have base:
    "wp_event
        (ro_checked_staged_transcript_program A)
        (hash_new_collision_event adversary_initial_state)
        adversary_initial_state
      \<le> hash_collision_budget_value
          (card (hash_map_output_values adversary_initial_state)) q"
    using budget adversary_initial_state_no_output_collision
    unfolding hash_collision_budget_def
    by blast
  have original:
    "wp_event
        (ro_checked_staged_transcript_program A)
        final_hash_collision_event
        adversary_initial_state
      \<le> hash_collision_budget_value 0 q"
    using base
    unfolding final_hash_collision_event_def hash_new_collision_event_def
      hash_map_new_output_collision_def
    by simp
  show ?thesis
    using projection original by simp
qed

lemma wp_ro_checked_staged_transcript_program_with_first_root_collision_bound_all_rounds:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        final_hash_collision_event
        adversary_initial_state
      \<le> hash_collision_budget_value 0 q"
proof -
  have projection:
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        final_hash_collision_event
        adversary_initial_state =
      wp_event
        (ro_checked_staged_transcript_program A)
        final_hash_collision_event
        adversary_initial_state"
    using
      ro_checked_staged_transcript_program_with_first_root_final_state_event_all_rounds[
        where P=hash_map_output_collision]
    unfolding final_hash_collision_event_def
    by simp
  have budget:
    "hash_collision_budget q
      (ro_checked_staged_transcript_program A)"
    unfolding q_def
    by (rule hash_collision_budget_ro_checked_staged_transcript_program[
      OF wf controlled])
  have base:
    "wp_event
        (ro_checked_staged_transcript_program A)
        (hash_new_collision_event adversary_initial_state)
        adversary_initial_state
      \<le> hash_collision_budget_value
          (card (hash_map_output_values adversary_initial_state)) q"
    using budget adversary_initial_state_no_output_collision
    unfolding hash_collision_budget_def
    by blast
  have original:
    "wp_event
        (ro_checked_staged_transcript_program A)
        final_hash_collision_event
        adversary_initial_state
      \<le> hash_collision_budget_value 0 q"
    using base
    unfolding final_hash_collision_event_def hash_new_collision_event_def
      hash_map_new_output_collision_def
    by simp
  show ?thesis
    using projection original by simp
qed


lemma wp_ro_checked_staged_transcript_program_with_first_root_initial_target_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state)
        adversary_initial_state
      \<le> nnreal q / nnreal size"
proof -
  have state_projection:
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow>
          hash_map_new_output_hit {PState adversary_initial_state}
            adversary_initial_state t)
        adversary_initial_state =
      wp_event
        (ro_checked_staged_transcript_program A)
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow>
          hash_map_new_output_hit {PState adversary_initial_state}
            adversary_initial_state t)
        adversary_initial_state"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_final_state_event[
        OF nonempty])
  have projection:
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state)
        adversary_initial_state =
      wp_event
        (ro_checked_staged_transcript_program A)
        (hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state)
        adversary_initial_state"
    using state_projection
    unfolding hash_new_output_hit_event_def .
  have program:
    "hash_target_program {PState adversary_initial_state} q
      (ro_checked_staged_transcript_program A)"
    unfolding q_def
    by (rule hash_target_program_ro_checked_staged_transcript_program[
      OF wf controlled])
  have original:
    "wp_event
        (ro_checked_staged_transcript_program A)
        (hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state)
        adversary_initial_state
      \<le> hash_target_budget_value {PState adversary_initial_state} q"
    using program
    unfolding hash_target_program_def hash_target_budget_def
    by blast
  show ?thesis
    using projection original
    unfolding hash_target_budget_value_def
    by simp
qed

lemma wp_ro_checked_staged_transcript_program_with_first_root_initial_target_bound_all_rounds:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state)
        adversary_initial_state
      \<le> nnreal q / nnreal size"
proof -
  have state_projection:
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow>
          hash_map_new_output_hit {PState adversary_initial_state}
            adversary_initial_state t)
        adversary_initial_state =
      wp_event
        (ro_checked_staged_transcript_program A)
        (\<lambda>out. case out of None \<Rightarrow> False | Some (_, t) \<Rightarrow>
          hash_map_new_output_hit {PState adversary_initial_state}
            adversary_initial_state t)
        adversary_initial_state"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_final_state_event_all_rounds)
  have projection:
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state)
        adversary_initial_state =
      wp_event
        (ro_checked_staged_transcript_program A)
        (hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state)
        adversary_initial_state"
    using state_projection
    unfolding hash_new_output_hit_event_def .
  have program:
    "hash_target_program {PState adversary_initial_state} q
      (ro_checked_staged_transcript_program A)"
    unfolding q_def
    by (rule hash_target_program_ro_checked_staged_transcript_program[
      OF wf controlled])
  have original:
    "wp_event
        (ro_checked_staged_transcript_program A)
        (hash_new_output_hit_event {PState adversary_initial_state}
          adversary_initial_state)
        adversary_initial_state
      \<le> hash_target_budget_value {PState adversary_initial_state} q"
    using program
    unfolding hash_target_program_def hash_target_budget_def
    by blast
  show ?thesis
    using projection original
    unfolding hash_target_budget_value_def
    by simp
qed


end
end
