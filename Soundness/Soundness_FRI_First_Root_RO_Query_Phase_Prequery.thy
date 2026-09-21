theory Soundness_FRI_First_Root_RO_Query_Phase_Prequery
  imports
    Stark.Soundness_FRI_First_Root_RO_Actual_Query_Product
    Stark.Controlled_RO_State_Relation
begin


context soundness
begin


lemma hash_relation_program_ro_checked_staged_query_program_with_witnesses_closed:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
    and trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots \<le> ceil_log (maxDegree + 1)"
  shows
    "hash_relation_program R b
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)
      (ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots query_state 0 rounds)"
proof (rule hash_relation_program_of_projection[
    where project="\<lambda>(raws, query_states, chunks). chunks"
      and n="ro_checked_staged_query_program A trace_roots
        composition_roots 0 rounds"])
  show
    "ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots query_state 0 rounds \<bind>
        (\<lambda>x. return (case x of
          (raws, query_states, chunks) \<Rightarrow> chunks)) =
      ro_checked_staged_query_program A trace_roots composition_roots 0 rounds"
    using ro_checked_staged_query_program_with_witnesses_projection[
      of A trace_roots composition_roots query_state 0 rounds]
    by (simp add: split_def)
  have len: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have exact:
    "hash_relation_program R b
      (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
        rounds + rounds * ro_checked_query_round_transcript_bound)
      (ro_checked_staged_query_program A trace_roots composition_roots
        0 rounds)"
    by (rule hash_relation_program_ro_checked_staged_query_program_closed[
          OF controlled len fibers trace_len composition_len])
  then show
    "hash_relation_program R b
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)
      (ro_checked_staged_query_program A trace_roots composition_roots
        0 rounds)"
    using wf unfolding staged_budget_wellformed_def by simp
qed

definition ro_checked_staged_first_root_query_phase_relation
  :: "'f staged_adversary \<Rightarrow> nat list set \<Rightarrow>
      ('f \<times> 'f list \<times> 'f) \<Rightarrow> 'f protocol_channel \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "ro_checked_staged_first_root_query_phase_relation
      A Q prefix prefix_state x y \<longleftrightarrow>
    (\<exists>data query_start raws query_states attacker_state j.
      Some (((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state) \<and>
      length raws = rounds \<and>
      length query_states = rounds \<and>
      map (\<lambda>raw. index (to_nat raw)) raws \<in> Q \<and>
      j < rounds \<and>
      fmlookup (HashMap (query_states ! j))
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) \<noteq> None \<and>
      x = QueryIndexChallenge
        (PQueryCounter (query_states ! j))
        (PState (query_states ! j)) \<and>
      y = raws ! j)"

lemma ro_checked_staged_first_root_query_phase_relation_fiber_card_bound:
  "card {y.
      ro_checked_staged_first_root_query_phase_relation
        A Q prefix prefix_state x y}
    \<le> query_index_raw_list_relation_fiber_bound Q"
proof -
  let ?values =
    "\<Union>i < rounds. query_index_raw_list_position_values Q i"
  have subset:
    "{y.
      ro_checked_staged_first_root_query_phase_relation
        A Q prefix prefix_state x y}
      \<subseteq> ?values"
    unfolding
      ro_checked_staged_first_root_query_phase_relation_def
      query_index_raw_list_position_values_def
      query_index_raw_list_preimage_def
    by blast
  have finite_values: "finite ?values"
    by simp
  have
    "card {y.
        ro_checked_staged_first_root_query_phase_relation
          A Q prefix prefix_state x y}
      \<le> card ?values"
    by (rule card_mono[OF finite_values subset])
  also have "... \<le>
      (\<Sum>i < rounds. card (query_index_raw_list_position_values Q i))"
    by (rule card_UN_le) simp
  also have "... = query_index_raw_list_relation_fiber_bound Q"
    unfolding query_index_raw_list_relation_fiber_bound_def
    by simp
  finally show ?thesis .
qed


definition ro_checked_staged_first_root_dependent_actual_query_index_list_hit
where
  "ro_checked_staged_first_root_dependent_actual_query_index_list_hit Q out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          Q prefix prefix_state)"

definition ro_checked_staged_first_root_dependent_query_start_prequery_hit
where
  "ro_checked_staged_first_root_dependent_query_start_prequery_hit Q out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          Q prefix prefix_state \<and>
        (\<exists>j < rounds.
          fmlookup (HashMap query_start)
            (QueryIndexChallenge
              (PQueryCounter (query_states ! j))
              (PState (query_states ! j))) =
            Some (raws ! j)))"

definition ro_checked_staged_first_root_dependent_query_phase_relation_hit
where
  "ro_checked_staged_first_root_dependent_query_phase_relation_hit A Q out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        hash_relation_hit
          (ro_checked_staged_first_root_query_phase_relation
            A (Q prefix prefix_state) prefix prefix_state)
          query_start attacker_state)"

lemma wp_ro_checked_staged_first_root_dependent_query_phase_relation_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and relation_fiber:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute (ro_checked_staged_first_root_query_head_program A) s)
        \<Longrightarrow>
        query_index_raw_list_relation_fiber_bound
          (Q prefix prefix_state) \<le> N"
    and trace_len:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute (ro_checked_staged_first_root_query_head_program A) s)
        \<Longrightarrow>
        length (staged_trace_fri_roots data) = ceil_log clength"
    and composition_len:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute (ro_checked_staged_first_root_query_head_program A) s)
        \<Longrightarrow>
        length (staged_composition_fri_roots data)
          \<le> ceil_log (maxDegree + 1)"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_checked_staged_first_root_dependent_query_phase_relation_hit A Q)
      s
    \<le> hash_relation_budget_value N
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)"
  unfolding
    ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
proof (rule wp_event_bind_output_state_dependent_relation_bound)
  show
    "\<not> ro_checked_staged_first_root_dependent_query_phase_relation_hit
      A Q None"
    unfolding
      ro_checked_staged_first_root_dependent_query_phase_relation_hit_def
    by simp
next
  fix x t out
  assume head:
    "Some (x, t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
    and tail:
      "out \<in>
        set_dist
          (execute
            (case x of
              (prefix_with_state, data, query_start) \<Rightarrow>
                ro_checked_staged_query_program_with_witnesses A
                    (staged_trace_fri_roots data)
                    (staged_composition_fri_roots data)
                    query_start 0 rounds \<bind>
                  (\<lambda>(raws, query_states, query_chunks).
                    return
                      (prefix_with_state,
                        data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                        query_start, raws, query_states)))
            t)"
    and event:
      "ro_checked_staged_first_root_dependent_query_phase_relation_hit
        A Q out"
  obtain prefix prefix_state data query_start where x_eq:
    "x = ((prefix, prefix_state), data, query_start)"
    by (cases x) (auto split: prod.splits)
  have t_eq: "t = query_start"
    by (rule ro_checked_staged_first_root_query_head_program_state)
      (use head x_eq in simp)
  have out_some: "out \<noteq> None"
    using event
    unfolding
      ro_checked_staged_first_root_dependent_query_phase_relation_hit_def
    by (cases out) auto
  obtain result attacker_state where out_pair:
    "out = Some (result, attacker_state)"
    using out_some by (cases out) auto
  obtain raws query_states query_chunks where out_eq:
    "out =
      Some
        (((prefix, prefix_state),
          data\<lparr>staged_query_chunks := query_chunks\<rparr>,
          query_start, raws, query_states),
        attacker_state)"
    using tail out_pair
    unfolding x_eq t_eq
    by (auto elim!: set_dist_bindE split: prod.splits)
  show
    "hash_relation_hit_event
      (case x of
        (prefix_with_state, data, query_start) \<Rightarrow>
          case prefix_with_state of
            (prefix, prefix_state) \<Rightarrow>
              ro_checked_staged_first_root_query_phase_relation
                A (Q prefix prefix_state) prefix prefix_state)
      t out"
    using event
    unfolding x_eq t_eq out_eq
      ro_checked_staged_first_root_dependent_query_phase_relation_hit_def
      hash_relation_hit_event_def
    by simp
next
  fix x t
  assume head:
    "Some (x, t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  obtain prefix prefix_state data query_start where x_eq:
    "x = ((prefix, prefix_state), data, query_start)"
    by (cases x) (auto split: prod.splits)
  have head':
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
    using head unfolding x_eq .
  have fibers:
    "\<And>x. card {y.
      ro_checked_staged_first_root_query_phase_relation
        A (Q prefix prefix_state) prefix prefix_state x y} \<le> N"
  proof -
    fix x
    have
      "card {y.
          ro_checked_staged_first_root_query_phase_relation
            A (Q prefix prefix_state) prefix prefix_state x y}
        \<le> query_index_raw_list_relation_fiber_bound
          (Q prefix prefix_state)"
      by (rule
          ro_checked_staged_first_root_query_phase_relation_fiber_card_bound)
    also have "... \<le> N"
      by (rule relation_fiber[OF head'])
    finally show
      "card {y.
        ro_checked_staged_first_root_query_phase_relation
          A (Q prefix prefix_state) prefix prefix_state x y} \<le> N" .
  qed
  let ?R =
    "ro_checked_staged_first_root_query_phase_relation
      A (Q prefix prefix_state) prefix prefix_state"
  let ?q =
    "sum_list (query_opening_budgets budgets) + rounds +
      rounds * ro_checked_query_round_transcript_bound"
  have base:
    "hash_relation_program ?R N ?q
      (ro_checked_staged_query_program_with_witnesses A
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        query_start 0 rounds)"
    by (rule
        hash_relation_program_ro_checked_staged_query_program_with_witnesses_closed[
          OF wf controlled fibers trace_len[OF head']
            composition_len[OF head']])
  have mapped:
    "hash_relation_program ?R N (?q + 0)
      (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          return
            ((prefix, prefix_state),
              data\<lparr>staged_query_chunks := query_chunks\<rparr>,
              query_start, raws, query_states)))"
  proof (rule hash_relation_program_bind)
    show
      "hash_relation_program ?R N ?q
        (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds)"
      by (rule base)
  next
    fix packed ::
      "'f list \<times> 'f protocol_channel list \<times> 'f list list"
    show
      "hash_relation_program ?R N 0
        (case packed of
          (raws, query_states, query_chunks) \<Rightarrow>
            return
              ((prefix, prefix_state),
                data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                query_start, raws, query_states))"
      by (cases packed)
        (simp add:
          hash_relation_program_zero[OF hash_map_preserving_return]
          split: prod.splits)
  qed
  show
    "hash_relation_program
      (case x of
        (prefix_with_state, data, query_start) \<Rightarrow>
          case prefix_with_state of
            (prefix, prefix_state) \<Rightarrow>
              ro_checked_staged_first_root_query_phase_relation
                A (Q prefix prefix_state) prefix prefix_state)
      N
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)
      (case x of
        (prefix_with_state, data, query_start) \<Rightarrow>
          ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data)
              query_start 0 rounds \<bind>
            (\<lambda>(raws, query_states, query_chunks).
              return
                (prefix_with_state,
                  data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                  query_start, raws, query_states)))"
    using mapped
    unfolding x_eq
    by simp
qed



lemma ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            s)"
  shows
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
proof -
  obtain head_data head_state query_chunks where
    head:
      "Some (((prefix, prefix_state), head_data, query_start), head_state) \<in>
        set_dist
          (execute (ro_checked_staged_first_root_query_head_program A) s)"
    and tail:
      "Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots head_data)
              (staged_composition_fri_roots head_data)
              query_start 0 rounds)
            head_state)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    using outcome
    unfolding
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have head_state_eq: "head_state = query_start"
    by (rule ro_checked_staged_first_root_query_head_program_state[OF head])
  have bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have props:
    "length raws = rounds \<and>
     length query_states = rounds \<and>
     length query_chunks = rounds \<and>
     query_start \<le> attacker_state \<and>
     PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
     (\<forall>j < rounds.
       query_states ! j \<le> attacker_state \<and>
       PQueryCounter (query_states ! j) = PQueryCounter query_start + j \<and>
       fmlookup (HashMap attacker_state)
         (QueryIndexChallenge
           (PQueryCounter (query_states ! j))
           (PState (query_states ! j))) =
         Some (raws ! j) \<and>
       verifier_query_round_chunk (index (to_nat (raws ! j)))
         (staged_trace_fri_roots head_data)
         (staged_composition_fri_roots head_data)
         (query_chunks ! j)) \<and>
     (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
    by (rule ro_checked_staged_query_program_with_witnesses_outcome[
          OF controlled bound])
      (use tail head_state_eq in simp)
  show ?thesis
    using props data_eq by auto
qed


lemma ro_checked_staged_first_root_dependent_actual_query_index_list_hit_imp_fresh_or_prequery_or_query_phase_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and actual:
      "ro_checked_staged_first_root_dependent_actual_query_index_list_hit Q
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
  shows
    "ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state))) \<or>
     ro_checked_staged_first_root_dependent_query_start_prequery_hit Q
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state))) \<or>
     ro_checked_staged_first_root_dependent_query_phase_relation_hit A Q
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
proof -
  have props:
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
  have len_raws: "length raws = rounds"
    using props by blast
  have len_states: "length query_states = rounds"
    using props by blast
  have len_chunks: "length (staged_query_chunks data) = rounds"
    using props by blast
  have extension: "query_start \<le> attacker_state"
    using props by blast
  have final_lookups:
    "\<And>j. j < rounds \<Longrightarrow>
      fmlookup (HashMap attacker_state)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raws ! j)"
    using props by blast
  have query_in: "map (\<lambda>raw. index (to_nat raw)) raws \<in> Q prefix prefix_state"
    using actual
    unfolding
      ro_checked_staged_first_root_dependent_actual_query_index_list_hit_def
    by simp
  show ?thesis
  proof (cases
      "\<forall>j < rounds.
        fmlookup (HashMap (query_states ! j))
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) = None")
    case True
    have raw_in:
      "raws \<in> query_index_raw_list_preimage (Q prefix prefix_state)"
      unfolding query_index_raw_list_preimage_def
      using len_raws query_in by blast
    have raw_fresh:
      "ro_query_witnesses_raws_fresh_hit raws
        (Some ((raws, query_states, staged_query_chunks data),
          attacker_state))"
      unfolding ro_query_witnesses_raws_fresh_hit_def
      using len_raws len_states len_chunks True by simp
    have list_fresh:
      "ro_query_witnesses_query_index_list_fresh_hit
        (Q prefix prefix_state)
        (Some ((raws, query_states, staged_query_chunks data),
          attacker_state))"
      by (rule ro_query_witnesses_query_index_list_fresh_hitI[
            OF raw_in raw_fresh])
    show ?thesis
      unfolding
        ro_checked_staged_first_root_dependent_query_index_list_fresh_hit_def
      using list_fresh by simp
  next
    case False
    then obtain j where
      j_bound: "j < rounds"
      and nonfresh:
        "fmlookup (HashMap (query_states ! j))
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) \<noteq> None"
      by blast
    let ?key =
      "QueryIndexChallenge
        (PQueryCounter (query_states ! j))
        (PState (query_states ! j))"
    have final_lookup:
      "fmlookup (HashMap attacker_state) ?key = Some (raws ! j)"
      by (rule final_lookups[OF j_bound])
    show ?thesis
    proof (cases "fmlookup (HashMap query_start) ?key")
      case None
      have relation:
        "ro_checked_staged_first_root_query_phase_relation
          A (Q prefix prefix_state) prefix prefix_state ?key (raws ! j)"
        unfolding ro_checked_staged_first_root_query_phase_relation_def
        using outcome len_raws len_states query_in j_bound nonfresh
        by blast
      have relation_hit:
        "hash_relation_hit
          (ro_checked_staged_first_root_query_phase_relation
            A (Q prefix prefix_state) prefix prefix_state)
          query_start attacker_state"
        unfolding hash_relation_hit_def
        using None final_lookup relation by blast
      have event_hit:
        "ro_checked_staged_first_root_dependent_query_phase_relation_hit A Q
          (Some ((((prefix, prefix_state), data, query_start, raws,
            query_states), attacker_state)))"
        unfolding
          ro_checked_staged_first_root_dependent_query_phase_relation_hit_def
        using relation_hit by simp
      show ?thesis
        using event_hit by blast
    next
      case (Some old_raw)
      have old_final:
        "fmlookup (HashMap attacker_state) ?key = Some old_raw"
        by (rule hash_extension_lookup[OF Some extension])
      have old_eq: "old_raw = raws ! j"
        using old_final final_lookup by simp
      have prequery:
        "ro_checked_staged_first_root_dependent_query_start_prequery_hit Q
          (Some ((((prefix, prefix_state), data, query_start, raws,
            query_states), attacker_state)))"
        unfolding
          ro_checked_staged_first_root_dependent_query_start_prequery_hit_def
        using query_in j_bound Some old_eq by auto
      show ?thesis
        using prequery by blast
    qed
  qed
qed


lemma wp_ro_checked_staged_first_root_dependent_actual_query_index_list_hit_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (ro_checked_staged_first_root_dependent_actual_query_index_list_hit Q)
        adversary_initial_state
      \<le>
      wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q)
          adversary_initial_state +
        wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_checked_staged_first_root_dependent_query_start_prequery_hit Q)
          adversary_initial_state +
        wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_checked_staged_first_root_dependent_query_phase_relation_hit A Q)
          adversary_initial_state"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Actual =
    "ro_checked_staged_first_root_dependent_actual_query_index_list_hit Q"
  let ?Fresh =
    "ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q"
  let ?Prequery =
    "ro_checked_staged_first_root_dependent_query_start_prequery_hit Q"
  let ?Relation =
    "ro_checked_staged_first_root_dependent_query_phase_relation_hit A Q"
  have event_le:
    "wp_event ?M ?Actual adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?Fresh out \<or> ?Prequery out \<or> ?Relation out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and actual: "?Actual out"
    show "?Fresh out \<or> ?Prequery out \<or> ?Relation out"
    proof (cases out)
      case None
      then show ?thesis
        using actual
        unfolding
          ro_checked_staged_first_root_dependent_actual_query_index_list_hit_def
        by simp
    next
      case (Some packed)
      obtain prefix prefix_state data query_start raws query_states
          attacker_state where packed_eq:
        "packed =
          (((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state)"
        by (cases packed) (auto split: prod.splits)
      have outcome':
        "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state)) \<in>
          set_dist (execute ?M adversary_initial_state)"
        using support unfolding Some packed_eq .
      have actual':
        "?Actual
          (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state)))"
        using actual unfolding Some packed_eq .
      have split:
        "?Fresh
            (Some ((((prefix, prefix_state), data, query_start, raws,
              query_states), attacker_state))) \<or>
         ?Prequery
            (Some ((((prefix, prefix_state), data, query_start, raws,
              query_states), attacker_state))) \<or>
         ?Relation
            (Some ((((prefix, prefix_state), data, query_start, raws,
              query_states), attacker_state)))"
        by (rule
            ro_checked_staged_first_root_dependent_actual_query_index_list_hit_imp_fresh_or_prequery_or_query_phase_relation[
              OF wf controlled outcome' actual'])
      show ?thesis
        using split unfolding Some packed_eq .
    qed
  qed
  have union_tail:
    "wp_event ?M (\<lambda>out. ?Prequery out \<or> ?Relation out)
        adversary_initial_state
      \<le> wp_event ?M ?Prequery adversary_initial_state +
        wp_event ?M ?Relation adversary_initial_state"
    by (rule wp_event_union_bound)
  have union_all:
    "wp_event ?M (\<lambda>out. ?Fresh out \<or> ?Prequery out \<or> ?Relation out)
        adversary_initial_state
      \<le> wp_event ?M ?Fresh adversary_initial_state +
        wp_event ?M (\<lambda>out. ?Prequery out \<or> ?Relation out)
          adversary_initial_state"
    by (rule wp_event_union_bound)
  have combined:
    "wp_event ?M (\<lambda>out. ?Fresh out \<or> ?Prequery out \<or> ?Relation out)
        adversary_initial_state
      \<le> wp_event ?M ?Fresh adversary_initial_state +
          wp_event ?M ?Prequery adversary_initial_state +
          wp_event ?M ?Relation adversary_initial_state"
  proof (rule order_trans[OF union_all])
    show
      "wp_event ?M ?Fresh adversary_initial_state +
          wp_event ?M (\<lambda>out. ?Prequery out \<or> ?Relation out)
            adversary_initial_state
        \<le> wp_event ?M ?Fresh adversary_initial_state +
          wp_event ?M ?Prequery adversary_initial_state +
          wp_event ?M ?Relation adversary_initial_state"
      using union_tail by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF event_le combined])
qed

end
end
