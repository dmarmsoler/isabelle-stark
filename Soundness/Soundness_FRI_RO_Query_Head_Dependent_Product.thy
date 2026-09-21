theory Soundness_FRI_RO_Query_Head_Dependent_Product
  imports Soundness_FRI_RO_Actual_Query_Trace_Composition_Boundary
begin

context soundness
begin

definition ro_query_head_data
where
  "ro_query_head_data data =
    data\<lparr>staged_query_chunks := []\<rparr>"

lemma ro_checked_staged_first_root_query_head_program_query_chunks:
  assumes outcome:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  shows "staged_query_chunks data = []"
  using outcome
  unfolding ro_checked_staged_first_root_query_head_program_def
    ro_checked_staged_after_first_trace_fri_root_prefix_program_def
  by (auto simp: Let_def elim!: set_dist_bindE
      split: prod.splits nat.splits)

lemma ro_query_head_data_of_query_head_outcome:
  assumes outcome:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  shows "ro_query_head_data data = data"
  using ro_checked_staged_first_root_query_head_program_query_chunks[OF outcome]
  unfolding ro_query_head_data_def
  by simp

lemma ro_query_head_data_update_query_chunks[simp]:
  "ro_query_head_data (data\<lparr>staged_query_chunks := chunks\<rparr>) =
    ro_query_head_data data"
  unfolding ro_query_head_data_def by simp

definition
  ro_query_head_dependent_query_index_list_fresh_hit
where
  "ro_query_head_dependent_query_index_list_fresh_hit Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        ro_query_witnesses_query_index_list_fresh_hit
          (Q prefix prefix_state (ro_query_head_data data) query_start)
          (Some ((raws, query_states, staged_query_chunks data),
            attacker_state)))"

lemma
  ro_query_head_dependent_query_index_list_fresh_hit_None[simp]:
  "\<not> ro_query_head_dependent_query_index_list_fresh_hit Q None"
  unfolding
    ro_query_head_dependent_query_index_list_fresh_hit_def
  by simp


lemma
  wp_ro_checked_staged_transcript_query_head_dependent_fresh_bound:
  assumes subset:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute (ro_checked_staged_first_root_query_head_program A) s) \<Longrightarrow>
        Q prefix prefix_state data query_start \<subseteq> fri_query_index_list_space"
    and card_bound:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute (ro_checked_staged_first_root_query_head_program A) s) \<Longrightarrow>
        card (Q prefix prefix_state data query_start) \<le> N"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_query_index_list_fresh_hit Q)
      s \<le>
      nnreal N *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
  unfolding
    ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
proof (rule wp_event_bind_bound_by_cont)
  show
    "\<not> ro_query_head_dependent_query_index_list_fresh_hit Q None"
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
  have t_eq: "t = query_start"
    by (rule ro_checked_staged_first_root_query_head_program_state[OF head'])
  have head_norm: "ro_query_head_data data = data"
    by (rule ro_query_head_data_of_query_head_outcome[OF head'])
  let ?Q = "Q prefix prefix_state data query_start"
  let ?R = "(nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
  have exact:
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds)
      (ro_query_witnesses_query_index_list_fresh_hit ?Q)
      query_start \<le>
      nnreal (card (query_index_raw_list_preimage ?Q)) *
        (1 / nnreal size) ^ rounds"
    by (rule
        wp_ro_checked_staged_query_program_with_witnesses_query_index_list_fresh_bound)
  have product:
    "nnreal (card (query_index_raw_list_preimage ?Q)) *
        (1 / nnreal size) ^ rounds \<le>
      nnreal (card ?Q) * ?R"
    by (rule query_index_raw_list_preimage_probability_bound[OF subset[OF head']])
  have local:
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds)
      (ro_query_witnesses_query_index_list_fresh_hit ?Q)
      query_start \<le>
      nnreal (card ?Q) * ?R"
    by (rule order_trans[OF exact product])
  have event_eq:
    "(\<lambda>out. case out of
      None \<Rightarrow>
        ro_query_head_dependent_query_index_list_fresh_hit Q None
    | Some (p, u) \<Rightarrow>
        ro_query_head_dependent_query_index_list_fresh_hit Q
          (Some
            ((((prefix, prefix_state),
                data\<lparr>staged_query_chunks := snd (snd p)\<rparr>,
                query_start, fst p, fst (snd p)), u)))) =
      ro_query_witnesses_query_index_list_fresh_hit ?Q"
    unfolding
      ro_query_head_dependent_query_index_list_fresh_hit_def
    by (rule ext)
      (auto simp: head_norm
        ro_query_witnesses_query_index_list_fresh_hit_def
        ro_query_witnesses_raws_fresh_hit_def
        split: option.splits prod.splits)
  have mapped:
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          return
            ((prefix, prefix_state),
              data\<lparr>staged_query_chunks := query_chunks\<rparr>,
              query_start, raws, query_states)))
      (ro_query_head_dependent_query_index_list_fresh_hit Q)
      query_start =
      wp_event
        (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds)
        (ro_query_witnesses_query_index_list_fresh_hit ?Q)
        query_start"
    by (simp add: wp_event_bind_return_map split_def event_eq)
  have card_cast: "nnreal (card ?Q) \<le> nnreal N"
    using card_bound[OF head'] by simp
  have uniform: "nnreal (card ?Q) * ?R \<le> nnreal N * ?R"
    by (rule mult_right_mono[OF card_cast]) simp
  show
    "wp_event
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
      (ro_query_head_dependent_query_index_list_fresh_hit Q)
      t \<le> nnreal N * ?R"
    unfolding x_eq t_eq
  proof -
    have local':
      "wp_event
        (ro_checked_staged_query_program_with_witnesses A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)
            query_start 0 rounds \<bind>
          (\<lambda>(raws, query_states, query_chunks).
            return
              ((prefix, prefix_state),
                data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                query_start, raws, query_states)))
        (ro_query_head_dependent_query_index_list_fresh_hit Q)
        query_start \<le> nnreal (card ?Q) * ?R"
      unfolding mapped
      by (rule local)
    show
      "wp_event
        (case ((prefix, prefix_state), data, query_start) of
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
        (ro_query_head_dependent_query_index_list_fresh_hit Q)
        query_start \<le> nnreal N * ?R"
      by (simp only: prod.case; rule order_trans[OF local' uniform])
  qed
qed


definition ro_query_head_query_phase_relation
  :: "'f staged_adversary \<Rightarrow> nat list set \<Rightarrow> 'f staged_proof_data \<Rightarrow>
      'f protocol_channel \<Rightarrow> 'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "ro_query_head_query_phase_relation A Q data query_start x y \<longleftrightarrow>
    (\<exists>raws query_states query_chunks attacker_state j.
      Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data)
              query_start 0 rounds)
            query_start) \<and>
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

lemma ro_query_head_query_phase_relation_fiber_card_bound:
  "card {y.
      ro_query_head_query_phase_relation A Q data query_start x y}
    \<le> query_index_raw_list_relation_fiber_bound Q"
proof -
  let ?values =
    "\<Union>i < rounds. query_index_raw_list_position_values Q i"
  have subset:
    "{y. ro_query_head_query_phase_relation A Q data query_start x y}
      \<subseteq> ?values"
    unfolding
      ro_query_head_query_phase_relation_def
      query_index_raw_list_position_values_def
      query_index_raw_list_preimage_def
    by blast
  have finite_values: "finite ?values"
    by simp
  have
    "card {y.
        ro_query_head_query_phase_relation A Q data query_start x y}
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

definition ro_query_head_dependent_actual_query_index_list_hit
where
  "ro_query_head_dependent_actual_query_index_list_hit Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          Q prefix prefix_state (ro_query_head_data data) query_start)"

definition ro_query_head_dependent_query_start_prequery_hit
where
  "ro_query_head_dependent_query_start_prequery_hit Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          Q prefix prefix_state (ro_query_head_data data) query_start \<and>
        (\<exists>j < rounds.
          fmlookup (HashMap query_start)
            (QueryIndexChallenge
              (PQueryCounter (query_states ! j))
              (PState (query_states ! j))) =
            Some (raws ! j)))"

definition ro_query_head_dependent_query_phase_relation_hit
where
  "ro_query_head_dependent_query_phase_relation_hit A Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        hash_relation_hit
          (ro_query_head_query_phase_relation A
            (Q prefix prefix_state (ro_query_head_data data) query_start)
            (ro_query_head_data data) query_start)
          query_start attacker_state)"


lemma wp_ro_query_head_dependent_query_phase_relation_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and relation_fiber:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute (ro_checked_staged_first_root_query_head_program A) s)
        \<Longrightarrow>
        query_index_raw_list_relation_fiber_bound
          (Q prefix prefix_state data query_start) \<le> N"
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
      (ro_query_head_dependent_query_phase_relation_hit A Q)
      s
    \<le> hash_relation_budget_value N
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)"
  unfolding
    ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
proof (rule wp_event_bind_output_state_dependent_relation_bound)
  show
    "\<not> ro_query_head_dependent_query_phase_relation_hit A Q None"
    unfolding ro_query_head_dependent_query_phase_relation_hit_def
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
      "ro_query_head_dependent_query_phase_relation_hit A Q out"
  obtain prefix prefix_state data query_start where x_eq:
    "x = ((prefix, prefix_state), data, query_start)"
    by (cases x) (auto split: prod.splits)
  have head':
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
    using head unfolding x_eq .
  have t_eq: "t = query_start"
    by (rule ro_checked_staged_first_root_query_head_program_state[OF head'])
  have head_norm: "ro_query_head_data data = data"
    by (rule ro_query_head_data_of_query_head_outcome[OF head'])
  have out_some: "out \<noteq> None"
    using event
    unfolding ro_query_head_dependent_query_phase_relation_hit_def
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
              ro_query_head_query_phase_relation A
                (Q prefix prefix_state data query_start)
                data query_start)
      t out"
    using event head_norm
    unfolding x_eq t_eq out_eq
      ro_query_head_dependent_query_phase_relation_hit_def
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
      ro_query_head_query_phase_relation A
        (Q prefix prefix_state data query_start)
        data query_start x y} \<le> N"
  proof -
    fix x
    have
      "card {y.
          ro_query_head_query_phase_relation A
            (Q prefix prefix_state data query_start)
            data query_start x y}
        \<le> query_index_raw_list_relation_fiber_bound
          (Q prefix prefix_state data query_start)"
      by (rule ro_query_head_query_phase_relation_fiber_card_bound)
    also have "... \<le> N"
      by (rule relation_fiber[OF head'])
    finally show
      "card {y.
        ro_query_head_query_phase_relation A
          (Q prefix prefix_state data query_start)
          data query_start x y} \<le> N" .
  qed
  let ?R =
    "ro_query_head_query_phase_relation A
      (Q prefix prefix_state data query_start) data query_start"
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
              ro_query_head_query_phase_relation A
                (Q prefix prefix_state data query_start)
                data query_start)
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


lemma
  ro_query_head_dependent_actual_query_index_list_hit_imp_fresh_or_prequery_or_relation:
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
      "ro_query_head_dependent_actual_query_index_list_hit Q
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
  shows
    "ro_query_head_dependent_query_index_list_fresh_hit Q
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state))) \<or>
     ro_query_head_dependent_query_start_prequery_hit Q
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state))) \<or>
     ro_query_head_dependent_query_phase_relation_hit A Q
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
  let ?Q =
    "Q prefix prefix_state (ro_query_head_data data) query_start"
  have query_in: "map (\<lambda>raw. index (to_nat raw)) raws \<in> ?Q"
    using actual
    unfolding ro_query_head_dependent_actual_query_index_list_hit_def
    by simp
  from ro_checked_staged_transcript_program_with_first_root_outcomeE[
      OF outcome]
  obtain head_data query_chunks where
    tail:
      "Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots head_data)
              (staged_composition_fri_roots head_data)
              query_start 0 rounds)
            query_start)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    by blast
  have head_roots:
      "staged_trace_fri_roots (ro_query_head_data data) =
          staged_trace_fri_roots head_data \<and>
       staged_composition_fri_roots (ro_query_head_data data) =
          staged_composition_fri_roots head_data"
    using data_eq unfolding ro_query_head_data_def by simp
  have tail':
      "Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots (ro_query_head_data data))
              (staged_composition_fri_roots (ro_query_head_data data))
              query_start 0 rounds)
            query_start)"
    using tail head_roots by simp
  show ?thesis
  proof (cases
      "\<forall>j < rounds.
        fmlookup (HashMap (query_states ! j))
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) = None")
    case True
    have raw_in:
      "raws \<in> query_index_raw_list_preimage ?Q"
      unfolding query_index_raw_list_preimage_def
      using len_raws query_in by blast
    have raw_fresh:
      "ro_query_witnesses_raws_fresh_hit raws
        (Some ((raws, query_states, staged_query_chunks data),
          attacker_state))"
      unfolding ro_query_witnesses_raws_fresh_hit_def
      using len_raws len_states len_chunks True by simp
    have list_fresh:
      "ro_query_witnesses_query_index_list_fresh_hit ?Q
        (Some ((raws, query_states, staged_query_chunks data),
          attacker_state))"
      by (rule ro_query_witnesses_query_index_list_fresh_hitI[
            OF raw_in raw_fresh])
    show ?thesis
      unfolding ro_query_head_dependent_query_index_list_fresh_hit_def
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
        "ro_query_head_query_phase_relation A ?Q
          (ro_query_head_data data) query_start ?key (raws ! j)"
        unfolding ro_query_head_query_phase_relation_def
        using tail' len_raws len_states query_in j_bound nonfresh
        by blast
      have relation_hit:
        "hash_relation_hit
          (ro_query_head_query_phase_relation A ?Q
            (ro_query_head_data data) query_start)
          query_start attacker_state"
        unfolding hash_relation_hit_def
        using None final_lookup relation by blast
      have event_hit:
        "ro_query_head_dependent_query_phase_relation_hit A Q
          (Some ((((prefix, prefix_state), data, query_start, raws,
            query_states), attacker_state)))"
        unfolding ro_query_head_dependent_query_phase_relation_hit_def
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
        "ro_query_head_dependent_query_start_prequery_hit Q
          (Some ((((prefix, prefix_state), data, query_start, raws,
            query_states), attacker_state)))"
        unfolding ro_query_head_dependent_query_start_prequery_hit_def
        using query_in j_bound Some old_eq by auto
      show ?thesis
        using prequery by blast
    qed
  qed
qed

lemma wp_ro_query_head_dependent_actual_query_index_list_hit_split:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (ro_query_head_dependent_actual_query_index_list_hit Q)
        adversary_initial_state
      \<le>
      wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_index_list_fresh_hit Q)
          adversary_initial_state +
        wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_start_prequery_hit Q)
          adversary_initial_state +
        wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_phase_relation_hit A Q)
          adversary_initial_state"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Actual =
    "ro_query_head_dependent_actual_query_index_list_hit Q"
  let ?Fresh =
    "ro_query_head_dependent_query_index_list_fresh_hit Q"
  let ?Prequery =
    "ro_query_head_dependent_query_start_prequery_hit Q"
  let ?Relation =
    "ro_query_head_dependent_query_phase_relation_hit A Q"
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
        unfolding ro_query_head_dependent_actual_query_index_list_hit_def
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
            ro_query_head_dependent_actual_query_index_list_hit_imp_fresh_or_prequery_or_relation[
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
