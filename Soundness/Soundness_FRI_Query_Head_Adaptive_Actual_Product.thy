theory Soundness_FRI_Query_Head_Adaptive_Actual_Product
  imports
    Soundness_FRI_Query_Head_Future_Count_Bound
    Soundness_FRI_RO_Query_Head_Dependent_Product
begin

context soundness
begin

definition ro_query_head_dependent_actual_query_index_list_counted_hit
where
  "ro_query_head_dependent_actual_query_index_list_counted_hit Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        ro_query_witnesses_index_list_set_hit
          (Q prefix prefix_state (ro_query_head_data data) query_start)
          (Some ((raws, query_states, staged_query_chunks data),
            attacker_state)))"

lemma
  ro_query_head_dependent_actual_query_index_list_counted_hit_None[simp]:
  "\<not> ro_query_head_dependent_actual_query_index_list_counted_hit Q None"
  unfolding
    ro_query_head_dependent_actual_query_index_list_counted_hit_def
  by simp

lemma ro_query_witnesses_index_list_set_hit_None[simp]:
  "\<not> ro_query_witnesses_index_list_set_hit Q None"
  unfolding ro_query_witnesses_index_list_set_hit_def by simp

lemma
  ro_query_head_dependent_actual_query_index_list_hit_imp_counted_hit:
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
    "ro_query_head_dependent_actual_query_index_list_counted_hit Q
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
proof -
  have props:
    "length raws = rounds \<and>
     length query_states = rounds \<and>
     length (staged_query_chunks data) = rounds"
    using
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled outcome]
    by blast
  have query_in:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
      Q prefix prefix_state (ro_query_head_data data) query_start"
    using actual
    unfolding ro_query_head_dependent_actual_query_index_list_hit_def
    by simp
  show ?thesis
    unfolding
      ro_query_head_dependent_actual_query_index_list_counted_hit_def
      ro_query_witnesses_index_list_set_hit_def
      ro_query_witnesses_index_list_eq_hit_def
    using props query_in by auto
qed



lemma wp_ro_query_head_dependent_actual_query_index_list_hit_le_counted:
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
        (ro_query_head_dependent_actual_query_index_list_counted_hit Q)
        adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and actual: "ro_query_head_dependent_actual_query_index_list_hit Q out"
  show "ro_query_head_dependent_actual_query_index_list_counted_hit Q out"
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
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
      using support unfolding Some packed_eq .
    have actual':
      "ro_query_head_dependent_actual_query_index_list_hit Q
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
      using actual unfolding Some packed_eq .
    have counted:
      "ro_query_head_dependent_actual_query_index_list_counted_hit Q
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
      by (rule
          ro_query_head_dependent_actual_query_index_list_hit_imp_counted_hit[
            OF wf controlled outcome' actual'])
    show ?thesis
      using counted unfolding Some packed_eq .
  qed
qed


lemma
  wp_ro_checked_staged_transcript_query_head_dependent_counted_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
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
      (ro_query_head_dependent_actual_query_index_list_counted_hit Q)
      s \<le>
      nnreal N *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^
          (rounds -
            (query_future_prequery_count s +
              staged_attacker_query_budget budgets))"
  unfolding
    ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
proof (rule wp_event_bind_bound_by_cont)
  show
    "\<not> ro_query_head_dependent_actual_query_index_list_counted_hit Q None"
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
  let ?p =
    "nnreal (query_raw_preimage_card_envelope 1) / nnreal size"
  have Q_subset: "?Q \<subseteq> fri_query_index_list_space"
    by (rule subset[OF head'])
  have finite_Q: "finite ?Q"
    by (rule finite_subset[OF Q_subset finite_fri_query_index_list_space])
  have Q_lengths: "\<forall>xs \<in> ?Q. length xs = rounds"
    using Q_subset unfolding fri_query_index_list_space_def by blast
  have Q_entries: "\<forall>xs \<in> ?Q. set xs \<subseteq> query_sample_space"
    using Q_subset unfolding fri_query_index_list_space_def by blast
  have opening_length:
    "length (query_opening_budgets budgets) = rounds"
    using wf unfolding staged_budget_wellformed_def by blast
  have opening_controlled:
    "\<forall>j < rounds. \<forall>raw.
      controlled_ro_program (query_opening_budgets budgets ! j)
        (query_opening_stage A (0 + j) raw)"
    using wf controlled
    unfolding staged_budget_wellformed_def staged_adversary_controlled_def
    by simp
  have exact:
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        query_start 0 rounds)
      (ro_query_witnesses_index_list_set_hit ?Q)
      query_start \<le>
      nnreal (card ?Q) *
        ?p ^
          (rounds -
            (query_future_prequery_count query_start +
              sum_list (query_opening_budgets budgets)))"
    by (rule
        wp_ro_checked_staged_query_program_index_list_set_future_count_bound[
          OF finite_Q Q_lengths opening_length opening_controlled Q_entries])
  have head_count_raw:
    "query_future_prequery_count t \<le>
      query_future_prequery_count s +
        staged_prequery_attacker_query_budget budgets"
    by (rule
        ro_checked_staged_first_root_query_head_program_query_future_count_bound[
          OF wf controlled head'])
  have head_count:
    "query_future_prequery_count query_start \<le>
      query_future_prequery_count s +
        staged_prequery_attacker_query_budget budgets"
    using head_count_raw t_eq by simp
  have exponent_arg:
    "query_future_prequery_count query_start +
        sum_list (query_opening_budgets budgets) \<le>
      query_future_prequery_count s +
        staged_attacker_query_budget budgets"
    using head_count staged_prequery_plus_opening_budget[of budgets]
    by linarith
  have zero_in: "{0} \<subseteq> query_sample_space"
    unfolding query_sample_space_def
    using query_sample_space_size_pos by simp
  have p_le: "?p \<le> 1"
    using query_sample_space_envelope_fraction_le_one[OF zero_in]
    by simp
  have power_le:
    "?p ^
        (rounds -
          (query_future_prequery_count query_start +
            sum_list (query_opening_budgets budgets))) \<le>
      ?p ^
        (rounds -
          (query_future_prequery_count s +
            staged_attacker_query_budget budgets))"
    by (rule prob_power_nat_diff_antitone[OF p_le exponent_arg])
  have local:
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        query_start 0 rounds)
      (ro_query_witnesses_index_list_set_hit ?Q)
      query_start \<le>
      nnreal (card ?Q) *
        ?p ^
          (rounds -
            (query_future_prequery_count s +
              staged_attacker_query_budget budgets))"
  proof (rule order_trans[OF exact])
    show
      "nnreal (card ?Q) *
          ?p ^
            (rounds -
              (query_future_prequery_count query_start +
                sum_list (query_opening_budgets budgets))) \<le>
        nnreal (card ?Q) *
          ?p ^
            (rounds -
              (query_future_prequery_count s +
                staged_attacker_query_budget budgets))"
      by (rule mult_left_mono[OF power_le]) simp
  qed
  have event_eq:
    "(\<lambda>out. case out of
      None \<Rightarrow>
        ro_query_head_dependent_actual_query_index_list_counted_hit Q None
    | Some (p, u) \<Rightarrow>
        ro_query_head_dependent_actual_query_index_list_counted_hit Q
          (Some
            ((((prefix, prefix_state),
                data\<lparr>staged_query_chunks := snd (snd p)\<rparr>,
                query_start, fst p, fst (snd p)), u)))) =
      ro_query_witnesses_index_list_set_hit ?Q"
    unfolding
      ro_query_head_dependent_actual_query_index_list_counted_hit_def
    by (rule ext)
      (auto simp: head_norm split: option.splits prod.splits)
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
      (ro_query_head_dependent_actual_query_index_list_counted_hit Q)
      query_start =
      wp_event
        (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds)
        (ro_query_witnesses_index_list_set_hit ?Q)
        query_start"
    by (simp add: wp_event_bind_return_map split_def event_eq)
  have card_cast: "nnreal (card ?Q) \<le> nnreal N"
    using card_bound[OF head'] by simp
  have uniform:
    "nnreal (card ?Q) *
        ?p ^
          (rounds -
            (query_future_prequery_count s +
              staged_attacker_query_budget budgets)) \<le>
      nnreal N *
        ?p ^
          (rounds -
            (query_future_prequery_count s +
              staged_attacker_query_budget budgets))"
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
      (ro_query_head_dependent_actual_query_index_list_counted_hit Q)
      t \<le>
      nnreal N *
        ?p ^
          (rounds -
            (query_future_prequery_count s +
              staged_attacker_query_budget budgets))"
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
        (ro_query_head_dependent_actual_query_index_list_counted_hit Q)
        query_start \<le>
        nnreal (card ?Q) *
          ?p ^
            (rounds -
              (query_future_prequery_count s +
                staged_attacker_query_budget budgets))"
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
        (ro_query_head_dependent_actual_query_index_list_counted_hit Q)
        query_start \<le>
        nnreal N *
          ?p ^
            (rounds -
              (query_future_prequery_count s +
                staged_attacker_query_budget budgets))"
      by (simp only: prod.case; rule order_trans[OF local' uniform])
  qed
qed


lemma
  wp_ro_checked_staged_transcript_query_head_dependent_counted_initial_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        Q prefix prefix_state data query_start \<subseteq> fri_query_index_list_space"
    and card_bound:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        card (Q prefix prefix_state data query_start) \<le> N"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_counted_hit Q)
      adversary_initial_state \<le>
      nnreal N *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^
          (rounds - staged_attacker_query_budget budgets)"
proof -
  have base:
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_counted_hit Q)
      adversary_initial_state \<le>
      nnreal N *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^
          (rounds -
            (query_future_prequery_count adversary_initial_state +
              staged_attacker_query_budget budgets))"
  proof (rule
      wp_ro_checked_staged_transcript_query_head_dependent_counted_bound[
        OF wf controlled])
    fix prefix prefix_state data query_start t
    assume head:
      "Some (((prefix, prefix_state), data, query_start), t) \<in>
        set_dist
          (execute
            (ro_checked_staged_first_root_query_head_program A)
            adversary_initial_state)"
    show
      "Q prefix prefix_state data query_start \<subseteq>
        fri_query_index_list_space"
      by (rule subset[OF head])
  next
    fix prefix prefix_state data query_start t
    assume head:
      "Some (((prefix, prefix_state), data, query_start), t) \<in>
        set_dist
          (execute
            (ro_checked_staged_first_root_query_head_program A)
            adversary_initial_state)"
    show "card (Q prefix prefix_state data query_start) \<le> N"
      by (rule card_bound[OF head])
  qed
  have initial_count:
    "query_future_prequery_count adversary_initial_state = 0"
    unfolding query_future_prequery_count_def query_future_keys_def
    by simp
  show ?thesis
    using base unfolding initial_count by simp
qed

lemma wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        Q prefix prefix_state data query_start \<subseteq> fri_query_index_list_space"
    and card_bound:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        card (Q prefix prefix_state data query_start) \<le> N"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (ro_query_head_dependent_actual_query_index_list_hit Q)
        adversary_initial_state
      \<le>
      nnreal N *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^
          (rounds - staged_attacker_query_budget budgets)"
proof (rule order_trans)
  show
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (ro_query_head_dependent_actual_query_index_list_hit Q)
        adversary_initial_state
      \<le>
      wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (ro_query_head_dependent_actual_query_index_list_counted_hit Q)
        adversary_initial_state"
    by (rule
        wp_ro_query_head_dependent_actual_query_index_list_hit_le_counted[
          OF wf controlled])
  show
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (ro_query_head_dependent_actual_query_index_list_counted_hit Q)
        adversary_initial_state
      \<le>
      nnreal N *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^
          (rounds - staged_attacker_query_budget budgets)"
    by (rule
        wp_ro_checked_staged_transcript_query_head_dependent_counted_initial_bound[
          OF wf controlled subset card_bound])
qed
end
end
