theory Soundness_FRI_Query_Head_Adaptive_Rectangle_Family
  imports
    Staged_Security_Experiment_RO_Query_Rectangle_Family_Future_Count
    Soundness_FRI_Query_Head_Adaptive_Actual_Product
begin

context soundness
begin

text \<open>Lift the transition-rectangle product through the actual query-head
program.  The exact state-dependent family is retained until the final
head-uniform sum bound.\<close>

lemma wp_ro_checked_staged_transcript_query_head_dependent_rectangle_family_counted_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        finite (K prefix prefix_state data query_start)"
    and cover:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        Q prefix prefix_state data query_start \<subseteq>
          (\<Union>k\<in>K prefix prefix_state data query_start.
            fri_conditioned_query_lists
              (I prefix prefix_state data query_start k))"
    and subsets:
      "\<And>prefix prefix_state data query_start t k.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        k \<in> K prefix prefix_state data query_start \<Longrightarrow>
        I prefix prefix_state data query_start k \<subseteq> query_sample_space"
    and sum_bound:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        (\<Sum>k\<in>K prefix prefix_state data query_start.
          (nnreal
              (query_raw_preimage_card_envelope
                (card (I prefix prefix_state data query_start k))) /
            nnreal size) ^
          (rounds - staged_attacker_query_budget budgets)) \<le> B"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_counted_hit Q)
      adversary_initial_state \<le> B"
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
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  obtain prefix prefix_state data query_start where x_eq:
    "x = ((prefix, prefix_state), data, query_start)"
    by (cases x) (auto split: prod.splits)
  have head':
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
    using head unfolding x_eq .
  have t_eq: "t = query_start"
    by (rule ro_checked_staged_first_root_query_head_program_state[OF head'])
  have head_norm: "ro_query_head_data data = data"
    by (rule ro_query_head_data_of_query_head_outcome[OF head'])
  let ?K = "K prefix prefix_state data query_start"
  let ?I = "I prefix prefix_state data query_start"
  let ?Q = "Q prefix prefix_state data query_start"
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
      (\<Sum>k\<in>?K.
        (nnreal (query_raw_preimage_card_envelope (card (?I k))) /
          nnreal size) ^
        (rounds -
          (query_future_prequery_count query_start +
            sum_list (query_opening_budgets budgets))))"
    by (rule
        wp_ro_checked_staged_query_program_index_rectangle_family_future_count_bound[
          OF finite[OF head'] cover[OF head'] opening_length
            opening_controlled])
      (use subsets[OF head'] in blast)
  have head_count_raw:
    "query_future_prequery_count t \<le>
      query_future_prequery_count adversary_initial_state +
        staged_prequery_attacker_query_budget budgets"
    by (rule
        ro_checked_staged_first_root_query_head_program_query_future_count_bound[
          OF wf controlled head'])
  have initial_count:
    "query_future_prequery_count adversary_initial_state = 0"
    unfolding query_future_prequery_count_def query_future_keys_def by simp
  have head_count:
    "query_future_prequery_count query_start \<le>
      staged_prequery_attacker_query_budget budgets"
    using head_count_raw t_eq initial_count by simp
  have exponent_arg:
    "query_future_prequery_count query_start +
        sum_list (query_opening_budgets budgets) \<le>
      staged_attacker_query_budget budgets"
    using head_count staged_prequery_plus_opening_budget[of budgets]
    by linarith
  have power_sum:
    "(\<Sum>k\<in>?K.
        (nnreal (query_raw_preimage_card_envelope (card (?I k))) /
          nnreal size) ^
        (rounds -
          (query_future_prequery_count query_start +
            sum_list (query_opening_budgets budgets)))) \<le>
      (\<Sum>k\<in>?K.
        (nnreal (query_raw_preimage_card_envelope (card (?I k))) /
          nnreal size) ^
        (rounds - staged_attacker_query_budget budgets))"
  proof (rule sum_mono)
    fix k
    assume k_in: "k \<in> ?K"
    have I_subset: "?I k \<subseteq> query_sample_space"
      by (rule subsets[OF head' k_in])
    have p_le:
      "nnreal (query_raw_preimage_card_envelope (card (?I k))) /
          nnreal size \<le> 1"
      by (rule query_sample_space_envelope_fraction_le_one[OF I_subset])
    show
      "(nnreal (query_raw_preimage_card_envelope (card (?I k))) /
          nnreal size) ^
          (rounds -
            (query_future_prequery_count query_start +
              sum_list (query_opening_budgets budgets))) \<le>
        (nnreal (query_raw_preimage_card_envelope (card (?I k))) /
          nnreal size) ^
          (rounds - staged_attacker_query_budget budgets)"
      by (rule prob_power_nat_diff_antitone[OF p_le exponent_arg])
  qed
  have local:
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        query_start 0 rounds)
      (ro_query_witnesses_index_list_set_hit ?Q)
      query_start \<le> B"
    by (rule order_trans[OF exact order_trans[OF power_sum sum_bound[OF head']]])
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
      t \<le> B"
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
        query_start \<le> B"
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
        query_start \<le> B"
      by (simp only: prod.case; rule local')
  qed
qed

lemma wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_family_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        finite (K prefix prefix_state data query_start)"
    and cover:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        Q prefix prefix_state data query_start \<subseteq>
          (\<Union>k\<in>K prefix prefix_state data query_start.
            fri_conditioned_query_lists
              (I prefix prefix_state data query_start k))"
    and subsets:
      "\<And>prefix prefix_state data query_start t k.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        k \<in> K prefix prefix_state data query_start \<Longrightarrow>
        I prefix prefix_state data query_start k \<subseteq> query_sample_space"
    and sum_bound:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        (\<Sum>k\<in>K prefix prefix_state data query_start.
          (nnreal
              (query_raw_preimage_card_envelope
                (card (I prefix prefix_state data query_start k))) /
            nnreal size) ^
          (rounds - staged_attacker_query_budget budgets)) \<le> B"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit Q)
      adversary_initial_state \<le> B"
  by (rule order_trans[
        OF wp_ro_query_head_dependent_actual_query_index_list_hit_le_counted[
          OF wf controlled]
          wp_ro_checked_staged_transcript_query_head_dependent_rectangle_family_counted_bound[
            OF wf controlled finite cover subsets sum_bound]])

lemma wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        Q prefix prefix_state data query_start \<subseteq>
          fri_conditioned_query_lists
            (I prefix prefix_state data query_start)"
    and subset:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        I prefix prefix_state data query_start \<subseteq> query_sample_space"
    and card_bound:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute
              (ro_checked_staged_first_root_query_head_program A)
              adversary_initial_state) \<Longrightarrow>
        card (I prefix prefix_state data query_start) \<le> N"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit Q)
      adversary_initial_state \<le>
      (nnreal (query_raw_preimage_card_envelope N) / nnreal size) ^
        (rounds - staged_attacker_query_budget budgets)"
proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_family_bound[
      OF wf controlled,
      where K="\<lambda>prefix prefix_state data query_start. {()}"
        and I="\<lambda>prefix prefix_state data query_start _.
          I prefix prefix_state data query_start"])
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show "finite {()}"
    by simp
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "Q prefix prefix_state data query_start \<subseteq>
      (\<Union>k\<in>{()}.
        fri_conditioned_query_lists
          (I prefix prefix_state data query_start))"
    using cover[OF head] by simp
next
  fix prefix prefix_state data query_start t k
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
    and "k \<in> {()}"
  show "I prefix prefix_state data query_start \<subseteq> query_sample_space"
    by (rule subset[OF head])
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  have raw_card:
    "query_raw_preimage_card_envelope
        (card (I prefix prefix_state data query_start))
      \<le> query_raw_preimage_card_envelope N"
    by (rule query_raw_preimage_card_envelope_mono[OF card_bound[OF head]])
  have fraction:
    "nnreal
        (query_raw_preimage_card_envelope
          (card (I prefix prefix_state data query_start))) /
        nnreal size
      \<le> nnreal (query_raw_preimage_card_envelope N) / nnreal size"
    by (rule nnreal_nat_divide_right_mono[OF raw_card])
  have power:
    "(nnreal
        (query_raw_preimage_card_envelope
          (card (I prefix prefix_state data query_start))) /
      nnreal size) ^
      (rounds - staged_attacker_query_budget budgets)
    \<le> (nnreal (query_raw_preimage_card_envelope N) / nnreal size) ^
        (rounds - staged_attacker_query_budget budgets)"
    by (rule power_mono[OF fraction]) simp
  show
    "(\<Sum>k\<in>{()}.
      (nnreal
          (query_raw_preimage_card_envelope
            (card (I prefix prefix_state data query_start))) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets))
    \<le> (nnreal (query_raw_preimage_card_envelope N) / nnreal size) ^
        (rounds - staged_attacker_query_budget budgets)"
    using power by simp
qed

end
end
