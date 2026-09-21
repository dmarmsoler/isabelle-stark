theory Soundness_FRI_Conditioned_Query_Start
  imports
    Stark.Soundness_FRI_Conditioned_Query_Head
    Stark.Soundness_FRI_RO_Actual_Query_Zero_Round_Parameter_Bound
begin

context soundness
begin

definition fri_conditioned_trace_residual_query_lists
  :: "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_conditioned_trace_residual_query_lists data query_start =
    fri_conditioned_quantitative_residual_query_lists
      (clength - 1)
      (staged_trace_fri_roots data)
      (staged_trace_fri_challenges data)
      (staged_trace_final data)
      query_start"

definition fri_conditioned_composition_residual_query_lists
  :: "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_conditioned_composition_residual_query_lists data query_start =
    (if to_nat (staged_degree data) \<le> maxDegree then
      fri_conditioned_quantitative_residual_query_lists
        (to_nat (staged_degree data))
        (staged_composition_fri_roots data)
        (staged_composition_fri_challenges data)
        (staged_composition_final data)
        query_start
     else {})"

lemma fri_conditioned_trace_residual_query_lists_subset:
  "fri_conditioned_trace_residual_query_lists data query_start \<subseteq>
    fri_query_index_list_space"
  unfolding fri_conditioned_trace_residual_query_lists_def
  by (rule fri_conditioned_quantitative_residual_query_lists_subset)

lemma fri_conditioned_composition_residual_query_lists_subset:
  "fri_conditioned_composition_residual_query_lists data query_start \<subseteq>
    fri_query_index_list_space"
proof (cases "to_nat (staged_degree data) \<le> maxDegree")
  case True
  show ?thesis
    unfolding fri_conditioned_composition_residual_query_lists_def
      if_P[OF True]
    by (rule fri_conditioned_quantitative_residual_query_lists_subset)
next
  case False
  show ?thesis
    unfolding fri_conditioned_composition_residual_query_lists_def
      if_not_P[OF False]
    by simp
qed

lemma ceil_log_clength_le_eval_power:
  assumes eval_power: "clength * scale = 2 ^ N"
  shows "ceil_log clength \<le> N"
proof (rule ceil_log_le_power)
  have "clength \<le> clength * scale"
    using scale_pos by simp
  then show "clength \<le> 2 ^ N"
    using eval_power by simp
qed

lemma ceil_log_reachable_degree_le_eval_power:
  assumes eval_power: "clength * scale = 2 ^ N"
    and degree_bound: "d \<le> maxDegree"
  shows "ceil_log (Suc d) \<le> N"
proof (rule ceil_log_le_power)
  have "Suc d \<le> maxDegree + 1"
    using degree_bound by simp
  also have "... \<le> clength * scale"
    using maxDegree_less_eval_domain by simp
  also have "... = 2 ^ N"
    by (rule eval_power)
  finally show "Suc d \<le> 2 ^ N" .
qed

lemma card_fri_conditioned_trace_residual_query_lists:
  assumes trace_roots:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    and trace_challenges:
      "length (staged_trace_fri_challenges data) = ceil_log clength"
  shows
    "card (fri_conditioned_trace_residual_query_lists data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound (clength - 1)"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have round_count:
      "length (staged_trace_fri_challenges data) =
        ceil_log (Suc (clength - 1))"
    using trace_challenges clength_pos by simp
  have rounds_le: "ceil_log (Suc (clength - 1)) \<le> N"
    using ceil_log_clength_le_eval_power[OF eval_power] clength_pos by simp
  show ?thesis
    unfolding fri_conditioned_trace_residual_query_lists_def
    by (rule card_fri_conditioned_quantitative_residual_query_lists[
        OF eval_power round_count rounds_le])
      (use trace_roots trace_challenges in simp)
qed

lemma
  fri_conditioned_trace_residual_query_lists_relation_fiber_bound:
  assumes trace_roots:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    and trace_challenges:
      "length (staged_trace_fri_challenges data) = ceil_log clength"
  shows
    "query_index_raw_list_relation_fiber_bound
      (fri_conditioned_trace_residual_query_lists data query_start) \<le>
      rounds *
        query_raw_preimage_card_envelope
          (rounds *
            fri_conditioned_residual_query_list_card_bound (clength - 1))"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have round_count:
      "length (staged_trace_fri_challenges data) =
        ceil_log (Suc (clength - 1))"
    using trace_challenges clength_pos by simp
  have rounds_le: "ceil_log (Suc (clength - 1)) \<le> N"
    using ceil_log_clength_le_eval_power[OF eval_power] clength_pos by simp
  show ?thesis
    unfolding fri_conditioned_trace_residual_query_lists_def
    by (rule
        fri_conditioned_quantitative_residual_query_lists_relation_fiber_bound[
          OF eval_power round_count rounds_le])
      (use trace_roots trace_challenges in simp)
qed

lemma card_fri_conditioned_composition_residual_query_lists:
  assumes composition_roots:
      "length (staged_composition_fri_roots data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
    and composition_challenges:
      "length (staged_composition_fri_challenges data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
  shows
    "card (fri_conditioned_composition_residual_query_lists data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound
        (to_nat (staged_degree data))"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have rounds_le:
      "ceil_log (Suc (to_nat (staged_degree data))) \<le> N"
    by (rule ceil_log_reachable_degree_le_eval_power[
        OF eval_power degree_bound])
  show ?thesis
    unfolding fri_conditioned_composition_residual_query_lists_def
      if_P[OF degree_bound]
    by (rule card_fri_conditioned_quantitative_residual_query_lists[
        OF eval_power composition_challenges rounds_le])
      (use composition_roots composition_challenges in simp)
qed

lemma
  fri_conditioned_composition_residual_query_lists_relation_fiber_bound:
  assumes composition_roots:
      "length (staged_composition_fri_roots data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
    and composition_challenges:
      "length (staged_composition_fri_challenges data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
  shows
    "query_index_raw_list_relation_fiber_bound
      (fri_conditioned_composition_residual_query_lists data query_start) \<le>
      rounds *
        query_raw_preimage_card_envelope
          (rounds *
            fri_conditioned_residual_query_list_card_bound
              (to_nat (staged_degree data)))"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have rounds_le:
      "ceil_log (Suc (to_nat (staged_degree data))) \<le> N"
    by (rule ceil_log_reachable_degree_le_eval_power[
        OF eval_power degree_bound])
  show ?thesis
    unfolding fri_conditioned_composition_residual_query_lists_def
      if_P[OF degree_bound]
    by (rule
        fri_conditioned_quantitative_residual_query_lists_relation_fiber_bound[
          OF eval_power composition_challenges rounds_le])
      (use composition_roots composition_challenges in simp)
qed

lemma fri_conditioned_residual_query_list_card_bound_mono:
  assumes le: "d \<le> D"
  shows
    "fri_conditioned_residual_query_list_card_bound d \<le>
      fri_conditioned_residual_query_list_card_bound D"
proof -
  have ceil_le: "ceil_log (Suc d) \<le> ceil_log (Suc D)"
    by (rule ceil_log_mono) (use le in simp)
  show ?thesis
    unfolding fri_conditioned_residual_query_list_card_bound_def
    by (rule sum_mono2) (use ceil_le in auto)
qed

lemma card_fri_conditioned_composition_residual_query_lists_uniform:
  assumes composition_roots:
      "length (staged_composition_fri_roots data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
    and composition_challenges:
      "length (staged_composition_fri_challenges data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
  shows
    "card (fri_conditioned_composition_residual_query_lists data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound maxDegree"
proof (rule order_trans)
  show
    "card (fri_conditioned_composition_residual_query_lists data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound
        (to_nat (staged_degree data))"
    by (rule card_fri_conditioned_composition_residual_query_lists[
        OF composition_roots composition_challenges degree_bound])
  show
    "fri_conditioned_residual_query_list_card_bound
        (to_nat (staged_degree data)) \<le>
      fri_conditioned_residual_query_list_card_bound maxDegree"
    by (rule fri_conditioned_residual_query_list_card_bound_mono[
        OF degree_bound])
qed

lemma
  fri_conditioned_composition_residual_query_lists_relation_fiber_bound_uniform:
  assumes composition_roots:
      "length (staged_composition_fri_roots data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
    and composition_challenges:
      "length (staged_composition_fri_challenges data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
  shows
    "query_index_raw_list_relation_fiber_bound
      (fri_conditioned_composition_residual_query_lists data query_start) \<le>
      rounds *
        query_raw_preimage_card_envelope
          (rounds *
            fri_conditioned_residual_query_list_card_bound maxDegree)"
proof (rule query_index_raw_list_relation_fiber_bound_by_card)
  show
    "fri_conditioned_composition_residual_query_lists data query_start \<subseteq>
      fri_query_index_list_space"
    by (rule fri_conditioned_composition_residual_query_lists_subset)
  show
    "card (fri_conditioned_composition_residual_query_lists data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound maxDegree"
    by (rule
        card_fri_conditioned_composition_residual_query_lists_uniform[
          OF composition_roots composition_challenges degree_bound])
qed

lemma card_fri_conditioned_composition_residual_query_lists_uniform_all:
  assumes composition_roots:
      "length (staged_composition_fri_roots data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
    and composition_challenges:
      "length (staged_composition_fri_challenges data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
  shows
    "card (fri_conditioned_composition_residual_query_lists data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound maxDegree"
proof (cases "to_nat (staged_degree data) \<le> maxDegree")
  case True
  show ?thesis
    by (rule card_fri_conditioned_composition_residual_query_lists_uniform[
        OF composition_roots composition_challenges True])
next
  case False
  show ?thesis
    unfolding fri_conditioned_composition_residual_query_lists_def
      if_not_P[OF False]
    by simp
qed

lemma
  fri_conditioned_composition_residual_query_lists_relation_fiber_bound_all:
  assumes composition_roots:
      "length (staged_composition_fri_roots data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
    and composition_challenges:
      "length (staged_composition_fri_challenges data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
  shows
    "query_index_raw_list_relation_fiber_bound
      (fri_conditioned_composition_residual_query_lists data query_start) \<le>
      rounds *
        query_raw_preimage_card_envelope
          (rounds *
            fri_conditioned_residual_query_list_card_bound maxDegree)"
proof (cases "to_nat (staged_degree data) \<le> maxDegree")
  case True
  show ?thesis
    by (rule
        fri_conditioned_composition_residual_query_lists_relation_fiber_bound_uniform[
          OF composition_roots composition_challenges True])
next
  case False
  show ?thesis
    unfolding fri_conditioned_composition_residual_query_lists_def
      if_not_P[OF False]
      query_index_raw_list_relation_fiber_bound_def
      query_index_raw_list_position_values_def
      query_index_raw_list_preimage_def
    by simp
qed

definition fri_conditioned_trace_query_head_lists
  :: "('f \<times> 'f list \<times> 'f) \<Rightarrow> 'f protocol_channel \<Rightarrow>
      'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_conditioned_trace_query_head_lists prefix prefix_state data query_start =
    fri_conditioned_trace_residual_query_lists data query_start"

definition fri_conditioned_composition_query_head_lists
  :: "('f \<times> 'f list \<times> 'f) \<Rightarrow> 'f protocol_channel \<Rightarrow>
      'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_conditioned_composition_query_head_lists
      prefix prefix_state data query_start =
    fri_conditioned_composition_residual_query_lists data query_start"

lemma
  ro_checked_staged_after_first_trace_fri_root_prefix_program_output_fri_lengths:
  assumes prefix_eq: "prefix = (fr, [], first_root)"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              prefix)
            s)"
  shows
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (Suc (to_nat (staged_degree data))) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (Suc (to_nat (staged_degree data)))"
proof (cases "ceil_log clength")
  case 0
  from outcome obtain trace_final as dg s6
      composition_roots composition_bs s7 composition_final where
    composition_out:
      "Some ((composition_roots, composition_bs), s7) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (Suc (to_nat dg))) [])
            s6)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = [],
         staged_trace_fri_challenges = [],
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = []\<rparr>"
    unfolding prefix_eq
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def 0
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
  have composition_lengths:
      "length composition_roots = ceil_log (Suc (to_nat dg)) \<and>
       length composition_bs = ceil_log (Suc (to_nat dg))"
    using ro_staged_composition_fri_program_output_lengths[
        OF composition_out]
    by simp
  show ?thesis
    using 0 data_eq composition_lengths by simp
next
  case (Suc n)
  from outcome obtain b s1 trace_roots trace_bs' s2
      trace_final as dg s8 composition_roots composition_bs s9
      composition_final where
    trace_out:
      "Some ((trace_roots, trace_bs'), s2) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A 1 n [b])
            s1)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s9) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (Suc (to_nat dg))) [])
            s8)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = first_root # trace_roots,
         staged_trace_fri_challenges = trace_bs',
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = []\<rparr>"
    unfolding prefix_eq
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def Suc
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
  have trace_lengths:
      "length trace_roots = n \<and> length trace_bs' = Suc n"
    using ro_staged_trace_fri_program_output_lengths[OF trace_out]
    by simp
  have composition_lengths:
      "length composition_roots = ceil_log (Suc (to_nat dg)) \<and>
       length composition_bs = ceil_log (Suc (to_nat dg))"
    using ro_staged_composition_fri_program_output_lengths[
        OF composition_out]
    by simp
  show ?thesis
    using Suc data_eq trace_lengths composition_lengths by simp
qed

lemma ro_staged_first_trace_fri_root_prefix_program_output_shape:
  assumes outcome:
      "Some ((prefix, prefix_state), t) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A) s)"
  shows "\<exists>fr first_root. prefix = (fr, [], first_root)"
  using outcome
  unfolding ro_staged_first_trace_fri_root_prefix_program_def
  by (cases "ceil_log clength")
    (auto elim!: set_dist_bindE split: prod.splits)

lemma ro_checked_staged_first_root_query_head_program_output_fri_lengths:
  assumes outcome:
      "Some (((prefix, prefix_state), data, query_start), t) \<in>
        set_dist
          (execute (ro_checked_staged_first_root_query_head_program A) s)"
  shows
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (Suc (to_nat (staged_degree data))) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (Suc (to_nat (staged_degree data)))"
proof -
  from outcome obtain prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A) s)"
    and after:
      "Some (data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              prefix)
            prefix_final)"
    unfolding ro_checked_staged_first_root_query_head_program_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  from ro_staged_first_trace_fri_root_prefix_program_output_shape[
      OF prefix_out]
  obtain fr first_root where prefix_eq: "prefix = (fr, [], first_root)"
    by blast
  show ?thesis
    by (rule
        ro_checked_staged_after_first_trace_fri_root_prefix_program_output_fri_lengths[
          OF prefix_eq after])
qed

lemma wp_ro_checked_staged_trace_conditioned_residual_fresh_bound:
  "wp_event
    (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
    (ro_query_head_dependent_query_index_list_fresh_hit
      fri_conditioned_trace_query_head_lists)
    adversary_initial_state \<le>
    nnreal (fri_conditioned_residual_query_list_card_bound (clength - 1)) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof (rule
    wp_ro_checked_staged_transcript_query_head_dependent_fresh_bound)
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "fri_conditioned_trace_query_head_lists
        prefix prefix_state data query_start \<subseteq>
      fri_query_index_list_space"
    unfolding fri_conditioned_trace_query_head_lists_def
    by (rule fri_conditioned_trace_residual_query_lists_subset)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
  show
    "card
      (fri_conditioned_trace_query_head_lists
        prefix prefix_state data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound (clength - 1)"
    unfolding fri_conditioned_trace_query_head_lists_def
    by (rule card_fri_conditioned_trace_residual_query_lists)
      (use shape in simp_all)
qed

lemma wp_ro_checked_staged_composition_conditioned_residual_fresh_bound:
  "wp_event
    (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
    (ro_query_head_dependent_query_index_list_fresh_hit
      fri_conditioned_composition_query_head_lists)
    adversary_initial_state \<le>
    nnreal (fri_conditioned_residual_query_list_card_bound maxDegree) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof (rule
    wp_ro_checked_staged_transcript_query_head_dependent_fresh_bound)
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "fri_conditioned_composition_query_head_lists
        prefix prefix_state data query_start \<subseteq>
      fri_query_index_list_space"
    unfolding fri_conditioned_composition_query_head_lists_def
    by (rule fri_conditioned_composition_residual_query_lists_subset)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  have shape:
      "length (staged_composition_fri_roots data) =
         ceil_log (Suc (to_nat (staged_degree data))) \<and>
       length (staged_composition_fri_challenges data) =
         ceil_log (Suc (to_nat (staged_degree data)))"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
  show
    "card
      (fri_conditioned_composition_query_head_lists
        prefix prefix_state data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound maxDegree"
    unfolding fri_conditioned_composition_query_head_lists_def
    by (rule
        card_fri_conditioned_composition_residual_query_lists_uniform_all)
      (use shape in simp_all)
qed

lemma wp_ro_checked_staged_trace_conditioned_residual_query_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_phase_relation_hit A
        fri_conditioned_trace_query_head_lists)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (rounds *
          query_raw_preimage_card_envelope
            (rounds *
              fri_conditioned_residual_query_list_card_bound (clength - 1)))
        (sum_list (query_opening_budgets budgets) + rounds +
          rounds * ro_checked_query_round_transcript_bound)"
proof (rule wp_ro_query_head_dependent_query_phase_relation_hit_bound[
    OF wf controlled])
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
  show
    "query_index_raw_list_relation_fiber_bound
      (fri_conditioned_trace_query_head_lists
        prefix prefix_state data query_start) \<le>
      rounds *
        query_raw_preimage_card_envelope
          (rounds *
            fri_conditioned_residual_query_list_card_bound (clength - 1))"
    unfolding fri_conditioned_trace_query_head_lists_def
    by (rule
        fri_conditioned_trace_residual_query_lists_relation_fiber_bound)
      (use shape in simp_all)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show "length (staged_trace_fri_roots data) = ceil_log clength"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "length (staged_composition_fri_roots data) \<le>
      ceil_log (maxDegree + 1)"
    using
      ro_checked_staged_first_root_query_head_program_output_lengths_all_rounds[
        OF head]
    by blast
qed

lemma
  wp_ro_checked_staged_composition_conditioned_residual_query_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_phase_relation_hit A
        fri_conditioned_composition_query_head_lists)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (rounds *
          query_raw_preimage_card_envelope
            (rounds *
              fri_conditioned_residual_query_list_card_bound maxDegree))
        (sum_list (query_opening_budgets budgets) + rounds +
          rounds * ro_checked_query_round_transcript_bound)"
proof (rule wp_ro_query_head_dependent_query_phase_relation_hit_bound[
    OF wf controlled])
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  have shape:
      "length (staged_composition_fri_roots data) =
         ceil_log (Suc (to_nat (staged_degree data))) \<and>
       length (staged_composition_fri_challenges data) =
         ceil_log (Suc (to_nat (staged_degree data)))"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
  show
    "query_index_raw_list_relation_fiber_bound
      (fri_conditioned_composition_query_head_lists
        prefix prefix_state data query_start) \<le>
      rounds *
        query_raw_preimage_card_envelope
          (rounds *
            fri_conditioned_residual_query_list_card_bound maxDegree)"
    unfolding fri_conditioned_composition_query_head_lists_def
    by (rule
        fri_conditioned_composition_residual_query_lists_relation_fiber_bound_all)
      (use shape in simp_all)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show "length (staged_trace_fri_roots data) = ceil_log clength"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "length (staged_composition_fri_roots data) \<le>
      ceil_log (maxDegree + 1)"
    using
      ro_checked_staged_first_root_query_head_program_output_lengths_all_rounds[
        OF head]
    by blast
qed

definition fri_conditioned_combined_query_head_lists
  :: "('f \<times> 'f list \<times> 'f) \<Rightarrow> 'f protocol_channel \<Rightarrow>
      'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_conditioned_combined_query_head_lists
      prefix prefix_state data query_start =
    fri_conditioned_trace_query_head_lists
        prefix prefix_state data query_start \<union>
      fri_conditioned_composition_query_head_lists
        prefix prefix_state data query_start"

lemma fri_conditioned_combined_query_head_lists_subset:
  "fri_conditioned_combined_query_head_lists
      prefix prefix_state data query_start \<subseteq> fri_query_index_list_space"
  unfolding fri_conditioned_combined_query_head_lists_def
  using fri_conditioned_trace_residual_query_lists_subset
    fri_conditioned_composition_residual_query_lists_subset
  unfolding fri_conditioned_trace_query_head_lists_def
    fri_conditioned_composition_query_head_lists_def
  by blast

lemma card_fri_conditioned_combined_query_head_lists:
  assumes shape:
      "length (staged_trace_fri_roots data) = ceil_log clength"
      "length (staged_trace_fri_challenges data) = ceil_log clength"
      "length (staged_composition_fri_roots data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
      "length (staged_composition_fri_challenges data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
  shows
    "card
      (fri_conditioned_combined_query_head_lists
        prefix prefix_state data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound (clength - 1) +
        fri_conditioned_residual_query_list_card_bound maxDegree"
proof -
  have trace:
      "card
        (fri_conditioned_trace_query_head_lists
          prefix prefix_state data query_start) \<le>
        fri_conditioned_residual_query_list_card_bound (clength - 1)"
    unfolding fri_conditioned_trace_query_head_lists_def
    by (rule card_fri_conditioned_trace_residual_query_lists[
        OF shape(1,2)])
  have composition:
      "card
        (fri_conditioned_composition_query_head_lists
          prefix prefix_state data query_start) \<le>
        fri_conditioned_residual_query_list_card_bound maxDegree"
    unfolding fri_conditioned_composition_query_head_lists_def
    by (rule
        card_fri_conditioned_composition_residual_query_lists_uniform_all[
          OF shape(3,4)])
  have union:
      "card
        (fri_conditioned_trace_query_head_lists
            prefix prefix_state data query_start \<union>
          fri_conditioned_composition_query_head_lists
            prefix prefix_state data query_start) \<le>
        card
          (fri_conditioned_trace_query_head_lists
            prefix prefix_state data query_start) +
        card
          (fri_conditioned_composition_query_head_lists
            prefix prefix_state data query_start)"
    by (rule card_Un_le)
  show ?thesis
    unfolding fri_conditioned_combined_query_head_lists_def
    by (rule order_trans[OF union]) (use trace composition in simp)
qed

lemma
  fri_conditioned_combined_query_head_lists_relation_fiber_bound:
  assumes shape:
      "length (staged_trace_fri_roots data) = ceil_log clength"
      "length (staged_trace_fri_challenges data) = ceil_log clength"
      "length (staged_composition_fri_roots data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
      "length (staged_composition_fri_challenges data) =
        ceil_log (Suc (to_nat (staged_degree data)))"
  shows
    "query_index_raw_list_relation_fiber_bound
      (fri_conditioned_combined_query_head_lists
        prefix prefix_state data query_start) \<le>
      rounds *
        query_raw_preimage_card_envelope
          (rounds *
            (fri_conditioned_residual_query_list_card_bound (clength - 1) +
             fri_conditioned_residual_query_list_card_bound maxDegree))"
proof (rule query_index_raw_list_relation_fiber_bound_by_card)
  show
    "fri_conditioned_combined_query_head_lists
        prefix prefix_state data query_start \<subseteq> fri_query_index_list_space"
    by (rule fri_conditioned_combined_query_head_lists_subset)
  show
    "card
      (fri_conditioned_combined_query_head_lists
        prefix prefix_state data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound (clength - 1) +
        fri_conditioned_residual_query_list_card_bound maxDegree"
    by (rule card_fri_conditioned_combined_query_head_lists[OF shape])
qed

lemma wp_ro_checked_staged_combined_conditioned_residual_fresh_bound:
  "wp_event
    (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
    (ro_query_head_dependent_query_index_list_fresh_hit
      fri_conditioned_combined_query_head_lists)
    adversary_initial_state \<le>
    nnreal
      (fri_conditioned_residual_query_list_card_bound (clength - 1) +
       fri_conditioned_residual_query_list_card_bound maxDegree) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof (rule
    wp_ro_checked_staged_transcript_query_head_dependent_fresh_bound)
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "fri_conditioned_combined_query_head_lists
        prefix prefix_state data query_start \<subseteq> fri_query_index_list_space"
    by (rule fri_conditioned_combined_query_head_lists_subset)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (Suc (to_nat (staged_degree data))) \<and>
       length (staged_composition_fri_challenges data) =
         ceil_log (Suc (to_nat (staged_degree data)))"
    by (rule
        ro_checked_staged_first_root_query_head_program_output_fri_lengths[
          OF head])
  show
    "card
      (fri_conditioned_combined_query_head_lists
        prefix prefix_state data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound (clength - 1) +
        fri_conditioned_residual_query_list_card_bound maxDegree"
    by (rule card_fri_conditioned_combined_query_head_lists)
      (use shape in simp_all)
qed

lemma
  wp_ro_checked_staged_combined_conditioned_residual_query_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_phase_relation_hit A
        fri_conditioned_combined_query_head_lists)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (rounds *
          query_raw_preimage_card_envelope
            (rounds *
              (fri_conditioned_residual_query_list_card_bound (clength - 1) +
               fri_conditioned_residual_query_list_card_bound maxDegree)))
        (sum_list (query_opening_budgets budgets) + rounds +
          rounds * ro_checked_query_round_transcript_bound)"
proof (rule wp_ro_query_head_dependent_query_phase_relation_hit_bound[
    OF wf controlled])
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (Suc (to_nat (staged_degree data))) \<and>
       length (staged_composition_fri_challenges data) =
         ceil_log (Suc (to_nat (staged_degree data)))"
    by (rule
        ro_checked_staged_first_root_query_head_program_output_fri_lengths[
          OF head])
  show
    "query_index_raw_list_relation_fiber_bound
      (fri_conditioned_combined_query_head_lists
        prefix prefix_state data query_start) \<le>
      rounds *
        query_raw_preimage_card_envelope
          (rounds *
            (fri_conditioned_residual_query_list_card_bound (clength - 1) +
             fri_conditioned_residual_query_list_card_bound maxDegree))"
    by (rule fri_conditioned_combined_query_head_lists_relation_fiber_bound)
      (use shape in simp_all)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show "length (staged_trace_fri_roots data) = ceil_log clength"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "length (staged_composition_fri_roots data) \<le>
      ceil_log (maxDegree + 1)"
    using
      ro_checked_staged_first_root_query_head_program_output_lengths_all_rounds[
        OF head]
    by blast
qed

end
end
