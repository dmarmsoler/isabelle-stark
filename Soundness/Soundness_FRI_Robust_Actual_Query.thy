theory Soundness_FRI_Robust_Actual_Query
  imports
    Soundness_FRI_Robust_Conceptual_Split
    Stark.Soundness_FRI_Query_Head_Adaptive_Rectangle_Family
begin

context soundness
begin

definition fri_robust_residual_layer_query_indices
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow>
    nat \<Rightarrow> nat set"
where
  "fri_robust_residual_layer_query_indices roots challenges layers i =
    fri_conditioned_query_indices roots i
      (fri_robust_conditioned_agreement_indices challenges layers i)"

lemma fri_robust_residual_layer_query_indices_subset:
  "fri_robust_residual_layer_query_indices roots challenges layers i
    \<subseteq> query_sample_space"
  unfolding fri_robust_residual_layer_query_indices_def
  by (rule fri_conditioned_query_indices_subset)

definition fri_robust_residual_active_layers
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
    'f \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "fri_robust_residual_active_layers d K roots challenges
      final_value prefix_state =
    {i. i < length challenges \<and>
      \<not> fri_canonical_layer_close d
        (fri_robust_conditioned_layers (length challenges)
          (fri_builder_conceptual_layers roots prefix_state final_value))
        (fri_linear_radius (length challenges) K) i \<and>
      fri_canonical_layer_close d
        (fri_robust_conditioned_layers (length challenges)
          (fri_builder_conceptual_layers roots prefix_state final_value))
        (fri_linear_radius (length challenges) K) (Suc i) \<and>
      card (fri_robust_conditioned_agreement_indices challenges
        (fri_builder_conceptual_layers roots prefix_state final_value) i)
        \<le> length (fri_canonical_domain_at (Suc i)) -
          fri_linear_margin K i}"

lemma finite_fri_robust_residual_active_layers[simp]:
  "finite (fri_robust_residual_active_layers d K roots challenges
    final_value prefix_state)"
  unfolding fri_robust_residual_active_layers_def
  by (rule finite_subset[OF _ finite_lessThan[of "length challenges"]])
    auto

definition fri_robust_quantitative_residual_query_lists
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
    'f \<Rightarrow> 'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_robust_quantitative_residual_query_lists d K roots challenges
      final_value prefix_state =
    {qs \<in> fri_query_index_list_space.
      \<exists>i \<in> fri_robust_residual_active_layers
          d K roots challenges final_value prefix_state.
        qs \<in> fri_robust_conditioned_residual_query_lists
          roots challenges
          (fri_builder_conceptual_layers roots prefix_state final_value) i}"

lemma fri_robust_quantitative_residual_query_lists_subset:
  "fri_robust_quantitative_residual_query_lists d K roots challenges
      final_value prefix_state \<subseteq> fri_query_index_list_space"
  unfolding fri_robust_quantitative_residual_query_lists_def by auto

lemma fri_robust_quantitative_residual_query_lists_rectangle_cover:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "fri_robust_quantitative_residual_query_lists d K roots challenges
        final_value prefix_state
      \<subseteq>
      (\<Union>i\<in>fri_robust_residual_active_layers d K roots challenges
          final_value prefix_state.
        fri_conditioned_query_lists
          (fri_robust_residual_layer_query_indices roots challenges
            (fri_builder_conceptual_layers
              roots prefix_state final_value) i))"
proof
  let ?layers =
    "fri_builder_conceptual_layers roots prefix_state final_value"
  fix qs
  assume qs_in:
      "qs \<in> fri_robust_quantitative_residual_query_lists
        d K roots challenges final_value prefix_state"
  then obtain i where active:
      "i \<in> fri_robust_residual_active_layers
        d K roots challenges final_value prefix_state"
    and qs_space: "qs \<in> fri_query_index_list_space"
    and residual:
      "qs \<in> fri_robust_conditioned_residual_query_lists
        roots challenges ?layers i"
    unfolding fri_robust_quantitative_residual_query_lists_def by blast
  from active have i_bound: "i < length challenges"
    unfolding fri_robust_residual_active_layers_def by auto
  have layer_bound: "i < length roots"
    using i_bound lengths by simp
  have layer_subset:
      "fri_robust_conditioned_residual_query_lists
          roots challenges ?layers i \<inter> fri_query_index_list_space
        \<subseteq>
        fri_conditioned_query_lists
          (fri_robust_residual_layer_query_indices
            roots challenges ?layers i)"
    unfolding fri_robust_residual_layer_query_indices_def
    by (rule fri_robust_conditioned_residual_restricted_subset[
          OF eval_power roots_le layer_bound])
  have rectangle:
      "qs \<in> fri_conditioned_query_lists
        (fri_robust_residual_layer_query_indices
          roots challenges ?layers i)"
    by (rule set_mp[OF layer_subset])
      (use residual qs_space in blast)
  show
      "qs \<in>
        (\<Union>i\<in>fri_robust_residual_active_layers
            d K roots challenges final_value prefix_state.
          fri_conditioned_query_lists
            (fri_robust_residual_layer_query_indices roots challenges
              ?layers i))"
    using active rectangle by blast
qed


lemma card_fri_robust_residual_layer_query_indices_active:
  assumes eval_power: "clength * scale = 2 ^ N"
    and exponent_fit: "length challenges + K \<le> N"
    and lengths: "length challenges = length roots"
    and active:
      "i \<in> fri_robust_residual_active_layers
        d K roots challenges final_value prefix_state"
  shows
    "card
      (fri_robust_residual_layer_query_indices roots challenges
        (fri_builder_conceptual_layers roots prefix_state final_value) i)
      \<le>
      modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) -
          fri_linear_margin K i)"
proof -
  let ?layers =
    "fri_builder_conceptual_layers roots prefix_state final_value"
  from active have i_bound: "i < length challenges"
    and agreement_card:
      "card (fri_robust_conditioned_agreement_indices
        challenges ?layers i) \<le>
        length (fri_canonical_domain_at (Suc i)) -
          fri_linear_margin K i"
    unfolding fri_robust_residual_active_layers_def by auto
  have next_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        length (?layers ! Suc i)"
    by (rule fri_builder_conceptual_layers_cover)
      (use i_bound lengths in simp)
  have suc_le_N: "Suc i \<le> N"
    using i_bound exponent_fit by linarith
  have modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
    by (rule fri_canonical_domain_at_pos[OF eval_power suc_le_N])
  show ?thesis
    unfolding fri_robust_residual_layer_query_indices_def
    by (rule card_fri_conditioned_query_indices[
          OF modulus_pos
            fri_robust_conditioned_agreement_indices_subset[
              OF next_cover]
            agreement_card])
qed

definition fri_robust_residual_rectangle_layer_raw_card_bound
  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "fri_robust_residual_rectangle_layer_raw_card_bound K i =
    query_raw_preimage_card_envelope
      (modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) -
          fri_linear_margin K i))"

definition ro_checked_staged_robust_residual_rectangle_error_adaptive
  :: "nat \<Rightarrow> nat \<Rightarrow> staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_robust_residual_rectangle_error_adaptive d K budgets =
    (\<Sum>i<ceil_log (Suc d).
      (nnreal
          (fri_robust_residual_rectangle_layer_raw_card_bound K i) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets))"

lemma fri_robust_residual_active_layer_probability_sum_le:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and exponent_fit: "length challenges + K \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "(\<Sum>i\<in>fri_robust_residual_active_layers
        d K roots challenges final_value prefix_state.
      (nnreal
          (query_raw_preimage_card_envelope
            (card
              (fri_robust_residual_layer_query_indices roots challenges
                (fri_builder_conceptual_layers roots prefix_state final_value)
                i))) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets))
    \<le> ro_checked_staged_robust_residual_rectangle_error_adaptive
        d K budgets"
proof -
  let ?A =
    "fri_robust_residual_active_layers
      d K roots challenges final_value prefix_state"
  let ?B = "{..<ceil_log (Suc d)}"
  let ?f =
    "\<lambda>i.
      (nnreal
          (query_raw_preimage_card_envelope
            (card
              (fri_robust_residual_layer_query_indices roots challenges
                (fri_builder_conceptual_layers roots prefix_state final_value)
                i))) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets)"
  let ?g =
    "\<lambda>i.
      (nnreal (fri_robust_residual_rectangle_layer_raw_card_bound K i) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets)"
  have subset: "?A \<subseteq> ?B"
    using round_count
    unfolding fri_robust_residual_active_layers_def
    by auto
  have local: "(\<Sum>i\<in>?A. ?f i) \<le> (\<Sum>i\<in>?A. ?g i)"
  proof (rule sum_mono)
    fix i
    assume i_active: "i \<in> ?A"
    let ?I =
      "fri_robust_residual_layer_query_indices roots challenges
        (fri_builder_conceptual_layers roots prefix_state final_value) i"
    let ?E =
      "modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) -
          fri_linear_margin K i)"
    have I_card: "card ?I \<le> ?E"
      by (rule card_fri_robust_residual_layer_query_indices_active[
            OF eval_power exponent_fit lengths i_active])
    have raw_card:
        "query_raw_preimage_card_envelope (card ?I) \<le>
          query_raw_preimage_card_envelope ?E"
      by (rule query_raw_preimage_card_envelope_mono[OF I_card])
    have fraction_le:
        "nnreal (query_raw_preimage_card_envelope (card ?I)) /
            nnreal size
          \<le>
          nnreal (query_raw_preimage_card_envelope ?E) / nnreal size"
      by (rule nnreal_nat_divide_right_mono[OF raw_card])
    show "?f i \<le> ?g i"
      unfolding
        fri_robust_residual_rectangle_layer_raw_card_bound_def Let_def
      by (rule power_mono[OF fraction_le]) simp
  qed
  have extend: "(\<Sum>i\<in>?A. ?g i) \<le> (\<Sum>i\<in>?B. ?g i)"
    by (rule sum_mono2) (use subset in auto)
  show ?thesis
    unfolding
      ro_checked_staged_robust_residual_rectangle_error_adaptive_def Let_def
    by (rule order_trans[OF local extend])
qed


definition fri_robust_trace_residual_query_lists
  :: "nat \<Rightarrow> 'f staged_proof_data \<Rightarrow>
    'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_robust_trace_residual_query_lists K data query_start =
    fri_robust_quantitative_residual_query_lists
      (clength - 1) K
      (staged_trace_fri_roots data)
      (staged_trace_fri_challenges data)
      (staged_trace_final data) query_start"

definition fri_robust_composition_residual_query_lists
  :: "nat \<Rightarrow> 'f staged_proof_data \<Rightarrow>
    'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_robust_composition_residual_query_lists K data query_start =
    (if to_nat (staged_degree data) \<le> maxDegree then
      fri_robust_quantitative_residual_query_lists
        (to_nat (staged_degree data)) K
        (staged_composition_fri_roots data)
        (staged_composition_fri_challenges data)
        (staged_composition_final data) query_start
     else {})"

lemma fri_robust_trace_residual_query_lists_subset:
  "fri_robust_trace_residual_query_lists K data query_start
    \<subseteq> fri_query_index_list_space"
  unfolding fri_robust_trace_residual_query_lists_def
  by (rule fri_robust_quantitative_residual_query_lists_subset)

lemma fri_robust_composition_residual_query_lists_subset:
  "fri_robust_composition_residual_query_lists K data query_start
    \<subseteq> fri_query_index_list_space"
  unfolding fri_robust_composition_residual_query_lists_def
    fri_robust_quantitative_residual_query_lists_def
  by auto

definition fri_robust_trace_query_head_lists
  :: "nat \<Rightarrow> ('f \<times> 'f list \<times> 'f) \<Rightarrow>
    'f protocol_channel \<Rightarrow> 'f staged_proof_data \<Rightarrow>
    'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_robust_trace_query_head_lists K
      prefix prefix_state data query_start =
    fri_robust_trace_residual_query_lists K data query_start"

definition fri_robust_composition_query_head_lists
  :: "nat \<Rightarrow> ('f \<times> 'f list \<times> 'f) \<Rightarrow>
    'f protocol_channel \<Rightarrow> 'f staged_proof_data \<Rightarrow>
    'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_robust_composition_query_head_lists K
      prefix prefix_state data query_start =
    fri_robust_composition_residual_query_lists K data query_start"

definition fri_robust_combined_query_head_lists
  :: "nat \<Rightarrow> ('f \<times> 'f list \<times> 'f) \<Rightarrow>
    'f protocol_channel \<Rightarrow> 'f staged_proof_data \<Rightarrow>
    'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_robust_combined_query_head_lists K
      prefix prefix_state data query_start =
    fri_robust_trace_query_head_lists K
        prefix prefix_state data query_start \<union>
      fri_robust_composition_query_head_lists K
        prefix prefix_state data query_start"

lemma ro_checked_staged_robust_residual_rectangle_error_adaptive_mono:
  assumes "d \<le> D"
  shows
    "ro_checked_staged_robust_residual_rectangle_error_adaptive
        d K budgets
      \<le> ro_checked_staged_robust_residual_rectangle_error_adaptive
        D K budgets"
  unfolding
    ro_checked_staged_robust_residual_rectangle_error_adaptive_def
  by (rule sum_mono2)
    (use ceil_log_mono[of "Suc d" "Suc D"] assms in auto)


lemma wp_ro_checked_staged_trace_robust_residual_actual_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_exponent_fit: "ceil_log clength + K \<le> N"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit
        (fri_robust_trace_query_head_lists K))
      adversary_initial_state
    \<le> ro_checked_staged_robust_residual_rectangle_error_adaptive
        (clength - 1) K budgets"
proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_family_bound[
      OF wf controlled,
      where
        K="\<lambda>prefix prefix_state data query_start.
          fri_robust_residual_active_layers (clength - 1) K
            (staged_trace_fri_roots data)
            (staged_trace_fri_challenges data)
            (staged_trace_final data) query_start"
      and
        I="\<lambda>prefix prefix_state data query_start i.
          fri_robust_residual_layer_query_indices
            (staged_trace_fri_roots data)
            (staged_trace_fri_challenges data)
            (fri_builder_conceptual_layers
              (staged_trace_fri_roots data) query_start
              (staged_trace_final data))
            i"])
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "finite
      (fri_robust_residual_active_layers (clength - 1) K
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (staged_trace_final data) query_start)"
    by simp
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
  have roots_le: "length (staged_trace_fri_roots data) \<le> N"
    using shape trace_exponent_fit by linarith
  have lengths:
      "length (staged_trace_fri_challenges data) =
        length (staged_trace_fri_roots data)"
    using shape by simp
  show
    "fri_robust_trace_query_head_lists K
        prefix prefix_state data query_start
      \<subseteq>
      (\<Union>i\<in>fri_robust_residual_active_layers (clength - 1) K
          (staged_trace_fri_roots data)
          (staged_trace_fri_challenges data)
          (staged_trace_final data) query_start.
        fri_conditioned_query_lists
          (fri_robust_residual_layer_query_indices
            (staged_trace_fri_roots data)
            (staged_trace_fri_challenges data)
            (fri_builder_conceptual_layers
              (staged_trace_fri_roots data) query_start
              (staged_trace_final data))
            i))"
    unfolding fri_robust_trace_query_head_lists_def
      fri_robust_trace_residual_query_lists_def
    by (rule fri_robust_quantitative_residual_query_lists_rectangle_cover[
          OF eval_power roots_le lengths])
next
  fix prefix prefix_state data query_start t i
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
    and
    "i \<in>
      fri_robust_residual_active_layers (clength - 1) K
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (staged_trace_final data) query_start"
  show
    "fri_robust_residual_layer_query_indices
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (fri_builder_conceptual_layers
          (staged_trace_fri_roots data) query_start
          (staged_trace_final data))
        i
      \<subseteq> query_sample_space"
    by (rule fri_robust_residual_layer_query_indices_subset)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
  have round_count:
      "length (staged_trace_fri_challenges data) =
        ceil_log (Suc (clength - 1))"
    using shape clength_pos by simp
  have exponent_fit:
      "length (staged_trace_fri_challenges data) + K \<le> N"
    using shape trace_exponent_fit by simp
  have lengths:
      "length (staged_trace_fri_challenges data) =
        length (staged_trace_fri_roots data)"
    using shape by simp
  show
    "(\<Sum>i\<in>fri_robust_residual_active_layers (clength - 1) K
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (staged_trace_final data) query_start.
      (nnreal
          (query_raw_preimage_card_envelope
            (card
              (fri_robust_residual_layer_query_indices
                (staged_trace_fri_roots data)
                (staged_trace_fri_challenges data)
                (fri_builder_conceptual_layers
                  (staged_trace_fri_roots data) query_start
                  (staged_trace_final data))
                i))) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets))
    \<le> ro_checked_staged_robust_residual_rectangle_error_adaptive
        (clength - 1) K budgets"
    by (rule fri_robust_residual_active_layer_probability_sum_le[
          OF eval_power round_count exponent_fit lengths])
qed


lemma wp_ro_checked_staged_composition_robust_residual_actual_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and composition_exponent_fit:
      "ceil_log (Suc maxDegree) + K \<le> N"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit
        (fri_robust_composition_query_head_lists K))
      adversary_initial_state
    \<le> ro_checked_staged_robust_residual_rectangle_error_adaptive
        maxDegree K budgets"
proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_family_bound[
      OF wf controlled,
      where
        K="\<lambda>prefix prefix_state data query_start.
          if to_nat (staged_degree data) \<le> maxDegree then
            fri_robust_residual_active_layers
              (to_nat (staged_degree data)) K
              (staged_composition_fri_roots data)
              (staged_composition_fri_challenges data)
              (staged_composition_final data) query_start
          else {}"
      and
        I="\<lambda>prefix prefix_state data query_start i.
          fri_robust_residual_layer_query_indices
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (fri_builder_conceptual_layers
              (staged_composition_fri_roots data) query_start
              (staged_composition_final data))
            i"])
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "finite
      (if to_nat (staged_degree data) \<le> maxDegree then
        fri_robust_residual_active_layers
          (to_nat (staged_degree data)) K
          (staged_composition_fri_roots data)
          (staged_composition_fri_challenges data)
          (staged_composition_final data) query_start
       else {})"
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
    "fri_robust_composition_query_head_lists K
        prefix prefix_state data query_start
      \<subseteq>
      (\<Union>i\<in>
        (if to_nat (staged_degree data) \<le> maxDegree then
          fri_robust_residual_active_layers
            (to_nat (staged_degree data)) K
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (staged_composition_final data) query_start
         else {}).
        fri_conditioned_query_lists
          (fri_robust_residual_layer_query_indices
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (fri_builder_conceptual_layers
              (staged_composition_fri_roots data) query_start
              (staged_composition_final data))
            i))"
  proof (cases "to_nat (staged_degree data) \<le> maxDegree")
    case True
    have shape:
        "length (staged_composition_fri_roots data) =
            ceil_log (Suc (to_nat (staged_degree data))) \<and>
         length (staged_composition_fri_challenges data) =
            ceil_log (Suc (to_nat (staged_degree data)))"
      using
        ro_checked_staged_first_root_query_head_program_output_fri_lengths[
          OF head]
      by blast
    have log_le:
        "ceil_log (Suc (to_nat (staged_degree data))) \<le>
          ceil_log (Suc maxDegree)"
      by (rule ceil_log_mono) (use True in simp)
    have roots_le:
        "length (staged_composition_fri_roots data) \<le> N"
      using shape log_le composition_exponent_fit by linarith
    have lengths:
        "length (staged_composition_fri_challenges data) =
          length (staged_composition_fri_roots data)"
      using shape by simp
    show ?thesis
      unfolding fri_robust_composition_query_head_lists_def
        fri_robust_composition_residual_query_lists_def
        if_P[OF True]
      by (rule
          fri_robust_quantitative_residual_query_lists_rectangle_cover[
            OF eval_power roots_le lengths])
  next
    case False
    show ?thesis
      unfolding fri_robust_composition_query_head_lists_def
        fri_robust_composition_residual_query_lists_def
        if_not_P[OF False]
      by simp
  qed
next
  fix prefix prefix_state data query_start t i
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
    and
    "i \<in>
      (if to_nat (staged_degree data) \<le> maxDegree then
        fri_robust_residual_active_layers
          (to_nat (staged_degree data)) K
          (staged_composition_fri_roots data)
          (staged_composition_fri_challenges data)
          (staged_composition_final data) query_start
       else {})"
  show
    "fri_robust_residual_layer_query_indices
        (staged_composition_fri_roots data)
        (staged_composition_fri_challenges data)
        (fri_builder_conceptual_layers
          (staged_composition_fri_roots data) query_start
          (staged_composition_final data))
        i
      \<subseteq> query_sample_space"
    by (rule fri_robust_residual_layer_query_indices_subset)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "(\<Sum>i\<in>
        (if to_nat (staged_degree data) \<le> maxDegree then
          fri_robust_residual_active_layers
            (to_nat (staged_degree data)) K
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (staged_composition_final data) query_start
         else {}).
      (nnreal
          (query_raw_preimage_card_envelope
            (card
              (fri_robust_residual_layer_query_indices
                (staged_composition_fri_roots data)
                (staged_composition_fri_challenges data)
                (fri_builder_conceptual_layers
                  (staged_composition_fri_roots data) query_start
                  (staged_composition_final data))
                i))) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets))
    \<le> ro_checked_staged_robust_residual_rectangle_error_adaptive
        maxDegree K budgets"
  proof (cases "to_nat (staged_degree data) \<le> maxDegree")
    case True
    have shape:
        "length (staged_composition_fri_roots data) =
            ceil_log (Suc (to_nat (staged_degree data))) \<and>
         length (staged_composition_fri_challenges data) =
            ceil_log (Suc (to_nat (staged_degree data)))"
      using
        ro_checked_staged_first_root_query_head_program_output_fri_lengths[
          OF head]
      by blast
    have round_count:
        "length (staged_composition_fri_challenges data) =
          ceil_log (Suc (to_nat (staged_degree data)))"
      using shape by simp
    have log_le:
        "ceil_log (Suc (to_nat (staged_degree data))) \<le>
          ceil_log (Suc maxDegree)"
      by (rule ceil_log_mono) (use True in simp)
    have exponent_fit:
        "length (staged_composition_fri_challenges data) + K \<le> N"
      using shape log_le composition_exponent_fit by linarith
    have lengths:
        "length (staged_composition_fri_challenges data) =
          length (staged_composition_fri_roots data)"
      using shape by simp
    have local:
      "(\<Sum>i\<in>
          fri_robust_residual_active_layers
            (to_nat (staged_degree data)) K
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (staged_composition_final data) query_start.
        (nnreal
            (query_raw_preimage_card_envelope
              (card
                (fri_robust_residual_layer_query_indices
                  (staged_composition_fri_roots data)
                  (staged_composition_fri_challenges data)
                  (fri_builder_conceptual_layers
                    (staged_composition_fri_roots data) query_start
                    (staged_composition_final data))
                  i))) /
          nnreal size) ^
        (rounds - staged_attacker_query_budget budgets))
      \<le> ro_checked_staged_robust_residual_rectangle_error_adaptive
          (to_nat (staged_degree data)) K budgets"
      by (rule fri_robust_residual_active_layer_probability_sum_le[
            OF eval_power round_count exponent_fit lengths])
    have mono:
        "ro_checked_staged_robust_residual_rectangle_error_adaptive
            (to_nat (staged_degree data)) K budgets
          \<le> ro_checked_staged_robust_residual_rectangle_error_adaptive
              maxDegree K budgets"
      by (rule
          ro_checked_staged_robust_residual_rectangle_error_adaptive_mono[
            OF True])
    show ?thesis
      unfolding if_P[OF True]
      by (rule order_trans[OF local mono])
  next
    case False
    show ?thesis
      unfolding if_not_P[OF False] by simp
  qed
qed


definition
  ro_checked_staged_robust_combined_actual_residual_rectangle_error_adaptive
    :: "nat \<Rightarrow> staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_robust_combined_actual_residual_rectangle_error_adaptive
      K budgets =
    ro_checked_staged_robust_residual_rectangle_error_adaptive
      (clength - 1) K budgets +
    ro_checked_staged_robust_residual_rectangle_error_adaptive
      maxDegree K budgets"

lemma wp_ro_checked_staged_combined_robust_residual_actual_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_exponent_fit: "ceil_log clength + K \<le> N"
    and composition_exponent_fit:
      "ceil_log (Suc maxDegree) + K \<le> N"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit
        (fri_robust_combined_query_head_lists K))
      adversary_initial_state
    \<le>
      ro_checked_staged_robust_combined_actual_residual_rectangle_error_adaptive
        K budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Trace =
    "ro_query_head_dependent_actual_query_index_list_hit
      (fri_robust_trace_query_head_lists K)"
  let ?Composition =
    "ro_query_head_dependent_actual_query_index_list_hit
      (fri_robust_composition_query_head_lists K)"
  have event_eq:
      "ro_query_head_dependent_actual_query_index_list_hit
          (fri_robust_combined_query_head_lists K) =
        (\<lambda>out. ?Trace out \<or> ?Composition out)"
    unfolding ro_query_head_dependent_actual_query_index_list_hit_def
      fri_robust_combined_query_head_lists_def
    by (rule ext) (auto split: option.splits prod.splits)
  have union:
      "wp_event ?M
          (ro_query_head_dependent_actual_query_index_list_hit
            (fri_robust_combined_query_head_lists K))
          adversary_initial_state
        \<le>
        wp_event ?M ?Trace adversary_initial_state +
        wp_event ?M ?Composition adversary_initial_state"
    unfolding event_eq
    by (rule wp_event_union_bound)
  have trace:
      "wp_event ?M ?Trace adversary_initial_state \<le>
        ro_checked_staged_robust_residual_rectangle_error_adaptive
          (clength - 1) K budgets"
    by (rule
        wp_ro_checked_staged_trace_robust_residual_actual_rectangle_bound_adaptive[
          OF wf controlled eval_power trace_exponent_fit])
  have composition:
      "wp_event ?M ?Composition adversary_initial_state \<le>
        ro_checked_staged_robust_residual_rectangle_error_adaptive
          maxDegree K budgets"
    by (rule
        wp_ro_checked_staged_composition_robust_residual_actual_rectangle_bound_adaptive[
          OF wf controlled eval_power composition_exponent_fit])
  show ?thesis
    unfolding
      ro_checked_staged_robust_combined_actual_residual_rectangle_error_adaptive_def
    by (rule order_trans[OF union add_mono[OF trace composition]])
qed

end

end
