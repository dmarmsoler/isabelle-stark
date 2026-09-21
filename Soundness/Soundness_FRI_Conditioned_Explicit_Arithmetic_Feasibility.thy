theory Soundness_FRI_Conditioned_Explicit_Arithmetic_Feasibility
  imports Stark.Soundness_FRI_Conditioned_Explicit_Nontriviality
begin

context soundness
begin

lemma nnreal_nat_ratio_le_twelfth:
  fixes n d :: nat
  assumes positive: "0 < d"
    and dominance: "12 * n \<le> d"
  shows "nnreal n / nnreal d \<le> (1 / 12 :: nnreal)"
proof -
  have scaled_fraction:
      "nnreal (12 * n) / nnreal d \<le> (1 :: nnreal)"
  proof -
    have
        "nnreal (12 * n) / nnreal d \<le> nnreal d / nnreal d"
      by (rule nnreal_nat_divide_right_mono[OF dominance])
    also have "nnreal d / nnreal d = (1 :: nnreal)"
      by (rule nnreal_nat_divide_self) (use positive in simp)
    finally show ?thesis .
  qed
  have divided:
      "(nnreal (12 * n) / nnreal d) / 12 \<le> (1 / 12 :: nnreal)"
    by (rule prob_divide_right_mono[OF scaled_fraction])
  have divide_identity:
      "(nnreal (12 * n) / nnreal d) / 12 =
        nnreal n / nnreal d"
    apply (subst nn2real_eq_iff[symmetric])
    by (simp only: nn2real_divide nn2real_nnreal nn2real_numeral
        of_nat_mult of_nat_numeral divide_inverse;
        simp add: mult.assoc)
  show ?thesis
    using divided divide_identity by simp
qed

lemma conditioned_bad_challenge_lists_not_full:
  assumes positive: "0 < n"
    and dominance: "n < CARD('f)"
  shows
    "generic_fri_bad_challenge_lists n
        (fri_conditioned_bad_challenges d committed) \<noteq>
      fri_challenge_space n"
proof -
  have card_bound:
      "card
          (generic_fri_bad_challenge_lists n
            (fri_conditioned_bad_challenges d committed))
        \<le> n * CARD('f) ^ (n - 1)"
    by (rule card_conditioned_bad_challenge_lists_bound)
  obtain m where n_eq: "n = Suc m"
    using positive by (cases n) auto
  have exponent: "CARD('f) ^ n = CARD('f) * CARD('f) ^ (n - 1)"
    unfolding n_eq
    by (simp add: mult.commute)
  have power_positive: "0 < CARD('f) ^ (n - 1)"
    by simp
  have strict:
      "n * CARD('f) ^ (n - 1) < CARD('f) ^ n"
    unfolding exponent
    using dominance power_positive by simp
  have bad_strict:
      "card
          (generic_fri_bad_challenge_lists n
            (fri_conditioned_bad_challenges d committed))
        < card (fri_challenge_space n)"
    using card_bound strict
    unfolding card_fri_challenge_space
    by simp
  show ?thesis
    using bad_strict by auto
qed

definition ro_checked_staged_conditioned_sampled_arithmetic_feasible
  :: "staged_budgets \<Rightarrow> nat \<Rightarrow> bool"
where
  "ro_checked_staged_conditioned_sampled_arithmetic_feasible
      budgets padding_fiber \<longleftrightarrow>
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in
       12 * q \<le> size \<and>
       12 * (q * (1 + (7 * q + 2))) \<le> size \<and>
       12 * (q * (ro_conditioned_augmented_query_raw_relation_fiber_bound +
         (q * q + 7 * q + 2))) \<le> size \<and>
       12 * (q * (padding_fiber + (5 * q + 2))) \<le> size)"

lemma ro_checked_staged_conditioned_sampled_arithmetic_feasibleD:
  assumes feasible:
    "ro_checked_staged_conditioned_sampled_arithmetic_feasible
      budgets padding_fiber"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows initial:
      "nnreal q / nnreal size \<le> (1 / 12 :: nnreal)"
    and challenge:
      "nnreal (q * (1 + (7 * q + 2))) / nnreal size \<le>
        (1 / 12 :: nnreal)"
    and residual:
      "nnreal
          (q * (ro_conditioned_augmented_query_raw_relation_fiber_bound +
            (q * q + 7 * q + 2))) /
          nnreal size
        \<le> (1 / 12 :: nnreal)"
    and padding:
      "nnreal (q * (padding_fiber + (5 * q + 2))) / nnreal size \<le>
        (1 / 12 :: nnreal)"
proof -
  have size_positive: "0 < size"
    using size_card by simp
  have initial_dominance: "12 * q \<le> size"
    and challenge_dominance:
      "12 * (q * (1 + (7 * q + 2))) \<le> size"
    and residual_dominance:
      "12 * (q *
        (ro_conditioned_augmented_query_raw_relation_fiber_bound +
          (q * q + 7 * q + 2))) \<le> size"
    and padding_dominance:
      "12 * (q * (padding_fiber + (5 * q + 2))) \<le> size"
    using feasible
    unfolding
      ro_checked_staged_conditioned_sampled_arithmetic_feasible_def
      q_def Let_def
    by blast+
  show "nnreal q / nnreal size \<le> (1 / 12 :: nnreal)"
    by (rule nnreal_nat_ratio_le_twelfth[
      OF size_positive initial_dominance])
  show
      "nnreal (q * (1 + (7 * q + 2))) / nnreal size \<le>
        (1 / 12 :: nnreal)"
    by (rule nnreal_nat_ratio_le_twelfth[
      OF size_positive challenge_dominance])
  show
      "nnreal
          (q * (ro_conditioned_augmented_query_raw_relation_fiber_bound +
            (q * q + 7 * q + 2))) /
          nnreal size
        \<le> (1 / 12 :: nnreal)"
    by (rule nnreal_nat_ratio_le_twelfth[
      OF size_positive residual_dominance])
  show
      "nnreal (q * (padding_fiber + (5 * q + 2))) / nnreal size \<le>
        (1 / 12 :: nnreal)"
    by (rule nnreal_nat_ratio_le_twelfth[
      OF size_positive padding_dominance])
qed

lemma ro_checked_staged_conditioned_sampled_arithmetic_feasible_components:
  assumes feasible:
    "ro_checked_staged_conditioned_sampled_arithmetic_feasible
      budgets padding_fiber"
  shows initial_component:
      "ro_checked_staged_conditioned_initial_target_error budgets \<le> 1 / 12"
    and trace_challenge_component:
      "ro_checked_staged_conditioned_trace_challenge_error budgets \<le> 1 / 12"
    and composition_challenge_component:
      "ro_checked_staged_conditioned_composition_challenge_error budgets \<le>
        1 / 12"
    and residual_component:
      "ro_checked_staged_conditioned_residual_query_error budgets \<le> 1 / 12"
    and padding_component:
      "nnreal
          (ro_checked_staged_transcript_hash_query_budget_for budgets *
            (padding_fiber +
              (5 * ro_checked_staged_transcript_hash_query_budget_for budgets +
                2))) /
          nnreal size
        \<le> (1 / 12 :: nnreal)"
proof -
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have initial0:
      "nnreal ?q / nnreal size \<le> (1 / 12 :: nnreal)"
    by (rule
      ro_checked_staged_conditioned_sampled_arithmetic_feasibleD(1)[
        OF feasible])
  have challenge0:
      "nnreal (?q * (1 + (7 * ?q + 2))) / nnreal size \<le>
        (1 / 12 :: nnreal)"
    by (rule
      ro_checked_staged_conditioned_sampled_arithmetic_feasibleD(2)[
        OF feasible])
  have residual0:
      "nnreal
          (?q * (ro_conditioned_augmented_query_raw_relation_fiber_bound +
            (?q * ?q + 7 * ?q + 2))) /
          nnreal size
        \<le> (1 / 12 :: nnreal)"
    by (rule
      ro_checked_staged_conditioned_sampled_arithmetic_feasibleD(3)[
        OF feasible])
  have padding0:
      "nnreal (?q * (padding_fiber + (5 * ?q + 2))) / nnreal size \<le>
        (1 / 12 :: nnreal)"
    by (rule
      ro_checked_staged_conditioned_sampled_arithmetic_feasibleD(4)[
        OF feasible])
  show
      "ro_checked_staged_conditioned_initial_target_error budgets \<le> 1 / 12"
    using initial0
    unfolding ro_checked_staged_conditioned_initial_target_error_def
    by simp
  show
      "ro_checked_staged_conditioned_trace_challenge_error budgets \<le> 1 / 12"
    using challenge0
    unfolding ro_checked_staged_conditioned_trace_challenge_error_def Let_def
    by simp
  show
      "ro_checked_staged_conditioned_composition_challenge_error budgets \<le>
        1 / 12"
    using challenge0
    unfolding
      ro_checked_staged_conditioned_composition_challenge_error_def Let_def
    by simp
  show
      "ro_checked_staged_conditioned_residual_query_error budgets \<le> 1 / 12"
    using residual0
    unfolding ro_checked_staged_conditioned_residual_query_error_def Let_def
    by simp
  show
      "nnreal
          (ro_checked_staged_transcript_hash_query_budget_for budgets *
            (padding_fiber +
              (5 * ro_checked_staged_transcript_hash_query_budget_for budgets +
                2))) /
          nnreal size
        \<le> (1 / 12 :: nnreal)"
    by (rule padding0)
qed

definition
  ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible
where
  "ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible
      budgets \<longleftrightarrow>
    hash_collision_budget_value 0
        (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      \<le> 1 / 12 \<and>
    ro_checked_staged_trace_composition_good_actual_query_error budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_trace_composition_prefix_target_error budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_fri_builder_merkle_target_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_first_root_alpha_pivot_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_conditioned_sampled_arithmetic_feasible budgets
      trace_composition_padding_query_raw_fiber_bound \<and>
    0 < rounds \<and>
    0 < ceil_log clength \<and>
    ceil_log clength < size \<and>
    ceil_log (Suc maxDegree) < size \<and>
    fri_conditioned_residual_query_list_card_bound (clength - 1) <
      query_sample_space_size ^ rounds \<and>
    fri_conditioned_residual_query_list_card_bound maxDegree <
      query_sample_space_size ^ rounds \<and>
    trace_composition_padding_query_index_bound <
      query_sample_space_size"

definition
  ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible
where
  "ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible
      budgets \<longleftrightarrow>
    hash_collision_budget_value 0
        (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      \<le> 1 / 12 \<and>
    ro_checked_staged_zero_round_bad_actual_query_error budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
        budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_zero_round_trace_composition_good_actual_query_error
        budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_trace_composition_prefix_target_error budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_fri_builder_merkle_target_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_zero_round_alpha_pivot_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_conditioned_sampled_arithmetic_feasible budgets
      composition_padding_query_raw_fiber_bound \<and>
    0 < rounds \<and>
    ceil_log (Suc maxDegree) < size \<and>
    fri_conditioned_residual_query_list_card_bound maxDegree <
      query_sample_space_size ^ rounds \<and>
    composition_padding_query_index_bound < query_sample_space_size"

definition
  ro_absorb_checked_staged_conditioned_explicit_arithmetic_feasible
where
  "ro_absorb_checked_staged_conditioned_explicit_arithmetic_feasible
      budgets \<longleftrightarrow>
    (if ceil_log clength = 0
     then
       ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible
         budgets
     else
       ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible
         budgets)"

lemma
  ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible_imp_nontrivial:
  assumes feasible:
    "ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible
      budgets"
  shows
    "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_nontrivial
      budgets"
proof -
  have legacy_collision:
      "hash_collision_budget_value 0
          (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
        \<le> 1 / 12"
    and legacy_query:
      "ro_checked_staged_trace_composition_good_actual_query_error budgets
        \<le> 1 / 12"
    and legacy_trace_target:
      "ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets
        \<le> 1 / 12"
    and legacy_composition_target:
      "ro_absorb_checked_staged_trace_composition_prefix_target_error budgets
        \<le> 1 / 12"
    and legacy_builder_target:
      "ro_absorb_checked_staged_fri_builder_merkle_target_error budgets
        \<le> 1 / 12"
    and legacy_alpha:
      "ro_checked_staged_first_root_alpha_pivot_error budgets \<le> 1 / 12"
    and sampled:
      "ro_checked_staged_conditioned_sampled_arithmetic_feasible budgets
        trace_composition_padding_query_raw_fiber_bound"
    using feasible
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible_def
    by blast+
  have initial_component:
      "ro_checked_staged_conditioned_initial_target_error budgets \<le> 1 / 12"
    and trace_challenge_component:
      "ro_checked_staged_conditioned_trace_challenge_error budgets \<le> 1 / 12"
    and composition_challenge_component:
      "ro_checked_staged_conditioned_composition_challenge_error budgets \<le>
        1 / 12"
    and residual_component:
      "ro_checked_staged_conditioned_residual_query_error budgets \<le> 1 / 12"
    and padding_raw:
      "nnreal
          (ro_checked_staged_transcript_hash_query_budget_for budgets *
            (trace_composition_padding_query_raw_fiber_bound +
              (5 * ro_checked_staged_transcript_hash_query_budget_for budgets +
                2))) /
          nnreal size
        \<le> (1 / 12 :: nnreal)"
    by (rule
      ro_checked_staged_conditioned_sampled_arithmetic_feasible_components[
        OF sampled])+
  have padding_component:
      "ro_checked_staged_conditioned_composition_padding_error budgets \<le>
        1 / 12"
    using padding_raw
    unfolding
      ro_checked_staged_conditioned_composition_padding_error_def Let_def
    by simp
  show ?thesis
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_nontrivial_def
    using legacy_collision legacy_query legacy_trace_target
      legacy_composition_target legacy_builder_target legacy_alpha
      initial_component trace_challenge_component composition_challenge_component
      residual_component padding_component
    by blast
qed

lemma
  ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible_imp_nontrivial:
  assumes feasible:
    "ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible
      budgets"
  shows
    "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_nontrivial
      budgets"
proof -
  have legacy_collision:
      "hash_collision_budget_value 0
          (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
        \<le> 1 / 12"
    and legacy_bad:
      "ro_checked_staged_zero_round_bad_actual_query_error budgets \<le> 1 / 12"
    and legacy_trace_target:
      "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
          budgets
        \<le> 1 / 12"
    and legacy_query:
      "ro_checked_staged_zero_round_trace_composition_good_actual_query_error
          budgets
        \<le> 1 / 12"
    and legacy_composition_target:
      "ro_absorb_checked_staged_trace_composition_prefix_target_error budgets
        \<le> 1 / 12"
    and legacy_builder_target:
      "ro_absorb_checked_staged_fri_builder_merkle_target_error budgets
        \<le> 1 / 12"
    and legacy_alpha:
      "ro_checked_staged_zero_round_alpha_pivot_error budgets \<le> 1 / 12"
    and sampled:
      "ro_checked_staged_conditioned_sampled_arithmetic_feasible budgets
        composition_padding_query_raw_fiber_bound"
    using feasible
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible_def
    by blast+
  have initial_component:
      "ro_checked_staged_conditioned_initial_target_error budgets \<le> 1 / 12"
    and trace_challenge_unused:
      "ro_checked_staged_conditioned_trace_challenge_error budgets \<le> 1 / 12"
    and composition_challenge_component:
      "ro_checked_staged_conditioned_composition_challenge_error budgets \<le>
        1 / 12"
    and residual_component:
      "ro_checked_staged_conditioned_residual_query_error budgets \<le> 1 / 12"
    and padding_raw:
      "nnreal
          (ro_checked_staged_transcript_hash_query_budget_for budgets *
            (composition_padding_query_raw_fiber_bound +
              (5 * ro_checked_staged_transcript_hash_query_budget_for budgets +
                2))) /
          nnreal size
        \<le> (1 / 12 :: nnreal)"
    by (rule
      ro_checked_staged_conditioned_sampled_arithmetic_feasible_components[
        OF sampled])+
  have padding_component:
      "ro_checked_staged_conditioned_zero_round_composition_padding_error
          budgets
        \<le> 1 / 12"
    using padding_raw
    unfolding
      ro_checked_staged_conditioned_zero_round_composition_padding_error_def
      Let_def
    by simp
  show ?thesis
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_nontrivial_def
    using legacy_collision legacy_bad legacy_trace_target legacy_query
      legacy_composition_target legacy_builder_target legacy_alpha
      initial_component composition_challenge_component residual_component
      padding_component
    by blast
qed

lemma
  ro_absorb_checked_staged_conditioned_explicit_arithmetic_feasible_imp_nontrivial:
  assumes feasible:
    "ro_absorb_checked_staged_conditioned_explicit_arithmetic_feasible budgets"
  shows
    "ro_absorb_checked_staged_conditioned_explicit_parameter_nontrivial budgets"
proof (cases "ceil_log clength = 0")
  case True
  have zero_feasible:
      "ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible
        budgets"
    using feasible True
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_arithmetic_feasible_def
    by simp
  have zero_nontrivial:
      "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_nontrivial
        budgets"
    by (rule
      ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible_imp_nontrivial[
        OF zero_feasible])
  show ?thesis
    using True zero_nontrivial
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_parameter_nontrivial_def
    by simp
next
  case False
  have nonempty_feasible:
      "ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible
        budgets"
    using feasible False
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_arithmetic_feasible_def
    by simp
  have nonempty_nontrivial:
      "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_nontrivial
        budgets"
    by (rule
      ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible_imp_nontrivial[
        OF nonempty_feasible])
  show ?thesis
    using False nonempty_nontrivial
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_parameter_nontrivial_def
    by simp
qed

lemma
  ro_absorb_checked_staged_conditioned_nonempty_feasible_trace_challenge_not_full:
  assumes feasible:
    "ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible
      budgets"
  shows
    "generic_fri_bad_challenge_lists (ceil_log clength)
        (fri_conditioned_bad_challenges (clength - 1) committed) \<noteq>
      fri_challenge_space (ceil_log clength)"
proof -
  have positive: "0 < ceil_log clength"
    and dominance: "ceil_log clength < size"
    using feasible
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible_def
    by blast+
  have field_dominance: "ceil_log clength < CARD('f)"
    using dominance size_card by simp
  show ?thesis
    by (rule conditioned_bad_challenge_lists_not_full[
      OF positive field_dominance])
qed

lemma
  ro_absorb_checked_staged_conditioned_nonempty_feasible_composition_challenge_not_full:
  assumes feasible:
    "ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible
      budgets"
    and degree: "d \<le> maxDegree"
    and positive: "0 < ceil_log (Suc d)"
  shows
    "generic_fri_bad_challenge_lists (ceil_log (Suc d))
        (fri_conditioned_bad_challenges d committed) \<noteq>
      fri_challenge_space (ceil_log (Suc d))"
proof -
  have maximum_dominance: "ceil_log (Suc maxDegree) < size"
    using feasible
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible_def
    by blast
  have logarithm_mono: "ceil_log (Suc d) \<le> ceil_log (Suc maxDegree)"
    by (rule ceil_log_mono) (use degree in simp)
  have dominance: "ceil_log (Suc d) < CARD('f)"
    using logarithm_mono maximum_dominance size_card by simp
  show ?thesis
    by (rule conditioned_bad_challenge_lists_not_full[
      OF positive dominance])
qed

lemma
  ro_absorb_checked_staged_conditioned_zero_feasible_composition_challenge_not_full:
  assumes feasible:
    "ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible
      budgets"
    and degree: "d \<le> maxDegree"
    and positive: "0 < ceil_log (Suc d)"
  shows
    "generic_fri_bad_challenge_lists (ceil_log (Suc d))
        (fri_conditioned_bad_challenges d committed) \<noteq>
      fri_challenge_space (ceil_log (Suc d))"
proof -
  have maximum_dominance: "ceil_log (Suc maxDegree) < size"
    using feasible
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible_def
    by blast
  have logarithm_mono: "ceil_log (Suc d) \<le> ceil_log (Suc maxDegree)"
    by (rule ceil_log_mono) (use degree in simp)
  have dominance: "ceil_log (Suc d) < CARD('f)"
    using logarithm_mono maximum_dominance size_card by simp
  show ?thesis
    by (rule conditioned_bad_challenge_lists_not_full[
      OF positive dominance])
qed

lemma
  ro_absorb_checked_staged_conditioned_nonempty_feasible_trace_residual_not_full:
  assumes feasible:
    "ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible
      budgets"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log clength"
    and rounds_le: "ceil_log clength \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "fri_conditioned_quantitative_residual_query_lists (clength - 1)
        roots challenges final_value prefix_state \<noteq>
      fri_query_index_list_space"
proof -
  have strict:
      "fri_conditioned_residual_query_list_card_bound (clength - 1) <
        query_sample_space_size ^ rounds"
    using feasible
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible_def
    by blast
  have successor: "Suc (clength - 1) = clength"
    using clength_pos by simp
  have round_count0:
      "length challenges = ceil_log (Suc (clength - 1))"
    using round_count successor by simp
  have rounds_le0: "ceil_log (Suc (clength - 1)) \<le> N"
    using rounds_le successor by simp
  show ?thesis
    by (rule fri_conditioned_quantitative_residual_query_lists_not_full[
      OF eval_power round_count0 rounds_le0 lengths strict])
qed

lemma
  ro_absorb_checked_staged_conditioned_nonempty_feasible_composition_residual_not_full:
  assumes feasible:
    "ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible
      budgets"
    and degree: "d \<le> maxDegree"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "fri_conditioned_quantitative_residual_query_lists d
        roots challenges final_value prefix_state \<noteq>
      fri_query_index_list_space"
proof -
  have maximum_strict:
      "fri_conditioned_residual_query_list_card_bound maxDegree <
        query_sample_space_size ^ rounds"
    using feasible
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible_def
    by blast
  have bound_mono:
      "fri_conditioned_residual_query_list_card_bound d \<le>
        fri_conditioned_residual_query_list_card_bound maxDegree"
    by (rule fri_conditioned_residual_query_list_card_bound_mono[OF degree])
  have strict:
      "fri_conditioned_residual_query_list_card_bound d <
        query_sample_space_size ^ rounds"
    by (rule le_less_trans[OF bound_mono maximum_strict])
  show ?thesis
    by (rule fri_conditioned_quantitative_residual_query_lists_not_full[
      OF eval_power round_count rounds_le lengths strict])
qed

lemma
  ro_absorb_checked_staged_conditioned_zero_feasible_composition_residual_not_full:
  assumes feasible:
    "ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible
      budgets"
    and degree: "d \<le> maxDegree"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "fri_conditioned_quantitative_residual_query_lists d
        roots challenges final_value prefix_state \<noteq>
      fri_query_index_list_space"
proof -
  have maximum_strict:
      "fri_conditioned_residual_query_list_card_bound maxDegree <
        query_sample_space_size ^ rounds"
    using feasible
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible_def
    by blast
  have bound_mono:
      "fri_conditioned_residual_query_list_card_bound d \<le>
        fri_conditioned_residual_query_list_card_bound maxDegree"
    by (rule fri_conditioned_residual_query_list_card_bound_mono[OF degree])
  have strict:
      "fri_conditioned_residual_query_list_card_bound d <
        query_sample_space_size ^ rounds"
    by (rule le_less_trans[OF bound_mono maximum_strict])
  show ?thesis
    by (rule fri_conditioned_quantitative_residual_query_lists_not_full[
      OF eval_power round_count rounds_le lengths strict])
qed

lemma
  ro_absorb_checked_staged_conditioned_nonempty_feasible_padding_not_full:
  assumes feasible:
    "ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible
      budgets"
    and degree: "d \<le> fri_padded_degree_bound maxDegree"
    and lengths: "length original = length candidate"
  shows
    "trace_composition_padding_query_lists
        original candidate composition as d \<noteq>
      fri_query_index_list_space"
proof -
  have maximum_strict:
      "trace_composition_padding_query_index_bound <
        query_sample_space_size"
    and rounds_positive: "0 < rounds"
    using feasible
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_nonempty_arithmetic_feasible_def
    by blast+
  have bound_mono:
      "trace_composition_query_index_bound_for d \<le>
        trace_composition_padding_query_index_bound"
    unfolding trace_composition_padding_query_index_bound_def
    by (rule trace_composition_query_index_bound_for_mono[OF degree])
  have strict:
      "trace_composition_query_index_bound_for d <
        query_sample_space_size"
    by (rule le_less_trans[OF bound_mono maximum_strict])
  have card_strict:
      "card (trace_composition_padding_query_lists
          original candidate composition as d) <
        card fri_query_index_list_space"
    by (rule trace_composition_padding_query_lists_strict[
      OF lengths strict rounds_positive])
  show ?thesis
    using card_strict by auto
qed

lemma
  ro_absorb_checked_staged_conditioned_zero_feasible_padding_not_full:
  assumes feasible:
    "ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible
      budgets"
    and degree: "d \<le> fri_padded_degree_bound maxDegree"
  shows
    "composition_padding_query_lists trace_table composition_table as d \<noteq>
      fri_query_index_list_space"
proof -
  have maximum_strict:
      "composition_padding_query_index_bound < query_sample_space_size"
    and rounds_positive: "0 < rounds"
    using feasible
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_zero_round_arithmetic_feasible_def
    by blast+
  have bound_mono:
      "query_agreement_bound_for d \<le> composition_padding_query_index_bound"
    unfolding composition_padding_query_index_bound_def
    by (rule query_agreement_bound_for_mono[OF degree])
  have strict:
      "query_agreement_bound_for d < query_sample_space_size"
    by (rule le_less_trans[OF bound_mono maximum_strict])
  show ?thesis
    by (rule composition_padding_query_lists_not_full[
      OF strict rounds_positive])
qed

corollary ro_absorb_stark_soundness_conditioned_explicit_arithmetic_nontrivial:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and feasible:
      "ro_absorb_checked_staged_conditioned_explicit_arithmetic_feasible budgets"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A < 1"
proof -
  have parameter_conditions:
      "ro_absorb_checked_staged_conditioned_explicit_parameter_nontrivial
        budgets"
    by (rule
      ro_absorb_checked_staged_conditioned_explicit_arithmetic_feasible_imp_nontrivial[
        OF feasible])
  show ?thesis
    by (rule ro_absorb_stark_soundness_conditioned_explicit_nontrivial[
      OF false_statement wf controlled parameter_conditions])
qed

end
end
