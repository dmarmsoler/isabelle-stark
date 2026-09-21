theory Soundness_FRI_Conditioned_Explicit_Component_Audit
  imports Stark.Soundness_FRI_Conditioned_Explicit_Arithmetic_Feasibility
begin

section \<open>Exact component and projection audit\<close>

text \<open>
  This theory exposes the two all-round branch totals as lists of their eleven
  effective components.  The joint sampled term is expanded into its trace
  challenge, composition challenge, residual-query, and padding terms.

  The names in these lists are not treated as opaque arithmetic atoms.  Their
  defining theories tie them to the checked transcript and verifier budgets,
  exact quotient/remainder modulo fibers, authenticated FRI evidence, Merkle
  target sets, and alpha-pivot relation fibers.  Keeping the top-level lists
  here makes component-to-total reasoning explicit without duplicating those
  semantic definitions.
\<close>

context soundness
begin

definition nonempty_parameter_error_components
  :: "staged_budgets \<Rightarrow> prob list"
where
  "nonempty_parameter_error_components budgets = [
    hash_collision_budget_value 0
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets),
    ro_checked_staged_trace_composition_good_actual_query_error budgets,
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets,
    ro_absorb_checked_staged_trace_composition_prefix_target_error budgets,
    ro_absorb_checked_staged_fri_builder_merkle_target_error budgets,
    ro_checked_staged_conditioned_initial_target_error budgets,
    ro_checked_staged_conditioned_trace_challenge_error budgets,
    ro_checked_staged_conditioned_composition_challenge_error budgets,
    ro_checked_staged_conditioned_residual_query_error budgets,
    ro_checked_staged_conditioned_composition_padding_error budgets,
    ro_checked_staged_first_root_alpha_pivot_error budgets]"

lemma nonempty_parameter_error_eq_sum_list:
  "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
      budgets =
    sum_list (nonempty_parameter_error_components budgets)"
  unfolding
    ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error_def
    nonempty_parameter_error_components_def
    ro_checked_staged_conditioned_joint_sampled_error_def
  by (simp add: add.assoc)

lemma nonempty_parameter_error_component_le:
  assumes component:
    "component \<in> set (nonempty_parameter_error_components budgets)"
  shows
    "component \<le>
      ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
        budgets"
  unfolding nonempty_parameter_error_eq_sum_list
  by (rule member_le_sum_list[OF component]) simp

definition zero_round_parameter_error_components
  :: "staged_budgets \<Rightarrow> prob list"
where
  "zero_round_parameter_error_components budgets = [
    hash_collision_budget_value 0
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets),
    ro_checked_staged_zero_round_bad_actual_query_error budgets,
    ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
      budgets,
    ro_checked_staged_zero_round_trace_composition_good_actual_query_error
      budgets,
    ro_absorb_checked_staged_trace_composition_prefix_target_error budgets,
    ro_absorb_checked_staged_fri_builder_merkle_target_error budgets,
    ro_checked_staged_conditioned_initial_target_error budgets,
    ro_checked_staged_conditioned_composition_challenge_error budgets,
    ro_checked_staged_conditioned_residual_query_error budgets,
    ro_checked_staged_conditioned_zero_round_composition_padding_error budgets,
    ro_checked_staged_zero_round_alpha_pivot_error budgets]"

lemma zero_round_parameter_error_eq_sum_list:
  "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
      budgets =
    sum_list (zero_round_parameter_error_components budgets)"
  unfolding
    ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error_def
    zero_round_parameter_error_components_def
    ro_checked_staged_conditioned_zero_round_joint_sampled_error_def
  by (simp add: add.assoc)

lemma zero_round_parameter_error_component_le:
  assumes component:
    "component \<in> set (zero_round_parameter_error_components budgets)"
  shows
    "component \<le>
      ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
        budgets"
  unfolding zero_round_parameter_error_eq_sum_list
  by (rule member_le_sum_list[OF component]) simp

subsection \<open>Security target and necessary cardinality conditions\<close>

text \<open>
  The bit target is represented directly in the public theorem's probability
  codomain, @{typ nnreal}.  There is no conversion through an approximate
  floating-point or integer probability representation.
\<close>

definition soundness_security_target :: "nat \<Rightarrow> prob"
where
  "soundness_security_target security_bits =
    1 / nnreal (2 ^ security_bits)"

lemma nnreal_nat_ratio_le_security_target_iff:
  assumes positive: "0 < d"
  shows
    "(nnreal n / nnreal d \<le> soundness_security_target security_bits) \<longleftrightarrow>
      2 ^ security_bits * n \<le> d"
proof -
  have d_pos: "(0 :: real) < real d"
    using positive by simp
  have power_pos: "(0 :: real) < real (2 ^ security_bits)"
    by simp
  have ratio_iff:
      "(real n / real d \<le> 1 / real (2 ^ security_bits)) \<longleftrightarrow>
        real n * real (2 ^ security_bits) \<le> real d"
    using d_pos power_pos
    by (simp add: pos_divide_le_eq pos_le_divide_eq mult.commute)
  have cast_iff:
      "(real n * real (2 ^ security_bits) \<le> real d) \<longleftrightarrow>
        n * 2 ^ security_bits \<le> d"
  proof -
    have cast_mult:
        "(real (n * 2 ^ security_bits) :: real) =
          real n * real (2 ^ security_bits)"
      by simp
    have cast_order:
        "((real (n * 2 ^ security_bits) :: real) \<le> real d) \<longleftrightarrow>
          n * 2 ^ security_bits \<le> d"
      by (rule of_nat_le_iff)
    show ?thesis
      using cast_mult cast_order by simp
  qed
  show ?thesis
    unfolding soundness_security_target_def
    apply (subst nn2real_le_iff[symmetric])
    apply (simp only: nn2real_divide nn2real_nnreal nn2real_1)
    using ratio_iff cast_iff
    by (simp add: mult.commute)
qed

lemma nonempty_target_imp_collision_cardinality:
  assumes target:
    "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
        budgets
      \<le> soundness_security_target security_bits"
  shows
    "2 ^ security_bits *
        (ro_absorb_checked_staged_security_hash_query_budget_for budgets *
          ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      \<le> size"
proof -
  let ?q =
    "ro_absorb_checked_staged_security_hash_query_budget_for budgets"
  have collision_le_total:
      "hash_collision_budget_value 0 ?q \<le>
        ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
          budgets"
    by (rule nonempty_parameter_error_component_le)
      (simp add: nonempty_parameter_error_components_def)
  have collision_le_target:
      "hash_collision_budget_value 0 ?q \<le>
        soundness_security_target security_bits"
    by (rule order_trans[OF collision_le_total target])
  have ratio:
      "nnreal (?q * ?q) / nnreal size \<le>
        soundness_security_target security_bits"
    using collision_le_target
    unfolding hash_collision_budget_value_def
    by simp
  have size_pos: "0 < size"
    using size_card by simp
  show ?thesis
    using ratio
      nnreal_nat_ratio_le_security_target_iff[OF size_pos,
        of "?q * ?q" security_bits]
    by simp
qed

lemma nonempty_target_imp_initial_query_cardinality:
  assumes target:
    "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
        budgets
      \<le> soundness_security_target security_bits"
  shows
    "2 ^ security_bits *
        ro_checked_staged_transcript_hash_query_budget_for budgets
      \<le> size"
proof -
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have initial_le_total:
      "ro_checked_staged_conditioned_initial_target_error budgets \<le>
        ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
          budgets"
    by (rule nonempty_parameter_error_component_le)
      (simp add: nonempty_parameter_error_components_def)
  have ratio:
      "nnreal ?q / nnreal size \<le> soundness_security_target security_bits"
    using order_trans[OF initial_le_total target]
    unfolding ro_checked_staged_conditioned_initial_target_error_def .
  have size_pos: "0 < size"
    using size_card by simp
  show ?thesis
    using ratio
      nnreal_nat_ratio_le_security_target_iff[OF size_pos,
        of ?q security_bits]
    by simp
qed

lemma zero_round_target_imp_collision_cardinality:
  assumes target:
    "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
        budgets
      \<le> soundness_security_target security_bits"
  shows
    "2 ^ security_bits *
        (ro_absorb_checked_staged_security_hash_query_budget_for budgets *
          ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      \<le> size"
proof -
  let ?q =
    "ro_absorb_checked_staged_security_hash_query_budget_for budgets"
  have collision_le_total:
      "hash_collision_budget_value 0 ?q \<le>
        ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
          budgets"
    by (rule zero_round_parameter_error_component_le)
      (simp add: zero_round_parameter_error_components_def)
  have ratio:
      "nnreal (?q * ?q) / nnreal size \<le>
        soundness_security_target security_bits"
    using order_trans[OF collision_le_total target]
    unfolding hash_collision_budget_value_def
    by simp
  have size_pos: "0 < size"
    using size_card by simp
  show ?thesis
    using ratio
      nnreal_nat_ratio_le_security_target_iff[OF size_pos,
        of "?q * ?q" security_bits]
    by simp
qed

lemma zero_round_target_imp_initial_query_cardinality:
  assumes target:
    "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
        budgets
      \<le> soundness_security_target security_bits"
  shows
    "2 ^ security_bits *
        ro_checked_staged_transcript_hash_query_budget_for budgets
      \<le> size"
proof -
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have initial_le_total:
      "ro_checked_staged_conditioned_initial_target_error budgets \<le>
        ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
          budgets"
    by (rule zero_round_parameter_error_component_le)
      (simp add: zero_round_parameter_error_components_def)
  have ratio:
      "nnreal ?q / nnreal size \<le> soundness_security_target security_bits"
    using order_trans[OF initial_le_total target]
    unfolding ro_checked_staged_conditioned_initial_target_error_def .
  have size_pos: "0 < size"
    using size_card by simp
  show ?thesis
    using ratio
      nnreal_nat_ratio_le_security_target_iff[OF size_pos,
        of ?q security_bits]
    by simp
qed

subsection \<open>Actual-query projections are not full-space estimates\<close>

lemma actual_query_trace_composition_projection_not_full:
  assumes trace_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
    and composition_low:
      "composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate data query_start)"
    and not_all:
      "\<not> all_queries_consistent
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (ro_actual_query_composition_candidate data query_start)
        (staged_alphas data)"
    and strict:
      "trace_composition_query_index_bound < query_sample_space_size"
  shows
    "ro_actual_query_trace_composition_accepted_query_lists
        prefix prefix_state data query_start \<noteq>
      fri_query_index_list_space"
proof -
  have
      "card
          (ro_actual_query_trace_composition_accepted_query_lists
            prefix prefix_state data query_start)
        \<le> trace_composition_query_index_bound ^ rounds"
    by (rule
      ro_actual_query_trace_composition_accepted_query_lists_card_bound[
        OF trace_low composition_low not_all])
  also have "... < query_sample_space_size ^ rounds"
    by (rule power_strict_mono[OF strict _ rounds_positive]) simp
  also have "... = card fri_query_index_list_space"
    unfolding card_fri_query_index_list_space card_query_sample_space by simp
  finally show ?thesis by auto
qed

lemma zero_round_bad_actual_query_projection_not_full:
  assumes zero: "ceil_log clength = 0"
    and false_statement: "\<not> exists_valid_trace"
  shows
    "ro_actual_query_zero_round_bad_query_lists
        prefix prefix_state data query_start \<noteq>
      fri_query_index_list_space"
proof -
  have query_space_gt_one: "1 < query_sample_space_size"
    by (rule
      not_exists_valid_trace_imp_query_sample_space_size_gt_one[
        OF false_statement])
  have
      "card
          (ro_actual_query_zero_round_bad_query_lists
            prefix prefix_state data query_start)
        \<le> (query_sample_space_size - 1) ^ rounds"
    by (rule ro_actual_query_zero_round_bad_query_lists_card_bound[OF zero])
  also have "... < query_sample_space_size ^ rounds"
    by (rule power_strict_mono[OF _ _ rounds_positive])
      (use query_space_gt_one in simp_all)
  also have "... = card fri_query_index_list_space"
    unfolding card_fri_query_index_list_space card_query_sample_space by simp
  finally show ?thesis by auto
qed

lemma zero_round_good_actual_query_projection_not_full:
  "ro_actual_query_zero_round_trace_composition_good_query_lists
      data prefix_state query_start \<noteq>
    fri_query_index_list_space"
proof -
  have strict: "query_agreement_bound < query_sample_space_size"
    by (rule spec_degree_wellformed_query_margin[
      OF spec_degree_wellformed_from_spec_query_margin])
  have
      "card
          (ro_actual_query_zero_round_trace_composition_good_query_lists
            data prefix_state query_start)
        \<le> query_agreement_bound ^ rounds"
    by (rule
      ro_actual_query_zero_round_trace_composition_good_query_lists_card_bound)
  also have "... < query_sample_space_size ^ rounds"
    by (rule power_strict_mono[OF strict _ rounds_positive]) simp
  also have "... = card fri_query_index_list_space"
    unfolding card_fri_query_index_list_space card_query_sample_space by simp
  finally show ?thesis by auto
qed

end
end
