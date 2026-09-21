theory Soundness_FRI_Conditioned_Explicit_Residual_Projection_Obstruction
  imports Stark.Soundness_FRI_Conditioned_Explicit_Component_Audit
begin

section \<open>Residual-projection obstruction in the current exact bound\<close>

text \<open>
  The residual-query relation currently bounds one random-oracle output fiber
  through a cardinality bound for complete sampled query lists.  The following
  arithmetic makes the resulting loss explicit.  It is an obstruction of the
  displayed parameter error, not a lower bound on the real verifier acceptance
  probability.
\<close>

lemma modulo_preimage_card_envelope_ge_half:
  assumes q_two: "2 \<le> q"
    and m_two: "2 \<le> m"
    and q_le: "q \<le> 2 * m"
  shows
    "q div 2 \<le> modulo_preimage_card_envelope q m (m - 1)"
proof (cases "q < m")
  case True
  then have q_le_pred: "q \<le> m - 1"
    using q_two m_two by simp
  show ?thesis
    unfolding modulo_preimage_card_envelope_def
    using True q_le_pred m_two
    by simp
next
  case False
  then have m_le: "m \<le> q"
    by simp
  show ?thesis
  proof (cases "q < 2 * m")
    case True
    have div_lower: "1 \<le> q div m"
      using m_le m_two
      by (simp add: less_eq_div_iff_mult_less_eq)
    have div_upper: "q div m < 2"
      using True m_two
      by (simp add: div_less_iff_less_mult)
    have div_eq: "q div m = 1"
      using div_lower div_upper by simp
    have decomposition:
        "q = (q div m) * m + q mod m"
      using div_mult_mod_eq[of q m] by simp
    have mod_eq: "q mod m = q - m"
      using decomposition div_eq m_le by simp
    have rem_le: "q - m \<le> m - 1"
      using True m_le by linarith
    show ?thesis
      unfolding modulo_preimage_card_envelope_def div_eq mod_eq
      using rem_le q_two by simp
  next
    case False
    then have q_eq: "q = 2 * m"
      using q_le by linarith
    show ?thesis
      unfolding q_eq modulo_preimage_card_envelope_def
      using m_two by simp
  qed
qed

lemma one_third_le_nnreal_floor_half:
  assumes q_two: "2 \<le> q"
  shows
    "(1 :: nnreal) / 3 \<le> nnreal (q div 2) / nnreal q"
proof -
  have q_pos: "0 < q"
    using q_two by simp
  have div_one: "1 \<le> q div 2"
    using q_two by (simp add: less_eq_div_iff_mult_less_eq)
  have decomposition: "q = (q div 2) * 2 + q mod 2"
    using div_mult_mod_eq[of q 2] by simp
  have remainder: "q mod 2 < 2"
    by simp
  have cross: "q \<le> 3 * (q div 2)"
    using decomposition remainder div_one by linarith
  have cross_real:
      "(real q :: real) \<le> 3 * real (q div 2)"
  proof -
    have "(real q :: real) \<le> real (3 * (q div 2))"
      by (rule of_nat_mono[OF cross])
    then show ?thesis by simp
  qed
  have real_ratio:
      "(1 :: real) / 3 \<le> real (q div 2) / real q"
    using cross_real q_pos
    by (simp add: pos_divide_le_eq divide_le_eq)
  show ?thesis
    apply (subst nn2real_le_iff[symmetric])
    apply (simp only: nn2real_divide nn2real_nnreal nn2real_1)
    using real_ratio
    by simp
qed


context soundness
begin

lemma first_successor_domain_supports_half_query_space:
  assumes domain_large: "8 \<le> clength * scale"
    and query_nontrivial: "2 \<le> query_sample_space_size"
  shows
    "query_sample_space_size div 2 \<le>
      modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at 1))
        (length (fri_canonical_domain_at 1) - 1)"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have N_nonzero: "N \<noteq> 0"
    using domain_large eval_power by (cases N) auto
  obtain M where N_eq: "N = Suc M"
    using N_nonzero by (cases N) auto
  have domain_double:
      "clength * scale =
        2 * length (fri_canonical_domain_at 1)"
    unfolding fri_canonical_domain_at_length eval_power N_eq
    by (simp add: mult.commute)
  have successor_two: "2 \<le> length (fri_canonical_domain_at 1)"
  proof -
    have four_le: "4 \<le> (clength * scale) div 2"
      using domain_large
      by (simp add: less_eq_div_iff_mult_less_eq)
    then show ?thesis
      unfolding fri_canonical_domain_at_length
      by simp
  qed
  have query_le:
      "query_sample_space_size \<le>
        2 * length (fri_canonical_domain_at 1)"
    using query_sample_space_size_le_domain domain_double by simp
  show ?thesis
    by (rule modulo_preimage_card_envelope_ge_half[
      OF query_nontrivial successor_two query_le])
qed

lemma first_trace_residual_envelope_le:
  assumes nonempty: "0 < ceil_log clength"
  shows
    "(modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at 1))
        (length (fri_canonical_domain_at 1) - 1)) ^ rounds
      \<le> fri_conditioned_residual_query_list_card_bound (clength - 1)"
proof -
  have clength_suc: "Suc (clength - 1) = clength"
    using clength_pos by simp
  have zero_in: "0 \<in> {..<ceil_log (Suc (clength - 1))}"
    using nonempty clength_suc by simp
  let ?f = "\<lambda>i.
    (modulo_preimage_card_envelope query_sample_space_size
      (length (fri_canonical_domain_at (Suc i)))
      (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
  have first_le:
      "?f 0 \<le> (\<Sum>i<ceil_log (Suc (clength - 1)). ?f i)"
    apply (rule member_le_sum)
      apply (rule zero_in)
     apply simp
    apply simp
    done
  show ?thesis
    unfolding fri_conditioned_residual_query_list_card_bound_def
    using first_le by simp
qed


lemma half_query_space_le_trace_residual:
  assumes domain_large: "8 \<le> clength * scale"
    and query_nontrivial: "2 \<le> query_sample_space_size"
    and nonempty: "0 < ceil_log clength"
  shows
    "query_sample_space_size div 2 \<le>
      fri_conditioned_residual_query_list_card_bound (clength - 1)"
proof -
  let ?E =
    "modulo_preimage_card_envelope query_sample_space_size
      (length (fri_canonical_domain_at 1))
      (length (fri_canonical_domain_at 1) - 1)"
  have half_le_E: "query_sample_space_size div 2 \<le> ?E"
    by (rule first_successor_domain_supports_half_query_space[
      OF domain_large query_nontrivial])
  have E_one: "1 \<le> ?E"
    using query_nontrivial half_le_E by simp
  have one_le_rounds: "1 \<le> rounds"
    using rounds_positive by simp
  have E_le_power: "?E \<le> ?E ^ rounds"
  proof -
    have "?E ^ 1 \<le> ?E ^ rounds"
      by (rule power_increasing[OF one_le_rounds E_one])
    then show ?thesis by simp
  qed
  have power_le_residual: "?E ^ rounds \<le>
      fri_conditioned_residual_query_list_card_bound (clength - 1)"
    by (rule first_trace_residual_envelope_le[OF nonempty])
  show ?thesis
    by (rule order_trans[OF half_le_E
      order_trans[OF E_le_power power_le_residual]])
qed

lemma half_query_envelope_le_augmented_raw_fiber:
  assumes domain_large: "8 \<le> clength * scale"
    and query_nontrivial: "2 \<le> query_sample_space_size"
    and nonempty: "0 < ceil_log clength"
  shows
    "query_raw_preimage_card_envelope
        (query_sample_space_size div 2)
      \<le> ro_conditioned_augmented_query_raw_relation_fiber_bound"
proof -
  let ?T =
    "fri_conditioned_residual_query_list_card_bound (clength - 1)"
  let ?C =
    "fri_conditioned_residual_query_list_card_bound maxDegree"
  let ?K = "rounds * (?T + ?C)"
  let ?H =
    "query_raw_preimage_card_envelope
      (query_sample_space_size div 2)"
  let ?I = "query_raw_preimage_card_envelope ?K"
  have half_le_T: "query_sample_space_size div 2 \<le> ?T"
    by (rule half_query_space_le_trace_residual[
      OF domain_large query_nontrivial nonempty])
  have T_le_sum: "?T \<le> ?T + ?C"
    by simp
  have one_le_rounds: "1 \<le> rounds"
    using rounds_positive by simp
  have sum_le_K: "?T + ?C \<le> ?K"
  proof -
    have "1 * (?T + ?C) \<le> rounds * (?T + ?C)"
      apply (rule mult_right_mono[OF one_le_rounds])
      apply simp
      done
    then show ?thesis by simp
  qed
  have half_le_K: "query_sample_space_size div 2 \<le> ?K"
    by (rule order_trans[OF half_le_T
      order_trans[OF T_le_sum sum_le_K]])
  have envelope_le: "?H \<le> ?I"
    by (rule query_raw_preimage_card_envelope_mono[OF half_le_K])
  have I_le_scaled: "?I \<le> rounds * ?I"
  proof -
    have "1 * ?I \<le> rounds * ?I"
      apply (rule mult_right_mono[OF one_le_rounds])
      apply simp
      done
    then show ?thesis by simp
  qed
  have H_le_residual:
      "?H \<le> ro_conditioned_residual_query_raw_relation_fiber_bound"
    unfolding ro_conditioned_residual_query_raw_relation_fiber_bound_def
    by (rule order_trans[OF envelope_le I_le_scaled])
  show ?thesis
    unfolding ro_conditioned_augmented_query_raw_relation_fiber_bound_def
    using H_le_residual by simp
qed


lemma one_third_le_conditioned_residual_query_error:
  assumes domain_large: "8 \<le> clength * scale"
    and query_nontrivial: "2 \<le> query_sample_space_size"
    and nonempty: "0 < ceil_log clength"
  shows
    "(1 :: prob) / 3 \<le>
      ro_checked_staged_conditioned_residual_query_error budgets"
proof -
  let ?Q = "query_sample_space_size"
  let ?H = "query_raw_preimage_card_envelope (?Q div 2)"
  let ?A = "ro_conditioned_augmented_query_raw_relation_fiber_bound"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?N = "?q * (?A + (?q * ?q + 7 * ?q + 2))"
  have one_third_le_half:
      "(1 :: prob) / 3 \<le> nnreal (?Q div 2) / nnreal ?Q"
    by (rule one_third_le_nnreal_floor_half[OF query_nontrivial])
  have half_le_envelope:
      "nnreal (?Q div 2) / nnreal ?Q \<le>
        nnreal ?H / nnreal size"
    by (rule query_uniform_fraction_le_query_envelope) simp
  have H_le_A: "?H \<le> ?A"
    by (rule half_query_envelope_le_augmented_raw_fiber[
      OF domain_large query_nontrivial nonempty])
  have q_pos: "0 < ?q"
    unfolding ro_checked_staged_transcript_hash_query_budget_for_def
    by simp
  have A_le_sum: "?A \<le> ?A + (?q * ?q + 7 * ?q + 2)"
    by simp
  have sum_le_N: "?A + (?q * ?q + 7 * ?q + 2) \<le> ?N"
  proof -
    have
      "1 * (?A + (?q * ?q + 7 * ?q + 2)) \<le>
        ?q * (?A + (?q * ?q + 7 * ?q + 2))"
      apply (rule mult_right_mono)
        using q_pos apply simp
      apply simp
      done
    then show ?thesis by simp
  qed
  have H_le_N: "?H \<le> ?N"
    by (rule order_trans[OF H_le_A order_trans[OF A_le_sum sum_le_N]])
  have envelope_le_error:
      "nnreal ?H / nnreal size \<le>
        ro_checked_staged_conditioned_residual_query_error budgets"
    unfolding ro_checked_staged_conditioned_residual_query_error_def Let_def
    by (rule nnreal_nat_divide_right_mono[OF H_le_N])
  show ?thesis
    by (rule order_trans[OF one_third_le_half
      order_trans[OF half_le_envelope envelope_le_error]])
qed

lemma soundness_security_target_le_quarter:
  assumes bits_two: "2 \<le> (security_bits::nat)"
  shows
    "soundness_security_target security_bits \<le> (1 :: prob) / 4"
proof -
  have exponent_le: "(2::nat) ^ 2 \<le> 2 ^ security_bits"
    by (rule power_increasing[OF bits_two]) simp
  have denom_real:
      "(4::real) \<le> real (2 ^ security_bits)"
  proof -
    have "(real ((2::nat) ^ 2) :: real) \<le> real (2 ^ security_bits)"
      by (rule of_nat_mono[OF exponent_le])
    then show ?thesis by simp
  qed
  have denom_pos: "(0::real) < real (2 ^ security_bits)"
    by simp
  have real_bound:
      "(1::real) / real (2 ^ security_bits) \<le> 1 / 4"
    using denom_real denom_pos
    by (simp add: pos_divide_le_eq divide_le_eq)
  show ?thesis
    unfolding soundness_security_target_def
    apply (subst nn2real_le_iff[symmetric])
    apply (simp only: nn2real_divide nn2real_nnreal nn2real_1)
    using real_bound
    by simp
qed

lemma one_third_le_nonempty_parameter_error:
  assumes domain_large: "8 \<le> clength * scale"
    and query_nontrivial: "2 \<le> query_sample_space_size"
    and nonempty: "0 < ceil_log clength"
  shows
    "(1 :: prob) / 3 \<le>
      ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
        budgets"
proof -
  have residual:
      "(1 :: prob) / 3 \<le>
        ro_checked_staged_conditioned_residual_query_error budgets"
    by (rule one_third_le_conditioned_residual_query_error[
      OF domain_large query_nontrivial nonempty])
  have component:
      "ro_checked_staged_conditioned_residual_query_error budgets \<le>
        ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
          budgets"
    by (rule nonempty_parameter_error_component_le)
      (simp add: nonempty_parameter_error_components_def)
  show ?thesis
    by (rule order_trans[OF residual component])
qed

lemma realistic_nonempty_parameter_error_not_security_target:
  assumes domain_large: "8 \<le> clength * scale"
    and false_statement: "\<not> exists_valid_trace"
    and nonempty: "0 < ceil_log clength"
    and bits_two: "2 \<le> security_bits"
  shows
    "\<not> ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
        budgets
      \<le> soundness_security_target security_bits"
proof
  assume target:
      "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
          budgets
        \<le> soundness_security_target security_bits"
  have query_nontrivial: "2 \<le> query_sample_space_size"
    using not_exists_valid_trace_imp_query_sample_space_size_gt_one[
      OF false_statement] by simp
  have third_le:
      "(1 :: prob) / 3 \<le>
        ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
          budgets"
    by (rule one_third_le_nonempty_parameter_error[
      OF domain_large query_nontrivial nonempty])
  have target_le: "soundness_security_target security_bits \<le>
      (1 :: prob) / 4"
    by (rule soundness_security_target_le_quarter[OF bits_two])
  have impossible: "(1 :: prob) / 3 \<le> 1 / 4"
    by (rule order_trans[OF third_le order_trans[OF target target_le]])
  have represented:
      "nn2real ((1 :: prob) / 3) \<le> nn2real ((1 :: prob) / 4)"
    using impossible by (simp only: nn2real_le_iff)
  have real_impossible: "(1 :: real) / 3 \<le> 1 / 4"
    using represented by simp
  then show False by linarith
qed

end

end
