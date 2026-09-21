
theory Soundness_FRI_Correlated_Agreement_Comparison
 imports Stark.Soundness_FRI_Correlated_Agreement_Parameter_Bound
   Stark.Soundness_FRI_Robust_Balanced_Strict_Selected_Parameter_Bound
begin
section \<open>Complete-error comparison with the strict selected bound\<close>
text \<open>
  The former common-charge ledger is retained as a reference. The local
  target credit and both changed challenge charges remain explicit. The reference arithmetic specializes parameter
  expressions only; it constructs no field interpretation or accepting execution.
  These comparisons do not resolve the earlier balanced-clean survivor maximum.
\<close>

context soundness
begin

definition ro_mca_common_parameter_error :: "staged_budgets \<Rightarrow> prob" where
 "ro_mca_common_parameter_error budgets =
   hash_collision_budget_value 0 (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
   ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
   ro_absorb_checked_staged_trace_composition_prefix_target_error budgets +
   ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
   ro_checked_staged_conditioned_initial_target_error budgets +
   ro_checked_staged_conditioned_residual_query_phase_target_error budgets +
   ro_checked_staged_first_root_robust_alpha_pivot_error budgets"

definition ro_mca_sampling_error :: "nat \<Rightarrow> nat \<Rightarrow> staged_budgets \<Rightarrow> prob" where
 "ro_mca_sampling_error rT rC budgets =
   ro_mca_rectangle_error (mca_decoded_semantic_query_index_bound rT rC) budgets +
   ro_mca_combined_rectangle_error rT rC budgets"

definition ro_mca_previous_sampling_error :: "nat \<Rightarrow> staged_budgets \<Rightarrow> prob" where
 "ro_mca_previous_sampling_error C budgets =
   ro_checked_staged_balanced_decoded_semantic_rectangle_error_adaptive C budgets +
   ro_checked_staged_balanced_strict_selected_combined_actual_residual_rectangle_error_adaptive C budgets"


lemma ro_mca_nonempty_error_decomposition:
 "ro_mca_nonempty_parameter_error rT rC budgets + ro_prefix_local_target_saving budgets =
   ro_mca_common_parameter_error budgets +
   (ro_mca_sampling_error rT rC budgets + (ro_mca_challenge_error budgets + ro_mca_challenge_error budgets))"
 unfolding ro_mca_nonempty_parameter_error_def ro_mca_common_parameter_error_def
   ro_mca_sampling_error_def
 by (simp add: ro_composition_prefix_target_error_local_credit
   ro_query_phase_target_error_local_credit ro_prefix_local_target_saving_def
   Let_def algebra_simps)

lemma ro_mca_nonempty_error_le_former:
 "ro_mca_nonempty_parameter_error rT rC budgets \<le>
   ro_mca_common_parameter_error budgets +
   (ro_mca_sampling_error rT rC budgets + (ro_mca_challenge_error budgets + ro_mca_challenge_error budgets))"
 by (subst ro_mca_nonempty_error_decomposition[symmetric]) simp

lemma ro_mca_previous_error_decomposition:
 "ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets =
   ro_mca_common_parameter_error budgets +
   (ro_mca_previous_sampling_error C budgets +
    ro_checked_staged_balanced_trace_challenge_error C budgets +
    ro_checked_staged_balanced_composition_challenge_error C budgets)"
 unfolding ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error_def
   ro_mca_common_parameter_error_def ro_mca_previous_sampling_error_def
 by (simp add: algebra_simps)

lemma ro_mca_complete_comparison_iff:
 "(ro_mca_nonempty_parameter_error rT rC budgets \<le>
   ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets) \<longleftrightarrow>
  (ro_mca_sampling_error rT rC budgets + (ro_mca_challenge_error budgets + ro_mca_challenge_error budgets) \<le>
   ro_mca_previous_sampling_error C budgets +
   ro_checked_staged_balanced_trace_challenge_error C budgets +
   ro_checked_staged_balanced_composition_challenge_error C budgets +
   ro_prefix_local_target_saving budgets)"
proof -
 have "(ro_mca_nonempty_parameter_error rT rC budgets \<le>
   ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets) \<longleftrightarrow>
   (ro_mca_nonempty_parameter_error rT rC budgets + ro_prefix_local_target_saving budgets \<le>
    ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets +
    ro_prefix_local_target_saving budgets)" by simp
 also have "... \<longleftrightarrow>
   (ro_mca_sampling_error rT rC budgets + (ro_mca_challenge_error budgets + ro_mca_challenge_error budgets) \<le>
    ro_mca_previous_sampling_error C budgets +
    ro_checked_staged_balanced_trace_challenge_error C budgets +
    ro_checked_staged_balanced_composition_challenge_error C budgets +
    ro_prefix_local_target_saving budgets)"
   unfolding ro_mca_nonempty_error_decomposition ro_mca_previous_error_decomposition
   by (simp add: add.assoc)
 finally show ?thesis .
qed

lemma ro_mca_complete_strict_comparison_iff:
 "(ro_mca_nonempty_parameter_error rT rC budgets <
   ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets) \<longleftrightarrow>
  (ro_mca_sampling_error rT rC budgets + (ro_mca_challenge_error budgets + ro_mca_challenge_error budgets) <
   ro_mca_previous_sampling_error C budgets +
   ro_checked_staged_balanced_trace_challenge_error C budgets +
   ro_checked_staged_balanced_composition_challenge_error C budgets +
   ro_prefix_local_target_saving budgets)"
proof -
 have "(ro_mca_nonempty_parameter_error rT rC budgets <
   ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets) \<longleftrightarrow>
   (ro_mca_nonempty_parameter_error rT rC budgets + ro_prefix_local_target_saving budgets <
    ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets +
    ro_prefix_local_target_saving budgets)" by simp
 also have "... \<longleftrightarrow>
   (ro_mca_sampling_error rT rC budgets + (ro_mca_challenge_error budgets + ro_mca_challenge_error budgets) <
    ro_mca_previous_sampling_error C budgets +
    ro_checked_staged_balanced_trace_challenge_error C budgets +
    ro_checked_staged_balanced_composition_challenge_error C budgets +
    ro_prefix_local_target_saving budgets)"
   unfolding ro_mca_nonempty_error_decomposition ro_mca_previous_error_decomposition
   by (simp add: add.assoc)
 finally show ?thesis .
qed


lemma ro_mca_reference_semantic_base:
 assumes p: "powers=2" and sc: "scale=64" and m: "query_sample_space_size=65472"
   and dg: "maxDegree=1023" and roots: "length all_constraint_roots=1024"
 shows "trace_composition_padding_query_index_bound=33791"
proof -
 have interval: "{Suc 0..<2::nat} = {Suc 0}" by auto
 show ?thesis
   unfolding trace_composition_padding_query_index_bound_def
   unfolding trace_composition_query_index_bound_for_def
   unfolding query_agreement_bound_for_def
   unfolding fri_padded_degree_bound_def
   using p sc m dg roots by (simp add: interval)
qed

lemma ro_mca_reference_balanced_radius:
 assumes ep: "clength*scale=2^16"
 shows "fri_balanced_radius 10 54 0 = 13438"
 unfolding fri_balanced_radius_def fri_balanced_margin_def
   fri_canonical_domain_at_length ep
 by (simp add: atLeast0LessThan fri_mca_ten_indices)

lemma ro_mca_reference_balanced_cap:
 assumes ep: "clength*scale=2^16"
 shows "fri_balanced_challenge_card_bound 10 54 = 13441"
 using fri_balanced_radius_step[of 0 10 54] ro_mca_reference_balanced_radius[OF ep]
 unfolding fri_balanced_challenge_card_bound_def by simp

lemma ro_mca_reference_previous_residual:
 assumes ep: "clength*scale=2^16" and qs: "query_sample_space_size=65472"
 shows "fri_balanced_strict_selected_residual_index_card_bound 1023 54 = 64320"
 unfolding fri_balanced_strict_selected_residual_index_card_bound_def
   fri_mca_scale64_log fri_mca_ten_indices fri_balanced_margin_def
   fri_canonical_domain_at_length ep qs modulo_preimage_card_envelope_def
 by (simp add: fri_mca_ten_indices)

lemma ro_mca_reference_new_residual:
 assumes ep: "clength*scale=2^16" and qs: "query_sample_space_size=65472"
 shows "fri_mca_residual_index_bound 1023 fri_mca_quarter_radii 10581 = 54954"
 unfolding fri_mca_residual_index_bound_def fri_mca_scale64_log
   fri_mca_scale64_support_threshold[OF ep qs] fri_canonical_domain_at_length ep
 by (simp add: fri_mca_scale64_support_threshold[OF ep qs])

lemma ro_mca_reference_semantic_envelopes:
 assumes cl: "clength=1024" and sc: "scale=64" and p: "powers=2"
   and dg: "maxDegree=1023" and roots: "length all_constraint_roots=1024"
 shows "balanced_decoded_semantic_query_index_bound 54 = 60667"
   "mca_decoded_semantic_query_index_bound 10581 10581 = 54953"
proof -
 have ep: "clength*scale=2^16" using cl sc by simp
 have qs: "query_sample_space_size=65472" by (rule fri_mca_scale64_query_size[OF ep sc p])
 have base: "trace_composition_padding_query_index_bound=33791"
   by (rule ro_mca_reference_semantic_base[OF p sc qs dg roots])
 have logs: "ceil_log clength = 10" "ceil_log (Suc maxDegree) = 10" using cl dg by simp_all
 show "balanced_decoded_semantic_query_index_bound 54 = 60667"
   unfolding balanced_decoded_semantic_query_index_bound_def
   using base ro_mca_reference_balanced_radius[OF ep] logs by simp
 show "mca_decoded_semantic_query_index_bound 10581 10581 = 54953"
   unfolding mca_decoded_semantic_query_index_bound_def base by simp
qed


lemma ro_mca_reference_sampling:
 assumes cl: "clength=1024" and sc: "scale=64" and p: "powers=2"
   and dg: "maxDegree=1023" and roots: "length all_constraint_roots=1024"
 shows "ro_mca_sampling_error 10581 10581 budgets =
     ro_mca_rectangle_error 54953 budgets +
     (ro_mca_rectangle_error 54954 budgets + ro_mca_rectangle_error 54954 budgets)"
   "ro_mca_previous_sampling_error 54 budgets =
     ro_mca_rectangle_error 60667 budgets +
     (ro_mca_rectangle_error 64320 budgets + ro_mca_rectangle_error 64320 budgets)"
proof -
 have ep: "clength*scale=2^16" using cl sc by simp
 have qs: "query_sample_space_size=65472" by (rule fri_mca_scale64_query_size[OF ep sc p])
 have dt: "clength-1=1023" using cl by simp
 note semantic = ro_mca_reference_semantic_envelopes[OF cl sc p dg roots]
 note new = ro_mca_reference_new_residual[OF ep qs]
 note old = ro_mca_reference_previous_residual[OF ep qs]
 have bounds: "fri_mca_residual_branch_bound 10581 True = 54954"
   "fri_mca_residual_branch_bound 10581 False = 54954"
   unfolding fri_mca_residual_branch_bound_def
   by (simp_all only: if_True if_False dt dg new)
 show "ro_mca_sampling_error 10581 10581 budgets =
     ro_mca_rectangle_error 54953 budgets +
     (ro_mca_rectangle_error 54954 budgets + ro_mca_rectangle_error 54954 budgets)"
   unfolding ro_mca_sampling_error_def ro_mca_combined_rectangle_error_def
   by (simp only: semantic bounds)
 show "ro_mca_previous_sampling_error 54 budgets =
     ro_mca_rectangle_error 60667 budgets +
     (ro_mca_rectangle_error 64320 budgets + ro_mca_rectangle_error 64320 budgets)"
   unfolding ro_mca_previous_sampling_error_def
     ro_checked_staged_balanced_strict_selected_combined_actual_residual_rectangle_error_adaptive_def
     ro_checked_staged_balanced_strict_selected_residual_rectangle_error_adaptive_def
     ro_checked_staged_balanced_decoded_semantic_rectangle_error_adaptive_def
     ro_mca_rectangle_error_def
   by (simp only: semantic dt dg old)
qed

end
end
