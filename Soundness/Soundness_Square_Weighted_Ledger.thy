(* Title: Stark/Soundness_Square_Weighted_Ledger.thy
   License: BSD-3-Clause *)

theory Soundness_Square_Weighted_Ledger
  imports Soundness_Square_Prefix_Budgets
    Stark.Soundness_FRI_Weighted_Soundness
    Stark.Soundness_FRI_Correlated_Agreement_Comparison
begin

section \<open>Source-connected weighted error ledger for the square workload\<close>

text \<open>This layer specializes the existing weighted error to length 1024,
  scale 64 and the reference radii 10581, retaining arbitrary staged allocations.
  The quotient and remainder are those of the unchanged modulo sampler.
  All common charges, including nested alpha charges, the full initial-target
  charge and the weighted connection charge remain. The arithmetic definitions
  are connected to the source by exact HOL equalities; numerical diagnostic
  files are not proof inputs. No allocation maximum or bit-security target is
  certified here.\<close>

subsection \<open>Explicit arithmetic definitions\<close>


lemma square_nn2real_of_nat:
  "nn2real (semiring_1_class.of_nat n) = real n"
  by (simp only: nnreal_of_nat[symmetric] nn2real_nnreal)

lemma square_nnreal_power:
  "nn2real (x^k) = (nn2real x)^k"
  by (induction k) simp_all

definition square_mca_common_numerator :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "square_mca_common_numerator R s j opening =
    (let q=s+j+opening+50+535*R; v=50+1429*R; n=q+v;
         aft=j+opening+48+535*R; t=opening+535*R; h=s+j+50; b=2*s+6
     in n^2 + (aft+v)*b + (t+v)*(1+2*h) + v*(20+2*q) +
        2*q*(16384+(7*q+2)) + t*(20+2*h) +
        q^2 + q + aft*b + q*(6*q+3))"

definition square_modulo_base :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "square_modulo_base F B =
    real ((F div 65472)*B + min B (F mod 65472)) / real F"

definition square_weighted_ledger :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "square_weighted_ledger F R s j opening =
    (let n=s+j+opening+100+1964*R
     in real (square_mca_common_numerator R s j opening) / real F +
       real n / real F +
       real n * (square_modulo_base F 54953^R + 2*square_modulo_base F 54954^R) +
       5*real n*(real n-1)/(2*real F))"

context soundness
begin

subsection \<open>All retained non-sampling charges\<close>

lemma square_common_error_ledger:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
    and wf: "staged_budget_wellformed budgets"
  shows "ro_mca_weighted_common_error budgets =
    nnreal (square_mca_common_numerator rounds (square_early_budget budgets)
      (square_middle_budget budgets) (square_opening_budget budgets)) / nnreal size"
proof -
  note md=square_budget_metadata[OF schema geometry]
  note rb=square_round_budget[OF schema geometry]
  note tb=square_total_budget[OF schema geometry]
  note pb=square_prefix_budgets[OF schema geometry wf]
  have cap: "fri_mca_direct_cap=16384"
    unfolding fri_mca_direct_cap_def fri_mca_quarter_radii_def
      fri_canonical_domain_at_length
    using geometry by simp
  show ?thesis
    apply (rule nn2real_eq_iff[THEN iffD1])
    unfolding ro_mca_weighted_common_error_def
      ro_absorb_checked_staged_first_root_prefix_merkle_target_error_def
      ro_absorb_checked_staged_local_composition_prefix_target_error_def
      ro_absorb_checked_staged_fri_builder_merkle_target_error_def
      ro_mca_challenge_error_def ro_checked_staged_local_query_phase_target_error_def
      ro_checked_staged_first_root_robust_alpha_pivot_error_def
      ro_checked_staged_first_root_prefix_merkle_target_error_def
      hash_collision_budget_value_def square_mca_common_numerator_def
    by (simp add: square_nn2real_of_nat md rb tb pb cap square_budget_partition
      square_opening_budget_def[symmetric] Let_def
      add_divide_nnreal[symmetric] algebra_simps power2_eq_square)
qed


subsection \<open>Exact modulo sampling and the complete weighted alternative\<close>

lemma square_weighted_residual_ledger:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
  shows "nn2real (ro_mca_weighted_residual_power_sum 10581 10581 k) =
    square_modulo_base size 54953^k + 2*square_modulo_base size 54954^k"
proof -
  note md=square_workload_reference_metadata[OF schema geometry]
  have ep: "clength*scale=2^16" using geometry by simp
  note semantic=ro_mca_reference_semantic_envelopes(2)[OF geometry md(1,2)]
  note residual=ro_mca_reference_new_residual[OF ep md(3)]
  have branches: "fri_mca_residual_branch_bound 10581 True=54954"
    "fri_mca_residual_branch_bound 10581 False=54954"
    unfolding fri_mca_residual_branch_bound_def
    using geometry md residual by simp_all
  show ?thesis
    unfolding ro_mca_weighted_residual_power_sum_explicit semantic branches
      query_raw_preimage_card_envelope_def md(3)
    by (simp add: square_nnreal_power square_nn2real_of_nat
      square_modulo_base_def algebra_simps)
qed

lemma square_weighted_error_ledger:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
    and wf: "staged_budget_wellformed budgets"
  shows "nn2real (ro_mca_weighted_nonempty_parameter_error 10581 10581 budgets) =
    square_weighted_ledger size rounds (square_early_budget budgets)
      (square_middle_budget budgets) (square_opening_budget budgets)"
  unfolding ro_mca_weighted_nonempty_parameter_error_def
    ro_mca_weighted_sampling_error_def
    square_common_error_ledger[OF schema geometry wf]
  by (simp add: square_nn2real_of_nat square_weighted_residual_ledger[OF schema geometry]
    ro_mca_weighted_connection_charge_real square_total_budget[OF schema geometry]
    square_budget_partition square_weighted_ledger_def Let_def)

subsection \<open>Eligibility and the unchanged public minimum\<close>

text \<open>The equality above concerns the weighted alternative. The public
  endpoint retains its minimum with older routes. Accordingly the final result
  below is one-sided, not an equality for the public error or the acceptance
  probability. No new premise is added to the existing public theorem.\<close>

lemma square_weighted_regime:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
  shows "ro_mca_weighted_parameter_regime 16"
  using square_budget_metadata[OF schema geometry] geometry rounds_positive
  unfolding ro_mca_weighted_parameter_regime_def ro_mca_parameter_regime_def
    fri_padded_degree_bound_def
  by (simp add: ceil_log_def floor_log_rec)

lemma square_public_error_le_ledger:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
    and wf: "staged_budget_wellformed budgets"
  shows "nn2real (ro_mca_weighted_parameter_error 16 10581 10581 budgets) \<le>
    square_weighted_ledger size rounds (square_early_budget budgets)
      (square_middle_budget budgets) (square_opening_budget budgets)"
proof -
  have "ro_mca_weighted_parameter_error 16 10581 10581 budgets \<le>
    ro_mca_weighted_nonempty_parameter_error 10581 10581 budgets"
    unfolding ro_mca_weighted_parameter_error_def
    using square_weighted_regime[OF schema geometry] by simp
  then have "nn2real (ro_mca_weighted_parameter_error 16 10581 10581 budgets) \<le>
    nn2real (ro_mca_weighted_nonempty_parameter_error 10581 10581 budgets)" by simp
  then show ?thesis by (simp only: square_weighted_error_ledger[OF schema geometry wf])
qed

end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then writeln ("Checked ledger theorem, displayed premises: " ^
      string_of_int (Thm.nprems_of th))
    else error "Unexpected ledger proof dependency")
    @{thms square_nn2real_of_nat square_nnreal_power
      soundness.square_common_error_ledger
      soundness.square_weighted_residual_ledger
      soundness.square_weighted_error_ledger
      soundness.square_weighted_regime
      soundness.square_public_error_le_ledger};
\<close>

end
