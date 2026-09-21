(* Title: Stark/Soundness_Square_Budget_Counts.thy
   License: BSD-3-Clause *)

theory Soundness_Square_Budget_Counts
  imports Stark.Staged_Security_Experiment_RO_Verifier_Budgets
    Stark.Soundness_Square_Sequence_Workload
begin

section \<open>Exact budget accounting for the reference square workload\<close>

text \<open>These equalities specialize the existing budget envelopes, not actual
  execution call counts or distinct oracle keys. Every staged budget field is
  retained. In particular, no opening-stage budget is set to zero. The generic
  metadata obligations are discharged by the existing reference workload
  interpretation; they are not new locale or public soundness assumptions.\<close>

context soundness
begin

subsection \<open>Workload metadata and builder/verifier budgets\<close>

lemma square_budget_metadata:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
  shows "maxDegree=1023" "length spec=3" "ceil_log clength=10"
    "ceil_log (maxDegree+1)=10" "floor_log (clength*scale)=16"
  using square_workload_reference_metadata[OF schema geometry] schema geometry
  by (simp_all add: square_workload_spec_def ceil_log_def floor_log_rec)

lemma square_round_budget:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
  shows "ro_checked_query_round_transcript_bound=534"
    "ro_verifier_query_round_hash_budget=1429"
    "ro_verifier_header_hash_budget=50"
    "ro_verifier_hash_query_budget=50+1429*rounds"
proof -
  note md=square_budget_metadata[OF schema geometry]
  have layers: "fri_layers_transcript_length 10 65536=250"
  proof -
    have ten: "(10::nat)=Suc(Suc(Suc(Suc(Suc(Suc(Suc(Suc(Suc(Suc 0)))))))))"
      by simp
    show ?thesis by (simp only: ten fri_layers_transcript_length.simps)
      (simp add: floor_log_rec)
  qed
  show "ro_checked_query_round_transcript_bound=534"
    unfolding ro_checked_query_round_transcript_bound_def
      query_decommitment_transcript_length_def powers_scaled_def
    using md geometry by (simp add: layers)
  show qb: "ro_verifier_query_round_hash_budget=1429"
    unfolding ro_verifier_query_round_hash_budget_def
      ro_verifier_query_decommit_hash_budget_def ro_verifier_fri_layer_hash_budget_def
      verifier_query_decommit_hash_budget_def verifier_fri_layer_hash_budget_def
    using md geometry by simp
  show hb: "ro_verifier_header_hash_budget=50"
    unfolding ro_verifier_header_hash_budget_def verifier_header_hash_budget_def
    using md by simp
  show "ro_verifier_hash_query_budget=50+1429*rounds"
    by (simp add: ro_verifier_hash_query_budget_def hb qb mult.commute)
qed

lemma square_total_budget:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
  shows "ro_checked_staged_transcript_hash_query_budget_for budgets =
      staged_attacker_query_budget budgets+50+535*rounds"
    "ro_absorb_checked_staged_security_hash_query_budget_for budgets =
      staged_attacker_query_budget budgets+100+1964*rounds"
proof -
  note md=square_budget_metadata[OF schema geometry]
  note rb=square_round_budget[OF schema geometry]
  show q: "ro_checked_staged_transcript_hash_query_budget_for budgets =
      staged_attacker_query_budget budgets+50+535*rounds"
    unfolding ro_checked_staged_transcript_hash_query_budget_for_def
      staged_attacker_query_budget_def
    by (simp only: md rb; simp add: algebra_simps ceil_log_def floor_log_rec)
  show "ro_absorb_checked_staged_security_hash_query_budget_for budgets =
      staged_attacker_query_budget budgets+100+1964*rounds"
    unfolding ro_absorb_checked_staged_security_hash_query_budget_for_def
    by (simp add: q rb algebra_simps)
qed


subsection \<open>A partition retaining every staged allocation\<close>

text \<open>The early part consists of the trace root and first trace-FRI root.
  The middle part contains the remaining pre-query attacker stages; the opening
  part contains every query-opening budget. Their sum is the original global
  attacker budget, including for records that are not wellformed.\<close>

definition square_early_budget :: "staged_budgets \<Rightarrow> nat" where
  "square_early_budget budgets = trace_root_budget budgets +
    sum_list (take 1 (trace_fri_budgets budgets))"

definition square_middle_budget :: "staged_budgets \<Rightarrow> nat" where
  "square_middle_budget budgets = sum_list (drop 1 (trace_fri_budgets budgets)) +
    trace_final_budget budgets + degree_budget budgets +
    sum_list (composition_fri_budgets budgets) + composition_final_budget budgets"

definition square_opening_budget :: "staged_budgets \<Rightarrow> nat" where
  "square_opening_budget budgets = sum_list (query_opening_budgets budgets)"

lemma square_trace_budget_split:
  "sum_list (trace_fri_budgets budgets) =
    sum_list (take 1 (trace_fri_budgets budgets)) +
    sum_list (drop 1 (trace_fri_budgets budgets))"
  by (simp only: sum_list_append[symmetric] append_take_drop_id)

lemma square_budget_partition:
  "staged_attacker_query_budget budgets =
    square_early_budget budgets + square_middle_budget budgets + square_opening_budget budgets"
  using square_trace_budget_split[of budgets]
  unfolding staged_attacker_query_budget_def square_early_budget_def
    square_middle_budget_def square_opening_budget_def
  by arith

end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then writeln ("Checked budget theorem, displayed premises: " ^
      string_of_int (Thm.nprems_of th))
    else error "Unexpected budget proof dependency")
    @{thms soundness.square_budget_metadata soundness.square_round_budget
      soundness.square_total_budget soundness.square_budget_partition};
\<close>
end
