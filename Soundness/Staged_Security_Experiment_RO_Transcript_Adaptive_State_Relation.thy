(*  Title:      Stark/Staged_Security_Experiment_RO_Transcript_Adaptive_State_Relation.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_RO_Transcript_Adaptive_State_Relation
  imports Staged_Security_Experiment_RO_Adaptive_State_Relation
begin

context soundness
begin

lemma adaptive_hash_query_budget_ro_checked_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "adaptive_hash_query_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets)
      (ro_checked_staged_transcript_program A)"
proof -
  let ?trace_root = "trace_root_budget budgets"
  let ?trace_fri =
    "sum_list (trace_fri_budgets budgets) + 2 * ceil_log clength"
  let ?trace_final = "trace_final_budget budgets"
  let ?alpha = "2 * length spec"
  let ?degree = "degree_budget budgets"
  let ?composition_fri =
    "sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  let ?query =
    "sum_list (query_opening_budgets budgets) + rounds +
      rounds * ro_checked_query_round_transcript_bound"
  have trace_root_range:
    "adaptive_hash_query_budget ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_adaptive_hash_query_budget)
  have trace_fri_range:
    "adaptive_hash_query_budget ?trace_fri
      (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len: "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "adaptive_hash_query_budget
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          2 * ceil_log clength)
        (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule adaptive_hash_query_budget_ro_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final_range:
    "\<And>bs. adaptive_hash_query_budget ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_adaptive_hash_query_budget)
  have alpha_range:
    "adaptive_hash_query_budget ?alpha (ro_staged_alpha_program (length spec))"
    by (rule adaptive_hash_query_budget_ro_staged_alpha_program)
  have degree_range:
    "\<And>as. adaptive_hash_query_budget ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_adaptive_hash_query_budget)
  have composition_fri_range:
    "\<And>dg. adaptive_hash_query_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule adaptive_hash_query_budget_guarded_ro_staged_composition_fri_program
        [OF wf controlled])
  have composition_final_range:
    "\<And>dg bs. adaptive_hash_query_budget ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_adaptive_hash_query_budget)
  have query_range:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list).
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      adaptive_hash_query_budget ?query
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
  proof -
    fix trace_roots composition_roots :: "'f list"
    assume trace_len: "length trace_roots = ceil_log clength"
      and composition_len:
        "length composition_roots \<le> ceil_log (maxDegree + 1)"
    have len: "0 + rounds \<le> length (query_opening_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "adaptive_hash_query_budget
        (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
          rounds + rounds * ro_checked_query_round_transcript_bound)
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      by (rule adaptive_hash_query_budget_ro_checked_staged_query_program_closed
          [OF controlled len trace_len composition_len])
    then show
      "adaptive_hash_query_budget ?query
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have query_tail:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list) F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      adaptive_hash_query_budget (?query + 0)
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds \<bind>
          (\<lambda>query_chunks. return (F query_chunks)))"
    by (rule adaptive_hash_query_budget_bind)
      (rule query_range, assumption, assumption, rule adaptive_hash_query_budget_return)
  have after_composition_final_record:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list) composition_final F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      adaptive_hash_query_budget (1 + (?query + 0))
        (ro_record_staged_message composition_final \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots 0 rounds \<bind>
            (\<lambda>query_chunks. return (F query_chunks))))"
    by (rule adaptive_hash_query_budget_bind)
      (rule adaptive_hash_query_budget_ro_record_staged_message,
        rule query_tail, assumption, assumption)
  have after_composition_final:
    "\<And>(trace_roots :: 'f list) dg (composition_roots :: 'f list) bs F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      adaptive_hash_query_budget (?composition_final + (1 + (?query + 0)))
        (composition_final_stage A dg bs \<bind>
          (\<lambda>composition_final.
            ro_record_staged_message composition_final \<bind>
              (\<lambda>_. ro_checked_staged_query_program A trace_roots
                composition_roots 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return (F composition_final query_chunks)))))"
    by (rule adaptive_hash_query_budget_bind)
      (rule composition_final_range, rule after_composition_final_record,
        assumption, assumption)
  have after_composition_fri:
    "\<And>(trace_roots :: 'f list) dg F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      adaptive_hash_query_budget
        (?composition_fri +
          (?composition_final + (1 + (?query + 0))))
        ((assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. ro_staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [])) \<bind>
          (\<lambda>(composition_roots, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                ro_record_staged_message composition_final \<bind>
                  (\<lambda>_. ro_checked_staged_query_program A trace_roots
                    composition_roots 0 rounds \<bind>
                    (\<lambda>query_chunks.
                      return
                        (F composition_roots composition_bs
                          composition_final query_chunks))))))"
  proof (rule adaptive_hash_query_budget_bind_on_outcomes)
    fix trace_roots :: "'f list"
    fix dg F
    show "adaptive_hash_query_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_range)
  next
    fix trace_roots :: "'f list"
    fix dg F s x t
    assume trace_len: "length trace_roots = ceil_log clength"
      and out:
        "Some (x, t) \<in>
          set_dist
            (execute
              (assert (ceil_log (to_nat dg + 1) \<le>
                  ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. ro_staged_composition_fri_program A dg 0
                  (ceil_log (to_nat dg + 1)) [])) s)"
    show "adaptive_hash_query_budget (?composition_final + (1 + (?query + 0)))
      (case x of (composition_roots, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            ro_record_staged_message composition_final \<bind>
              (\<lambda>_. ro_checked_staged_query_program A trace_roots
                composition_roots 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have composition_len:
        "length composition_roots \<le> ceil_log (maxDegree + 1)"
        using guarded_ro_staged_composition_fri_program_output_roots_length_le
          [OF out[unfolded Pair]] .
      have "adaptive_hash_query_budget (?composition_final + (1 + (?query + 0)))
        (composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            ro_record_staged_message composition_final \<bind>
              (\<lambda>_. ro_checked_staged_query_program A trace_roots
                composition_roots 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
        by (rule after_composition_final[OF trace_len composition_len])
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_degree_record:
    "\<And>(trace_roots :: 'f list) dg F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      adaptive_hash_query_budget
        (1 +
          (?composition_fri +
            (?composition_final + (1 + (?query + 0)))))
        (ro_record_staged_message dg \<bind>
          (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
              ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])) \<bind>
            (\<lambda>(composition_roots, composition_bs).
              composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  ro_record_staged_message composition_final \<bind>
                    (\<lambda>_. ro_checked_staged_query_program A trace_roots
                      composition_roots 0 rounds \<bind>
                      (\<lambda>query_chunks.
                        return
                          (F composition_roots composition_bs
                            composition_final query_chunks)))))))"
    by (rule adaptive_hash_query_budget_bind)
      (rule adaptive_hash_query_budget_ro_record_staged_message,
        rule after_composition_fri, assumption)
  have after_degree:
    "\<And>(trace_roots :: 'f list) as F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      adaptive_hash_query_budget
        (?degree +
          (1 +
            (?composition_fri +
              (?composition_final + (1 + (?query + 0))))))
        (degree_stage A as \<bind>
          (\<lambda>dg. ro_record_staged_message dg \<bind>
            (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. ro_staged_composition_fri_program A dg 0
                (ceil_log (to_nat dg + 1)) [])) \<bind>
              (\<lambda>(composition_roots, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    ro_record_staged_message composition_final \<bind>
                      (\<lambda>_. ro_checked_staged_query_program A trace_roots
                        composition_roots 0 rounds \<bind>
                        (\<lambda>query_chunks.
                          return
                            (F dg composition_roots composition_bs
                              composition_final query_chunks))))))))"
    by (rule adaptive_hash_query_budget_bind)
      (rule degree_range, rule after_degree_record, assumption)
  have after_alpha:
    "\<And>(trace_roots :: 'f list) F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      adaptive_hash_query_budget
        (?alpha +
          (?degree +
            (1 +
              (?composition_fri +
                (?composition_final + (1 + (?query + 0)))))))
        (ro_staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. ro_record_staged_message dg \<bind>
              (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                  ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. ro_staged_composition_fri_program A dg 0
                  (ceil_log (to_nat dg + 1)) [])) \<bind>
                (\<lambda>(composition_roots, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      ro_record_staged_message composition_final \<bind>
                        (\<lambda>_. ro_checked_staged_query_program A trace_roots
                          composition_roots 0 rounds \<bind>
                          (\<lambda>query_chunks.
                            return
                              (F as dg composition_roots composition_bs
                                composition_final query_chunks)))))))))"
    by (rule adaptive_hash_query_budget_bind)
      (rule alpha_range, rule after_degree, assumption)
  have after_trace_final_record:
    "\<And>(trace_roots :: 'f list) trace_final F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      adaptive_hash_query_budget
        (1 +
          (?alpha +
            (?degree +
              (1 +
                (?composition_fri +
                  (?composition_final + (1 + (?query + 0))))))))
        (ro_record_staged_message trace_final \<bind>
          (\<lambda>_. ro_staged_alpha_program (length spec) \<bind>
            (\<lambda>as. degree_stage A as \<bind>
              (\<lambda>dg. ro_record_staged_message dg \<bind>
                (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_. ro_staged_composition_fri_program A dg 0
                    (ceil_log (to_nat dg + 1)) [])) \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        ro_record_staged_message composition_final \<bind>
                          (\<lambda>_. ro_checked_staged_query_program A trace_roots
                            composition_roots 0 rounds \<bind>
                            (\<lambda>query_chunks.
                              return
                                (F as dg composition_roots composition_bs
                                  composition_final query_chunks))))))))))"
    by (rule adaptive_hash_query_budget_bind)
      (rule adaptive_hash_query_budget_ro_record_staged_message,
        rule after_alpha, assumption)
  have after_trace_final:
    "\<And>(trace_roots :: 'f list) trace_bs F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      adaptive_hash_query_budget
        (?trace_final +
          (1 +
            (?alpha +
              (?degree +
                (1 +
                  (?composition_fri +
                    (?composition_final + (1 + (?query + 0)))))))))
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. ro_record_staged_message trace_final \<bind>
            (\<lambda>_. ro_staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. ro_record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                      ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. ro_staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          ro_record_staged_message composition_final \<bind>
                            (\<lambda>_. ro_checked_staged_query_program A
                              trace_roots composition_roots 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_final as dg composition_roots
                                    composition_bs composition_final
                                    query_chunks)))))))))))"
    by (rule adaptive_hash_query_budget_bind)
      (rule trace_final_range, rule after_trace_final_record, assumption)
  have after_trace_fri:
    "\<And>F. adaptive_hash_query_budget
      (?trace_fri +
        (?trace_final +
          (1 +
            (?alpha +
              (?degree +
                (1 +
                  (?composition_fri +
                    (?composition_final + (1 + (?query + 0))))))))))
      (ro_staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final. ro_record_staged_message trace_final \<bind>
              (\<lambda>_. ro_staged_alpha_program (length spec) \<bind>
                (\<lambda>as. degree_stage A as \<bind>
                  (\<lambda>dg. ro_record_staged_message dg \<bind>
                    (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                        ceil_log (maxDegree + 1)) \<bind>
                      (\<lambda>_. ro_staged_composition_fri_program A dg 0
                        (ceil_log (to_nat dg + 1)) [])) \<bind>
                      (\<lambda>(composition_roots, composition_bs).
                        composition_final_stage A dg composition_bs \<bind>
                          (\<lambda>composition_final.
                            ro_record_staged_message composition_final \<bind>
                              (\<lambda>_. ro_checked_staged_query_program A
                                trace_roots composition_roots 0 rounds \<bind>
                                (\<lambda>query_chunks.
                                  return
                                    (F trace_roots trace_bs trace_final as dg
                                      composition_roots composition_bs
                                      composition_final query_chunks))))))))))))"
  proof (rule adaptive_hash_query_budget_bind_on_outcomes)
    fix F
    show "adaptive_hash_query_budget ?trace_fri
      (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_range)
  next
    fix F s x t
    assume out:
      "Some (x, t) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s)"
    show "adaptive_hash_query_budget
      (?trace_final +
        (1 +
          (?alpha +
            (?degree +
              (1 +
                (?composition_fri +
                  (?composition_final + (1 + (?query + 0)))))))))
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. ro_record_staged_message trace_final \<bind>
            (\<lambda>_. ro_staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. ro_record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                      ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. ro_staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          ro_record_staged_message composition_final \<bind>
                            (\<lambda>_. ro_checked_staged_query_program A
                              trace_roots composition_roots 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have trace_len: "length trace_roots = ceil_log clength"
        using ro_staged_trace_fri_program_output_lengths[OF out[unfolded Pair]]
        by simp
      have "adaptive_hash_query_budget
        (?trace_final +
          (1 +
            (?alpha +
              (?degree +
                (1 +
                  (?composition_fri +
                    (?composition_final + (1 + (?query + 0)))))))))
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. ro_record_staged_message trace_final \<bind>
            (\<lambda>_. ro_staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. ro_record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                      ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. ro_staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          ro_record_staged_message composition_final \<bind>
                            (\<lambda>_. ro_checked_staged_query_program A
                              trace_roots composition_roots 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
        by (rule after_trace_final[OF trace_len])
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_trace_root_record:
    "\<And>fr F. adaptive_hash_query_budget
      (1 +
        (?trace_fri +
          (?trace_final +
            (1 +
              (?alpha +
                (?degree +
                  (1 +
                    (?composition_fri +
                      (?composition_final + (1 + (?query + 0)))))))))))
      (ro_record_staged_message fr \<bind>
        (\<lambda>_. ro_staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final. ro_record_staged_message trace_final \<bind>
                (\<lambda>_. ro_staged_alpha_program (length spec) \<bind>
                  (\<lambda>as. degree_stage A as \<bind>
                    (\<lambda>dg. ro_record_staged_message dg \<bind>
                      (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                          ceil_log (maxDegree + 1)) \<bind>
                        (\<lambda>_. ro_staged_composition_fri_program A dg 0
                          (ceil_log (to_nat dg + 1)) [])) \<bind>
                        (\<lambda>(composition_roots, composition_bs).
                          composition_final_stage A dg composition_bs \<bind>
                            (\<lambda>composition_final.
                              ro_record_staged_message composition_final \<bind>
                                (\<lambda>_. ro_checked_staged_query_program A
                                  trace_roots composition_roots 0 rounds \<bind>
                                  (\<lambda>query_chunks.
                                    return
                                      (F trace_roots trace_bs trace_final as
                                        dg composition_roots composition_bs
                                        composition_final query_chunks)))))))))))))"
    by (rule adaptive_hash_query_budget_bind)
      (rule adaptive_hash_query_budget_ro_record_staged_message, rule after_trace_fri)
  have whole:
    "adaptive_hash_query_budget
      (?trace_root +
        (1 +
          (?trace_fri +
            (?trace_final +
              (1 +
                (?alpha +
                  (?degree +
                    (1 +
                      (?composition_fri +
                        (?composition_final + (1 + (?query + 0))))))))))))
      (ro_checked_staged_transcript_program A)"
    unfolding ro_checked_staged_transcript_program_def Let_def
  proof (rule adaptive_hash_query_budget_bind)
    show "adaptive_hash_query_budget ?trace_root (trace_root_stage A)"
      by (rule trace_root_range)
  next
    fix fr
    show "adaptive_hash_query_budget
      (1 +
        (?trace_fri +
          (?trace_final +
            (1 +
              (?alpha +
                (?degree +
                  (1 +
                    (?composition_fri +
                      (?composition_final + (1 + (?query + 0)))))))))))
      (ro_record_staged_message fr \<bind>
        (\<lambda>_. ro_staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                ro_record_staged_message trace_final \<bind>
                  (\<lambda>_. ro_staged_alpha_program (length spec) \<bind>
                    (\<lambda>as. degree_stage A as \<bind>
                      (\<lambda>dg. ro_record_staged_message dg \<bind>
                        (\<lambda>_. assert (ceil_log (to_nat dg + 1) \<le>
                          ceil_log (maxDegree + 1)) \<bind>
                          (\<lambda>_. ro_staged_composition_fri_program A dg 0
                            (ceil_log (to_nat dg + 1)) [] \<bind>
                            (\<lambda>(composition_roots, composition_bs).
                              composition_final_stage A dg composition_bs \<bind>
                                (\<lambda>composition_final.
                                  ro_record_staged_message
                                    composition_final \<bind>
                                    (\<lambda>_. ro_checked_staged_query_program A
                                      trace_roots composition_roots 0
                                      rounds \<bind>
                                      (\<lambda>query_chunks.
                                        return
                                          \<lparr>staged_trace_root = fr,
                                           staged_trace_fri_roots =
                                            trace_roots,
                                           staged_trace_fri_challenges =
                                            trace_bs,
                                           staged_trace_final =
                                            trace_final,
                                           staged_alphas = as,
                                           staged_degree = dg,
                                           staged_composition_fri_roots =
                                            composition_roots,
                                           staged_composition_fri_challenges =
                                            composition_bs,
                                           staged_composition_final =
                                            composition_final,
                                           staged_query_chunks =
                                            query_chunks\<rparr>)))))))))))))"
      using after_trace_root_record
        [of fr
          "\<lambda>trace_roots trace_bs trace_final as dg composition_roots
              composition_bs composition_final query_chunks.
            \<lparr>staged_trace_root = fr,
             staged_trace_fri_roots = trace_roots,
             staged_trace_fri_challenges = trace_bs,
             staged_trace_final = trace_final,
             staged_alphas = as,
             staged_degree = dg,
             staged_composition_fri_roots = composition_roots,
             staged_composition_fri_challenges = composition_bs,
             staged_composition_final = composition_final,
             staged_query_chunks = query_chunks\<rparr>"]
      by (simp add: sm_bind_assoc)
  qed
  have budget_eq:
    "?trace_root +
        (1 +
          (?trace_fri +
            (?trace_final +
              (1 +
                (?alpha +
                  (?degree +
                    (1 +
                      (?composition_fri +
                        (?composition_final + (1 + (?query + 0))))))))))) =
      ro_checked_staged_transcript_hash_query_budget_for budgets"
    unfolding ro_checked_staged_transcript_hash_query_budget_for_def
    by (simp add: add.assoc add.commute add.left_commute)
  show ?thesis
    using whole unfolding budget_eq .
qed

end
end
