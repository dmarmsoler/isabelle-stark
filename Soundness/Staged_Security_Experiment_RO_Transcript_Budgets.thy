theory Staged_Security_Experiment_RO_Transcript_Budgets
  imports Staged_Security_Experiment_RO_Budgets
begin

context soundness
begin

definition ro_checked_staged_transcript_hash_query_budget_for ::
  "staged_budgets \<Rightarrow> nat" where
  "ro_checked_staged_transcript_hash_query_budget_for budgets =
    trace_root_budget budgets + 1 +
    (sum_list (trace_fri_budgets budgets) + 2 * ceil_log clength) +
    trace_final_budget budgets + 1 +
    2 * length spec +
    degree_budget budgets + 1 +
    (sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1)) +
    composition_final_budget budgets + 1 +
    (sum_list (query_opening_budgets budgets) + rounds +
      rounds * ro_checked_query_round_transcript_bound)"

lemma ro_staged_trace_fri_program_output_lengths:
  assumes out:
    "Some ((roots, bs'), t) \<in>
      set_dist (execute (ro_staged_trace_fri_program A i n bs) s)"
  shows "length roots = n \<and> length bs' = length bs + n"
  using out
proof (induction n arbitrary: i bs s roots bs' t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain root b roots' bs'' s1 s2 s3 where
    tail:
      "Some ((roots', bs''), s3) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A (Suc i) n (bs @ [b])) s2)"
    and roots_eq: "roots = root # roots'"
    and bs_eq: "bs' = bs''"
    unfolding ro_staged_trace_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  from Suc.IH[OF tail] roots_eq bs_eq show ?case
    by simp
qed

lemma ro_staged_composition_fri_program_output_lengths:
  assumes out:
    "Some ((roots, bs'), t) \<in>
      set_dist (execute (ro_staged_composition_fri_program A dg i n bs) s)"
  shows "length roots = n \<and> length bs' = length bs + n"
  using out
proof (induction n arbitrary: i bs s roots bs' t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain root b roots' bs'' s1 s2 s3 where
    tail:
      "Some ((roots', bs''), s3) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg (Suc i) n
              (bs @ [b])) s2)"
    and roots_eq: "roots = root # roots'"
    and bs_eq: "bs' = bs''"
    unfolding ro_staged_composition_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  from Suc.IH[OF tail] roots_eq bs_eq show ?case
    by simp
qed

lemma guarded_ro_staged_composition_fri_program_output_roots_length_le:
  assumes out:
    "Some ((roots, bs), t) \<in>
      set_dist
        (execute
          (assert (ceil_log (to_nat dg + 1) \<le>
              ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])) s)"
  shows "length roots \<le> ceil_log (maxDegree + 1)"
proof -
  obtain u s' where assert_out:
      "Some (u, s') \<in> set_dist
        (execute
          (assert (ceil_log (to_nat dg + 1) \<le>
            ceil_log (maxDegree + 1))) s)"
    and fri_out:
      "Some ((roots, bs), t) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s')"
    using out by (auto elim!: set_dist_bindE)
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have "length roots = ceil_log (to_nat dg + 1)"
    using ro_staged_composition_fri_program_output_lengths[OF fri_out]
    by simp
  then show ?thesis
    using round_bound by simp
qed

lemma hash_range_budget_ro_checked_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
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
    "hash_range_budget ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have trace_fri_range:
    "hash_range_budget ?trace_fri
      (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len: "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_range_budget
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          2 * ceil_log clength)
        (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_range_budget_ro_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final_range:
    "\<And>bs. hash_range_budget ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have alpha_range:
    "hash_range_budget ?alpha (ro_staged_alpha_program (length spec))"
    by (rule hash_range_budget_ro_staged_alpha_program)
  have degree_range:
    "\<And>as. hash_range_budget ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have composition_fri_range:
    "\<And>dg. hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_range_budget_guarded_ro_staged_composition_fri_program
        [OF wf controlled])
  have composition_final_range:
    "\<And>dg bs. hash_range_budget ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have query_range:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list).
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_range_budget ?query
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
      "hash_range_budget
        (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
          rounds + rounds * ro_checked_query_round_transcript_bound)
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      by (rule hash_range_budget_ro_checked_staged_query_program_closed
          [OF controlled len trace_len composition_len])
    then show
      "hash_range_budget ?query
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have query_tail:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list) F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_range_budget (?query + 0)
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds \<bind>
          (\<lambda>query_chunks. return (F query_chunks)))"
    by (rule hash_range_budget_bind)
      (rule query_range, assumption, assumption, rule hash_range_budget_return)
  have after_composition_final_record:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list) composition_final F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_range_budget (1 + (?query + 0))
        (ro_record_staged_message composition_final \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots 0 rounds \<bind>
            (\<lambda>query_chunks. return (F query_chunks))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_record_staged_message,
        rule query_tail, assumption, assumption)
  have after_composition_final:
    "\<And>(trace_roots :: 'f list) dg (composition_roots :: 'f list) bs F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_range_budget (?composition_final + (1 + (?query + 0)))
        (composition_final_stage A dg bs \<bind>
          (\<lambda>composition_final.
            ro_record_staged_message composition_final \<bind>
              (\<lambda>_. ro_checked_staged_query_program A trace_roots
                composition_roots 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return (F composition_final query_chunks)))))"
    by (rule hash_range_budget_bind)
      (rule composition_final_range, rule after_composition_final_record,
        assumption, assumption)
  have after_composition_fri:
    "\<And>(trace_roots :: 'f list) dg F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_range_budget
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
  proof (rule hash_range_budget_bind_on_outcomes)
    fix trace_roots :: "'f list"
    fix dg F
    show "hash_range_budget ?composition_fri
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
    show "hash_range_budget (?composition_final + (1 + (?query + 0)))
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
      have "hash_range_budget (?composition_final + (1 + (?query + 0)))
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
      hash_range_budget
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
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_record_staged_message,
        rule after_composition_fri, assumption)
  have after_degree:
    "\<And>(trace_roots :: 'f list) as F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_range_budget
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
    by (rule hash_range_budget_bind)
      (rule degree_range, rule after_degree_record, assumption)
  have after_alpha:
    "\<And>(trace_roots :: 'f list) F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_range_budget
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
    by (rule hash_range_budget_bind)
      (rule alpha_range, rule after_degree, assumption)
  have after_trace_final_record:
    "\<And>(trace_roots :: 'f list) trace_final F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_range_budget
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
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_record_staged_message,
        rule after_alpha, assumption)
  have after_trace_final:
    "\<And>(trace_roots :: 'f list) trace_bs F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_range_budget
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
    by (rule hash_range_budget_bind)
      (rule trace_final_range, rule after_trace_final_record, assumption)
  have after_trace_fri:
    "\<And>F. hash_range_budget
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
  proof (rule hash_range_budget_bind_on_outcomes)
    fix F
    show "hash_range_budget ?trace_fri
      (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_range)
  next
    fix F s x t
    assume out:
      "Some (x, t) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s)"
    show "hash_range_budget
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
      have "hash_range_budget
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
    "\<And>fr F. hash_range_budget
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
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_record_staged_message, rule after_trace_fri)
  have whole:
    "hash_range_budget
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
  proof (rule hash_range_budget_bind)
    show "hash_range_budget ?trace_root (trace_root_stage A)"
      by (rule trace_root_range)
  next
    fix fr
    show "hash_range_budget
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

lemma hash_target_program_ro_checked_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
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
    "hash_target_program B ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have trace_fri_range:
    "hash_target_program B ?trace_fri
      (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len: "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_target_program B
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          2 * ceil_log clength)
        (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_target_program_ro_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final_range:
    "\<And>bs. hash_target_program B ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have alpha_range:
    "hash_target_program B ?alpha (ro_staged_alpha_program (length spec))"
    by (rule hash_target_program_ro_staged_alpha_program)
  have degree_range:
    "\<And>as. hash_target_program B ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have composition_fri_range:
    "\<And>dg. hash_target_program B ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_target_program_guarded_ro_staged_composition_fri_program
        [OF wf controlled])
  have composition_final_range:
    "\<And>dg bs. hash_target_program B ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have query_range:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list).
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_target_program B ?query
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
      "hash_target_program B
        (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
          rounds + rounds * ro_checked_query_round_transcript_bound)
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      by (rule hash_target_program_ro_checked_staged_query_program_closed
          [OF controlled len trace_len composition_len])
    then show
      "hash_target_program B ?query
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have query_tail:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list) F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_target_program B (?query + 0)
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds \<bind>
          (\<lambda>query_chunks. return (F query_chunks)))"
    by (rule hash_target_program_bind)
      (rule query_range, assumption, assumption, rule hash_target_program_return)
  have after_composition_final_record:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list) composition_final F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_target_program B (1 + (?query + 0))
        (ro_record_staged_message composition_final \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots 0 rounds \<bind>
            (\<lambda>query_chunks. return (F query_chunks))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_record_staged_message,
        rule query_tail, assumption, assumption)
  have after_composition_final:
    "\<And>(trace_roots :: 'f list) dg (composition_roots :: 'f list) bs F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_target_program B (?composition_final + (1 + (?query + 0)))
        (composition_final_stage A dg bs \<bind>
          (\<lambda>composition_final.
            ro_record_staged_message composition_final \<bind>
              (\<lambda>_. ro_checked_staged_query_program A trace_roots
                composition_roots 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return (F composition_final query_chunks)))))"
    by (rule hash_target_program_bind)
      (rule composition_final_range, rule after_composition_final_record,
        assumption, assumption)
  have after_composition_fri:
    "\<And>(trace_roots :: 'f list) dg F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_target_program B
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
  proof (rule hash_target_program_bind_on_outcomes)
    fix trace_roots :: "'f list"
    fix dg F
    show "hash_target_program B ?composition_fri
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
    show "hash_target_program B (?composition_final + (1 + (?query + 0)))
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
      have "hash_target_program B (?composition_final + (1 + (?query + 0)))
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
      hash_target_program B
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
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_record_staged_message,
        rule after_composition_fri, assumption)
  have after_degree:
    "\<And>(trace_roots :: 'f list) as F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_target_program B
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
    by (rule hash_target_program_bind)
      (rule degree_range, rule after_degree_record, assumption)
  have after_alpha:
    "\<And>(trace_roots :: 'f list) F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_target_program B
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
    by (rule hash_target_program_bind)
      (rule alpha_range, rule after_degree, assumption)
  have after_trace_final_record:
    "\<And>(trace_roots :: 'f list) trace_final F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_target_program B
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
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_record_staged_message,
        rule after_alpha, assumption)
  have after_trace_final:
    "\<And>(trace_roots :: 'f list) trace_bs F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_target_program B
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
    by (rule hash_target_program_bind)
      (rule trace_final_range, rule after_trace_final_record, assumption)
  have after_trace_fri:
    "\<And>F. hash_target_program B
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
  proof (rule hash_target_program_bind_on_outcomes)
    fix F
    show "hash_target_program B ?trace_fri
      (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_range)
  next
    fix F s x t
    assume out:
      "Some (x, t) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s)"
    show "hash_target_program B
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
      have "hash_target_program B
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
    "\<And>fr F. hash_target_program B
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
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_record_staged_message, rule after_trace_fri)
  have whole:
    "hash_target_program B
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
  proof (rule hash_target_program_bind)
    show "hash_target_program B ?trace_root (trace_root_stage A)"
      by (rule trace_root_range)
  next
    fix fr
    show "hash_target_program B
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

lemma hash_relation_program_ro_checked_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
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
    "hash_relation_program R b ?trace_root (trace_root_stage A)"
    using controlled fibers unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_relation)
  have trace_fri_range:
    "hash_relation_program R b ?trace_fri
      (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len: "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_relation_program R b
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          2 * ceil_log clength)
        (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_relation_program_ro_staged_trace_fri_program
          [OF controlled len fibers])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final_range:
    "\<And>bs. hash_relation_program R b ?trace_final (trace_final_stage A bs)"
    using controlled fibers unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_relation)
  have alpha_range:
    "hash_relation_program R b ?alpha (ro_staged_alpha_program (length spec))"
    by (rule hash_relation_program_ro_staged_alpha_program[OF fibers])
  have degree_range:
    "\<And>as. hash_relation_program R b ?degree (degree_stage A as)"
    using controlled fibers unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_relation)
  have composition_fri_range:
    "\<And>dg. hash_relation_program R b ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_relation_program_guarded_ro_staged_composition_fri_program
        [OF wf controlled fibers])
  have composition_final_range:
    "\<And>dg bs. hash_relation_program R b ?composition_final
      (composition_final_stage A dg bs)"
    using controlled fibers unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_relation)
  have query_range:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list).
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_relation_program R b ?query
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
      "hash_relation_program R b
        (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
          rounds + rounds * ro_checked_query_round_transcript_bound)
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      by (rule hash_relation_program_ro_checked_staged_query_program_closed
          [OF controlled len fibers trace_len composition_len])
    then show
      "hash_relation_program R b ?query
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have query_tail:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list) F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_relation_program R b (?query + 0)
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds \<bind>
          (\<lambda>query_chunks. return (F query_chunks)))"
    by (rule hash_relation_program_bind)
      (rule query_range, assumption, assumption,
        rule hash_relation_program_zero[OF hash_map_preserving_return])
  have after_composition_final_record:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list) composition_final F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_relation_program R b (1 + (?query + 0))
        (ro_record_staged_message composition_final \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots 0 rounds \<bind>
            (\<lambda>query_chunks. return (F query_chunks))))"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_ro_record_staged_message[OF fibers],
        rule query_tail, assumption, assumption)
  have after_composition_final:
    "\<And>(trace_roots :: 'f list) dg (composition_roots :: 'f list) bs F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      hash_relation_program R b (?composition_final + (1 + (?query + 0)))
        (composition_final_stage A dg bs \<bind>
          (\<lambda>composition_final.
            ro_record_staged_message composition_final \<bind>
              (\<lambda>_. ro_checked_staged_query_program A trace_roots
                composition_roots 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return (F composition_final query_chunks)))))"
    by (rule hash_relation_program_bind)
      (rule composition_final_range, rule after_composition_final_record,
        assumption, assumption)
  have after_composition_fri:
    "\<And>(trace_roots :: 'f list) dg F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_relation_program R b
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
  proof (rule hash_relation_program_bind_on_outcomes)
    fix trace_roots :: "'f list"
    fix dg F
    show "hash_relation_program R b ?composition_fri
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
    show "hash_relation_program R b (?composition_final + (1 + (?query + 0)))
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
      have "hash_relation_program R b (?composition_final + (1 + (?query + 0)))
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
      hash_relation_program R b
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
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_ro_record_staged_message[OF fibers],
        rule after_composition_fri, assumption)
  have after_degree:
    "\<And>(trace_roots :: 'f list) as F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_relation_program R b
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
    by (rule hash_relation_program_bind)
      (rule degree_range, rule after_degree_record, assumption)
  have after_alpha:
    "\<And>(trace_roots :: 'f list) F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_relation_program R b
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
    by (rule hash_relation_program_bind)
      (rule alpha_range, rule after_degree, assumption)
  have after_trace_final_record:
    "\<And>(trace_roots :: 'f list) trace_final F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_relation_program R b
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
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_ro_record_staged_message[OF fibers],
        rule after_alpha, assumption)
  have after_trace_final:
    "\<And>(trace_roots :: 'f list) trace_bs F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      hash_relation_program R b
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
    by (rule hash_relation_program_bind)
      (rule trace_final_range, rule after_trace_final_record, assumption)
  have after_trace_fri:
    "\<And>F. hash_relation_program R b
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
  proof (rule hash_relation_program_bind_on_outcomes)
    fix F
    show "hash_relation_program R b ?trace_fri
      (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_range)
  next
    fix F s x t
    assume out:
      "Some (x, t) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s)"
    show "hash_relation_program R b
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
      have "hash_relation_program R b
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
    "\<And>fr F. hash_relation_program R b
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
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_ro_record_staged_message[OF fibers], rule after_trace_fri)
  have whole:
    "hash_relation_program R b
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
  proof (rule hash_relation_program_bind)
    show "hash_relation_program R b ?trace_root (trace_root_stage A)"
      by (rule trace_root_range)
  next
    fix fr
    show "hash_relation_program R b
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
