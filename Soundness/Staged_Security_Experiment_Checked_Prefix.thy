(*  Title:      Stark/Staged_Security_Experiment_Checked_Prefix.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Checked_Prefix
  imports Staged_Security_Experiment_Targets
begin

text \<open>Checked staged-prefix replay, alignment, and transcript extraction lemmas.\<close>

context soundness
begin

lemma hash_relation_program_checked_staged_query_challenge_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (staged_query_search_queries budgets i)
      (checked_staged_query_challenge_prefix_program A i)"
proof -
  let ?alpha_prefix = "staged_alpha_search_queries budgets 0"
  let ?alpha = "length spec"
  let ?degree = "degree_budget budgets"
  let ?composition_fri =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  let ?query = "sum_list (take i (query_opening_budgets budgets)) + i"
  have alpha_prefix:
    "hash_relation_program R b ?alpha_prefix
      (staged_alpha_prefix_program A)"
    by (rule hash_relation_program_staged_alpha_prefix_program
        [OF wf controlled fibers])
  have alpha:
    "hash_relation_program R b ?alpha
      (staged_alpha_program (length spec))"
    by (rule hash_relation_program_staged_alpha_program[OF fibers])
  have degree:
    "\<And>as. hash_relation_program R b ?degree (degree_stage A as)"
  proof -
    fix as
    have controlled_degree:
      "controlled_ro_program ?degree (degree_stage A as)"
      using controlled unfolding staged_adversary_controlled_def by blast
    show "hash_relation_program R b ?degree (degree_stage A as)"
      by (rule controlled_ro_program_relation
          [OF controlled_degree fibers])
  qed
  have composition_fri:
    "\<And>dg. hash_relation_program R b ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_relation_program_guarded_staged_composition_fri_program
        [OF wf controlled fibers])
  have composition_final:
    "\<And>dg composition_bs. hash_relation_program R b ?composition_final
      (composition_final_stage A dg composition_bs)"
  proof -
    fix dg composition_bs
    have controlled_final:
      "controlled_ro_program ?composition_final
        (composition_final_stage A dg composition_bs)"
      using controlled unfolding staged_adversary_controlled_def by blast
    show "hash_relation_program R b ?composition_final
      (composition_final_stage A dg composition_bs)"
      by (rule controlled_ro_program_relation
          [OF controlled_final fibers])
  qed
  have query:
    "\<And>trace_roots composition_roots.
      hash_relation_program R b ?query
        (checked_staged_query_program A trace_roots composition_roots 0 i)"
  proof -
    fix trace_roots composition_roots
    have len: "0 + i \<le> length (query_opening_budgets budgets)"
      using wf i_bound unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_relation_program R b
        (sum_list (take i (drop 0 (query_opening_budgets budgets))) + i)
        (checked_staged_query_program A trace_roots composition_roots 0 i)"
      by (rule hash_relation_program_checked_staged_query_program
          [OF controlled len fibers])
    then show "hash_relation_program R b ?query
        (checked_staged_query_program A trace_roots composition_roots 0 i)"
      by simp
  qed
  have after_query:
    "\<And>fr trace_roots trace_bs trace_final as dg composition_roots
        composition_bs composition_final.
      hash_relation_program R b (?query + 0)
        (checked_staged_query_program A trace_roots composition_roots 0 i \<bind>
          (\<lambda>query_chunks. return
            \<lparr>sqp_trace_root = fr,
             sqp_trace_fri_roots = trace_roots,
             sqp_trace_fri_challenges = trace_bs,
             sqp_trace_final = trace_final,
             sqp_alphas = as,
             sqp_degree = dg,
             sqp_composition_fri_roots = composition_roots,
             sqp_composition_fri_challenges = composition_bs,
             sqp_composition_final = composition_final,
             sqp_query_chunks = query_chunks\<rparr>))"
    by (rule hash_relation_program_bind)
      (rule query,
        rule hash_relation_program_zero[OF hash_map_preserving_return])
  have after_composition_final_record:
    "\<And>fr trace_roots trace_bs trace_final as dg composition_roots
        composition_bs composition_final.
      hash_relation_program R b (0 + (?query + 0))
        (record_staged_message composition_final \<bind>
          (\<lambda>_. checked_staged_query_program A trace_roots
            composition_roots 0 i \<bind>
            (\<lambda>query_chunks. return
              \<lparr>sqp_trace_root = fr,
               sqp_trace_fri_roots = trace_roots,
               sqp_trace_fri_challenges = trace_bs,
               sqp_trace_final = trace_final,
               sqp_alphas = as,
               sqp_degree = dg,
               sqp_composition_fri_roots = composition_roots,
               sqp_composition_fri_challenges = composition_bs,
               sqp_composition_final = composition_final,
               sqp_query_chunks = query_chunks\<rparr>)))"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_record_staged_message, rule after_query)
  have after_composition_final:
    "\<And>fr trace_roots trace_bs trace_final as dg composition_roots
        composition_bs.
      hash_relation_program R b
        (?composition_final + (0 + (?query + 0)))
        (composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. checked_staged_query_program A trace_roots
                composition_roots 0 i \<bind>
                (\<lambda>query_chunks. return
                  \<lparr>sqp_trace_root = fr,
                   sqp_trace_fri_roots = trace_roots,
                   sqp_trace_fri_challenges = trace_bs,
                   sqp_trace_final = trace_final,
                   sqp_alphas = as,
                   sqp_degree = dg,
                   sqp_composition_fri_roots = composition_roots,
                   sqp_composition_fri_challenges = composition_bs,
                   sqp_composition_final = composition_final,
                   sqp_query_chunks = query_chunks\<rparr>))))"
    by (rule hash_relation_program_bind)
      (rule composition_final, rule after_composition_final_record)
  have after_composition_fri:
    "\<And>fr trace_roots trace_bs trace_final as dg.
      hash_relation_program R b
        (?composition_fri +
          (?composition_final + (0 + (?query + 0))))
        ((assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [])) \<bind>
          (\<lambda>(composition_roots, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. checked_staged_query_program A trace_roots
                    composition_roots 0 i \<bind>
                    (\<lambda>query_chunks. return
                      \<lparr>sqp_trace_root = fr,
                       sqp_trace_fri_roots = trace_roots,
                       sqp_trace_fri_challenges = trace_bs,
                       sqp_trace_final = trace_final,
                       sqp_alphas = as,
                       sqp_degree = dg,
                       sqp_composition_fri_roots = composition_roots,
                       sqp_composition_fri_challenges = composition_bs,
                       sqp_composition_final = composition_final,
                       sqp_query_chunks = query_chunks\<rparr>)))))"
  proof -
    fix fr trace_roots trace_bs trace_final as dg
    have cont:
      "\<And>x. hash_relation_program R b
        (?composition_final + (0 + (?query + 0)))
        (case x of (composition_roots, composition_bs) \<Rightarrow>
          composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. checked_staged_query_program A trace_roots
                  composition_roots 0 i \<bind>
                  (\<lambda>query_chunks. return
                    \<lparr>sqp_trace_root = fr,
                     sqp_trace_fri_roots = trace_roots,
                     sqp_trace_fri_challenges = trace_bs,
                     sqp_trace_final = trace_final,
                     sqp_alphas = as,
                     sqp_degree = dg,
                     sqp_composition_fri_roots = composition_roots,
                     sqp_composition_fri_challenges = composition_bs,
                     sqp_composition_final = composition_final,
                     sqp_query_chunks = query_chunks\<rparr>))))"
    proof -
      fix x
      show "hash_relation_program R b
        (?composition_final + (0 + (?query + 0)))
        (case x of (composition_roots, composition_bs) \<Rightarrow>
          composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. checked_staged_query_program A trace_roots
                  composition_roots 0 i \<bind>
                  (\<lambda>query_chunks. return
                    \<lparr>sqp_trace_root = fr,
                     sqp_trace_fri_roots = trace_roots,
                     sqp_trace_fri_challenges = trace_bs,
                     sqp_trace_final = trace_final,
                     sqp_alphas = as,
                     sqp_degree = dg,
                     sqp_composition_fri_roots = composition_roots,
                     sqp_composition_fri_challenges = composition_bs,
                     sqp_composition_final = composition_final,
                     sqp_query_chunks = query_chunks\<rparr>))))"
      proof (cases x)
        case (Pair composition_roots composition_bs)
        have step:
          "hash_relation_program R b
            (?composition_final + (0 + (?query + 0)))
            (composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. checked_staged_query_program A trace_roots
                    composition_roots 0 i \<bind>
                    (\<lambda>query_chunks. return
                      \<lparr>sqp_trace_root = fr,
                       sqp_trace_fri_roots = trace_roots,
                       sqp_trace_fri_challenges = trace_bs,
                       sqp_trace_final = trace_final,
                       sqp_alphas = as,
                       sqp_degree = dg,
                       sqp_composition_fri_roots = composition_roots,
                       sqp_composition_fri_challenges = composition_bs,
                       sqp_composition_final = composition_final,
                       sqp_query_chunks = query_chunks\<rparr>))))"
          by (rule after_composition_final)
        show ?thesis
          unfolding Pair using step by simp
      qed
    qed
    show "hash_relation_program R b
        (?composition_fri +
          (?composition_final + (0 + (?query + 0))))
        ((assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [])) \<bind>
          (\<lambda>(composition_roots, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. checked_staged_query_program A trace_roots
                    composition_roots 0 i \<bind>
                    (\<lambda>query_chunks. return
                      \<lparr>sqp_trace_root = fr,
                       sqp_trace_fri_roots = trace_roots,
                       sqp_trace_fri_challenges = trace_bs,
                       sqp_trace_final = trace_final,
                       sqp_alphas = as,
                       sqp_degree = dg,
                       sqp_composition_fri_roots = composition_roots,
                       sqp_composition_fri_challenges = composition_bs,
                       sqp_composition_final = composition_final,
                       sqp_query_chunks = query_chunks\<rparr>)))))"
      by (rule hash_relation_program_bind)
        (rule composition_fri, rule cont)
  qed
  have after_degree_record:
    "\<And>fr trace_roots trace_bs trace_final as dg.
      hash_relation_program R b
        (0 + (?composition_fri +
          (?composition_final + (0 + (?query + 0)))))
        (record_staged_message dg \<bind>
          (\<lambda>_. (assert
            (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])) \<bind>
            (\<lambda>(composition_roots, composition_bs).
              composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  record_staged_message composition_final \<bind>
                    (\<lambda>_. checked_staged_query_program A trace_roots
                      composition_roots 0 i \<bind>
                      (\<lambda>query_chunks. return
                        \<lparr>sqp_trace_root = fr,
                         sqp_trace_fri_roots = trace_roots,
                         sqp_trace_fri_challenges = trace_bs,
                         sqp_trace_final = trace_final,
                         sqp_alphas = as,
                         sqp_degree = dg,
                         sqp_composition_fri_roots = composition_roots,
                         sqp_composition_fri_challenges = composition_bs,
                         sqp_composition_final = composition_final,
                         sqp_query_chunks = query_chunks\<rparr>))))))"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_record_staged_message,
        rule after_composition_fri)
  have after_degree:
    "\<And>fr trace_roots trace_bs trace_final as.
      hash_relation_program R b
        (?degree + (0 + (?composition_fri +
          (?composition_final + (0 + (?query + 0))))))
        (degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
              assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                composition_rounds [] \<bind>
                (\<lambda>(composition_roots, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                      (\<lambda>_. checked_staged_query_program A trace_roots
                        composition_roots 0 i \<bind>
                        (\<lambda>query_chunks. return
                          \<lparr>sqp_trace_root = fr,
                           sqp_trace_fri_roots = trace_roots,
                           sqp_trace_fri_challenges = trace_bs,
                           sqp_trace_final = trace_final,
                           sqp_alphas = as,
                           sqp_degree = dg,
                           sqp_composition_fri_roots = composition_roots,
                           sqp_composition_fri_challenges = composition_bs,
                           sqp_composition_final = composition_final,
                           sqp_query_chunks = query_chunks\<rparr>))))))))"
  proof -
    fix fr trace_roots trace_bs trace_final as
    have cont:
      "\<And>dg. hash_relation_program R b
        (0 + (?composition_fri +
          (?composition_final + (0 + (?query + 0)))))
        (record_staged_message dg \<bind>
          (\<lambda>_. assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [] \<bind>
              (\<lambda>(composition_roots, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                    (\<lambda>_. checked_staged_query_program A trace_roots
                      composition_roots 0 i \<bind>
                      (\<lambda>query_chunks. return
                        \<lparr>sqp_trace_root = fr,
                         sqp_trace_fri_roots = trace_roots,
                         sqp_trace_fri_challenges = trace_bs,
                         sqp_trace_final = trace_final,
                         sqp_alphas = as,
                         sqp_degree = dg,
                         sqp_composition_fri_roots = composition_roots,
                         sqp_composition_fri_challenges = composition_bs,
                         sqp_composition_final = composition_final,
                         sqp_query_chunks = query_chunks\<rparr>)))))))"
    proof -
      fix dg
      have step:
        "hash_relation_program R b
          (0 + (?composition_fri +
            (?composition_final + (0 + (?query + 0)))))
          (record_staged_message dg \<bind>
            (\<lambda>_. (assert
              (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                (ceil_log (to_nat dg + 1)) [])) \<bind>
              (\<lambda>(composition_roots, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                    (\<lambda>_. checked_staged_query_program A trace_roots
                      composition_roots 0 i \<bind>
                      (\<lambda>query_chunks. return
                        \<lparr>sqp_trace_root = fr,
                         sqp_trace_fri_roots = trace_roots,
                         sqp_trace_fri_challenges = trace_bs,
                         sqp_trace_final = trace_final,
                         sqp_alphas = as,
                         sqp_degree = dg,
                         sqp_composition_fri_roots = composition_roots,
                         sqp_composition_fri_challenges = composition_bs,
                         sqp_composition_final = composition_final,
                         sqp_query_chunks = query_chunks\<rparr>))))))"
        by (rule after_degree_record)
      show "hash_relation_program R b
        (0 + (?composition_fri +
          (?composition_final + (0 + (?query + 0)))))
        (record_staged_message dg \<bind>
          (\<lambda>_. assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [] \<bind>
              (\<lambda>(composition_roots, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                    (\<lambda>_. checked_staged_query_program A trace_roots
                      composition_roots 0 i \<bind>
                      (\<lambda>query_chunks. return
                        \<lparr>sqp_trace_root = fr,
                         sqp_trace_fri_roots = trace_roots,
                         sqp_trace_fri_challenges = trace_bs,
                         sqp_trace_final = trace_final,
                         sqp_alphas = as,
                         sqp_degree = dg,
                         sqp_composition_fri_roots = composition_roots,
                         sqp_composition_fri_challenges = composition_bs,
                         sqp_composition_final = composition_final,
                         sqp_query_chunks = query_chunks\<rparr>)))))))"
        using step by (simp add: sm_bind_assoc)
    qed
    show "hash_relation_program R b
        (?degree + (0 + (?composition_fri +
          (?composition_final + (0 + (?query + 0))))))
        (degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
              assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                composition_rounds [] \<bind>
                (\<lambda>(composition_roots, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                      (\<lambda>_. checked_staged_query_program A trace_roots
                        composition_roots 0 i \<bind>
                        (\<lambda>query_chunks. return
                          \<lparr>sqp_trace_root = fr,
                           sqp_trace_fri_roots = trace_roots,
                           sqp_trace_fri_challenges = trace_bs,
                           sqp_trace_final = trace_final,
                           sqp_alphas = as,
                           sqp_degree = dg,
                           sqp_composition_fri_roots = composition_roots,
                           sqp_composition_fri_challenges = composition_bs,
                           sqp_composition_final = composition_final,
                           sqp_query_chunks = query_chunks\<rparr>))))))))"
      unfolding Let_def
      by (rule hash_relation_program_bind)
        (rule degree, rule cont)
  qed
  have after_alpha:
    "\<And>fr trace_roots trace_bs trace_final.
      hash_relation_program R b
        (?alpha + (?degree + (0 + (?composition_fri +
          (?composition_final + (0 + (?query + 0)))))))
        (staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
                assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  composition_rounds [] \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                        (\<lambda>_. checked_staged_query_program A trace_roots
                          composition_roots 0 i \<bind>
                          (\<lambda>query_chunks. return
                            \<lparr>sqp_trace_root = fr,
                             sqp_trace_fri_roots = trace_roots,
                             sqp_trace_fri_challenges = trace_bs,
                             sqp_trace_final = trace_final,
                             sqp_alphas = as,
                             sqp_degree = dg,
                             sqp_composition_fri_roots = composition_roots,
                             sqp_composition_fri_challenges = composition_bs,
                             sqp_composition_final = composition_final,
                             sqp_query_chunks = query_chunks\<rparr>)))))))))"
    by (rule hash_relation_program_bind)
      (rule alpha, rule after_degree)
  have after_alpha_prefix:
    "hash_relation_program R b
      (?alpha_prefix +
        (?alpha + (?degree + (0 + (?composition_fri +
          (?composition_final + (0 + (?query + 0))))))))
      (checked_staged_query_challenge_prefix_program A i)"
    unfolding checked_staged_query_challenge_prefix_program_def
  proof (rule hash_relation_program_bind)
    show "hash_relation_program R b ?alpha_prefix
      (staged_alpha_prefix_program A)"
      by (rule alpha_prefix)
  next
    fix x
    show "hash_relation_program R b
      (?alpha + (?degree + (0 + (?composition_fri +
        (?composition_final + (0 + (?query + 0)))))))
      (case x of (fr, trace_roots, trace_bs, trace_final) \<Rightarrow>
        staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
                assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  composition_rounds [] \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                        (\<lambda>_. checked_staged_query_program A trace_roots
                          composition_roots 0 i \<bind>
                          (\<lambda>query_chunks. return
                            \<lparr>sqp_trace_root = fr,
                             sqp_trace_fri_roots = trace_roots,
                             sqp_trace_fri_challenges = trace_bs,
                             sqp_trace_final = trace_final,
                             sqp_alphas = as,
                             sqp_degree = dg,
                             sqp_composition_fri_roots = composition_roots,
                             sqp_composition_fri_challenges = composition_bs,
                             sqp_composition_final = composition_final,
                             sqp_query_chunks = query_chunks\<rparr>)))))))))"
    proof (cases x)
      case (fields fr trace_roots trace_bs trace_final)
      have step:
        "hash_relation_program R b
          (?alpha + (?degree + (0 + (?composition_fri +
            (?composition_final + (0 + (?query + 0)))))))
          (staged_alpha_program (length spec) \<bind>
            (\<lambda>as. degree_stage A as \<bind>
              (\<lambda>dg. record_staged_message dg \<bind>
                (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
                  assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_. staged_composition_fri_program A dg 0
                    composition_rounds [] \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                          (\<lambda>_. checked_staged_query_program A trace_roots
                            composition_roots 0 i \<bind>
                            (\<lambda>query_chunks. return
                              \<lparr>sqp_trace_root = fr,
                               sqp_trace_fri_roots = trace_roots,
                               sqp_trace_fri_challenges = trace_bs,
                               sqp_trace_final = trace_final,
                               sqp_alphas = as,
                               sqp_degree = dg,
                               sqp_composition_fri_roots = composition_roots,
                               sqp_composition_fri_challenges = composition_bs,
                               sqp_composition_final = composition_final,
                               sqp_query_chunks = query_chunks\<rparr>)))))))))"
        by (rule after_alpha)
      show ?thesis
        unfolding fields using step by simp
    qed
  qed
  show ?thesis
    using after_alpha_prefix
    unfolding staged_query_search_queries_def
      staged_alpha_search_queries_def
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma staged_trace_fri_program_challenge_prefix_pre_alignment:
  assumes outcome:
    "Some ((roots, bs'), t) \<in>
      set_dist (execute (staged_trace_fri_program A i n bs) s)"
  shows "take (length bs) bs' = bs"
  using outcome
proof (induction n arbitrary: i bs roots bs' s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain root b roots' s1 s2 s3 where
    rest_out:
      "Some ((roots', bs'), t) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A (Suc i) n (bs @ [b])) s3)"
    unfolding staged_trace_fri_program.simps
    by (auto elim!: set_dist_bindE)
  have prefix_suc:
    "take (length (bs @ [b])) bs' = bs @ [b]"
    by (rule Suc.IH[OF rest_out])
  have "take (length bs) bs' =
      take (length bs) (take (length (bs @ [b])) bs')"
    by simp
  also have "... = bs"
    using prefix_suc by simp
  finally show ?case .
qed

lemma staged_trace_fri_program_alignment:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
    and outcome:
      "Some ((roots, bs'), t) \<in>
        set_dist (execute (staged_trace_fri_program A i n bs) s)"
  shows
    "length roots = n \<and>
     length bs' = length bs + n \<and>
     PTranscript t = PTranscript s @ roots \<and>
     PState t = foldl concat (PState s) roots \<and>
     s \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s + n \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s \<and>
     (\<forall>j < n.
        fmlookup (HashMap t)
          (TraceFriChallenge (PTraceFriCounter s + j)
            (foldl concat (PState s) (take (Suc j) roots))) =
        Some (bs' ! (length bs + j)))"
  using bound outcome
proof (induction n arbitrary: i bs roots bs' s t)
  case 0
  then show ?case by (simp add: hash_ext_refl)
next
  case (Suc n)
  from staged_trace_fri_program_Suc_outcomeE[OF Suc.prems(2)]
  obtain root b roots' s1 s2 s3 where
    stage_out:
      "Some (root, s1) \<in>
        set_dist (execute (trace_fri_root_stage A i bs) s)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in>
        set_dist (execute receive_trace_fri_challenge s2)"
    and rest_out:
      "Some ((roots', bs'), t) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A (Suc i) n (bs @ [b])) s3)"
    and roots_eq: "roots = root # roots'"
    .
  have i_bound: "i < length (trace_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have stage_fields:
    "PState s1 = PState s \<and>
     PTranscript s1 = PTranscript s \<and>
     PTraceFriCounter s1 = PTraceFriCounter s \<and>
     PCompositionFriCounter s1 = PCompositionFriCounter s \<and>
     PAlphaCounter s1 = PAlphaCounter s \<and>
     PQueryCounter s1 = PQueryCounter s"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have ext_s_s1: "s \<le> s1"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have s2:
    "s2 = s1\<lparr>
      PState := concat (PState s1) root,
      PTranscript := PTranscript s1 @ [root]\<rparr>"
    by (rule record_staged_message_outcome[OF record_out])
  have ext_s1_s2: "s1 \<le> s2"
    unfolding s2 less_eq_hash_ext_def less_eq_fmap_def by simp
  have s2_fields:
    "PState s2 = concat (PState s) root \<and>
     PTranscript s2 = PTranscript s @ [root] \<and>
     PTraceFriCounter s2 = PTraceFriCounter s \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s \<and>
     PAlphaCounter s2 = PAlphaCounter s \<and>
     PQueryCounter s2 = PQueryCounter s"
    unfolding s2 using stage_fields by simp
  have challenge_fields:
    "PState s3 = PState s2 \<and>
     PTranscript s3 = PTranscript s2"
    using receive_trace_fri_challenge_outcome[OF challenge_out] by simp
  have ext_s2_s3: "s2 \<le> s3"
    using receive_trace_fri_challenge_outcome[OF challenge_out] by simp
  have challenge_counters:
    "PTraceFriCounter s3 = Suc (PTraceFriCounter s2) \<and>
     PCompositionFriCounter s3 = PCompositionFriCounter s2 \<and>
     PAlphaCounter s3 = PAlphaCounter s2 \<and>
     PQueryCounter s3 = PQueryCounter s2"
    using receive_trace_fri_challenge_counter_outcome[OF challenge_out] by simp
  have rest_bound:
    "Suc i + n \<le> length (trace_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have rest_alignment:
    "length roots' = n \<and>
     length bs' = length (bs @ [b]) + n \<and>
     PTranscript t = PTranscript s3 @ roots' \<and>
     PState t = foldl concat (PState s3) roots' \<and>
     s3 \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s3 + n \<and>
     PCompositionFriCounter t = PCompositionFriCounter s3 \<and>
     PAlphaCounter t = PAlphaCounter s3 \<and>
     PQueryCounter t = PQueryCounter s3 \<and>
     (\<forall>j < n.
        fmlookup (HashMap t)
          (TraceFriChallenge (PTraceFriCounter s3 + j)
            (foldl concat (PState s3) (take (Suc j) roots'))) =
        Some (bs' ! (length (bs @ [b]) + j)))"
    by (rule Suc.IH[OF rest_bound rest_out])
  have ext_s3_t: "s3 \<le> t"
    using rest_alignment by simp
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_s1])
      (rule hash_ext_trans[OF ext_s1_s2],
        rule hash_ext_trans[OF ext_s2_s3 ext_s3_t])
  have challenge_lookup_s3:
    "fmlookup (HashMap s3)
      (TraceFriChallenge (PTraceFriCounter s)
        (concat (PState s) root)) = Some b"
    using receive_trace_fri_challenge_outcome[OF challenge_out]
      s2_fields by simp
  have challenge_lookup_t:
    "fmlookup (HashMap t)
      (TraceFriChallenge (PTraceFriCounter s)
        (concat (PState s) root)) = Some b"
    by (rule hash_extension_lookup[OF challenge_lookup_s3 ext_s3_t])
  have prefix_suc:
    "take (length (bs @ [b])) bs' = bs @ [b]"
    by (rule staged_trace_fri_program_challenge_prefix_pre_alignment
        [OF rest_out])
  have lookup_all:
    "\<forall>j < Suc n.
      fmlookup (HashMap t)
        (TraceFriChallenge (PTraceFriCounter s + j)
          (foldl concat (PState s) (take (Suc j) (root # roots')))) =
      Some (bs' ! (length bs + j))"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show
      "fmlookup (HashMap t)
        (TraceFriChallenge (PTraceFriCounter s + j)
          (foldl concat (PState s) (take (Suc j) (root # roots')))) =
      Some (bs' ! (length bs + j))"
    proof (cases j)
      case 0
      have "bs' ! length bs = b"
      proof -
        have idx_lt: "length bs < length (bs @ [b])"
          by simp
        have "bs' ! length bs =
            take (length (bs @ [b])) bs' ! length bs"
          using idx_lt by simp
        also have "... = (bs @ [b]) ! length bs"
          using prefix_suc by simp
        also have "... = b"
          by simp
        finally show ?thesis .
      qed
      then show ?thesis
        using challenge_lookup_t unfolding 0 by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      show ?thesis
        using rest_alignment k_bound s2_fields challenge_fields
          challenge_counters
        unfolding Suc
        by simp
    qed
  qed
  show ?case
    unfolding roots_eq
    using s2_fields challenge_fields challenge_counters rest_alignment
      ext_s_t lookup_all
    by simp
qed

lemma staged_trace_fri_program_challenge_prefix:
  assumes outcome:
    "Some ((roots, bs'), t) \<in>
      set_dist (execute (staged_trace_fri_program A i n bs) s)"
  shows "take (length bs) bs' = bs"
  using outcome
proof (induction n arbitrary: i bs roots bs' s t)
  case 0
  then show ?case by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain root b roots' s1 s2 s3 where
    rest_out:
      "Some ((roots', bs'), t) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A (Suc i) n (bs @ [b])) s3)"
    unfolding staged_trace_fri_program.simps
    by (auto elim!: set_dist_bindE)
  have prefix_suc:
    "take (length (bs @ [b])) bs' = bs @ [b]"
    by (rule Suc.IH[OF rest_out])
  have "take (length bs) bs' =
      take (length bs) (take (length (bs @ [b])) bs')"
    by simp
  also have "... = bs"
    using prefix_suc by simp
  finally show ?case .
qed

lemma staged_trace_fri_program_challenge_length:
  assumes outcome:
    "Some ((roots, bs'), t) \<in>
      set_dist (execute (staged_trace_fri_program A i n bs) s)"
  shows "length bs' = length bs + n"
  using outcome
proof (induction n arbitrary: i bs roots bs' s t)
  case 0
  then show ?case by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain root b roots' s1 s2 s3 where
    rest_out:
      "Some ((roots', bs'), t) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A (Suc i) n (bs @ [b])) s3)"
    unfolding staged_trace_fri_program.simps
    by (auto elim!: set_dist_bindE)
  have "length bs' = length (bs @ [b]) + n"
    by (rule Suc.IH[OF rest_out])
  then show ?case by simp
qed

lemma staged_alpha_prefix_program_trace_challenge_length:
  assumes outcome:
    "Some ((fr, trace_roots, trace_bs, trace_final), t) \<in>
      set_dist (execute (staged_alpha_prefix_program A) s)"
  shows "length trace_bs = ceil_log clength"
proof -
  from outcome obtain s1 s2 s3 where
    fri_out:
      "Some ((trace_roots, trace_bs), s2) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A 0 (ceil_log clength) []) s1)"
    unfolding staged_alpha_prefix_program_def
    by (auto elim!: set_dist_bindE)
  have "length trace_bs = length ([] :: 'f list) + ceil_log clength"
    by (rule staged_trace_fri_program_challenge_length[OF fri_out])
  then show ?thesis by simp
qed

lemma staged_alpha_prefix_trace_vector_member_imp_position_value:
  assumes outcome:
    "Some ((fr, trace_roots, trace_bs, trace_final), t) \<in>
      set_dist (execute (staged_alpha_prefix_program A) s)"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and member: "trace_bs \<in> B"
    and i_bound: "i < ceil_log clength"
  shows "trace_bs ! i \<in> fri_vector_position_values B i"
  by (rule fri_vector_member_imp_position_value
      [OF subset member i_bound])

lemma staged_alpha_prefix_bad_trace_vector_coordinate_cover_bound:
  assumes subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event (staged_alpha_prefix_program A)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((_, _, trace_bs, _), _) \<Rightarrow> trace_bs \<in> B) s \<le>
      (\<Sum>i < ceil_log clength.
        wp_event (staged_alpha_prefix_program A)
          (\<lambda>out. case out of None \<Rightarrow> False
            | Some ((_, _, trace_bs, _), _) \<Rightarrow>
                trace_bs ! i \<in> fri_vector_position_values B i) s)"
proof -
  let ?bad =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some ((_, _, trace_bs, _), _) \<Rightarrow> trace_bs \<in> B"
  let ?coord =
    "\<lambda>i out. case out of None \<Rightarrow> False
      | Some ((_, _, trace_bs, _), _) \<Rightarrow>
          trace_bs ! i \<in> fri_vector_position_values B i"
  have bad_to_coord:
    "wp_event (staged_alpha_prefix_program A) ?bad s \<le>
      wp_event (staged_alpha_prefix_program A)
        (\<lambda>out. \<exists>i \<in> {..<ceil_log clength}. ?coord i out) s"
  proof (rule wp_event_mono)
    fix out
    assume bad: "?bad out"
    show "\<exists>i \<in> {..<ceil_log clength}. ?coord i out"
    proof (cases out)
      case None
      then show ?thesis using bad by simp
    next
      case (Some result)
      then obtain fr trace_roots trace_bs trace_final t where
        out_eq:
          "out = Some ((fr, trace_roots, trace_bs, trace_final), t)"
        by (cases result, auto split: prod.splits)
      have member: "trace_bs \<in> B"
        using bad unfolding out_eq by simp
      from fri_vector_member_coordinate_cover[OF subset member nonempty]
      obtain i where i_bound: "i < ceil_log clength"
        and coord: "trace_bs ! i \<in> fri_vector_position_values B i"
        by blast
      show ?thesis
        by (rule bexI[of _ i]) (use i_bound coord out_eq in simp_all)
    qed
  qed
  also have "... \<le>
      (\<Sum>i < ceil_log clength.
        wp_event (staged_alpha_prefix_program A) (?coord i) s)"
    by (rule wp_event_finite_UN_bound) simp_all
  finally show ?thesis .
qed

lemma staged_alpha_prefix_trace_coordinate_hit_imp_new_output_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log clength"
    and absent:
      "trace_fri_challenge_values_absent
        (fri_vector_position_values B i) s"
    and outcome:
      "Some ((fr, trace_roots, trace_bs, trace_final), t) \<in>
        set_dist (execute (staged_alpha_prefix_program A) s)"
    and hit: "trace_bs ! i \<in> fri_vector_position_values B i"
  shows
    "hash_new_output_hit_event (fri_vector_position_values B i) s
      (Some ((fr, trace_roots, trace_bs, trace_final), t))"
proof -
  from outcome obtain s1 s2 s3 s4 where
    root_out:
      "Some (fr, s1) \<in> set_dist (execute (trace_root_stage A) s)"
    and record_root:
      "Some ((), s2) \<in> set_dist (execute (record_staged_message fr) s1)"
    and fri_out:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and final_out:
      "Some (trace_final, s4) \<in>
        set_dist (execute (trace_final_stage A trace_bs) s3)"
    and record_final:
      "Some ((), t) \<in>
        set_dist (execute (record_staged_message trace_final) s4)"
    unfolding staged_alpha_prefix_program_def
    by (auto elim!: set_dist_bindE)
  have root_controlled:
    "controlled_ro_program (trace_root_budget budgets)
      (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def by simp
  have final_controlled:
    "controlled_ro_program (trace_final_budget budgets)
      (trace_final_stage A trace_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have ext_s_s1: "s \<le> s1"
    using controlled_ro_program_extension[OF root_controlled] root_out
    unfolding hash_extension_preserving_def by blast
  have s2_eq:
    "s2 = s1\<lparr>
      PState := concat (PState s1) fr,
      PTranscript := PTranscript s1 @ [fr]\<rparr>"
    by (rule record_staged_message_outcome[OF record_root])
  have ext_s1_s2: "s1 \<le> s2"
    unfolding s2_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have trace_bound:
    "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have trace_alignment:
    "length trace_roots = ceil_log clength \<and>
     length trace_bs = length ([] :: 'f list) + ceil_log clength \<and>
     PTranscript s3 = PTranscript s2 @ trace_roots \<and>
     PState s3 = foldl concat (PState s2) trace_roots \<and>
     s2 \<le> s3 \<and>
     PTraceFriCounter s3 = PTraceFriCounter s2 + ceil_log clength \<and>
     PCompositionFriCounter s3 = PCompositionFriCounter s2 \<and>
     PAlphaCounter s3 = PAlphaCounter s2 \<and>
     PQueryCounter s3 = PQueryCounter s2 \<and>
     (\<forall>j < ceil_log clength.
        fmlookup (HashMap s3)
          (TraceFriChallenge (PTraceFriCounter s2 + j)
            (foldl concat (PState s2) (take (Suc j) trace_roots))) =
        Some (trace_bs ! (length ([] :: 'f list) + j)))"
    by (rule staged_trace_fri_program_alignment
        [OF controlled trace_bound fri_out])
  let ?key =
    "TraceFriChallenge (PTraceFriCounter s2 + i)
      (foldl concat (PState s2) (take (Suc i) trace_roots))"
  have lookup_s3:
    "fmlookup (HashMap s3) ?key = Some (trace_bs ! i)"
    using trace_alignment i_bound by simp
  have ext_s_s3: "s \<le> s3"
    by (rule hash_ext_trans[OF ext_s_s1])
      (rule hash_ext_trans[OF ext_s1_s2], use trace_alignment in simp)
  have ext_s3_s4: "s3 \<le> s4"
    using controlled_ro_program_extension[OF final_controlled] final_out
    unfolding hash_extension_preserving_def by blast
  have t_eq:
    "t = s4\<lparr>
      PState := concat (PState s4) trace_final,
      PTranscript := PTranscript s4 @ [trace_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_final])
  have ext_s4_t: "s4 \<le> t"
    unfolding t_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have ext_s3_t: "s3 \<le> t"
    by (rule hash_ext_trans[OF ext_s3_s4 ext_s4_t])
  have lookup_t:
    "fmlookup (HashMap t) ?key = Some (trace_bs ! i)"
    by (rule hash_extension_lookup[OF lookup_s3 ext_s3_t])
  have none_s: "fmlookup (HashMap s) ?key = None"
  proof (cases "fmlookup (HashMap s) ?key")
    case None
    then show ?thesis .
  next
    case (Some old)
    have lookup_s3_old: "fmlookup (HashMap s3) ?key = Some old"
      by (rule hash_extension_lookup[OF Some ext_s_s3])
    then have old_eq: "old = trace_bs ! i"
      using lookup_s3 by simp
    have "old \<notin> fri_vector_position_values B i"
      using absent Some
      unfolding trace_fri_challenge_values_absent_def by blast
    then show ?thesis
      using old_eq hit by simp
  qed
  have "hash_map_new_output_hit (fri_vector_position_values B i) s t"
    unfolding hash_map_new_output_hit_def
    using none_s lookup_t hit by blast
  then show ?thesis
    unfolding hash_new_output_hit_event_def by simp
qed

lemma staged_alpha_prefix_trace_coordinate_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log clength"
    and absent:
      "trace_fri_challenge_values_absent
        (fri_vector_position_values B i) s"
  shows
    "wp_event (staged_alpha_prefix_program A)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((_, _, trace_bs, _), _) \<Rightarrow>
            trace_bs ! i \<in> fri_vector_position_values B i) s \<le>
      staged_phase_target_error (fri_vector_position_values B i)
        (staged_alpha_search_queries budgets 0)"
proof -
  let ?P =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some ((_, _, trace_bs, _), _) \<Rightarrow>
          trace_bs ! i \<in> fri_vector_position_values B i"
  let ?H =
    "hash_new_output_hit_event (fri_vector_position_values B i) s"
  have event_imp_hit:
    "wp_event (staged_alpha_prefix_program A) ?P s \<le>
      wp_event (staged_alpha_prefix_program A) ?H s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute (staged_alpha_prefix_program A) s)"
      and event: "?P out"
    show "?H out"
    proof (cases out)
      case None
      then show ?thesis using event by simp
    next
      case (Some result)
      then obtain fr trace_roots trace_bs trace_final t where
        out_eq:
          "out = Some ((fr, trace_roots, trace_bs, trace_final), t)"
        by (cases result, auto split: prod.splits)
      have outcome:
        "Some ((fr, trace_roots, trace_bs, trace_final), t) \<in>
          set_dist (execute (staged_alpha_prefix_program A) s)"
        using support unfolding out_eq .
      have hit: "trace_bs ! i \<in> fri_vector_position_values B i"
        using event unfolding out_eq by simp
      show ?thesis
        unfolding out_eq
        by (rule
            staged_alpha_prefix_trace_coordinate_hit_imp_new_output_hit
            [OF wf controlled i_bound absent outcome hit])
    qed
  qed
  also have
    "wp_event (staged_alpha_prefix_program A) ?H s \<le>
      staged_phase_target_error (fri_vector_position_values B i)
        (staged_alpha_search_queries budgets 0)"
    by (rule staged_alpha_prefix_target_hit_bound[OF wf controlled])
  finally show ?thesis .
qed

lemma staged_trace_fri_challenge_prefix_program_length:
  assumes outcome:
    "Some ((fr, trace_bs, rt), t) \<in>
      set_dist
        (execute (staged_trace_fri_challenge_prefix_program A i) s)"
  shows "length trace_bs = i"
proof -
  from outcome obtain roots pre_state post_state where
    fri_out:
      "Some ((roots, trace_bs), post_state) \<in>
        set_dist
          (execute (staged_trace_fri_program A 0 i []) pre_state)"
    unfolding staged_trace_fri_challenge_prefix_program_def
    by (auto elim!: set_dist_bindE)
  have "length trace_bs = length ([] :: 'f list) + i"
    by (rule staged_trace_fri_program_challenge_length[OF fri_out])
  then show ?thesis by simp
qed

lemma staged_trace_fri_prefix_vector_member_imp_position_value:
  assumes outcome:
    "Some ((fr, trace_bs, rt), t) \<in>
      set_dist
        (execute (staged_trace_fri_challenge_prefix_program A i) s)"
    and subset: "B \<subseteq> fri_challenge_space i"
    and member: "trace_bs \<in> B"
    and j_bound: "j < i"
  shows "trace_bs ! j \<in> fri_vector_position_values B j"
  by (rule fri_vector_member_imp_position_value
      [OF subset member j_bound])

lemma staged_trace_fri_prefix_head_challenge_imp_position_value:
  assumes outcome:
    "Some (((fr, trace_bs, rt), b), t) \<in>
      set_dist
        (execute
          (staged_trace_fri_challenge_prefix_program A i \<bind>
            (\<lambda>prefix. receive_trace_fri_challenge \<bind>
              (\<lambda>b. return (prefix, b)))) s)"
    and member: "trace_bs @ [b] \<in> B"
  shows "b \<in> fri_vector_position_values B i"
proof -
  from outcome obtain s1 where
    prefix_out:
      "Some ((fr, trace_bs, rt), s1) \<in>
        set_dist
          (execute (staged_trace_fri_challenge_prefix_program A i) s)"
    by (auto elim!: set_dist_bindE)
  have len: "length trace_bs = i"
    by (rule staged_trace_fri_challenge_prefix_program_length
        [OF prefix_out])
  show ?thesis
    by (rule fri_vector_extend_member_imp_position_value
        [OF member len])
qed

lemma staged_alpha_program_alignment:
  assumes outcome:
    "Some (as, t) \<in> set_dist (execute (staged_alpha_program n) s)"
  shows
    "length as = n \<and>
     PTranscript t = PTranscript s @ as \<and>
     PState t = foldl concat (PState s) as \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s + n \<and>
     PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction n arbitrary: as s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from staged_alpha_program_Suc_outcomeE[OF Suc.prems]
  obtain a as' s1 s2 where
    challenge_out:
      "Some (a, s1) \<in>
        set_dist (execute receive_alpha_challenge s)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (record_staged_message a) s1)"
    and rest_out:
      "Some (as', t) \<in>
        set_dist (execute (staged_alpha_program n) s2)"
    and as_eq: "as = a # as'"
    .
  have challenge_fields:
    "PState s1 = PState s \<and>
     PTranscript s1 = PTranscript s"
    using receive_alpha_challenge_outcome[OF challenge_out] by simp
  have challenge_counters:
    "PTraceFriCounter s1 = PTraceFriCounter s \<and>
     PCompositionFriCounter s1 = PCompositionFriCounter s \<and>
     PAlphaCounter s1 = Suc (PAlphaCounter s) \<and>
     PQueryCounter s1 = PQueryCounter s"
    using receive_alpha_challenge_counter_outcome[OF challenge_out] by simp
  have s2:
    "s2 = s1\<lparr>
      PState := concat (PState s1) a,
      PTranscript := PTranscript s1 @ [a]\<rparr>"
    by (rule record_staged_message_outcome[OF record_out])
  have s2_fields:
    "PState s2 = concat (PState s) a \<and>
     PTranscript s2 = PTranscript s @ [a] \<and>
     PTraceFriCounter s2 = PTraceFriCounter s \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s \<and>
     PAlphaCounter s2 = Suc (PAlphaCounter s) \<and>
     PQueryCounter s2 = PQueryCounter s"
    unfolding s2 using challenge_fields challenge_counters by simp
  have rest_alignment:
    "length as' = n \<and>
     PTranscript t = PTranscript s2 @ as' \<and>
     PState t = foldl concat (PState s2) as' \<and>
     PTraceFriCounter t = PTraceFriCounter s2 \<and>
     PCompositionFriCounter t = PCompositionFriCounter s2 \<and>
     PAlphaCounter t = PAlphaCounter s2 + n \<and>
     PQueryCounter t = PQueryCounter s2"
    by (rule Suc.IH[OF rest_out])
  show ?case
    unfolding as_eq
    using s2_fields rest_alignment
    by simp
qed

lemma staged_receive_alpha_challenge_preserves_alpha_future_fresh:
  assumes future: "alpha_future_fresh s"
    and outcome: "Some (a, t) \<in> set_dist (execute receive_alpha_challenge s)"
  shows "alpha_future_fresh t"
proof -
  have counter_t: "PAlphaCounter t = Suc (PAlphaCounter s)"
    using receive_alpha_challenge_counter_outcome[OF outcome] by simp
  show ?thesis
    unfolding alpha_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_future: "PAlphaCounter t \<le> i"
    have i_ge_s: "PAlphaCounter s \<le> i"
      using counter_t i_future by simp
    have neq:
      "AlphaChallenge i x \<noteq>
        AlphaChallenge (PAlphaCounter s) (PState s)"
      using counter_t i_future by auto
    have "fmlookup (HashMap t) (AlphaChallenge i x) =
        fmlookup (HashMap s) (AlphaChallenge i x)"
      by (rule receive_alpha_challenge_preserves_other_lookup
          [OF outcome neq])
    also have "... = None"
      using future i_ge_s unfolding alpha_future_fresh_def by blast
    finally show "fmlookup (HashMap t) (AlphaChallenge i x) = None" .
  qed
qed

lemma record_staged_message_preserves_alpha_future_fresh:
  assumes future: "alpha_future_fresh s"
    and outcome:
      "Some ((), t) \<in> set_dist (execute (record_staged_message x) s)"
  shows "alpha_future_fresh t"
proof -
  have t_eq:
    "t = s\<lparr>
      PState := concat (PState s) x,
      PTranscript := PTranscript s @ [x]\<rparr>"
    by (rule record_staged_message_outcome[OF outcome])
  show ?thesis
    using future unfolding t_eq alpha_future_fresh_def by simp
qed

lemma staged_alpha_program_preserves_alpha_future_fresh:
  assumes future: "alpha_future_fresh s"
    and outcome:
      "Some (as, t) \<in> set_dist (execute (staged_alpha_program n) s)"
  shows "alpha_future_fresh t"
  using future outcome
proof (induction n arbitrary: as s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases rule:
      staged_alpha_program_Suc_outcomeE[OF Suc.prems(2)])
    case (1 a as' s1 s2)
    have future_s1:
      "alpha_future_fresh s1"
      by (rule staged_receive_alpha_challenge_preserves_alpha_future_fresh
          [OF Suc.prems(1) 1(1)])
    have future_s2:
      "alpha_future_fresh s2"
      by (rule record_staged_message_preserves_alpha_future_fresh
          [OF future_s1 1(2)])
    show ?thesis
      by (rule Suc.IH[OF future_s2 1(3)])
  qed
qed

lemma wp_staged_alpha_program_exact_challenges_bound:
  assumes len: "length as = n"
    and future: "alpha_future_fresh s"
  shows
    "wp_event (staged_alpha_program n)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as', _) \<Rightarrow> as' = as) s \<le>
      (1 / nnreal size) ^ n"
  using len future
proof (induction n arbitrary: as s)
  case 0
  then have as_empty: "as = []"
    by simp
  show ?case
    unfolding as_empty by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  obtain a as_tail where as_eq: "as = a # as_tail"
    using Suc.prems(1) by (cases as) auto
  have len_tail: "length as_tail = n"
    using Suc.prems(1) as_eq by simp
  let ?tail =
    "staged_alpha_program n ::
      ('f list, 'f protocol_channel) state_monad"
  let ?Q =
    "\<lambda>out :: ('f list \<times>
        'f protocol_channel) option.
      case out of None \<Rightarrow> False | Some (as', _) \<Rightarrow> as' = as"
  let ?Head =
    "\<lambda>out :: ('f \<times>
        'f protocol_channel) option.
      case out of None \<Rightarrow> False | Some (a0, _) \<Rightarrow> a0 \<in> {a}"
  have head_bound:
    "wp_event receive_alpha_challenge ?Head s \<le> 1 / nnreal size"
  proof -
    have current_fresh:
      "fmlookup (HashMap s)
        (AlphaChallenge (PAlphaCounter s) (PState s)) = None"
      by (rule alpha_future_fresh_current[OF Suc.prems(2)])
    have "wp_event receive_alpha_challenge ?Head s =
        nnreal (card ({a} :: 'f set)) / nnreal size"
      by (rule wp_receive_alpha_challenge_fresh_set[OF current_fresh])
    then show ?thesis by simp
  qed
  have bind_bound:
    "wp_event
      (receive_alpha_challenge \<bind>
        (\<lambda>a0. record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind>
            (\<lambda>as'. return (a0 # as')))))
      ?Q s \<le>
      wp_event receive_alpha_challenge ?Head s *
        (1 / nnreal size) ^ n"
  proof (rule wp_event_bind_bound_by_head_and_cont[where P = ?Head])
    show "\<not> ?Q None"
      by simp
  next
    fix a0 t
    assume recv:
      "Some (a0, t) \<in> set_dist (execute receive_alpha_challenge s)"
      and not_head: "\<not> ?Head (Some (a0, t))"
    have a0_ne: "a0 \<noteq> a"
      using not_head by simp
    have cont_false:
      "wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t \<le>
       wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        (\<lambda>_ :: ('f list \<times>
          'f protocol_channel) option. False) t"
      by (rule wp_event_mono_on_support)
        (use a0_ne as_eq in
          \<open>auto simp: wpsimps elim!: set_dist_bindE
              split: option.splits prod.splits\<close>)
    also have "... = 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
    finally have le_zero:
      "wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t \<le> 0" .
    show
      "wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t = 0"
      by (rule antisym[OF le_zero]) simp
  next
    fix a0 t
    assume recv:
      "Some (a0, t) \<in> set_dist (execute receive_alpha_challenge s)"
      and head: "?Head (Some (a0, t))"
    have a0_eq: "a0 = a"
      using head by simp
    have future_t: "alpha_future_fresh t"
      by (rule staged_receive_alpha_challenge_preserves_alpha_future_fresh
          [OF Suc.prems(2) recv])
    have record_cont_bound:
      "wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t \<le> (1 / nnreal size) ^ n"
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?Q None"
        by simp
    next
      fix uu u
      assume record_out:
        "Some (uu, u) \<in>
          set_dist (execute (record_staged_message a0) t)"
      have record_unit:
        "Some ((), u) \<in>
          set_dist (execute (record_staged_message a0) t)"
        using record_out by (cases uu) simp
      have future_u: "alpha_future_fresh u"
        by (rule record_staged_message_preserves_alpha_future_fresh
            [OF future_t record_unit])
      have tail_bound:
        "wp_event ?tail
          (\<lambda>out. case out of None \<Rightarrow> False
            | Some (as', _) \<Rightarrow> as' = as_tail) u
          \<le> (1 / nnreal size) ^ n"
        by (rule Suc.IH[OF len_tail future_u])
      have cont_eq:
        "wp_event
          (?tail \<bind> (\<lambda>as'. return (a0 # as'))) ?Q u =
         wp_event ?tail
          (\<lambda>out. case out of None \<Rightarrow> False
            | Some (as', _) \<Rightarrow> as' = as_tail) u"
        by (simp add: wp_event_bind_return_map a0_eq as_eq
            split: option.splits prod.splits)
      show
        "wp_event (?tail \<bind> (\<lambda>as'. return (a0 # as'))) ?Q u
          \<le> (1 / nnreal size) ^ n"
        unfolding cont_eq by (rule tail_bound)
    qed
    show
      "wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t \<le> (1 / nnreal size) ^ n"
      by (rule record_cont_bound)
  qed
  have "wp_event (staged_alpha_program (Suc n)) ?Q s
      \<le> wp_event receive_alpha_challenge ?Head s *
        (1 / nnreal size) ^ n"
    unfolding staged_alpha_program.simps by (rule bind_bound)
  also have "... \<le> (1 / nnreal size) * (1 / nnreal size) ^ n"
    by (rule mult_right_mono[OF head_bound]) simp
  also have "... = (1 / nnreal size) ^ Suc n"
    by simp
  finally show ?case .
qed

lemma wp_staged_alpha_program_finite_set_bound:
  assumes future: "alpha_future_fresh s"
    and finite_B: "finite B"
    and lengths: "\<And>as. as \<in> B \<Longrightarrow> length as = n"
  shows
    "wp_event (staged_alpha_program n)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le>
      nnreal (card B) / (nnreal size) ^ n"
proof -
  let ?P =
    "\<lambda>as out. case out of None \<Rightarrow> False
      | Some (as', _) \<Rightarrow> as' = as"
  have event_mono:
    "wp_event (staged_alpha_program n)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le>
     wp_event (staged_alpha_program n)
      (\<lambda>out. \<exists>as \<in> B. ?P as out) s"
    by (rule wp_event_mono) (auto split: option.splits prod.splits)
  also have "... \<le> (\<Sum>as\<in>B. (1 / nnreal size) ^ n)"
    by (rule wp_event_finite_UN_bound[OF finite_B])
      (rule wp_staged_alpha_program_exact_challenges_bound
        [OF lengths future])
  also have "... = nnreal (card B) * ((1 / nnreal size) ^ n)"
    using finite_B by simp
  also have "... = nnreal (card B) / (nnreal size) ^ n"
    using size_card by transfer (simp add: power_divide)
  finally show ?thesis .
qed

lemma wp_staged_alpha_program_alpha_space_set_bound:
  assumes future: "alpha_future_fresh s"
    and subset: "B \<subseteq> alpha_space"
  shows
    "wp_event (staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le>
      nnreal (card B) / nnreal (CARD('f) ^ length spec)"
proof -
  have finite_B: "finite B"
    by (rule finite_subset[OF subset])
      (simp add: alpha_space_def finite_length_lists_UNIV)
  have lengths: "\<And>as. as \<in> B \<Longrightarrow> length as = length spec"
    using subset unfolding alpha_space_def by auto
  have "wp_event (staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le>
      nnreal (card B) / (nnreal size) ^ length spec"
    by (rule wp_staged_alpha_program_finite_set_bound
        [OF future finite_B lengths])
  also have "... =
      nnreal (card B) / nnreal (CARD('f) ^ length spec)"
    using size_card by simp
  finally show ?thesis .
qed

lemma staged_after_alpha_prefix_program_alpha_space_list_bound_from_fresh:
  assumes future: "alpha_future_fresh s"
    and subset: "B \<subseteq> alpha_space"
  shows
    "wp_event
      (staged_after_alpha_prefix_program A
        (fr, trace_roots, trace_bs, trace_final))
      (staged_transcript_alpha_list_hit B) s \<le>
      nnreal (card B) / nnreal (CARD('f) ^ length spec)"
proof -
  have alpha_bound:
    "wp_event (staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le>
      nnreal (card B) / nnreal (CARD('f) ^ length spec)"
    by (rule wp_staged_alpha_program_alpha_space_set_bound
        [OF future subset])
  show ?thesis
    by (rule staged_after_alpha_prefix_program_alpha_list_bound_from_alpha_program
        [OF alpha_bound])
qed

lemma staged_transcript_program_alpha_space_list_bound_from_fresh_prefix:
  assumes prefix_future:
    "\<And>prefix t.
      Some (prefix, t) \<in>
        set_dist (execute (staged_alpha_prefix_program A)
          adversary_initial_state) \<Longrightarrow>
      alpha_future_fresh t"
    and subset: "B \<subseteq> alpha_space"
  shows
    "wp_event (staged_transcript_program A)
      (staged_transcript_alpha_list_hit B) adversary_initial_state \<le>
      nnreal (card B) / nnreal (CARD('f) ^ length spec)"
  unfolding staged_transcript_program_alpha_prefix_decomp
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> staged_transcript_alpha_list_hit B None"
    unfolding staged_transcript_alpha_list_hit_def by simp
next
  fix prefix t
  assume prefix_out:
    "Some (prefix, t) \<in>
      set_dist (execute (staged_alpha_prefix_program A)
        adversary_initial_state)"
  obtain fr trace_roots trace_bs trace_final
    where prefix_eq: "prefix = (fr, trace_roots, trace_bs, trace_final)"
    by (cases prefix) auto
  have future_t: "alpha_future_fresh t"
    by (rule prefix_future[OF prefix_out])
  show
    "wp_event (staged_after_alpha_prefix_program A prefix)
      (staged_transcript_alpha_list_hit B) t \<le>
      nnreal (card B) / nnreal (CARD('f) ^ length spec)"
    unfolding prefix_eq
    by (rule staged_after_alpha_prefix_program_alpha_space_list_bound_from_fresh
        [OF future_t subset])
qed

lemma staged_composition_fri_program_challenge_prefix_pre_alignment:
  assumes outcome:
    "Some ((roots, bs'), t) \<in>
      set_dist
        (execute (staged_composition_fri_program A dg i n bs) s)"
  shows "take (length bs) bs' = bs"
  using outcome
proof (induction n arbitrary: i bs roots bs' s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain root b roots' s1 s2 s3 where
    rest_out:
      "Some ((roots', bs'), t) \<in>
        set_dist
          (execute
            (staged_composition_fri_program
              A dg (Suc i) n (bs @ [b])) s3)"
    unfolding staged_composition_fri_program.simps
    by (auto elim!: set_dist_bindE)
  have prefix_suc:
    "take (length (bs @ [b])) bs' = bs @ [b]"
    by (rule Suc.IH[OF rest_out])
  have "take (length bs) bs' =
      take (length bs) (take (length (bs @ [b])) bs')"
    by simp
  also have "... = bs"
    using prefix_suc by simp
  finally show ?case .
qed

lemma staged_composition_fri_program_alignment:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound:
      "i + n \<le> length (composition_fri_budgets budgets)"
    and outcome:
      "Some ((roots, bs'), t) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg i n bs) s)"
  shows
    "length roots = n \<and>
     length bs' = length bs + n \<and>
     PTranscript t = PTranscript s @ roots \<and>
     PState t = foldl concat (PState s) roots \<and>
     s \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s + n \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s \<and>
     (\<forall>j < n.
        fmlookup (HashMap t)
          (CompositionFriChallenge (PCompositionFriCounter s + j)
            (foldl concat (PState s) (take (Suc j) roots))) =
        Some (bs' ! (length bs + j)))"
  using bound outcome
proof (induction n arbitrary: i bs roots bs' s t)
  case 0
  then show ?case by (simp add: hash_ext_refl)
next
  case (Suc n)
  from staged_composition_fri_program_Suc_outcomeE[OF Suc.prems(2)]
  obtain root b roots' s1 s2 s3 where
    stage_out:
      "Some (root, s1) \<in>
        set_dist
          (execute (composition_fri_root_stage A dg i bs) s)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in>
        set_dist (execute receive_composition_fri_challenge s2)"
    and rest_out:
      "Some ((roots', bs'), t) \<in>
        set_dist
          (execute
            (staged_composition_fri_program
              A dg (Suc i) n (bs @ [b])) s3)"
    and roots_eq: "roots = root # roots'"
    .
  have i_bound: "i < length (composition_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have stage_fields:
    "PState s1 = PState s \<and>
     PTranscript s1 = PTranscript s \<and>
     PTraceFriCounter s1 = PTraceFriCounter s \<and>
     PCompositionFriCounter s1 = PCompositionFriCounter s \<and>
     PAlphaCounter s1 = PAlphaCounter s \<and>
     PQueryCounter s1 = PQueryCounter s"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have ext_s_s1: "s \<le> s1"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have s2:
    "s2 = s1\<lparr>
      PState := concat (PState s1) root,
      PTranscript := PTranscript s1 @ [root]\<rparr>"
    by (rule record_staged_message_outcome[OF record_out])
  have ext_s1_s2: "s1 \<le> s2"
    unfolding s2 less_eq_hash_ext_def less_eq_fmap_def by simp
  have s2_fields:
    "PState s2 = concat (PState s) root \<and>
     PTranscript s2 = PTranscript s @ [root] \<and>
     PTraceFriCounter s2 = PTraceFriCounter s \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s \<and>
     PAlphaCounter s2 = PAlphaCounter s \<and>
     PQueryCounter s2 = PQueryCounter s"
    unfolding s2 using stage_fields by simp
  have challenge_fields:
    "PState s3 = PState s2 \<and>
     PTranscript s3 = PTranscript s2"
    using receive_composition_fri_challenge_outcome[OF challenge_out]
    by simp
  have ext_s2_s3: "s2 \<le> s3"
    using receive_composition_fri_challenge_outcome[OF challenge_out]
    by simp
  have challenge_counters:
    "PTraceFriCounter s3 = PTraceFriCounter s2 \<and>
     PCompositionFriCounter s3 =
       Suc (PCompositionFriCounter s2) \<and>
     PAlphaCounter s3 = PAlphaCounter s2 \<and>
     PQueryCounter s3 = PQueryCounter s2"
    using
      receive_composition_fri_challenge_counter_outcome[OF challenge_out]
    by simp
  have rest_bound:
    "Suc i + n \<le> length (composition_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have rest_alignment:
    "length roots' = n \<and>
     length bs' = length (bs @ [b]) + n \<and>
     PTranscript t = PTranscript s3 @ roots' \<and>
     PState t = foldl concat (PState s3) roots' \<and>
     s3 \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s3 \<and>
     PCompositionFriCounter t = PCompositionFriCounter s3 + n \<and>
     PAlphaCounter t = PAlphaCounter s3 \<and>
     PQueryCounter t = PQueryCounter s3 \<and>
     (\<forall>j < n.
        fmlookup (HashMap t)
          (CompositionFriChallenge (PCompositionFriCounter s3 + j)
            (foldl concat (PState s3) (take (Suc j) roots'))) =
        Some (bs' ! (length (bs @ [b]) + j)))"
    by (rule Suc.IH[OF rest_bound rest_out])
  have ext_s3_t: "s3 \<le> t"
    using rest_alignment by simp
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_s1])
      (rule hash_ext_trans[OF ext_s1_s2],
        rule hash_ext_trans[OF ext_s2_s3 ext_s3_t])
  have challenge_lookup_s3:
    "fmlookup (HashMap s3)
      (CompositionFriChallenge (PCompositionFriCounter s)
        (concat (PState s) root)) = Some b"
    using receive_composition_fri_challenge_outcome[OF challenge_out]
      s2_fields by simp
  have challenge_lookup_t:
    "fmlookup (HashMap t)
      (CompositionFriChallenge (PCompositionFriCounter s)
        (concat (PState s) root)) = Some b"
    by (rule hash_extension_lookup[OF challenge_lookup_s3 ext_s3_t])
  have prefix_suc:
    "take (length (bs @ [b])) bs' = bs @ [b]"
    by (rule staged_composition_fri_program_challenge_prefix_pre_alignment
        [OF rest_out])
  have lookup_all:
    "\<forall>j < Suc n.
      fmlookup (HashMap t)
        (CompositionFriChallenge (PCompositionFriCounter s + j)
          (foldl concat (PState s) (take (Suc j) (root # roots')))) =
      Some (bs' ! (length bs + j))"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show
      "fmlookup (HashMap t)
        (CompositionFriChallenge (PCompositionFriCounter s + j)
          (foldl concat (PState s) (take (Suc j) (root # roots')))) =
      Some (bs' ! (length bs + j))"
    proof (cases j)
      case 0
      have "bs' ! length bs = b"
      proof -
        have idx_lt: "length bs < length (bs @ [b])"
          by simp
        have "bs' ! length bs =
            take (length (bs @ [b])) bs' ! length bs"
          using idx_lt by simp
        also have "... = (bs @ [b]) ! length bs"
          using prefix_suc by simp
        also have "... = b"
          by simp
        finally show ?thesis .
      qed
      then show ?thesis
        using challenge_lookup_t unfolding 0 by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      show ?thesis
        using rest_alignment k_bound s2_fields challenge_fields
          challenge_counters
        unfolding Suc
        by simp
    qed
  qed
  show ?case
    unfolding roots_eq
    using s2_fields challenge_fields challenge_counters rest_alignment
      ext_s_t lookup_all
    by simp
qed

lemma staged_composition_fri_program_challenge_prefix:
  assumes outcome:
    "Some ((roots, bs'), t) \<in>
      set_dist
        (execute (staged_composition_fri_program A dg i n bs) s)"
  shows "take (length bs) bs' = bs"
  using outcome
proof (induction n arbitrary: i bs roots bs' s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain root b roots' s1 s2 s3 where
    rest_out:
      "Some ((roots', bs'), t) \<in>
        set_dist
          (execute
            (staged_composition_fri_program
              A dg (Suc i) n (bs @ [b])) s3)"
    unfolding staged_composition_fri_program.simps
    by (auto elim!: set_dist_bindE)
  have prefix_suc:
    "take (length (bs @ [b])) bs' = bs @ [b]"
    by (rule Suc.IH[OF rest_out])
  have "take (length bs) bs' =
      take (length bs) (take (length (bs @ [b])) bs')"
    by simp
  also have "... = bs"
    using prefix_suc by simp
  finally show ?case .
qed

lemma staged_composition_fri_program_challenge_length:
  assumes outcome:
    "Some ((roots, bs'), t) \<in>
      set_dist
        (execute (staged_composition_fri_program A dg i n bs) s)"
  shows "length bs' = length bs + n"
  using outcome
proof (induction n arbitrary: i bs roots bs' s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain root b roots' s1 s2 s3 where
    rest_out:
      "Some ((roots', bs'), t) \<in>
        set_dist
          (execute
            (staged_composition_fri_program
              A dg (Suc i) n (bs @ [b])) s3)"
    unfolding staged_composition_fri_program.simps
    by (auto elim!: set_dist_bindE)
  have "length bs' = length (bs @ [b]) + n"
    by (rule Suc.IH[OF rest_out])
  then show ?case by simp
qed

lemma staged_composition_fri_challenge_prefix_program_length:
  assumes outcome:
    "Some ((dg, composition_bs, rt), t) \<in>
      set_dist
        (execute (staged_composition_fri_challenge_prefix_program A i) s)"
  shows "length composition_bs = i"
proof -
  from outcome obtain as s1 dg0 s2 s3 where
    inner:
      "Some ((dg, composition_bs, rt), t) \<in>
        set_dist
          (execute
            (let composition_rounds = ceil_log (to_nat dg0 + 1)
             in assert (Suc i \<le> composition_rounds) \<bind>
                (\<lambda>_. assert
                  (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_.
                    staged_composition_fri_program A dg0 0 i [] \<bind>
                      (\<lambda>(composition_roots, composition_bs).
                        composition_fri_root_stage A dg0 i
                          composition_bs \<bind>
                          (\<lambda>rt.
                            record_staged_message rt \<bind>
                              (\<lambda>_. return
                                (dg0, composition_bs, rt)))))))
            s3)"
    unfolding staged_composition_fri_challenge_prefix_program_def
    by (auto elim!: set_dist_bindE)
  let ?rounds = "ceil_log (to_nat dg0 + 1)"
  have fri_out:
    "\<exists>composition_roots s4.
      Some ((composition_roots, composition_bs), s4) \<in>
        set_dist
          (execute (staged_composition_fri_program A dg0 0 i []) s3)"
  proof (cases "Suc i \<le> ?rounds")
    case False
    then show ?thesis
      using inner
      by (auto simp: assert_def throw_no_outcome elim!: set_dist_bindE)
  next
    case first_guard: True
    show ?thesis
    proof (cases "?rounds \<le> ceil_log (maxDegree + 1)")
      case False
      then show ?thesis
        using inner first_guard
        by (auto simp: assert_def throw_no_outcome elim!: set_dist_bindE)
    next
      case second_guard: True
      from inner obtain composition_roots s4 where
        "Some ((composition_roots, composition_bs), s4) \<in>
          set_dist
            (execute (staged_composition_fri_program A dg0 0 i []) s3)"
        using first_guard second_guard
        by (auto simp: assert_def elim!: set_dist_bindE split: prod.splits)
      then show ?thesis by blast
    qed
  qed
  then obtain composition_roots s4 where fri_out:
    "Some ((composition_roots, composition_bs), s4) \<in>
      set_dist
        (execute (staged_composition_fri_program A dg0 0 i []) s3)"
    by blast
  have "length composition_bs = length ([] :: 'f list) + i"
    by (rule staged_composition_fri_program_challenge_length[OF fri_out])
  then show ?thesis by simp
qed

lemma staged_composition_fri_prefix_vector_member_imp_position_value:
  assumes outcome:
    "Some ((dg, composition_bs, rt), t) \<in>
      set_dist
        (execute (staged_composition_fri_challenge_prefix_program A i) s)"
    and subset: "B \<subseteq> fri_challenge_space i"
    and member: "composition_bs \<in> B"
    and j_bound: "j < i"
  shows "composition_bs ! j \<in> fri_vector_position_values B j"
  by (rule fri_vector_member_imp_position_value
      [OF subset member j_bound])

lemma staged_composition_fri_prefix_head_challenge_imp_position_value:
  assumes outcome:
    "Some (((dg, composition_bs, rt), b), t) \<in>
      set_dist
        (execute
          (staged_composition_fri_challenge_prefix_program A i \<bind>
            (\<lambda>prefix. receive_composition_fri_challenge \<bind>
              (\<lambda>b. return (prefix, b)))) s)"
    and member: "composition_bs @ [b] \<in> B"
  shows "b \<in> fri_vector_position_values B i"
proof -
  from outcome obtain s1 where
    prefix_out:
      "Some ((dg, composition_bs, rt), s1) \<in>
        set_dist
          (execute (staged_composition_fri_challenge_prefix_program A i) s)"
    by (auto elim!: set_dist_bindE)
  have len: "length composition_bs = i"
    by (rule staged_composition_fri_challenge_prefix_program_length
        [OF prefix_out])
  show ?thesis
    by (rule fri_vector_extend_member_imp_position_value
        [OF member len])
qed

lemma staged_composition_fri_vector_bad_coordinate_cover_bound:
  assumes subset:
    "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
  shows
    "wp_event (staged_composition_fri_vector_program A)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((dg, composition_bs), _) \<Rightarrow>
            composition_bs \<in> B dg \<and>
            0 < ceil_log (to_nat dg + 1) \<and>
            ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) s \<le>
      (\<Sum>i < ceil_log (maxDegree + 1).
        wp_event (staged_composition_fri_vector_program A)
          (\<lambda>out. case out of None \<Rightarrow> False
            | Some ((dg, composition_bs), _) \<Rightarrow>
                i < ceil_log (to_nat dg + 1) \<and>
                composition_bs ! i \<in>
                  fri_vector_position_values (B dg) i) s)"
proof -
  let ?bad =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some ((dg, composition_bs), _) \<Rightarrow>
          composition_bs \<in> B dg \<and>
          0 < ceil_log (to_nat dg + 1) \<and>
          ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
  let ?coord =
    "\<lambda>i out. case out of None \<Rightarrow> False
      | Some ((dg, composition_bs), _) \<Rightarrow>
          i < ceil_log (to_nat dg + 1) \<and>
          composition_bs ! i \<in> fri_vector_position_values (B dg) i"
  have bad_to_coord:
    "wp_event (staged_composition_fri_vector_program A) ?bad s \<le>
      wp_event (staged_composition_fri_vector_program A)
        (\<lambda>out. \<exists>i \<in> {..<ceil_log (maxDegree + 1)}. ?coord i out) s"
  proof (rule wp_event_mono)
    fix out
    assume bad: "?bad out"
    show "\<exists>i \<in> {..<ceil_log (maxDegree + 1)}. ?coord i out"
    proof (cases out)
      case None
      then show ?thesis using bad by simp
    next
      case (Some result)
      then obtain dg composition_bs t where
        out_eq: "out = Some ((dg, composition_bs), t)"
        by (cases result, auto split: prod.splits)
      let ?n = "ceil_log (to_nat dg + 1)"
      have member: "composition_bs \<in> B dg"
        and nonempty: "0 < ?n"
        and rounds_bound: "?n \<le> ceil_log (maxDegree + 1)"
        using bad unfolding out_eq by simp_all
      from fri_vector_member_coordinate_cover
        [OF subset[of dg] member nonempty]
      obtain i where i_bound: "i < ?n"
        and coord:
          "composition_bs ! i \<in> fri_vector_position_values (B dg) i"
        by blast
      have i_max: "i < ceil_log (maxDegree + 1)"
        using i_bound rounds_bound by simp
      show ?thesis
        by (rule bexI[of _ i])
          (use i_bound i_max coord out_eq in simp_all)
    qed
  qed
  also have "... \<le>
      (\<Sum>i < ceil_log (maxDegree + 1).
        wp_event (staged_composition_fri_vector_program A) (?coord i) s)"
    by (rule wp_event_finite_UN_bound) simp_all
  finally show ?thesis .
qed

lemma
  staged_composition_fri_vector_coordinate_hit_imp_new_output_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log (to_nat dg + 1)"
    and absent:
      "composition_fri_challenge_values_absent
        (fri_vector_position_values (B dg) i) s"
    and outcome:
      "Some ((dg, composition_bs), t) \<in>
        set_dist (execute (staged_composition_fri_vector_program A) s)"
    and hit:
      "composition_bs ! i \<in> fri_vector_position_values (B dg) i"
  shows
    "hash_new_output_hit_event (fri_vector_position_values (B dg) i) s
      (Some ((dg, composition_bs), t))"
proof -
  from outcome obtain alpha_prefix s1 as s2 s3 s4 s5 roots where
    alpha_prefix_out:
      "Some (alpha_prefix, s1) \<in>
        set_dist (execute (staged_alpha_prefix_program A) s)"
    and alpha_out:
      "Some (as, s2) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s1)"
    and degree_out:
      "Some (dg, s3) \<in> set_dist (execute (degree_stage A as) s2)"
    and record_degree:
      "Some ((), s4) \<in>
        set_dist (execute (record_staged_message dg) s3)"
    and assert_out:
      "Some ((), s5) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1))) s4)"
    and fri_out:
      "Some ((roots, composition_bs), t) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s5)"
    unfolding staged_composition_fri_vector_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have len:
    "0 + ceil_log (to_nat dg + 1) \<le>
      length (composition_fri_budgets budgets)"
    using round_bound wf unfolding staged_budget_wellformed_def by simp
  have alignment:
    "length roots = ceil_log (to_nat dg + 1) \<and>
     length composition_bs =
       length ([] :: 'f list) + ceil_log (to_nat dg + 1) \<and>
     PTranscript t = PTranscript s5 @ roots \<and>
     PState t = foldl concat (PState s5) roots \<and>
     s5 \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s5 \<and>
     PCompositionFriCounter t =
       PCompositionFriCounter s5 + ceil_log (to_nat dg + 1) \<and>
     PAlphaCounter t = PAlphaCounter s5 \<and>
     PQueryCounter t = PQueryCounter s5 \<and>
     (\<forall>j < ceil_log (to_nat dg + 1).
        fmlookup (HashMap t)
          (CompositionFriChallenge (PCompositionFriCounter s5 + j)
            (foldl concat (PState s5) (take (Suc j) roots))) =
        Some (composition_bs ! (length ([] :: 'f list) + j)))"
    by (rule staged_composition_fri_program_alignment
        [OF controlled len fri_out])
  let ?key =
    "CompositionFriChallenge (PCompositionFriCounter s5 + i)
      (foldl concat (PState s5) (take (Suc i) roots))"
  have lookup_t:
    "fmlookup (HashMap t) ?key = Some (composition_bs ! i)"
    using alignment i_bound by simp
  have ext_s_t: "s \<le> t"
    using hash_target_program_staged_composition_fri_vector_program
        [OF wf controlled,
          of "fri_vector_position_values (B dg) i"] outcome
    unfolding hash_target_program_def hash_extension_preserving_def
    by blast
  have none_s: "fmlookup (HashMap s) ?key = None"
  proof (cases "fmlookup (HashMap s) ?key")
    case None
    then show ?thesis .
  next
    case (Some old)
    have old_lookup_t:
      "fmlookup (HashMap t) ?key = Some old"
      by (rule hash_extension_lookup[OF Some ext_s_t])
    then have old_eq: "old = composition_bs ! i"
      using lookup_t by simp
    have "old \<notin> fri_vector_position_values (B dg) i"
      using absent Some
      unfolding composition_fri_challenge_values_absent_def by blast
    then show ?thesis
      using old_eq hit by simp
  qed
  have "hash_map_new_output_hit
      (fri_vector_position_values (B dg) i) s t"
    unfolding hash_map_new_output_hit_def
    using none_s lookup_t hit by blast
  then show ?thesis
    unfolding hash_new_output_hit_event_def by simp
qed

lemma staged_composition_fri_vector_coordinate_bound_fixed_degree:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log (to_nat dg + 1)"
    and absent:
      "composition_fri_challenge_values_absent
        (fri_vector_position_values (B dg) i) s"
  shows
    "wp_event (staged_composition_fri_vector_program A)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((dg', composition_bs), _) \<Rightarrow>
            dg' = dg \<and>
            composition_bs ! i \<in> fri_vector_position_values (B dg) i) s \<le>
      staged_phase_target_error (fri_vector_position_values (B dg) i)
        (staged_composition_fri_vector_search_queries budgets)"
proof -
  let ?P =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some ((dg', composition_bs), _) \<Rightarrow>
          dg' = dg \<and>
          composition_bs ! i \<in> fri_vector_position_values (B dg) i"
  let ?H =
    "hash_new_output_hit_event (fri_vector_position_values (B dg) i) s"
  have event_imp_hit:
    "wp_event (staged_composition_fri_vector_program A) ?P s \<le>
      wp_event (staged_composition_fri_vector_program A) ?H s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist
        (execute (staged_composition_fri_vector_program A) s)"
      and event: "?P out"
    show "?H out"
    proof (cases out)
      case None
      then show ?thesis using event by simp
    next
      case (Some result)
      then obtain dg' composition_bs t where
        out_eq: "out = Some ((dg', composition_bs), t)"
        by (cases result, auto split: prod.splits)
      have dg_eq: "dg' = dg"
        using event unfolding out_eq by simp
      have outcome:
        "Some ((dg, composition_bs), t) \<in>
          set_dist
            (execute (staged_composition_fri_vector_program A) s)"
        using support unfolding out_eq dg_eq .
      have hit:
        "composition_bs ! i \<in> fri_vector_position_values (B dg) i"
        using event unfolding out_eq by simp
      show ?thesis
        unfolding out_eq dg_eq
        by (rule
            staged_composition_fri_vector_coordinate_hit_imp_new_output_hit
            [where B=B, OF wf controlled i_bound absent outcome hit])
    qed
  qed
  also have
    "wp_event (staged_composition_fri_vector_program A) ?H s \<le>
      staged_phase_target_error (fri_vector_position_values (B dg) i)
        (staged_composition_fri_vector_search_queries budgets)"
    by (rule staged_composition_fri_vector_target_hit_bound
        [OF wf controlled])
  finally show ?thesis .
qed

lemma composition_fri_challenge_values_absent_subset:
  assumes subset: "A \<subseteq> B"
    and absent: "composition_fri_challenge_values_absent B s"
  shows "composition_fri_challenge_values_absent A s"
  using subset absent
  unfolding composition_fri_challenge_values_absent_def by blast

lemma hash_map_new_output_hit_mono_set:
  assumes subset: "A \<subseteq> B"
    and hit: "hash_map_new_output_hit A s t"
  shows "hash_map_new_output_hit B s t"
  using subset hit unfolding hash_map_new_output_hit_def by blast

lemma hash_new_output_hit_event_mono_set:
  assumes subset: "A \<subseteq> B"
    and hit: "hash_new_output_hit_event A s out"
  shows "hash_new_output_hit_event B s out"
proof (cases out)
  case None
  then show ?thesis
    using hit unfolding hash_new_output_hit_event_def by simp
next
  case (Some result)
  then obtain x t where out_eq: "out = Some (x, t)"
    by (cases result) simp
  have map_hit: "hash_map_new_output_hit A s t"
    using hit unfolding out_eq hash_new_output_hit_event_def by simp
  have "hash_map_new_output_hit B s t"
    by (rule hash_map_new_output_hit_mono_set[OF subset map_hit])
  show ?thesis
    using `hash_map_new_output_hit B s t`
    unfolding out_eq hash_new_output_hit_event_def by simp
qed

lemma staged_composition_fri_vector_coordinate_bound_union:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and absent:
      "composition_fri_challenge_values_absent
        (\<Union>dg. fri_vector_position_values (B dg) i) s"
  shows
    "wp_event (staged_composition_fri_vector_program A)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((dg, composition_bs), _) \<Rightarrow>
            i < ceil_log (to_nat dg + 1) \<and>
            composition_bs ! i \<in>
              fri_vector_position_values (B dg) i) s \<le>
      staged_phase_target_error
        (\<Union>dg. fri_vector_position_values (B dg) i)
        (staged_composition_fri_vector_search_queries budgets)"
proof -
  let ?U = "(\<Union>dg. fri_vector_position_values (B dg) i)"
  let ?P =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some ((dg, composition_bs), _) \<Rightarrow>
          i < ceil_log (to_nat dg + 1) \<and>
          composition_bs ! i \<in> fri_vector_position_values (B dg) i"
  let ?H = "hash_new_output_hit_event ?U s"
  have event_imp_hit:
    "wp_event (staged_composition_fri_vector_program A) ?P s \<le>
      wp_event (staged_composition_fri_vector_program A) ?H s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist
        (execute (staged_composition_fri_vector_program A) s)"
      and event: "?P out"
    show "?H out"
    proof (cases out)
      case None
      then show ?thesis using event by simp
    next
      case (Some result)
      then obtain dg composition_bs t where
        out_eq: "out = Some ((dg, composition_bs), t)"
        by (cases result, auto split: prod.splits)
      have outcome:
        "Some ((dg, composition_bs), t) \<in>
          set_dist
            (execute (staged_composition_fri_vector_program A) s)"
        using support unfolding out_eq .
      have i_bound: "i < ceil_log (to_nat dg + 1)"
        using event unfolding out_eq by simp
      have hit:
        "composition_bs ! i \<in> fri_vector_position_values (B dg) i"
        using event unfolding out_eq by simp
      have small_absent:
        "composition_fri_challenge_values_absent
          (fri_vector_position_values (B dg) i) s"
        by (rule composition_fri_challenge_values_absent_subset
            [OF _ absent]) blast
      have small_hit:
        "hash_new_output_hit_event
          (fri_vector_position_values (B dg) i) s
          (Some ((dg, composition_bs), t))"
        by (rule
            staged_composition_fri_vector_coordinate_hit_imp_new_output_hit
            [where B=B,
              OF wf controlled i_bound small_absent outcome hit])
      have subset:
        "fri_vector_position_values (B dg) i \<subseteq> ?U"
        by blast
      show ?thesis
        unfolding out_eq
        by (rule hash_new_output_hit_event_mono_set
            [OF subset small_hit])
    qed
  qed
  also have
    "wp_event (staged_composition_fri_vector_program A) ?H s \<le>
      staged_phase_target_error ?U
        (staged_composition_fri_vector_search_queries budgets)"
    by (rule staged_composition_fri_vector_target_hit_bound
        [OF wf controlled])
  finally show ?thesis .
qed

lemma staged_composition_fri_vector_bad_bound_union:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and absent:
      "\<And>i. i < ceil_log (maxDegree + 1) \<Longrightarrow>
        composition_fri_challenge_values_absent
          (\<Union>dg. fri_vector_position_values (B dg) i) s"
  shows
    "wp_event (staged_composition_fri_vector_program A)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((dg, composition_bs), _) \<Rightarrow>
            composition_bs \<in> B dg \<and>
            0 < ceil_log (to_nat dg + 1) \<and>
            ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) s \<le>
      (\<Sum>i < ceil_log (maxDegree + 1).
        staged_phase_target_error
          (\<Union>dg. fri_vector_position_values (B dg) i)
          (staged_composition_fri_vector_search_queries budgets))"
proof -
  let ?coord =
    "\<lambda>i out. case out of None \<Rightarrow> False
      | Some ((dg, composition_bs), _) \<Rightarrow>
          i < ceil_log (to_nat dg + 1) \<and>
          composition_bs ! i \<in> fri_vector_position_values (B dg) i"
  have cover:
    "wp_event (staged_composition_fri_vector_program A)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((dg, composition_bs), _) \<Rightarrow>
            composition_bs \<in> B dg \<and>
            0 < ceil_log (to_nat dg + 1) \<and>
            ceil_log (to_nat dg + 1) \<le>
              ceil_log (maxDegree + 1)) s \<le>
      (\<Sum>i < ceil_log (maxDegree + 1).
        wp_event (staged_composition_fri_vector_program A)
          (?coord i) s)"
    by (rule staged_composition_fri_vector_bad_coordinate_cover_bound
        [OF subset])
  also have "... \<le>
      (\<Sum>i < ceil_log (maxDegree + 1).
        staged_phase_target_error
          (\<Union>dg. fri_vector_position_values (B dg) i)
          (staged_composition_fri_vector_search_queries budgets))"
  proof (rule sum_mono)
    fix i
    assume i_in: "i \<in> {..<ceil_log (maxDegree + 1)}"
    then have i_bound: "i < ceil_log (maxDegree + 1)"
      by simp
    show
      "wp_event (staged_composition_fri_vector_program A)
        (?coord i) s \<le>
        staged_phase_target_error
          (\<Union>dg. fri_vector_position_values (B dg) i)
          (staged_composition_fri_vector_search_queries budgets)"
      by (rule staged_composition_fri_vector_coordinate_bound_union
          [OF wf controlled absent[OF i_bound]])
  qed
  finally show ?thesis .
qed

lemma staged_composition_fri_full_vector_bad_bound_union:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and absent:
      "\<And>i. i < ceil_log (maxDegree + 1) \<Longrightarrow>
        composition_fri_challenge_values_absent
          (\<Union>dg. fri_vector_position_values (B dg) i)
          adversary_initial_state"
  shows
    "wp_event (staged_composition_fri_full_vector_program A)
      (staged_composition_prefix_fri_vector_hit B)
      adversary_initial_state \<le>
      (\<Sum>i < ceil_log (maxDegree + 1).
        staged_phase_target_error
          (\<Union>dg. fri_vector_position_values (B dg) i)
          (staged_composition_fri_vector_search_queries budgets))"
proof -
  let ?Q =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some ((dg, composition_bs), _) \<Rightarrow>
          composition_bs \<in> B dg \<and>
          0 < ceil_log (to_nat dg + 1) \<and>
          ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
  have projected:
    "wp_event (staged_composition_fri_vector_program A) ?Q
      adversary_initial_state \<le>
      (\<Sum>i < ceil_log (maxDegree + 1).
        staged_phase_target_error
          (\<Union>dg. fri_vector_position_values (B dg) i)
          (staged_composition_fri_vector_search_queries budgets))"
    by (rule staged_composition_fri_vector_bad_bound_union
        [OF wf controlled subset absent])
  have eq:
    "wp_event (staged_composition_fri_vector_program A) ?Q
      adversary_initial_state =
     wp_event (staged_composition_fri_full_vector_program A)
      (staged_composition_prefix_fri_vector_hit B)
      adversary_initial_state"
    unfolding staged_composition_fri_vector_program_projection
      wp_event_bind_return_map
      staged_composition_prefix_fri_vector_hit_def
    by (simp split: option.splits prod.splits)
  show ?thesis
    using projected unfolding eq .
qed

lemma staged_transcript_program_composition_fri_vector_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and absent:
      "\<And>i. i < ceil_log (maxDegree + 1) \<Longrightarrow>
        composition_fri_challenge_values_absent
          (\<Union>dg. fri_vector_position_values (B dg) i)
          adversary_initial_state"
  shows
    "wp_event (staged_transcript_program A)
      (staged_transcript_composition_fri_vector_guarded_hit B)
      adversary_initial_state \<le>
      (\<Sum>i < ceil_log (maxDegree + 1).
        staged_phase_target_error
          (\<Union>dg. fri_vector_position_values (B dg) i)
          (staged_composition_fri_vector_search_queries budgets))"
proof -
  have prefix_bound:
    "wp_event (staged_composition_fri_full_vector_program A)
      (staged_composition_prefix_fri_vector_hit B)
      adversary_initial_state \<le>
      (\<Sum>i < ceil_log (maxDegree + 1).
        staged_phase_target_error
          (\<Union>dg. fri_vector_position_values (B dg) i)
          (staged_composition_fri_vector_search_queries budgets))"
    by (rule staged_composition_fri_full_vector_bad_bound_union
        [OF wf controlled subset absent])
  show ?thesis
    unfolding staged_transcript_program_composition_fri_full_vector_decomp
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show
      "staged_transcript_composition_fri_vector_guarded_hit B None \<Longrightarrow>
        staged_composition_prefix_fri_vector_hit B None"
      unfolding staged_transcript_composition_fri_vector_guarded_hit_def
        staged_composition_prefix_fri_vector_hit_def
      by simp
  next
    fix prefix t out
    assume cont:
      "out \<in>
        set_dist
          (execute
            (staged_after_composition_fri_full_vector_program A prefix) t)"
      and hit:
        "staged_transcript_composition_fri_vector_guarded_hit B out"
    show "staged_composition_prefix_fri_vector_hit B (Some (prefix, t))"
      by (rule staged_after_composition_fri_full_vector_program_hitD
          [OF cont hit])
  qed
qed

lemma staged_query_program_alignment:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and outcome:
      "Some (chunks, t) \<in>
        set_dist (execute (staged_query_program A i n) s)"
  shows
    "length chunks = n \<and>
     PTranscript t = PTranscript s @ List.concat chunks \<and>
     PState t = foldl concat (PState s) (List.concat chunks) \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s + n"
  using bound outcome
proof (induction n arbitrary: i chunks s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from staged_query_program_Suc_outcomeE[OF Suc.prems(2)]
  obtain raw chunk chunks' s1 s2 s3 where
    challenge_out:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and stage_out:
      "Some (chunk, s2) \<in>
        set_dist (execute (query_opening_stage A i raw) s1)"
    and record_out:
      "Some ((), s3) \<in>
        set_dist (execute (record_staged_messages chunk) s2)"
    and rest_out:
      "Some (chunks', t) \<in>
        set_dist (execute (staged_query_program A (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
    .
  have challenge_fields:
    "PState s1 = PState s \<and>
     PTranscript s1 = PTranscript s"
    using receive_query_index_challenge_outcome[OF challenge_out] by simp
  have challenge_counters:
    "PTraceFriCounter s1 = PTraceFriCounter s \<and>
     PCompositionFriCounter s1 = PCompositionFriCounter s \<and>
     PAlphaCounter s1 = PAlphaCounter s \<and>
     PQueryCounter s1 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF challenge_out]
    by simp
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have stage_fields:
    "PState s2 = PState s1 \<and>
     PTranscript s2 = PTranscript s1 \<and>
     PTraceFriCounter s2 = PTraceFriCounter s1 \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
     PAlphaCounter s2 = PAlphaCounter s1 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have s3:
    "s3 = s2\<lparr>
      PState := foldl concat (PState s2) chunk,
      PTranscript := PTranscript s2 @ chunk\<rparr>"
    by (rule record_staged_messages_outcome[OF record_out])
  have s3_fields:
    "PState s3 = foldl concat (PState s) chunk \<and>
     PTranscript s3 = PTranscript s @ chunk \<and>
     PTraceFriCounter s3 = PTraceFriCounter s \<and>
     PCompositionFriCounter s3 = PCompositionFriCounter s \<and>
     PAlphaCounter s3 = PAlphaCounter s \<and>
     PQueryCounter s3 = Suc (PQueryCounter s)"
    unfolding s3
    using challenge_fields challenge_counters stage_fields by simp
  have rest_bound:
    "Suc i + n \<le> length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have rest_alignment:
    "length chunks' = n \<and>
     PTranscript t = PTranscript s3 @ List.concat chunks' \<and>
     PState t =
       foldl concat (PState s3) (List.concat chunks') \<and>
     PTraceFriCounter t = PTraceFriCounter s3 \<and>
     PCompositionFriCounter t = PCompositionFriCounter s3 \<and>
     PAlphaCounter t = PAlphaCounter s3 \<and>
     PQueryCounter t = PQueryCounter s3 + n"
    by (rule Suc.IH[OF rest_bound rest_out])
  show ?case
    unfolding chunks_eq
    using s3_fields rest_alignment
    by (simp add: foldl_append)
qed

lemma staged_query_program_outcome_with_raws:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and outcome:
      "Some (chunks, t) \<in>
        set_dist (execute (staged_query_program A i n) s)"
  shows
    "\<exists>raw_idxs query_idxs.
      length raw_idxs = n \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length chunks = n \<and>
      PTranscript t = PTranscript s @ List.concat chunks \<and>
      PState t = state_after_query_chunks (PState s) chunks n \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s + n \<and>
      (\<forall>j < n.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + j)
            (state_after_query_chunks (PState s) chunks j)) =
          Some (raw_idxs ! j)) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale)"
  using bound outcome
proof (induction n arbitrary: i chunks s t)
  case 0
  then show ?case
    by (intro exI[of _ "[]"])
      (simp add: state_after_query_chunks_def hash_ext_refl)
next
  case (Suc n)
  from staged_query_program_Suc_outcomeE[OF Suc.prems(2)]
  obtain raw chunk chunks' s1 s2 s3 where
    challenge_out:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and stage_out:
      "Some (chunk, s2) \<in>
        set_dist (execute (query_opening_stage A i raw) s1)"
    and record_out:
      "Some ((), s3) \<in>
        set_dist (execute (record_staged_messages chunk) s2)"
    and rest_out:
      "Some (chunks', t) \<in>
        set_dist (execute (staged_query_program A (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
    .
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have challenge:
    "s \<le> s1 \<and>
     PState s1 = PState s \<and>
     PTranscript s1 = PTranscript s \<and>
     fmlookup (HashMap s1)
       (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule receive_query_index_challenge_outcome[OF challenge_out])
  have challenge_counters:
    "PQueryCounter s1 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF challenge_out]
    by simp
  have ext_s1_s2: "s1 \<le> s2"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have stage_fields:
    "PState s2 = PState s1 \<and>
     PTranscript s2 = PTranscript s1 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have s3_eq:
    "s3 = s2\<lparr>
      PState := foldl concat (PState s2) chunk,
      PTranscript := PTranscript s2 @ chunk\<rparr>"
    by (rule record_staged_messages_outcome[OF record_out])
  have ext_s2_s3: "s2 \<le> s3"
    unfolding s3_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have s3_fields:
    "PState s3 = foldl concat (PState s) chunk \<and>
     PTranscript s3 = PTranscript s @ chunk \<and>
     PQueryCounter s3 = Suc (PQueryCounter s)"
    unfolding s3_eq using challenge stage_fields challenge_counters by simp
  have rest_bound:
    "Suc i + n \<le> length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  from Suc.IH[OF rest_bound rest_out]
  obtain raw_tail idx_tail where
    len_raw_tail: "length raw_tail = n"
    and idx_tail_def:
      "idx_tail = map (\<lambda>raw. index (to_nat raw)) raw_tail"
    and len_chunks_tail: "length chunks' = n"
    and tr_tail:
      "PTranscript t = PTranscript s3 @ List.concat chunks'"
    and st_tail:
      "PState t = state_after_query_chunks (PState s3) chunks' n"
    and ext_s3_t: "s3 \<le> t"
    and query_count_tail:
      "PQueryCounter t = PQueryCounter s3 + n"
    and lookup_tail:
      "\<And>j. j < n \<Longrightarrow>
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s3 + j)
            (state_after_query_chunks (PState s3) chunks' j)) =
          Some (raw_tail ! j)"
    and idx_tail_bound:
      "\<forall>idx \<in> set idx_tail. idx < clength * scale"
    by blast
  let ?raws = "raw # raw_tail"
  let ?idxs = "index (to_nat raw) # idx_tail"
  let ?chunks = "chunk # chunks'"
  have idxs_def: "?idxs = map (\<lambda>raw. index (to_nat raw)) ?raws"
    using idx_tail_def by simp
  have tr_all:
    "PTranscript t = PTranscript s @ List.concat ?chunks"
    using tr_tail s3_fields by simp
  have state_shift:
    "\<And>j. state_after_query_chunks (PState s) ?chunks (Suc j) =
      state_after_query_chunks (PState s3) chunks' j"
    using s3_fields unfolding state_after_query_chunks_def by simp
  have st_all:
    "PState t = state_after_query_chunks (PState s) ?chunks (Suc n)"
    using st_tail state_shift[of n] by simp
  have ext_s_s2: "s \<le> s2"
    by (rule hash_ext_trans[OF conjunct1[OF challenge] ext_s1_s2])
  have ext_s_s3: "s \<le> s3"
    by (rule hash_ext_trans[OF ext_s_s2 ext_s2_s3])
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_s3 ext_s3_t])
  have query_count_all: "PQueryCounter t = PQueryCounter s + Suc n"
    using query_count_tail s3_fields by simp
  have ext_s1_t: "s1 \<le> t"
    by (rule hash_ext_trans[OF ext_s1_s2])
      (rule hash_ext_trans[OF ext_s2_s3 ext_s3_t])
  have lookup_head_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) =
      Some raw"
    by (rule hash_extension_lookup[OF conjunct2[OF conjunct2[OF conjunct2[OF challenge]]] ext_s1_t])
  have lookup_all:
    "\<And>j. j < Suc n \<Longrightarrow>
      fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + j)
          (state_after_query_chunks (PState s) ?chunks j)) =
        Some (?raws ! j)"
  proof -
    fix j
    assume j_bound: "j < Suc n"
    show
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + j)
          (state_after_query_chunks (PState s) ?chunks j)) =
        Some (?raws ! j)"
    proof (cases j)
      case 0
      then show ?thesis
        using lookup_head_t unfolding state_after_query_chunks_def by simp
    next
      case (Suc k)
      then show ?thesis
        using lookup_tail[of k] j_bound state_shift[of k] s3_fields by simp
    qed
  qed
  have idx_bound_all:
    "\<forall>idx \<in> set ?idxs. idx < clength * scale"
    using idx_tail_bound index_less_domain by auto
  show ?case
    unfolding chunks_eq
    apply (intro exI[of _ ?raws] exI[of _ ?idxs] conjI)
            apply (simp add: len_raw_tail)
           apply (rule idxs_def)
          apply (simp add: len_chunks_tail)
         apply (rule tr_all)
        apply (rule st_all)
       apply (rule ext_s_t)
      apply (rule query_count_all)
     apply (intro allI impI, rule lookup_all, assumption)
    using idx_bound_all by simp
qed

lemma checked_staged_query_program_chunks_match_verifier:
  assumes outcome:
    "Some (chunks, t) \<in>
      set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            i n) s)"
  shows
    "\<exists>raw_idxs query_idxs.
      length raw_idxs = n \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length chunks = n \<and>
      (\<forall>j < n.
        verifier_query_round_chunk (query_idxs ! j)
          trace_roots composition_roots (chunks ! j)) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale)"
  using outcome
proof (induction n arbitrary: i chunks s t)
  case 0
  then show ?case
    by (intro exI[of _ "[]"] exI[of _ "[]"]) simp
next
  case (Suc n)
  obtain raw chunk chunks' s1 s2 s3 where
    chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and rest_out:
      "Some (chunks', t) \<in>
        set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
  proof (rule checked_staged_query_program_Suc_outcomeE[OF Suc.prems])
    fix raw chunk chunks' s1 s2 s3
    assume shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
      and rest:
        "Some (chunks', t) \<in>
          set_dist
            (execute
              (checked_staged_query_program A trace_roots composition_roots
                (Suc i) n) s3)"
      and chunks: "chunks = chunk # chunks'"
    show ?thesis
      by (rule that[OF shape rest chunks])
  qed
  from Suc.IH[OF rest_out]
  obtain raw_tail idx_tail where
    len_raw_tail: "length raw_tail = n"
    and idx_tail_def:
      "idx_tail = map (\<lambda>raw. index (to_nat raw)) raw_tail"
    and len_chunks_tail: "length chunks' = n"
    and tail_shape:
      "\<forall>j < n.
        verifier_query_round_chunk (idx_tail ! j)
          trace_roots composition_roots (chunks' ! j)"
    and idx_tail_bound:
      "\<forall>idx \<in> set idx_tail. idx < clength * scale"
    by blast
  let ?raws = "raw # raw_tail"
  let ?idxs = "index (to_nat raw) # idx_tail"
  have idxs_def: "?idxs = map (\<lambda>raw. index (to_nat raw)) ?raws"
    using idx_tail_def by simp
  have shape_all:
    "\<forall>j < Suc n.
      verifier_query_round_chunk (?idxs ! j)
        trace_roots composition_roots ((chunk # chunks') ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show "verifier_query_round_chunk (?idxs ! j)
        trace_roots composition_roots ((chunk # chunks') ! j)"
    proof (cases j)
      case 0
      then show ?thesis
        using chunk_shape by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      then show ?thesis
        using tail_shape Suc by simp
    qed
  qed
  have idx_bound_all:
    "\<forall>idx \<in> set ?idxs. idx < clength * scale"
    using idx_tail_bound index_less_domain by auto
  show ?case
    unfolding chunks_eq
    by (intro exI[of _ ?raws] exI[of _ ?idxs] conjI)
      (use len_raw_tail idxs_def len_chunks_tail shape_all idx_bound_all
        in simp_all)
qed

lemma checked_staged_query_program_outcome_with_raws:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and outcome:
      "Some (chunks, t) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              i n) s)"
  shows
    "\<exists>raw_idxs query_idxs.
      length raw_idxs = n \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length chunks = n \<and>
      PTranscript t = PTranscript s @ List.concat chunks \<and>
      PState t = state_after_query_chunks (PState s) chunks n \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s + n \<and>
      (\<forall>j < n.
        verifier_query_round_chunk (query_idxs ! j)
          trace_roots composition_roots (chunks ! j)) \<and>
      (\<forall>j < n.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + j)
            (state_after_query_chunks (PState s) chunks j)) =
          Some (raw_idxs ! j)) \<and>
  (\<forall>idx \<in> set query_idxs. idx < clength * scale)"
  using bound outcome
proof (induction n arbitrary: i chunks s t)
  case 0
  then show ?case
    by (intro exI[of _ "[]"] exI[of _ "[]"])
      (simp add: state_after_query_chunks_def hash_ext_refl)
next
  case (Suc n)
  from checked_staged_query_program_Suc_outcomeE[OF Suc.prems(2)]
  obtain raw chunk chunks' s1 s2 s3 where
    challenge_out:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and stage_out:
      "Some (chunk, s2) \<in>
        set_dist (execute (query_opening_stage A i raw) s1)"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and record_out:
      "Some ((), s3) \<in>
        set_dist (execute (record_staged_messages chunk) s2)"
    and rest_out:
      "Some (chunks', t) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
    .
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have challenge:
    "s \<le> s1 \<and>
     PState s1 = PState s \<and>
     PTranscript s1 = PTranscript s \<and>
     fmlookup (HashMap s1)
       (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule receive_query_index_challenge_outcome[OF challenge_out])
  have challenge_counters:
    "PQueryCounter s1 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF challenge_out]
    by simp
  have ext_s1_s2: "s1 \<le> s2"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have stage_fields:
    "PState s2 = PState s1 \<and>
     PTranscript s2 = PTranscript s1 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have s3_eq:
    "s3 = s2\<lparr>
      PState := foldl concat (PState s2) chunk,
      PTranscript := PTranscript s2 @ chunk\<rparr>"
    by (rule record_staged_messages_outcome[OF record_out])
  have ext_s2_s3: "s2 \<le> s3"
    unfolding s3_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have s3_fields:
    "PState s3 = foldl concat (PState s) chunk \<and>
     PTranscript s3 = PTranscript s @ chunk \<and>
     PQueryCounter s3 = Suc (PQueryCounter s)"
    unfolding s3_eq using challenge stage_fields challenge_counters by simp
  have rest_bound:
    "Suc i + n \<le> length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  from Suc.IH[OF rest_bound rest_out]
  obtain raw_tail idx_tail where
    len_raw_tail: "length raw_tail = n"
    and idx_tail_def:
      "idx_tail = map (\<lambda>raw. index (to_nat raw)) raw_tail"
    and len_chunks_tail: "length chunks' = n"
    and tr_tail:
      "PTranscript t = PTranscript s3 @ List.concat chunks'"
    and st_tail:
      "PState t = state_after_query_chunks (PState s3) chunks' n"
    and ext_s3_t: "s3 \<le> t"
    and query_count_tail:
      "PQueryCounter t = PQueryCounter s3 + n"
    and chunk_shape_tail:
      "\<And>j. j < n \<Longrightarrow>
        verifier_query_round_chunk (idx_tail ! j)
          trace_roots composition_roots (chunks' ! j)"
    and lookup_tail:
      "\<And>j. j < n \<Longrightarrow>
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s3 + j)
            (state_after_query_chunks (PState s3) chunks' j)) =
        Some (raw_tail ! j)"
    and idx_tail_bound:
      "\<forall>idx \<in> set idx_tail. idx < clength * scale"
    by blast
  let ?raws = "raw # raw_tail"
  let ?idxs = "index (to_nat raw) # idx_tail"
  let ?chunks = "chunk # chunks'"
  have idxs_def: "?idxs = map (\<lambda>raw. index (to_nat raw)) ?raws"
    using idx_tail_def by simp
  have tr_all:
    "PTranscript t = PTranscript s @ List.concat ?chunks"
    using tr_tail s3_fields by simp
  have state_shift:
    "\<And>j. state_after_query_chunks (PState s) ?chunks (Suc j) =
      state_after_query_chunks (PState s3) chunks' j"
    using s3_fields unfolding state_after_query_chunks_def by simp
  have st_all:
    "PState t = state_after_query_chunks (PState s) ?chunks (Suc n)"
    using st_tail state_shift[of n] by simp
  have ext_s_s2: "s \<le> s2"
    by (rule hash_ext_trans[OF conjunct1[OF challenge] ext_s1_s2])
  have ext_s_s3: "s \<le> s3"
    by (rule hash_ext_trans[OF ext_s_s2 ext_s2_s3])
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_s3 ext_s3_t])
  have query_count_all: "PQueryCounter t = PQueryCounter s + Suc n"
    using query_count_tail s3_fields by simp
  have ext_s1_t: "s1 \<le> t"
    by (rule hash_ext_trans[OF ext_s1_s2])
      (rule hash_ext_trans[OF ext_s2_s3 ext_s3_t])
  have lookup_head_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) =
      Some raw"
    by (rule hash_extension_lookup
        [OF conjunct2[OF conjunct2[OF conjunct2[OF challenge]]] ext_s1_t])
  have chunk_shape_all:
    "\<And>j. j < Suc n \<Longrightarrow>
      verifier_query_round_chunk (?idxs ! j)
        trace_roots composition_roots (?chunks ! j)"
  proof -
    fix j
    assume j_bound: "j < Suc n"
    show
      "verifier_query_round_chunk (?idxs ! j)
        trace_roots composition_roots (?chunks ! j)"
    proof (cases j)
      case 0
      then show ?thesis
        using chunk_shape by simp
    next
      case (Suc k)
      then show ?thesis
        using chunk_shape_tail[of k] j_bound by simp
    qed
  qed
  have lookup_all:
    "\<And>j. j < Suc n \<Longrightarrow>
      fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + j)
          (state_after_query_chunks (PState s) ?chunks j)) =
        Some (?raws ! j)"
  proof -
    fix j
    assume j_bound: "j < Suc n"
    show
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + j)
          (state_after_query_chunks (PState s) ?chunks j)) =
        Some (?raws ! j)"
    proof (cases j)
      case 0
      then show ?thesis
        using lookup_head_t unfolding state_after_query_chunks_def by simp
    next
      case (Suc k)
      then show ?thesis
        using lookup_tail[of k] j_bound state_shift[of k] s3_fields by simp
    qed
  qed
  have idx_bound_all:
    "\<forall>idx \<in> set ?idxs. idx < clength * scale"
    using idx_tail_bound index_less_domain by auto
  show ?case
    unfolding chunks_eq
    by (intro exI[of _ ?raws] exI[of _ ?idxs] conjI)
      (use len_raw_tail idxs_def len_chunks_tail tr_all st_all ext_s_t
        query_count_all chunk_shape_all lookup_all idx_bound_all in simp_all)
qed

lemma checked_staged_query_program_chunks_match_verifier_lengths:
  assumes outcome:
    "Some (chunks, t) \<in>
      set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            i rounds) s)"
  shows
    "\<exists>query_idxs.
      staged_query_chunks_match_verifier_lengths
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = chunks\<rparr>
        query_idxs"
proof -
  from checked_staged_query_program_chunks_match_verifier[OF outcome]
  obtain raw_idxs query_idxs where
    len_chunks: "length chunks = rounds"
    and chunk_shape:
      "\<forall>j < rounds.
        verifier_query_round_chunk (query_idxs ! j)
          trace_roots composition_roots (chunks ! j)"
    by blast
  have chunk_lens:
    "\<forall>j < rounds.
      length (chunks ! j) =
        verifier_query_round_transcript_length (query_idxs ! j)
          trace_roots composition_roots"
    using chunk_shape verifier_query_round_chunk_length by blast
  show ?thesis
    by (intro exI[of _ query_idxs])
      (use len_chunks chunk_lens in
        \<open>simp add: staged_query_chunks_match_verifier_lengths_def\<close>)
qed

lemma checked_staged_transcript_program_query_chunks_match_verifier_lengths:
  assumes outcome:
    "Some (data, t) \<in>
      set_dist
        (execute (checked_staged_transcript_program A) s)"
  shows "\<exists>query_idxs.
    staged_query_chunks_match_verifier_lengths data query_idxs"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 s12 query_chunks where
    query_out:
      "Some (query_chunks, s12) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              0 rounds)
            s11)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
    unfolding checked_staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  show ?thesis
    unfolding data_eq
    by (rule checked_staged_query_program_chunks_match_verifier_lengths
        [OF query_out])
qed

lemma checked_staged_security_experiment_with_data_state_query_lengthsE:
  assumes outcome:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_data_state A)
          initial_state)"
  obtains query_idxs where
    "staged_query_chunks_match_verifier_lengths data query_idxs"
proof -
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF outcome]
  have builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A) initial_state)"
    by blast
  from checked_staged_transcript_program_query_chunks_match_verifier_lengths
      [OF builder]
  obtain query_idxs where
    "staged_query_chunks_match_verifier_lengths data query_idxs"
    by blast
  then show ?thesis
    by (rule that)
qed

lemma verifier_query_round_program_replays_shaped_chunk:
  assumes outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and lookup:
      "fmlookup (HashMap s)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        (map snd f_fl) (map snd fl) chunk"
    and transcript: "PTranscript s = chunk @ rest"
  shows
    "PTranscript t = rest \<and>
     PState t = foldl concat (PState s) chunk \<and>
     PQueryCounter t = Suc (PQueryCounter s) \<and>
     s \<le> t"
proof -
  from verifier_query_round_program_outcome[OF outcome]
  obtain raw' idx' chunk' where
    idx'_def: "idx' = index (to_nat raw')"
    and chunk'_shape:
      "verifier_query_round_chunk idx' (map snd f_fl) (map snd fl)
        chunk'"
    and transcript': "PTranscript s = chunk' @ PTranscript t"
    and state_t: "PState t = foldl concat (PState s) chunk'"
    and ext: "s \<le> t"
    and counter_t: "PQueryCounter t = Suc (PQueryCounter s)"
    and lookup_t:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw'"
    by blast
  have lookup_t_from_s:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF lookup ext])
  have raw'_eq: "raw' = raw"
    using lookup_t lookup_t_from_s by simp
  have idx'_eq: "idx' = index (to_nat raw)"
    unfolding idx'_def raw'_eq by simp
  have len_eq: "length chunk' = length chunk"
    using verifier_query_round_chunk_length[OF chunk'_shape]
      verifier_query_round_chunk_length[OF chunk_shape]
    unfolding idx'_eq by simp
  have chunk'_eq: "chunk' = chunk"
  proof -
    have "chunk' = take (length chunk') (PTranscript s)"
      using transcript' by simp
    also have "... = chunk"
      using transcript len_eq by simp
    finally show ?thesis .
  qed
  have transcript_t: "PTranscript t = rest"
    using transcript' transcript unfolding chunk'_eq by simp
  show ?thesis
    using transcript_t state_t counter_t ext unfolding chunk'_eq by simp
qed

lemma ntimes_verifier_query_round_program_replays_shaped_chunks:
  assumes outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              n) s)"
    and len_raw: "length raw_idxs = n"
    and len_chunks: "length chunks = n"
    and chunk_shape:
      "\<And>i. i < n \<Longrightarrow>
        verifier_query_round_chunk (index (to_nat (raw_idxs ! i)))
          (map snd f_fl) (map snd fl) (chunks ! i)"
    and lookup:
      "\<And>i. i < n \<Longrightarrow>
        fmlookup (HashMap s)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) chunks i)) =
        Some (raw_idxs ! i)"
    and transcript: "PTranscript s = List.concat chunks @ rest"
  shows
    "PTranscript t = rest \<and>
     PState t = state_after_query_chunks (PState s) chunks n \<and>
     PQueryCounter t = PQueryCounter s + n \<and>
     s \<le> t"
  using outcome len_raw len_chunks chunk_shape lookup transcript
proof (induction n arbitrary: s results t raw_idxs chunks rest)
  case 0
  then show ?case
    by (simp add: state_after_query_chunks_def hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(2) obtain raw raw_tail where raw_eq:
    "raw_idxs = raw # raw_tail"
    by (cases raw_idxs) simp_all
  from Suc.prems(3) obtain chunk chunk_tail where chunks_eq:
    "chunks = chunk # chunk_tail"
    by (cases chunks) simp_all
  from Suc.prems(1) obtain u s1 results' where
    head:
      "Some (u, s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and tail:
      "Some (results', t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              n) s1)"
    and results_eq: "results = u # results'"
    by (auto elim!: set_dist_bindE)
  have u_eq: "u = ()"
    by (cases u) simp
  have len_raw_tail: "length raw_tail = n"
    using Suc.prems(2) unfolding raw_eq by simp
  have len_chunk_tail: "length chunk_tail = n"
    using Suc.prems(3) unfolding chunks_eq by simp
  have head_shape:
    "verifier_query_round_chunk (index (to_nat raw))
      (map snd f_fl) (map snd fl) chunk"
    using Suc.prems(4)[of 0] unfolding raw_eq chunks_eq by simp
  have head_lookup:
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) =
      Some raw"
    using Suc.prems(5)[of 0]
    unfolding raw_eq chunks_eq state_after_query_chunks_def by simp
  have head_transcript:
    "PTranscript s = chunk @ (List.concat chunk_tail @ rest)"
    using Suc.prems(6) unfolding chunks_eq by simp
  from verifier_query_round_program_replays_shaped_chunk
      [OF head[unfolded u_eq] head_lookup head_shape head_transcript]
  have replay_head:
    "PTranscript s1 = List.concat chunk_tail @ rest \<and>
     PState s1 = foldl concat (PState s) chunk \<and>
     PQueryCounter s1 = Suc (PQueryCounter s) \<and>
     s \<le> s1" .
  have tail_shape:
    "\<And>i. i < n \<Longrightarrow>
      verifier_query_round_chunk (index (to_nat (raw_tail ! i)))
        (map snd f_fl) (map snd fl) (chunk_tail ! i)"
  proof -
    fix i
    assume i_bound: "i < n"
    then show
      "verifier_query_round_chunk (index (to_nat (raw_tail ! i)))
        (map snd f_fl) (map snd fl) (chunk_tail ! i)"
      using Suc.prems(4)[of "Suc i"]
      unfolding raw_eq chunks_eq by simp
  qed
  have state_shift:
    "\<And>i. state_after_query_chunks (PState s) (chunk # chunk_tail)
        (Suc i) =
      state_after_query_chunks (PState s1) chunk_tail i"
    using replay_head unfolding state_after_query_chunks_def by simp
  have tail_lookup:
    "\<And>i. i < n \<Longrightarrow>
      fmlookup (HashMap s1)
        (QueryIndexChallenge (PQueryCounter s1 + i)
          (state_after_query_chunks (PState s1) chunk_tail i)) =
      Some (raw_tail ! i)"
  proof -
    fix i
    assume i_bound: "i < n"
    have lookup_s:
      "fmlookup (HashMap s)
        (QueryIndexChallenge (PQueryCounter s + Suc i)
          (state_after_query_chunks (PState s) (chunk # chunk_tail)
            (Suc i))) =
        Some (raw_tail ! i)"
      using Suc.prems(5)[of "Suc i"] i_bound
      unfolding raw_eq chunks_eq by simp
    have key_eq:
      "QueryIndexChallenge (PQueryCounter s + Suc i)
          (state_after_query_chunks (PState s) (chunk # chunk_tail)
            (Suc i)) =
       QueryIndexChallenge (PQueryCounter s1 + i)
          (state_after_query_chunks (PState s1) chunk_tail i)"
      using replay_head state_shift[of i] by simp
    show
      "fmlookup (HashMap s1)
        (QueryIndexChallenge (PQueryCounter s1 + i)
          (state_after_query_chunks (PState s1) chunk_tail i)) =
      Some (raw_tail ! i)"
      using hash_extension_lookup[OF lookup_s conjunct2[OF conjunct2[OF conjunct2[OF replay_head]]]]
      unfolding key_eq .
  qed
  from Suc.IH[OF tail len_raw_tail len_chunk_tail tail_shape tail_lookup
      conjunct1[OF replay_head]]
  have replay_tail:
    "PTranscript t = rest \<and>
     PState t = state_after_query_chunks (PState s1) chunk_tail n \<and>
     PQueryCounter t = PQueryCounter s1 + n \<and>
     s1 \<le> t" .
  have state_all:
    "PState t =
      state_after_query_chunks (PState s) (chunk # chunk_tail) (Suc n)"
    using replay_tail state_shift[of n] by simp
  have counter_all: "PQueryCounter t = PQueryCounter s + Suc n"
    using replay_head replay_tail by simp
  have ext_all: "s \<le> t"
    using replay_head replay_tail by (blast intro: hash_ext_trans)
  show ?case
    unfolding raw_eq chunks_eq
    using replay_tail state_all counter_all ext_all by simp
qed

lemma checked_staged_query_program_ntimes_replay:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and checked:
      "Some (chunks, attacker_t) \<in>
        set_dist
          (execute
            (checked_staged_query_program A (map snd f_fl) (map snd fl)
              i n) attacker_s)"
    and verifier:
      "Some (results, verifier_t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              n) verifier_s)"
    and hash_ext: "attacker_t \<le> verifier_s"
    and state_eq: "PState verifier_s = PState attacker_s"
    and counter_eq: "PQueryCounter verifier_s = PQueryCounter attacker_s"
    and transcript_eq:
      "PTranscript verifier_s = List.concat chunks @ rest"
  shows
    "PTranscript verifier_t = rest \<and>
     PState verifier_t =
      state_after_query_chunks (PState verifier_s) chunks n \<and>
     PQueryCounter verifier_t = PQueryCounter verifier_s + n \<and>
     verifier_s \<le> verifier_t"
proof -
  from checked_staged_query_program_outcome_with_raws
      [OF controlled bound checked]
  obtain raw_idxs query_idxs where
    len_raw: "length raw_idxs = n"
    and query_idxs_def:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length chunks = n"
    and chunk_shape:
      "\<And>j. j < n \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! j)
          (map snd f_fl) (map snd fl) (chunks ! j)"
    and lookup:
      "\<And>j. j < n \<Longrightarrow>
        fmlookup (HashMap attacker_t)
          (QueryIndexChallenge (PQueryCounter attacker_s + j)
            (state_after_query_chunks (PState attacker_s) chunks j)) =
        Some (raw_idxs ! j)"
    by blast
  have chunk_shape_raw:
    "\<And>j. j < n \<Longrightarrow>
      verifier_query_round_chunk (index (to_nat (raw_idxs ! j)))
        (map snd f_fl) (map snd fl) (chunks ! j)"
  proof -
    fix j
    assume j_bound: "j < n"
    have "query_idxs ! j = index (to_nat (raw_idxs ! j))"
      using query_idxs_def len_raw j_bound by simp
    then show
      "verifier_query_round_chunk (index (to_nat (raw_idxs ! j)))
        (map snd f_fl) (map snd fl) (chunks ! j)"
      using chunk_shape[OF j_bound] by simp
  qed
  have lookup_verifier:
    "\<And>j. j < n \<Longrightarrow>
      fmlookup (HashMap verifier_s)
        (QueryIndexChallenge (PQueryCounter verifier_s + j)
          (state_after_query_chunks (PState verifier_s) chunks j)) =
      Some (raw_idxs ! j)"
  proof -
    fix j
    assume j_bound: "j < n"
    have lookup_attacker:
      "fmlookup (HashMap attacker_t)
        (QueryIndexChallenge (PQueryCounter attacker_s + j)
          (state_after_query_chunks (PState attacker_s) chunks j)) =
      Some (raw_idxs ! j)"
      by (rule lookup[OF j_bound])
    have lookup_verifier_s:
      "fmlookup (HashMap verifier_s)
        (QueryIndexChallenge (PQueryCounter attacker_s + j)
          (state_after_query_chunks (PState attacker_s) chunks j)) =
      Some (raw_idxs ! j)"
      by (rule hash_extension_lookup[OF lookup_attacker hash_ext])
    show
      "fmlookup (HashMap verifier_s)
        (QueryIndexChallenge (PQueryCounter verifier_s + j)
          (state_after_query_chunks (PState verifier_s) chunks j)) =
      Some (raw_idxs ! j)"
      using lookup_verifier_s state_eq counter_eq by simp
  qed
  show ?thesis
    by (rule ntimes_verifier_query_round_program_replays_shaped_chunks
        [OF verifier len_raw len_chunks chunk_shape_raw lookup_verifier
          transcript_eq])
qed

lemma checked_staged_transcript_program_outcome_shape:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
  shows
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     ceil_log (to_nat (staged_degree data) + 1) \<le>
       ceil_log (maxDegree + 1) \<and>
     length (staged_query_chunks data) = rounds"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 s12 query_chunks where
    trace_out:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s5)"
    and degree_eq: "staged_degree data = dg"
    and assert_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1))) s8)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s9)"
    and query_out:
      "Some (query_chunks, s12) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              0 rounds)
            s11)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
    unfolding checked_staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have trace_len:
    "length trace_roots = ceil_log clength \<and>
     length trace_bs = ceil_log clength"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have alignment:
      "length trace_roots = ceil_log clength \<and>
       length trace_bs = length ([] :: 'f list) + ceil_log clength \<and>
       PTranscript s3 = PTranscript s2 @ trace_roots \<and>
       PState s3 = foldl concat (PState s2) trace_roots \<and>
       s2 \<le> s3 \<and>
       PTraceFriCounter s3 = PTraceFriCounter s2 + ceil_log clength \<and>
       PCompositionFriCounter s3 = PCompositionFriCounter s2 \<and>
       PAlphaCounter s3 = PAlphaCounter s2 \<and>
       PQueryCounter s3 = PQueryCounter s2 \<and>
       (\<forall>j < ceil_log clength.
          fmlookup (HashMap s3)
            (TraceFriChallenge (PTraceFriCounter s2 + j)
              (foldl concat (PState s2) (take (Suc j) trace_roots))) =
          Some (trace_bs ! (length ([] :: 'f list) + j)))"
      by (rule staged_trace_fri_program_alignment
          [OF controlled len trace_out])
    then show ?thesis by simp
  qed
  have alpha_len: "length as = length spec"
    using staged_alpha_program_alignment[OF alpha_out] by simp
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_len:
    "length composition_roots = ceil_log (to_nat dg + 1) \<and>
     length composition_bs = ceil_log (to_nat dg + 1)"
  proof -
    have len:
      "0 + ceil_log (to_nat dg + 1) \<le>
        length (composition_fri_budgets budgets)"
      using wf round_bound unfolding staged_budget_wellformed_def by simp
    have alignment:
      "length composition_roots = ceil_log (to_nat dg + 1) \<and>
       length composition_bs =
         length ([] :: 'f list) + ceil_log (to_nat dg + 1) \<and>
       PTranscript s10 = PTranscript s9 @ composition_roots \<and>
       PState s10 = foldl concat (PState s9) composition_roots \<and>
       s9 \<le> s10 \<and>
       PTraceFriCounter s10 = PTraceFriCounter s9 \<and>
       PCompositionFriCounter s10 =
         PCompositionFriCounter s9 + ceil_log (to_nat dg + 1) \<and>
       PAlphaCounter s10 = PAlphaCounter s9 \<and>
       PQueryCounter s10 = PQueryCounter s9 \<and>
       (\<forall>j < ceil_log (to_nat dg + 1).
          fmlookup (HashMap s10)
            (CompositionFriChallenge (PCompositionFriCounter s9 + j)
              (foldl concat (PState s9) (take (Suc j) composition_roots))) =
          Some (composition_bs ! (length ([] :: 'f list) + j)))"
      by (rule staged_composition_fri_program_alignment
          [OF controlled len composition_out])
    then show ?thesis by simp
  qed
  have query_len: "length query_chunks = rounds"
    using checked_staged_query_program_chunks_match_verifier[OF query_out]
    by blast
  show ?thesis
    unfolding data_eq degree_eq
    using trace_len alpha_len composition_len round_bound query_len by simp
qed

lemma checked_staged_transcript_program_outcome_header_transcript:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
  shows
    "verifier_header_transcript
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
proof -
  have shape:
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     ceil_log (to_nat (staged_degree data) + 1) \<le>
       ceil_log (maxDegree + 1) \<and>
     length (staged_query_chunks data) = rounds"
    by (rule checked_staged_transcript_program_outcome_shape
        [OF wf controlled outcome])
  show ?thesis
    by (rule staged_proof_transcript_verifier_header_transcript)
      (use shape in simp_all)
qed

lemma staged_transcript_program_outcome_shape:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (staged_transcript_program A)
            adversary_initial_state)"
  shows
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     ceil_log (to_nat (staged_degree data) + 1) \<le>
       ceil_log (maxDegree + 1) \<and>
     length (staged_query_chunks data) = rounds"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 s12 query_chunks where
    trace_out:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s5)"
    and degree_eq: "staged_degree data = dg"
    and assert_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1))) s8)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s9)"
    and query_out:
      "Some (query_chunks, s12) \<in>
        set_dist (execute (staged_query_program A 0 rounds) s11)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
    unfolding staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have trace_len:
    "length trace_roots = ceil_log clength \<and>
     length trace_bs = ceil_log clength"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have alignment:
      "length trace_roots = ceil_log clength \<and>
       length trace_bs = length ([] :: 'f list) + ceil_log clength \<and>
       PTranscript s3 = PTranscript s2 @ trace_roots \<and>
       PState s3 = foldl concat (PState s2) trace_roots \<and>
       s2 \<le> s3 \<and>
       PTraceFriCounter s3 = PTraceFriCounter s2 + ceil_log clength \<and>
       PCompositionFriCounter s3 = PCompositionFriCounter s2 \<and>
       PAlphaCounter s3 = PAlphaCounter s2 \<and>
       PQueryCounter s3 = PQueryCounter s2 \<and>
       (\<forall>j < ceil_log clength.
          fmlookup (HashMap s3)
            (TraceFriChallenge (PTraceFriCounter s2 + j)
              (foldl concat (PState s2) (take (Suc j) trace_roots))) =
          Some (trace_bs ! (length ([] :: 'f list) + j)))"
      by (rule staged_trace_fri_program_alignment
          [OF controlled len trace_out])
    then show ?thesis by simp
  qed
  have alpha_len: "length as = length spec"
    using staged_alpha_program_alignment[OF alpha_out] by simp
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_len:
    "length composition_roots = ceil_log (to_nat dg + 1) \<and>
     length composition_bs = ceil_log (to_nat dg + 1)"
  proof -
    have len:
      "0 + ceil_log (to_nat dg + 1) \<le>
        length (composition_fri_budgets budgets)"
      using wf round_bound unfolding staged_budget_wellformed_def by simp
    have alignment:
      "length composition_roots = ceil_log (to_nat dg + 1) \<and>
       length composition_bs =
         length ([] :: 'f list) + ceil_log (to_nat dg + 1) \<and>
       PTranscript s10 = PTranscript s9 @ composition_roots \<and>
       PState s10 = foldl concat (PState s9) composition_roots \<and>
       s9 \<le> s10 \<and>
       PTraceFriCounter s10 = PTraceFriCounter s9 \<and>
       PCompositionFriCounter s10 =
         PCompositionFriCounter s9 + ceil_log (to_nat dg + 1) \<and>
       PAlphaCounter s10 = PAlphaCounter s9 \<and>
       PQueryCounter s10 = PQueryCounter s9 \<and>
       (\<forall>j < ceil_log (to_nat dg + 1).
          fmlookup (HashMap s10)
            (CompositionFriChallenge (PCompositionFriCounter s9 + j)
              (foldl concat (PState s9) (take (Suc j) composition_roots))) =
          Some (composition_bs ! (length ([] :: 'f list) + j)))"
      by (rule staged_composition_fri_program_alignment
          [OF controlled len composition_out])
    then show ?thesis by simp
  qed
  have query_len:
    "length query_chunks = rounds"
  proof -
    have len: "0 + rounds \<le> length (query_opening_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have alignment:
      "length query_chunks = rounds \<and>
       PTranscript s12 = PTranscript s11 @ List.concat query_chunks \<and>
       PState s12 =
         foldl concat (PState s11) (List.concat query_chunks) \<and>
       PTraceFriCounter s12 = PTraceFriCounter s11 \<and>
       PCompositionFriCounter s12 = PCompositionFriCounter s11 \<and>
       PAlphaCounter s12 = PAlphaCounter s11 \<and>
       PQueryCounter s12 = PQueryCounter s11 + rounds"
      by (rule staged_query_program_alignment[OF controlled len query_out])
    then show ?thesis by simp
  qed
  show ?thesis
    unfolding data_eq degree_eq
    using trace_len alpha_len composition_len round_bound query_len by simp
qed

lemma hash_target_program_outcome_extension:
  assumes target: "hash_target_program B q m"
    and outcome: "Some (x, t) \<in> set_dist (execute m s)"
  shows "s \<le> t"
  using hash_target_program_extension[OF target] outcome
  unfolding hash_extension_preserving_def by blast

lemma staged_transcript_program_outcome_query_lookups:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (staged_transcript_program A)
            adversary_initial_state)"
  shows
    "\<exists>raw_idxs query_idxs.
      length raw_idxs = rounds \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length (staged_query_chunks data) = rounds \<and>
      PState attacker_state =
        state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) rounds \<and>
      PQueryCounter attacker_state = rounds \<and>
      (\<forall>j < rounds.
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
          Some (raw_idxs ! j)) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale)"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 s12 query_chunks where
    root_out:
      "Some (fr, s1) \<in>
        set_dist (execute (trace_root_stage A) adversary_initial_state)"
    and record_root:
      "Some ((), s2) \<in> set_dist (execute (record_staged_message fr) s1)"
    and trace_out:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and final_out:
      "Some (trace_final, s4) \<in>
        set_dist (execute (trace_final_stage A trace_bs) s3)"
    and record_final:
      "Some ((), s5) \<in>
        set_dist (execute (record_staged_message trace_final) s4)"
    and alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s5)"
    and degree_out:
      "Some (dg, s7) \<in> set_dist (execute (degree_stage A as) s6)"
    and record_degree:
      "Some ((), s8) \<in> set_dist (execute (record_staged_message dg) s7)"
    and assert_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1))) s8)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s9)"
    and composition_final_out:
      "Some (composition_final, s11) \<in>
        set_dist
          (execute (composition_final_stage A dg composition_bs) s10)"
    and record_composition_final:
      "Some ((), s12) \<in>
        set_dist (execute (record_staged_message composition_final) s11)"
    and query_out:
      "Some (query_chunks, attacker_state) \<in>
        set_dist (execute (staged_query_program A 0 rounds) s12)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
    unfolding staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have root_controlled:
    "controlled_ro_program (trace_root_budget budgets)
      (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def by simp
  have trace_final_controlled:
    "controlled_ro_program (trace_final_budget budgets)
      (trace_final_stage A trace_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have degree_controlled:
    "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_controlled:
    "controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg composition_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have root_state: "PState s1 = 0"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp
  have s2_eq:
    "s2 = s1\<lparr>
      PState := concat (PState s1) fr,
      PTranscript := PTranscript s1 @ [fr]\<rparr>"
    by (rule record_staged_message_outcome[OF record_root])
  have trace_bound:
    "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have trace_alignment:
    "PState s3 = foldl concat (PState s2) trace_roots"
    using staged_trace_fri_program_alignment
        [OF controlled trace_bound trace_out]
    by simp
  have state_s3:
    "PState s3 = foldl concat (concat 0 fr) trace_roots"
    using root_state trace_alignment unfolding s2_eq by simp
  have state_s4: "PState s4 = PState s3"
    using controlled_stage_outcome_fields
        [OF trace_final_controlled final_out]
    by simp
  have s5_eq:
    "s5 = s4\<lparr>
      PState := concat (PState s4) trace_final,
      PTranscript := PTranscript s4 @ [trace_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_final])
  have alpha_alignment:
    "PState s6 = foldl concat (PState s5) as"
    using staged_alpha_program_alignment[OF alpha_out] by simp
  have state_s6:
    "PState s6 =
      foldl concat
        (concat (foldl concat (concat 0 fr) trace_roots) trace_final)
        as"
    using state_s3 state_s4 alpha_alignment unfolding s5_eq by simp
  have state_s7: "PState s7 = PState s6"
    using controlled_stage_outcome_fields[OF degree_controlled degree_out]
    by simp
  have s8_eq:
    "s8 = s7\<lparr>
      PState := concat (PState s7) dg,
      PTranscript := PTranscript s7 @ [dg]\<rparr>"
    by (rule record_staged_message_outcome[OF record_degree])
  have s9_eq: "s9 = s8"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_bound:
    "0 + ceil_log (to_nat dg + 1) \<le>
      length (composition_fri_budgets budgets)"
    using wf round_bound unfolding staged_budget_wellformed_def by simp
  have composition_alignment:
    "PState s10 = foldl concat (PState s9) composition_roots"
    using staged_composition_fri_program_alignment
        [OF controlled composition_bound composition_out]
    by simp
  have state_s10:
    "PState s10 =
      foldl concat
        (concat
          (foldl concat
            (concat (foldl concat (concat 0 fr) trace_roots) trace_final)
            as)
          dg)
        composition_roots"
    using state_s6 state_s7 composition_alignment
    unfolding s8_eq s9_eq by simp
  have state_s11: "PState s11 = PState s10"
    using controlled_stage_outcome_fields
        [OF composition_final_controlled composition_final_out]
    by simp
  have s12_eq:
    "s12 = s11\<lparr>
      PState := concat (PState s11) composition_final,
      PTranscript := PTranscript s11 @ [composition_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_composition_final])
  have state_s12:
    "PState s12 =
      concat
        (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat 0 fr) trace_roots) trace_final)
              as)
            dg)
          composition_roots)
        composition_final"
    using state_s10 state_s11 unfolding s12_eq by simp
  have query_counter_s12: "PQueryCounter s12 = 0"
  proof -
    have root_fields:
      "PQueryCounter s1 = PQueryCounter adversary_initial_state"
      using controlled_stage_outcome_fields[OF root_controlled root_out]
      by simp
    have trace_counters:
      "PQueryCounter s3 = PQueryCounter s2"
      using staged_trace_fri_program_alignment
          [OF controlled trace_bound trace_out]
      by simp
    have final_counter: "PQueryCounter s4 = PQueryCounter s3"
      using controlled_stage_outcome_fields
          [OF trace_final_controlled final_out]
      by simp
    have alpha_counter: "PQueryCounter s6 = PQueryCounter s5"
      using staged_alpha_program_alignment[OF alpha_out] by simp
    have degree_counter: "PQueryCounter s7 = PQueryCounter s6"
      using controlled_stage_outcome_fields[OF degree_controlled degree_out]
      by simp
    have comp_counter: "PQueryCounter s10 = PQueryCounter s9"
      using staged_composition_fri_program_alignment
          [OF controlled composition_bound composition_out]
      by simp
    have comp_final_counter: "PQueryCounter s11 = PQueryCounter s10"
      using controlled_stage_outcome_fields
          [OF composition_final_controlled composition_final_out]
      by simp
    show ?thesis
      using root_fields trace_counters final_counter alpha_counter
        degree_counter comp_counter comp_final_counter
      unfolding s2_eq s5_eq s8_eq s9_eq s12_eq by simp
  qed
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  from staged_query_program_outcome_with_raws
      [OF controlled query_bound query_out]
  obtain raw_idxs query_idxs where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_def:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and state_attacker:
      "PState attacker_state =
        state_after_query_chunks (PState s12) query_chunks rounds"
    and query_counter_attacker:
      "PQueryCounter attacker_state = PQueryCounter s12 + rounds"
    and lookup:
      "\<And>j. j < rounds \<Longrightarrow>
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge (PQueryCounter s12 + j)
            (state_after_query_chunks (PState s12) query_chunks j)) =
        Some (raw_idxs ! j)"
    and idx_bound:
      "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by blast
  have start_eq:
    "PState s12 = staged_query_start_hash data"
    unfolding data_eq staged_query_start_hash_def
      staged_composition_fri_start_hash_def staged_trace_fri_start_hash_def
    using state_s12 by simp
  have chunks_eq: "staged_query_chunks data = query_chunks"
    unfolding data_eq by simp
  have state_attacker':
    "PState attacker_state =
      state_after_query_chunks
        (staged_query_start_hash data)
        (staged_query_chunks data) rounds"
    using state_attacker start_eq chunks_eq by simp
  have query_counter_attacker':
    "PQueryCounter attacker_state = rounds"
    using query_counter_attacker query_counter_s12 by simp
  have lookup':
    "\<And>j. j < rounds \<Longrightarrow>
      fmlookup (HashMap attacker_state)
        (QueryIndexChallenge j
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) j)) =
      Some (raw_idxs ! j)"
    using lookup start_eq query_counter_s12 chunks_eq by simp
  show ?thesis
    by (intro exI[of _ raw_idxs] exI[of _ query_idxs] conjI)
      (use len_raw query_idxs_def chunks_eq len_chunks state_attacker'
        query_counter_attacker' lookup' idx_bound
        in simp_all)
qed

lemma checked_staged_transcript_program_outcome_query_lookups:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
  shows
    "\<exists>raw_idxs query_idxs.
      length raw_idxs = rounds \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length (staged_query_chunks data) = rounds \<and>
      PState attacker_state =
        state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) rounds \<and>
      PQueryCounter attacker_state = rounds \<and>
      (\<forall>j < rounds.
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
          Some (raw_idxs ! j)) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale)"
proof -
  have unchecked_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (staged_transcript_program A) adversary_initial_state)"
    by (rule checked_staged_transcript_program_outcome_imp_staged_transcript_program
        [OF outcome])
  show ?thesis
    by (rule staged_transcript_program_outcome_query_lookups
        [OF wf controlled unchecked_out])
qed

lemma checked_staged_transcript_program_query_phaseE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
  obtains fr trace_roots trace_bs trace_final as dg composition_roots
      composition_bs composition_final query_start query_chunks
  where
    "Some (query_chunks, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            0 rounds)
          query_start)"
    "data =
      \<lparr>staged_trace_root = fr,
       staged_trace_fri_roots = trace_roots,
       staged_trace_fri_challenges = trace_bs,
       staged_trace_final = trace_final,
       staged_alphas = as,
       staged_degree = dg,
       staged_composition_fri_roots = composition_roots,
       staged_composition_fri_challenges = composition_bs,
       staged_composition_final = composition_final,
       staged_query_chunks = query_chunks\<rparr>"
    "PState query_start = staged_query_start_hash data"
    "PQueryCounter query_start = 0"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 query_start query_chunks where
    root_out:
      "Some (fr, s1) \<in>
        set_dist (execute (trace_root_stage A) adversary_initial_state)"
    and record_root:
      "Some ((), s2) \<in> set_dist (execute (record_staged_message fr) s1)"
    and trace_out:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and final_out:
      "Some (trace_final, s4) \<in>
        set_dist (execute (trace_final_stage A trace_bs) s3)"
    and record_final:
      "Some ((), s5) \<in>
        set_dist (execute (record_staged_message trace_final) s4)"
    and alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s5)"
    and degree_out:
      "Some (dg, s7) \<in> set_dist (execute (degree_stage A as) s6)"
    and record_degree:
      "Some ((), s8) \<in> set_dist (execute (record_staged_message dg) s7)"
    and assert_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1))) s8)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s9)"
    and composition_final_out:
      "Some (composition_final, s11) \<in>
        set_dist
          (execute (composition_final_stage A dg composition_bs) s10)"
    and record_composition_final:
      "Some ((), query_start) \<in>
        set_dist (execute (record_staged_message composition_final) s11)"
    and query_out:
      "Some (query_chunks, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              0 rounds)
            query_start)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
    unfolding checked_staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have root_controlled:
    "controlled_ro_program (trace_root_budget budgets)
      (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def by simp
  have trace_final_controlled:
    "controlled_ro_program (trace_final_budget budgets)
      (trace_final_stage A trace_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have degree_controlled:
    "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_controlled:
    "controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg composition_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have root_state: "PState s1 = 0"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp
  have s2_eq:
    "s2 = s1\<lparr>
      PState := concat (PState s1) fr,
      PTranscript := PTranscript s1 @ [fr]\<rparr>"
    by (rule record_staged_message_outcome[OF record_root])
  have trace_bound:
    "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have trace_alignment:
    "PState s3 = foldl concat (PState s2) trace_roots"
    using staged_trace_fri_program_alignment
        [OF controlled trace_bound trace_out]
    by simp
  have state_s3:
    "PState s3 = foldl concat (concat 0 fr) trace_roots"
    using root_state trace_alignment unfolding s2_eq by simp
  have state_s4: "PState s4 = PState s3"
    using controlled_stage_outcome_fields
        [OF trace_final_controlled final_out]
    by simp
  have s5_eq:
    "s5 = s4\<lparr>
      PState := concat (PState s4) trace_final,
      PTranscript := PTranscript s4 @ [trace_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_final])
  have alpha_alignment:
    "PState s6 = foldl concat (PState s5) as"
    using staged_alpha_program_alignment[OF alpha_out] by simp
  have state_s6:
    "PState s6 =
      foldl concat
        (concat (foldl concat (concat 0 fr) trace_roots) trace_final)
        as"
    using state_s3 state_s4 alpha_alignment unfolding s5_eq by simp
  have state_s7: "PState s7 = PState s6"
    using controlled_stage_outcome_fields[OF degree_controlled degree_out]
    by simp
  have s8_eq:
    "s8 = s7\<lparr>
      PState := concat (PState s7) dg,
      PTranscript := PTranscript s7 @ [dg]\<rparr>"
    by (rule record_staged_message_outcome[OF record_degree])
  have s9_eq: "s9 = s8"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_bound:
    "0 + ceil_log (to_nat dg + 1) \<le>
      length (composition_fri_budgets budgets)"
    using wf round_bound unfolding staged_budget_wellformed_def by simp
  have composition_alignment:
    "PState s10 = foldl concat (PState s9) composition_roots"
    using staged_composition_fri_program_alignment
        [OF controlled composition_bound composition_out]
    by simp
  have state_s10:
    "PState s10 =
      foldl concat
        (concat
          (foldl concat
            (concat (foldl concat (concat 0 fr) trace_roots) trace_final)
            as)
          dg)
        composition_roots"
    using state_s6 state_s7 composition_alignment
    unfolding s8_eq s9_eq by simp
  have state_s11: "PState s11 = PState s10"
    using controlled_stage_outcome_fields
        [OF composition_final_controlled composition_final_out]
    by simp
  have query_start_eq:
    "query_start = s11\<lparr>
      PState := concat (PState s11) composition_final,
      PTranscript := PTranscript s11 @ [composition_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_composition_final])
  have state_query_start:
    "PState query_start =
      concat
        (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat 0 fr) trace_roots) trace_final)
              as)
            dg)
          composition_roots)
        composition_final"
    using state_s10 state_s11 unfolding query_start_eq by simp
  have query_counter_start: "PQueryCounter query_start = 0"
  proof -
    have root_fields:
      "PQueryCounter s1 = PQueryCounter adversary_initial_state"
      using controlled_stage_outcome_fields[OF root_controlled root_out]
      by simp
    have trace_counters:
      "PQueryCounter s3 = PQueryCounter s2"
      using staged_trace_fri_program_alignment
          [OF controlled trace_bound trace_out]
      by simp
    have final_counter: "PQueryCounter s4 = PQueryCounter s3"
      using controlled_stage_outcome_fields
          [OF trace_final_controlled final_out]
      by simp
    have alpha_counter: "PQueryCounter s6 = PQueryCounter s5"
      using staged_alpha_program_alignment[OF alpha_out] by simp
    have degree_counter: "PQueryCounter s7 = PQueryCounter s6"
      using controlled_stage_outcome_fields[OF degree_controlled degree_out]
      by simp
    have comp_counter: "PQueryCounter s10 = PQueryCounter s9"
      using staged_composition_fri_program_alignment
          [OF controlled composition_bound composition_out]
      by simp
    have comp_final_counter: "PQueryCounter s11 = PQueryCounter s10"
      using controlled_stage_outcome_fields
          [OF composition_final_controlled composition_final_out]
      by simp
    show ?thesis
      using root_fields trace_counters final_counter alpha_counter
        degree_counter comp_counter comp_final_counter
      unfolding s2_eq s5_eq s8_eq s9_eq query_start_eq by simp
  qed
  have start_eq:
    "PState query_start = staged_query_start_hash data"
    unfolding data_eq staged_query_start_hash_def
      staged_composition_fri_start_hash_def staged_trace_fri_start_hash_def
    using state_query_start by simp
  show ?thesis
    by (rule that[OF query_out data_eq start_eq query_counter_start])
qed

lemma checked_staged_security_with_data_state_accepted_shape_query_keys:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist (execute
          (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    and shape:
      "accepted_transcript_shape
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) as query_idxs"
  shows
    "as = staged_alphas data \<and>
     (\<exists>raw_idxs.
      length raw_idxs = rounds \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      (\<forall>i < rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale))"
proof -
  let ?s = "verifier_state_from_adversary attacker_state
    (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF outcome]
  have builder:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist (execute verify_monad ?s)"
    by blast+
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  from accepted_transcript_shape_query_chunksE[OF shape]
  obtain result' final_state' fr f_fri_roots f_final dg
      composition_fri_roots final rest raw_idxs query_chunks trailing
    where out_eq:
      "Some (result, final_state) = Some (result', final_state')"
    and header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and concat_chunks: "List.concat query_chunks @ trailing = rest"
    and chunk_shape:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          f_fri_roots composition_fri_roots (query_chunks ! i)"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter ?s + i)
            (state_after_query_chunks
              (verifier_header_state ?s fr f_fri_roots f_final as dg
                composition_fri_roots final)
              query_chunks i)) =
        Some (raw_idxs ! i)"
    and idx_bound:
      "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by blast
  have header_eq:
    "fr = staged_trace_root data \<and>
     f_fri_roots = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     composition_fri_roots = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF staged_header header]
    by simp
  have final_state_eq: "final_state' = final_state"
    using out_eq by simp
  have header_state_eq:
    "verifier_header_state ?s fr f_fri_roots f_final as dg
      composition_fri_roots final =
      staged_query_start_hash data"
    using header_eq
    unfolding verifier_header_state_def verifier_header_messages_def
      staged_query_start_hash_def staged_composition_fri_start_hash_def
      staged_trace_fri_start_hash_def
    by simp
  from checked_staged_transcript_program_query_chunks_match_verifier_lengths
      [OF builder]
  obtain staged_query_idxs where
    staged_match:
      "staged_query_chunks_match_verifier_lengths data staged_query_idxs"
    by blast
  have query_idxs_len: "length query_idxs = rounds"
    using query_idxs_eq len_raw by simp
  have staged_match_query_idxs:
    "staged_query_chunks_match_verifier_lengths data query_idxs"
    by (rule staged_query_chunks_match_verifier_lengths_transfer
        [OF staged_match query_idxs_len])
  have parser_chunk_len:
    "\<And>i. i < rounds \<Longrightarrow>
      length (query_chunks ! i) =
        verifier_query_round_transcript_length (query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    show
      "length (query_chunks ! i) =
        verifier_query_round_transcript_length (query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
      using verifier_query_round_chunk_length[OF chunk_shape[OF i_bound]]
        header_eq by simp
  qed
  have concat_staged:
    "List.concat query_chunks @ trailing =
      List.concat (staged_query_chunks data)"
    using concat_chunks header_eq by simp
  have query_chunks_eq:
    "query_chunks = staged_query_chunks data \<and> trailing = []"
    by (rule query_chunks_eq_staged_if_matching_lengths
        [OF len_chunks concat_staged parser_chunk_len
          staged_match_query_idxs])
  have lookup_staged:
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have lookup_i:
      "fmlookup (HashMap final_state')
        (QueryIndexChallenge (PQueryCounter ?s + i)
          (state_after_query_chunks
            (verifier_header_state ?s fr f_fri_roots f_final as dg
              composition_fri_roots final)
            query_chunks i)) =
        Some (raw_idxs ! i)"
      by (rule lookup[OF i_bound])
    show
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
      using lookup_i final_state_eq header_state_eq query_chunks_eq by simp
  qed
  show ?thesis
    using header_eq len_raw query_idxs_eq lookup_staged idx_bound by blast
qed

lemma checked_staged_security_with_data_state_accepted_shape_query_set_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist (execute
          (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    and shape:
      "accepted_transcript_shape
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) as query_idxs"
    and hit: "\<exists>i < rounds. query_idxs ! i \<in> B"
  shows "staged_transcript_query_index_set_hit B (Some (data, attacker_state))"
proof -
  let ?s = "verifier_state_from_adversary attacker_state
    (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF outcome]
  have builder:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist (execute verify_monad ?s)"
    by blast+
  from checked_staged_transcript_program_outcome_query_lookups
      [OF wf controlled builder]
  obtain attacker_raw_idxs where
    lookup_attacker:
      "\<forall>j < rounds.
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge j
            (state_after_query_chunks (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
          Some (attacker_raw_idxs ! j)"
    by blast
  from checked_staged_security_with_data_state_accepted_shape_query_keys
      [OF wf controlled outcome shape]
  obtain raw_idxs where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    by blast
  from hit obtain i where i_bound: "i < rounds"
    and query_hit: "query_idxs ! i \<in> B"
    by blast
  have raw_i: "i < length raw_idxs"
    using len_raw i_bound by simp
  have raw_hit: "index (to_nat (raw_idxs ! i)) \<in> B"
    using query_hit query_idxs_eq raw_i by (simp add: nth_map)
  have ext: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have lookup_initial:
    "fmlookup (HashMap ?s)
      (QueryIndexChallenge i
        (state_after_query_chunks (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (attacker_raw_idxs ! i)"
    using lookup_attacker i_bound by simp
  have lookup_final_from_initial:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (attacker_raw_idxs ! i)"
    by (rule hash_extension_lookup[OF lookup_initial ext])
  have raw_eq: "attacker_raw_idxs ! i = raw_idxs ! i"
    using lookup_final_from_initial lookup[OF i_bound] by simp
  have attacker_raw_hit: "index (to_nat (attacker_raw_idxs ! i)) \<in> B"
    using raw_hit raw_eq by simp
  have lookup_attacker_i:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge i
        (state_after_query_chunks (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (attacker_raw_idxs ! i)"
    using lookup_attacker i_bound by simp
  show ?thesis
    unfolding staged_transcript_query_index_set_hit_def
    using i_bound lookup_attacker_i attacker_raw_hit by auto
qed

lemma staged_security_with_data_query_index_set_bound_from_transcript:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and transcript_bound:
      "wp_event (staged_transcript_program A)
        (staged_transcript_query_index_set_hit B)
        adversary_initial_state \<le> C"
  shows
    "wp_event (staged_security_experiment_with_data A)
      (staged_security_with_data_query_index_set_hit B)
      adversary_initial_state \<le> C"
  unfolding staged_security_experiment_with_data_def
proof (rule wp_event_bind_bound_by_head_event[OF transcript_bound])
  show "staged_security_with_data_query_index_set_hit B None \<Longrightarrow>
    staged_transcript_query_index_set_hit B None"
    unfolding staged_security_with_data_query_index_set_hit_def
      staged_transcript_query_index_set_hit_def
    by simp
next
  fix data attacker_state out
  assume builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (staged_transcript_program A)
            adversary_initial_state)"
    and cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>s. put
                (verifier_state_from_adversary s
                  (staged_proof_transcript data)) \<bind>
                (\<lambda>_. verify_monad \<bind>
                  (\<lambda>result. return (data, result)))))
            attacker_state)"
    and hit: "staged_security_with_data_query_index_set_hit B out"
  from staged_transcript_program_outcome_query_lookups
      [OF wf controlled builder]
  obtain raw_idxs query_idxs where
    len_raw: "length raw_idxs = rounds"
    and lookup_attacker:
      "\<forall>j < rounds.
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
          Some (raw_idxs ! j)"
    by blast
  from hit obtain data' result final_state i raw where
    out_eq: "out = Some ((data', result), final_state)"
    and i_bound: "i < rounds"
    and lookup_final:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data')
            (staged_query_chunks data') i)) =
        Some raw"
    and raw_hit: "index (to_nat raw) \<in> B"
    unfolding staged_security_with_data_query_index_set_hit_def
    by (auto split: option.splits prod.splits)
  from cont[unfolded out_eq] obtain verifier_state verifier_result where
    verifier:
      "Some (verifier_result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and data'_eq: "data' = data"
    by (auto elim!: set_dist_bindE)
  have ext:
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data) \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have lookup_initial:
    "fmlookup
      (HashMap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    using lookup_attacker i_bound by simp
  have lookup_final_from_initial:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    by (rule hash_extension_lookup[OF lookup_initial ext])
  have raw_eq: "raw = raw_idxs ! i"
    using lookup_final lookup_final_from_initial data'_eq by simp
  have lookup_attacker_i:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    using lookup_attacker i_bound by simp
  have raw_idxs_hit: "index (to_nat (raw_idxs ! i)) \<in> B"
    using raw_hit raw_eq by simp
  show "staged_transcript_query_index_set_hit B
      (Some (data, attacker_state))"
    unfolding staged_transcript_query_index_set_hit_def
    using i_bound lookup_attacker_i raw_idxs_hit by auto
qed

lemma checked_staged_security_with_data_query_index_set_bound_from_transcript:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and transcript_bound:
      "wp_event (checked_staged_transcript_program A)
        (staged_transcript_query_index_set_hit B)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data A)
      (staged_security_with_data_query_index_set_hit B)
      adversary_initial_state \<le> C"
  unfolding checked_staged_security_experiment_with_data_def
proof (rule wp_event_bind_bound_by_head_event[OF transcript_bound])
  show "staged_security_with_data_query_index_set_hit B None \<Longrightarrow>
    staged_transcript_query_index_set_hit B None"
    unfolding staged_security_with_data_query_index_set_hit_def
      staged_transcript_query_index_set_hit_def
    by simp
next
  fix data attacker_state out
  assume builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>s. put
                (verifier_state_from_adversary s
                  (staged_proof_transcript data)) \<bind>
                (\<lambda>_. verify_monad \<bind>
                  (\<lambda>result. return (data, result)))))
            attacker_state)"
    and hit: "staged_security_with_data_query_index_set_hit B out"
  from checked_staged_transcript_program_outcome_query_lookups
      [OF wf controlled builder]
  obtain raw_idxs query_idxs where
    len_raw: "length raw_idxs = rounds"
    and lookup_attacker:
      "\<forall>j < rounds.
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
          Some (raw_idxs ! j)"
    by blast
  from hit obtain data' result final_state i raw where
    out_eq: "out = Some ((data', result), final_state)"
    and i_bound: "i < rounds"
    and lookup_final:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data')
            (staged_query_chunks data') i)) =
        Some raw"
    and raw_hit: "index (to_nat raw) \<in> B"
    unfolding staged_security_with_data_query_index_set_hit_def
    by (auto split: option.splits prod.splits)
  from cont[unfolded out_eq] obtain verifier_state verifier_result where
    verifier:
      "Some (verifier_result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and data'_eq: "data' = data"
    by (auto elim!: set_dist_bindE)
  have ext:
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data) \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have lookup_initial:
    "fmlookup
      (HashMap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    using lookup_attacker i_bound by simp
  have lookup_final_from_initial:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    by (rule hash_extension_lookup[OF lookup_initial ext])
  have raw_eq: "raw = raw_idxs ! i"
    using lookup_final lookup_final_from_initial data'_eq by simp
  have lookup_attacker_i:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    using lookup_attacker i_bound by simp
  have raw_idxs_hit: "index (to_nat (raw_idxs ! i)) \<in> B"
    using raw_hit raw_eq by simp
  show "staged_transcript_query_index_set_hit B
      (Some (data, attacker_state))"
    unfolding staged_transcript_query_index_set_hit_def
    using i_bound lookup_attacker_i raw_idxs_hit by auto
qed

lemma staged_transcript_query_index_set_hit_imp_target_hit:
  assumes hit: "staged_transcript_query_index_set_hit B out"
  shows
    "hash_new_output_hit_event (query_index_raw_preimage B)
      adversary_initial_state out"
proof (cases out)
  case None
  then show ?thesis
    using hit unfolding staged_transcript_query_index_set_hit_def by simp
next
  case (Some result)
  then obtain data t where out_eq: "out = Some (data, t)"
    by (cases result) simp
  from hit[unfolded out_eq staged_transcript_query_index_set_hit_def]
  obtain i raw where lookup:
      "fmlookup (HashMap t)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
        Some raw"
    and raw_in: "raw \<in> query_index_raw_preimage B"
    unfolding query_index_raw_preimage_def by auto
  have new_hit:
    "hash_map_new_output_hit (query_index_raw_preimage B)
      adversary_initial_state t"
    unfolding hash_map_new_output_hit_def
    using lookup raw_in by auto
  show ?thesis
    unfolding out_eq hash_new_output_hit_event_def
    using new_hit by simp
qed

lemma staged_transcript_query_index_set_hit_bound_from_target_program:
  assumes target:
    "hash_target_program (query_index_raw_preimage B) q m"
  shows
    "wp_event m (staged_transcript_query_index_set_hit B)
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B) q"
proof -
  have event_mono:
    "wp_event m (staged_transcript_query_index_set_hit B)
      adversary_initial_state \<le>
      wp_event m
        (hash_new_output_hit_event (query_index_raw_preimage B)
          adversary_initial_state)
        adversary_initial_state"
    by (rule wp_event_mono)
      (rule staged_transcript_query_index_set_hit_imp_target_hit)
  have target_bound:
    "wp_event m
        (hash_new_output_hit_event (query_index_raw_preimage B)
          adversary_initial_state)
        adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B) q"
    using target unfolding hash_target_program_def hash_target_budget_def
      staged_phase_target_error_def by blast
  show ?thesis
    by (rule order_trans[OF event_mono target_bound])
qed

lemma staged_transcript_query_index_set_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (staged_transcript_program A)
      (staged_transcript_query_index_set_hit B)
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule staged_transcript_query_index_set_hit_bound_from_target_program)
    (rule hash_target_program_staged_transcript_program[OF wf controlled])

lemma checked_staged_transcript_query_index_set_hit_bound_from_target_program:
  assumes target:
    "hash_target_program (query_index_raw_preimage B) q
      (checked_staged_transcript_program A)"
  shows
    "wp_event (checked_staged_transcript_program A)
      (staged_transcript_query_index_set_hit B)
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B) q"
  by (rule staged_transcript_query_index_set_hit_bound_from_target_program
      [OF target])

lemma checked_staged_transcript_query_index_set_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_transcript_program A)
      (staged_transcript_query_index_set_hit B)
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule checked_staged_transcript_query_index_set_hit_bound_from_target_program)
    (rule hash_target_program_checked_staged_transcript_program
      [OF wf controlled])

lemma staged_security_with_data_query_index_set_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (staged_security_experiment_with_data A)
      (staged_security_with_data_query_index_set_hit B)
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule staged_security_with_data_query_index_set_bound_from_transcript
      [OF wf controlled
        staged_transcript_query_index_set_hit_bound[OF wf controlled]])

lemma checked_staged_security_with_data_query_index_set_hit_bound_from_target_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and target:
      "hash_target_program (query_index_raw_preimage B) q
        (checked_staged_transcript_program A)"
  shows
    "wp_event (checked_staged_security_experiment_with_data A)
      (staged_security_with_data_query_index_set_hit B)
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B) q"
  by (rule checked_staged_security_with_data_query_index_set_bound_from_transcript
      [OF wf controlled
        checked_staged_transcript_query_index_set_hit_bound_from_target_program
          [OF target]])

lemma checked_staged_security_with_data_query_index_set_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data A)
      (staged_security_with_data_query_index_set_hit B)
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule checked_staged_security_with_data_query_index_set_hit_bound_from_target_program
      [OF wf controlled
        hash_target_program_checked_staged_transcript_program
          [OF wf controlled]])

end

end
