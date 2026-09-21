(*  Title:      Stark/Soundness_FRI_First_Root_Prefix.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_Prefix
  imports Soundness_FRI_State_Dependent_Query_Product
begin

text \<open>
  A proof-only decomposition of the checked transcript builder immediately after
  the trace commitment root and first trace-FRI root have been recorded, but
  before the first trace-FRI challenge is sampled.  The decomposition does not
  change the staged protocol.
\<close>

context soundness
begin

definition checked_staged_after_first_trace_fri_root_program
  :: "'f staged_adversary \<Rightarrow> ('f \<times> 'f list \<times> 'f) \<Rightarrow>
      ('f staged_proof_data, 'f protocol_channel) state_monad"
  where
  "checked_staged_after_first_trace_fri_root_program A prefix =
    (case prefix of (fr, trace_bs, first_root) \<Rightarrow>
      do {
        b \<leftarrow> receive_trace_fri_challenge;
        (trace_roots, trace_bs') \<leftarrow>
          staged_trace_fri_program A 1 (ceil_log clength - 1)
            (trace_bs @ [b]);
        trace_final \<leftarrow> trace_final_stage A trace_bs';
        record_staged_message trace_final;
        as \<leftarrow> staged_alpha_program (length spec);
        dg \<leftarrow> degree_stage A as;
        record_staged_message dg;
        let composition_rounds = ceil_log (to_nat dg + 1);
        assert (composition_rounds \<le> ceil_log (maxDegree + 1));
        (composition_roots, composition_bs) \<leftarrow>
          staged_composition_fri_program A dg 0 composition_rounds [];
        composition_final \<leftarrow>
          composition_final_stage A dg composition_bs;
        record_staged_message composition_final;
        query_chunks \<leftarrow>
          checked_staged_query_program A (first_root # trace_roots)
            composition_roots 0 rounds;
        return
          \<lparr>staged_trace_root = fr,
           staged_trace_fri_roots = first_root # trace_roots,
           staged_trace_fri_challenges = trace_bs',
           staged_trace_final = trace_final,
           staged_alphas = as,
           staged_degree = dg,
           staged_composition_fri_roots = composition_roots,
           staged_composition_fri_challenges = composition_bs,
           staged_composition_final = composition_final,
           staged_query_chunks = query_chunks\<rparr>
      })"

lemma checked_staged_transcript_program_first_trace_fri_root_decomp:
  assumes nonempty: "0 < ceil_log clength"
  shows
    "checked_staged_transcript_program A =
      staged_trace_fri_challenge_prefix_program A 0 \<bind>
        checked_staged_after_first_trace_fri_root_program A"
proof -
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  show ?thesis
    unfolding checked_staged_transcript_program_def
      staged_trace_fri_challenge_prefix_program_def
      checked_staged_after_first_trace_fri_root_program_def
      rounds_eq
    by (simp add: sm_bind_assoc Let_def split_def)
qed

lemma staged_trace_fri_challenge_prefix_program_zero_challenges:
  assumes outcome:
    "Some ((fr, trace_bs, first_root), prefix_state) \<in>
      set_dist
        (execute (staged_trace_fri_challenge_prefix_program A 0) s)"
  shows "trace_bs = []"
  using outcome
  unfolding staged_trace_fri_challenge_prefix_program_def
  by (auto elim!: set_dist_bindE)

lemma checked_staged_transcript_program_first_trace_fri_root_supportE:
  assumes nonempty: "0 < ceil_log clength"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A) s)"
  obtains fr first_root prefix_state where
    "Some ((fr, [], first_root), prefix_state) \<in>
      set_dist
        (execute (staged_trace_fri_challenge_prefix_program A 0) s)"
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_after_first_trace_fri_root_program A
            (fr, [], first_root))
          prefix_state)"
proof -
  have decomp:
    "checked_staged_transcript_program A =
      staged_trace_fri_challenge_prefix_program A 0 \<bind>
        checked_staged_after_first_trace_fri_root_program A"
    by (rule
        checked_staged_transcript_program_first_trace_fri_root_decomp
          [OF nonempty])
  from outcome[unfolded decomp]
  obtain prefix prefix_state where
    head:
      "Some (prefix, prefix_state) \<in>
        set_dist
          (execute (staged_trace_fri_challenge_prefix_program A 0) s)"
    and tail:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_first_trace_fri_root_program A prefix)
            prefix_state)"
    by (auto elim!: set_dist_bindE)
  obtain fr trace_bs first_root where prefix_eq:
    "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  have trace_bs_eq: "trace_bs = []"
    by (rule
        staged_trace_fri_challenge_prefix_program_zero_challenges
          [OF head[unfolded prefix_eq]])
  have head':
    "Some ((fr, [], first_root), prefix_state) \<in>
      set_dist
        (execute (staged_trace_fri_challenge_prefix_program A 0) s)"
    using head unfolding prefix_eq trace_bs_eq .
  have tail':
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_after_first_trace_fri_root_program A
            (fr, [], first_root))
          prefix_state)"
    using tail unfolding prefix_eq trace_bs_eq .
  show ?thesis
    by (rule that[OF head' tail'])
qed

lemma checked_staged_after_first_trace_fri_root_program_data:
  assumes outcome:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_after_first_trace_fri_root_program A
            (fr, [], first_root))
          prefix_state)"
  shows
    "staged_trace_root data = fr"
    "staged_trace_fri_roots data \<noteq> []"
    "staged_trace_fri_roots data ! 0 = first_root"
  using outcome
  unfolding checked_staged_after_first_trace_fri_root_program_def
  by (auto simp: Let_def split_def elim!: set_dist_bindE)

definition first_trace_fri_root_prefix_state_for
  :: "'f staged_adversary \<Rightarrow> 'f staged_proof_data \<Rightarrow>
      'f protocol_channel \<Rightarrow> 'f protocol_channel"
  where
  "first_trace_fri_root_prefix_state_for A data attacker_state =
    (SOME prefix_state.
      \<exists>fr first_root.
        Some ((fr, [], first_root), prefix_state) \<in>
          set_dist
            (execute (staged_trace_fri_challenge_prefix_program A 0)
              adversary_initial_state) \<and>
        Some (data, attacker_state) \<in>
          set_dist
            (execute
              (checked_staged_after_first_trace_fri_root_program A
                (fr, [], first_root))
              prefix_state))"

lemma first_trace_fri_root_prefix_state_for_support:
  assumes nonempty: "0 < ceil_log clength"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
  shows
    "\<exists>fr first_root.
      Some ((fr, [], first_root),
          first_trace_fri_root_prefix_state_for A data attacker_state) \<in>
        set_dist
          (execute (staged_trace_fri_challenge_prefix_program A 0)
            adversary_initial_state) \<and>
      Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_first_trace_fri_root_program A
              (fr, [], first_root))
            (first_trace_fri_root_prefix_state_for A data attacker_state))"
proof -
  obtain fr first_root prefix_state where
    head:
      "Some ((fr, [], first_root), prefix_state) \<in>
        set_dist
          (execute (staged_trace_fri_challenge_prefix_program A 0)
            adversary_initial_state)"
    and tail:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_first_trace_fri_root_program A
              (fr, [], first_root))
            prefix_state)"
    by (rule
        checked_staged_transcript_program_first_trace_fri_root_supportE
          [OF nonempty builder])
  have ex:
    "\<exists>prefix_state fr first_root.
      Some ((fr, [], first_root), prefix_state) \<in>
        set_dist
          (execute (staged_trace_fri_challenge_prefix_program A 0)
            adversary_initial_state) \<and>
      Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_first_trace_fri_root_program A
              (fr, [], first_root))
            prefix_state)"
    using head tail by blast
  have selected:
    "\<exists>fr first_root.
      Some ((fr, [], first_root),
          (SOME prefix_state.
            \<exists>fr first_root.
              Some ((fr, [], first_root), prefix_state) \<in>
                set_dist
                  (execute
                    (staged_trace_fri_challenge_prefix_program A 0)
                    adversary_initial_state) \<and>
              Some (data, attacker_state) \<in>
                set_dist
                  (execute
                    (checked_staged_after_first_trace_fri_root_program A
                      (fr, [], first_root))
                    prefix_state))) \<in>
        set_dist
          (execute (staged_trace_fri_challenge_prefix_program A 0)
            adversary_initial_state) \<and>
      Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_first_trace_fri_root_program A
              (fr, [], first_root))
            (SOME prefix_state.
              \<exists>fr first_root.
                Some ((fr, [], first_root), prefix_state) \<in>
                  set_dist
                    (execute
                      (staged_trace_fri_challenge_prefix_program A 0)
                      adversary_initial_state) \<and>
                Some (data, attacker_state) \<in>
                  set_dist
                    (execute
                      (checked_staged_after_first_trace_fri_root_program A
                        (fr, [], first_root))
                      prefix_state)))"
    by (rule someI_ex) (use ex in blast)
  show ?thesis
    using selected
    unfolding first_trace_fri_root_prefix_state_for_def .
qed

lemma first_trace_fri_root_prefix_state_for_data:
  assumes nonempty: "0 < ceil_log clength"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
  shows
    "staged_trace_fri_roots data \<noteq> []"
    "\<exists>fr first_root.
      staged_trace_root data = fr \<and>
      staged_trace_fri_roots data ! 0 = first_root \<and>
      Some ((fr, [], first_root),
          first_trace_fri_root_prefix_state_for A data attacker_state) \<in>
        set_dist
          (execute (staged_trace_fri_challenge_prefix_program A 0)
            adversary_initial_state)"
proof -
  obtain fr first_root where
    head:
      "Some ((fr, [], first_root),
          first_trace_fri_root_prefix_state_for A data attacker_state) \<in>
        set_dist
          (execute (staged_trace_fri_challenge_prefix_program A 0)
            adversary_initial_state)"
    and tail:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_first_trace_fri_root_program A
              (fr, [], first_root))
            (first_trace_fri_root_prefix_state_for A data attacker_state))"
    using first_trace_fri_root_prefix_state_for_support[OF nonempty builder]
    by blast
  have data_facts:
    "staged_trace_root data = fr"
    "staged_trace_fri_roots data \<noteq> []"
    "staged_trace_fri_roots data ! 0 = first_root"
    by (rule checked_staged_after_first_trace_fri_root_program_data[OF tail])+
  show "staged_trace_fri_roots data \<noteq> []"
    by (rule data_facts(2))
  show
    "\<exists>fr first_root.
      staged_trace_root data = fr \<and>
      staged_trace_fri_roots data ! 0 = first_root \<and>
      Some ((fr, [], first_root),
          first_trace_fri_root_prefix_state_for A data attacker_state) \<in>
        set_dist
          (execute (staged_trace_fri_challenge_prefix_program A 0)
            adversary_initial_state)"
    using data_facts head by blast
qed


lemma hash_target_program_checked_staged_after_first_trace_fri_root_program:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget)
      (checked_staged_after_first_trace_fri_root_program A prefix)"
proof -
  let ?trace_tail =
    "sum_list
      (take (ceil_log clength - 1)
        (drop 1 (trace_fri_budgets budgets))) +
      (ceil_log clength - 1)"
  let ?trace_final = "trace_final_budget budgets"
  let ?alpha = "length spec"
  let ?degree = "degree_budget budgets"
  let ?composition =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  let ?query =
    "sum_list (query_opening_budgets budgets) + rounds"
  let ?used =
    "1 +
      (?trace_tail +
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition +
                    (?composition_final +
                      (0 + (?query + 0))))))))))"
  have trace_bound:
    "1 + (ceil_log clength - 1) \<le>
      length (trace_fri_budgets budgets)"
    using nonempty wf
    unfolding staged_budget_wellformed_def
    by simp
  have trace_tail:
    "\<And>bs. hash_target_program B ?trace_tail
      (staged_trace_fri_program A 1 (ceil_log clength - 1) bs)"
    by (rule hash_target_program_staged_trace_fri_program
        [OF controlled trace_bound])
  have challenge:
    "hash_target_program B 1 receive_trace_fri_challenge"
    by (rule hash_target_program_receive_trace_fri_challenge)
  have trace_final:
    "\<And>bs. hash_target_program B ?trace_final (trace_final_stage A bs)"
    using controlled
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have record_target:
    "\<And>x. hash_target_program B 0 (record_staged_message x)"
    by (rule hash_target_program_record_staged_message)
  have alpha:
    "hash_target_program B ?alpha (staged_alpha_program (length spec))"
    by (rule hash_target_program_staged_alpha_program)
  have degree:
    "\<And>as. hash_target_program B ?degree (degree_stage A as)"
    using controlled
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have composition:
    "\<And>dg. hash_target_program B ?composition
      (assert
        (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
       (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
  proof -
    fix dg
    let ?n = "ceil_log (to_nat dg + 1)"
    let ?m = "ceil_log (maxDegree + 1)"
    have bound:
      "hash_target_program B (0 + ?composition)
        (assert (?n \<le> ?m) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0 ?n []))"
    proof (rule hash_target_program_bind_on_outcomes)
      show "hash_target_program B 0 (assert (?n \<le> ?m))"
        by (rule hash_target_program_assert)
    next
      fix s :: "'f protocol_channel"
        and u :: unit
        and t :: "'f protocol_channel"
      assume out:
        "Some (u, t) \<in> set_dist (execute (assert (?n \<le> ?m)) s)"
      have n_le: "?n \<le> ?m"
        using out
        unfolding assert_def
        by (cases "?n \<le> ?m") (auto simp: throw_no_outcome)
      have length_eq:
        "length (composition_fri_budgets budgets) = ?m"
        using wf unfolding staged_budget_wellformed_def by simp
      have exact:
        "hash_target_program B
          (sum_list
            (take ?n (drop 0 (composition_fri_budgets budgets))) + ?n)
          (staged_composition_fri_program A dg 0 ?n [])"
        by (rule hash_target_program_staged_composition_fri_program
            [OF controlled])
          (use n_le length_eq in simp)
      have take_le:
        "sum_list (take ?n (composition_fri_budgets budgets)) \<le>
          sum_list (composition_fri_budgets budgets)"
        by (rule sum_list_take_le)
      have budget_le:
        "sum_list
            (take ?n (drop 0 (composition_fri_budgets budgets))) + ?n
          \<le> ?composition"
        using take_le n_le by simp
      show
        "hash_target_program B ?composition
          (staged_composition_fri_program A dg 0 ?n [])"
        by (rule hash_target_program_mono[OF budget_le exact])
    qed
    show
      "hash_target_program B ?composition
        (assert (?n \<le> ?m) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0 ?n []))"
      using bound by simp
  qed
  have composition_final:
    "\<And>dg bs. hash_target_program B ?composition_final
      (composition_final_stage A dg bs)"
    using controlled
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have query:
    "\<And>trace_roots composition_roots.
      hash_target_program B ?query
        (checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
  proof -
    fix trace_roots composition_roots
    have bound:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_target_program B
        (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) + rounds)
        (checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      by (rule hash_target_program_checked_staged_query_program
          [OF controlled bound])
    show
      "hash_target_program B ?query
        (checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      using exact wf
      unfolding staged_budget_wellformed_def
      by simp
  qed
  obtain fr trace_bs first_root where prefix_eq:
    "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  have exact:
    "hash_target_program B ?used
      (checked_staged_after_first_trace_fri_root_program A prefix)"
    unfolding prefix_eq
      checked_staged_after_first_trace_fri_root_program_def
    apply (simp only: case_prod_beta fst_conv snd_conv)
    apply (rule hash_target_program_bind)
     apply (rule challenge)
    apply (rule hash_target_program_bind)
     apply (rule trace_tail)
    apply (rename_tac trace_pair)
    apply (case_tac trace_pair)
    apply (simp only: case_prod_beta fst_conv snd_conv Let_def)
    apply (rule hash_target_program_bind)
     apply (rule trace_final)
    apply (rule hash_target_program_bind)
     apply (rule record_target)
    apply (rule hash_target_program_bind)
     apply (rule alpha)
    apply (rule hash_target_program_bind)
     apply (rule degree)
    apply (rule hash_target_program_bind)
     apply (rule record_target)
    apply (subst sm_bind_assoc[symmetric])
    apply (rule hash_target_program_bind)
     apply (rule composition)
    apply (rename_tac composition_pair)
    apply (case_tac composition_pair)
    apply (simp only: case_prod_beta fst_conv snd_conv Let_def)
    apply (rule hash_target_program_bind)
     apply (rule composition_final)
    apply (rule hash_target_program_bind)
     apply (rule record_target)
    apply (rule hash_target_program_bind)
     apply (rule query)
    apply (rule hash_target_program_return)
    done
  have trace_sum_le:
    "sum_list
      (take (ceil_log clength - 1)
        (drop 1 (trace_fri_budgets budgets))) \<le>
      sum_list (trace_fri_budgets budgets)"
  proof -
    have take_le:
      "sum_list
        (take (ceil_log clength - 1)
          (drop 1 (trace_fri_budgets budgets))) \<le>
        sum_list (drop 1 (trace_fri_budgets budgets))"
      by (rule sum_list_take_le)
    have drop_le:
      "sum_list (drop 1 (trace_fri_budgets budgets)) \<le>
        sum_list (trace_fri_budgets budgets)"
      by (cases "trace_fri_budgets budgets") simp_all
    show ?thesis
      by (rule order_trans[OF take_le drop_le])
  qed
  have trace_part_le:
    "1 + ?trace_tail \<le>
      sum_list (trace_fri_budgets budgets) + ceil_log clength"
    using nonempty trace_sum_le by presburger
  let ?rest =
    "?trace_final +
      (0 +
        (?alpha +
          (?degree +
            (0 +
              (?composition +
                (?composition_final + (0 + (?query + 0))))))))"
  have used_without_root:
    "?used \<le>
      (sum_list (trace_fri_budgets budgets) + ceil_log clength) +
        ?rest"
    using add_right_mono[OF trace_part_le, of ?rest]
    by (simp add: add.assoc)
  have used_le:
    "?used \<le>
      staged_attacker_query_budget budgets +
        staged_challenge_query_budget"
    using used_without_root
    unfolding staged_attacker_query_budget_def
      staged_challenge_query_budget_def
    by (simp add: add.assoc add.commute add.left_commute)
  show ?thesis
    by (rule hash_target_program_mono[OF used_le exact])
qed
end

end
