theory Soundness_FRI_Query_Future_Fresh_Zero_Budget
  imports Soundness_FRI_Conditioned_Explicit_Security_Target
begin

context soundness
begin

lemma controlled_ro_program_zero_hash_map_preserving:
  assumes controlled: "controlled_ro_program q m"
    and zero: "q = 0"
  shows "hash_map_preserving m"
  using controlled zero
proof (induction rule: controlled_ro_program.induct)
  case (Return x)
  show ?case by (rule hash_map_preserving_return)
next
  case Fail
  show ?case by (rule hash_map_preserving_throw)
next
  case (Sample d)
  show ?case by (rule hash_map_preserving_state_independent_sample)
next
  case (Query q k x)
  then show ?case by simp
next
  case (Bind q m r k)
  have q0: "q = 0" and r0: "r = 0"
    using Bind.prems by simp_all
  have head_preserving: "hash_map_preserving m"
    by (rule Bind.IH(1)[OF q0])
  have tail_preserving: "\<And>x. hash_map_preserving (k x)"
    using Bind.IH(2) r0 by blast
  show ?case
    unfolding hash_map_preserving_def
  proof (intro allI impI)
    fix s z t
    assume out: "Some (z, t) \<in> set_dist (execute (m \<bind> k) s)"
    then obtain x u where
      head: "Some (x, u) \<in> set_dist (execute m s)"
      and tail: "Some (z, t) \<in> set_dist (execute (k x) u)"
      by (auto elim!: set_dist_bindE)
    have map_u: "HashMap u = HashMap s"
      using head_preserving head
      unfolding hash_map_preserving_def by blast
    have map_t: "HashMap t = HashMap u"
      using tail_preserving[of x] tail
      unfolding hash_map_preserving_def by blast
    show "HashMap t = HashMap s"
      using map_u map_t by simp
  qed
next
  case (Weaken q m r)
  have q0: "q = 0"
    using Weaken.hyps Weaken.prems by simp
  show ?case
    by (rule Weaken.IH[OF q0])
qed


lemma controlled_ro_program_zero_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and controlled: "controlled_ro_program q m"
    and zero: "q = 0"
    and outcome: "Some (x, t) \<in> set_dist (execute m s)"
  shows "query_future_fresh t"
proof -
  have map_eq: "HashMap t = HashMap s"
    using controlled_ro_program_zero_hash_map_preserving[OF controlled zero]
      outcome
    unfolding hash_map_preserving_def by blast
  have counter_eq: "PQueryCounter t = PQueryCounter s"
    using controlled_ro_program_preserves_protocol_fields[OF controlled]
      outcome
    unfolding protocol_fields_preserving_def by blast
  show ?thesis
    using future map_eq counter_eq
    unfolding query_future_fresh_def by simp
qed


lemma query_future_fresh_lookupD:
  assumes future: "query_future_fresh s"
    and bound: "PQueryCounter s \<le> i"
  shows "fmlookup (HashMap s) (QueryIndexChallenge i x) = None"
  using future bound unfolding query_future_fresh_def by blast

lemma ro_record_staged_message_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some ((), t) \<in> set_dist (execute (ro_record_staged_message a) s)"
  shows "query_future_fresh t"
proof -
  from ro_record_staged_message_outcome[OF outcome]
  obtain h u where
    hash_out:
      "Some (h, u) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState s) a)) s)"
    and t_eq:
      "t = u\<lparr>PState := h, PTranscript := PTranscript u @ [a]\<rparr>"
    and counter_eq: "PQueryCounter u = PQueryCounter s"
    by blast
  show ?thesis
    unfolding query_future_fresh_def t_eq
  proof (intro allI impI)
    fix i x
    assume i_ge0:
      "PQueryCounter
        (u\<lparr>PState := h, PTranscript := PTranscript u @ [a]\<rparr>) \<le> i"
    have i_ge: "PQueryCounter u \<le> i"
      using i_ge0 by simp
    have i_ge_s: "PQueryCounter s \<le> i"
      using i_ge counter_eq by simp
    have old_none:
      "fmlookup (HashMap s) (QueryIndexChallenge i x) = None"
      by (rule query_future_fresh_lookupD[OF future i_ge_s])
    have neq:
      "QueryIndexChallenge i x \<noteq> TranscriptAbsorb (PState s) a"
      by simp
    show
      "fmlookup
        (HashMap (u\<lparr>PState := h, PTranscript := PTranscript u @ [a]\<rparr>))
        (QueryIndexChallenge i x) = None"
      using protocol_hash_preserves_other_lookup[OF hash_out neq] old_none
      by simp
  qed
qed

lemma receive_trace_fri_challenge_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s)"
  shows "query_future_fresh t"
proof -
  have counter_eq: "PQueryCounter t = PQueryCounter s"
    using receive_trace_fri_challenge_counter_outcome[OF outcome] by blast
  show ?thesis
    unfolding query_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge: "PQueryCounter t \<le> i"
    have i_ge_s: "PQueryCounter s \<le> i"
      using i_ge counter_eq by simp
    have old_none:
      "fmlookup (HashMap s) (QueryIndexChallenge i x) = None"
      by (rule query_future_fresh_lookupD[OF future i_ge_s])
    have neq:
      "QueryIndexChallenge i x \<noteq>
        TraceFriChallenge (PTraceFriCounter s) (PState s)"
      by simp
    show "fmlookup (HashMap t) (QueryIndexChallenge i x) = None"
      using receive_trace_fri_challenge_preserves_other_lookup[OF outcome neq]
        old_none
      by simp
  qed
qed

lemma receive_composition_fri_challenge_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some (b, t) \<in>
        set_dist (execute receive_composition_fri_challenge s)"
  shows "query_future_fresh t"
proof -
  have counter_eq: "PQueryCounter t = PQueryCounter s"
    using receive_composition_fri_challenge_counter_outcome[OF outcome] by blast
  show ?thesis
    unfolding query_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge: "PQueryCounter t \<le> i"
    have i_ge_s: "PQueryCounter s \<le> i"
      using i_ge counter_eq by simp
    have old_none:
      "fmlookup (HashMap s) (QueryIndexChallenge i x) = None"
      by (rule query_future_fresh_lookupD[OF future i_ge_s])
    have neq:
      "QueryIndexChallenge i x \<noteq>
        CompositionFriChallenge (PCompositionFriCounter s) (PState s)"
      by simp
    show "fmlookup (HashMap t) (QueryIndexChallenge i x) = None"
      using
        receive_composition_fri_challenge_preserves_other_lookup[OF outcome neq]
        old_none
      by simp
  qed
qed

lemma receive_alpha_challenge_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some (a, t) \<in> set_dist (execute receive_alpha_challenge s)"
  shows "query_future_fresh t"
proof -
  have counter_eq: "PQueryCounter t = PQueryCounter s"
    using receive_alpha_challenge_counter_outcome[OF outcome] by blast
  show ?thesis
    unfolding query_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge: "PQueryCounter t \<le> i"
    have i_ge_s: "PQueryCounter s \<le> i"
      using i_ge counter_eq by simp
    have old_none:
      "fmlookup (HashMap s) (QueryIndexChallenge i x) = None"
      by (rule query_future_fresh_lookupD[OF future i_ge_s])
    have neq:
      "QueryIndexChallenge i x \<noteq>
        AlphaChallenge (PAlphaCounter s) (PState s)"
      by simp
    show "fmlookup (HashMap t) (QueryIndexChallenge i x) = None"
      using receive_alpha_challenge_preserves_other_lookup[OF outcome neq]
        old_none
      by simp
  qed
qed


lemma staged_attacker_query_budget_zeroD:
  assumes zero: "staged_attacker_query_budget budgets = 0"
  shows
    "trace_root_budget budgets = 0 \<and>
     (\<forall>i < length (trace_fri_budgets budgets).
        trace_fri_budgets budgets ! i = 0) \<and>
     trace_final_budget budgets = 0 \<and>
     degree_budget budgets = 0 \<and>
     (\<forall>i < length (composition_fri_budgets budgets).
        composition_fri_budgets budgets ! i = 0) \<and>
     composition_final_budget budgets = 0 \<and>
     (\<forall>i < length (query_opening_budgets budgets).
        query_opening_budgets budgets ! i = 0)"
proof -
  have parts:
    "trace_root_budget budgets = 0"
    "sum_list (trace_fri_budgets budgets) = 0"
    "trace_final_budget budgets = 0"
    "degree_budget budgets = 0"
    "sum_list (composition_fri_budgets budgets) = 0"
    "composition_final_budget budgets = 0"
    "sum_list (query_opening_budgets budgets) = 0"
    using zero unfolding staged_attacker_query_budget_def by simp_all
  have trace_entries:
    "\<forall>i < length (trace_fri_budgets budgets).
      trace_fri_budgets budgets ! i = 0"
    using parts(2) by simp
  have composition_entries:
    "\<forall>i < length (composition_fri_budgets budgets).
      composition_fri_budgets budgets ! i = 0"
    using parts(5) by simp
  have query_entries:
    "\<forall>i < length (query_opening_budgets budgets).
      query_opening_budgets budgets ! i = 0"
    using parts(7) by simp
  show ?thesis
    using parts trace_entries composition_entries query_entries by blast
qed

lemma ro_staged_alpha_program_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some (as, t) \<in> set_dist (execute (ro_staged_alpha_program n) s)"
  shows "query_future_fresh t"
  using outcome future
proof (induction n arbitrary: s as t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain a s1 u s2 as_tail t0 where
    challenge:
      "Some (a, s1) \<in> set_dist (execute receive_alpha_challenge s)"
    and record_out:
      "Some (u, s2) \<in> set_dist (execute (ro_record_staged_message a) s1)"
    and tail:
      "Some (as_tail, t0) \<in>
        set_dist (execute (ro_staged_alpha_program n) s2)"
    and ret:
      "Some (as, t) \<in> set_dist (execute (return (a # as_tail)) t0)"
    unfolding ro_staged_alpha_program.simps
    by (auto elim!: set_dist_bindE)
  have u_eq: "u = ()" by (cases u) simp
  have future1:
    "query_future_fresh s1"
    by (rule receive_alpha_challenge_preserves_query_future_fresh[
        OF Suc.prems(2) challenge])
  have future2:
    "query_future_fresh s2"
    by (rule ro_record_staged_message_preserves_query_future_fresh[
        OF future1 record_out[unfolded u_eq]])
  have future_t0:
    "query_future_fresh t0"
    by (rule Suc.IH[OF tail future2])
  have t_eq: "t = t0"
    using ret by simp
  show ?case
    using future_t0 t_eq by simp
qed

lemma ro_staged_trace_fri_program_preserves_query_future_fresh_zero:
  assumes future: "query_future_fresh builder"
    and controlled:
      "\<forall>j cs. j < N \<longrightarrow>
        controlled_ro_program 0 (trace_fri_root_stage A j cs)"
    and bound: "i + n \<le> N"
    and outcome:
      "Some ((roots, bs'), sent) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A i n bs) builder)"
  shows "query_future_fresh sent"
  using outcome future bound
proof (induction n arbitrary: i bs roots bs' builder sent)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain root s1 s2 b s3 roots_tail bs_tail where
    stage_out:
      "Some (root, s1) \<in>
        set_dist (execute (trace_fri_root_stage A i bs) builder)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in>
        set_dist (execute receive_trace_fri_challenge s2)"
    and tail_out:
      "Some ((roots_tail, bs_tail), sent) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A (Suc i) n (bs @ [b])) s3)"
    unfolding ro_staged_trace_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  have i_bound: "i < N"
    using Suc.prems(3) by simp
  have tail_bound: "Suc i + n \<le> N"
    using Suc.prems(3) by simp
  have future1: "query_future_fresh s1"
    by (rule controlled_ro_program_zero_preserves_query_future_fresh[
          OF Suc.prems(2) controlled[rule_format, OF i_bound]
            refl stage_out])
  have future2: "query_future_fresh s2"
    by (rule ro_record_staged_message_preserves_query_future_fresh[
          OF future1 record_out])
  have future3: "query_future_fresh s3"
    by (rule receive_trace_fri_challenge_preserves_query_future_fresh[
          OF future2 challenge_out])
  show ?case
    by (rule Suc.IH[OF tail_out future3 tail_bound])
qed

lemma ro_staged_composition_fri_program_preserves_query_future_fresh_zero:
  assumes future: "query_future_fresh builder"
    and controlled:
      "\<forall>dg j cs. j < N \<longrightarrow>
        controlled_ro_program 0 (composition_fri_root_stage A dg j cs)"
    and bound: "i + n \<le> N"
    and outcome:
      "Some ((roots, bs'), sent) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg i n bs) builder)"
  shows "query_future_fresh sent"
  using outcome future bound
proof (induction n arbitrary: i bs roots bs' builder sent)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain root s1 s2 b s3 roots_tail bs_tail where
    stage_out:
      "Some (root, s1) \<in>
        set_dist (execute (composition_fri_root_stage A dg i bs) builder)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in>
        set_dist (execute receive_composition_fri_challenge s2)"
    and tail_out:
      "Some ((roots_tail, bs_tail), sent) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg (Suc i) n
              (bs @ [b])) s3)"
    unfolding ro_staged_composition_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  have i_bound: "i < N"
    using Suc.prems(3) by simp
  have tail_bound: "Suc i + n \<le> N"
    using Suc.prems(3) by simp
  have future1: "query_future_fresh s1"
    by (rule controlled_ro_program_zero_preserves_query_future_fresh[
          OF Suc.prems(2) controlled[rule_format, OF i_bound]
            refl stage_out])
  have future2: "query_future_fresh s2"
    by (rule ro_record_staged_message_preserves_query_future_fresh[
          OF future1 record_out])
  have future3: "query_future_fresh s3"
    by (rule receive_composition_fri_challenge_preserves_query_future_fresh[
          OF future2 challenge_out])
  show ?case
    by (rule Suc.IH[OF tail_out future3 tail_bound])
qed

lemma ro_record_staged_messages_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some ((), t) \<in>
        set_dist (execute (ro_record_staged_messages xs) s)"
  shows "query_future_fresh t"
  using outcome future
proof (induction xs arbitrary: s t)
  case Nil
  then show ?case
    unfolding ro_record_staged_messages_def by simp
next
  case (Cons x xs)
  from Cons.prems(1) obtain u where
    head:
      "Some ((), u) \<in>
        set_dist (execute (ro_record_staged_message x) s)"
    and tail:
      "Some ((), t) \<in>
        set_dist (execute (ro_record_staged_messages xs) u)"
    unfolding ro_record_staged_messages_def
    by (auto elim!: set_dist_bindE)
  have future_u: "query_future_fresh u"
    by (rule ro_record_staged_message_preserves_query_future_fresh[
          OF Cons.prems(2) head])
  show ?case
    by (rule Cons.IH[OF tail future_u])
qed

lemma ro_checked_staged_query_program_with_witnesses_future_fresh_hit_zero:
  assumes future: "query_future_fresh s"
    and controlled:
      "\<forall>j raw. j < N \<longrightarrow>
        controlled_ro_program 0 (query_opening_stage A j raw)"
    and bound: "i + n \<le> N"
    and outcome:
      "Some ((raws, query_states, chunks), t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots s i n)
            s)"
  shows
    "ro_query_witnesses_raws_fresh_hit raws
      (Some ((raws, query_states, chunks), t))"
  using outcome future bound
proof (induction n arbitrary: i s t raws query_states chunks)
  case 0
  then show ?case
    unfolding ro_query_witnesses_raws_fresh_hit_def by simp
next
  case (Suc n)
  from Suc.prems(1)
  obtain raw chunk raws_tail query_states_tail chunks_tail
      s1 s2 s_assert s3 where
    challenge_out:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and stage_out:
      "Some (chunk, s2) \<in>
        set_dist (execute (query_opening_stage A i raw) s1)"
    and assert_out:
      "Some ((), s_assert) \<in>
        set_dist
          (execute
            (assert
              (verifier_query_round_chunk (index (to_nat raw))
                trace_roots composition_roots chunk))
            s2)"
    and record_out:
      "Some ((), s3) \<in>
        set_dist (execute (ro_record_staged_messages chunk) s_assert)"
    and tail_out:
      "Some ((raws_tail, query_states_tail, chunks_tail), t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots s3 (Suc i) n)
            s3)"
    and raws_eq: "raws = raw # raws_tail"
    and query_states_eq: "query_states = s # query_states_tail"
    and chunks_eq: "chunks = chunk # chunks_tail"
    unfolding ro_checked_staged_query_program_with_witnesses.simps Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have assert_eq: "s_assert = s2"
    using assert_out unfolding assert_def
    by (cases
        "verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk")
      (simp_all add: throw_no_outcome)
  have i_bound: "i < N"
    using Suc.prems(3) by simp
  have tail_bound: "Suc i + n \<le> N"
    using Suc.prems(3) by simp
  have current_fresh:
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
    by (rule query_future_fresh_current[OF Suc.prems(2)])
  have future1: "query_future_fresh s1"
    by (rule receive_query_index_challenge_preserves_query_future_fresh[
          OF Suc.prems(2) challenge_out])
  have future2: "query_future_fresh s2"
    by (rule controlled_ro_program_zero_preserves_query_future_fresh[
          OF future1 controlled[rule_format, OF i_bound] refl stage_out])
  have record_out':
    "Some ((), s3) \<in>
      set_dist (execute (ro_record_staged_messages chunk) s2)"
    using record_out assert_eq by simp
  have future3: "query_future_fresh s3"
    by (rule ro_record_staged_messages_preserves_query_future_fresh[
          OF future2 record_out'])
  have tail_hit:
    "ro_query_witnesses_raws_fresh_hit raws_tail
      (Some ((raws_tail, query_states_tail, chunks_tail), t))"
    by (rule Suc.IH[OF tail_out future3 tail_bound])
  show ?case
    using current_fresh tail_hit
    unfolding ro_query_witnesses_raws_fresh_hit_def
      raws_eq query_states_eq chunks_eq
    by (auto simp: nth_Cons split: nat.splits)
qed

lemma staged_adversary_controlled_query_budget_zeroD:
  assumes controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
  shows
    "controlled_ro_program 0 (trace_root_stage A) \<and>
     (\<forall>i < length (trace_fri_budgets budgets). \<forall>bs.
       controlled_ro_program 0 (trace_fri_root_stage A i bs)) \<and>
     (\<forall>bs. controlled_ro_program 0 (trace_final_stage A bs)) \<and>
     (\<forall>as. controlled_ro_program 0 (degree_stage A as)) \<and>
     (\<forall>dg i. i < length (composition_fri_budgets budgets) \<longrightarrow>
       (\<forall>bs. controlled_ro_program 0
         (composition_fri_root_stage A dg i bs))) \<and>
     (\<forall>dg bs.
       controlled_ro_program 0 (composition_final_stage A dg bs)) \<and>
     (\<forall>i < length (query_opening_budgets budgets). \<forall>raw.
       controlled_ro_program 0 (query_opening_stage A i raw))"
proof -
  have zeros:
    "trace_root_budget budgets = 0 \<and>
     (\<forall>i < length (trace_fri_budgets budgets).
        trace_fri_budgets budgets ! i = 0) \<and>
     trace_final_budget budgets = 0 \<and>
     degree_budget budgets = 0 \<and>
     (\<forall>i < length (composition_fri_budgets budgets).
        composition_fri_budgets budgets ! i = 0) \<and>
     composition_final_budget budgets = 0 \<and>
     (\<forall>i < length (query_opening_budgets budgets).
        query_opening_budgets budgets ! i = 0)"
    by (rule staged_attacker_query_budget_zeroD[OF zero])
  show ?thesis
    using controlled zeros
    unfolding staged_adversary_controlled_def
    by auto
qed

lemma ro_staged_first_trace_fri_root_prefix_program_preserves_query_future_fresh_zero:
  assumes future: "query_future_fresh s"
    and trace_root:
      "controlled_ro_program 0 (trace_root_stage A)"
    and trace_fri_root:
      "0 < ceil_log clength \<Longrightarrow>
        controlled_ro_program 0 (trace_fri_root_stage A 0 [])"
    and outcome:
      "Some (result, t) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A) s)"
  shows "query_future_fresh t"
proof (cases "ceil_log clength")
  case 0
  from outcome obtain fr s1 s2 where
    stage_out:
      "Some (fr, s1) \<in> set_dist (execute (trace_root_stage A) s)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message fr) s1)"
    and t_eq: "t = s2"
    unfolding ro_staged_first_trace_fri_root_prefix_program_def 0
    by (auto elim!: set_dist_bindE)
  have future1: "query_future_fresh s1"
    by (rule controlled_ro_program_zero_preserves_query_future_fresh[
          OF future trace_root refl stage_out])
  have future2: "query_future_fresh s2"
    by (rule ro_record_staged_message_preserves_query_future_fresh[
          OF future1 record_out])
  show ?thesis using future2 t_eq by simp
next
  case (Suc n)
  from outcome obtain fr s1 s2 first_root s3 s4 where
    trace_stage_out:
      "Some (fr, s1) \<in> set_dist (execute (trace_root_stage A) s)"
    and trace_record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message fr) s1)"
    and fri_stage_out:
      "Some (first_root, s3) \<in>
        set_dist (execute (trace_fri_root_stage A 0 []) s2)"
    and fri_record_out:
      "Some ((), s4) \<in>
        set_dist (execute (ro_record_staged_message first_root) s3)"
    and t_eq: "t = s4"
    unfolding ro_staged_first_trace_fri_root_prefix_program_def Suc
    by (auto elim!: set_dist_bindE)
  have future1: "query_future_fresh s1"
    by (rule controlled_ro_program_zero_preserves_query_future_fresh[
          OF future trace_root refl trace_stage_out])
  have future2: "query_future_fresh s2"
    by (rule ro_record_staged_message_preserves_query_future_fresh[
          OF future1 trace_record_out])
  have first_controlled:
    "controlled_ro_program 0 (trace_fri_root_stage A 0 [])"
    by (rule trace_fri_root) (simp add: Suc)
  have future3: "query_future_fresh s3"
    by (rule controlled_ro_program_zero_preserves_query_future_fresh[
          OF future2 first_controlled refl fri_stage_out])
  have future4: "query_future_fresh s4"
    by (rule ro_record_staged_message_preserves_query_future_fresh[
          OF future3 fri_record_out])
  show ?thesis using future4 t_eq by simp
qed

lemma
  ro_checked_staged_after_first_trace_fri_root_prefix_program_preserves_query_future_fresh_zero:
  assumes future: "query_future_fresh s"
    and trace_fri:
      "\<forall>j < ceil_log clength. \<forall>bs.
        controlled_ro_program 0 (trace_fri_root_stage A j bs)"
    and trace_final:
      "\<forall>bs. controlled_ro_program 0 (trace_final_stage A bs)"
    and degree:
      "\<forall>as. controlled_ro_program 0 (degree_stage A as)"
    and composition_fri:
      "\<forall>dg j. j < ceil_log (maxDegree + 1) \<longrightarrow>
        (\<forall>bs. controlled_ro_program 0
          (composition_fri_root_stage A dg j bs))"
    and composition_final:
      "\<forall>dg bs.
        controlled_ro_program 0 (composition_final_stage A dg bs)"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program
              A prefix)
            s)"
  shows "query_future_fresh t"
proof -
  obtain fr trace_bs first_root where
    prefix_eq: "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  have trace_fri_all:
    "\<forall>j bs. j < ceil_log clength \<longrightarrow>
      controlled_ro_program 0 (trace_fri_root_stage A j bs)"
    using trace_fri by blast
  have composition_fri_all:
    "\<forall>dg j bs. j < ceil_log (maxDegree + 1) \<longrightarrow>
      controlled_ro_program 0
        (composition_fri_root_stage A dg j bs)"
    using composition_fri by blast
  show ?thesis
  proof (cases "ceil_log clength")
    case 0
    from outcome obtain trace_final_value s1 s2 as s3 dg s4 s5
        s_assert composition_roots composition_bs s6
        composition_final_value s7 s8 where
      trace_final_out:
        "Some (trace_final_value, s1) \<in>
          set_dist (execute (trace_final_stage A []) s)"
      and trace_record_out:
        "Some ((), s2) \<in>
          set_dist
            (execute (ro_record_staged_message trace_final_value) s1)"
      and alpha_out:
        "Some (as, s3) \<in>
          set_dist (execute (ro_staged_alpha_program (length spec)) s2)"
      and degree_out:
        "Some (dg, s4) \<in> set_dist (execute (degree_stage A as) s3)"
      and degree_record_out:
        "Some ((), s5) \<in>
          set_dist (execute (ro_record_staged_message dg) s4)"
      and assert_out:
        "Some ((), s_assert) \<in>
          set_dist
            (execute
              (assert
                (ceil_log (to_nat dg + 1) \<le>
                  ceil_log (maxDegree + 1)))
              s5)"
      and composition_out:
        "Some ((composition_roots, composition_bs), s6) \<in>
          set_dist
            (execute
              (ro_staged_composition_fri_program A dg 0
                (ceil_log (to_nat dg + 1)) [])
              s_assert)"
      and composition_final_out:
        "Some (composition_final_value, s7) \<in>
          set_dist
            (execute
              (composition_final_stage A dg composition_bs) s6)"
      and composition_record_out:
        "Some ((), s8) \<in>
          set_dist
            (execute
              (ro_record_staged_message composition_final_value) s7)"
      and t_eq: "t = s8"
      using outcome
      unfolding
        ro_checked_staged_after_first_trace_fri_root_prefix_program_def
        prefix_eq 0 Let_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    have assert_props:
      "s_assert = s5 \<and>
       ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
      using assert_out unfolding assert_def
      by (cases
          "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
        (simp_all add: throw_no_outcome)
    have composition_bound:
      "0 + ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
      using assert_props by simp
    have future1: "query_future_fresh s1"
      by (rule controlled_ro_program_zero_preserves_query_future_fresh[
            OF future trace_final[rule_format] refl trace_final_out])
    have future2: "query_future_fresh s2"
      by (rule ro_record_staged_message_preserves_query_future_fresh[
            OF future1 trace_record_out])
    have future3: "query_future_fresh s3"
      by (rule ro_staged_alpha_program_preserves_query_future_fresh[
            OF future2 alpha_out])
    have future4: "query_future_fresh s4"
      by (rule controlled_ro_program_zero_preserves_query_future_fresh[
            OF future3 degree[rule_format] refl degree_out])
    have future5: "query_future_fresh s5"
      by (rule ro_record_staged_message_preserves_query_future_fresh[
            OF future4 degree_record_out])
    have composition_out':
      "Some ((composition_roots, composition_bs), s6) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])
            s5)"
      using composition_out assert_props by simp
    have future6: "query_future_fresh s6"
      by (rule
          ro_staged_composition_fri_program_preserves_query_future_fresh_zero[
            OF future5 composition_fri_all
              composition_bound composition_out'])
    have future7: "query_future_fresh s7"
      by (rule controlled_ro_program_zero_preserves_query_future_fresh[
            OF future6 composition_final[rule_format] refl
              composition_final_out])
    have future8: "query_future_fresh s8"
      by (rule ro_record_staged_message_preserves_query_future_fresh[
            OF future7 composition_record_out])
    show ?thesis using future8 t_eq by simp
  next
    case (Suc n)
    from outcome obtain b s1 trace_roots trace_bs' s2
        trace_final_value s3 s4 as s5 dg s6 s7 s_assert
        composition_roots composition_bs s8 composition_final_value s9 s10
      where
      challenge_out:
        "Some (b, s1) \<in>
          set_dist (execute receive_trace_fri_challenge s)"
      and trace_fri_out:
        "Some ((trace_roots, trace_bs'), s2) \<in>
          set_dist
            (execute
              (ro_staged_trace_fri_program A 1 n
                (trace_bs @ [b]))
              s1)"
      and trace_final_out:
        "Some (trace_final_value, s3) \<in>
          set_dist (execute (trace_final_stage A trace_bs') s2)"
      and trace_record_out:
        "Some ((), s4) \<in>
          set_dist
            (execute (ro_record_staged_message trace_final_value) s3)"
      and alpha_out:
        "Some (as, s5) \<in>
          set_dist (execute (ro_staged_alpha_program (length spec)) s4)"
      and degree_out:
        "Some (dg, s6) \<in> set_dist (execute (degree_stage A as) s5)"
      and degree_record_out:
        "Some ((), s7) \<in>
          set_dist (execute (ro_record_staged_message dg) s6)"
      and assert_out:
        "Some ((), s_assert) \<in>
          set_dist
            (execute
              (assert
                (ceil_log (to_nat dg + 1) \<le>
                  ceil_log (maxDegree + 1)))
              s7)"
      and composition_out:
        "Some ((composition_roots, composition_bs), s8) \<in>
          set_dist
            (execute
              (ro_staged_composition_fri_program A dg 0
                (ceil_log (to_nat dg + 1)) [])
              s_assert)"
      and composition_final_out:
        "Some (composition_final_value, s9) \<in>
          set_dist
            (execute
              (composition_final_stage A dg composition_bs) s8)"
      and composition_record_out:
        "Some ((), s10) \<in>
          set_dist
            (execute
              (ro_record_staged_message composition_final_value) s9)"
      and t_eq: "t = s10"
      using outcome
      unfolding
        ro_checked_staged_after_first_trace_fri_root_prefix_program_def
        prefix_eq Suc Let_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    have assert_props:
      "s_assert = s7 \<and>
       ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
      using assert_out unfolding assert_def
      by (cases
          "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
        (simp_all add: throw_no_outcome)
    have composition_bound:
      "0 + ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
      using assert_props by simp
    have future1: "query_future_fresh s1"
      by (rule receive_trace_fri_challenge_preserves_query_future_fresh[
            OF future challenge_out])
    have future2: "query_future_fresh s2"
      by (rule
          ro_staged_trace_fri_program_preserves_query_future_fresh_zero[
            OF future1 trace_fri_all])
        (use Suc trace_fri_out in simp_all)
    have future3: "query_future_fresh s3"
      by (rule controlled_ro_program_zero_preserves_query_future_fresh[
            OF future2 trace_final[rule_format] refl trace_final_out])
    have future4: "query_future_fresh s4"
      by (rule ro_record_staged_message_preserves_query_future_fresh[
            OF future3 trace_record_out])
    have future5: "query_future_fresh s5"
      by (rule ro_staged_alpha_program_preserves_query_future_fresh[
            OF future4 alpha_out])
    have future6: "query_future_fresh s6"
      by (rule controlled_ro_program_zero_preserves_query_future_fresh[
            OF future5 degree[rule_format] refl degree_out])
    have future7: "query_future_fresh s7"
      by (rule ro_record_staged_message_preserves_query_future_fresh[
            OF future6 degree_record_out])
    have composition_out':
      "Some ((composition_roots, composition_bs), s8) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])
            s7)"
      using composition_out assert_props by simp
    have future8: "query_future_fresh s8"
      by (rule
          ro_staged_composition_fri_program_preserves_query_future_fresh_zero[
            OF future7 composition_fri_all
              composition_bound composition_out'])
    have future9: "query_future_fresh s9"
      by (rule controlled_ro_program_zero_preserves_query_future_fresh[
            OF future8 composition_final[rule_format] refl
              composition_final_out])
    have future10: "query_future_fresh s10"
      by (rule ro_record_staged_message_preserves_query_future_fresh[
            OF future9 composition_record_out])
    show ?thesis using future10 t_eq by simp
  qed
qed

lemma ro_checked_staged_first_root_query_head_program_preserves_query_future_fresh_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
    and future: "query_future_fresh s"
    and outcome:
      "Some (result, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_first_root_query_head_program A) s)"
  shows "query_future_fresh t"
proof -
  have zero_controlled:
    "controlled_ro_program 0 (trace_root_stage A) \<and>
     (\<forall>i < length (trace_fri_budgets budgets). \<forall>bs.
       controlled_ro_program 0 (trace_fri_root_stage A i bs)) \<and>
     (\<forall>bs. controlled_ro_program 0 (trace_final_stage A bs)) \<and>
     (\<forall>as. controlled_ro_program 0 (degree_stage A as)) \<and>
     (\<forall>dg i. i < length (composition_fri_budgets budgets) \<longrightarrow>
       (\<forall>bs. controlled_ro_program 0
         (composition_fri_root_stage A dg i bs))) \<and>
     (\<forall>dg bs.
       controlled_ro_program 0 (composition_final_stage A dg bs)) \<and>
     (\<forall>i < length (query_opening_budgets budgets). \<forall>raw.
       controlled_ro_program 0 (query_opening_stage A i raw))"
    by (rule staged_adversary_controlled_query_budget_zeroD[
          OF controlled zero])
  have lengths:
    "length (trace_fri_budgets budgets) = ceil_log clength \<and>
     length (composition_fri_budgets budgets) =
       ceil_log (maxDegree + 1) \<and>
     length (query_opening_budgets budgets) = rounds"
    using wf unfolding staged_budget_wellformed_def by blast
  have trace_root_controlled:
    "controlled_ro_program 0 (trace_root_stage A)"
    using zero_controlled by blast
  have trace_fri_controlled:
    "\<forall>j < ceil_log clength. \<forall>bs.
      controlled_ro_program 0 (trace_fri_root_stage A j bs)"
    using zero_controlled lengths by simp
  have trace_final_controlled:
    "\<forall>bs. controlled_ro_program 0 (trace_final_stage A bs)"
    using zero_controlled by blast
  have degree_controlled:
    "\<forall>as. controlled_ro_program 0 (degree_stage A as)"
    using zero_controlled by blast
  have composition_fri_controlled:
    "\<forall>dg j. j < ceil_log (maxDegree + 1) \<longrightarrow>
      (\<forall>bs. controlled_ro_program 0
        (composition_fri_root_stage A dg j bs))"
    using zero_controlled lengths by simp
  have composition_final_controlled:
    "\<forall>dg bs.
      controlled_ro_program 0 (composition_final_stage A dg bs)"
    using zero_controlled by blast
  from outcome obtain prefix_with_state s1 data s2 where
    prefix_out:
      "Some (prefix_with_state, s1) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A) s)"
    and after_out:
      "Some (data, s2) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              (fst prefix_with_state))
            s1)"
    and t_eq: "t = s2"
    unfolding ro_checked_staged_first_root_query_head_program_def
    by (auto elim!: set_dist_bindE)
  have future1: "query_future_fresh s1"
  proof (rule
      ro_staged_first_trace_fri_root_prefix_program_preserves_query_future_fresh_zero[
        OF future trace_root_controlled _ prefix_out])
    assume positive: "0 < ceil_log clength"
    show
      "controlled_ro_program 0 (trace_fri_root_stage A 0 [])"
      using trace_fri_controlled positive by blast
  qed
  have future2: "query_future_fresh s2"
    by (rule
        ro_checked_staged_after_first_trace_fri_root_prefix_program_preserves_query_future_fresh_zero[
          OF future1 trace_fri_controlled trace_final_controlled
            degree_controlled composition_fri_controlled
            composition_final_controlled after_out])
  show ?thesis using future2 t_eq by simp
qed


end
end
