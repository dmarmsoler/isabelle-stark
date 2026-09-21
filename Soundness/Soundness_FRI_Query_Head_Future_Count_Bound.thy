theory Soundness_FRI_Query_Head_Future_Count_Bound
  imports Stark.Staged_Security_Experiment_RO_Query_List_Future_Count_Exact_Product
begin

context soundness
begin


lemma query_future_keys_eqI:
  assumes counter: "PQueryCounter t = PQueryCounter s"
    and lookup:
      "\<And>i x. fmlookup (HashMap t) (QueryIndexChallenge i x) =
        fmlookup (HashMap s) (QueryIndexChallenge i x)"
  shows "query_future_keys t = query_future_keys s"
proof -
  have dom:
    "\<And>i x.
      QueryIndexChallenge i x \<in> fmdom' (HashMap t) \<longleftrightarrow>
      QueryIndexChallenge i x \<in> fmdom' (HashMap s)"
  proof -
    fix i x
    show
      "QueryIndexChallenge i x \<in> fmdom' (HashMap t) \<longleftrightarrow>
       QueryIndexChallenge i x \<in> fmdom' (HashMap s)"
      using lookup[of i x]
      by (simp add: fmlookup_dom'_iff)
  qed
  show ?thesis
    unfolding query_future_keys_def counter
    using dom by blast
qed

lemma receive_trace_fri_challenge_query_future_keys_eq:
  assumes outcome:
    "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s)"
  shows "query_future_keys t = query_future_keys s"
proof (rule query_future_keys_eqI)
  show "PQueryCounter t = PQueryCounter s"
    using receive_trace_fri_challenge_counter_outcome[OF outcome] by blast
next
  fix i x
  have neq:
    "QueryIndexChallenge i x \<noteq>
      TraceFriChallenge (PTraceFriCounter s) (PState s)"
    by simp
  show
    "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
    by (rule receive_trace_fri_challenge_preserves_other_lookup[
          OF outcome neq])
qed

lemma receive_composition_fri_challenge_query_future_keys_eq:
  assumes outcome:
    "Some (b, t) \<in>
      set_dist (execute receive_composition_fri_challenge s)"
  shows "query_future_keys t = query_future_keys s"
proof (rule query_future_keys_eqI)
  show "PQueryCounter t = PQueryCounter s"
    using receive_composition_fri_challenge_counter_outcome[OF outcome]
    by blast
next
  fix i x
  have neq:
    "QueryIndexChallenge i x \<noteq>
      CompositionFriChallenge (PCompositionFriCounter s) (PState s)"
    by simp
  show
    "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
    by (rule receive_composition_fri_challenge_preserves_other_lookup[
          OF outcome neq])
qed

lemma receive_alpha_challenge_query_future_keys_eq:
  assumes outcome:
    "Some (a, t) \<in> set_dist (execute receive_alpha_challenge s)"
  shows "query_future_keys t = query_future_keys s"
proof (rule query_future_keys_eqI)
  show "PQueryCounter t = PQueryCounter s"
    using receive_alpha_challenge_counter_outcome[OF outcome] by blast
next
  fix i x
  have neq:
    "QueryIndexChallenge i x \<noteq>
      AlphaChallenge (PAlphaCounter s) (PState s)"
    by simp
  show
    "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
    by (rule receive_alpha_challenge_preserves_other_lookup[
          OF outcome neq])
qed

lemma receive_trace_fri_challenge_query_future_prequery_count_eq:
  assumes outcome:
    "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s)"
  shows
    "query_future_prequery_count t = query_future_prequery_count s"
  unfolding query_future_prequery_count_def
  using receive_trace_fri_challenge_query_future_keys_eq[OF outcome]
  by simp

lemma receive_composition_fri_challenge_query_future_prequery_count_eq:
  assumes outcome:
    "Some (b, t) \<in>
      set_dist (execute receive_composition_fri_challenge s)"
  shows
    "query_future_prequery_count t = query_future_prequery_count s"
  unfolding query_future_prequery_count_def
  using receive_composition_fri_challenge_query_future_keys_eq[OF outcome]
  by simp

lemma receive_alpha_challenge_query_future_prequery_count_eq:
  assumes outcome:
    "Some (a, t) \<in> set_dist (execute receive_alpha_challenge s)"
  shows
    "query_future_prequery_count t = query_future_prequery_count s"
  unfolding query_future_prequery_count_def
  using receive_alpha_challenge_query_future_keys_eq[OF outcome]
  by simp


lemma ro_staged_alpha_program_query_future_prequery_count_eq:
  assumes outcome:
    "Some (as, t) \<in> set_dist (execute (ro_staged_alpha_program n) s)"
  shows
    "query_future_prequery_count t = query_future_prequery_count s"
  using outcome
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
  have count1:
    "query_future_prequery_count s1 = query_future_prequery_count s"
    by (rule receive_alpha_challenge_query_future_prequery_count_eq[
          OF challenge])
  have count2:
    "query_future_prequery_count s2 = query_future_prequery_count s1"
    by (rule ro_record_staged_message_query_future_prequery_count_eq[
          OF record_out[unfolded u_eq]])
  have count_t0:
    "query_future_prequery_count t0 = query_future_prequery_count s2"
    by (rule Suc.IH[OF tail])
  have t_eq: "t = t0"
    using ret by simp
  show ?case
    using count1 count2 count_t0 t_eq by simp
qed


lemma ro_staged_trace_fri_program_query_future_prequery_count_bound:
  assumes controlled:
      "\<forall>j cs. j < length qs \<longrightarrow>
        controlled_ro_program (qs ! j) (trace_fri_root_stage A j cs)"
    and bound: "i + n \<le> length qs"
    and outcome:
      "Some ((roots, bs'), sent) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A i n bs) builder)"
  shows
    "query_future_prequery_count sent \<le>
      query_future_prequery_count builder +
        sum_list (take n (drop i qs))"
  using outcome bound
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
  have i_bound: "i < length qs"
    using Suc.prems(2) by simp
  have tail_bound: "Suc i + n \<le> length qs"
    using Suc.prems(2) by simp
  have count1:
    "query_future_prequery_count s1 \<le>
      query_future_prequery_count builder + qs ! i"
    by (rule controlled_ro_program_query_future_prequery_count_bound[
          OF controlled[rule_format, OF i_bound] stage_out])
  have count2:
    "query_future_prequery_count s2 = query_future_prequery_count s1"
    by (rule ro_record_staged_message_query_future_prequery_count_eq[
          OF record_out])
  have count3:
    "query_future_prequery_count s3 = query_future_prequery_count s2"
    by (rule receive_trace_fri_challenge_query_future_prequery_count_eq[
          OF challenge_out])
  have tail:
    "query_future_prequery_count sent \<le>
      query_future_prequery_count s3 +
        sum_list (take n (drop (Suc i) qs))"
    by (rule Suc.IH[OF tail_out tail_bound])
  have sum_eq:
    "sum_list (take (Suc n) (drop i qs)) =
      qs ! i + sum_list (take n (drop (Suc i) qs))"
    by (rule sum_list_take_Suc_drop[OF i_bound])
  show ?case
    using count1 count2 count3 tail
    unfolding sum_eq by linarith
qed

lemma ro_staged_composition_fri_program_query_future_prequery_count_bound:
  assumes controlled:
      "\<forall>dg j cs. j < length qs \<longrightarrow>
        controlled_ro_program (qs ! j)
          (composition_fri_root_stage A dg j cs)"
    and bound: "i + n \<le> length qs"
    and outcome:
      "Some ((roots, bs'), sent) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg i n bs) builder)"
  shows
    "query_future_prequery_count sent \<le>
      query_future_prequery_count builder +
        sum_list (take n (drop i qs))"
  using outcome bound
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
  have i_bound: "i < length qs"
    using Suc.prems(2) by simp
  have tail_bound: "Suc i + n \<le> length qs"
    using Suc.prems(2) by simp
  have count1:
    "query_future_prequery_count s1 \<le>
      query_future_prequery_count builder + qs ! i"
    by (rule controlled_ro_program_query_future_prequery_count_bound[
          OF controlled[rule_format, OF i_bound] stage_out])
  have count2:
    "query_future_prequery_count s2 = query_future_prequery_count s1"
    by (rule ro_record_staged_message_query_future_prequery_count_eq[
          OF record_out])
  have count3:
    "query_future_prequery_count s3 = query_future_prequery_count s2"
    by (rule
        receive_composition_fri_challenge_query_future_prequery_count_eq[
          OF challenge_out])
  have tail:
    "query_future_prequery_count sent \<le>
      query_future_prequery_count s3 +
        sum_list (take n (drop (Suc i) qs))"
    by (rule Suc.IH[OF tail_out tail_bound])
  have sum_eq:
    "sum_list (take (Suc n) (drop i qs)) =
      qs ! i + sum_list (take n (drop (Suc i) qs))"
    by (rule sum_list_take_Suc_drop[OF i_bound])
  show ?case
    using count1 count2 count3 tail
    unfolding sum_eq by linarith
qed


lemma ro_staged_first_trace_fri_root_prefix_program_query_future_count_bound:
  assumes trace_root:
      "controlled_ro_program q0 (trace_root_stage A)"
    and trace_length: "length qs = ceil_log clength"
    and trace_fri:
      "\<forall>j < length qs. \<forall>bs.
        controlled_ro_program (qs ! j) (trace_fri_root_stage A j bs)"
    and outcome:
      "Some (result, t) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A) s)"
  shows
    "query_future_prequery_count t \<le>
      query_future_prequery_count s + q0 + sum_list (take 1 qs)"
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
  have count1:
    "query_future_prequery_count s1 \<le>
      query_future_prequery_count s + q0"
    by (rule controlled_ro_program_query_future_prequery_count_bound[
          OF trace_root stage_out])
  have count2:
    "query_future_prequery_count s2 = query_future_prequery_count s1"
    by (rule ro_record_staged_message_query_future_prequery_count_eq[
          OF record_out])
  have qs_empty: "qs = []"
    using trace_length 0 by simp
  show ?thesis
    using count1 count2 t_eq unfolding qs_empty by simp
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
  have qs_nonempty: "qs \<noteq> []"
    using trace_length Suc by auto
  have zero_bound: "0 < length qs"
    using qs_nonempty by simp
  have count1:
    "query_future_prequery_count s1 \<le>
      query_future_prequery_count s + q0"
    by (rule controlled_ro_program_query_future_prequery_count_bound[
          OF trace_root trace_stage_out])
  have count2:
    "query_future_prequery_count s2 = query_future_prequery_count s1"
    by (rule ro_record_staged_message_query_future_prequery_count_eq[
          OF trace_record_out])
  have first_controlled:
    "controlled_ro_program (qs ! 0) (trace_fri_root_stage A 0 [])"
    using trace_fri zero_bound by blast
  have count3:
    "query_future_prequery_count s3 \<le>
      query_future_prequery_count s2 + qs ! 0"
    by (rule controlled_ro_program_query_future_prequery_count_bound[
          OF first_controlled fri_stage_out])
  have count4:
    "query_future_prequery_count s4 = query_future_prequery_count s3"
    by (rule ro_record_staged_message_query_future_prequery_count_eq[
          OF fri_record_out])
  have take_one: "sum_list (take 1 qs) = qs ! 0"
    using qs_nonempty by (cases qs) simp_all
  have count13:
    "query_future_prequery_count s3 \<le>
      (query_future_prequery_count s + q0) + qs ! 0"
  proof (rule order_trans[OF count3])
    show
      "query_future_prequery_count s2 + qs ! 0 \<le>
        (query_future_prequery_count s + q0) + qs ! 0"
      using count1 count2 by simp
  qed
  show ?thesis
    using count13 count4 t_eq
    unfolding take_one by simp
qed
lemma nat_le_add_trans:
  fixes x y a b z :: nat
  assumes first: "x \<le> y + a"
    and second: "z \<le> x + b"
  shows "z \<le> y + (a + b)"
proof -
  have upper: "x + b \<le> (y + a) + b"
    using first by simp
  have middle: "z \<le> (y + a) + b"
    using second upper by (rule order_trans)
  show ?thesis
    using middle by (simp add: add.assoc)
qed


lemma
  ro_checked_staged_after_first_trace_fri_root_prefix_program_query_future_count_bound:
  assumes trace_length: "length trace_qs = ceil_log clength"
    and composition_length:
      "length composition_qs = ceil_log (maxDegree + 1)"
    and trace_fri:
      "\<forall>j bs. j < length trace_qs \<longrightarrow>
        controlled_ro_program (trace_qs ! j)
          (trace_fri_root_stage A j bs)"
    and trace_final:
      "\<forall>bs. controlled_ro_program trace_final_q
        (trace_final_stage A bs)"
    and degree:
      "\<forall>as. controlled_ro_program degree_q (degree_stage A as)"
    and composition_fri:
      "\<forall>dg j bs. j < length composition_qs \<longrightarrow>
        controlled_ro_program (composition_qs ! j)
          (composition_fri_root_stage A dg j bs)"
    and composition_final:
      "\<forall>dg bs. controlled_ro_program composition_final_q
        (composition_final_stage A dg bs)"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program
              A prefix)
            s)"
  shows
    "query_future_prequery_count t \<le>
      query_future_prequery_count s +
        (sum_list (drop 1 trace_qs) +
         trace_final_q +
         degree_q +
         sum_list composition_qs +
         composition_final_q)"
proof -
  obtain fr trace_bs first_root where
    prefix_eq: "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
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
      "0 + ceil_log (to_nat dg + 1) \<le> length composition_qs"
      using assert_props composition_length by simp
    have trace_qs_empty: "trace_qs = []"
      using trace_length 0 by simp
    have count1:
      "query_future_prequery_count s1 \<le>
        query_future_prequery_count s + trace_final_q"
      by (rule controlled_ro_program_query_future_prequery_count_bound[
            OF trace_final[rule_format] trace_final_out])
    have count2:
      "query_future_prequery_count s2 = query_future_prequery_count s1"
      by (rule ro_record_staged_message_query_future_prequery_count_eq[
            OF trace_record_out])
    have count3:
      "query_future_prequery_count s3 = query_future_prequery_count s2"
      by (rule ro_staged_alpha_program_query_future_prequery_count_eq[
            OF alpha_out])
    have count4_step:
      "query_future_prequery_count s4 \<le>
        query_future_prequery_count s3 + degree_q"
      by (rule controlled_ro_program_query_future_prequery_count_bound[
            OF degree[rule_format] degree_out])
    have count4:
      "query_future_prequery_count s4 \<le>
        query_future_prequery_count s + (trace_final_q + degree_q)"
      by (rule nat_le_add_trans[OF count1])
        (use count2 count3 count4_step in simp)
    have count5:
      "query_future_prequery_count s5 = query_future_prequery_count s4"
      by (rule ro_record_staged_message_query_future_prequery_count_eq[
            OF degree_record_out])
    have composition_out':
      "Some ((composition_roots, composition_bs), s6) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])
            s5)"
      using composition_out assert_props by simp
    have count6_take:
      "query_future_prequery_count s6 \<le>
        query_future_prequery_count s5 +
          sum_list
            (take (ceil_log (to_nat dg + 1)) composition_qs)"
      using
        ro_staged_composition_fri_program_query_future_prequery_count_bound[
          OF composition_fri composition_bound composition_out']
      by simp
    have take_le:
      "sum_list (take (ceil_log (to_nat dg + 1)) composition_qs) \<le>
        sum_list composition_qs"
      by (rule sum_list_take_le)
    have count6_step:
      "query_future_prequery_count s6 \<le>
        query_future_prequery_count s5 + sum_list composition_qs"
      by (rule order_trans[OF count6_take])
        (rule add_left_mono[OF take_le])
    have count6:
      "query_future_prequery_count s6 \<le>
        query_future_prequery_count s +
          ((trace_final_q + degree_q) + sum_list composition_qs)"
      by (rule nat_le_add_trans[OF count4])
        (use count5 count6_step in simp)
    have count7_step:
      "query_future_prequery_count s7 \<le>
        query_future_prequery_count s6 + composition_final_q"
      by (rule controlled_ro_program_query_future_prequery_count_bound[
            OF composition_final[rule_format] composition_final_out])
    have count7:
      "query_future_prequery_count s7 \<le>
        query_future_prequery_count s +
          (((trace_final_q + degree_q) + sum_list composition_qs) +
            composition_final_q)"
      by (rule nat_le_add_trans[OF count6 count7_step])
    have count8:
      "query_future_prequery_count s8 = query_future_prequery_count s7"
      by (rule ro_record_staged_message_query_future_prequery_count_eq[
            OF composition_record_out])
    show ?thesis
      using count7 count8 t_eq
      unfolding trace_qs_empty
      by (simp add: add.assoc)
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
    have trace_bound: "1 + n \<le> length trace_qs"
      using trace_length Suc by simp
    have composition_bound:
      "0 + ceil_log (to_nat dg + 1) \<le> length composition_qs"
      using assert_props composition_length by simp
    have tail_length: "length (drop 1 trace_qs) = n"
      using trace_length Suc by simp
    have count1:
      "query_future_prequery_count s1 = query_future_prequery_count s"
      by (rule receive_trace_fri_challenge_query_future_prequery_count_eq[
            OF challenge_out])
    have count2_take:
      "query_future_prequery_count s2 \<le>
        query_future_prequery_count s1 +
          sum_list (take n (drop 1 trace_qs))"
      by (rule ro_staged_trace_fri_program_query_future_prequery_count_bound[
            OF trace_fri trace_bound trace_fri_out])
    have tail_take:
      "take n (drop 1 trace_qs) = drop 1 trace_qs"
      using tail_length by simp
    have count2:
      "query_future_prequery_count s2 \<le>
        query_future_prequery_count s + sum_list (drop 1 trace_qs)"
      using count1 count2_take unfolding tail_take by simp
    have count3_step:
      "query_future_prequery_count s3 \<le>
        query_future_prequery_count s2 + trace_final_q"
      by (rule controlled_ro_program_query_future_prequery_count_bound[
            OF trace_final[rule_format] trace_final_out])
    have count3:
      "query_future_prequery_count s3 \<le>
        query_future_prequery_count s +
          (sum_list (drop 1 trace_qs) + trace_final_q)"
      by (rule nat_le_add_trans[OF count2 count3_step])
    have count4:
      "query_future_prequery_count s4 = query_future_prequery_count s3"
      by (rule ro_record_staged_message_query_future_prequery_count_eq[
            OF trace_record_out])
    have count5:
      "query_future_prequery_count s5 = query_future_prequery_count s4"
      by (rule ro_staged_alpha_program_query_future_prequery_count_eq[
            OF alpha_out])
    have count6_step:
      "query_future_prequery_count s6 \<le>
        query_future_prequery_count s5 + degree_q"
      by (rule controlled_ro_program_query_future_prequery_count_bound[
            OF degree[rule_format] degree_out])
    have count6:
      "query_future_prequery_count s6 \<le>
        query_future_prequery_count s +
          ((sum_list (drop 1 trace_qs) + trace_final_q) + degree_q)"
      by (rule nat_le_add_trans[OF count3])
        (use count4 count5 count6_step in simp)
    have count7:
      "query_future_prequery_count s7 = query_future_prequery_count s6"
      by (rule ro_record_staged_message_query_future_prequery_count_eq[
            OF degree_record_out])
    have composition_out':
      "Some ((composition_roots, composition_bs), s8) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])
            s7)"
      using composition_out assert_props by simp
    have count8_take:
      "query_future_prequery_count s8 \<le>
        query_future_prequery_count s7 +
          sum_list
            (take (ceil_log (to_nat dg + 1)) composition_qs)"
      using
        ro_staged_composition_fri_program_query_future_prequery_count_bound[
          OF composition_fri composition_bound composition_out']
      by simp
    have take_le:
      "sum_list (take (ceil_log (to_nat dg + 1)) composition_qs) \<le>
        sum_list composition_qs"
      by (rule sum_list_take_le)
    have count8_step:
      "query_future_prequery_count s8 \<le>
        query_future_prequery_count s7 + sum_list composition_qs"
      by (rule order_trans[OF count8_take])
        (rule add_left_mono[OF take_le])
    have count8:
      "query_future_prequery_count s8 \<le>
        query_future_prequery_count s +
          (((sum_list (drop 1 trace_qs) + trace_final_q) + degree_q) +
            sum_list composition_qs)"
      by (rule nat_le_add_trans[OF count6])
        (use count7 count8_step in simp)
    have count9_step:
      "query_future_prequery_count s9 \<le>
        query_future_prequery_count s8 + composition_final_q"
      by (rule controlled_ro_program_query_future_prequery_count_bound[
            OF composition_final[rule_format] composition_final_out])
    have count9:
      "query_future_prequery_count s9 \<le>
        query_future_prequery_count s +
          ((((sum_list (drop 1 trace_qs) + trace_final_q) + degree_q) +
            sum_list composition_qs) + composition_final_q)"
      by (rule nat_le_add_trans[OF count8 count9_step])
    have count10:
      "query_future_prequery_count s10 = query_future_prequery_count s9"
      by (rule ro_record_staged_message_query_future_prequery_count_eq[
            OF composition_record_out])
    show ?thesis
      using count9 count10 t_eq
      by (simp add: add.assoc)
  qed
qed


definition staged_prequery_attacker_query_budget :: "staged_budgets \<Rightarrow> nat"
  where
    "staged_prequery_attacker_query_budget budgets =
      trace_root_budget budgets +
      sum_list (trace_fri_budgets budgets) +
      trace_final_budget budgets +
      degree_budget budgets +
      sum_list (composition_fri_budgets budgets) +
      composition_final_budget budgets"

lemma ro_checked_staged_first_root_query_head_program_query_future_count_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (result, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_first_root_query_head_program A) s)"
  shows
    "query_future_prequery_count t \<le>
      query_future_prequery_count s +
        staged_prequery_attacker_query_budget budgets"
proof -
  have lengths:
    "length (trace_fri_budgets budgets) = ceil_log clength \<and>
     length (composition_fri_budgets budgets) =
       ceil_log (maxDegree + 1) \<and>
     length (query_opening_budgets budgets) = rounds"
    using wf unfolding staged_budget_wellformed_def by blast
  have trace_length:
    "length (trace_fri_budgets budgets) = ceil_log clength"
    using lengths by blast
  have composition_length:
    "length (composition_fri_budgets budgets) =
      ceil_log (maxDegree + 1)"
    using lengths by blast
  have trace_root_controlled:
    "controlled_ro_program (trace_root_budget budgets)
      (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have trace_fri_controlled:
    "\<forall>j bs. j < length (trace_fri_budgets budgets) \<longrightarrow>
      controlled_ro_program (trace_fri_budgets budgets ! j)
        (trace_fri_root_stage A j bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have trace_fri_prefix_controlled:
    "\<forall>j < length (trace_fri_budgets budgets). \<forall>bs.
      controlled_ro_program (trace_fri_budgets budgets ! j)
        (trace_fri_root_stage A j bs)"
    using trace_fri_controlled by blast
  have trace_final_controlled:
    "\<forall>bs. controlled_ro_program (trace_final_budget budgets)
      (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have degree_controlled:
    "\<forall>as. controlled_ro_program (degree_budget budgets)
      (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_fri_controlled:
    "\<forall>dg j bs. j < length (composition_fri_budgets budgets) \<longrightarrow>
      controlled_ro_program (composition_fri_budgets budgets ! j)
        (composition_fri_root_stage A dg j bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_controlled:
    "\<forall>dg bs. controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
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
  have count1:
    "query_future_prequery_count s1 \<le>
      query_future_prequery_count s + trace_root_budget budgets +
        sum_list (take 1 (trace_fri_budgets budgets))"
    by (rule
        ro_staged_first_trace_fri_root_prefix_program_query_future_count_bound[
          OF trace_root_controlled trace_length trace_fri_prefix_controlled
            prefix_out])
  have count2:
    "query_future_prequery_count s2 \<le>
      query_future_prequery_count s1 +
        (sum_list (drop 1 (trace_fri_budgets budgets)) +
         trace_final_budget budgets +
         degree_budget budgets +
         sum_list (composition_fri_budgets budgets) +
         composition_final_budget budgets)"
    by (rule
        ro_checked_staged_after_first_trace_fri_root_prefix_program_query_future_count_bound[
          OF _ _ trace_fri_controlled trace_final_controlled
            degree_controlled composition_fri_controlled
            composition_final_controlled after_out])
      (use lengths in simp_all)
  have combined:
    "query_future_prequery_count s2 \<le>
      query_future_prequery_count s +
        ((trace_root_budget budgets +
          sum_list (take 1 (trace_fri_budgets budgets))) +
         (sum_list (drop 1 (trace_fri_budgets budgets)) +
          trace_final_budget budgets +
          degree_budget budgets +
          sum_list (composition_fri_budgets budgets) +
          composition_final_budget budgets))"
    using count1 count2 by linarith
  have trace_split:
    "sum_list (take 1 (trace_fri_budgets budgets)) +
      sum_list (drop 1 (trace_fri_budgets budgets)) =
      sum_list (trace_fri_budgets budgets)"
    by (metis append_take_drop_id sum_list_append)
  show ?thesis
    using combined t_eq trace_split
    unfolding staged_prequery_attacker_query_budget_def
    by (simp add: add.assoc add.commute)
qed

lemma staged_prequery_plus_opening_budget:
  "staged_prequery_attacker_query_budget budgets +
      sum_list (query_opening_budgets budgets) =
    staged_attacker_query_budget budgets"
  unfolding staged_prequery_attacker_query_budget_def
    staged_attacker_query_budget_def
  by simp

end

end
