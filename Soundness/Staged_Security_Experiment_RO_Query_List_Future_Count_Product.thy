theory Staged_Security_Experiment_RO_Query_List_Future_Count_Product
  imports Soundness_FRI_Query_Future_Count
begin

context soundness
begin

definition ro_query_witnesses_index_set_hit
  :: "nat set \<Rightarrow>
      (('f list \<times> 'f protocol_channel list \<times> 'f list list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "ro_query_witnesses_index_set_hit indices out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some ((raws, query_states, chunks), _) \<Rightarrow>
        length query_states = length raws \<and>
        length chunks = length raws \<and>
        set (map (\<lambda>raw. index (to_nat raw)) raws) \<subseteq> indices)"

lemma ro_query_witnesses_index_set_hit_None[simp]:
  "\<not> ro_query_witnesses_index_set_hit indices None"
  unfolding ro_query_witnesses_index_set_hit_def by simp

lemma ro_query_witnesses_index_set_hit_empty[simp]:
  "ro_query_witnesses_index_set_hit indices
    (Some (([], [], []), s))"
  unfolding ro_query_witnesses_index_set_hit_def by simp

lemma ro_query_witnesses_index_set_hit_head_raw:
  assumes hit:
    "ro_query_witnesses_index_set_hit indices
      (Some ((raw # raws, query_state # query_states,
        chunk # chunks), t))"
  shows "raw \<in> query_index_raw_preimage indices"
  using hit
  unfolding ro_query_witnesses_index_set_hit_def
    query_index_raw_preimage_def
  by simp

lemma ro_query_witnesses_index_set_hit_tail:
  assumes hit:
    "ro_query_witnesses_index_set_hit indices
      (Some ((raw # raws, query_state # query_states,
        chunk # chunks), t))"
  shows
    "ro_query_witnesses_index_set_hit indices
      (Some ((raws, query_states, chunks), t))"
  using hit
  unfolding ro_query_witnesses_index_set_hit_def
  by auto

lemma query_index_raw_preimage_envelope_probability_bound:
  assumes subset: "indices \<subseteq> query_sample_space"
  shows
    "nnreal (card (query_index_raw_preimage indices)) / nnreal size \<le>
      nnreal (query_raw_preimage_card_envelope (card indices)) /
        nnreal size"
proof -
  have card_le:
    "card (query_index_raw_preimage indices) \<le>
      query_raw_preimage_card_envelope (card indices)"
    by (rule card_query_index_raw_preimage_le_query_envelope[OF subset])
  show ?thesis
    by (rule nnreal_nat_divide_right_mono[OF card_le])
qed

lemma wp_receive_query_index_challenge_fresh_index_set_le:
  assumes fresh:
      "fmlookup (HashMap s)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
    and subset: "indices \<subseteq> query_sample_space"
  shows
    "wp_event receive_query_index_challenge
      (\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (raw, _) \<Rightarrow> raw \<in> query_index_raw_preimage indices)
      s \<le>
      nnreal (query_raw_preimage_card_envelope (card indices)) /
        nnreal size"
proof -
  have raw:
    "wp_event receive_query_index_challenge
      (\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (raw, _) \<Rightarrow> raw \<in> query_index_raw_preimage indices)
      s \<le>
      nnreal (card (query_index_raw_preimage indices)) / nnreal size"
    by (rule wp_receive_query_index_challenge_raw_set_le[OF fresh])
  show ?thesis
    by (rule order_trans[OF raw
          query_index_raw_preimage_envelope_probability_bound[OF subset]])
qed

lemma prob_power_nat_diff_antitone:
  fixes p :: prob
  assumes p_le: "p \<le> 1"
    and ab: "a \<le> b"
  shows "p ^ (n - a) \<le> p ^ (n - b)"
proof -
  have diff: "n - b \<le> n - a"
    using ab by simp
  show ?thesis
    by (rule power_decreasing[OF diff]) (simp_all add: p_le)
qed

lemma prob_mult_power_nat_diff_le:
  fixes p :: prob
  assumes p_le: "p \<le> 1"
  shows "p * p ^ (n - k) \<le> p ^ (Suc n - k)"
proof (cases "k \<le> n")
  case True
  have diff: "Suc n - k = Suc (n - k)"
    using True by simp
  show ?thesis
    unfolding diff power_Suc
    by (simp add: mult.commute)
next
  case False
  have n_le: "n \<le> k"
    using False by simp
  have sn_le: "Suc n \<le> k"
    using False by simp
  show ?thesis
    using p_le n_le sn_le by simp
qed


lemma wp_ro_checked_staged_query_program_after_raw_future_count_bound:
  fixes p :: prob
  assumes p_le: "p \<le> 1"
    and controlled:
      "controlled_ro_program q (query_opening_stage A i raw)"
    and tail_bound:
      "\<And>next_query_state.
        wp_event
          (ro_checked_staged_query_program_with_witnesses A trace_roots
            composition_roots next_query_state (Suc i) n)
          (ro_query_witnesses_index_set_hit indices)
          next_query_state \<le>
        p ^ (n - (query_future_prequery_count next_query_state + b))"
  shows
    "wp_event
      (do {
        chunk \<leftarrow> query_opening_stage A i raw;
        assert
          (verifier_query_round_chunk (index (to_nat raw)) trace_roots
            composition_roots chunk);
        ro_record_staged_messages chunk;
        next_query_state \<leftarrow> get;
        (raws, query_states, chunks) \<leftarrow>
          ro_checked_staged_query_program_with_witnesses A trace_roots
            composition_roots next_query_state (Suc i) n;
        return
          (raw # raws, query_state # query_states, chunk # chunks)
      })
      (ro_query_witnesses_index_set_hit indices) s \<le>
    p ^ (n - (query_future_prequery_count s + q + b))"
proof -
  let ?Q = "ro_query_witnesses_index_set_hit indices"
  let ?D = "p ^ (n - (query_future_prequery_count s + q + b))"
  show ?thesis
    unfolding Let_def
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?Q None"
      by simp
  next
    fix chunk s1
    assume chunk_support:
      "Some (chunk, s1) \<in>
        set_dist (execute (query_opening_stage A i raw) s)"
    have count_s1:
      "query_future_prequery_count s1 \<le>
        query_future_prequery_count s + q"
      by (rule controlled_ro_program_query_future_prequery_count_bound[
            OF controlled chunk_support])
    show
      "wp_event
        (assert
          (verifier_query_round_chunk (index (to_nat raw)) trace_roots
            composition_roots chunk) \<bind>
          (\<lambda>_. do {
            ro_record_staged_messages chunk;
            next_query_state \<leftarrow> get;
            (raws, query_states, chunks) \<leftarrow>
              ro_checked_staged_query_program_with_witnesses A trace_roots
                composition_roots next_query_state (Suc i) n;
            return
              (raw # raws, query_state # query_states, chunk # chunks)
          }))
        ?Q s1 \<le> ?D"
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?Q None"
        by simp
    next
      fix u s2
      assume assert_support:
        "Some (u, s2) \<in>
          set_dist
            (execute
              (assert
                (verifier_query_round_chunk (index (to_nat raw)) trace_roots
                  composition_roots chunk))
              s1)"
      have s2_eq: "s2 = s1"
        using assert_support
        unfolding assert_def
        by (auto simp: throw_no_outcome split: if_splits)
      show
        "wp_event
          (do {
            ro_record_staged_messages chunk;
            next_query_state \<leftarrow> get;
            (raws, query_states, chunks) \<leftarrow>
              ro_checked_staged_query_program_with_witnesses A trace_roots
                composition_roots next_query_state (Suc i) n;
            return
              (raw # raws, query_state # query_states, chunk # chunks)
          })
          ?Q s2 \<le> ?D"
        unfolding Let_def
      proof (rule wp_event_bind_bound_by_cont)
        show "\<not> ?Q None"
          by simp
      next
        fix v s3
        assume record_support:
          "Some (v, s3) \<in>
            set_dist (execute (ro_record_staged_messages chunk) s2)"
        have v_eq: "v = ()"
          by (cases v) simp
        have count_s3:
          "query_future_prequery_count s3 =
            query_future_prequery_count s2"
          by (rule
              ro_record_staged_messages_query_future_prequery_count_eq[
                OF record_support[unfolded v_eq]])
        show
          "wp_event
            (do {
              next_query_state \<leftarrow> get;
              (raws, query_states, chunks) \<leftarrow>
                ro_checked_staged_query_program_with_witnesses A trace_roots
                  composition_roots next_query_state (Suc i) n;
              return
                (raw # raws, query_state # query_states, chunk # chunks)
            })
            ?Q s3 \<le> ?D"
        proof (rule wp_event_bind_bound_by_cont)
          show "\<not> ?Q None"
            by simp
        next
          fix next_query_state s4
          assume get_support:
            "Some (next_query_state, s4) \<in> set_dist (execute get s3)"
          have next_eq: "next_query_state = s4"
            using get_support by simp
          have s4_eq: "s4 = s3"
            using get_support by simp
          have count_s4:
            "query_future_prequery_count s4 \<le>
              query_future_prequery_count s + q"
            using count_s1 count_s3
            unfolding s2_eq s4_eq
            by simp
          have exponent_arg:
            "query_future_prequery_count s4 + b \<le>
              query_future_prequery_count s + q + b"
            using count_s4 by simp
          have tail_le:
            "wp_event
              (ro_checked_staged_query_program_with_witnesses A trace_roots
                composition_roots next_query_state (Suc i) n)
              (ro_query_witnesses_index_set_hit indices) s4 \<le> ?D"
          proof -
            have ih:
              "wp_event
                (ro_checked_staged_query_program_with_witnesses A trace_roots
                  composition_roots s4 (Suc i) n)
                (ro_query_witnesses_index_set_hit indices) s4 \<le>
              p ^ (n - (query_future_prequery_count s4 + b))"
              by (rule tail_bound[of s4])
            have power_le:
              "p ^ (n - (query_future_prequery_count s4 + b)) \<le> ?D"
              unfolding Let_def
              by (rule prob_power_nat_diff_antitone[
                    OF p_le exponent_arg])
            show ?thesis
              unfolding next_eq
              by (rule order_trans[OF ih power_le])
          qed
          show
            "wp_event
              (ro_checked_staged_query_program_with_witnesses A trace_roots
                  composition_roots next_query_state (Suc i) n \<bind>
                (\<lambda>(raws, query_states, chunks).
                  return
                    (raw # raws, query_state # query_states,
                      chunk # chunks)))
              ?Q s4 \<le> ?D"
          proof (rule wp_event_bind_bound_by_head_event[
                where P = "ro_query_witnesses_index_set_hit indices"])
            show
              "wp_event
                (ro_checked_staged_query_program_with_witnesses A trace_roots
                  composition_roots next_query_state (Suc i) n)
                (ro_query_witnesses_index_set_hit indices) s4 \<le> ?D"
              by (rule tail_le)
          next
            show
              "?Q None \<Longrightarrow>
                ro_query_witnesses_index_set_hit indices None"
              by simp
          next
            fix result t out
            assume tail_support:
                "Some (result, t) \<in>
                  set_dist
                    (execute
                      (ro_checked_staged_query_program_with_witnesses A
                        trace_roots composition_roots next_query_state
                        (Suc i) n)
                      s4)"
              and return_support:
                "out \<in>
                  set_dist
                    (execute
                      ((\<lambda>(raws, query_states, chunks).
                          return
                            (raw # raws, query_state # query_states,
                              chunk # chunks))
                        result)
                      t)"
              and hit: "?Q out"
            obtain raws query_states chunks where result_eq:
              "result = (raws, query_states, chunks)"
              by (cases result) auto
            obtain hit_result hit_state where out_some:
              "out = Some (hit_result, hit_state)"
              using hit by (cases out) auto
            have return_support':
              "Some (hit_result, hit_state) \<in>
                set_dist
                  (execute
                    (return
                      (raw # raws, query_state # query_states,
                        chunk # chunks))
                    t)"
              using return_support out_some unfolding result_eq by simp
            have out_eq:
              "out =
                Some
                  ((raw # raws, query_state # query_states,
                    chunk # chunks), t)"
              using out_some return_support' by simp
            have
              "ro_query_witnesses_index_set_hit indices
                (Some ((raws, query_states, chunks), t))"
              by (rule ro_query_witnesses_index_set_hit_tail)
                (use hit out_eq in simp)
            then show
              "ro_query_witnesses_index_set_hit indices
                (Some (result, t))"
              unfolding result_eq .
          qed
        qed
      qed
    qed
  qed
qed


lemma wp_ro_checked_staged_query_program_after_raw_not_in_zero:
  assumes raw_not: "raw \<notin> query_index_raw_preimage indices"
  shows
    "wp_event
      (do {
        chunk \<leftarrow> query_opening_stage A i raw;
        assert
          (verifier_query_round_chunk (index (to_nat raw)) trace_roots
            composition_roots chunk);
        ro_record_staged_messages chunk;
        next_query_state \<leftarrow> get;
        (raws, query_states, chunks) \<leftarrow>
          ro_checked_staged_query_program_with_witnesses A trace_roots
            composition_roots next_query_state (Suc i) n;
        return
          (raw # raws, query_state # query_states, chunk # chunks)
      })
      (ro_query_witnesses_index_set_hit indices) s = 0"
proof (rule ccontr)
  let ?Q = "ro_query_witnesses_index_set_hit indices"
  assume nonzero:
    "wp_event
      (do {
        chunk \<leftarrow> query_opening_stage A i raw;
        assert
          (verifier_query_round_chunk (index (to_nat raw)) trace_roots
            composition_roots chunk);
        ro_record_staged_messages chunk;
        next_query_state \<leftarrow> get;
        (raws, query_states, chunks) \<leftarrow>
          ro_checked_staged_query_program_with_witnesses A trace_roots
            composition_roots next_query_state (Suc i) n;
        return
          (raw # raws, query_state # query_states, chunk # chunks)
      })
      ?Q s \<noteq> 0"
  from wp_event_nonzero_imp_exists_support[OF nonzero]
  obtain out where out_support:
      "out \<in>
        set_dist
          (execute
            (do {
              chunk \<leftarrow> query_opening_stage A i raw;
              assert
                (verifier_query_round_chunk (index (to_nat raw)) trace_roots
                  composition_roots chunk);
              ro_record_staged_messages chunk;
              next_query_state \<leftarrow> get;
              (raws, query_states, chunks) \<leftarrow>
                ro_checked_staged_query_program_with_witnesses A trace_roots
                  composition_roots next_query_state (Suc i) n;
              return
                (raw # raws, query_state # query_states, chunk # chunks)
            })
            s)"
    and hit: "?Q out"
    by blast
  obtain hit_result hit_state where out_some:
    "out = Some (hit_result, hit_state)"
    using hit by (cases out) auto
  obtain chunk result t where return_support:
    "Some (hit_result, hit_state) \<in>
      set_dist
        (execute
          ((\<lambda>(raws, query_states, chunks).
              return
                (raw # raws, query_state # query_states, chunk # chunks))
            result)
          t)"
    using out_support unfolding out_some
    by (auto elim!: set_dist_bindE split: prod.splits)
  obtain raws query_states chunks where result_eq:
    "result = (raws, query_states, chunks)"
    by (cases result) auto
  have out_eq:
    "out =
      Some ((raw # raws, query_state # query_states, chunk # chunks), t)"
    using out_some return_support unfolding result_eq by simp
  have "raw \<in> query_index_raw_preimage indices"
    by (rule ro_query_witnesses_index_set_hit_head_raw)
      (use hit out_eq in simp)
  then show False
    using raw_not by blast
qed


lemma wp_ro_checked_staged_query_program_index_set_future_count_bound:
  assumes len_qs: "length qs = n"
    and controlled:
      "\<forall>j < n. \<forall>raw.
        controlled_ro_program (qs ! j)
          (query_opening_stage A (i + j) raw)"
    and subset: "indices \<subseteq> query_sample_space"
  shows
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots s i n)
      (ro_query_witnesses_index_set_hit indices) s \<le>
    (nnreal (query_raw_preimage_card_envelope (card indices)) /
      nnreal size) ^
      (n - (query_future_prequery_count s + sum_list qs))"
  using len_qs controlled subset
proof (induction n arbitrary: i s qs)
  case 0
  then have qs_eq: "qs = []"
    by simp
  show ?case
    unfolding qs_eq
      ro_checked_staged_query_program_with_witnesses.simps
      ro_query_witnesses_index_set_hit_def
    by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  obtain q qs_tail where qs_eq: "qs = q # qs_tail"
    using Suc.prems(1) by (cases qs) auto
  have len_tail: "length qs_tail = n"
    using Suc.prems(1) unfolding qs_eq by simp
  let ?p =
    "nnreal (query_raw_preimage_card_envelope (card indices)) /
      nnreal size"
  let ?b = "sum_list qs_tail"
  have p_le: "?p \<le> 1"
    by (rule query_sample_space_envelope_fraction_le_one[
          OF Suc.prems(3)])
  have head_control:
    "\<And>raw. controlled_ro_program q (query_opening_stage A i raw)"
  proof -
    fix raw
    show
      "controlled_ro_program q (query_opening_stage A i raw)"
      using Suc.prems(2)[rule_format, of 0 raw]
      unfolding qs_eq
      by simp
  qed
  have tail_control:
    "\<forall>j < n. \<forall>raw.
      controlled_ro_program (qs_tail ! j)
        (query_opening_stage A (Suc i + j) raw)"
  proof (intro allI impI)
    fix j raw
    assume j_lt: "j < n"
    have sj_lt: "Suc j < Suc n"
      using j_lt by simp
    show
      "controlled_ro_program (qs_tail ! j)
        (query_opening_stage A (Suc i + j) raw)"
      using Suc.prems(2)[rule_format, of "Suc j" raw] sj_lt
      unfolding qs_eq
      by simp
  qed
  have tail_bound:
    "\<And>next_query_state.
      wp_event
        (ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots next_query_state (Suc i) n)
        (ro_query_witnesses_index_set_hit indices)
        next_query_state \<le>
      ?p ^
        (n -
          (query_future_prequery_count next_query_state +
            sum_list qs_tail))"
  proof -
    fix next_query_state
    show
      "wp_event
        (ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots next_query_state (Suc i) n)
        (ro_query_witnesses_index_set_hit indices)
        next_query_state \<le>
      ?p ^
        (n -
          (query_future_prequery_count next_query_state +
            sum_list qs_tail))"
      by (rule Suc.IH[OF len_tail tail_control Suc.prems(3)])
  qed
  show ?case
  proof (cases
      "fmlookup (HashMap s)
        (QueryIndexChallenge (PQueryCounter s) (PState s))")
    case None
    let ?Head =
      "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (raw, _) \<Rightarrow> raw \<in> query_index_raw_preimage indices"
    let ?D =
      "?p ^ (n - (query_future_prequery_count s + q + ?b))"
    have head_bound:
      "wp_event receive_query_index_challenge ?Head s \<le> ?p"
      by (rule
          wp_receive_query_index_challenge_fresh_index_set_le[
            OF None Suc.prems(3)])
    have bind_bound:
      "wp_event
        (ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots s i (Suc n))
        (ro_query_witnesses_index_set_hit indices) s \<le>
      wp_event receive_query_index_challenge ?Head s * ?D"
      unfolding ro_checked_staged_query_program_with_witnesses.simps
        Let_def
    proof (rule wp_event_bind_bound_by_head_and_cont)
      show
        "\<not> ro_query_witnesses_index_set_hit indices None"
        by simp
    next
      fix raw query_state
      assume raw_support:
          "Some (raw, query_state) \<in>
            set_dist (execute receive_query_index_challenge s)"
        and not_head:
          "\<not> ?Head (Some (raw, query_state))"
      have raw_not:
        "raw \<notin> query_index_raw_preimage indices"
        using not_head by simp
      show
        "wp_event
          (do {
            chunk \<leftarrow> query_opening_stage A i raw;
            assert
              (verifier_query_round_chunk (index (to_nat raw)) trace_roots
                composition_roots chunk);
            ro_record_staged_messages chunk;
            next_query_state \<leftarrow> get;
            (raws, query_states, chunks) \<leftarrow>
              ro_checked_staged_query_program_with_witnesses A trace_roots
                composition_roots next_query_state (Suc i) n;
            return
              (raw # raws, s # query_states, chunk # chunks)
          })
          (ro_query_witnesses_index_set_hit indices) query_state = 0"
        by (rule
            wp_ro_checked_staged_query_program_after_raw_not_in_zero[
              OF raw_not])
    next
      fix raw query_state
      assume raw_support:
          "Some (raw, query_state) \<in>
            set_dist (execute receive_query_index_challenge s)"
        and head_hit:
          "?Head (Some (raw, query_state))"
      have count_query_state:
        "query_future_prequery_count query_state \<le>
          query_future_prequery_count s"
        by (rule receive_query_index_challenge_future_count_le[
              OF raw_support])
      have after:
        "wp_event
          (do {
            chunk \<leftarrow> query_opening_stage A i raw;
            assert
              (verifier_query_round_chunk (index (to_nat raw)) trace_roots
                composition_roots chunk);
            ro_record_staged_messages chunk;
            next_query_state \<leftarrow> get;
            (raws, query_states, chunks) \<leftarrow>
              ro_checked_staged_query_program_with_witnesses A trace_roots
                composition_roots next_query_state (Suc i) n;
            return
              (raw # raws, s # query_states, chunk # chunks)
          })
          (ro_query_witnesses_index_set_hit indices) query_state \<le>
        ?p ^
          (n -
            (query_future_prequery_count query_state + q + ?b))"
        by (rule
            wp_ro_checked_staged_query_program_after_raw_future_count_bound[
              OF p_le head_control tail_bound])
      have exponent_arg:
        "query_future_prequery_count query_state + q + ?b \<le>
          query_future_prequery_count s + q + ?b"
        using count_query_state by simp
      have power_le:
        "?p ^
            (n -
              (query_future_prequery_count query_state + q + ?b)) \<le>
          ?D"
        unfolding Let_def
        by (rule prob_power_nat_diff_antitone[
              OF p_le exponent_arg])
      show
        "wp_event
          (do {
            chunk \<leftarrow> query_opening_stage A i raw;
            assert
              (verifier_query_round_chunk (index (to_nat raw)) trace_roots
                composition_roots chunk);
            ro_record_staged_messages chunk;
            next_query_state \<leftarrow> get;
            (raws, query_states, chunks) \<leftarrow>
              ro_checked_staged_query_program_with_witnesses A trace_roots
                composition_roots next_query_state (Suc i) n;
            return
              (raw # raws, s # query_states, chunk # chunks)
          })
          (ro_query_witnesses_index_set_hit indices) query_state \<le> ?D"
        by (rule order_trans[OF after power_le])
    qed
    have product_head:
      "wp_event receive_query_index_challenge ?Head s * ?D \<le>
        ?p * ?D"
      by (rule mult_right_mono[OF head_bound]) simp
    have product_round:
      "?p * ?D \<le>
        ?p ^
          (Suc n -
            (query_future_prequery_count s + q + ?b))"
      unfolding Let_def
      by (rule prob_mult_power_nat_diff_le[OF p_le])
    have final_bound:
      "wp_event
        (ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots s i (Suc n))
        (ro_query_witnesses_index_set_hit indices) s \<le>
      ?p ^
        (Suc n -
          (query_future_prequery_count s + q + ?b))"
      by (rule order_trans[OF bind_bound
            order_trans[OF product_head product_round]])
    show ?thesis
      using final_bound
      unfolding qs_eq
      by (simp add: add.assoc)
next
    case (Some old_raw)
    have current_dom:
      "QueryIndexChallenge (PQueryCounter s) (PState s) \<in>
        fmdom' (HashMap s)"
      by (rule fmdom'I[OF Some])
    have current_in:
      "QueryIndexChallenge (PQueryCounter s) (PState s) \<in>
        query_future_keys s"
      unfolding query_future_keys_def
      using current_dom by simp
    have nonempty: "query_future_keys s \<noteq> {}"
      using current_in by blast
    have count_pos:
      "0 < query_future_prequery_count s"
      unfolding query_future_prequery_count_def
      using finite_query_future_keys[of s] nonempty
      by (simp add: card_gt_0_iff)
    obtain c where count_eq:
      "query_future_prequery_count s = Suc c"
      using count_pos by (cases "query_future_prequery_count s") auto
    have bind_bound:
      "wp_event
        (ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots s i (Suc n))
        (ro_query_witnesses_index_set_hit indices) s \<le>
      ?p ^ (n - (c + q + ?b))"
      unfolding ro_checked_staged_query_program_with_witnesses.simps
        Let_def
    proof (rule wp_event_bind_bound_by_cont)
      show
        "\<not> ro_query_witnesses_index_set_hit indices None"
        by simp
    next
      fix raw query_state
      assume raw_support:
        "Some (raw, query_state) \<in>
          set_dist (execute receive_query_index_challenge s)"
      have decrease:
        "Suc (query_future_prequery_count query_state) \<le>
          query_future_prequery_count s"
        by (rule
            receive_query_index_challenge_known_future_count_Suc_le[
              OF Some raw_support])
      have count_query_state:
        "query_future_prequery_count query_state \<le> c"
        using decrease count_eq by simp
      have after:
        "wp_event
          (do {
            chunk \<leftarrow> query_opening_stage A i raw;
            assert
              (verifier_query_round_chunk (index (to_nat raw)) trace_roots
                composition_roots chunk);
            ro_record_staged_messages chunk;
            next_query_state \<leftarrow> get;
            (raws, query_states, chunks) \<leftarrow>
              ro_checked_staged_query_program_with_witnesses A trace_roots
                composition_roots next_query_state (Suc i) n;
            return
              (raw # raws, s # query_states, chunk # chunks)
          })
          (ro_query_witnesses_index_set_hit indices) query_state \<le>
        ?p ^
          (n -
            (query_future_prequery_count query_state + q + ?b))"
        by (rule
            wp_ro_checked_staged_query_program_after_raw_future_count_bound[
              OF p_le head_control tail_bound])
      have exponent_arg:
        "query_future_prequery_count query_state + q + ?b \<le>
          c + q + ?b"
        using count_query_state by simp
      have power_le:
        "?p ^
            (n -
              (query_future_prequery_count query_state + q + ?b)) \<le>
          ?p ^ (n - (c + q + ?b))"
        by (rule prob_power_nat_diff_antitone[
              OF p_le exponent_arg])
      show
        "wp_event
          (do {
            chunk \<leftarrow> query_opening_stage A i raw;
            assert
              (verifier_query_round_chunk (index (to_nat raw)) trace_roots
                composition_roots chunk);
            ro_record_staged_messages chunk;
            next_query_state \<leftarrow> get;
            (raws, query_states, chunks) \<leftarrow>
              ro_checked_staged_query_program_with_witnesses A trace_roots
                composition_roots next_query_state (Suc i) n;
            return
              (raw # raws, s # query_states, chunk # chunks)
          })
          (ro_query_witnesses_index_set_hit indices) query_state \<le>
        ?p ^ (n - (c + q + ?b))"
        by (rule order_trans[OF after power_le])
    qed
    have target_eq:
      "?p ^ (n - (c + q + ?b)) =
        ?p ^
          (Suc n -
            (query_future_prequery_count s + q + ?b))"
      unfolding count_eq by simp
    have final_bound:
      "wp_event
        (ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots s i (Suc n))
        (ro_query_witnesses_index_set_hit indices) s \<le>
      ?p ^
        (Suc n -
          (query_future_prequery_count s + q + ?b))"
      using bind_bound target_eq by simp
    show ?thesis
      using final_bound
      unfolding qs_eq
      by (simp add: add.assoc)
  qed
qed

end

end
