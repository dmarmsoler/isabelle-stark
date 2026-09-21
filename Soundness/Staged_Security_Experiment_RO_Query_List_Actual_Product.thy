(*  Title:      Stark/Staged_Security_Experiment_RO_Query_List_Actual_Product.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_RO_Query_List_Actual_Product
  imports
    Staged_Security_Experiment_RO_Query_List_Prequery
    Soundness_FRI_Query_List_Exact_Product
begin

text \<open>
  Proof-only actual-path query-list accounting for the RO checked query
  program.  The augmented program below returns the raw query-index samples and
  the pre-query states as ghost data, so product bounds can be tied to the
  sampled path instead of to an existential final-state witness.
\<close>

context soundness
begin

primrec ro_checked_staged_query_program_with_witnesses
  :: "'f staged_adversary \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f protocol_channel \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow>
      ('f list \<times> 'f protocol_channel list \<times> 'f list list,
       'f protocol_channel) state_monad"
where
  "ro_checked_staged_query_program_with_witnesses A trace_roots
      composition_roots query_state i 0 = return ([], [], [])"
| "ro_checked_staged_query_program_with_witnesses A trace_roots
      composition_roots query_state i (Suc n) =
    do {
      raw \<leftarrow> receive_query_index_challenge;
      let idx = index (to_nat raw);
      chunk \<leftarrow> query_opening_stage A i raw;
      assert
        (verifier_query_round_chunk idx trace_roots composition_roots chunk);
      ro_record_staged_messages chunk;
      next_query_state \<leftarrow> get;
      (raws, query_states, chunks) \<leftarrow>
        ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots next_query_state (Suc i) n;
      return (raw # raws, query_state # query_states, chunk # chunks)
    }"

definition ro_query_witnesses_raws_fresh_hit
  :: "'f list \<Rightarrow>
      (('f list \<times> 'f protocol_channel list \<times> 'f list list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "ro_query_witnesses_raws_fresh_hit raws out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some ((raws', query_states, chunks), _) \<Rightarrow>
        raws' = raws \<and>
        length query_states = length raws \<and>
        length chunks = length raws \<and>
        (\<forall>j < length raws.
          fmlookup (HashMap (query_states ! j))
            (QueryIndexChallenge
              (PQueryCounter (query_states ! j))
              (PState (query_states ! j))) = None))"

definition ro_query_witnesses_query_index_list_fresh_hit
  :: "nat list set \<Rightarrow>
      (('f list \<times> 'f protocol_channel list \<times> 'f list list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "ro_query_witnesses_query_index_list_fresh_hit Q out \<longleftrightarrow>
    (\<exists>raws \<in> query_index_raw_list_preimage Q.
      ro_query_witnesses_raws_fresh_hit raws out)"

lemma ro_query_witnesses_raws_fresh_hit_None[simp]:
  "\<not> ro_query_witnesses_raws_fresh_hit raws None"
  unfolding ro_query_witnesses_raws_fresh_hit_def by simp

lemma ro_query_witnesses_query_index_list_fresh_hit_None[simp]:
  "\<not> ro_query_witnesses_query_index_list_fresh_hit Q None"
  unfolding ro_query_witnesses_query_index_list_fresh_hit_def by simp

lemma ro_query_witnesses_query_index_list_fresh_hitI:
  assumes raw_in: "raws \<in> query_index_raw_list_preimage Q"
    and hit: "ro_query_witnesses_raws_fresh_hit raws out"
  shows "ro_query_witnesses_query_index_list_fresh_hit Q out"
  using raw_in hit
  unfolding ro_query_witnesses_query_index_list_fresh_hit_def by blast

lemma ro_query_witnesses_raws_fresh_hit_head_raw:
  assumes hit:
    "ro_query_witnesses_raws_fresh_hit (raw # raws)
      (Some ((raw' # raws', query_state # query_states,
        chunk # chunks), t))"
  shows "raw' = raw"
  using hit unfolding ro_query_witnesses_raws_fresh_hit_def by simp

lemma ro_query_witnesses_raws_fresh_hit_head_fresh:
  assumes hit:
    "ro_query_witnesses_raws_fresh_hit (raw # raws)
      (Some ((raw' # raws', query_state # query_states,
        chunk # chunks), t))"
  shows
    "fmlookup (HashMap query_state)
      (QueryIndexChallenge (PQueryCounter query_state)
        (PState query_state)) = None"
proof -
  have all_fresh:
    "\<forall>j < Suc (length raws).
      fmlookup (HashMap ((query_state # query_states) ! j))
        (QueryIndexChallenge
          (PQueryCounter ((query_state # query_states) ! j))
          (PState ((query_state # query_states) ! j))) = None"
    using hit unfolding ro_query_witnesses_raws_fresh_hit_def by simp
  show ?thesis
    using all_fresh[rule_format, of 0] by simp
qed

lemma ro_query_witnesses_raws_fresh_hit_tail:
  assumes hit:
    "ro_query_witnesses_raws_fresh_hit (raw # raws)
      (Some ((raw' # raws', query_state # query_states,
        chunk # chunks), t))"
  shows
    "ro_query_witnesses_raws_fresh_hit raws
      (Some ((raws', query_states, chunks), t))"
  using hit unfolding ro_query_witnesses_raws_fresh_hit_def
  by auto

lemma wp_receive_query_index_challenge_fresh_singleton_raw_bound:
  "wp_event receive_query_index_challenge
    (\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (raw', _) \<Rightarrow>
        fmlookup (HashMap s)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = None \<and>
        raw' = raw)
    s \<le> 1 / nnreal size"
proof (cases
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = None")
  case True
  have event_eq:
    "(\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (raw', _) \<Rightarrow>
        fmlookup (HashMap s)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = None \<and>
        raw' = raw) =
     (\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (raw', _) \<Rightarrow> raw' \<in> {raw})"
  proof (rule ext)
    fix out
    show "(case out of
        None \<Rightarrow> False
      | Some (raw', _) \<Rightarrow>
          fmlookup (HashMap s)
            (QueryIndexChallenge (PQueryCounter s) (PState s)) = None \<and>
          raw' = raw) =
      (case out of None \<Rightarrow> False | Some (raw', _) \<Rightarrow> raw' \<in> {raw})"
      using True by (cases out) auto
  qed
  have "wp_event receive_query_index_challenge
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (raw', _) \<Rightarrow> raw' \<in> {raw}) s \<le>
      nnreal (card {raw}) / nnreal size"
    by (rule wp_receive_query_index_challenge_raw_set_le[OF True])
  then show ?thesis
    unfolding event_eq by simp
next
  case False
  have event_false:
    "(\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (raw', _) \<Rightarrow>
        fmlookup (HashMap s)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = None \<and>
        raw' = raw) = (\<lambda>_. False)"
  proof (rule ext)
    fix out
    show "(case out of
        None \<Rightarrow> False
      | Some (raw', _) \<Rightarrow>
          fmlookup (HashMap s)
            (QueryIndexChallenge (PQueryCounter s) (PState s)) = None \<and>
          raw' = raw) = False"
      using False by (cases out) auto
  qed
  show ?thesis
    unfolding event_false by simp
qed

lemma wp_ro_checked_staged_query_program_with_witnesses_after_raw_bound:
  assumes tail_bound:
    "\<And>next_query_state.
      wp_event
        (ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots next_query_state (Suc i) n)
        (ro_query_witnesses_raws_fresh_hit raws) next_query_state \<le> D"
  shows
    "wp_event
      (do {
        chunk \<leftarrow> query_opening_stage A i raw;
        assert
          (verifier_query_round_chunk (index (to_nat raw)) trace_roots
            composition_roots chunk);
        ro_record_staged_messages chunk;
        next_query_state \<leftarrow> get;
        (raws', query_states, chunks) \<leftarrow>
          ro_checked_staged_query_program_with_witnesses A trace_roots
            composition_roots next_query_state (Suc i) n;
        return
          (raw # raws', query_state # query_states, chunk # chunks)
      })
      (ro_query_witnesses_raws_fresh_hit (raw # raws)) s \<le> D"
proof -
  let ?Q = "ro_query_witnesses_raws_fresh_hit (raw # raws)"
  show ?thesis
    unfolding Let_def
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?Q None"
      by simp
  next
    fix chunk s1
    assume chunk_support:
      "Some (chunk, s1) \<in> set_dist (execute (query_opening_stage A i raw) s)"
    show
      "wp_event
        (assert
          (verifier_query_round_chunk (index (to_nat raw)) trace_roots
            composition_roots chunk) \<bind>
          (\<lambda>_. do {
            ro_record_staged_messages chunk;
            next_query_state \<leftarrow> get;
            (raws', query_states, chunks) \<leftarrow>
              ro_checked_staged_query_program_with_witnesses A trace_roots
                composition_roots next_query_state (Suc i) n;
            return
              (raw # raws', query_state # query_states, chunk # chunks)
          }))
        ?Q s1 \<le> D"
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
      show
        "wp_event
          (do {
            ro_record_staged_messages chunk;
            next_query_state \<leftarrow> get;
            (raws', query_states, chunks) \<leftarrow>
              ro_checked_staged_query_program_with_witnesses A trace_roots
                composition_roots next_query_state (Suc i) n;
            return
              (raw # raws', query_state # query_states, chunk # chunks)
          })
          ?Q s2 \<le> D"
        unfolding Let_def
      proof (rule wp_event_bind_bound_by_cont)
        show "\<not> ?Q None"
          by simp
      next
        fix v s3
        assume record_support:
          "Some (v, s3) \<in>
            set_dist (execute (ro_record_staged_messages chunk) s2)"
        show
          "wp_event
            (do {
              next_query_state \<leftarrow> get;
              (raws', query_states, chunks) \<leftarrow>
                ro_checked_staged_query_program_with_witnesses A trace_roots
                  composition_roots next_query_state (Suc i) n;
              return
                (raw # raws', query_state # query_states, chunk # chunks)
            })
            ?Q s3 \<le> D"
        proof (rule wp_event_bind_bound_by_cont)
          show "\<not> ?Q None"
            by simp
        next
          fix next_query_state s4
          assume get_support:
            "Some (next_query_state, s4) \<in> set_dist (execute get s3)"
          have next_eq: "next_query_state = s4"
            using get_support by simp
          show
            "wp_event
              (ro_checked_staged_query_program_with_witnesses A trace_roots
                  composition_roots next_query_state (Suc i) n \<bind>
                (\<lambda>(raws', query_states, chunks).
                  return
                    (raw # raws', query_state # query_states,
                      chunk # chunks)))
              ?Q s4 \<le> D"
          proof (rule wp_event_bind_bound_by_head_event
              [where P = "ro_query_witnesses_raws_fresh_hit raws"])
            show
              "wp_event
                (ro_checked_staged_query_program_with_witnesses A trace_roots
                  composition_roots next_query_state (Suc i) n)
                (ro_query_witnesses_raws_fresh_hit raws) s4 \<le> D"
              using tail_bound[of s4] unfolding next_eq .
          next
            show
              "?Q None \<Longrightarrow>
                ro_query_witnesses_raws_fresh_hit raws None"
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
                      ((\<lambda>(raws', query_states, chunks).
                          return
                            (raw # raws', query_state # query_states,
                              chunk # chunks))
                        result)
                      t)"
              and hit: "?Q out"
            obtain raws' query_states chunks where result_eq:
              "result = (raws', query_states, chunks)"
              by (cases result) auto
            obtain hit_result hit_state where out_some:
              "out = Some (hit_result, hit_state)"
              using hit by (cases out) auto
            have return_support':
              "Some (hit_result, hit_state) \<in>
                set_dist
                  (execute
                    (return
                      (raw # raws', query_state # query_states,
                        chunk # chunks))
                    t)"
              using return_support out_some unfolding result_eq by simp
            have out_eq:
              "out =
                Some
                  ((raw # raws', query_state # query_states, chunk # chunks), t)"
              using out_some return_support' by simp
            have
              "ro_query_witnesses_raws_fresh_hit raws
                (Some ((raws', query_states, chunks), t))"
              by (rule ro_query_witnesses_raws_fresh_hit_tail)
                (use hit out_eq in simp)
            then show
              "ro_query_witnesses_raws_fresh_hit raws
                (Some (result, t))"
              unfolding result_eq .
          qed
        qed
      qed
    qed
  qed
qed

lemma wp_ro_checked_staged_query_program_with_witnesses_raws_fresh_bound:
  assumes len_raws: "length raws = n"
  shows
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots s i n)
      (ro_query_witnesses_raws_fresh_hit raws) s \<le>
      (1 / nnreal size) ^ n"
  using len_raws
proof (induction n arbitrary: i s raws)
  case 0
  then show ?case
    unfolding ro_query_witnesses_raws_fresh_hit_def
    by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  obtain raw raws_tail where raws_eq: "raws = raw # raws_tail"
    by (rule list_length_SucE[OF Suc.prems])
  have len_tail: "length raws_tail = n"
    using Suc.prems unfolding raws_eq by simp
  let ?Head =
    "\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (raw', _) \<Rightarrow>
        fmlookup (HashMap s)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = None \<and>
        raw' = raw"
  let ?Q = "ro_query_witnesses_raws_fresh_hit (raw # raws_tail)"
  let ?D = "(1 / nnreal size) ^ n"
  have head_bound:
    "wp_event receive_query_index_challenge ?Head s \<le> 1 / nnreal size"
    by (rule wp_receive_query_index_challenge_fresh_singleton_raw_bound)
  have bind_bound:
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots s i (Suc n))
      ?Q s \<le>
      wp_event receive_query_index_challenge ?Head s * ?D"
    unfolding ro_checked_staged_query_program_with_witnesses.simps Let_def
  proof (rule wp_event_bind_bound_by_head_and_cont)
    show "\<not> ?Q None"
      by simp
  next
    fix raw' query_state
    assume raw_support:
        "Some (raw', query_state) \<in>
          set_dist (execute receive_query_index_challenge s)"
      and not_head: "\<not> ?Head (Some (raw', query_state))"
    show
      "wp_event
        (do {
          chunk \<leftarrow> query_opening_stage A i raw';
          assert
            (verifier_query_round_chunk (index (to_nat raw')) trace_roots
              composition_roots chunk);
          ro_record_staged_messages chunk;
          next_query_state \<leftarrow> get;
          (raws', query_states, chunks) \<leftarrow>
            ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots next_query_state (Suc i) n;
          return
            (raw' # raws', s # query_states, chunk # chunks)
        })
        ?Q query_state = 0"
    proof (rule ccontr)
      assume nonzero:
        "wp_event
          (do {
            chunk \<leftarrow> query_opening_stage A i raw';
            assert
              (verifier_query_round_chunk (index (to_nat raw')) trace_roots
                composition_roots chunk);
            ro_record_staged_messages chunk;
            next_query_state \<leftarrow> get;
            (raws', query_states, chunks) \<leftarrow>
              ro_checked_staged_query_program_with_witnesses A trace_roots
                composition_roots next_query_state (Suc i) n;
            return
              (raw' # raws', s # query_states, chunk # chunks)
          })
          ?Q query_state \<noteq> 0"
      from wp_event_nonzero_imp_exists_support[OF nonzero]
      obtain out where out_support:
          "out \<in>
            set_dist
              (execute
                (do {
                  chunk \<leftarrow> query_opening_stage A i raw';
                  assert
                    (verifier_query_round_chunk (index (to_nat raw'))
                      trace_roots composition_roots chunk);
                  ro_record_staged_messages chunk;
                  next_query_state \<leftarrow> get;
                  (raws', query_states, chunks) \<leftarrow>
                    ro_checked_staged_query_program_with_witnesses A trace_roots
                      composition_roots next_query_state (Suc i) n;
                  return
                    (raw' # raws', s # query_states, chunk # chunks)
                })
                query_state)"
        and hit: "?Q out"
        by blast
      obtain hit_result hit_state where out_some:
        "out = Some (hit_result, hit_state)"
        using hit by (cases out) auto
      obtain chunk result t where return_support:
        "Some (hit_result, hit_state) \<in>
          set_dist
            (execute
              ((\<lambda>(raws', query_states, chunks).
                  return (raw' # raws', s # query_states, chunk # chunks))
                result)
              t)"
        using out_support unfolding out_some
        by (auto elim!: set_dist_bindE split: prod.splits)
      obtain raws' query_states chunks where result_eq:
        "result = (raws', query_states, chunks)"
        by (cases result) auto
      have out_eq:
        "out =
          Some ((raw' # raws', s # query_states, chunk # chunks), t)"
        using out_some return_support unfolding result_eq by simp
      have raw_eq: "raw' = raw"
        using hit out_eq
        unfolding ro_query_witnesses_raws_fresh_hit_def
        by simp
      have all_fresh:
        "\<forall>j < Suc (length raws_tail).
          fmlookup (HashMap ((s # query_states) ! j))
            (QueryIndexChallenge
              (PQueryCounter ((s # query_states) ! j))
              (PState ((s # query_states) ! j))) = None"
        using hit out_eq
        unfolding ro_query_witnesses_raws_fresh_hit_def
        by simp
      have current_fresh:
        "fmlookup (HashMap s)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
        using all_fresh[rule_format, of 0] by simp
      have head_hit': "?Head (Some (raw', query_state))"
        using raw_eq current_fresh by simp
      show False
        using not_head head_hit' by blast
    qed
  next
    fix raw' query_state
    assume raw_support:
        "Some (raw', query_state) \<in>
          set_dist (execute receive_query_index_challenge s)"
      and head_hit: "?Head (Some (raw', query_state))"
    have raw_eq: "raw' = raw"
      using head_hit by simp
    show
      "wp_event
        (do {
          chunk \<leftarrow> query_opening_stage A i raw';
          assert
            (verifier_query_round_chunk (index (to_nat raw')) trace_roots
              composition_roots chunk);
          ro_record_staged_messages chunk;
          next_query_state \<leftarrow> get;
          (raws', query_states, chunks) \<leftarrow>
            ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots next_query_state (Suc i) n;
          return
            (raw' # raws', s # query_states, chunk # chunks)
        })
        ?Q query_state \<le> ?D"
      unfolding raw_eq Let_def
    proof (rule
        wp_ro_checked_staged_query_program_with_witnesses_after_raw_bound
          [where query_state = s and s = query_state and raws = raws_tail
            and D = ?D])
      fix next_query_state
      show
        "wp_event
          (ro_checked_staged_query_program_with_witnesses A trace_roots
            composition_roots next_query_state (Suc i) n)
          (ro_query_witnesses_raws_fresh_hit raws_tail)
          next_query_state \<le> ?D"
        by (rule Suc.IH[OF len_tail])
    qed
  qed
  have product_bound:
    "wp_event receive_query_index_challenge ?Head s * ?D \<le>
      (1 / nnreal size) * ?D"
    by (rule mult_right_mono[OF head_bound]) simp
  show ?case
    unfolding raws_eq power_Suc
    by (rule order_trans[OF bind_bound product_bound])
qed

lemma wp_ro_checked_staged_query_program_with_witnesses_query_index_list_fresh_bound:
  "wp_event
    (ro_checked_staged_query_program_with_witnesses A trace_roots
      composition_roots s i rounds)
    (ro_query_witnesses_query_index_list_fresh_hit Q) s \<le>
    nnreal (card (query_index_raw_list_preimage Q)) *
      (1 / nnreal size) ^ rounds"
  unfolding ro_query_witnesses_query_index_list_fresh_hit_def
proof -
  have finite_raws: "finite (query_index_raw_list_preimage Q)"
    by (rule finite_query_index_raw_list_preimage)
  have
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots s i rounds)
      (\<lambda>out. \<exists>raws \<in> query_index_raw_list_preimage Q.
        ro_query_witnesses_raws_fresh_hit raws out)
      s \<le>
      (\<Sum>raws \<in> query_index_raw_list_preimage Q.
        (1 / nnreal size) ^ rounds)"
  proof (rule wp_event_finite_UN_bound[OF finite_raws])
    fix raws
    assume raw_in: "raws \<in> query_index_raw_list_preimage Q"
    have len_raws: "length raws = rounds"
      using raw_in unfolding query_index_raw_list_preimage_def by simp
    show
      "wp_event
        (ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots s i rounds)
        (ro_query_witnesses_raws_fresh_hit raws) s \<le>
        (1 / nnreal size) ^ rounds"
      by (rule
          wp_ro_checked_staged_query_program_with_witnesses_raws_fresh_bound
            [OF len_raws])
  qed
  also have "... =
      nnreal (card (query_index_raw_list_preimage Q)) *
        (1 / nnreal size) ^ rounds"
    using finite_raws by simp
  finally show
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots s i rounds)
      (\<lambda>out. \<exists>raws \<in> query_index_raw_list_preimage Q.
        ro_query_witnesses_raws_fresh_hit raws out)
      s \<le>
      nnreal (card (query_index_raw_list_preimage Q)) *
        (1 / nnreal size) ^ rounds"
    .
qed

lemma ro_checked_staged_query_program_with_witnesses_projection:
  "ro_checked_staged_query_program_with_witnesses A trace_roots
      composition_roots query_state i n \<bind>
      (\<lambda>(raws, query_states, chunks). return chunks) =
    ro_checked_staged_query_program A trace_roots composition_roots i n"
proof (induction n arbitrary: i query_state)
  case 0
  then show ?case
    by (simp add: ro_checked_staged_query_program_with_witnesses_def)
next
  case (Suc n)
  have tail:
    "\<And>next_query_state chunk.
      ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots next_query_state (Suc i) n \<bind>
        (\<lambda>(raws, query_states, chunks). return (chunk # chunks)) =
      ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind> (\<lambda>chunks. return (chunk # chunks))"
  proof -
    fix next_query_state chunk
    have ih:
      "ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots next_query_state (Suc i) n \<bind>
          (\<lambda>(raws, query_states, chunks). return chunks) =
        ro_checked_staged_query_program A trace_roots composition_roots
          (Suc i) n"
      by (rule Suc.IH)
    have map:
      "ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots next_query_state (Suc i) n \<bind>
          (\<lambda>(raws, query_states, chunks). return (chunk # chunks)) =
        (ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots next_query_state (Suc i) n \<bind>
          (\<lambda>(raws, query_states, chunks). return chunks)) \<bind>
          (\<lambda>chunks. return (chunk # chunks))"
      by (simp add: sm_bind_assoc split_def)
    also have "... =
        ro_checked_staged_query_program A trace_roots composition_roots
          (Suc i) n \<bind> (\<lambda>chunks. return (chunk # chunks))"
      by (simp only: ih)
    finally show
      "ro_checked_staged_query_program_with_witnesses A trace_roots
          composition_roots next_query_state (Suc i) n \<bind>
          (\<lambda>(raws, query_states, chunks). return (chunk # chunks)) =
        ro_checked_staged_query_program A trace_roots composition_roots
          (Suc i) n \<bind> (\<lambda>chunks. return (chunk # chunks))"
      .
  qed
  have tail':
    "\<And>next_query_state chunk.
      ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots next_query_state (Suc i) n \<bind>
        (\<lambda>x. return (chunk # snd (snd x))) =
      ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind> (\<lambda>chunks. return (chunk # chunks))"
    using tail by (simp add: split_def)
  show ?case
    by (simp add: Let_def sm_bind_assoc split_def tail' sm_bind_get_ignore)
qed

lemma ro_checked_staged_query_program_with_witnesses_outcome:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and outcome:
      "Some ((raws, query_states, chunks), t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots s i n)
            s)"
  shows
    "length raws = n \<and>
     length query_states = n \<and>
     length chunks = n \<and>
     s \<le> t \<and>
     PQueryCounter t = PQueryCounter s + n \<and>
     (\<forall>j < n.
       query_states ! j \<le> t \<and>
       PQueryCounter (query_states ! j) = PQueryCounter s + j \<and>
       fmlookup (HashMap t)
         (QueryIndexChallenge
           (PQueryCounter (query_states ! j))
           (PState (query_states ! j))) =
         Some (raws ! j) \<and>
       verifier_query_round_chunk (index (to_nat (raws ! j)))
         trace_roots composition_roots (chunks ! j)) \<and>
     (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
  using bound outcome
proof (induction n arbitrary: i s t raws query_states chunks)
  case 0
  then show ?case
    by (simp add: ro_checked_staged_query_program_with_witnesses_def
        hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(2)
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
    and rest_out:
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
  have assert_props:
    "s_assert = s2 \<and>
     verifier_query_round_chunk (index (to_nat raw))
       trace_roots composition_roots chunk"
    using assert_out
    unfolding assert_def
    by (cases
        "verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk")
      (simp_all add: throw_no_outcome)
  have s_assert_eq: "s_assert = s2"
    using assert_props by simp
  have chunk_shape:
    "verifier_query_round_chunk (index (to_nat raw))
      trace_roots composition_roots chunk"
    using assert_props by simp

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
  have challenge_counter:
    "PQueryCounter s1 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF challenge_out]
    by simp
  have ext_s1_s2: "s1 \<le> s2"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have stage_counter: "PQueryCounter s2 = PQueryCounter s1"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have record_out':
    "Some ((), s3) \<in>
      set_dist (execute (ro_record_staged_messages chunk) s2)"
    using record_out s_assert_eq by simp
  have record_props: "s2 \<le> s3 \<and> PQueryCounter s3 = PQueryCounter s2"
    by (rule
        ro_record_staged_messages_hash_extends_query_counter[OF record_out'])
  have ext_s2_s3: "s2 \<le> s3"
    using record_props by simp
  have counter_s3: "PQueryCounter s3 = Suc (PQueryCounter s)"
    using record_props stage_counter challenge_counter by simp
  have rest_bound:
    "Suc i + n \<le> length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_result:
    "length raws_tail = n \<and>
     length query_states_tail = n \<and>
     length chunks_tail = n \<and>
     s3 \<le> t \<and>
     PQueryCounter t = PQueryCounter s3 + n \<and>
     (\<forall>j < n.
       query_states_tail ! j \<le> t \<and>
       PQueryCounter (query_states_tail ! j) = PQueryCounter s3 + j \<and>
       fmlookup (HashMap t)
         (QueryIndexChallenge
           (PQueryCounter (query_states_tail ! j))
           (PState (query_states_tail ! j))) =
         Some (raws_tail ! j) \<and>
       verifier_query_round_chunk
         (index (to_nat (raws_tail ! j)))
         trace_roots composition_roots (chunks_tail ! j)) \<and>
     (\<forall>raw \<in> set raws_tail.
       index (to_nat raw) < clength * scale)"
    by (rule Suc.IH[OF rest_bound rest_out])
  have len_raw_tail: "length raws_tail = n"
    using tail_result by blast
  have len_states_tail: "length query_states_tail = n"
    using tail_result by blast
  have len_chunks_tail: "length chunks_tail = n"
    using tail_result by blast
  have ext_s3_t: "s3 \<le> t"
    using tail_result by blast
  have query_count_tail:
    "PQueryCounter t = PQueryCounter s3 + n"
    using tail_result by blast
  have tail_props:
    "\<forall>j < n.
      query_states_tail ! j \<le> t \<and>
      PQueryCounter (query_states_tail ! j) =
        PQueryCounter s3 + j \<and>
      fmlookup (HashMap t)
        (QueryIndexChallenge
          (PQueryCounter (query_states_tail ! j))
          (PState (query_states_tail ! j))) =
        Some (raws_tail ! j) \<and>
      verifier_query_round_chunk
        (index (to_nat (raws_tail ! j)))
        trace_roots composition_roots (chunks_tail ! j)"
    using tail_result by blast
  have raw_tail_bound:
    "\<forall>raw \<in> set raws_tail.
      index (to_nat raw) < clength * scale"
    using tail_result by blast

  have ext_s_t: "s \<le> t"
  proof -
    have "s \<le> s1"
      using challenge by simp
    moreover have "s1 \<le> t"
      by (rule hash_ext_trans[OF ext_s1_s2])
        (rule hash_ext_trans[OF ext_s2_s3 ext_s3_t])
    ultimately show ?thesis
      by (rule hash_ext_trans)
  qed
  have ext_s1_t: "s1 \<le> t"
    by (rule hash_ext_trans[OF ext_s1_s2])
      (rule hash_ext_trans[OF ext_s2_s3 ext_s3_t])
  have lookup_head_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup)
      (use challenge ext_s1_t in simp_all)
  have query_count_all:
    "PQueryCounter t = PQueryCounter s + Suc n"
    using query_count_tail counter_s3 by simp
  have query_props_all:
    "\<forall>j < Suc n.
      (s # query_states_tail) ! j \<le> t \<and>
      PQueryCounter ((s # query_states_tail) ! j) =
        PQueryCounter s + j \<and>
      fmlookup (HashMap t)
        (QueryIndexChallenge
          (PQueryCounter ((s # query_states_tail) ! j))
          (PState ((s # query_states_tail) ! j))) =
        Some ((raw # raws_tail) ! j) \<and>
      verifier_query_round_chunk
        (index (to_nat ((raw # raws_tail) ! j)))
        trace_roots composition_roots ((chunk # chunks_tail) ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show
      "(s # query_states_tail) ! j \<le> t \<and>
       PQueryCounter ((s # query_states_tail) ! j) =
         PQueryCounter s + j \<and>
       fmlookup (HashMap t)
         (QueryIndexChallenge
           (PQueryCounter ((s # query_states_tail) ! j))
           (PState ((s # query_states_tail) ! j))) =
         Some ((raw # raws_tail) ! j) \<and>
       verifier_query_round_chunk
         (index (to_nat ((raw # raws_tail) ! j)))
         trace_roots composition_roots ((chunk # chunks_tail) ! j)"
    proof (cases j)
      case 0
      then show ?thesis
        using ext_s_t lookup_head_t chunk_shape by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      have tail_k:
        "query_states_tail ! k \<le> t \<and>
         PQueryCounter (query_states_tail ! k) =
           PQueryCounter s3 + k \<and>
         fmlookup (HashMap t)
           (QueryIndexChallenge
             (PQueryCounter (query_states_tail ! k))
             (PState (query_states_tail ! k))) =
           Some (raws_tail ! k) \<and>
         verifier_query_round_chunk
           (index (to_nat (raws_tail ! k)))
           trace_roots composition_roots (chunks_tail ! k)"
        using tail_props k_bound by blast
      have state_ext_k: "query_states_tail ! k \<le> t"
        using tail_k by blast
      have counter_k:
        "PQueryCounter (query_states_tail ! k) =
          PQueryCounter s + Suc k"
        using tail_k counter_s3 by simp
      have lookup_k:
        "fmlookup (HashMap t)
          (QueryIndexChallenge
            (PQueryCounter (query_states_tail ! k))
            (PState (query_states_tail ! k))) =
          Some (raws_tail ! k)"
        using tail_k by blast
      have shape_k:
        "verifier_query_round_chunk
          (index (to_nat (raws_tail ! k)))
          trace_roots composition_roots (chunks_tail ! k)"
        using tail_k by blast
      show ?thesis
        using state_ext_k counter_k lookup_k shape_k Suc by simp
    qed
  qed
  have raw_bound_all:
    "\<forall>raw' \<in> set (raw # raws_tail).
      index (to_nat raw') < clength * scale"
    using raw_tail_bound index_less_domain by auto
  show ?case
    unfolding raws_eq query_states_eq chunks_eq
    proof (intro conjI)
    show "length (raw # raws_tail) = Suc n"
      using len_raw_tail by simp
    show "length (s # query_states_tail) = Suc n"
      using len_states_tail by simp
    show "length (chunk # chunks_tail) = Suc n"
      using len_chunks_tail by simp
    show "s \<le> t"
      by (rule ext_s_t)
    show "PQueryCounter t = PQueryCounter s + Suc n"
      by (rule query_count_all)
    show
      "\<forall>j<Suc n.
        (s # query_states_tail) ! j \<le> t \<and>
        PQueryCounter ((s # query_states_tail) ! j) =
          PQueryCounter s + j \<and>
        fmlookup (HashMap t)
          (QueryIndexChallenge
            (PQueryCounter ((s # query_states_tail) ! j))
            (PState ((s # query_states_tail) ! j))) =
          Some ((raw # raws_tail) ! j) \<and>
        verifier_query_round_chunk
          (index (to_nat ((raw # raws_tail) ! j)))
          trace_roots composition_roots ((chunk # chunks_tail) ! j)"
      by (rule query_props_all)
    show
      "\<forall>raw'\<in>set (raw # raws_tail).
        index (to_nat raw') < clength * scale"
      by (rule raw_bound_all)
  qed
qed

end

end
