(*  Title:      Stark/Staged_Security_Experiment_Core.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Core
  imports Controlled_RO Security_Experiment
begin

text \<open>Core staged-adversary records, transcript builders, and experiment projections.\<close>


record staged_budgets =
  trace_root_budget :: nat
  trace_fri_budgets :: "nat list"
  trace_final_budget :: nat
  degree_budget :: nat
  composition_fri_budgets :: "nat list"
  composition_final_budget :: nat
  query_opening_budgets :: "nat list"

record 'f staged_adversary =
  trace_root_stage :: "('f, 'f protocol_channel) state_monad"
  trace_fri_root_stage ::
    "nat \<Rightarrow> 'f list \<Rightarrow> ('f, 'f protocol_channel) state_monad"
  trace_final_stage ::
    "'f list \<Rightarrow> ('f, 'f protocol_channel) state_monad"
  degree_stage ::
    "'f list \<Rightarrow> ('f, 'f protocol_channel) state_monad"
  composition_fri_root_stage ::
    "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'f protocol_channel) state_monad"
  composition_final_stage ::
    "'f \<Rightarrow> 'f list \<Rightarrow> ('f, 'f protocol_channel) state_monad"
  query_opening_stage ::
    "nat \<Rightarrow> 'f \<Rightarrow> ('f list, 'f protocol_channel) state_monad"

record 'f staged_proof_data =
  staged_trace_root :: 'f
  staged_trace_fri_roots :: "'f list"
  staged_trace_fri_challenges :: "'f list"
  staged_trace_final :: 'f
  staged_alphas :: "'f list"
  staged_degree :: 'f
  staged_composition_fri_roots :: "'f list"
  staged_composition_fri_challenges :: "'f list"
  staged_composition_final :: 'f
  staged_query_chunks :: "'f list list"

record 'f staged_composition_prefix_data =
  scp_trace_root :: 'f
  scp_trace_fri_roots :: "'f list"
  scp_trace_fri_challenges :: "'f list"
  scp_trace_final :: 'f
  scp_alphas :: "'f list"
  scp_degree :: 'f
  scp_composition_fri_roots :: "'f list"
  scp_composition_fri_challenges :: "'f list"

record 'f staged_query_prefix_data =
  sqp_trace_root :: 'f
  sqp_trace_fri_roots :: "'f list"
  sqp_trace_fri_challenges :: "'f list"
  sqp_trace_final :: 'f
  sqp_alphas :: "'f list"
  sqp_degree :: 'f
  sqp_composition_fri_roots :: "'f list"
  sqp_composition_fri_challenges :: "'f list"
  sqp_composition_final :: 'f
  sqp_query_chunks :: "'f list list"

context soundness
begin

lemma wp_event_bind_return_map:
  fixes m :: "('x, 'f protocol_channel) state_monad"
  shows
    "wp_event (m \<bind> (\<lambda>x. return (f x))) P s =
      wp_event m (\<lambda>out. case out of None \<Rightarrow> P None
        | Some (x, t) \<Rightarrow> P (Some (f x, t))) s"
proof -
  have indicator_eq:
    "(\<lambda>out. case out of None \<Rightarrow> if P None then 1 else 0
      | Some (x, t) \<Rightarrow> if P (Some (f x, t)) then 1 else 0) =
     (\<lambda>out. if (case out of None \<Rightarrow> P None
      | Some (x, t) \<Rightarrow> P (Some (f x, t))) then 1 else 0)"
    by (rule ext) (simp split: option.splits prod.splits)
  show ?thesis
    unfolding wp_event_def
    apply (subst wp_bind)
    apply (rule arg_cong[where f="\<lambda>Q. wp m Q s"])
    apply (rule ext)
    apply (simp add: wp_return indicator_eq
        split: option.splits prod.splits)
    done
qed

lemma wp_event_bind_mono_cont:
  fixes m :: "('x, 'f protocol_channel) state_monad"
    and k :: "'x \<Rightarrow> ('y, 'f protocol_channel) state_monad"
    and l :: "'x \<Rightarrow> ('z, 'f protocol_channel) state_monad"
  assumes none: "P None \<Longrightarrow> Q None"
    and cont:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        wp_event (k x) P t \<le> wp_event (l x) Q t"
  shows "wp_event (m \<bind> k) P s \<le> wp_event (m \<bind> l) Q s"
proof -
  have left:
    "wp_event (m \<bind> k) P s =
      wp m (\<lambda>out. case out of
          None \<Rightarrow> if P None then 1 else 0
        | Some (x, t) \<Rightarrow> wp_event (k x) P t) s"
    unfolding wp_event_def by (simp add: wpsimps)
  have right:
    "wp_event (m \<bind> l) Q s =
      wp m (\<lambda>out. case out of
          None \<Rightarrow> if Q None then 1 else 0
        | Some (x, t) \<Rightarrow> wp_event (l x) Q t) s"
    unfolding wp_event_def by (simp add: wpsimps)
  show ?thesis
    unfolding left right
  proof (rule wp_mono_on_support)
    fix out
    assume out: "out \<in> set_dist (execute m s)"
    show "(case out of None \<Rightarrow> if P None then 1 else 0
          | Some (x, t) \<Rightarrow> wp_event (k x) P t)
        \<le> (case out of None \<Rightarrow> if Q None then 1 else 0
          | Some (x, t) \<Rightarrow> wp_event (l x) Q t)"
    proof (cases out)
      case None
      then show ?thesis
        using none by (cases "P None") simp_all
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) auto
      show ?thesis
        using cont[of x t] out Some xt by simp
    qed
  qed
qed

lemma wp_event_assert_bind_le:
  fixes k :: "unit \<Rightarrow> ('x, 'f protocol_channel) state_monad"
  assumes none: "\<not> P None"
  shows "wp_event (assert b \<bind> k) P s \<le> wp_event (k ()) P s"
proof (cases b)
  case True
  then show ?thesis
    unfolding assert_def by simp
next
  case False
  then show ?thesis
    using none unfolding assert_def
    by (simp add: wp_event_def wpsimps throw_no_outcome)
qed

definition staged_budget_wellformed :: "staged_budgets \<Rightarrow> bool"
  where
    "staged_budget_wellformed budgets \<longleftrightarrow>
      length (trace_fri_budgets budgets) = ceil_log clength \<and>
      length (composition_fri_budgets budgets) =
        ceil_log (maxDegree + 1) \<and>
      length (query_opening_budgets budgets) = rounds"

definition staged_adversary_controlled
  :: "staged_budgets \<Rightarrow> 'f staged_adversary \<Rightarrow> bool"
  where
    "staged_adversary_controlled budgets A \<longleftrightarrow>
      controlled_ro_program (trace_root_budget budgets)
        (trace_root_stage A) \<and>
      (\<forall>i bs.
        i < length (trace_fri_budgets budgets) \<longrightarrow>
        controlled_ro_program (trace_fri_budgets budgets ! i)
          (trace_fri_root_stage A i bs)) \<and>
      (\<forall>bs.
        controlled_ro_program (trace_final_budget budgets)
          (trace_final_stage A bs)) \<and>
      (\<forall>as.
        controlled_ro_program (degree_budget budgets)
          (degree_stage A as)) \<and>
      (\<forall>dg i bs.
        i < length (composition_fri_budgets budgets) \<longrightarrow>
        controlled_ro_program (composition_fri_budgets budgets ! i)
          (composition_fri_root_stage A dg i bs)) \<and>
      (\<forall>dg bs.
        controlled_ro_program (composition_final_budget budgets)
          (composition_final_stage A dg bs)) \<and>
      (\<forall>i raw.
        i < length (query_opening_budgets budgets) \<longrightarrow>
        controlled_ro_program (query_opening_budgets budgets ! i)
          (query_opening_stage A i raw))"

definition staged_attacker_query_budget :: "staged_budgets \<Rightarrow> nat"
  where
    "staged_attacker_query_budget budgets =
      trace_root_budget budgets +
      sum_list (trace_fri_budgets budgets) +
      trace_final_budget budgets +
      degree_budget budgets +
      sum_list (composition_fri_budgets budgets) +
      composition_final_budget budgets +
      sum_list (query_opening_budgets budgets)"

definition staged_challenge_query_budget :: nat
  where
    "staged_challenge_query_budget =
      ceil_log clength + length spec +
      ceil_log (maxDegree + 1) + rounds"

definition staged_trace_fri_search_queries
  :: "staged_budgets \<Rightarrow> nat \<Rightarrow> nat"
  where
    "staged_trace_fri_search_queries budgets i =
      trace_root_budget budgets +
      sum_list (take (Suc i) (trace_fri_budgets budgets)) + i"

definition staged_alpha_search_queries
  :: "staged_budgets \<Rightarrow> nat \<Rightarrow> nat"
  where
    "staged_alpha_search_queries budgets i =
      trace_root_budget budgets +
      sum_list (trace_fri_budgets budgets) +
      trace_final_budget budgets +
      ceil_log clength + i"

definition staged_composition_fri_search_queries
  :: "staged_budgets \<Rightarrow> nat \<Rightarrow> nat"
  where
    "staged_composition_fri_search_queries budgets i =
      trace_root_budget budgets +
      sum_list (trace_fri_budgets budgets) +
      trace_final_budget budgets +
      degree_budget budgets +
      sum_list (take (Suc i) (composition_fri_budgets budgets)) +
      ceil_log clength + length spec + i"

definition staged_composition_fri_vector_search_queries
  :: "staged_budgets \<Rightarrow> nat"
  where
    "staged_composition_fri_vector_search_queries budgets =
      staged_alpha_search_queries budgets 0 +
      length spec +
      degree_budget budgets +
      sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"

definition staged_query_search_queries
  :: "staged_budgets \<Rightarrow> nat \<Rightarrow> nat"
  where
    "staged_query_search_queries budgets i =
      trace_root_budget budgets +
      sum_list (trace_fri_budgets budgets) +
      trace_final_budget budgets +
      degree_budget budgets +
      sum_list (composition_fri_budgets budgets) +
      composition_final_budget budgets +
      sum_list (take i (query_opening_budgets budgets)) +
      ceil_log clength + length spec +
      ceil_log (maxDegree + 1) + i"

definition staged_phase_relation_error
  :: "nat \<Rightarrow> nat \<Rightarrow> prob"
  where
    "staged_phase_relation_error fiber_bound query_bound =
      hash_relation_budget_value fiber_bound query_bound"

definition staged_phase_target_error
  :: "'f set \<Rightarrow> nat \<Rightarrow> prob"
  where
    "staged_phase_target_error B query_bound =
      hash_target_budget_value B query_bound"

lemma staged_phase_query_index_target_error_fraction_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
  shows
    "staged_phase_target_error (query_index_raw_preimage B) q \<le>
      nnreal q * (nnreal (card B) / nnreal (card query_sample_space))"
proof -
  have raw:
    "nnreal (card (query_index_raw_preimage B)) / nnreal size \<le>
      nnreal (card B) / nnreal (card query_sample_space)"
    using raw_bound subset unfolding query_index_raw_preimage_bound_def
    by blast
  have eq:
    "staged_phase_target_error (query_index_raw_preimage B) q =
      nnreal q *
        (nnreal (card (query_index_raw_preimage B)) / nnreal size)"
    unfolding staged_phase_target_error_def hash_target_budget_value_def
    by transfer (simp add: field_simps)
  show ?thesis
    unfolding eq by (rule mult_left_mono) (use raw in simp_all)
qed

lemma staged_phase_query_index_target_error_query_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (card B) / nnreal (card query_sample_space) \<le> C"
  shows
    "staged_phase_target_error (query_index_raw_preimage B) q \<le>
      nnreal q * C"
proof -
  have
    "staged_phase_target_error (query_index_raw_preimage B) q \<le>
      nnreal q * (nnreal (card B) / nnreal (card query_sample_space))"
    by (rule staged_phase_query_index_target_error_fraction_bound
        [OF raw_bound subset])
  also have "... \<le> nnreal q * C"
    by (rule mult_left_mono) (use frac in simp_all)
  finally show ?thesis .
qed

definition record_staged_message
  :: "'f \<Rightarrow> (unit, 'f protocol_channel) state_monad"
  where
    "record_staged_message x =
      modify
        (\<lambda>s. s\<lparr>
          PState := concat (PState s) x,
          PTranscript := PTranscript s @ [x]\<rparr>)"

definition record_staged_messages
  :: "'f list \<Rightarrow> (unit, 'f protocol_channel) state_monad"
  where
    "record_staged_messages xs = mfold2 record_staged_message xs"

primrec staged_trace_fri_program
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow>
      ('f list \<times> 'f list, 'f protocol_channel) state_monad"
where
  "staged_trace_fri_program A i 0 bs = return ([], bs)"
| "staged_trace_fri_program A i (Suc n) bs =
    do {
      root \<leftarrow> trace_fri_root_stage A i bs;
      record_staged_message root;
      b \<leftarrow> receive_trace_fri_challenge;
      (roots, bs') \<leftarrow> staged_trace_fri_program A (Suc i) n (bs @ [b]);
      return (root # roots, bs')
    }"

primrec staged_alpha_program
  :: "nat \<Rightarrow> ('f list, 'f protocol_channel) state_monad"
where
  "staged_alpha_program 0 = return []"
| "staged_alpha_program (Suc n) =
    do {
      a \<leftarrow> receive_alpha_challenge;
      record_staged_message a;
      as \<leftarrow> staged_alpha_program n;
      return (a # as)
    }"

primrec staged_composition_fri_program
  :: "'f staged_adversary \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow>
      ('f list \<times> 'f list, 'f protocol_channel) state_monad"
where
  "staged_composition_fri_program A dg i 0 bs = return ([], bs)"
| "staged_composition_fri_program A dg i (Suc n) bs =
    do {
      root \<leftarrow> composition_fri_root_stage A dg i bs;
      record_staged_message root;
      b \<leftarrow> receive_composition_fri_challenge;
      (roots, bs') \<leftarrow>
        staged_composition_fri_program A dg (Suc i) n (bs @ [b]);
      return (root # roots, bs')
    }"

primrec staged_query_program
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      ('f list list, 'f protocol_channel) state_monad"
where
  "staged_query_program A i 0 = return []"
| "staged_query_program A i (Suc n) =
    do {
      raw \<leftarrow> receive_query_index_challenge;
      chunk \<leftarrow> query_opening_stage A i raw;
      record_staged_messages chunk;
      chunks \<leftarrow> staged_query_program A (Suc i) n;
      return (chunk # chunks)
    }"

primrec checked_staged_query_program
  :: "'f staged_adversary \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> ('f list list, 'f protocol_channel) state_monad"
where
  "checked_staged_query_program A trace_roots composition_roots i 0 =
    return []"
| "checked_staged_query_program A trace_roots composition_roots i (Suc n) =
    do {
      raw \<leftarrow> receive_query_index_challenge;
      let idx = index (to_nat raw);
      chunk \<leftarrow> query_opening_stage A i raw;
      assert
        (verifier_query_round_chunk idx trace_roots composition_roots chunk);
      record_staged_messages chunk;
      chunks \<leftarrow>
        checked_staged_query_program A trace_roots composition_roots
          (Suc i) n;
      return (chunk # chunks)
    }"

definition staged_transcript_program
  :: "'f staged_adversary \<Rightarrow>
      ('f staged_proof_data, 'f protocol_channel) state_monad"
  where
    "staged_transcript_program A =
      do {
        fr \<leftarrow> trace_root_stage A;
        record_staged_message fr;
        (trace_roots, trace_bs) \<leftarrow>
          staged_trace_fri_program A 0 (ceil_log clength) [];
        trace_final \<leftarrow> trace_final_stage A trace_bs;
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
        query_chunks \<leftarrow> staged_query_program A 0 rounds;
        return
          \<lparr>staged_trace_root = fr,
           staged_trace_fri_roots = trace_roots,
           staged_trace_fri_challenges = trace_bs,
           staged_trace_final = trace_final,
           staged_alphas = as,
           staged_degree = dg,
           staged_composition_fri_roots = composition_roots,
           staged_composition_fri_challenges = composition_bs,
           staged_composition_final = composition_final,
           staged_query_chunks = query_chunks\<rparr>
      }"

definition checked_staged_transcript_program
  :: "'f staged_adversary \<Rightarrow>
      ('f staged_proof_data, 'f protocol_channel) state_monad"
  where
    "checked_staged_transcript_program A =
      do {
        fr \<leftarrow> trace_root_stage A;
        record_staged_message fr;
        (trace_roots, trace_bs) \<leftarrow>
          staged_trace_fri_program A 0 (ceil_log clength) [];
        trace_final \<leftarrow> trace_final_stage A trace_bs;
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
          checked_staged_query_program A trace_roots composition_roots
            0 rounds;
        return
          \<lparr>staged_trace_root = fr,
           staged_trace_fri_roots = trace_roots,
           staged_trace_fri_challenges = trace_bs,
           staged_trace_final = trace_final,
           staged_alphas = as,
           staged_degree = dg,
           staged_composition_fri_roots = composition_roots,
           staged_composition_fri_challenges = composition_bs,
           staged_composition_final = composition_final,
           staged_query_chunks = query_chunks\<rparr>
      }"

definition staged_alpha_prefix_program
  :: "'f staged_adversary \<Rightarrow>
      ('f \<times> 'f list \<times> 'f list \<times> 'f, 'f protocol_channel)
        state_monad"
  where
    "staged_alpha_prefix_program A =
      do {
        fr \<leftarrow> trace_root_stage A;
        record_staged_message fr;
        (trace_roots, trace_bs) \<leftarrow>
          staged_trace_fri_program A 0 (ceil_log clength) [];
        trace_final \<leftarrow> trace_final_stage A trace_bs;
        record_staged_message trace_final;
        return (fr, trace_roots, trace_bs, trace_final)
      }"

definition staged_trace_fri_challenge_prefix_program
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow>
      ('f \<times> 'f list \<times> 'f, 'f protocol_channel) state_monad"
  where
    "staged_trace_fri_challenge_prefix_program A i =
      do {
        fr \<leftarrow> trace_root_stage A;
        record_staged_message fr;
        (_, trace_bs) \<leftarrow> staged_trace_fri_program A 0 i [];
        root \<leftarrow> trace_fri_root_stage A i trace_bs;
        record_staged_message root;
        return (fr, trace_bs, root)
      }"

definition staged_alpha_challenge_prefix_program
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow>
      (('f \<times> 'f list \<times> 'f list \<times> 'f) \<times> 'f list,
       'f protocol_channel) state_monad"
  where
    "staged_alpha_challenge_prefix_program A i =
      do {
        prefix \<leftarrow> staged_alpha_prefix_program A;
        as_prefix \<leftarrow> staged_alpha_program i;
        return (prefix, as_prefix)
      }"

definition staged_composition_fri_challenge_prefix_program
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow>
      ('f \<times> 'f list \<times> 'f, 'f protocol_channel) state_monad"
  where
    "staged_composition_fri_challenge_prefix_program A i =
      do {
        (_, _, trace_bs, _) \<leftarrow> staged_alpha_prefix_program A;
        as \<leftarrow> staged_alpha_program (length spec);
        dg \<leftarrow> degree_stage A as;
        record_staged_message dg;
        let composition_rounds = ceil_log (to_nat dg + 1);
        assert (Suc i \<le> composition_rounds);
        assert (composition_rounds \<le> ceil_log (maxDegree + 1));
        (_, composition_bs) \<leftarrow> staged_composition_fri_program A dg 0 i [];
        root \<leftarrow> composition_fri_root_stage A dg i composition_bs;
        record_staged_message root;
        return (dg, composition_bs, root)
      }"

definition staged_composition_fri_vector_program
  :: "'f staged_adversary \<Rightarrow>
      ('f \<times> 'f list, 'f protocol_channel) state_monad"
  where
    "staged_composition_fri_vector_program A =
      do {
        (_, _, trace_bs, _) \<leftarrow> staged_alpha_prefix_program A;
        as \<leftarrow> staged_alpha_program (length spec);
        dg \<leftarrow> degree_stage A as;
        record_staged_message dg;
        let composition_rounds = ceil_log (to_nat dg + 1);
        assert (composition_rounds \<le> ceil_log (maxDegree + 1));
        (_, composition_bs) \<leftarrow>
          staged_composition_fri_program A dg 0 composition_rounds [];
        return (dg, composition_bs)
      }"

definition staged_composition_fri_full_vector_program
  :: "'f staged_adversary \<Rightarrow>
      ('f staged_composition_prefix_data, 'f protocol_channel) state_monad"
  where
    "staged_composition_fri_full_vector_program A =
      do {
        (fr, trace_roots, trace_bs, trace_final) \<leftarrow>
          staged_alpha_prefix_program A;
        as \<leftarrow> staged_alpha_program (length spec);
        dg \<leftarrow> degree_stage A as;
        record_staged_message dg;
        let composition_rounds = ceil_log (to_nat dg + 1);
        assert (composition_rounds \<le> ceil_log (maxDegree + 1));
        (composition_roots, composition_bs) \<leftarrow>
          staged_composition_fri_program A dg 0 composition_rounds [];
        return
          \<lparr>scp_trace_root = fr,
           scp_trace_fri_roots = trace_roots,
           scp_trace_fri_challenges = trace_bs,
           scp_trace_final = trace_final,
           scp_alphas = as,
           scp_degree = dg,
           scp_composition_fri_roots = composition_roots,
           scp_composition_fri_challenges = composition_bs\<rparr>
      }"

definition staged_query_challenge_prefix_program
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow>
      ('f \<times> 'f \<times> 'f list list, 'f protocol_channel) state_monad"
  where
    "staged_query_challenge_prefix_program A i =
      do {
        (_, _, trace_bs, _) \<leftarrow> staged_alpha_prefix_program A;
        as \<leftarrow> staged_alpha_program (length spec);
        dg \<leftarrow> degree_stage A as;
        record_staged_message dg;
        let composition_rounds = ceil_log (to_nat dg + 1);
        assert (composition_rounds \<le> ceil_log (maxDegree + 1));
        (_, composition_bs) \<leftarrow>
          staged_composition_fri_program A dg 0 composition_rounds [];
        composition_final \<leftarrow>
          composition_final_stage A dg composition_bs;
        record_staged_message composition_final;
        query_chunks \<leftarrow> staged_query_program A 0 i;
        return (dg, composition_final, query_chunks)
      }"

definition checked_staged_query_challenge_prefix_program
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow>
      ('f staged_query_prefix_data, 'f protocol_channel) state_monad"
  where
    "checked_staged_query_challenge_prefix_program A i =
      do {
        (fr, trace_roots, trace_bs, trace_final) \<leftarrow>
          staged_alpha_prefix_program A;
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
          checked_staged_query_program A trace_roots composition_roots 0 i;
        return
          \<lparr>sqp_trace_root = fr,
           sqp_trace_fri_roots = trace_roots,
           sqp_trace_fri_challenges = trace_bs,
           sqp_trace_final = trace_final,
           sqp_alphas = as,
           sqp_degree = dg,
           sqp_composition_fri_roots = composition_roots,
           sqp_composition_fri_challenges = composition_bs,
           sqp_composition_final = composition_final,
           sqp_query_chunks = query_chunks\<rparr>
      }"

definition staged_proof_transcript :: "'f staged_proof_data \<Rightarrow> 'f list"
  where
    "staged_proof_transcript data =
      verifier_header_messages
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data) @
      List.concat (staged_query_chunks data)"

definition staged_trace_fri_start_hash :: "'f staged_proof_data \<Rightarrow> 'f"
  where
    "staged_trace_fri_start_hash data =
      concat 0 (staged_trace_root data)"

definition staged_composition_fri_start_hash
  :: "'f staged_proof_data \<Rightarrow> 'f"
  where
    "staged_composition_fri_start_hash data =
      concat
        (foldl concat
          (concat
            (foldl concat
              (staged_trace_fri_start_hash data)
              (staged_trace_fri_roots data))
            (staged_trace_final data))
          (staged_alphas data))
        (staged_degree data)"

definition staged_query_start_hash :: "'f staged_proof_data \<Rightarrow> 'f"
  where
    "staged_query_start_hash data =
      concat
        (foldl concat
          (staged_composition_fri_start_hash data)
          (staged_composition_fri_roots data))
        (staged_composition_final data)"

definition staged_query_chunks_match_verifier_lengths
  :: "'f staged_proof_data \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "staged_query_chunks_match_verifier_lengths data query_idxs \<longleftrightarrow>
      length (staged_query_chunks data) = rounds \<and>
      (\<forall>i < rounds.
        length (staged_query_chunks data ! i) =
          verifier_query_round_transcript_length (query_idxs ! i)
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data))"

lemma query_chunks_eq_staged_if_matching_lengths:
  assumes parser_len: "length query_chunks = rounds"
    and concat_eq:
      "List.concat query_chunks @ trailing =
        List.concat (staged_query_chunks data)"
    and parser_chunk_len:
      "\<And>i. i < rounds \<Longrightarrow>
        length (query_chunks ! i) =
          verifier_query_round_transcript_length (query_idxs ! i)
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)"
    and staged_len:
      "staged_query_chunks_match_verifier_lengths data query_idxs"
  shows "query_chunks = staged_query_chunks data \<and> trailing = []"
proof -
  have staged_chunks_len:
    "length (staged_query_chunks data) = rounds"
    using staged_len
    unfolding staged_query_chunks_match_verifier_lengths_def by simp
  have same_len:
    "length query_chunks = length (staged_query_chunks data)"
    using parser_len staged_chunks_len by simp
  have same_chunk_lens:
    "\<And>i. i < length query_chunks \<Longrightarrow>
      length (query_chunks ! i) =
        length (staged_query_chunks data ! i)"
  proof -
    fix i
    assume i_bound: "i < length query_chunks"
    then have i_round: "i < rounds"
      using parser_len by simp
    show
      "length (query_chunks ! i) =
        length (staged_query_chunks data ! i)"
      using parser_chunk_len[OF i_round] staged_len i_round
      unfolding staged_query_chunks_match_verifier_lengths_def by simp
  qed
  show ?thesis
    by (rule concat_append_eq_concat_same_chunk_lengths
        [OF same_len same_chunk_lens concat_eq])
qed

lemma verifier_query_round_transcript_length_index_irrelevant:
  "verifier_query_round_transcript_length idx trace_roots composition_roots =
   verifier_query_round_transcript_length idx' trace_roots composition_roots"
  unfolding verifier_query_round_transcript_length_def
    query_decommitment_transcript_length_def powers_scaled_def
  by simp

lemma staged_query_chunks_match_verifier_lengths_transfer:
  assumes match: "staged_query_chunks_match_verifier_lengths data query_idxs"
    and len: "length query_idxs' = rounds"
  shows "staged_query_chunks_match_verifier_lengths data query_idxs'"
proof -
  have chunks_len: "length (staged_query_chunks data) = rounds"
    using match unfolding staged_query_chunks_match_verifier_lengths_def
    by simp
  have chunk_lens:
    "\<forall>i < rounds.
      length (staged_query_chunks data ! i) =
        verifier_query_round_transcript_length (query_idxs' ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < rounds"
    have old:
      "length (staged_query_chunks data ! i) =
        verifier_query_round_transcript_length (query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
      using match i_bound
      unfolding staged_query_chunks_match_verifier_lengths_def by simp
    show
      "length (staged_query_chunks data ! i) =
        verifier_query_round_transcript_length (query_idxs' ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
      using old
        verifier_query_round_transcript_length_index_irrelevant
          [of "query_idxs ! i"
            "staged_trace_fri_roots data"
            "staged_composition_fri_roots data" "query_idxs' ! i"]
      by simp
  qed
  show ?thesis
    unfolding staged_query_chunks_match_verifier_lengths_def
    using chunks_len chunk_lens by simp
qed

definition staged_transcript_trace_fri_vector_hit
  :: "'f list set \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_transcript_trace_fri_vector_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, _) \<Rightarrow> staged_trace_fri_challenges data \<in> B)"

definition staged_transcript_alpha_list_hit
  :: "'f list set \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_transcript_alpha_list_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, _) \<Rightarrow> staged_alphas data \<in> B)"

definition staged_transcript_composition_fri_vector_hit
  :: "('f \<Rightarrow> 'f list set) \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_transcript_composition_fri_vector_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, _) \<Rightarrow>
          staged_composition_fri_challenges data \<in>
            B (staged_degree data))"

definition staged_transcript_composition_fri_vector_guarded_hit
  :: "('f \<Rightarrow> 'f list set) \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_transcript_composition_fri_vector_guarded_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, _) \<Rightarrow>
          staged_composition_fri_challenges data \<in>
            B (staged_degree data) \<and>
          0 < ceil_log (to_nat (staged_degree data) + 1) \<and>
          ceil_log (to_nat (staged_degree data) + 1) \<le>
            ceil_log (maxDegree + 1))"

definition staged_transcript_query_index_set_hit
  :: "nat set \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_transcript_query_index_set_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, t) \<Rightarrow>
          (\<exists>i raw. i < rounds \<and>
            fmlookup (HashMap t)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
              Some raw \<and>
            index (to_nat raw) \<in> B))"

definition staged_security_with_data_trace_fri_vector_hit
  :: "'f list set \<Rightarrow>
      (('f staged_proof_data \<times> unit list) \<times> 'f protocol_channel)
        option \<Rightarrow> bool"
  where
    "staged_security_with_data_trace_fri_vector_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some ((data, _), _) \<Rightarrow> staged_trace_fri_challenges data \<in> B)"

definition staged_security_with_data_alpha_list_hit
  :: "'f list set \<Rightarrow>
      (('f staged_proof_data \<times> unit list) \<times> 'f protocol_channel)
        option \<Rightarrow> bool"
  where
    "staged_security_with_data_alpha_list_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some ((data, _), _) \<Rightarrow> staged_alphas data \<in> B)"

definition staged_security_with_data_alpha_bad_set_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (('f staged_proof_data \<times> unit list) \<times> 'f protocol_channel)
        option \<Rightarrow> bool"
  where
    "staged_security_with_data_alpha_bad_set_hit bad_sets out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some ((data, _), _) \<Rightarrow>
          (\<exists>trace_table. staged_alphas data \<in> bad_sets trace_table))"

definition staged_security_with_data_composition_fri_vector_guarded_hit
  :: "('f \<Rightarrow> 'f list set) \<Rightarrow>
      (('f staged_proof_data \<times> unit list) \<times> 'f protocol_channel)
        option \<Rightarrow> bool"
  where
    "staged_security_with_data_composition_fri_vector_guarded_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some ((data, _), _) \<Rightarrow>
          staged_composition_fri_challenges data \<in>
            B (staged_degree data) \<and>
          0 < ceil_log (to_nat (staged_degree data) + 1) \<and>
          ceil_log (to_nat (staged_degree data) + 1) \<le>
            ceil_log (maxDegree + 1))"

definition staged_security_with_data_query_index_set_hit
  :: "nat set \<Rightarrow>
      (('f staged_proof_data \<times> unit list) \<times> 'f protocol_channel)
        option \<Rightarrow> bool"
  where
    "staged_security_with_data_query_index_set_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some ((data, _), t) \<Rightarrow>
          (\<exists>i raw. i < rounds \<and>
            fmlookup (HashMap t)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
              Some raw \<and>
            index (to_nat raw) \<in> B))"

definition staged_security_with_data_query_bad_hit
  :: "(('f staged_proof_data \<times> unit list) \<times> 'f protocol_channel)
        option \<Rightarrow> bool"
  where
    "staged_security_with_data_query_bad_hit out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some ((_, result), final_state) \<Rightarrow>
          (\<exists>s.
            Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
            query_bad s (Some (result, final_state))))"

definition staged_security_with_data_query_sampling_hit
  :: "(('f staged_proof_data \<times> unit list) \<times> 'f protocol_channel)
        option \<Rightarrow> bool"
  where
    "staged_security_with_data_query_sampling_hit out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some ((_, result), final_state) \<Rightarrow>
          (\<exists>s trace_table composition_table as.
            query_rounds_any_index_set_hit s
              (query_sampling_success_space trace_table composition_table as)
              rounds
              (Some (result, final_state))))"

definition staged_security_with_data_query_header_sampling_hit
  :: "(('f staged_proof_data \<times> unit list) \<times> 'f protocol_channel)
        option \<Rightarrow> bool"
  where
    "staged_security_with_data_query_header_sampling_hit out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some ((_, result), final_state) \<Rightarrow>
          (\<exists>s.
            query_header_rounds_any_index_set_hit s
              (query_header_supported_union_good_sets s
                query_sampling_success_space)
              (Some (result, final_state))))"

definition staged_security_with_data_state_query_bad_hit
  :: "((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_query_bad_hit out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), result), final_state) \<Rightarrow>
          (let s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in
            Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
            query_bad s (Some (result, final_state))))"

definition staged_security_with_data_state_query_header_sampling_hit
  :: "((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_query_header_sampling_hit out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), result), final_state) \<Rightarrow>
          (let s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in
            query_header_rounds_any_index_set_hit s
              (query_header_supported_union_good_sets s
                query_sampling_success_space)
              (Some (result, final_state))))"

definition staged_security_with_data_state_query_header_key_hit
  :: "((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_query_header_key_hit out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), _), final_state) \<Rightarrow>
          (let s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data);
           B =
            query_header_supported_union_good_sets s
              query_sampling_success_space
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              (staged_alphas data)
              (staged_degree data)
              (staged_composition_fri_roots data)
              (staged_composition_final data)
           in
            (\<exists>i raw. i < rounds \<and>
              fmlookup (HashMap final_state)
                (QueryIndexChallenge i
                  (state_after_query_chunks
                    (staged_query_start_hash data)
                    (staged_query_chunks data) i)) =
                Some raw \<and>
              index (to_nat raw) \<in> B)))"

definition staged_security_with_data_state_verifier_event
  :: "('f protocol_channel \<Rightarrow>
        (unit list \<times> 'f protocol_channel) option \<Rightarrow> bool) \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_verifier_event P out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), result), final_state) \<Rightarrow>
          P
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (Some (result, final_state)))"

definition staged_security_with_data_state_transcript_pre_hit
  :: "((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_transcript_pre_hit out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), _), _) \<Rightarrow>
          hash_map_output_values
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)) \<inter>
            set (staged_proof_transcript data) \<noteq> {})"

definition staged_security_with_data_state_transcript_new_hit
  :: "((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_transcript_new_hit out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), _), final_state) \<Rightarrow>
          hash_map_new_output_hit (set (staged_proof_transcript data))
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            final_state)"

definition staged_composition_prefix_fri_vector_hit
  :: "('f \<Rightarrow> 'f list set) \<Rightarrow>
      ('f staged_composition_prefix_data \<times> 'f protocol_channel) option \<Rightarrow>
        bool"
  where
    "staged_composition_prefix_fri_vector_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (prefix, _) \<Rightarrow>
          scp_composition_fri_challenges prefix \<in>
            B (scp_degree prefix) \<and>
          0 < ceil_log (to_nat (scp_degree prefix) + 1) \<and>
          ceil_log (to_nat (scp_degree prefix) + 1) \<le>
            ceil_log (maxDegree + 1))"

definition staged_after_alpha_prefix_program
  :: "'f staged_adversary \<Rightarrow>
      'f \<times> 'f list \<times> 'f list \<times> 'f \<Rightarrow>
      ('f staged_proof_data, 'f protocol_channel) state_monad"
  where
    "staged_after_alpha_prefix_program A prefix =
      (case prefix of (fr, trace_roots, trace_bs, trace_final) \<Rightarrow>
        do {
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
          query_chunks \<leftarrow> staged_query_program A 0 rounds;
          return
            \<lparr>staged_trace_root = fr,
             staged_trace_fri_roots = trace_roots,
             staged_trace_fri_challenges = trace_bs,
             staged_trace_final = trace_final,
             staged_alphas = as,
             staged_degree = dg,
             staged_composition_fri_roots = composition_roots,
             staged_composition_fri_challenges = composition_bs,
             staged_composition_final = composition_final,
             staged_query_chunks = query_chunks\<rparr>
        })"

definition staged_after_composition_fri_full_vector_program
  :: "'f staged_adversary \<Rightarrow> 'f staged_composition_prefix_data \<Rightarrow>
      ('f staged_proof_data, 'f protocol_channel) state_monad"
  where
    "staged_after_composition_fri_full_vector_program A prefix =
      do {
        composition_final \<leftarrow>
          composition_final_stage A
            (scp_degree prefix)
            (scp_composition_fri_challenges prefix);
        record_staged_message composition_final;
        query_chunks \<leftarrow> staged_query_program A 0 rounds;
        return
          \<lparr>staged_trace_root = scp_trace_root prefix,
           staged_trace_fri_roots = scp_trace_fri_roots prefix,
           staged_trace_fri_challenges = scp_trace_fri_challenges prefix,
           staged_trace_final = scp_trace_final prefix,
           staged_alphas = scp_alphas prefix,
           staged_degree = scp_degree prefix,
           staged_composition_fri_roots =
             scp_composition_fri_roots prefix,
           staged_composition_fri_challenges =
             scp_composition_fri_challenges prefix,
           staged_composition_final = composition_final,
           staged_query_chunks = query_chunks\<rparr>
      }"

lemma staged_transcript_program_alpha_prefix_decomp:
  "staged_transcript_program A =
    staged_alpha_prefix_program A \<bind>
      staged_after_alpha_prefix_program A"
  unfolding staged_transcript_program_def staged_alpha_prefix_program_def
    staged_after_alpha_prefix_program_def Let_def
  by (simp add: sm_bind_assoc split_def split: prod.splits)

lemma staged_transcript_program_composition_fri_full_vector_decomp:
  "staged_transcript_program A =
    staged_composition_fri_full_vector_program A \<bind>
      staged_after_composition_fri_full_vector_program A"
  unfolding staged_transcript_program_def
    staged_composition_fri_full_vector_program_def
    staged_after_composition_fri_full_vector_program_def
    staged_alpha_prefix_program_def Let_def
  by (simp add: sm_bind_assoc split_def split: prod.splits)

lemma staged_composition_fri_vector_program_projection:
  "staged_composition_fri_vector_program A =
    staged_composition_fri_full_vector_program A \<bind>
      (\<lambda>prefix. return
        (scp_degree prefix, scp_composition_fri_challenges prefix))"
  unfolding staged_composition_fri_vector_program_def
    staged_composition_fri_full_vector_program_def
    staged_alpha_prefix_program_def Let_def
  by (simp add: sm_bind_assoc split_def split: prod.splits)

lemma staged_after_alpha_prefix_program_trace_fri_vector_hitD:
  assumes outcome:
    "out \<in>
      set_dist
        (execute
          (staged_after_alpha_prefix_program A
            (fr, trace_roots, trace_bs, trace_final)) s)"
    and hit: "staged_transcript_trace_fri_vector_hit B out"
  shows "trace_bs \<in> B"
proof (cases out)
  case None
  then show ?thesis
    using hit unfolding staged_transcript_trace_fri_vector_hit_def by simp
next
  case (Some result)
  then obtain data u where out_eq: "out = Some (data, u)"
    by (cases result) simp
  from outcome[unfolded out_eq]
  obtain as s1 dg s2 s3 composition_roots composition_bs s4
      composition_final s5 s6 query_chunks where
    ret:
      "Some (data, u) \<in>
        set_dist
          (execute
            (return
              \<lparr>staged_trace_root = fr,
               staged_trace_fri_roots = trace_roots,
               staged_trace_fri_challenges = trace_bs,
               staged_trace_final = trace_final,
               staged_alphas = as,
               staged_degree = dg,
               staged_composition_fri_roots = composition_roots,
               staged_composition_fri_challenges = composition_bs,
               staged_composition_final = composition_final,
               staged_query_chunks = query_chunks\<rparr>)
            s6)"
    unfolding staged_after_alpha_prefix_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have data_eq:
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
    using ret by simp
  show ?thesis
    using hit unfolding out_eq data_eq
      staged_transcript_trace_fri_vector_hit_def
    by simp
qed

lemma staged_after_alpha_prefix_program_alpha_list_hitD:
  assumes outcome:
    "out \<in>
      set_dist
        (execute
          (staged_after_alpha_prefix_program A
            (fr, trace_roots, trace_bs, trace_final)) s)"
    and hit: "staged_transcript_alpha_list_hit B out"
  shows
    "\<exists>as s1.
      Some (as, s1) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s) \<and>
      as \<in> B"
proof (cases out)
  case None
  then show ?thesis
    using hit unfolding staged_transcript_alpha_list_hit_def by simp
next
  case (Some result)
  then obtain data u where out_eq: "out = Some (data, u)"
    by (cases result) simp
  from outcome[unfolded out_eq]
  obtain as s1 dg s2 s3 composition_roots composition_bs s4
      composition_final s5 s6 query_chunks where
    alpha_out:
      "Some (as, s1) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s)"
    and ret:
      "Some (data, u) \<in>
        set_dist
          (execute
            (return
              \<lparr>staged_trace_root = fr,
               staged_trace_fri_roots = trace_roots,
               staged_trace_fri_challenges = trace_bs,
               staged_trace_final = trace_final,
               staged_alphas = as,
               staged_degree = dg,
               staged_composition_fri_roots = composition_roots,
               staged_composition_fri_challenges = composition_bs,
               staged_composition_final = composition_final,
               staged_query_chunks = query_chunks\<rparr>)
            s6)"
    unfolding staged_after_alpha_prefix_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have data_eq:
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
    using ret by simp
  have as_in: "as \<in> B"
    using hit unfolding out_eq data_eq
      staged_transcript_alpha_list_hit_def
    by simp
  show ?thesis
    using alpha_out as_in by blast
qed

lemma staged_after_alpha_prefix_program_alpha_list_bound_from_alpha_program:
  assumes alpha_bound:
    "wp_event (staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le> C"
  shows
    "wp_event
      (staged_after_alpha_prefix_program A
        (fr, trace_roots, trace_bs, trace_final))
      (staged_transcript_alpha_list_hit B) s \<le> C"
proof -
  have decomp:
    "staged_after_alpha_prefix_program A
        (fr, trace_roots, trace_bs, trace_final) =
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. let composition_rounds =
              ceil_log (to_nat dg + 1)
             in assert
                (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  composition_rounds [] \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                      (\<lambda>_. staged_query_program A 0 rounds \<bind>
                      (\<lambda>query_chunks.
                        return
                          \<lparr>staged_trace_root = fr,
                           staged_trace_fri_roots = trace_roots,
                           staged_trace_fri_challenges = trace_bs,
                           staged_trace_final = trace_final,
                           staged_alphas = as,
                           staged_degree = dg,
                           staged_composition_fri_roots =
                            composition_roots,
                           staged_composition_fri_challenges =
                            composition_bs,
                           staged_composition_final =
                            composition_final,
                           staged_query_chunks =
                            query_chunks\<rparr>)))))))))"
    unfolding staged_after_alpha_prefix_program_def Let_def
    by simp
  show ?thesis
    unfolding decomp
  proof (rule wp_event_bind_bound_by_head_event[OF alpha_bound])
    show "staged_transcript_alpha_list_hit B None \<Longrightarrow>
      (case None of None \<Rightarrow> False | Some (as, _) \<Rightarrow> as \<in> B)"
      unfolding staged_transcript_alpha_list_hit_def by simp
  next
    fix as s1 out
    assume alpha_out:
      "Some (as, s1) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s)"
      and cont:
        "out \<in>
          set_dist
            (execute
              (degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. let composition_rounds =
                    ceil_log (to_nat dg + 1)
                   in assert
                      (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                      (\<lambda>_. staged_composition_fri_program A dg 0
                        composition_rounds [] \<bind>
                        (\<lambda>(composition_roots, composition_bs).
                          composition_final_stage A dg composition_bs \<bind>
                          (\<lambda>composition_final.
                            record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 rounds \<bind>
                            (\<lambda>query_chunks.
                              return
                                \<lparr>staged_trace_root = fr,
                                 staged_trace_fri_roots = trace_roots,
                                 staged_trace_fri_challenges = trace_bs,
                                 staged_trace_final = trace_final,
                                 staged_alphas = as,
                                 staged_degree = dg,
                                 staged_composition_fri_roots =
                                  composition_roots,
                                 staged_composition_fri_challenges =
                                  composition_bs,
                                 staged_composition_final =
                                  composition_final,
                                 staged_query_chunks =
                                  query_chunks\<rparr>))))))))
              s1)"
      and hit: "staged_transcript_alpha_list_hit B out"
    show "(case Some (as, s1) of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B)"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding staged_transcript_alpha_list_hit_def by simp
    next
      case (Some result)
      then obtain data u where out_eq: "out = Some (data, u)"
        by (cases result) simp
      from cont[unfolded out_eq]
      obtain dg s2 s3 composition_roots composition_bs s4
          composition_final s5 s6 query_chunks where
        ret:
          "Some (data, u) \<in>
            set_dist
              (execute
                (return
                  \<lparr>staged_trace_root = fr,
                   staged_trace_fri_roots = trace_roots,
                   staged_trace_fri_challenges = trace_bs,
                   staged_trace_final = trace_final,
                   staged_alphas = as,
                   staged_degree = dg,
                   staged_composition_fri_roots = composition_roots,
                   staged_composition_fri_challenges = composition_bs,
                   staged_composition_final = composition_final,
                   staged_query_chunks = query_chunks\<rparr>)
                s6)"
        by (auto simp: Let_def assert_def
            elim!: set_dist_bindE split: prod.splits)
      have data_eq:
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
        using ret by simp
      show ?thesis
        using hit unfolding out_eq data_eq
          staged_transcript_alpha_list_hit_def by simp
    qed
  qed
qed

lemma staged_after_composition_fri_full_vector_program_hitD:
  assumes outcome:
    "out \<in>
      set_dist
        (execute
          (staged_after_composition_fri_full_vector_program A prefix) s)"
    and hit:
      "staged_transcript_composition_fri_vector_guarded_hit B out"
  shows "staged_composition_prefix_fri_vector_hit B (Some (prefix, s))"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding staged_transcript_composition_fri_vector_guarded_hit_def
    by simp
next
  case (Some result)
  then obtain data u where out_eq: "out = Some (data, u)"
    by (cases result) simp
  from outcome[unfolded out_eq]
  obtain composition_final s1 s2 query_chunks where
    ret:
      "Some (data, u) \<in>
        set_dist
          (execute
            (return
              \<lparr>staged_trace_root = scp_trace_root prefix,
               staged_trace_fri_roots = scp_trace_fri_roots prefix,
               staged_trace_fri_challenges =
                 scp_trace_fri_challenges prefix,
               staged_trace_final = scp_trace_final prefix,
               staged_alphas = scp_alphas prefix,
               staged_degree = scp_degree prefix,
               staged_composition_fri_roots =
                 scp_composition_fri_roots prefix,
               staged_composition_fri_challenges =
                 scp_composition_fri_challenges prefix,
               staged_composition_final = composition_final,
               staged_query_chunks = query_chunks\<rparr>)
            s2)"
    unfolding staged_after_composition_fri_full_vector_program_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have data_eq:
    "data =
      \<lparr>staged_trace_root = scp_trace_root prefix,
       staged_trace_fri_roots = scp_trace_fri_roots prefix,
       staged_trace_fri_challenges = scp_trace_fri_challenges prefix,
       staged_trace_final = scp_trace_final prefix,
       staged_alphas = scp_alphas prefix,
       staged_degree = scp_degree prefix,
       staged_composition_fri_roots =
         scp_composition_fri_roots prefix,
       staged_composition_fri_challenges =
         scp_composition_fri_challenges prefix,
       staged_composition_final = composition_final,
       staged_query_chunks = query_chunks\<rparr>"
    using ret by simp
  show ?thesis
    using hit
    unfolding out_eq data_eq
      staged_transcript_composition_fri_vector_guarded_hit_def
      staged_composition_prefix_fri_vector_hit_def
    by simp
qed

lemma staged_proof_transcript_verifier_header_transcript:
  assumes trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    and alpha_len:
      "length (staged_alphas data) = length spec"
    and composition_len:
      "length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1)"
  shows
    "verifier_header_transcript
      (verifier_state_from_adversary s (staged_proof_transcript data))
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
  using trace_len alpha_len composition_len
  unfolding verifier_header_transcript_def staged_proof_transcript_def
  by simp

definition staged_security_experiment
  :: "'f staged_adversary \<Rightarrow>
      (unit list, 'f protocol_channel) state_monad"
  where
    "staged_security_experiment A =
      staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_. verify_monad)))"

definition staged_security_experiment_with_data
  :: "'f staged_adversary \<Rightarrow>
      ('f staged_proof_data \<times> unit list, 'f protocol_channel) state_monad"
  where
    "staged_security_experiment_with_data A =
      staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_. verify_monad \<bind> (\<lambda>result. return (data, result)))))"

definition staged_security_experiment_with_data_state
  :: "'f staged_adversary \<Rightarrow>
      (('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list,
        'f protocol_channel) state_monad"
  where
    "staged_security_experiment_with_data_state A =
      staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_.
              verify_monad \<bind>
                (\<lambda>result. return ((data, s), result)))))"

definition checked_staged_security_experiment
  :: "'f staged_adversary \<Rightarrow>
      (unit list, 'f protocol_channel) state_monad"
  where
    "checked_staged_security_experiment A =
      checked_staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_. verify_monad)))"

definition checked_staged_security_experiment_with_data
  :: "'f staged_adversary \<Rightarrow>
      ('f staged_proof_data \<times> unit list, 'f protocol_channel) state_monad"
  where
    "checked_staged_security_experiment_with_data A =
      checked_staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_. verify_monad \<bind> (\<lambda>result. return (data, result)))))"

definition checked_staged_security_experiment_with_data_state
  :: "'f staged_adversary \<Rightarrow>
      (('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list,
        'f protocol_channel) state_monad"
  where
    "checked_staged_security_experiment_with_data_state A =
      checked_staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_.
              verify_monad \<bind>
                (\<lambda>result. return ((data, s), result)))))"

lemma staged_security_experiment_projection:
  "staged_security_experiment_with_data A \<bind>
    (\<lambda>x. return (snd x)) =
    staged_security_experiment A"
  unfolding staged_security_experiment_with_data_def
    staged_security_experiment_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma staged_security_experiment_with_data_state_projection:
  "staged_security_experiment_with_data_state A \<bind>
    (\<lambda>x. return (snd x)) =
    staged_security_experiment A"
  unfolding staged_security_experiment_with_data_state_def
    staged_security_experiment_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma staged_security_experiment_with_data_state_projection_to_data:
  "staged_security_experiment_with_data_state A \<bind>
    (\<lambda>x. case x of ((data, _), result) \<Rightarrow>
      return (data, result)) =
    staged_security_experiment_with_data A"
  unfolding staged_security_experiment_with_data_state_def
    staged_security_experiment_with_data_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma checked_staged_security_experiment_projection:
  "checked_staged_security_experiment_with_data A \<bind>
    (\<lambda>x. return (snd x)) =
    checked_staged_security_experiment A"
  unfolding checked_staged_security_experiment_with_data_def
    checked_staged_security_experiment_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma checked_staged_security_experiment_with_data_state_projection:
  "checked_staged_security_experiment_with_data_state A \<bind>
    (\<lambda>x. return (snd x)) =
    checked_staged_security_experiment A"
  unfolding checked_staged_security_experiment_with_data_state_def
    checked_staged_security_experiment_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma checked_staged_security_experiment_with_data_state_projection_to_data:
  "checked_staged_security_experiment_with_data_state A \<bind>
    (\<lambda>x. case x of ((data, _), result) \<Rightarrow>
      return (data, result)) =
    checked_staged_security_experiment_with_data A"
  unfolding checked_staged_security_experiment_with_data_state_def
    checked_staged_security_experiment_with_data_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma staged_security_experiment_acceptance_with_data:
  "wp_event (staged_security_experiment A) accepted adversary_initial_state =
    wp_event (staged_security_experiment_with_data A) accepted
      adversary_initial_state"
proof -
  have proj:
    "staged_security_experiment A =
      staged_security_experiment_with_data A \<bind>
        (\<lambda>x. return (snd x))"
    using staged_security_experiment_projection by simp
  show ?thesis
    unfolding proj
    by (subst wp_event_bind_return_map[where f=snd])
      (unfold wp_event_def accepted_def,
       rule arg_cong[where
        f="\<lambda>Q. wp (staged_security_experiment_with_data A) Q
          adversary_initial_state"],
       rule ext, simp split: option.splits prod.splits)
qed

lemma staged_security_experiment_acceptance_with_data_state:
  "wp_event (staged_security_experiment A) accepted adversary_initial_state =
    wp_event (staged_security_experiment_with_data_state A) accepted
      adversary_initial_state"
proof -
  have proj:
    "staged_security_experiment A =
      staged_security_experiment_with_data_state A \<bind>
        (\<lambda>x. return (snd x))"
    using staged_security_experiment_with_data_state_projection by simp
  show ?thesis
    unfolding proj
    by (subst wp_event_bind_return_map[where f=snd])
      (unfold wp_event_def accepted_def,
       rule arg_cong[where
        f="\<lambda>Q. wp (staged_security_experiment_with_data_state A) Q
          adversary_initial_state"],
       rule ext, simp split: option.splits prod.splits)
qed

lemma checked_staged_security_experiment_acceptance_with_data:
  "wp_event (checked_staged_security_experiment A) accepted
      adversary_initial_state =
    wp_event (checked_staged_security_experiment_with_data A) accepted
      adversary_initial_state"
proof -
  have proj:
    "checked_staged_security_experiment A =
      checked_staged_security_experiment_with_data A \<bind>
        (\<lambda>x. return (snd x))"
    using checked_staged_security_experiment_projection by simp
  show ?thesis
    unfolding proj
    by (subst wp_event_bind_return_map[where f=snd])
      (unfold wp_event_def accepted_def,
       rule arg_cong[where
        f="\<lambda>Q. wp (checked_staged_security_experiment_with_data A) Q
          adversary_initial_state"],
       rule ext, simp split: option.splits prod.splits)
qed

lemma checked_staged_security_experiment_acceptance_with_data_state:
  "wp_event (checked_staged_security_experiment A) accepted
      adversary_initial_state =
    wp_event (checked_staged_security_experiment_with_data_state A) accepted
      adversary_initial_state"
proof -
  have proj:
    "checked_staged_security_experiment A =
      checked_staged_security_experiment_with_data_state A \<bind>
        (\<lambda>x. return (snd x))"
    using checked_staged_security_experiment_with_data_state_projection
    by simp
  show ?thesis
    unfolding proj
    by (subst wp_event_bind_return_map[where f=snd])
      (unfold wp_event_def accepted_def,
       rule arg_cong[where
        f="\<lambda>Q. wp (checked_staged_security_experiment_with_data_state A) Q
          adversary_initial_state"],
       rule ext, simp split: option.splits prod.splits)
qed

lemma staged_security_experiment_with_data_event_from_data_state:
  "wp_event (staged_security_experiment_with_data A) P adversary_initial_state =
    wp_event (staged_security_experiment_with_data_state A)
      (\<lambda>out. case out of None \<Rightarrow> P None
        | Some (((data, _), result), t) \<Rightarrow> P (Some ((data, result), t)))
      adversary_initial_state"
proof -
  have proj:
    "staged_security_experiment_with_data A =
      staged_security_experiment_with_data_state A \<bind>
        (\<lambda>x. case x of ((data, _), result) \<Rightarrow>
          return (data, result))"
    using staged_security_experiment_with_data_state_projection_to_data
    by simp
  show ?thesis
    unfolding proj wp_event_def
    apply (subst wp_bind)
    apply (rule arg_cong[where
      f="\<lambda>Q. wp (staged_security_experiment_with_data_state A) Q
        adversary_initial_state"])
    apply (rule ext)
    apply (simp add: wp_return split: option.splits prod.splits)
    done
qed

lemma checked_staged_security_experiment_with_data_event_from_data_state:
  "wp_event (checked_staged_security_experiment_with_data A) P
      adversary_initial_state =
    wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out. case out of None \<Rightarrow> P None
        | Some (((data, _), result), t) \<Rightarrow> P (Some ((data, result), t)))
      adversary_initial_state"
proof -
  have proj:
    "checked_staged_security_experiment_with_data A =
      checked_staged_security_experiment_with_data_state A \<bind>
        (\<lambda>x. case x of ((data, _), result) \<Rightarrow>
          return (data, result))"
    using checked_staged_security_experiment_with_data_state_projection_to_data
    by simp
  show ?thesis
    unfolding proj wp_event_def
    apply (subst wp_bind)
    apply (rule arg_cong[where
      f="\<lambda>Q. wp (checked_staged_security_experiment_with_data_state A) Q
        adversary_initial_state"])
    apply (rule ext)
    apply (simp add: wp_return split: option.splits prod.splits)
    done
qed

lemma staged_security_experiment_with_data_state_outcomeE:
  assumes
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (staged_security_experiment_with_data_state A) initial_state)"
  obtains
    "Some (data, attacker_state) \<in>
      set_dist (execute (staged_transcript_program A) initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
  using assms unfolding staged_security_experiment_with_data_state_def
  by (auto elim!: set_dist_bindE intro: that)

lemma checked_staged_security_experiment_with_data_state_outcomeE:
  assumes
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_data_state A)
          initial_state)"
  obtains
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A) initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
  using assms
  unfolding checked_staged_security_experiment_with_data_state_def
  by (auto elim!: set_dist_bindE intro: that)

lemma checked_staged_security_with_data_state_verifier_event_bound_from_cont:
  assumes no_none: "\<And>s. \<not> P s None"
    and cont_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (P
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event P)
      adversary_initial_state \<le> C"
  unfolding checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> staged_security_with_data_state_verifier_event P None"
    unfolding staged_security_with_data_state_verifier_event_def by simp
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have cont_eq:
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad \<bind>
            (\<lambda>result. return ((data, s), result)))))
      (staged_security_with_data_state_verifier_event P) attacker_state =
      wp_event verify_monad (P ?s) ?s"
    unfolding wp_event_def staged_security_with_data_state_verifier_event_def
    apply (simp add: wpsimps)
    apply (rule arg_cong[where f="\<lambda>Q. wp verify_monad Q ?s"])
    apply (rule ext)
    apply (simp add: no_none wp_return split: option.splits prod.splits)
    done
  show
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad \<bind>
            (\<lambda>result. return ((data, s), result)))))
      (staged_security_with_data_state_verifier_event P) attacker_state \<le> C"
	    unfolding cont_eq by (rule cont_bound[OF builder])
qed

lemma checked_staged_security_with_data_state_bound_from_data_cont:
  assumes none: "\<not> P None"
    and cont_bound:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<Longrightarrow>
        wp_event verify_monad
          (\<lambda>out.
            P (case out of
                None \<Rightarrow> None
              | Some (result, final_state) \<Rightarrow>
                  Some (((data, attacker_state), result), final_state)))
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A) P
      adversary_initial_state \<le> C"
  unfolding checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> P None"
    by (rule none)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have cont_eq:
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad \<bind>
            (\<lambda>result. return ((data, s), result)))))
      P attacker_state =
     wp_event verify_monad
      (\<lambda>out.
        P (case out of
            None \<Rightarrow> None
          | Some (result, final_state) \<Rightarrow>
              Some (((data, attacker_state), result), final_state)))
      ?s"
    unfolding wp_event_def
    apply (simp add: none wpsimps)
    apply (rule arg_cong[where f="\<lambda>Q. wp verify_monad Q ?s"])
    apply (rule ext)
    apply (rename_tac out)
    apply (case_tac out)
     apply (simp add: none)
    apply (rename_tac result_state)
    apply (case_tac result_state)
    by (simp add: wp_return)
  show
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad \<bind>
            (\<lambda>result. return ((data, s), result)))))
      P attacker_state \<le> C"
    unfolding cont_eq by (rule cont_bound[OF builder])
qed

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound:
  assumes query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le> C"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and event:
      "staged_security_with_data_state_verifier_event query_bad out"
    show "staged_security_with_data_state_query_bad_hit out"
    proof (cases out)
      case None
      then show ?thesis
        using event unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      have verifier:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        using checked_staged_security_experiment_with_data_state_outcomeE
          [OF support[unfolded out_eq]]
        by blast
      have bad: "query_bad ?s (Some (result, final_state))"
        using event
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
      show ?thesis
        unfolding out_eq staged_security_with_data_state_query_bad_hit_def
          Let_def
        using verifier bad by simp
    qed
  qed
  also have "... \<le> C"
    by (rule query_bound)
  finally show ?thesis .
qed

definition staged_semantic_adversary
  :: "'f staged_adversary \<Rightarrow> 'f semantic_adversary"
  where
    "staged_semantic_adversary A =
      staged_transcript_program A \<bind>
        (\<lambda>data. return (staged_proof_transcript data))"

lemma staged_security_experiment_eq_security_experiment:
  "staged_security_experiment A =
    security_experiment (staged_semantic_adversary A)"
  unfolding staged_security_experiment_def security_experiment_def
    staged_semantic_adversary_def verifier_state_transfer_def
  by (simp add: sm_bind_assoc)

definition staged_adversary_acceptance_probability
  :: "'f staged_adversary \<Rightarrow> prob"
  where
    "staged_adversary_acceptance_probability A =
      wp_event (staged_security_experiment A)
        (\<lambda>out. \<not> Option.is_none out) adversary_initial_state"

definition checked_staged_adversary_acceptance_probability
  :: "'f staged_adversary \<Rightarrow> prob"
  where
    "checked_staged_adversary_acceptance_probability A =
      wp_event (checked_staged_security_experiment A)
        (\<lambda>out. \<not> Option.is_none out) adversary_initial_state"

end

end
