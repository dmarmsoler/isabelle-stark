(* Title: Stark/Soundness_FRI_Weighted_Staged_Logging.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Staged_Logging
  imports
    "Soundness_FRI_Weighted_Program_Logging"
begin

section \<open>Staged Logging for weighted MCA soundness\<close>

text \<open>Derive logging bounds from the actual staged commitment, challenge and query programs, including reachable-continuation budget guards. No new adversary-control premise is introduced.\<close>

subsection \<open>Logged Reachable Continuations\<close>

lemma lo_bind_cong:
  assumes eq: "\<And>s x t. Some (x,t)\<in>set_dist (execute m s) \<Longrightarrow> execute (k x) t=execute (l x) t"
  shows "m \<bind> k=m \<bind> l"
proof (rule execute_inject[THEN iffD1], rule ext, rule dist_inject[THEN iffD1])
  fix s
  show "dist (execute (m \<bind> k) s)=dist (execute (m \<bind> l) s)"
    unfolding sm_bind.rep_eq dist_bind.rep_eq map_fun_def comp_def
    apply (rule map_bind_cong)
     apply simp
    using eq
    apply (auto simp: bind_cont_map_def set_dist_def split: option.splits prod.splits)
    by fastforce
qed

context soundness
begin

lemma lo_bind_on_outcomes:
  fixes m :: "('a, 'f protocol_channel) state_monad"
    and k :: "'a \<Rightarrow> ('b, 'f protocol_channel) state_monad"
  assumes left: "lc_program q m"
    and right: "\<And>s x t. Some (x,t)\<in>set_dist (execute m s) \<Longrightarrow> lc_program r (k x)"
  shows "lc_program (q+r) (m \<bind> k)"
proof -
  let ?reach="\<lambda>x. \<exists>s t. Some (x,t)\<in>set_dist (execute m s)"
  let ?kont="\<lambda>x. if ?reach x then k x else throw"
  have kont: "lc_program r (?kont x)" for x
  proof (cases "?reach x")
    case True
    then show ?thesis using right by auto
  next
    case False
    have zero: "lc_program 0 (throw :: ('b, 'f protocol_channel) state_monad)"
      by (rule lc_preserving) (rule hash_map_preserving_throw)
    have bounded: "lc_program r (throw :: ('b, 'f protocol_channel) state_monad)"
      by (rule lc_weaken[OF zero]) simp
    show ?thesis using False bounded by simp
  qed
  have eq: "m \<bind> ?kont=m \<bind> k"
    by (rule lo_bind_cong) auto
  have "lc_program (q+r) (m \<bind> ?kont)" by (rule lc_bind[OF left]) (rule kont)
  then show ?thesis by (simp only: eq)
qed

lemmas lc_program_zero = lc_preserving
lemmas lc_program_hash = lc_hash
lemmas lc_program_bind = lc_bind
lemmas lc_program_bind_on_outcomes = lo_bind_on_outcomes
lemmas controlled_ro_program_lc_program = lc_controlled
lemma lc_program_mono: "q \<le> r \<Longrightarrow> lc_program q m \<Longrightarrow> lc_program r m"
  by (rule lc_weaken)

lemma lc_program_get:
  "lc_program 0
    (get :: ('f protocol_channel, 'f protocol_channel) state_monad)"
  by (rule lc_program_zero)
    (rule hash_map_preserving_get)

lemma lc_program_assert:
  "lc_program 0
    (assert x :: (unit, 'f protocol_channel) state_monad)"
  by (rule lc_program_zero)
    (rule hash_map_preserving_assert)

lemma lc_program_modify:
  fixes f :: "'f protocol_channel \<Rightarrow> 'f protocol_channel"
  assumes "\<And>s. HashMap (f s) = HashMap s"
  shows "lc_program 0 (modify f)"
  by (rule lc_program_zero)
    (rule hash_map_preserving_modify[OF assms])

lemma lc_program_return:
  "lc_program 0
    (return x :: ('a, 'f protocol_channel) state_monad)"
  by (rule lc_program_zero)
    (rule hash_map_preserving_return)

lemma lc_program_ro_record_staged_message:
  "lc_program 1 (ro_record_staged_message x)"
proof -
  have modify_step:
    "lc_program 0
      (modify
        (\<lambda>s. s\<lparr>PState := h,
          PTranscript := PTranscript s @ [x]\<rparr>) ::
        (unit, 'f protocol_channel) state_monad)"
    for h :: 'f
    by (rule lc_program_modify) simp
  have hash_then_modify:
    "lc_program (1 + 0)
      (hash (TranscriptAbsorb (PState s) x) \<bind>
        (\<lambda>h. modify
          (\<lambda>s. s\<lparr>PState := h,
            PTranscript := PTranscript s @ [x]\<rparr>)) ::
        (unit, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule lc_program_bind)
      (rule lc_program_hash, rule modify_step)
  have "lc_program (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: 'f protocol_channel.
          hash (TranscriptAbsorb (PState s) x) \<bind>
            (\<lambda>h. modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := PTranscript s @ [x]\<rparr>))))"
    by (rule lc_program_bind[
      OF lc_program_get hash_then_modify])
  then show ?thesis
    unfolding ro_record_staged_message_def
    by simp
qed


lemma lc_program_ro_record_staged_messages:
  "lc_program (length xs) (ro_record_staged_messages xs)"
proof (induction xs)
  case Nil
  then show ?case
    unfolding ro_record_staged_messages_def
    by (simp add: lc_program_return)
next
  case (Cons x xs)
  have "lc_program (1 + length xs)
      (ro_record_staged_message x \<bind>
        (\<lambda>_. ro_record_staged_messages xs))"
    by (rule lc_program_bind)
      (rule lc_program_ro_record_staged_message,
        rule Cons.IH)
  then show ?case
    unfolding ro_record_staged_messages_def by simp
qed

lemma lc_program_receive_counted_tagged_random_field_element:
  assumes bump: "\<And>s. HashMap (bump s) = HashMap s"
  shows "lc_program 1
    (protocol_receive_counted_tagged_random_field_element counter bump tag ::
      ('f, 'f, unit) protocol_c_monad)"
proof -
  have modify_return:
    "lc_program (0 + 0)
      (modify bump \<bind> (\<lambda>_. return r) ::
        ('f, 'f protocol_channel) state_monad)"
    for r :: 'f
    by (rule lc_program_bind)
      (rule lc_program_modify[OF bump],
        rule lc_program_return)
  have hash_tail:
    "lc_program (1 + (0 + 0))
      (hash (tag (counter s) (PState s)) \<bind>
        (\<lambda>r. modify bump \<bind> (\<lambda>_. return r)) ::
        ('f, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule lc_program_bind)
      (rule lc_program_hash, rule modify_return)
  have "lc_program (0 + (1 + (0 + 0)))
      (get \<bind>
        (\<lambda>s :: 'f protocol_channel.
          hash (tag (counter s) (PState s)) \<bind>
            (\<lambda>r. modify bump \<bind> (\<lambda>_. return r))))"
    by (rule lc_program_bind[
      OF lc_program_get hash_tail])
  then show ?thesis
    unfolding protocol_receive_counted_tagged_random_field_element_def
    by simp
qed

lemma lc_program_receive_query_index_challenge:
  "lc_program 1
    (receive_query_index_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_query_index_challenge_def
  by (rule
    lc_program_receive_counted_tagged_random_field_element)
    simp

lemma lc_program_receive_trace_fri_challenge:
  "lc_program 1
    (receive_trace_fri_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_trace_fri_challenge_def
  by (rule
    lc_program_receive_counted_tagged_random_field_element)
    simp

lemma lc_program_receive_composition_fri_challenge:
  "lc_program 1
    (receive_composition_fri_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_composition_fri_challenge_def
  by (rule
    lc_program_receive_counted_tagged_random_field_element)
    simp

lemma lc_program_receive_alpha_challenge:
  "lc_program 1
    (receive_alpha_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_alpha_challenge_def
  by (rule
    lc_program_receive_counted_tagged_random_field_element)
    simp

lemma lc_program_ro_staged_alpha_program:
  "lc_program (2 * n) (ro_staged_alpha_program n)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: lc_program_return)
next
  case (Suc n)
  have challenge:
    "lc_program 1 (receive_alpha_challenge :: ('f, 'f protocol_channel) state_monad)"
    by (rule lc_program_receive_alpha_challenge)
  have record_msg:
    "lc_program 1 (ro_record_staged_message a)" for a
    by (rule lc_program_ro_record_staged_message)
  have tail_return:
    "lc_program (2 * n + 0)
      (ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))" for a
    by (rule lc_program_bind)
      (rule Suc.IH, rule lc_program_return)
  have after_record:
    "lc_program (1 + (2 * n + 0))
      (ro_record_staged_message a \<bind>
        (\<lambda>_. ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))" for a
    by (rule lc_program_bind)
      (rule record_msg, rule tail_return)
  have "lc_program (1 + (1 + (2 * n + 0)))
      (ro_staged_alpha_program (Suc n))"
    unfolding ro_staged_alpha_program.simps
    by (rule lc_program_bind)
      (rule challenge, rule after_record)
  then show ?case by simp
qed


lemma lc_program_ro_staged_trace_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
  shows
    "lc_program
      (sum_list (take n (drop i (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case
    by (simp add: lc_program_return)
next
  case (Suc n)
  have i_bound: "i < length (trace_fri_budgets budgets)"
    using Suc.prems by simp
  have stage:
    "lc_program (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
  proof -
    have stage_controlled:
      "controlled_ro_program (trace_fri_budgets budgets ! i)
        (trace_fri_root_stage A i bs)"
      using controlled i_bound
      unfolding staged_adversary_controlled_def by blast
    show ?thesis
      by (rule controlled_ro_program_lc_program[
        OF stage_controlled])
  qed
  have record_budget:
    "\<And>root. lc_program 1 (ro_record_staged_message root)"
    by (rule lc_program_ro_record_staged_message)
  have challenge:
    "lc_program 1 (receive_trace_fri_challenge :: ('f, 'f protocol_channel) state_monad)"
    by (rule lc_program_receive_trace_fri_challenge)
  have tail:
    "\<And>root b'. lc_program
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b']))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>root b'. lc_program
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
        2 * n + 0)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule lc_program_bind)
      (rule tail,
        simp add: lc_program_return split: prod.splits)
  have after_challenge:
    "\<And>root. lc_program
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          2 * n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b'. ro_staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule lc_program_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. lc_program
      (1 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b'. ro_staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule lc_program_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "lc_program
      (trace_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_trace_fri_program A i (Suc n) bs)"
    unfolding ro_staged_trace_fri_program.simps
    by (rule lc_program_bind)
      (rule stage, rule after_record)
  have budget_eq:
    "trace_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              2 * n + 0))) =
      sum_list (take (Suc n) (drop i (trace_fri_budgets budgets))) +
        2 * Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed


lemma lc_program_ro_staged_composition_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
  shows
    "lc_program
      (sum_list (take n (drop i (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case
    by (simp add: lc_program_return)
next
  case (Suc n)
  have i_bound: "i < length (composition_fri_budgets budgets)"
    using Suc.prems by simp
  have stage:
    "lc_program (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
  proof -
    have stage_controlled:
      "controlled_ro_program (composition_fri_budgets budgets ! i)
        (composition_fri_root_stage A dg i bs)"
      using controlled i_bound
      unfolding staged_adversary_controlled_def by blast
    show ?thesis
      by (rule controlled_ro_program_lc_program[
        OF stage_controlled])
  qed
  have record_budget:
    "\<And>root. lc_program 1 (ro_record_staged_message root)"
    by (rule lc_program_ro_record_staged_message)
  have challenge:
    "lc_program 1 (receive_composition_fri_challenge :: ('f, 'f protocol_channel) state_monad)"
    by (rule lc_program_receive_composition_fri_challenge)
  have tail:
    "\<And>root b'. lc_program
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b']))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>root b'. lc_program
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) +
        2 * n + 0)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b']) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule lc_program_bind)
      (rule tail,
        simp add: lc_program_return split: prod.splits)
  have after_challenge:
    "\<And>root. lc_program
      (1 +
        (sum_list
          (take n (drop (Suc i) (composition_fri_budgets budgets))) +
          2 * n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b'. ro_staged_composition_fri_program A dg (Suc i) n
          (bs @ [b']) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule lc_program_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. lc_program
      (1 +
        (1 +
          (sum_list
            (take n (drop (Suc i) (composition_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_composition_fri_challenge \<bind>
          (\<lambda>b'. ro_staged_composition_fri_program A dg (Suc i) n
            (bs @ [b']) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule lc_program_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "lc_program
      (composition_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_composition_fri_program A dg i (Suc n) bs)"
    unfolding ro_staged_composition_fri_program.simps
    by (rule lc_program_bind)
      (rule stage, rule after_record)
  have budget_eq:
    "composition_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              2 * n + 0))) =
      sum_list (take (Suc n) (drop i (composition_fri_budgets budgets))) +
        2 * Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma lc_program_guarded_ro_staged_composition_fri_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "lc_program
      (sum_list (composition_fri_budgets budgets) +
        2 * ceil_log (maxDegree + 1))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
proof -
  let ?B =
    "sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1)"
  have "lc_program (0 + ?B)
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
      (\<lambda>_. ro_staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) []))"
  proof (rule lc_program_bind_on_outcomes)
    show "lc_program 0
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))"
      by (rule lc_program_assert)
  next
    fix s :: "'f protocol_channel" and x :: unit and t :: "'f protocol_channel"
    assume out:
      "Some (x, t) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1))) s)"
    have round_bound:
      "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
      using out unfolding assert_def
      by (cases "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
        (auto simp: throw_no_outcome)
    have len:
      "0 + ceil_log (to_nat dg + 1) \<le>
        length (composition_fri_budgets budgets)"
      using round_bound wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "lc_program
        (sum_list
          (take (ceil_log (to_nat dg + 1))
            (drop 0 (composition_fri_budgets budgets))) +
          2 * ceil_log (to_nat dg + 1))
        (ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])"
      by (rule
        lc_program_ro_staged_composition_fri_program[
          OF controlled len])
    have le:
      "sum_list
          (take (ceil_log (to_nat dg + 1))
            (drop 0 (composition_fri_budgets budgets))) +
          2 * ceil_log (to_nat dg + 1) \<le>
        sum_list (composition_fri_budgets budgets) +
          2 * ceil_log (maxDegree + 1)"
      using round_bound sum_list_take_le[of "ceil_log (to_nat dg + 1)"
          "composition_fri_budgets budgets"]
      by simp
    show "lc_program ?B
      ((\<lambda>_. ro_staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) []) x)"
      by (rule lc_program_mono[OF le exact])
  qed
  then show ?thesis by simp
qed



lemma lc_program_ro_checked_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
  shows
    "lc_program
      (sum_list (take n (drop i (query_opening_budgets budgets))) +
        n +
        n * verifier_query_round_transcript_length 0 trace_roots
          composition_roots)
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case
    by (simp add: lc_program_return)
next
  case (Suc n)
  let ?L =
    "verifier_query_round_transcript_length 0 trace_roots composition_roots"
  let ?tail =
    "sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
      n + n * ?L"
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems by simp
  have challenge:
    "lc_program 1 receive_query_index_challenge"
    by (rule lc_program_receive_query_index_challenge)
  have stage:
    "\<And>raw. lc_program
      (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
  proof -
    fix raw
    have stage_controlled:
      "controlled_ro_program (query_opening_budgets budgets ! i)
        (query_opening_stage A i raw)"
      using controlled i_bound
      unfolding staged_adversary_controlled_def by blast
    show "lc_program
        (query_opening_budgets budgets ! i)
        (query_opening_stage A i raw)"
      by (rule controlled_ro_program_lc_program[
        OF stage_controlled])
  qed
  have check:
    "\<And>raw chunk. lc_program 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule lc_program_assert)
  have tail:
    "lc_program ?tail
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>chunk. lc_program (?tail + 0)
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule lc_program_bind)
      (rule tail, rule lc_program_return)
  have after_record:
    "\<And>raw chunk. verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk \<Longrightarrow>
      lc_program (?L + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
  proof -
    fix raw chunk
    assume chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    have chunk_len: "length chunk = ?L"
      using verifier_query_round_chunk_length[OF chunk_shape]
        verifier_query_round_transcript_length_index_irrelevant
          [of "index (to_nat raw)" trace_roots composition_roots 0]
      by simp
    have step:
      "lc_program (length chunk + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      by (rule lc_program_bind)
        (rule lc_program_ro_record_staged_messages,
          rule tail_return)
    then show
      "lc_program (?L + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      using chunk_len by simp
  qed
  have after_check:
    "\<And>raw chunk. lc_program (0 + (?L + (?tail + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
  proof (rule lc_program_bind_on_outcomes)
    fix raw chunk
    show "lc_program 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
      by (rule check)
  next
    fix raw chunk
      and s :: "'f protocol_channel"
      and x :: unit
      and t :: "'f protocol_channel"
    assume out:
      "Some (x, t) \<in>
        set_dist
          (execute
            (assert
              (verifier_query_round_chunk (index (to_nat raw))
                trace_roots composition_roots chunk)) s)"
    have chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
      using out unfolding assert_def
      by (cases "verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk")
        (auto simp: throw_no_outcome)
    show "lc_program (?L + (?tail + 0))
      ((\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))) x)"
      by (rule after_record[OF chunk_shape])
  qed
  have after_stage:
    "\<And>raw. lc_program
      (query_opening_budgets budgets ! i +
        (0 + (?L + (?tail + 0))))
      (query_opening_stage A i raw \<bind>
        (\<lambda>chunk. assert
          (verifier_query_round_chunk (index (to_nat raw))
            trace_roots composition_roots chunk) \<bind>
          (\<lambda>_. ro_record_staged_messages chunk \<bind>
            (\<lambda>_. ro_checked_staged_query_program A trace_roots
              composition_roots (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks))))))"
    by (rule lc_program_bind)
      (rule stage, rule after_check)
  have whole:
    "lc_program
      (1 +
        (query_opening_budgets budgets ! i +
          (0 + (?L + (?tail + 0)))))
      (ro_checked_staged_query_program A trace_roots composition_roots
        i (Suc n))"
    unfolding ro_checked_staged_query_program.simps Let_def
    by (rule lc_program_bind)
      (rule challenge, rule after_stage)
  have budget_eq:
    "1 +
        (query_opening_budgets budgets ! i +
          (0 + (?L + (?tail + 0)))) =
      sum_list (take (Suc n) (drop i (query_opening_budgets budgets))) +
        Suc n + Suc n * ?L"
    using sum_list_take_Suc_drop[OF i_bound, of n]
    by (simp add: algebra_simps)
  show ?case
    using whole unfolding budget_eq .
qed

lemma lc_program_ro_checked_staged_query_program_closed:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots \<le> ceil_log (maxDegree + 1)"
  shows
    "lc_program
      (sum_list (take n (drop i (query_opening_budgets budgets))) + n +
        n * ro_checked_query_round_transcript_bound)
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
proof -
  let ?exact =
    "sum_list (take n (drop i (query_opening_budgets budgets))) + n +
      n * verifier_query_round_transcript_length 0 trace_roots composition_roots"
  let ?closed =
    "sum_list (take n (drop i (query_opening_budgets budgets))) + n +
      n * ro_checked_query_round_transcript_bound"
  have exact:
    "lc_program ?exact
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
    by (rule lc_program_ro_checked_staged_query_program[
      OF controlled bound])
  have len_le:
    "verifier_query_round_transcript_length 0 trace_roots composition_roots \<le>
      ro_checked_query_round_transcript_bound"
    by (rule
      verifier_query_round_transcript_length_le_ro_checked_query_round_transcript_bound[
        OF trace_len composition_len])
  have le: "?exact \<le> ?closed"
    using len_le by simp
  show ?thesis
    by (rule lc_program_mono[OF le exact])
qed


lemma lc_program_ro_checked_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "lc_program
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
    "lc_program ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_lc_program)
  have trace_fri_range:
    "lc_program ?trace_fri
      (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len: "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "lc_program
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          2 * ceil_log clength)
        (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule lc_program_ro_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final_range:
    "\<And>bs. lc_program ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_lc_program)
  have alpha_range:
    "lc_program ?alpha (ro_staged_alpha_program (length spec))"
    by (rule lc_program_ro_staged_alpha_program)
  have degree_range:
    "\<And>as. lc_program ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_lc_program)
  have composition_fri_range:
    "\<And>dg. lc_program ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule lc_program_guarded_ro_staged_composition_fri_program
        [OF wf controlled])
  have composition_final_range:
    "\<And>dg bs. lc_program ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_lc_program)
  have query_range:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list).
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      lc_program ?query
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
      "lc_program
        (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
          rounds + rounds * ro_checked_query_round_transcript_bound)
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      by (rule lc_program_ro_checked_staged_query_program_closed
          [OF controlled len trace_len composition_len])
    then show
      "lc_program ?query
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have query_tail:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list) F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      lc_program (?query + 0)
        (ro_checked_staged_query_program A trace_roots composition_roots
          0 rounds \<bind>
          (\<lambda>query_chunks. return (F query_chunks)))"
    by (rule lc_program_bind)
      (rule query_range, assumption, assumption, rule lc_program_return)
  have after_composition_final_record:
    "\<And>(trace_roots :: 'f list) (composition_roots :: 'f list) composition_final F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      lc_program (1 + (?query + 0))
        (ro_record_staged_message composition_final \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots 0 rounds \<bind>
            (\<lambda>query_chunks. return (F query_chunks))))"
    by (rule lc_program_bind)
      (rule lc_program_ro_record_staged_message,
        rule query_tail, assumption, assumption)
  have after_composition_final:
    "\<And>(trace_roots :: 'f list) dg (composition_roots :: 'f list) bs F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      length composition_roots \<le> ceil_log (maxDegree + 1) \<Longrightarrow>
      lc_program (?composition_final + (1 + (?query + 0)))
        (composition_final_stage A dg bs \<bind>
          (\<lambda>composition_final.
            ro_record_staged_message composition_final \<bind>
              (\<lambda>_. ro_checked_staged_query_program A trace_roots
                composition_roots 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return (F composition_final query_chunks)))))"
    by (rule lc_program_bind)
      (rule composition_final_range, rule after_composition_final_record,
        assumption, assumption)
  have after_composition_fri:
    "\<And>(trace_roots :: 'f list) dg F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      lc_program
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
  proof (rule lc_program_bind_on_outcomes)
    fix trace_roots :: "'f list"
    fix dg F
    show "lc_program ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_range)
  next
    fix trace_roots :: "'f list"
    fix dg s x t
    fix F :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list list \<Rightarrow> 'b"
    assume trace_len: "length trace_roots = ceil_log clength"
      and out:
        "Some (x, t) \<in>
          set_dist
            (execute
              (assert (ceil_log (to_nat dg + 1) \<le>
                  ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. ro_staged_composition_fri_program A dg 0
                  (ceil_log (to_nat dg + 1)) [])) s)"
    show "lc_program (?composition_final + (1 + (?query + 0)))
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
      have "lc_program (?composition_final + (1 + (?query + 0)))
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
      lc_program
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
    by (rule lc_program_bind)
      (rule lc_program_ro_record_staged_message,
        rule after_composition_fri, assumption)
  have after_degree:
    "\<And>(trace_roots :: 'f list) as F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      lc_program
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
    by (rule lc_program_bind)
      (rule degree_range, rule after_degree_record, assumption)
  have after_alpha:
    "\<And>(trace_roots :: 'f list) F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      lc_program
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
    by (rule lc_program_bind)
      (rule alpha_range, rule after_degree, assumption)
  have after_trace_final_record:
    "\<And>(trace_roots :: 'f list) trace_final F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      lc_program
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
    by (rule lc_program_bind)
      (rule lc_program_ro_record_staged_message,
        rule after_alpha, assumption)
  have after_trace_final:
    "\<And>(trace_roots :: 'f list) trace_bs F.
      length trace_roots = ceil_log clength \<Longrightarrow>
      lc_program
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
    by (rule lc_program_bind)
      (rule trace_final_range, rule after_trace_final_record, assumption)
  have after_trace_fri:
    "\<And>F. lc_program
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
  proof (rule lc_program_bind_on_outcomes)
    fix F
    show "lc_program ?trace_fri
      (ro_staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_range)
  next
    fix s x t
    fix F :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list list \<Rightarrow> 'b"
    assume out:
      "Some (x, t) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s)"
    show "lc_program
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
      have "lc_program
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
    "\<And>fr F. lc_program
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
    by (rule lc_program_bind)
      (rule lc_program_ro_record_staged_message, rule after_trace_fri)
  have whole:
    "lc_program
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
  proof (rule lc_program_bind)
    show "lc_program ?trace_root (trace_root_stage A)"
      by (rule trace_root_range)
  next
    fix fr
    show "lc_program
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
