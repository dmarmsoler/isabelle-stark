(*  Title:      Stark/Staged_Security_Experiment_RO_Adaptive_State_Relation.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_RO_Adaptive_State_Relation
  imports
    Staged_Security_Experiment_RO_Transcript_Budgets
    Controlled_RO_State_Relation
begin

text \<open>
  A query-count certificate for map-dependent hash relations.  Unlike the
  static relation calculus, the relation may inspect the current oracle map.
  The only probabilistic obligation is therefore discharged at each fresh
  random-oracle query.
\<close>

context soundness
begin

definition adaptive_hash_query_budget
  :: "nat \<Rightarrow> ('r, 'f protocol_channel) state_monad \<Rightarrow> bool"
where
  "adaptive_hash_query_budget q m \<longleftrightarrow>
    (\<forall>R b.
      (\<forall>M x. fmlookup M x = None \<longrightarrow>
        card {y.
          hash_state_relation_transition R M (fmupd x y M)} \<le> b) \<longrightarrow>
      hash_state_relation_budget R b q m)"

lemma hash_state_relation_budget_bind_on_outcomes:
  fixes m :: "('x, 'f protocol_channel) state_monad"
    and k :: "'x \<Rightarrow> ('y, 'f protocol_channel) state_monad"
  assumes m_budget: "hash_state_relation_budget R b q m"
    and k_budget:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_state_relation_budget R b r (k x)"
  shows "hash_state_relation_budget R b (q + r) (m \<bind> k)"
  unfolding hash_state_relation_budget_def
proof (intro allI)
  fix s :: "'f protocol_channel"
  let ?E =
    "hash_state_relation_transition_event R (HashMap s)"
  let ?Tail =
    "\<lambda>out. case out of
      None \<Rightarrow> 0
    | Some (x, t) \<Rightarrow>
        if hash_state_relation_transition R (HashMap s) (HashMap t)
        then 0
        else wp_event (k x)
          (hash_state_relation_transition_event R (HashMap t)) t"
  let ?Bound =
    "\<lambda>out. (if ?E out then 1 else 0) + ?Tail out"
  have split:
    "wp_event (m \<bind> k) ?E s \<le> wp m ?Bound s"
  proof -
    have exact:
      "wp_event (m \<bind> k) ?E s =
        wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s"
      unfolding wp_event_def
        hash_state_relation_transition_event_def
      by (simp add: wpsimps)
    have "wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s
        \<le> wp m ?Bound s"
    proof (rule wp_mono_on_support)
      fix out
      assume support: "out \<in> set_dist (execute m s)"
      show "(case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) \<le>
        ?Bound out"
      proof (cases out)
        case None
        then show ?thesis
          unfolding hash_state_relation_transition_event_def
          by simp
      next
        case (Some xt)
        then obtain x t where xt: "xt = (x, t)"
          by (cases xt) simp
        have step:
          "wp_event (k x) ?E t \<le>
            (if hash_state_relation_transition R
                (HashMap s) (HashMap t)
             then 1
             else wp_event (k x)
                (hash_state_relation_transition_event R (HashMap t)) t)"
          by (rule hash_state_relation_transition_event_step_bound)
        show ?thesis
          using Some xt step
          unfolding hash_state_relation_transition_event_def
          by (cases
              "hash_state_relation_transition R
                (HashMap s) (HashMap t)")
            simp_all
      qed
    qed
    then show ?thesis unfolding exact .
  qed
  have head_bound:
    "wp_event m ?E s \<le> hash_relation_budget_value b q"
    using m_budget
    unfolding hash_state_relation_budget_def
    by blast
  have tail_bound:
    "wp m ?Tail s \<le> hash_relation_budget_value b r"
  proof (rule wp_le_const_on_support)
    fix out
    assume support: "out \<in> set_dist (execute m s)"
    show "?Tail out \<le> hash_relation_budget_value b r"
    proof (cases out)
      case None
      then show ?thesis
        unfolding hash_relation_budget_value_def
        by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) simp
      have tail:
        "wp_event (k x)
            (hash_state_relation_transition_event R (HashMap t)) t \<le>
          hash_relation_budget_value b r"
        using k_budget[OF support[unfolded Some xt]]
        unfolding hash_state_relation_budget_def
        by blast
      show ?thesis using Some xt tail by simp
    qed
  qed
  have "wp_event (m \<bind> k) ?E s \<le> wp m ?Bound s"
    by (rule split)
  also have "... = wp_event m ?E s + wp m ?Tail s"
    unfolding wp_event_def wp_def dist_expect_def
    by (simp add: sum.distrib algebra_simps
        hash_state_relation_transition_event_def)
  also have "... \<le>
      hash_relation_budget_value b q +
        hash_relation_budget_value b r"
    by (intro add_mono head_bound tail_bound)
  also have "... = hash_relation_budget_value b (q + r)"
    by (rule hash_relation_budget_value_add)
  finally show
    "wp_event (m \<bind> k)
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      hash_relation_budget_value b (q + r)" .
qed

lemma hash_state_relation_budget_hash_fresh_adaptive:
  assumes steps:
    "\<And>M x. fmlookup M x = None \<Longrightarrow>
      card {y.
        hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  shows
    "hash_state_relation_budget R b 1
      (hash x :: ('f, 'f protocol_channel) state_monad)"
  unfolding hash_state_relation_budget_def
proof
  fix s :: "'f protocol_channel"
  let ?T =
    "{y. hash_state_relation_transition R (HashMap s)
      (fmupd x y (HashMap s))}"
  have exact:
    "wp_event (hash x)
        (hash_state_relation_transition_event R (HashMap s)) s =
      (if fmlookup (HashMap s) x = None
       then nnreal (card ?T) / nnreal size
       else 0)"
    by (rule wp_hash_state_relation_transition)
  show
    "wp_event (hash x)
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      hash_relation_budget_value b 1"
  proof (cases "fmlookup (HashMap s) x")
    case None
    have card_le: "card ?T \<le> b"
      by (rule steps[OF None])
    have
      "wp_event (hash x)
          (hash_state_relation_transition_event R (HashMap s)) s =
        nnreal (card ?T) / nnreal size"
      using exact None by simp
    also have "... \<le> nnreal b / nnreal size"
      by (rule nnreal_nat_divide_right_mono[OF card_le])
    also have "... = hash_relation_budget_value b 1"
      unfolding hash_relation_budget_value_def by simp
    finally show ?thesis .
  next
    case (Some y)
    show ?thesis
      using exact Some
      unfolding hash_relation_budget_value_def by simp
  qed
qed

lemma adaptive_hash_query_budget_zero:
  assumes preserving: "hash_map_preserving m"
  shows "adaptive_hash_query_budget 0 m"
  unfolding adaptive_hash_query_budget_def
  using hash_state_relation_budget_zero[OF preserving]
  by blast

lemma adaptive_hash_query_budget_hash:
  "adaptive_hash_query_budget 1
    (hash x :: ('f, 'f protocol_channel) state_monad)"
  unfolding adaptive_hash_query_budget_def
  using hash_state_relation_budget_hash_fresh_adaptive
  by blast

lemma adaptive_hash_query_budget_bind:
  assumes m: "adaptive_hash_query_budget q m"
    and k: "\<And>x. adaptive_hash_query_budget r (k x)"
  shows "adaptive_hash_query_budget (q + r) (m \<bind> k)"
  unfolding adaptive_hash_query_budget_def
proof (intro allI impI)
  fix R b
  assume steps:
    "\<forall>M x. fmlookup M x = None \<longrightarrow>
      card {y. hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  have m_budget: "hash_state_relation_budget R b q m"
    using m steps unfolding adaptive_hash_query_budget_def by blast
  have k_budget: "\<And>x. hash_state_relation_budget R b r (k x)"
    using k steps unfolding adaptive_hash_query_budget_def by blast
  show "hash_state_relation_budget R b (q + r) (m \<bind> k)"
    by (rule hash_state_relation_budget_bind[OF m_budget k_budget])
qed

lemma adaptive_hash_query_budget_bind_on_outcomes:
  assumes m: "adaptive_hash_query_budget q m"
    and k:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        adaptive_hash_query_budget r (k x)"
  shows "adaptive_hash_query_budget (q + r) (m \<bind> k)"
  unfolding adaptive_hash_query_budget_def
proof (intro allI impI)
  fix R b
  assume steps:
    "\<forall>M x. fmlookup M x = None \<longrightarrow>
      card {y. hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  have m_budget: "hash_state_relation_budget R b q m"
    using m steps unfolding adaptive_hash_query_budget_def by blast
  have k_budget:
    "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
      hash_state_relation_budget R b r (k x)"
    using k steps unfolding adaptive_hash_query_budget_def by blast
  show "hash_state_relation_budget R b (q + r) (m \<bind> k)"
    by (rule hash_state_relation_budget_bind_on_outcomes[
      OF m_budget k_budget])
qed

lemma adaptive_hash_query_budget_mono:
  assumes qr: "q \<le> r"
    and budget: "adaptive_hash_query_budget q m"
  shows "adaptive_hash_query_budget r m"
  unfolding adaptive_hash_query_budget_def
proof (intro allI impI)
  fix R b
  assume steps:
    "\<forall>M x. fmlookup M x = None \<longrightarrow>
      card {y. hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  have old: "hash_state_relation_budget R b q m"
    using budget steps
    unfolding adaptive_hash_query_budget_def
    by blast
  show "hash_state_relation_budget R b r m"
    by (rule hash_state_relation_budget_mono[OF qr old])
qed

lemma controlled_ro_program_adaptive_hash_query_budget:
  assumes controlled: "controlled_ro_program q m"
  shows "adaptive_hash_query_budget q m"
  unfolding adaptive_hash_query_budget_def
proof (intro allI impI)
  fix R b
  assume steps:
    "\<forall>M x. fmlookup M x = None \<longrightarrow>
      card {y. hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  show "hash_state_relation_budget R b q m"
    using controlled
  proof (induction rule: controlled_ro_program.induct)
    case (Return x)
    show ?case
      by (rule hash_state_relation_budget_zero)
        (rule hash_map_preserving_return)
  next
    case Fail
    show ?case
      by (rule hash_state_relation_budget_zero)
        (rule hash_map_preserving_throw)
  next
    case (Sample d)
    show ?case
      by (rule hash_state_relation_budget_zero)
        (rule hash_map_preserving_state_independent_sample)
  next
    case (Query q k x)
    have tail:
      "\<And>y. hash_state_relation_budget R b q (k y)"
      using Query.IH by blast
    have head:
      "hash_state_relation_budget R b 1
        (hash x :: ('f, 'f protocol_channel) state_monad)"
      by (rule hash_state_relation_budget_hash_fresh_adaptive)
        (use steps in blast)
    have
      "hash_state_relation_budget R b (1 + q)
        ((hash x :: ('f, 'f protocol_channel) state_monad) \<bind> k)"
      by (rule hash_state_relation_budget_bind[OF head tail])
    then show ?case by simp
  next
    case (Bind q m r k)
    show ?case
      by (rule hash_state_relation_budget_bind)
        (use Bind.IH in blast)+
  next
    case (Weaken q m r)
    show ?case
      by (rule hash_state_relation_budget_mono[OF Weaken.hyps(2)])
        (use Weaken.IH in blast)
  qed
qed

lemma adaptive_hash_query_budget_get:
  "adaptive_hash_query_budget 0
    (get :: ('f protocol_channel, 'f protocol_channel) state_monad)"
  by (rule adaptive_hash_query_budget_zero)
    (rule hash_map_preserving_get)

lemma adaptive_hash_query_budget_assert:
  "adaptive_hash_query_budget 0
    (assert x :: (unit, 'f protocol_channel) state_monad)"
  by (rule adaptive_hash_query_budget_zero)
    (rule hash_map_preserving_assert)

lemma adaptive_hash_query_budget_modify:
  assumes "\<And>s. HashMap (f s) = HashMap s"
  shows "adaptive_hash_query_budget 0 (modify f)"
  by (rule adaptive_hash_query_budget_zero)
    (rule hash_map_preserving_modify[OF assms])

lemma adaptive_hash_query_budget_return:
  "adaptive_hash_query_budget 0
    (return x :: ('a, 'f protocol_channel) state_monad)"
  by (rule adaptive_hash_query_budget_zero)
    (rule hash_map_preserving_return)

lemma adaptive_hash_query_budget_ro_record_staged_message:
  "adaptive_hash_query_budget 1 (ro_record_staged_message x)"
proof -
  have modify_step:
    "adaptive_hash_query_budget 0
      (modify
        (\<lambda>s. s\<lparr>PState := h,
          PTranscript := PTranscript s @ [x]\<rparr>) ::
        (unit, 'f protocol_channel) state_monad)"
    for h :: 'f
    by (rule adaptive_hash_query_budget_modify) simp
  have hash_then_modify:
    "adaptive_hash_query_budget (1 + 0)
      (hash (TranscriptAbsorb (PState s) x) \<bind>
        (\<lambda>h. modify
          (\<lambda>s. s\<lparr>PState := h,
            PTranscript := PTranscript s @ [x]\<rparr>)) ::
        (unit, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule adaptive_hash_query_budget_bind)
      (rule adaptive_hash_query_budget_hash, rule modify_step)
  have "adaptive_hash_query_budget (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: 'f protocol_channel.
          hash (TranscriptAbsorb (PState s) x) \<bind>
            (\<lambda>h. modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := PTranscript s @ [x]\<rparr>))))"
    by (rule adaptive_hash_query_budget_bind[
      OF adaptive_hash_query_budget_get hash_then_modify])
  then show ?thesis
    unfolding ro_record_staged_message_def
    by simp
qed

lemma adaptive_hash_query_budget_ro_record_staged_messages:
  "adaptive_hash_query_budget (length xs) (ro_record_staged_messages xs)"
proof (induction xs)
  case Nil
  then show ?case
    unfolding ro_record_staged_messages_def
    by (simp add: adaptive_hash_query_budget_return)
next
  case (Cons x xs)
  have "adaptive_hash_query_budget (1 + length xs)
      (ro_record_staged_message x \<bind>
        (\<lambda>_. ro_record_staged_messages xs))"
    by (rule adaptive_hash_query_budget_bind)
      (rule adaptive_hash_query_budget_ro_record_staged_message,
        rule Cons.IH)
  then show ?case
    unfolding ro_record_staged_messages_def by simp
qed

lemma adaptive_hash_query_budget_receive_counted_tagged_random_field_element:
  assumes bump: "\<And>s. HashMap (bump s) = HashMap s"
  shows "adaptive_hash_query_budget 1
    (protocol_receive_counted_tagged_random_field_element counter bump tag ::
      ('f, 'f, unit) protocol_c_monad)"
proof -
  have modify_return:
    "adaptive_hash_query_budget (0 + 0)
      (modify bump \<bind> (\<lambda>_. return r) ::
        ('f, 'f protocol_channel) state_monad)"
    for r :: 'f
    by (rule adaptive_hash_query_budget_bind)
      (rule adaptive_hash_query_budget_modify[OF bump],
        rule adaptive_hash_query_budget_return)
  have hash_tail:
    "adaptive_hash_query_budget (1 + (0 + 0))
      (hash (tag (counter s) (PState s)) \<bind>
        (\<lambda>r. modify bump \<bind> (\<lambda>_. return r)) ::
        ('f, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule adaptive_hash_query_budget_bind)
      (rule adaptive_hash_query_budget_hash, rule modify_return)
  have "adaptive_hash_query_budget (0 + (1 + (0 + 0)))
      (get \<bind>
        (\<lambda>s :: 'f protocol_channel.
          hash (tag (counter s) (PState s)) \<bind>
            (\<lambda>r. modify bump \<bind> (\<lambda>_. return r))))"
    by (rule adaptive_hash_query_budget_bind[
      OF adaptive_hash_query_budget_get hash_tail])
  then show ?thesis
    unfolding protocol_receive_counted_tagged_random_field_element_def
    by simp
qed

lemma adaptive_hash_query_budget_receive_query_index_challenge:
  "adaptive_hash_query_budget 1
    (receive_query_index_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_query_index_challenge_def
  by (rule
    adaptive_hash_query_budget_receive_counted_tagged_random_field_element)
    simp

lemma adaptive_hash_query_budget_receive_trace_fri_challenge:
  "adaptive_hash_query_budget 1
    (receive_trace_fri_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_trace_fri_challenge_def
  by (rule
    adaptive_hash_query_budget_receive_counted_tagged_random_field_element)
    simp

lemma adaptive_hash_query_budget_receive_composition_fri_challenge:
  "adaptive_hash_query_budget 1
    (receive_composition_fri_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_composition_fri_challenge_def
  by (rule
    adaptive_hash_query_budget_receive_counted_tagged_random_field_element)
    simp

lemma adaptive_hash_query_budget_receive_alpha_challenge:
  "adaptive_hash_query_budget 1
    (receive_alpha_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_alpha_challenge_def
  by (rule
    adaptive_hash_query_budget_receive_counted_tagged_random_field_element)
    simp

lemma adaptive_hash_query_budget_ro_staged_alpha_program:
  "adaptive_hash_query_budget (2 * n) (ro_staged_alpha_program n)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: adaptive_hash_query_budget_return)
next
  case (Suc n)
  have challenge:
    "adaptive_hash_query_budget 1 receive_alpha_challenge"
    by (rule adaptive_hash_query_budget_receive_alpha_challenge)
  have record_msg:
    "adaptive_hash_query_budget 1 (ro_record_staged_message a)" for a
    by (rule adaptive_hash_query_budget_ro_record_staged_message)
  have tail_return:
    "adaptive_hash_query_budget (2 * n + 0)
      (ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))" for a
    by (rule adaptive_hash_query_budget_bind)
      (rule Suc.IH, rule adaptive_hash_query_budget_return)
  have after_record:
    "adaptive_hash_query_budget (1 + (2 * n + 0))
      (ro_record_staged_message a \<bind>
        (\<lambda>_. ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))" for a
    by (rule adaptive_hash_query_budget_bind)
      (rule record_msg, rule tail_return)
  have "adaptive_hash_query_budget (1 + (1 + (2 * n + 0)))
      (ro_staged_alpha_program (Suc n))"
    unfolding ro_staged_alpha_program.simps
    by (rule adaptive_hash_query_budget_bind)
      (rule challenge, rule after_record)
  then show ?case by simp
qed

lemma adaptive_hash_query_budget_of_projection:
  fixes m :: "('x, 'f protocol_channel) state_monad"
    and n :: "('y, 'f protocol_channel) state_monad"
    and project :: "'x \<Rightarrow> 'y"
  assumes projection:
      "m \<bind> (\<lambda>x. return (project x)) = n"
    and budget: "adaptive_hash_query_budget q n"
  shows "adaptive_hash_query_budget q m"
  unfolding adaptive_hash_query_budget_def
proof (intro allI impI)
  fix R b
  assume steps:
    "\<forall>M x. fmlookup M x = None \<longrightarrow>
      card {y. hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  have budget_n: "hash_state_relation_budget R b q n"
    using budget steps
    unfolding adaptive_hash_query_budget_def
    by blast
  show "hash_state_relation_budget R b q m"
    unfolding hash_state_relation_budget_def
  proof
    fix s :: "'f protocol_channel"
    let ?E =
      "hash_state_relation_transition_event R (HashMap s)"
    have event_map:
      "(\<lambda>out. case out of
        None \<Rightarrow> ?E None
      | Some (x, t) \<Rightarrow> ?E (Some (project x, t))) = ?E"
      unfolding hash_state_relation_transition_event_def
      by (rule ext) (auto split: option.splits prod.splits)
    have mapped:
      "wp_event (m \<bind> (\<lambda>x. return (project x))) ?E s =
        wp_event m ?E s"
      by (subst wp_event_bind_return_map)
        (simp only: event_map)
    have "wp_event n ?E s \<le> hash_relation_budget_value b q"
      using budget_n unfolding hash_state_relation_budget_def by blast
    then show "wp_event m ?E s \<le> hash_relation_budget_value b q"
      using mapped unfolding projection by simp
  qed
qed


lemma adaptive_hash_query_budget_ro_staged_trace_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
  shows
    "adaptive_hash_query_budget
      (sum_list (take n (drop i (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case
    by (simp add: adaptive_hash_query_budget_return)
next
  case (Suc n)
  have i_bound: "i < length (trace_fri_budgets budgets)"
    using Suc.prems by simp
  have stage:
    "adaptive_hash_query_budget (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
  proof -
    have stage_controlled:
      "controlled_ro_program (trace_fri_budgets budgets ! i)
        (trace_fri_root_stage A i bs)"
      using controlled i_bound
      unfolding staged_adversary_controlled_def by blast
    show ?thesis
      by (rule controlled_ro_program_adaptive_hash_query_budget[
        OF stage_controlled])
  qed
  have record_budget:
    "\<And>root. adaptive_hash_query_budget 1 (ro_record_staged_message root)"
    by (rule adaptive_hash_query_budget_ro_record_staged_message)
  have challenge:
    "adaptive_hash_query_budget 1 receive_trace_fri_challenge"
    by (rule adaptive_hash_query_budget_receive_trace_fri_challenge)
  have tail:
    "\<And>root b'. adaptive_hash_query_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b']))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>root b'. adaptive_hash_query_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
        2 * n + 0)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule adaptive_hash_query_budget_bind)
      (rule tail,
        simp add: adaptive_hash_query_budget_return split: prod.splits)
  have after_challenge:
    "\<And>root. adaptive_hash_query_budget
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          2 * n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b'. ro_staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule adaptive_hash_query_budget_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. adaptive_hash_query_budget
      (1 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b'. ro_staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule adaptive_hash_query_budget_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "adaptive_hash_query_budget
      (trace_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_trace_fri_program A i (Suc n) bs)"
    unfolding ro_staged_trace_fri_program.simps
    by (rule adaptive_hash_query_budget_bind)
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

lemma adaptive_hash_query_budget_ro_staged_composition_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
  shows
    "adaptive_hash_query_budget
      (sum_list (take n (drop i (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case
    by (simp add: adaptive_hash_query_budget_return)
next
  case (Suc n)
  have i_bound: "i < length (composition_fri_budgets budgets)"
    using Suc.prems by simp
  have stage:
    "adaptive_hash_query_budget (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
  proof -
    have stage_controlled:
      "controlled_ro_program (composition_fri_budgets budgets ! i)
        (composition_fri_root_stage A dg i bs)"
      using controlled i_bound
      unfolding staged_adversary_controlled_def by blast
    show ?thesis
      by (rule controlled_ro_program_adaptive_hash_query_budget[
        OF stage_controlled])
  qed
  have record_budget:
    "\<And>root. adaptive_hash_query_budget 1 (ro_record_staged_message root)"
    by (rule adaptive_hash_query_budget_ro_record_staged_message)
  have challenge:
    "adaptive_hash_query_budget 1 receive_composition_fri_challenge"
    by (rule adaptive_hash_query_budget_receive_composition_fri_challenge)
  have tail:
    "\<And>root b'. adaptive_hash_query_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b']))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>root b'. adaptive_hash_query_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) +
        2 * n + 0)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b']) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule adaptive_hash_query_budget_bind)
      (rule tail,
        simp add: adaptive_hash_query_budget_return split: prod.splits)
  have after_challenge:
    "\<And>root. adaptive_hash_query_budget
      (1 +
        (sum_list
          (take n (drop (Suc i) (composition_fri_budgets budgets))) +
          2 * n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b'. ro_staged_composition_fri_program A dg (Suc i) n
          (bs @ [b']) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule adaptive_hash_query_budget_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. adaptive_hash_query_budget
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
    by (rule adaptive_hash_query_budget_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "adaptive_hash_query_budget
      (composition_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_composition_fri_program A dg i (Suc n) bs)"
    unfolding ro_staged_composition_fri_program.simps
    by (rule adaptive_hash_query_budget_bind)
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

lemma adaptive_hash_query_budget_guarded_ro_staged_composition_fri_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "adaptive_hash_query_budget
      (sum_list (composition_fri_budgets budgets) +
        2 * ceil_log (maxDegree + 1))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
proof -
  let ?B =
    "sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1)"
  have "adaptive_hash_query_budget (0 + ?B)
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
      (\<lambda>_. ro_staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) []))"
  proof (rule adaptive_hash_query_budget_bind_on_outcomes)
    show "adaptive_hash_query_budget 0
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))"
      by (rule adaptive_hash_query_budget_assert)
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
      "adaptive_hash_query_budget
        (sum_list
          (take (ceil_log (to_nat dg + 1))
            (drop 0 (composition_fri_budgets budgets))) +
          2 * ceil_log (to_nat dg + 1))
        (ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])"
      by (rule
        adaptive_hash_query_budget_ro_staged_composition_fri_program[
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
    show "adaptive_hash_query_budget ?B
      ((\<lambda>_. ro_staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) []) x)"
      by (rule adaptive_hash_query_budget_mono[OF le exact])
  qed
  then show ?thesis by simp
qed


lemma adaptive_hash_query_budget_ro_checked_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
  shows
    "adaptive_hash_query_budget
      (sum_list (take n (drop i (query_opening_budgets budgets))) +
        n +
        n * verifier_query_round_transcript_length 0 trace_roots
          composition_roots)
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case
    by (simp add: adaptive_hash_query_budget_return)
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
    "adaptive_hash_query_budget 1 receive_query_index_challenge"
    by (rule adaptive_hash_query_budget_receive_query_index_challenge)
  have stage:
    "\<And>raw. adaptive_hash_query_budget
      (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
  proof -
    fix raw
    have stage_controlled:
      "controlled_ro_program (query_opening_budgets budgets ! i)
        (query_opening_stage A i raw)"
      using controlled i_bound
      unfolding staged_adversary_controlled_def by blast
    show "adaptive_hash_query_budget
        (query_opening_budgets budgets ! i)
        (query_opening_stage A i raw)"
      by (rule controlled_ro_program_adaptive_hash_query_budget[
        OF stage_controlled])
  qed
  have check:
    "\<And>raw chunk. adaptive_hash_query_budget 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule adaptive_hash_query_budget_assert)
  have tail:
    "adaptive_hash_query_budget ?tail
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>chunk. adaptive_hash_query_budget (?tail + 0)
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule adaptive_hash_query_budget_bind)
      (rule tail, rule adaptive_hash_query_budget_return)
  have after_record:
    "\<And>raw chunk. verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk \<Longrightarrow>
      adaptive_hash_query_budget (?L + (?tail + 0))
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
      "adaptive_hash_query_budget (length chunk + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      by (rule adaptive_hash_query_budget_bind)
        (rule adaptive_hash_query_budget_ro_record_staged_messages,
          rule tail_return)
    then show
      "adaptive_hash_query_budget (?L + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      using chunk_len by simp
  qed
  have after_check:
    "\<And>raw chunk. adaptive_hash_query_budget (0 + (?L + (?tail + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
  proof (rule adaptive_hash_query_budget_bind_on_outcomes)
    fix raw chunk
    show "adaptive_hash_query_budget 0
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
    show "adaptive_hash_query_budget (?L + (?tail + 0))
      ((\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))) x)"
      by (rule after_record[OF chunk_shape])
  qed
  have after_stage:
    "\<And>raw. adaptive_hash_query_budget
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
    by (rule adaptive_hash_query_budget_bind)
      (rule stage, rule after_check)
  have whole:
    "adaptive_hash_query_budget
      (1 +
        (query_opening_budgets budgets ! i +
          (0 + (?L + (?tail + 0)))))
      (ro_checked_staged_query_program A trace_roots composition_roots
        i (Suc n))"
    unfolding ro_checked_staged_query_program.simps Let_def
    by (rule adaptive_hash_query_budget_bind)
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

lemma adaptive_hash_query_budget_ro_checked_staged_query_program_closed:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots \<le> ceil_log (maxDegree + 1)"
  shows
    "adaptive_hash_query_budget
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
    "adaptive_hash_query_budget ?exact
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
    by (rule adaptive_hash_query_budget_ro_checked_staged_query_program[
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
    by (rule adaptive_hash_query_budget_mono[OF le exact])
qed


end
end
