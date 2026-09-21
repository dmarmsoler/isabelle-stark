(*  Title:      Stark/Staged_Security_Experiment_Budgets.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Budgets
  imports Staged_Security_Experiment_Core
begin

text \<open>Hash range, collision, relation, and target-budget calculus for staged programs.\<close>

context soundness
begin

lemma record_staged_message_outcome:
  assumes
    "Some ((), t) \<in> set_dist (execute (record_staged_message x) s)"
  shows
    "t = s\<lparr>
      PState := concat (PState s) x,
      PTranscript := PTranscript s @ [x]\<rparr>"
  using assms unfolding record_staged_message_def modify_def
  by (auto elim!: set_dist_bindE)

lemma record_staged_message_simps[simp]:
  "HashMap
      (s\<lparr>PState := concat (PState s) x,
        PTranscript := PTranscript s @ [x]\<rparr>) = HashMap s"
  "PState
      (s\<lparr>PState := concat (PState s) x,
        PTranscript := PTranscript s @ [x]\<rparr>) =
    concat (PState s) x"
  "PTranscript
      (s\<lparr>PState := concat (PState s) x,
        PTranscript := PTranscript s @ [x]\<rparr>) =
    PTranscript s @ [x]"
  "PTraceFriCounter
      (s\<lparr>PState := concat (PState s) x,
        PTranscript := PTranscript s @ [x]\<rparr>) =
    PTraceFriCounter s"
  "PCompositionFriCounter
      (s\<lparr>PState := concat (PState s) x,
        PTranscript := PTranscript s @ [x]\<rparr>) =
    PCompositionFriCounter s"
  "PAlphaCounter
      (s\<lparr>PState := concat (PState s) x,
        PTranscript := PTranscript s @ [x]\<rparr>) =
    PAlphaCounter s"
  "PQueryCounter
      (s\<lparr>PState := concat (PState s) x,
        PTranscript := PTranscript s @ [x]\<rparr>) =
    PQueryCounter s"
  by simp_all

lemma record_staged_message_preserves_hash_map:
  "hash_map_preserving (record_staged_message x)"
  unfolding hash_map_preserving_def record_staged_message_def modify_def
  by (auto elim!: set_dist_bindE)

lemma hash_range_budget_record_staged_message:
  "hash_range_budget 0 (record_staged_message x)"
  unfolding record_staged_message_def
  by (rule hash_range_budget_modify_preserves_hash_map) simp

lemma hash_collision_budget_record_staged_message:
  "hash_collision_budget 0 (record_staged_message x)"
  unfolding record_staged_message_def
  by (rule hash_collision_budget_modify_preserves_hash_map) simp

lemma hash_target_program_record_staged_message:
  "hash_target_program B 0 (record_staged_message x)"
  by (rule hash_map_preserving_imp_hash_target_program_zero)
    (rule record_staged_message_preserves_hash_map)

lemma hash_relation_program_get:
  "hash_relation_program R b 0
    (get :: ('f protocol_channel, 'f protocol_channel) state_monad)"
  by (rule hash_relation_program_zero)
    (rule hash_map_preserving_get)

lemma hash_relation_program_assert:
  "hash_relation_program R b 0
    (assert x :: (unit, 'f protocol_channel) state_monad)"
  by (rule hash_relation_program_zero)
    (rule hash_map_preserving_assert)

lemma hash_relation_program_modify:
  assumes "\<And>s. HashMap (f s) = HashMap s"
  shows "hash_relation_program R b 0 (modify f)"
  by (rule hash_relation_program_zero)
    (rule hash_map_preserving_modify[OF assms])

lemma hash_relation_program_record_staged_message:
  "hash_relation_program R b 0 (record_staged_message x)"
  by (rule hash_relation_program_zero)
    (rule record_staged_message_preserves_hash_map)

lemma record_staged_messages_outcome:
  assumes
    "Some ((), t) \<in>
      set_dist (execute (record_staged_messages xs) s)"
  shows
    "t = s\<lparr>
      PState := foldl concat (PState s) xs,
      PTranscript := PTranscript s @ xs\<rparr>"
  using assms
proof (induction xs arbitrary: s)
  case Nil
  then show ?case
    unfolding record_staged_messages_def by simp
next
  case (Cons x xs)
  from Cons.prems obtain u where
    head:
      "Some ((), u) \<in>
        set_dist (execute (record_staged_message x) s)"
    and tail:
      "Some ((), t) \<in>
        set_dist (execute (record_staged_messages xs) u)"
    unfolding record_staged_messages_def
    by (auto elim!: set_dist_bindE)
  have u:
    "u = s\<lparr>
      PState := concat (PState s) x,
      PTranscript := PTranscript s @ [x]\<rparr>"
    by (rule record_staged_message_outcome[OF head])
  have t:
    "t = u\<lparr>
      PState := foldl concat (PState u) xs,
      PTranscript := PTranscript u @ xs\<rparr>"
    by (rule Cons.IH[OF tail])
  show ?case
    unfolding t u by simp
qed

lemma record_staged_messages_preserves_hash_map:
  "hash_map_preserving (record_staged_messages xs)"
  unfolding hash_map_preserving_def
  using record_staged_messages_outcome by fastforce

lemma hash_range_budget_record_staged_messages:
  "hash_range_budget 0 (record_staged_messages xs)"
  using record_staged_messages_preserves_hash_map
  unfolding hash_map_preserving_def hash_range_budget_def
    hash_map_output_values_def
  by auto

lemma hash_collision_budget_record_staged_messages:
  "hash_collision_budget 0 (record_staged_messages xs)"
  by (rule hash_map_preserving_imp_hash_collision_budget_zero_semantic)
    (rule record_staged_messages_preserves_hash_map)

lemma hash_target_program_record_staged_messages:
  "hash_target_program B 0 (record_staged_messages xs)"
  by (rule hash_map_preserving_imp_hash_target_program_zero)
    (rule record_staged_messages_preserves_hash_map)

lemma hash_relation_program_record_staged_messages:
  "hash_relation_program R b 0 (record_staged_messages xs)"
  by (rule hash_relation_program_zero)
    (rule record_staged_messages_preserves_hash_map)

lemma ro_record_staged_message_outcome:
  assumes
    "Some ((), t) \<in> set_dist (execute (ro_record_staged_message x) s)"
  obtains h u where
    "Some (h, u) \<in>
      set_dist (execute (hash (TranscriptAbsorb (PState s) x)) s)"
    "t = u\<lparr>PState := h, PTranscript := PTranscript u @ [x]\<rparr>"
    "PState u = PState s"
    "PTranscript u = PTranscript s"
    "PTraceFriCounter u = PTraceFriCounter s"
    "PCompositionFriCounter u = PCompositionFriCounter s"
    "PAlphaCounter u = PAlphaCounter s"
    "PQueryCounter u = PQueryCounter s"
    "s \<le> u"
proof -
  from assms obtain h u where hash_out:
      "Some (h, u) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState s) x)) s)"
    and mod_out:
      "Some ((), t) \<in>
        set_dist
          (execute
            (modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := PTranscript s @ [x]\<rparr>)) u)"
    unfolding ro_record_staged_message_def
    by (auto elim!: set_dist_bindE)
  have t_eq:
    "t = u\<lparr>PState := h, PTranscript := PTranscript u @ [x]\<rparr>"
    using mod_out unfolding modify_def
    by (auto elim!: set_dist_bindE)
  have fields:
    "PState u = PState s"
    "PTranscript u = PTranscript s"
    "PTraceFriCounter u = PTraceFriCounter s"
    "PCompositionFriCounter u = PCompositionFriCounter s"
    "PAlphaCounter u = PAlphaCounter s"
    "PQueryCounter u = PQueryCounter s"
    using protocol_hash_channel_preserves[OF hash_out]
    by simp_all
  have ext: "s \<le> u"
    using protocol_merkle.hash_outcome(1)[OF hash_out] .
  show ?thesis
    by (rule that[OF hash_out t_eq fields ext])
qed

lemma hash_range_budget_ro_record_staged_message:
  "hash_range_budget 1 (ro_record_staged_message x)"
proof -
  have get_step:
    "hash_range_budget 0
      (get :: ('f protocol_channel, 'f protocol_channel) state_monad)"
    by (rule hash_range_budget_get)
  have hash_then_modify:
    "hash_range_budget (1 + 0)
      (hash (TranscriptAbsorb (PState s) x) \<bind>
        (\<lambda>h. modify
          (\<lambda>s. s\<lparr>PState := h,
            PTranscript := PTranscript s @ [x]\<rparr>)) ::
        (unit, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash,
       rule hash_range_budget_modify_preserves_hash_map, simp)
  have "hash_range_budget (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: 'f protocol_channel.
          hash (TranscriptAbsorb (PState s) x) \<bind>
            (\<lambda>h. modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := PTranscript s @ [x]\<rparr>))))"
    by (rule hash_range_budget_bind[OF get_step hash_then_modify])
  then show ?thesis
    unfolding ro_record_staged_message_def
    by simp
qed

lemma hash_collision_budget_ro_record_staged_message:
  "hash_collision_budget 1 (ro_record_staged_message x)"
proof -
  have get_range:
    "hash_range_budget 0
      (get :: ('f protocol_channel, 'f protocol_channel) state_monad)"
    by (rule hash_range_budget_get)
  have get_coll:
    "hash_collision_budget 0
      (get :: ('f protocol_channel, 'f protocol_channel) state_monad)"
    by (rule hash_collision_budget_get)
  have hash_then_modify_range:
    "hash_range_budget (1 + 0)
      (hash (TranscriptAbsorb (PState s) x) \<bind>
        (\<lambda>h. modify
          (\<lambda>s. s\<lparr>PState := h,
            PTranscript := PTranscript s @ [x]\<rparr>)) ::
        (unit, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash,
       rule hash_range_budget_modify_preserves_hash_map, simp)
  have hash_then_modify_coll:
    "hash_collision_budget (1 + 0)
      (hash (TranscriptAbsorb (PState s) x) \<bind>
        (\<lambda>h. modify
          (\<lambda>s. s\<lparr>PState := h,
            PTranscript := PTranscript s @ [x]\<rparr>)) ::
        (unit, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_hash, rule hash_collision_budget_hash,
       rule hash_range_budget_modify_preserves_hash_map, simp,
       rule hash_collision_budget_modify_preserves_hash_map, simp)
  have "hash_collision_budget (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: 'f protocol_channel.
          hash (TranscriptAbsorb (PState s) x) \<bind>
            (\<lambda>h. modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := PTranscript s @ [x]\<rparr>))))"
    by (rule hash_collision_budget_bind[OF get_range get_coll
          hash_then_modify_range hash_then_modify_coll])
  then show ?thesis
    unfolding ro_record_staged_message_def
    by simp
qed

lemma hash_target_program_ro_record_staged_message:
  "hash_target_program B 1 (ro_record_staged_message x)"
proof -
  have hash_then_modify:
    "hash_target_program B (1 + 0)
      (hash (TranscriptAbsorb (PState s) x) \<bind>
        (\<lambda>h. modify
          (\<lambda>s. s\<lparr>PState := h,
            PTranscript := PTranscript s @ [x]\<rparr>)) ::
        (unit, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule hash_target_program_bind)
      (rule hash_target_program_hash,
       rule hash_target_program_modify, simp)
  have "hash_target_program B (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: 'f protocol_channel.
          hash (TranscriptAbsorb (PState s) x) \<bind>
            (\<lambda>h. modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := PTranscript s @ [x]\<rparr>))))"
    by (rule hash_target_program_bind[OF hash_target_program_get
          hash_then_modify])
  then show ?thesis
    unfolding ro_record_staged_message_def
    by simp
qed

lemma hash_relation_program_ro_record_staged_message:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b 1 (ro_record_staged_message x)"
proof -
  have modify_step:
    "hash_relation_program R b 0
      (modify
        (\<lambda>s. s\<lparr>PState := h,
          PTranscript := PTranscript s @ [x]\<rparr>) ::
        (unit, 'f protocol_channel) state_monad)"
    for h :: 'f
    by (rule hash_relation_program_modify) simp
  have hash_then_modify:
    "hash_relation_program R b (1 + 0)
      (hash (TranscriptAbsorb (PState s) x) \<bind>
        (\<lambda>h. modify
          (\<lambda>s. s\<lparr>PState := h,
            PTranscript := PTranscript s @ [x]\<rparr>)) ::
        (unit, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_hash[OF fibers], rule modify_step)
  have "hash_relation_program R b (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: 'f protocol_channel.
          hash (TranscriptAbsorb (PState s) x) \<bind>
            (\<lambda>h. modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := PTranscript s @ [x]\<rparr>))))"
    by (rule hash_relation_program_bind[OF hash_relation_program_get
          hash_then_modify])
  then show ?thesis
    unfolding ro_record_staged_message_def
    by simp
qed

lemma hash_range_budget_ro_record_staged_messages:
  "hash_range_budget (length xs) (ro_record_staged_messages xs)"
proof (induction xs)
  case Nil
  then show ?case
    unfolding ro_record_staged_messages_def
    by (simp add: hash_range_budget_return)
next
  case (Cons x xs)
  have "hash_range_budget (1 + length xs)
      (ro_record_staged_message x \<bind>
        (\<lambda>_. ro_record_staged_messages xs))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_record_staged_message, rule Cons.IH)
  then show ?case
    unfolding ro_record_staged_messages_def by simp
qed

lemma hash_collision_budget_ro_record_staged_messages:
  "hash_collision_budget (length xs) (ro_record_staged_messages xs)"
proof (induction xs)
  case Nil
  then show ?case
    unfolding ro_record_staged_messages_def
    by (simp add: hash_collision_budget_return)
next
  case (Cons x xs)
  have range_tail:
    "hash_range_budget (length xs) (ro_record_staged_messages xs)"
    by (rule hash_range_budget_ro_record_staged_messages)
  have "hash_collision_budget (1 + length xs)
      (ro_record_staged_message x \<bind>
        (\<lambda>_. ro_record_staged_messages xs))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_ro_record_staged_message,
       rule hash_collision_budget_ro_record_staged_message,
       rule range_tail,
       rule Cons.IH)
  then show ?case
    unfolding ro_record_staged_messages_def by simp
qed

lemma hash_target_program_ro_record_staged_messages:
  "hash_target_program B (length xs) (ro_record_staged_messages xs)"
proof (induction xs)
  case Nil
  then show ?case
    unfolding ro_record_staged_messages_def
    by (simp add: hash_target_program_return)
next
  case (Cons x xs)
  have "hash_target_program B (1 + length xs)
      (ro_record_staged_message x \<bind>
        (\<lambda>_. ro_record_staged_messages xs))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_record_staged_message, rule Cons.IH)
  then show ?case
    unfolding ro_record_staged_messages_def by simp
qed

lemma hash_relation_program_ro_record_staged_messages:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b (length xs) (ro_record_staged_messages xs)"
proof (induction xs)
  case Nil
  then show ?case
    unfolding ro_record_staged_messages_def
    by (simp add: hash_relation_program_zero hash_map_preserving_return)
next
  case (Cons x xs)
  have "hash_relation_program R b (1 + length xs)
      (ro_record_staged_message x \<bind>
        (\<lambda>_. ro_record_staged_messages xs))"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_ro_record_staged_message[OF fibers],
       rule Cons.IH)
  then show ?case
    unfolding ro_record_staged_messages_def by simp
qed

lemma hash_relation_program_receive_counted_tagged_random_field_element:
  assumes bump: "\<And>s. HashMap (bump s) = HashMap s"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b 1
    (protocol_receive_counted_tagged_random_field_element counter bump tag ::
      ('f, 'f, unit) protocol_c_monad)"
proof -
  have modify_return:
    "hash_relation_program R b (0 + 0)
      (modify bump \<bind> (\<lambda>_. return r) ::
        ('f, 'f protocol_channel) state_monad)"
    for r :: 'f
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_modify[OF bump],
        rule hash_relation_program_zero[OF hash_map_preserving_return])
  have hash_tail:
    "hash_relation_program R b (1 + (0 + 0))
      (hash (tag (counter s) (PState s)) \<bind>
        (\<lambda>r. modify bump \<bind> (\<lambda>_. return r)) ::
        ('f, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_hash[OF fibers], rule modify_return)
  have "hash_relation_program R b (0 + (1 + (0 + 0)))
      (get \<bind>
        (\<lambda>s :: 'f protocol_channel.
          hash (tag (counter s) (PState s)) \<bind>
            (\<lambda>r. modify bump \<bind> (\<lambda>_. return r))))"
    by (rule hash_relation_program_bind
        [OF hash_relation_program_get hash_tail])
  then show ?thesis
    unfolding protocol_receive_counted_tagged_random_field_element_def
    by simp
qed

lemma hash_relation_program_receive_query_index_challenge:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b 1
    (receive_query_index_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_query_index_challenge_def
  by (rule hash_relation_program_receive_counted_tagged_random_field_element)
    (simp_all add: fibers)

lemma hash_relation_program_receive_trace_fri_challenge:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b 1
    (receive_trace_fri_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_trace_fri_challenge_def
  by (rule hash_relation_program_receive_counted_tagged_random_field_element)
    (simp_all add: fibers)

lemma hash_relation_program_receive_composition_fri_challenge:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b 1
    (receive_composition_fri_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_composition_fri_challenge_def
  by (rule hash_relation_program_receive_counted_tagged_random_field_element)
    (simp_all add: fibers)

lemma hash_relation_program_receive_alpha_challenge:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b 1
    (receive_alpha_challenge :: ('f, 'f, unit) protocol_c_monad)"
  unfolding receive_alpha_challenge_def
  by (rule hash_relation_program_receive_counted_tagged_random_field_element)
    (simp_all add: fibers)

lemma controlled_stage_outcome_fields:
  assumes controlled: "controlled_ro_program q m"
    and outcome: "Some (x, t) \<in> set_dist (execute m s)"
  shows
    "PState t = PState s"
    "PTranscript t = PTranscript s"
    "PTraceFriCounter t = PTraceFriCounter s"
    "PCompositionFriCounter t = PCompositionFriCounter s"
    "PAlphaCounter t = PAlphaCounter s"
    "PQueryCounter t = PQueryCounter s"
  using controlled_ro_program_preserves_protocol_fields[OF controlled]
    outcome
  unfolding protocol_fields_preserving_def
  by blast+

lemma sum_list_take_Suc_drop:
  assumes "i < length xs"
  shows "sum_list (take (Suc n) (drop i xs)) =
    xs ! i + sum_list (take n (drop (Suc i) xs))"
proof -
  have drop_i:
    "drop i xs = xs ! i # drop (Suc i) xs"
    using Cons_nth_drop_Suc[OF assms] by simp
  show ?thesis
    unfolding drop_i by simp
qed

lemma sum_list_take_le:
  fixes xs :: "nat list"
  shows "sum_list (take n xs) \<le> sum_list xs"
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (cases xs) simp_all
qed

lemma hash_range_budget_staged_trace_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
  shows
    "hash_range_budget
      (sum_list (take n (drop i (trace_fri_budgets budgets))) + n)
      (staged_trace_fri_program A i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case by (simp add: hash_range_budget_return)
next
  case (Suc n)
  have i_bound: "i < length (trace_fri_budgets budgets)"
    using Suc.prems by simp
  have stage:
    "hash_range_budget (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have record_budget:
    "\<And>root. hash_range_budget 0 (record_staged_message root)"
    by (rule hash_range_budget_record_staged_message)
  have challenge: "hash_range_budget 1 receive_trace_fri_challenge"
    by (rule hash_range_budget_receive_trace_fri_challenge)
  have tail:
    "\<And>b. hash_range_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + n)
      (staged_trace_fri_program A (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>b root. hash_range_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + n + 0)
      (staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_range_budget_bind)
      (rule tail, simp add: hash_range_budget_return split: prod.splits)
  have after_challenge:
    "\<And>root. hash_range_budget
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b. staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_range_budget_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_range_budget
      (0 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            n + 0)))
      (record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b. staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_range_budget_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_range_budget
      (trace_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              n + 0))))
      (staged_trace_fri_program A i (Suc n) bs)"
    unfolding staged_trace_fri_program.simps
    by (rule hash_range_budget_bind)
      (rule stage, rule after_record)
  have budget_eq:
    "trace_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              n + 0))) =
      sum_list (take (Suc n) (drop i (trace_fri_budgets budgets))) + Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_collision_budget_staged_trace_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
  shows
    "hash_collision_budget
      (sum_list (take n (drop i (trace_fri_budgets budgets))) + n)
      (staged_trace_fri_program A i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case by (simp add: hash_collision_budget_return)
next
  case (Suc n)
  have i_bound: "i < length (trace_fri_budgets budgets)"
    using Suc.prems by simp
  have stage_range:
    "hash_range_budget (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have stage_coll:
    "hash_collision_budget (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have record_range:
    "\<And>root. hash_range_budget 0 (record_staged_message root)"
    by (rule hash_range_budget_record_staged_message)
  have record_coll:
    "\<And>root. hash_collision_budget 0 (record_staged_message root)"
    by (rule hash_collision_budget_record_staged_message)
  have challenge_range: "hash_range_budget 1 receive_trace_fri_challenge"
    by (rule hash_range_budget_receive_trace_fri_challenge)
  have challenge_coll: "hash_collision_budget 1 receive_trace_fri_challenge"
    by (rule hash_collision_budget_receive_trace_fri_challenge)
  have tail_range:
    "\<And>b. hash_range_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + n)
      (staged_trace_fri_program A (Suc i) n (bs @ [b]))"
    by (rule hash_range_budget_staged_trace_fri_program[OF controlled])
      (use Suc.prems in simp)
  have tail_coll:
    "\<And>b. hash_collision_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + n)
      (staged_trace_fri_program A (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return_range:
    "\<And>b root. hash_range_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + n + 0)
      (staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_range_budget_bind)
      (rule tail_range, simp add: hash_range_budget_return split: prod.splits)
  have tail_return_coll:
    "\<And>b root. hash_collision_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + n + 0)
      (staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_collision_budget_bind)
      (rule tail_range, rule tail_coll,
        simp add: hash_range_budget_return split: prod.splits,
        simp add: hash_collision_budget_return split: prod.splits)
  have after_challenge_range:
    "\<And>root. hash_range_budget
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b. staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_range_budget_bind)
      (rule challenge_range, rule tail_return_range)
  have after_challenge_coll:
    "\<And>root. hash_collision_budget
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b. staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_collision_budget_bind)
      (rule challenge_range, rule challenge_coll, rule tail_return_range,
        rule tail_return_coll)
  have after_record_range:
    "\<And>root. hash_range_budget
      (0 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            n + 0)))
      (record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b. staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_range_budget_bind)
      (rule record_range, rule after_challenge_range)
  have after_record_coll:
    "\<And>root. hash_collision_budget
      (0 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            n + 0)))
      (record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b. staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_collision_budget_bind)
      (rule record_range, rule record_coll, rule after_challenge_range,
        rule after_challenge_coll)
  have whole:
    "hash_collision_budget
      (trace_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              n + 0))))
      (staged_trace_fri_program A i (Suc n) bs)"
    unfolding staged_trace_fri_program.simps
    by (rule hash_collision_budget_bind)
      (rule stage_range, rule stage_coll, rule after_record_range,
        rule after_record_coll)
  have budget_eq:
    "trace_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              n + 0))) =
      sum_list (take (Suc n) (drop i (trace_fri_budgets budgets))) + Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_range_budget_staged_alpha_program:
  "hash_range_budget n (staged_alpha_program n)"
proof (induction n)
  case 0
  then show ?case by (simp add: hash_range_budget_return)
next
  case (Suc n)
  have challenge: "hash_range_budget 1 receive_alpha_challenge"
    by (rule hash_range_budget_receive_alpha_challenge)
  have record_budget:
    "\<And>a. hash_range_budget 0 (record_staged_message a)"
    by (rule hash_range_budget_record_staged_message)
  have tail_return:
    "\<And>a. hash_range_budget (n + 0)
      (staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))"
    by (rule hash_range_budget_bind)
      (rule Suc.IH, rule hash_range_budget_return)
  have after_record:
    "\<And>a. hash_range_budget (0 + (n + 0))
      (record_staged_message a \<bind>
        (\<lambda>_. staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))"
    by (rule hash_range_budget_bind)
      (rule record_budget, rule tail_return)
  have "hash_range_budget (1 + (0 + (n + 0)))
      (staged_alpha_program (Suc n))"
    unfolding staged_alpha_program.simps
    by (rule hash_range_budget_bind)
      (rule challenge, rule after_record)
  then show ?case by simp
qed

lemma hash_collision_budget_staged_alpha_program:
  "hash_collision_budget n (staged_alpha_program n)"
proof (induction n)
  case 0
  then show ?case by (simp add: hash_collision_budget_return)
next
  case (Suc n)
  have challenge_range: "hash_range_budget 1 receive_alpha_challenge"
    by (rule hash_range_budget_receive_alpha_challenge)
  have challenge_coll: "hash_collision_budget 1 receive_alpha_challenge"
    by (rule hash_collision_budget_receive_alpha_challenge)
  have record_range:
    "\<And>a. hash_range_budget 0 (record_staged_message a)"
    by (rule hash_range_budget_record_staged_message)
  have record_coll:
    "\<And>a. hash_collision_budget 0 (record_staged_message a)"
    by (rule hash_collision_budget_record_staged_message)
  have tail_return_range:
    "\<And>a. hash_range_budget (n + 0)
      (staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_staged_alpha_program,
        rule hash_range_budget_return)
  have tail_return_coll:
    "\<And>a. hash_collision_budget (n + 0)
      (staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_staged_alpha_program, rule Suc.IH,
        rule hash_range_budget_return, rule hash_collision_budget_return)
  have after_record_range:
    "\<And>a. hash_range_budget (0 + (n + 0))
      (record_staged_message a \<bind>
        (\<lambda>_. staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))"
    by (rule hash_range_budget_bind)
      (rule record_range, rule tail_return_range)
  have after_record_coll:
    "\<And>a. hash_collision_budget (0 + (n + 0))
      (record_staged_message a \<bind>
        (\<lambda>_. staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))"
  proof (rule hash_collision_budget_bind)
    fix a
    show "hash_range_budget 0 (record_staged_message a)"
      by (rule record_range)
    show "hash_collision_budget 0 (record_staged_message a)"
      by (rule record_coll)
    show "\<And>x. hash_range_budget (n + 0)
      (staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))"
      by (rule tail_return_range)
    show "\<And>x. hash_collision_budget (n + 0)
      (staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))"
      by (rule tail_return_coll)
  qed
  have "hash_collision_budget (1 + (0 + (n + 0)))
      (staged_alpha_program (Suc n))"
    unfolding staged_alpha_program.simps
    by (rule hash_collision_budget_bind)
      (rule challenge_range, rule challenge_coll, rule after_record_range,
        rule after_record_coll)
  then show ?case by simp
qed

lemma hash_range_budget_staged_composition_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
  shows
    "hash_range_budget
      (sum_list (take n (drop i (composition_fri_budgets budgets))) + n)
      (staged_composition_fri_program A dg i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case by (simp add: hash_range_budget_return)
next
  case (Suc n)
  have i_bound: "i < length (composition_fri_budgets budgets)"
    using Suc.prems by simp
  have stage:
    "hash_range_budget (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have record_budget:
    "\<And>root. hash_range_budget 0 (record_staged_message root)"
    by (rule hash_range_budget_record_staged_message)
  have challenge:
    "hash_range_budget 1 receive_composition_fri_challenge"
    by (rule hash_range_budget_receive_composition_fri_challenge)
  have tail:
    "\<And>b. hash_range_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + n)
      (staged_composition_fri_program A dg (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>b root. hash_range_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + n + 0)
      (staged_composition_fri_program A dg (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_range_budget_bind)
      (rule tail, simp add: hash_range_budget_return split: prod.splits)
  have after_challenge:
    "\<And>root. hash_range_budget
      (1 +
        (sum_list
          (take n (drop (Suc i) (composition_fri_budgets budgets))) +
          n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b. staged_composition_fri_program A dg (Suc i) n
          (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_range_budget_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_range_budget
      (0 +
        (1 +
          (sum_list
            (take n (drop (Suc i) (composition_fri_budgets budgets))) +
            n + 0)))
      (record_staged_message root \<bind>
        (\<lambda>_. receive_composition_fri_challenge \<bind>
          (\<lambda>b. staged_composition_fri_program A dg (Suc i) n
            (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_range_budget_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_range_budget
      (composition_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              n + 0))))
      (staged_composition_fri_program A dg i (Suc n) bs)"
    unfolding staged_composition_fri_program.simps
    by (rule hash_range_budget_bind)
      (rule stage, rule after_record)
  have budget_eq:
    "composition_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              n + 0))) =
      sum_list (take (Suc n) (drop i (composition_fri_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_collision_budget_staged_composition_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
  shows
    "hash_collision_budget
      (sum_list (take n (drop i (composition_fri_budgets budgets))) + n)
      (staged_composition_fri_program A dg i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case by (simp add: hash_collision_budget_return)
next
  case (Suc n)
  have i_bound: "i < length (composition_fri_budgets budgets)"
    using Suc.prems by simp
  have stage_range:
    "hash_range_budget (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have stage_coll:
    "hash_collision_budget (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have record_range:
    "\<And>root. hash_range_budget 0 (record_staged_message root)"
    by (rule hash_range_budget_record_staged_message)
  have record_coll:
    "\<And>root. hash_collision_budget 0 (record_staged_message root)"
    by (rule hash_collision_budget_record_staged_message)
  have challenge_range:
    "hash_range_budget 1 receive_composition_fri_challenge"
    by (rule hash_range_budget_receive_composition_fri_challenge)
  have challenge_coll:
    "hash_collision_budget 1 receive_composition_fri_challenge"
    by (rule hash_collision_budget_receive_composition_fri_challenge)
  have tail_range:
    "\<And>b. hash_range_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + n)
      (staged_composition_fri_program A dg (Suc i) n (bs @ [b]))"
    by (rule hash_range_budget_staged_composition_fri_program
        [OF controlled])
      (use Suc.prems in simp)
  have tail_coll:
    "\<And>b. hash_collision_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + n)
      (staged_composition_fri_program A dg (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return_range:
    "\<And>b root. hash_range_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + n + 0)
      (staged_composition_fri_program A dg (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_range_budget_bind)
      (rule tail_range, simp add: hash_range_budget_return split: prod.splits)
  have tail_return_coll:
    "\<And>b root. hash_collision_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + n + 0)
      (staged_composition_fri_program A dg (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_collision_budget_bind)
      (rule tail_range, rule tail_coll,
        simp add: hash_range_budget_return split: prod.splits,
        simp add: hash_collision_budget_return split: prod.splits)
  have after_challenge_range:
    "\<And>root. hash_range_budget
      (1 +
        (sum_list
          (take n (drop (Suc i) (composition_fri_budgets budgets))) +
          n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b. staged_composition_fri_program A dg (Suc i) n
          (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_range_budget_bind)
      (rule challenge_range, rule tail_return_range)
  have after_challenge_coll:
    "\<And>root. hash_collision_budget
      (1 +
        (sum_list
          (take n (drop (Suc i) (composition_fri_budgets budgets))) +
          n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b. staged_composition_fri_program A dg (Suc i) n
          (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_collision_budget_bind)
      (rule challenge_range, rule challenge_coll, rule tail_return_range,
        rule tail_return_coll)
  have after_record_range:
    "\<And>root. hash_range_budget
      (0 +
        (1 +
          (sum_list
            (take n (drop (Suc i) (composition_fri_budgets budgets))) +
            n + 0)))
      (record_staged_message root \<bind>
        (\<lambda>_. receive_composition_fri_challenge \<bind>
          (\<lambda>b. staged_composition_fri_program A dg (Suc i) n
            (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_range_budget_bind)
      (rule record_range, rule after_challenge_range)
  have after_record_coll:
    "\<And>root. hash_collision_budget
      (0 +
        (1 +
          (sum_list
            (take n (drop (Suc i) (composition_fri_budgets budgets))) +
            n + 0)))
      (record_staged_message root \<bind>
        (\<lambda>_. receive_composition_fri_challenge \<bind>
          (\<lambda>b. staged_composition_fri_program A dg (Suc i) n
            (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_collision_budget_bind)
      (rule record_range, rule record_coll, rule after_challenge_range,
        rule after_challenge_coll)
  have whole:
    "hash_collision_budget
      (composition_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              n + 0))))
      (staged_composition_fri_program A dg i (Suc n) bs)"
    unfolding staged_composition_fri_program.simps
    by (rule hash_collision_budget_bind)
      (rule stage_range, rule stage_coll, rule after_record_range,
        rule after_record_coll)
  have budget_eq:
    "composition_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              n + 0))) =
      sum_list (take (Suc n) (drop i (composition_fri_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_range_budget_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
  shows
    "hash_range_budget
      (sum_list (take n (drop i (query_opening_budgets budgets))) + n)
      (staged_query_program A i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case by (simp add: hash_range_budget_return)
next
  case (Suc n)
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems by simp
  have challenge: "hash_range_budget 1 receive_query_index_challenge"
    by (rule hash_range_budget_receive_query_index_challenge)
  have stage:
    "\<And>raw. hash_range_budget (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have record_budget:
    "\<And>chunk. hash_range_budget 0 (record_staged_messages chunk)"
    by (rule hash_range_budget_record_staged_messages)
  have tail:
    "hash_range_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n)
      (staged_query_program A (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>chunk. hash_range_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n + 0)
      (staged_query_program A (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_range_budget_bind)
      (rule tail, rule hash_range_budget_return)
  have after_record:
    "\<And>chunk. hash_range_budget
      (0 +
        (sum_list
          (take n (drop (Suc i) (query_opening_budgets budgets))) +
          n + 0))
      (record_staged_messages chunk \<bind>
        (\<lambda>_. staged_query_program A (Suc i) n \<bind>
          (\<lambda>chunks. return (chunk # chunks))))"
    by (rule hash_range_budget_bind)
      (rule record_budget, rule tail_return)
  have after_stage:
    "\<And>raw. hash_range_budget
      (query_opening_budgets budgets ! i +
        (0 +
          (sum_list
            (take n (drop (Suc i) (query_opening_budgets budgets))) +
            n + 0)))
      (query_opening_stage A i raw \<bind>
        (\<lambda>chunk. record_staged_messages chunk \<bind>
          (\<lambda>_. staged_query_program A (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
    by (rule hash_range_budget_bind)
      (rule stage, rule after_record)
  have whole:
    "hash_range_budget
      (1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (sum_list
              (take n (drop (Suc i) (query_opening_budgets budgets))) +
              n + 0))))
      (staged_query_program A i (Suc n))"
    unfolding staged_query_program.simps
    by (rule hash_range_budget_bind)
      (rule challenge, rule after_stage)
  have budget_eq:
    "1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (sum_list
              (take n (drop (Suc i) (query_opening_budgets budgets))) +
              n + 0))) =
      sum_list (take (Suc n) (drop i (query_opening_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_collision_budget_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
  shows
    "hash_collision_budget
      (sum_list (take n (drop i (query_opening_budgets budgets))) + n)
      (staged_query_program A i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case by (simp add: hash_collision_budget_return)
next
  case (Suc n)
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems by simp
  have challenge_range: "hash_range_budget 1 receive_query_index_challenge"
    by (rule hash_range_budget_receive_query_index_challenge)
  have challenge_coll: "hash_collision_budget 1 receive_query_index_challenge"
    by (rule hash_collision_budget_receive_query_index_challenge)
  have stage_range:
    "\<And>raw. hash_range_budget (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have stage_coll:
    "\<And>raw. hash_collision_budget (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have record_range:
    "\<And>chunk. hash_range_budget 0 (record_staged_messages chunk)"
    by (rule hash_range_budget_record_staged_messages)
  have record_coll:
    "\<And>chunk. hash_collision_budget 0 (record_staged_messages chunk)"
    by (rule hash_collision_budget_record_staged_messages)
  have tail_range:
    "hash_range_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n)
      (staged_query_program A (Suc i) n)"
    by (rule hash_range_budget_staged_query_program[OF controlled])
      (use Suc.prems in simp)
  have tail_coll:
    "hash_collision_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n)
      (staged_query_program A (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return_range:
    "\<And>chunk. hash_range_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n + 0)
      (staged_query_program A (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_range_budget_bind)
      (rule tail_range, rule hash_range_budget_return)
  have tail_return_coll:
    "\<And>chunk. hash_collision_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n + 0)
      (staged_query_program A (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_collision_budget_bind)
      (rule tail_range, rule tail_coll, rule hash_range_budget_return,
        rule hash_collision_budget_return)
  have after_record_range:
    "\<And>chunk. hash_range_budget
      (0 +
        (sum_list
          (take n (drop (Suc i) (query_opening_budgets budgets))) +
          n + 0))
      (record_staged_messages chunk \<bind>
        (\<lambda>_. staged_query_program A (Suc i) n \<bind>
          (\<lambda>chunks. return (chunk # chunks))))"
    by (rule hash_range_budget_bind)
      (rule record_range, rule tail_return_range)
  have after_record_coll:
    "\<And>chunk. hash_collision_budget
      (0 +
        (sum_list
          (take n (drop (Suc i) (query_opening_budgets budgets))) +
          n + 0))
      (record_staged_messages chunk \<bind>
        (\<lambda>_. staged_query_program A (Suc i) n \<bind>
          (\<lambda>chunks. return (chunk # chunks))))"
    by (rule hash_collision_budget_bind)
      (rule record_range, rule record_coll, rule tail_return_range,
        rule tail_return_coll)
  have after_stage_range:
    "\<And>raw. hash_range_budget
      (query_opening_budgets budgets ! i +
        (0 +
          (sum_list
            (take n (drop (Suc i) (query_opening_budgets budgets))) +
            n + 0)))
      (query_opening_stage A i raw \<bind>
        (\<lambda>chunk. record_staged_messages chunk \<bind>
          (\<lambda>_. staged_query_program A (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
    by (rule hash_range_budget_bind)
      (rule stage_range, rule after_record_range)
  have after_stage_coll:
    "\<And>raw. hash_collision_budget
      (query_opening_budgets budgets ! i +
        (0 +
          (sum_list
            (take n (drop (Suc i) (query_opening_budgets budgets))) +
            n + 0)))
      (query_opening_stage A i raw \<bind>
        (\<lambda>chunk. record_staged_messages chunk \<bind>
          (\<lambda>_. staged_query_program A (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
    by (rule hash_collision_budget_bind)
      (rule stage_range, rule stage_coll, rule after_record_range,
        rule after_record_coll)
  have whole:
    "hash_collision_budget
      (1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (sum_list
              (take n (drop (Suc i) (query_opening_budgets budgets))) +
              n + 0))))
      (staged_query_program A i (Suc n))"
    unfolding staged_query_program.simps
    by (rule hash_collision_budget_bind)
      (rule challenge_range, rule challenge_coll, rule after_stage_range,
        rule after_stage_coll)
  have budget_eq:
    "1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (sum_list
              (take n (drop (Suc i) (query_opening_budgets budgets))) +
              n + 0))) =
      sum_list (take (Suc n) (drop i (query_opening_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_target_program_staged_trace_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
  shows
    "hash_target_program B
      (sum_list (take n (drop i (trace_fri_budgets budgets))) + n)
      (staged_trace_fri_program A i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case by (simp add: hash_target_program_return)
next
  case (Suc n)
  have i_bound: "i < length (trace_fri_budgets budgets)"
    using Suc.prems by simp
  have stage:
    "hash_target_program B (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have record_budget:
    "\<And>root. hash_target_program B 0 (record_staged_message root)"
    by (rule hash_target_program_record_staged_message)
  have challenge: "hash_target_program B 1 receive_trace_fri_challenge"
    by (rule hash_target_program_receive_trace_fri_challenge)
  have tail:
    "\<And>b. hash_target_program B
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + n)
      (staged_trace_fri_program A (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>b root. hash_target_program B
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + n + 0)
      (staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_target_program_bind)
      (rule tail, simp add: hash_target_program_return split: prod.splits)
  have after_challenge:
    "\<And>root. hash_target_program B
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b. staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_target_program_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_target_program B
      (0 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            n + 0)))
      (record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b. staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_target_program_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_target_program B
      (trace_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              n + 0))))
      (staged_trace_fri_program A i (Suc n) bs)"
    unfolding staged_trace_fri_program.simps
    by (rule hash_target_program_bind)
      (rule stage, rule after_record)
  have budget_eq:
    "trace_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              n + 0))) =
      sum_list (take (Suc n) (drop i (trace_fri_budgets budgets))) + Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_target_program_staged_alpha_program:
  "hash_target_program B n (staged_alpha_program n)"
proof (induction n)
  case 0
  then show ?case by (simp add: hash_target_program_return)
next
  case (Suc n)
  have challenge: "hash_target_program B 1 receive_alpha_challenge"
    by (rule hash_target_program_receive_alpha_challenge)
  have record_budget:
    "\<And>a. hash_target_program B 0 (record_staged_message a)"
    by (rule hash_target_program_record_staged_message)
  have tail_return:
    "\<And>a. hash_target_program B (n + 0)
      (staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))"
    by (rule hash_target_program_bind)
      (rule Suc.IH, rule hash_target_program_return)
  have after_record:
    "\<And>a. hash_target_program B (0 + (n + 0))
      (record_staged_message a \<bind>
        (\<lambda>_. staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))"
    by (rule hash_target_program_bind)
      (rule record_budget, rule tail_return)
  have "hash_target_program B (1 + (0 + (n + 0)))
      (staged_alpha_program (Suc n))"
    unfolding staged_alpha_program.simps
    by (rule hash_target_program_bind)
      (rule challenge, rule after_record)
  then show ?case by simp
qed

lemma hash_target_program_staged_composition_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
  shows
    "hash_target_program B
      (sum_list (take n (drop i (composition_fri_budgets budgets))) + n)
      (staged_composition_fri_program A dg i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case by (simp add: hash_target_program_return)
next
  case (Suc n)
  have i_bound: "i < length (composition_fri_budgets budgets)"
    using Suc.prems by simp
  have stage:
    "hash_target_program B (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have record_budget:
    "\<And>root. hash_target_program B 0 (record_staged_message root)"
    by (rule hash_target_program_record_staged_message)
  have challenge:
    "hash_target_program B 1 receive_composition_fri_challenge"
    by (rule hash_target_program_receive_composition_fri_challenge)
  have tail:
    "\<And>b. hash_target_program B
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + n)
      (staged_composition_fri_program A dg (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>b root. hash_target_program B
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + n + 0)
      (staged_composition_fri_program A dg (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_target_program_bind)
      (rule tail, simp add: hash_target_program_return split: prod.splits)
  have after_challenge:
    "\<And>root. hash_target_program B
      (1 +
        (sum_list
          (take n (drop (Suc i) (composition_fri_budgets budgets))) +
          n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b. staged_composition_fri_program A dg (Suc i) n
          (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_target_program_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_target_program B
      (0 +
        (1 +
          (sum_list
            (take n (drop (Suc i) (composition_fri_budgets budgets))) +
            n + 0)))
      (record_staged_message root \<bind>
        (\<lambda>_. receive_composition_fri_challenge \<bind>
          (\<lambda>b. staged_composition_fri_program A dg (Suc i) n
            (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_target_program_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_target_program B
      (composition_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              n + 0))))
      (staged_composition_fri_program A dg i (Suc n) bs)"
    unfolding staged_composition_fri_program.simps
    by (rule hash_target_program_bind)
      (rule stage, rule after_record)
  have budget_eq:
    "composition_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              n + 0))) =
      sum_list (take (Suc n) (drop i (composition_fri_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_target_program_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
  shows
    "hash_target_program B
      (sum_list (take n (drop i (query_opening_budgets budgets))) + n)
      (staged_query_program A i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case by (simp add: hash_target_program_return)
next
  case (Suc n)
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems by simp
  have challenge: "hash_target_program B 1 receive_query_index_challenge"
    by (rule hash_target_program_receive_query_index_challenge)
  have stage:
    "\<And>raw. hash_target_program B (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have record_budget:
    "\<And>chunk. hash_target_program B 0 (record_staged_messages chunk)"
    by (rule hash_target_program_record_staged_messages)
  have tail:
    "hash_target_program B
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n)
      (staged_query_program A (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>chunk. hash_target_program B
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n + 0)
      (staged_query_program A (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_target_program_bind)
      (rule tail, rule hash_target_program_return)
  have after_record:
    "\<And>chunk. hash_target_program B
      (0 +
        (sum_list
          (take n (drop (Suc i) (query_opening_budgets budgets))) +
          n + 0))
      (record_staged_messages chunk \<bind>
        (\<lambda>_. staged_query_program A (Suc i) n \<bind>
          (\<lambda>chunks. return (chunk # chunks))))"
    by (rule hash_target_program_bind)
      (rule record_budget, rule tail_return)
  have after_stage:
    "\<And>raw. hash_target_program B
      (query_opening_budgets budgets ! i +
        (0 +
          (sum_list
            (take n (drop (Suc i) (query_opening_budgets budgets))) +
            n + 0)))
      (query_opening_stage A i raw \<bind>
        (\<lambda>chunk. record_staged_messages chunk \<bind>
          (\<lambda>_. staged_query_program A (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
    by (rule hash_target_program_bind)
      (rule stage, rule after_record)
  have whole:
    "hash_target_program B
      (1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (sum_list
              (take n (drop (Suc i) (query_opening_budgets budgets))) +
              n + 0))))
      (staged_query_program A i (Suc n))"
    unfolding staged_query_program.simps
    by (rule hash_target_program_bind)
      (rule challenge, rule after_stage)
  have budget_eq:
    "1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (sum_list
              (take n (drop (Suc i) (query_opening_budgets budgets))) +
              n + 0))) =
      sum_list (take (Suc n) (drop i (query_opening_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_target_program_checked_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
  shows
    "hash_target_program B
      (sum_list (take n (drop i (query_opening_budgets budgets))) + n)
      (checked_staged_query_program A trace_roots composition_roots i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case by (simp add: hash_target_program_return)
next
  case (Suc n)
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems by simp
  have challenge: "hash_target_program B 1 receive_query_index_challenge"
    by (rule hash_target_program_receive_query_index_challenge)
  have stage:
    "\<And>raw. hash_target_program B (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have check:
    "\<And>raw chunk. hash_target_program B 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule hash_target_program_assert)
  have record_budget:
    "\<And>chunk. hash_target_program B 0 (record_staged_messages chunk)"
    by (rule hash_target_program_record_staged_messages)
  have tail:
    "hash_target_program B
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n)
      (checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>chunk. hash_target_program B
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n + 0)
      (checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_target_program_bind)
      (rule tail, rule hash_target_program_return)
  have after_record:
    "\<And>chunk. hash_target_program B
      (0 +
        (sum_list
          (take n (drop (Suc i) (query_opening_budgets budgets))) +
          n + 0))
      (record_staged_messages chunk \<bind>
        (\<lambda>_. checked_staged_query_program A trace_roots composition_roots
          (Suc i) n \<bind>
          (\<lambda>chunks. return (chunk # chunks))))"
    by (rule hash_target_program_bind)
      (rule record_budget, rule tail_return)
  have after_check:
    "\<And>raw chunk. hash_target_program B
      (0 +
        (0 +
          (sum_list
            (take n (drop (Suc i) (query_opening_budgets budgets))) +
            n + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. record_staged_messages chunk \<bind>
          (\<lambda>_. checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
    by (rule hash_target_program_bind)
      (rule check, rule after_record)
  have after_stage:
    "\<And>raw. hash_target_program B
      (query_opening_budgets budgets ! i +
        (0 +
          (0 +
            (sum_list
              (take n (drop (Suc i) (query_opening_budgets budgets))) +
              n + 0))))
      (query_opening_stage A i raw \<bind>
        (\<lambda>chunk. assert
          (verifier_query_round_chunk (index (to_nat raw))
            trace_roots composition_roots chunk) \<bind>
          (\<lambda>_. record_staged_messages chunk \<bind>
            (\<lambda>_. checked_staged_query_program A trace_roots
              composition_roots (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks))))))"
    by (rule hash_target_program_bind)
      (rule stage, rule after_check)
  have whole:
    "hash_target_program B
      (1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (0 +
              (sum_list
                (take n (drop (Suc i) (query_opening_budgets budgets))) +
                n + 0)))))
      (checked_staged_query_program A trace_roots composition_roots
        i (Suc n))"
    unfolding checked_staged_query_program.simps Let_def
    by (rule hash_target_program_bind)
      (rule challenge, rule after_stage)
  have budget_eq:
    "1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (0 +
              (sum_list
                (take n (drop (Suc i) (query_opening_budgets budgets))) +
                n + 0)))) =
      sum_list (take (Suc n) (drop i (query_opening_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_relation_program_checked_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (sum_list (take n (drop i (query_opening_budgets budgets))) + n)
      (checked_staged_query_program A trace_roots composition_roots i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case
    by (simp add:
        hash_relation_program_zero[OF hash_map_preserving_return])
next
  case (Suc n)
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems by simp
  have challenge:
    "hash_relation_program R b 1 receive_query_index_challenge"
    by (rule hash_relation_program_receive_query_index_challenge[OF fibers])
  have stage:
    "\<And>raw. hash_relation_program R b
      (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
  proof -
    fix raw
    have stage_controlled:
      "controlled_ro_program (query_opening_budgets budgets ! i)
        (query_opening_stage A i raw)"
      using controlled i_bound
      unfolding staged_adversary_controlled_def by blast
    show "hash_relation_program R b
        (query_opening_budgets budgets ! i)
        (query_opening_stage A i raw)"
      by (rule controlled_ro_program_relation
          [OF stage_controlled fibers])
  qed
  have check:
    "\<And>raw chunk. hash_relation_program R b 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule hash_relation_program_assert)
  have record_budget:
    "\<And>chunk. hash_relation_program R b 0
      (record_staged_messages chunk)"
    by (rule hash_relation_program_record_staged_messages)
  have tail:
    "hash_relation_program R b
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n)
      (checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>chunk. hash_relation_program R b
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n + 0)
      (checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_relation_program_bind)
      (rule tail,
        rule hash_relation_program_zero[OF hash_map_preserving_return])
  have after_record:
    "\<And>chunk. hash_relation_program R b
      (0 +
        (sum_list
          (take n (drop (Suc i) (query_opening_budgets budgets))) +
          n + 0))
      (record_staged_messages chunk \<bind>
        (\<lambda>_. checked_staged_query_program A trace_roots composition_roots
          (Suc i) n \<bind>
          (\<lambda>chunks. return (chunk # chunks))))"
    by (rule hash_relation_program_bind)
      (rule record_budget, rule tail_return)
  have after_check:
    "\<And>raw chunk. hash_relation_program R b
      (0 +
        (0 +
          (sum_list
            (take n (drop (Suc i) (query_opening_budgets budgets))) +
            n + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. record_staged_messages chunk \<bind>
          (\<lambda>_. checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
    by (rule hash_relation_program_bind)
      (rule check, rule after_record)
  have after_stage:
    "\<And>raw. hash_relation_program R b
      (query_opening_budgets budgets ! i +
        (0 +
          (0 +
            (sum_list
              (take n (drop (Suc i) (query_opening_budgets budgets))) +
              n + 0))))
      (query_opening_stage A i raw \<bind>
        (\<lambda>chunk. assert
          (verifier_query_round_chunk (index (to_nat raw))
            trace_roots composition_roots chunk) \<bind>
          (\<lambda>_. record_staged_messages chunk \<bind>
            (\<lambda>_. checked_staged_query_program A trace_roots
              composition_roots (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks))))))"
    by (rule hash_relation_program_bind)
      (rule stage, rule after_check)
  have whole:
    "hash_relation_program R b
      (1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (0 +
              (sum_list
                (take n (drop (Suc i) (query_opening_budgets budgets))) +
                n + 0)))))
      (checked_staged_query_program A trace_roots composition_roots
        i (Suc n))"
    unfolding checked_staged_query_program.simps Let_def
    by (rule hash_relation_program_bind)
      (rule challenge, rule after_stage)
  have budget_eq:
    "1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (0 +
              (sum_list
                (take n (drop (Suc i) (query_opening_budgets budgets))) +
                n + 0)))) =
      sum_list (take (Suc n) (drop i (query_opening_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_relation_program_staged_trace_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (sum_list (take n (drop i (trace_fri_budgets budgets))) + n)
      (staged_trace_fri_program A i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case
    by (simp add:
        hash_relation_program_zero[OF hash_map_preserving_return])
next
  case (Suc n)
  have i_bound: "i < length (trace_fri_budgets budgets)"
    using Suc.prems by simp
  have stage:
    "hash_relation_program R b (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
  proof -
    have stage_controlled:
      "controlled_ro_program (trace_fri_budgets budgets ! i)
        (trace_fri_root_stage A i bs)"
      using controlled i_bound
      unfolding staged_adversary_controlled_def by blast
    show ?thesis
      by (rule controlled_ro_program_relation
          [OF stage_controlled fibers])
  qed
  have record_budget:
    "\<And>root. hash_relation_program R b 0 (record_staged_message root)"
    by (rule hash_relation_program_record_staged_message)
  have challenge:
    "hash_relation_program R b 1 receive_trace_fri_challenge"
    by (rule hash_relation_program_receive_trace_fri_challenge[OF fibers])
  have tail:
    "\<And>root b'. hash_relation_program R b
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + n)
      (staged_trace_fri_program A (Suc i) n (bs @ [b']))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>root b'. hash_relation_program R b
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
        n + 0)
      (staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_relation_program_bind)
      (rule tail,
        simp add: hash_relation_program_zero[OF hash_map_preserving_return]
          split: prod.splits)
  have after_challenge:
    "\<And>root. hash_relation_program R b
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b'. staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_relation_program_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_relation_program R b
      (0 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            n + 0)))
      (record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b'. staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_relation_program_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_relation_program R b
      (trace_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              n + 0))))
      (staged_trace_fri_program A i (Suc n) bs)"
    unfolding staged_trace_fri_program.simps
    by (rule hash_relation_program_bind)
      (rule stage, rule after_record)
  have budget_eq:
    "trace_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              n + 0))) =
      sum_list (take (Suc n) (drop i (trace_fri_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_relation_program_staged_alpha_program:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b n (staged_alpha_program n)"
proof (induction n)
  case 0
  then show ?case
    by (simp add:
        hash_relation_program_zero[OF hash_map_preserving_return])
next
  case (Suc n)
  have challenge: "hash_relation_program R b 1 receive_alpha_challenge"
    by (rule hash_relation_program_receive_alpha_challenge[OF fibers])
  have record_budget:
    "\<And>a. hash_relation_program R b 0 (record_staged_message a)"
    by (rule hash_relation_program_record_staged_message)
  have tail_return:
    "\<And>a. hash_relation_program R b (n + 0)
      (staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))"
    by (rule hash_relation_program_bind)
      (rule Suc.IH,
        rule hash_relation_program_zero[OF hash_map_preserving_return])
  have after_record:
    "\<And>a. hash_relation_program R b (0 + (n + 0))
      (record_staged_message a \<bind>
        (\<lambda>_. staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))"
    by (rule hash_relation_program_bind)
      (rule record_budget, rule tail_return)
  have "hash_relation_program R b (1 + (0 + (n + 0)))
      (staged_alpha_program (Suc n))"
    unfolding staged_alpha_program.simps
    by (rule hash_relation_program_bind)
      (rule challenge, rule after_record)
  then show ?case by simp
qed

lemma hash_relation_program_staged_composition_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (sum_list (take n (drop i (composition_fri_budgets budgets))) + n)
      (staged_composition_fri_program A dg i n bs)"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  then show ?case
    by (simp add:
        hash_relation_program_zero[OF hash_map_preserving_return])
next
  case (Suc n)
  have i_bound: "i < length (composition_fri_budgets budgets)"
    using Suc.prems by simp
  have stage:
    "hash_relation_program R b (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
  proof -
    have stage_controlled:
      "controlled_ro_program (composition_fri_budgets budgets ! i)
        (composition_fri_root_stage A dg i bs)"
      using controlled i_bound
      unfolding staged_adversary_controlled_def by blast
    show ?thesis
      by (rule controlled_ro_program_relation
          [OF stage_controlled fibers])
  qed
  have record_budget:
    "\<And>root. hash_relation_program R b 0 (record_staged_message root)"
    by (rule hash_relation_program_record_staged_message)
  have challenge:
    "hash_relation_program R b 1 receive_composition_fri_challenge"
    by (rule
        hash_relation_program_receive_composition_fri_challenge[OF fibers])
  have tail:
    "\<And>root b'. hash_relation_program R b
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + n)
      (staged_composition_fri_program A dg (Suc i) n (bs @ [b']))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>root b'. hash_relation_program R b
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + n + 0)
      (staged_composition_fri_program A dg (Suc i) n (bs @ [b']) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_relation_program_bind)
      (rule tail,
        simp add: hash_relation_program_zero[OF hash_map_preserving_return]
          split: prod.splits)
  have after_challenge:
    "\<And>root. hash_relation_program R b
      (1 +
        (sum_list
          (take n (drop (Suc i) (composition_fri_budgets budgets))) +
          n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b'. staged_composition_fri_program A dg (Suc i) n
          (bs @ [b']) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_relation_program_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_relation_program R b
      (0 +
        (1 +
          (sum_list
            (take n (drop (Suc i) (composition_fri_budgets budgets))) +
            n + 0)))
      (record_staged_message root \<bind>
        (\<lambda>_. receive_composition_fri_challenge \<bind>
          (\<lambda>b'. staged_composition_fri_program A dg (Suc i) n
            (bs @ [b']) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_relation_program_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_relation_program R b
      (composition_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              n + 0))))
      (staged_composition_fri_program A dg i (Suc n) bs)"
    unfolding staged_composition_fri_program.simps
    by (rule hash_relation_program_bind)
      (rule stage, rule after_record)
  have budget_eq:
    "composition_fri_budgets budgets ! i +
        (0 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              n + 0))) =
      sum_list (take (Suc n) (drop i (composition_fri_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_relation_program_guarded_staged_composition_fri_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (sum_list (composition_fri_budgets budgets) +
        ceil_log (maxDegree + 1))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
proof -
  let ?B =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  have "hash_relation_program R b (0 + ?B)
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
      (\<lambda>_. staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) []))"
  proof (rule hash_relation_program_bind_on_outcomes
      [where q=0 and r="?B"])
    show "hash_relation_program R b 0
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))"
      by (rule hash_relation_program_assert)
  next
    fix s x t
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
      "hash_relation_program R b
        (sum_list
          (take (ceil_log (to_nat dg + 1))
            (drop 0 (composition_fri_budgets budgets))) +
          ceil_log (to_nat dg + 1))
        (staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])"
      by (rule hash_relation_program_staged_composition_fri_program
          [OF controlled len fibers])
    have le:
      "sum_list
          (take (ceil_log (to_nat dg + 1))
            (drop 0 (composition_fri_budgets budgets))) +
          ceil_log (to_nat dg + 1) \<le>
        sum_list (composition_fri_budgets budgets) +
          ceil_log (maxDegree + 1)"
      using round_bound sum_list_take_le[of "ceil_log (to_nat dg + 1)"
          "composition_fri_budgets budgets"]
      by simp
    show "hash_relation_program R b ?B
      (staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) [])"
      by (rule hash_relation_program_mono[OF le exact])
  qed
  then show ?thesis by simp
qed

lemma hash_relation_program_staged_alpha_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (staged_alpha_search_queries budgets 0)
      (staged_alpha_prefix_program A)"
proof -
  let ?trace_root = "trace_root_budget budgets"
  let ?trace_fri =
    "sum_list (trace_fri_budgets budgets) + ceil_log clength"
  let ?trace_final = "trace_final_budget budgets"
  have trace_root:
    "hash_relation_program R b ?trace_root (trace_root_stage A)"
  proof -
    have controlled_root:
      "controlled_ro_program ?trace_root (trace_root_stage A)"
      using controlled unfolding staged_adversary_controlled_def by blast
    show ?thesis
      by (rule controlled_ro_program_relation
          [OF controlled_root fibers])
  qed
  have record_root:
    "\<And>fr. hash_relation_program R b 0 (record_staged_message fr)"
    by (rule hash_relation_program_record_staged_message)
  have trace_fri:
    "hash_relation_program R b ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_relation_program R b
        (sum_list
          (take (ceil_log clength) (drop 0 (trace_fri_budgets budgets))) +
          ceil_log clength)
        (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_relation_program_staged_trace_fri_program
          [OF controlled len fibers])
    have le:
      "sum_list
          (take (ceil_log clength) (drop 0 (trace_fri_budgets budgets))) +
          ceil_log clength \<le>
        sum_list (trace_fri_budgets budgets) + ceil_log clength"
      using sum_list_take_le[of "ceil_log clength"
          "trace_fri_budgets budgets"]
      by simp
    show ?thesis
      by (rule hash_relation_program_mono[OF le exact])
  qed
  have trace_final:
    "\<And>trace_roots trace_bs. hash_relation_program R b ?trace_final
      (trace_final_stage A trace_bs)"
  proof -
    fix trace_roots trace_bs
    have controlled_final:
      "controlled_ro_program ?trace_final
        (trace_final_stage A trace_bs)"
      using controlled unfolding staged_adversary_controlled_def by blast
    show "hash_relation_program R b ?trace_final
      (trace_final_stage A trace_bs)"
      by (rule controlled_ro_program_relation
          [OF controlled_final fibers])
  qed
  have record_final:
    "\<And>trace_final. hash_relation_program R b 0
      (record_staged_message trace_final)"
    by (rule hash_relation_program_record_staged_message)
  have after_final_record:
    "\<And>fr trace_roots trace_bs trace_final.
      hash_relation_program R b 0
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
  proof -
    fix fr trace_roots trace_bs trace_final
    have "hash_relation_program R b (0 + 0)
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
      by (rule hash_relation_program_bind)
        (rule record_final,
          rule hash_relation_program_zero[OF hash_map_preserving_return])
    then show "hash_relation_program R b 0
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
      by simp
  qed
  have after_final:
    "\<And>fr trace_roots trace_bs. hash_relation_program R b
      (?trace_final + 0)
      (trace_final_stage A trace_bs \<bind>
        (\<lambda>trace_final. record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
    by (rule hash_relation_program_bind)
      (rule trace_final, rule after_final_record)
  have after_trace_fri:
    "\<And>fr. hash_relation_program R b
      (?trace_fri + (?trace_final + 0))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final. record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))))"
  proof -
    fix fr
    have cont:
      "\<And>x. hash_relation_program R b (?trace_final + 0)
        (case x of (trace_roots, trace_bs) \<Rightarrow>
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final. record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
    proof -
      fix x
      show "hash_relation_program R b (?trace_final + 0)
        (case x of (trace_roots, trace_bs) \<Rightarrow>
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final. record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
      proof (cases x)
        case (Pair trace_roots trace_bs)
        have step:
          "hash_relation_program R b (?trace_final + 0)
            (trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final. record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
          by (rule after_final)
        show ?thesis
          unfolding Pair using step by simp
      qed
    qed
    have "hash_relation_program R b (?trace_fri + (?trace_final + 0))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final. record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))))"
      by (rule hash_relation_program_bind)
        (rule trace_fri, rule cont)
    then show "hash_relation_program R b
      (?trace_fri + (?trace_final + 0))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final. record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))))" .
  qed
  have after_root_record:
    "\<And>fr. hash_relation_program R b
      (0 + (?trace_fri + (?trace_final + 0)))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final. record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))))"
    by (rule hash_relation_program_bind)
      (rule record_root, rule after_trace_fri)
  have whole:
    "hash_relation_program R b
      (?trace_root + (0 + (?trace_fri + (?trace_final + 0))))
      (staged_alpha_prefix_program A)"
    unfolding staged_alpha_prefix_program_def
    by (rule hash_relation_program_bind)
      (rule trace_root, rule after_root_record)
  show ?thesis
    using whole
    unfolding staged_alpha_search_queries_def
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_range_budget_staged_alpha_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (staged_alpha_search_queries budgets 0)
      (staged_alpha_prefix_program A)"
proof -
  let ?trace_root = "trace_root_budget budgets"
  let ?trace_fri =
    "sum_list (trace_fri_budgets budgets) + ceil_log clength"
  let ?trace_final = "trace_final_budget budgets"
  have trace_root:
    "hash_range_budget ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have trace_fri:
    "hash_range_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_range_budget
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          ceil_log clength)
        (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_range_budget_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final:
    "\<And>bs. hash_range_budget ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have after_trace_final_record:
    "\<And>fr trace_roots trace_bs trace_final.
      hash_range_budget 0
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
  proof -
    fix fr trace_roots trace_bs trace_final
    have "hash_range_budget (0 + 0)
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
      by (rule hash_range_budget_bind)
        (rule hash_range_budget_record_staged_message,
          rule hash_range_budget_return)
    then show
      "hash_range_budget 0
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
      by simp
  qed
  have after_trace_final:
    "\<And>fr trace_roots trace_bs.
      hash_range_budget (?trace_final + 0)
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final.
            record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
    by (rule hash_range_budget_bind)
      (rule trace_final, rule after_trace_final_record)
  have after_trace_fri:
    "\<And>fr. hash_range_budget (?trace_fri + (?trace_final + 0))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final.
              record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))))"
  proof (rule hash_range_budget_bind)
    fix fr
    show "hash_range_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri)
  next
    fix fr x
    show "hash_range_budget (?trace_final + 0)
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final.
            record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have step:
        "hash_range_budget (?trace_final + 0)
          (trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final.
              record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
        by (rule after_trace_final)
      show ?thesis
        unfolding Pair using step by simp
    qed
  qed
  have after_trace_root_record:
    "\<And>fr. hash_range_budget (0 + (?trace_fri + (?trace_final + 0)))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                record_staged_message trace_final \<bind>
                  (\<lambda>_. return
                    (fr, trace_roots, trace_bs, trace_final))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message, rule after_trace_fri)
  have whole:
    "hash_range_budget
      (?trace_root + (0 + (?trace_fri + (?trace_final + 0))))
      (staged_alpha_prefix_program A)"
    unfolding staged_alpha_prefix_program_def
    by (rule hash_range_budget_bind)
      (rule trace_root, rule after_trace_root_record)
  show ?thesis
    using whole
    unfolding staged_alpha_search_queries_def
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_collision_budget_staged_alpha_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (staged_alpha_search_queries budgets 0)
      (staged_alpha_prefix_program A)"
proof -
  let ?trace_root = "trace_root_budget budgets"
  let ?trace_fri =
    "sum_list (trace_fri_budgets budgets) + ceil_log clength"
  let ?trace_final = "trace_final_budget budgets"
  have trace_root_range:
    "hash_range_budget ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have trace_root_coll:
    "hash_collision_budget ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have trace_fri_range':
    "hash_range_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_range_budget
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          ceil_log clength)
        (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_range_budget_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_fri_coll:
    "hash_collision_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_collision_budget
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          ceil_log clength)
        (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_collision_budget_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final_range:
    "\<And>bs. hash_range_budget ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have trace_final_coll:
    "\<And>bs. hash_collision_budget ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have after_trace_final_record_range:
    "\<And>fr trace_roots trace_bs trace_final.
      hash_range_budget 0
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
  proof -
    fix fr trace_roots trace_bs trace_final
    have "hash_range_budget (0 + 0)
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
      by (rule hash_range_budget_bind)
        (rule hash_range_budget_record_staged_message,
          rule hash_range_budget_return)
    then show "hash_range_budget 0
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
      by simp
  qed
  have after_trace_final_record_coll:
    "\<And>fr trace_roots trace_bs trace_final.
      hash_collision_budget 0
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
  proof -
    fix fr trace_roots trace_bs trace_final
    have "hash_collision_budget (0 + 0)
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
      by (rule hash_collision_budget_bind)
        (rule hash_range_budget_record_staged_message,
          rule hash_collision_budget_record_staged_message,
          rule hash_range_budget_return, rule hash_collision_budget_return)
    then show "hash_collision_budget 0
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
      by simp
  qed
  have after_trace_final_range:
    "\<And>fr trace_roots trace_bs.
      hash_range_budget (?trace_final + 0)
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final.
            record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
    by (rule hash_range_budget_bind)
      (rule trace_final_range, rule after_trace_final_record_range)
  have after_trace_final_coll:
    "\<And>fr trace_roots trace_bs.
      hash_collision_budget (?trace_final + 0)
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final.
            record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
    by (rule hash_collision_budget_bind)
      (rule trace_final_range, rule trace_final_coll,
        rule after_trace_final_record_range,
        rule after_trace_final_record_coll)
  have after_trace_fri_range:
    "\<And>fr. hash_range_budget (?trace_fri + (?trace_final + 0))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final.
              record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))))"
  proof (rule hash_range_budget_bind)
    fix fr
    show "hash_range_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_range')
  next
    fix fr x
    show "hash_range_budget (?trace_final + 0)
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final.
            record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have step:
        "hash_range_budget (?trace_final + 0)
          (trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final.
              record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
        by (rule after_trace_final_range)
      show ?thesis
        unfolding Pair using step by simp
    qed
  qed
  have after_trace_fri_coll:
    "\<And>fr. hash_collision_budget (?trace_fri + (?trace_final + 0))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final.
              record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))))"
  proof (rule hash_collision_budget_bind)
    fix fr
    show "hash_range_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_range')
    show "hash_collision_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_coll)
  next
    fix fr x
    show "hash_range_budget (?trace_final + 0)
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final.
            record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have step:
        "hash_range_budget (?trace_final + 0)
          (trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final.
              record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
        by (rule after_trace_final_range)
      show ?thesis
        unfolding Pair using step by simp
    qed
    show "hash_collision_budget (?trace_final + 0)
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final.
            record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have step:
        "hash_collision_budget (?trace_final + 0)
          (trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final.
              record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
        by (rule after_trace_final_coll)
      show ?thesis
        unfolding Pair using step by simp
    qed
  qed
  have after_trace_root_record_range:
    "\<And>fr. hash_range_budget (0 + (?trace_fri + (?trace_final + 0)))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                record_staged_message trace_final \<bind>
                  (\<lambda>_. return
                    (fr, trace_roots, trace_bs, trace_final))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule after_trace_fri_range)
  have after_trace_root_record_coll:
    "\<And>fr. hash_collision_budget
      (0 + (?trace_fri + (?trace_final + 0)))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                record_staged_message trace_final \<bind>
                  (\<lambda>_. return
                    (fr, trace_roots, trace_bs, trace_final))))))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule hash_collision_budget_record_staged_message,
        rule after_trace_fri_range, rule after_trace_fri_coll)
  have whole:
    "hash_collision_budget
      (?trace_root + (0 + (?trace_fri + (?trace_final + 0))))
      (staged_alpha_prefix_program A)"
    unfolding staged_alpha_prefix_program_def
    by (rule hash_collision_budget_bind)
      (rule trace_root_range, rule trace_root_coll,
        rule after_trace_root_record_range,
        rule after_trace_root_record_coll)
  show ?thesis
    using whole
    unfolding staged_alpha_search_queries_def
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_range_budget_checked_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
  shows
    "hash_range_budget
      (sum_list (take n (drop i (query_opening_budgets budgets))) + n)
      (checked_staged_query_program A trace_roots composition_roots i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case by (simp add: hash_range_budget_return)
next
  case (Suc n)
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems by simp
  have challenge: "hash_range_budget 1 receive_query_index_challenge"
    by (rule hash_range_budget_receive_query_index_challenge)
  have stage:
    "\<And>raw. hash_range_budget (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have check:
    "\<And>raw chunk. hash_range_budget 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule hash_range_budget_assert)
  have record_budget:
    "\<And>chunk. hash_range_budget 0 (record_staged_messages chunk)"
    by (rule hash_range_budget_record_staged_messages)
  have tail:
    "hash_range_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n)
      (checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>chunk. hash_range_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n + 0)
      (checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_range_budget_bind)
      (rule tail, rule hash_range_budget_return)
  have after_record:
    "\<And>chunk. hash_range_budget
      (0 +
        (sum_list
          (take n (drop (Suc i) (query_opening_budgets budgets))) +
          n + 0))
      (record_staged_messages chunk \<bind>
        (\<lambda>_. checked_staged_query_program A trace_roots composition_roots
          (Suc i) n \<bind>
          (\<lambda>chunks. return (chunk # chunks))))"
    by (rule hash_range_budget_bind)
      (rule record_budget, rule tail_return)
  have after_check:
    "\<And>raw chunk. hash_range_budget
      (0 +
        (0 +
          (sum_list
            (take n (drop (Suc i) (query_opening_budgets budgets))) +
            n + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. record_staged_messages chunk \<bind>
          (\<lambda>_. checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
    by (rule hash_range_budget_bind)
      (rule check, rule after_record)
  have after_stage:
    "\<And>raw. hash_range_budget
      (query_opening_budgets budgets ! i +
        (0 +
          (0 +
            (sum_list
              (take n (drop (Suc i) (query_opening_budgets budgets))) +
              n + 0))))
      (query_opening_stage A i raw \<bind>
        (\<lambda>chunk. assert
          (verifier_query_round_chunk (index (to_nat raw))
            trace_roots composition_roots chunk) \<bind>
          (\<lambda>_. record_staged_messages chunk \<bind>
            (\<lambda>_. checked_staged_query_program A trace_roots
              composition_roots (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks))))))"
    by (rule hash_range_budget_bind)
      (rule stage, rule after_check)
  have whole:
    "hash_range_budget
      (1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (0 +
              (sum_list
                (take n (drop (Suc i) (query_opening_budgets budgets))) +
                n + 0)))))
      (checked_staged_query_program A trace_roots composition_roots
        i (Suc n))"
    unfolding checked_staged_query_program.simps Let_def
    by (rule hash_range_budget_bind)
      (rule challenge, rule after_stage)
  have budget_eq:
    "1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (0 +
              (sum_list
                (take n (drop (Suc i) (query_opening_budgets budgets))) +
                n + 0)))) =
      sum_list (take (Suc n) (drop i (query_opening_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_collision_budget_checked_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
  shows
    "hash_collision_budget
      (sum_list (take n (drop i (query_opening_budgets budgets))) + n)
      (checked_staged_query_program A trace_roots composition_roots i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case by (simp add: hash_collision_budget_return)
next
  case (Suc n)
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems by simp
  have challenge_range: "hash_range_budget 1 receive_query_index_challenge"
    by (rule hash_range_budget_receive_query_index_challenge)
  have challenge_coll: "hash_collision_budget 1 receive_query_index_challenge"
    by (rule hash_collision_budget_receive_query_index_challenge)
  have stage_range:
    "\<And>raw. hash_range_budget (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have stage_coll:
    "\<And>raw. hash_collision_budget (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have check_range:
    "\<And>raw chunk. hash_range_budget 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule hash_range_budget_assert)
  have check_coll:
    "\<And>raw chunk. hash_collision_budget 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule hash_collision_budget_assert)
  have record_range:
    "\<And>chunk. hash_range_budget 0 (record_staged_messages chunk)"
    by (rule hash_range_budget_record_staged_messages)
  have record_coll:
    "\<And>chunk. hash_collision_budget 0 (record_staged_messages chunk)"
    by (rule hash_collision_budget_record_staged_messages)
  have tail_range:
    "hash_range_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n)
      (checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule hash_range_budget_checked_staged_query_program[OF controlled])
      (use Suc.prems in simp)
  have tail_coll:
    "hash_collision_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n)
      (checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return_range:
    "\<And>chunk. hash_range_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n + 0)
      (checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_range_budget_bind)
      (rule tail_range, rule hash_range_budget_return)
  have tail_return_coll:
    "\<And>chunk. hash_collision_budget
      (sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
        n + 0)
      (checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_collision_budget_bind)
      (rule tail_range, rule tail_coll, rule hash_range_budget_return,
        rule hash_collision_budget_return)
  have after_record_range:
    "\<And>chunk. hash_range_budget
      (0 +
        (sum_list
          (take n (drop (Suc i) (query_opening_budgets budgets))) +
          n + 0))
      (record_staged_messages chunk \<bind>
        (\<lambda>_. checked_staged_query_program A trace_roots composition_roots
          (Suc i) n \<bind>
          (\<lambda>chunks. return (chunk # chunks))))"
    by (rule hash_range_budget_bind)
      (rule record_range, rule tail_return_range)
  have after_record_coll:
    "\<And>chunk. hash_collision_budget
      (0 +
        (sum_list
          (take n (drop (Suc i) (query_opening_budgets budgets))) +
          n + 0))
      (record_staged_messages chunk \<bind>
        (\<lambda>_. checked_staged_query_program A trace_roots composition_roots
          (Suc i) n \<bind>
          (\<lambda>chunks. return (chunk # chunks))))"
    by (rule hash_collision_budget_bind)
      (rule record_range, rule record_coll, rule tail_return_range,
        rule tail_return_coll)
  have after_check_range:
    "\<And>raw chunk. hash_range_budget
      (0 +
        (0 +
          (sum_list
            (take n (drop (Suc i) (query_opening_budgets budgets))) +
            n + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. record_staged_messages chunk \<bind>
          (\<lambda>_. checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
    by (rule hash_range_budget_bind)
      (rule check_range, rule after_record_range)
  have after_check_coll:
    "\<And>raw chunk. hash_collision_budget
      (0 +
        (0 +
          (sum_list
            (take n (drop (Suc i) (query_opening_budgets budgets))) +
            n + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. record_staged_messages chunk \<bind>
          (\<lambda>_. checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
    by (rule hash_collision_budget_bind)
      (rule check_range, rule check_coll, rule after_record_range,
        rule after_record_coll)
  have after_stage_range:
    "\<And>raw. hash_range_budget
      (query_opening_budgets budgets ! i +
        (0 +
          (0 +
            (sum_list
              (take n (drop (Suc i) (query_opening_budgets budgets))) +
              n + 0))))
      (query_opening_stage A i raw \<bind>
        (\<lambda>chunk. assert
          (verifier_query_round_chunk (index (to_nat raw))
            trace_roots composition_roots chunk) \<bind>
          (\<lambda>_. record_staged_messages chunk \<bind>
            (\<lambda>_. checked_staged_query_program A trace_roots
              composition_roots (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks))))))"
    by (rule hash_range_budget_bind)
      (rule stage_range, rule after_check_range)
  have after_stage_coll:
    "\<And>raw. hash_collision_budget
      (query_opening_budgets budgets ! i +
        (0 +
          (0 +
            (sum_list
              (take n (drop (Suc i) (query_opening_budgets budgets))) +
              n + 0))))
      (query_opening_stage A i raw \<bind>
        (\<lambda>chunk. assert
          (verifier_query_round_chunk (index (to_nat raw))
            trace_roots composition_roots chunk) \<bind>
          (\<lambda>_. record_staged_messages chunk \<bind>
            (\<lambda>_. checked_staged_query_program A trace_roots
              composition_roots (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks))))))"
    by (rule hash_collision_budget_bind)
      (rule stage_range, rule stage_coll, rule after_check_range,
        rule after_check_coll)
  have whole:
    "hash_collision_budget
      (1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (0 +
              (sum_list
                (take n (drop (Suc i) (query_opening_budgets budgets))) +
                n + 0)))))
      (checked_staged_query_program A trace_roots composition_roots
        i (Suc n))"
    unfolding checked_staged_query_program.simps Let_def
    by (rule hash_collision_budget_bind)
      (rule challenge_range, rule challenge_coll, rule after_stage_range,
        rule after_stage_coll)
  have budget_eq:
    "1 +
        (query_opening_budgets budgets ! i +
          (0 +
            (0 +
              (sum_list
                (take n (drop (Suc i) (query_opening_budgets budgets))) +
                n + 0)))) =
      sum_list (take (Suc n) (drop i (query_opening_budgets budgets))) +
        Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_range_budget_ro_checked_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
  shows
    "hash_range_budget
      (sum_list (take n (drop i (query_opening_budgets budgets))) +
        n +
        n * verifier_query_round_transcript_length 0 trace_roots
          composition_roots)
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case by (simp add: hash_range_budget_return)
next
  case (Suc n)
  let ?L =
    "verifier_query_round_transcript_length 0 trace_roots composition_roots"
  let ?tail =
    "sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
      n + n * ?L"
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems by simp
  have challenge: "hash_range_budget 1 receive_query_index_challenge"
    by (rule hash_range_budget_receive_query_index_challenge)
  have stage:
    "\<And>raw. hash_range_budget (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have check:
    "\<And>raw chunk. hash_range_budget 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule hash_range_budget_assert)
  have tail:
    "hash_range_budget ?tail
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>chunk. hash_range_budget (?tail + 0)
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_range_budget_bind)
      (rule tail, rule hash_range_budget_return)
  have after_record:
    "\<And>raw chunk. verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk \<Longrightarrow>
      hash_range_budget (?L + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
  proof -
    fix raw chunk
    assume chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    have chunk_len:
      "length chunk = ?L"
      using verifier_query_round_chunk_length[OF chunk_shape]
        verifier_query_round_transcript_length_index_irrelevant
          [of "index (to_nat raw)" trace_roots composition_roots 0]
      by simp
    have step:
      "hash_range_budget (length chunk + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      by (rule hash_range_budget_bind)
        (rule hash_range_budget_ro_record_staged_messages,
          rule tail_return)
    then show
      "hash_range_budget (?L + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      using chunk_len by simp
  qed
  have after_check:
    "\<And>raw chunk. hash_range_budget (0 + (?L + (?tail + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
  proof (rule hash_range_budget_bind_on_outcomes)
    fix raw chunk
    show "hash_range_budget 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
      by (rule check)
  next
    fix raw chunk s x t
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
    show "hash_range_budget (?L + (?tail + 0))
      ((\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))) x)"
      by (rule after_record[OF chunk_shape])
  qed
  have after_stage:
    "\<And>raw. hash_range_budget
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
    by (rule hash_range_budget_bind)
      (rule stage, rule after_check)
  have whole:
    "hash_range_budget
      (1 +
        (query_opening_budgets budgets ! i +
          (0 + (?L + (?tail + 0)))))
      (ro_checked_staged_query_program A trace_roots composition_roots
        i (Suc n))"
    unfolding ro_checked_staged_query_program.simps Let_def
    by (rule hash_range_budget_bind)
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

lemma hash_collision_budget_ro_checked_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
  shows
    "hash_collision_budget
      (sum_list (take n (drop i (query_opening_budgets budgets))) +
        n +
        n * verifier_query_round_transcript_length 0 trace_roots
          composition_roots)
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case by (simp add: hash_collision_budget_return)
next
  case (Suc n)
  let ?L =
    "verifier_query_round_transcript_length 0 trace_roots composition_roots"
  let ?tail =
    "sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
      n + n * ?L"
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems by simp
  have challenge_range: "hash_range_budget 1 receive_query_index_challenge"
    by (rule hash_range_budget_receive_query_index_challenge)
  have challenge_coll: "hash_collision_budget 1 receive_query_index_challenge"
    by (rule hash_collision_budget_receive_query_index_challenge)
  have stage_range:
    "\<And>raw. hash_range_budget (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have stage_coll:
    "\<And>raw. hash_collision_budget (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have check_range:
    "\<And>raw chunk. hash_range_budget 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule hash_range_budget_assert)
  have check_coll:
    "\<And>raw chunk. hash_collision_budget 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule hash_collision_budget_assert)
  have tail_range:
    "hash_range_budget ?tail
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule hash_range_budget_ro_checked_staged_query_program[OF controlled])
      (use Suc.prems in simp)
  have tail_coll:
    "hash_collision_budget ?tail
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return_range:
    "\<And>chunk. hash_range_budget (?tail + 0)
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_range_budget_bind)
      (rule tail_range, rule hash_range_budget_return)
  have tail_return_coll:
    "\<And>chunk. hash_collision_budget (?tail + 0)
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_collision_budget_bind)
      (rule tail_range, rule tail_coll, rule hash_range_budget_return,
        rule hash_collision_budget_return)
  have after_record_range:
    "\<And>raw chunk. verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk \<Longrightarrow>
      hash_range_budget (?L + (?tail + 0))
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
      "hash_range_budget (length chunk + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      by (rule hash_range_budget_bind)
        (rule hash_range_budget_ro_record_staged_messages,
          rule tail_return_range)
    then show
      "hash_range_budget (?L + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      using chunk_len by simp
  qed
  have after_record_coll:
    "\<And>raw chunk. verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk \<Longrightarrow>
      hash_collision_budget (?L + (?tail + 0))
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
      "hash_collision_budget (length chunk + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      by (rule hash_collision_budget_bind)
        (rule hash_range_budget_ro_record_staged_messages,
          rule hash_collision_budget_ro_record_staged_messages,
          rule tail_return_range, rule tail_return_coll)
    then show
      "hash_collision_budget (?L + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      using chunk_len by simp
  qed
  have after_check_range:
    "\<And>raw chunk. hash_range_budget (0 + (?L + (?tail + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
  proof (rule hash_range_budget_bind_on_outcomes)
    fix raw chunk
    show "hash_range_budget 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
      by (rule check_range)
  next
    fix raw chunk s x t
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
    show "hash_range_budget (?L + (?tail + 0))
      ((\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))) x)"
      by (rule after_record_range[OF chunk_shape])
  qed
  have after_check_coll:
    "\<And>raw chunk. hash_collision_budget (0 + (?L + (?tail + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
  proof (rule hash_collision_budget_bind_on_outcomes)
    fix raw chunk
    show "hash_range_budget 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
      by (rule check_range)
    show "hash_collision_budget 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
      by (rule check_coll)
  next
    fix raw chunk s x t
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
    show "hash_range_budget (?L + (?tail + 0))
      ((\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))) x)"
      by (rule after_record_range[OF chunk_shape])
    show "hash_collision_budget (?L + (?tail + 0))
      ((\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))) x)"
      by (rule after_record_coll[OF chunk_shape])
  qed
  have after_stage_range:
    "\<And>raw. hash_range_budget
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
    by (rule hash_range_budget_bind)
      (rule stage_range, rule after_check_range)
  have after_stage_coll:
    "\<And>raw. hash_collision_budget
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
    by (rule hash_collision_budget_bind)
      (rule stage_range, rule stage_coll, rule after_check_range,
        rule after_check_coll)
  have whole:
    "hash_collision_budget
      (1 +
        (query_opening_budgets budgets ! i +
          (0 + (?L + (?tail + 0)))))
      (ro_checked_staged_query_program A trace_roots composition_roots
        i (Suc n))"
    unfolding ro_checked_staged_query_program.simps Let_def
    by (rule hash_collision_budget_bind)
      (rule challenge_range, rule challenge_coll, rule after_stage_range,
        rule after_stage_coll)
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

lemma hash_target_program_ro_checked_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
  shows
    "hash_target_program B
      (sum_list (take n (drop i (query_opening_budgets budgets))) +
        n +
        n * verifier_query_round_transcript_length 0 trace_roots
          composition_roots)
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case by (simp add: hash_target_program_return)
next
  case (Suc n)
  let ?L =
    "verifier_query_round_transcript_length 0 trace_roots composition_roots"
  let ?tail =
    "sum_list (take n (drop (Suc i) (query_opening_budgets budgets))) +
      n + n * ?L"
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems by simp
  have challenge: "hash_target_program B 1 receive_query_index_challenge"
    by (rule hash_target_program_receive_query_index_challenge)
  have stage:
    "\<And>raw. hash_target_program B (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have check:
    "\<And>raw chunk. hash_target_program B 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule hash_target_program_assert)
  have tail:
    "hash_target_program B ?tail
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>chunk. hash_target_program B (?tail + 0)
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_target_program_bind)
      (rule tail, rule hash_target_program_return)
  have after_record:
    "\<And>raw chunk. verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk \<Longrightarrow>
      hash_target_program B (?L + (?tail + 0))
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
      "hash_target_program B (length chunk + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      by (rule hash_target_program_bind)
        (rule hash_target_program_ro_record_staged_messages,
          rule tail_return)
    then show
      "hash_target_program B (?L + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      using chunk_len by simp
  qed
  have after_check:
    "\<And>raw chunk. hash_target_program B (0 + (?L + (?tail + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
  proof (rule hash_target_program_bind_on_outcomes)
    fix raw chunk
    show "hash_target_program B 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
      by (rule check)
  next
    fix raw chunk s x t
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
    show "hash_target_program B (?L + (?tail + 0))
      ((\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))) x)"
      by (rule after_record[OF chunk_shape])
  qed
  have after_stage:
    "\<And>raw. hash_target_program B
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
    by (rule hash_target_program_bind)
      (rule stage, rule after_check)
  have whole:
    "hash_target_program B
      (1 +
        (query_opening_budgets budgets ! i +
          (0 + (?L + (?tail + 0)))))
      (ro_checked_staged_query_program A trace_roots composition_roots
        i (Suc n))"
    unfolding ro_checked_staged_query_program.simps Let_def
    by (rule hash_target_program_bind)
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

lemma hash_relation_program_ro_checked_staged_query_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (sum_list (take n (drop i (query_opening_budgets budgets))) +
        n +
        n * verifier_query_round_transcript_length 0 trace_roots
          composition_roots)
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
  using bound
proof (induction n arbitrary: i)
  case 0
  then show ?case
    by (simp add: hash_relation_program_zero[OF hash_map_preserving_return])
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
    "hash_relation_program R b 1 receive_query_index_challenge"
    by (rule hash_relation_program_receive_query_index_challenge[OF fibers])
  have stage:
    "\<And>raw. hash_relation_program R b
      (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
  proof -
    fix raw
    have stage_controlled:
      "controlled_ro_program (query_opening_budgets budgets ! i)
        (query_opening_stage A i raw)"
      using controlled i_bound
      unfolding staged_adversary_controlled_def by blast
    show "hash_relation_program R b
        (query_opening_budgets budgets ! i)
        (query_opening_stage A i raw)"
      by (rule controlled_ro_program_relation
          [OF stage_controlled fibers])
  qed
  have check:
    "\<And>raw chunk. hash_relation_program R b 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
    by (rule hash_relation_program_assert)
  have tail:
    "hash_relation_program R b ?tail
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>chunk. hash_relation_program R b (?tail + 0)
      (ro_checked_staged_query_program A trace_roots composition_roots
        (Suc i) n \<bind>
        (\<lambda>chunks. return (chunk # chunks)))"
    by (rule hash_relation_program_bind)
      (rule tail,
        rule hash_relation_program_zero[OF hash_map_preserving_return])
  have after_record:
    "\<And>raw chunk. verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk \<Longrightarrow>
      hash_relation_program R b (?L + (?tail + 0))
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
      "hash_relation_program R b (length chunk + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      by (rule hash_relation_program_bind)
        (rule hash_relation_program_ro_record_staged_messages[OF fibers],
          rule tail_return)
    then show
      "hash_relation_program R b (?L + (?tail + 0))
        (ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks))))"
      using chunk_len by simp
  qed
  have after_check:
    "\<And>raw chunk. hash_relation_program R b (0 + (?L + (?tail + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk) \<bind>
        (\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))))"
  proof (rule hash_relation_program_bind_on_outcomes)
    fix raw chunk
    show "hash_relation_program R b 0
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk))"
      by (rule check)
  next
    fix raw chunk s x t
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
    show "hash_relation_program R b (?L + (?tail + 0))
      ((\<lambda>_. ro_record_staged_messages chunk \<bind>
          (\<lambda>_. ro_checked_staged_query_program A trace_roots
            composition_roots (Suc i) n \<bind>
            (\<lambda>chunks. return (chunk # chunks)))) x)"
      by (rule after_record[OF chunk_shape])
  qed
  have after_stage:
    "\<And>raw. hash_relation_program R b
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
    by (rule hash_relation_program_bind)
      (rule stage, rule after_check)
  have whole:
    "hash_relation_program R b
      (1 +
        (query_opening_budgets budgets ! i +
          (0 + (?L + (?tail + 0)))))
      (ro_checked_staged_query_program A trace_roots composition_roots
        i (Suc n))"
    unfolding ro_checked_staged_query_program.simps Let_def
    by (rule hash_relation_program_bind)
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

lemma hash_range_budget_guarded_staged_composition_fri_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (sum_list (composition_fri_budgets budgets) +
        ceil_log (maxDegree + 1))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
proof -
  let ?B =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  have "hash_range_budget (0 + ?B)
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
      (\<lambda>_. staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) []))"
  proof (rule hash_range_budget_bind_on_outcomes
      [where n=0 and n'="?B"])
  show "hash_range_budget 0
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))"
    unfolding hash_range_budget_def assert_def
    by (auto simp: throw_no_outcome)
next
  fix s x t
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
    "hash_range_budget
      (sum_list
        (take (ceil_log (to_nat dg + 1))
          (drop 0 (composition_fri_budgets budgets))) +
        ceil_log (to_nat dg + 1))
      (staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) [])"
    by (rule hash_range_budget_staged_composition_fri_program
        [OF controlled len])
  have le:
    "sum_list
        (take (ceil_log (to_nat dg + 1))
          (drop 0 (composition_fri_budgets budgets))) +
        ceil_log (to_nat dg + 1) \<le>
      sum_list (composition_fri_budgets budgets) +
        ceil_log (maxDegree + 1)"
    using round_bound sum_list_take_le[of "ceil_log (to_nat dg + 1)"
        "composition_fri_budgets budgets"]
    by simp
  show "hash_range_budget
    (sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1))
    (staged_composition_fri_program A dg 0
      (ceil_log (to_nat dg + 1)) [])"
    by (rule hash_range_budget_mono[OF le exact])
  qed
  then show ?thesis by simp
qed

lemma hash_collision_budget_guarded_staged_composition_fri_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (sum_list (composition_fri_budgets budgets) +
        ceil_log (maxDegree + 1))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
proof -
  let ?B =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  have "hash_collision_budget (0 + ?B)
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
      (\<lambda>_. staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) []))"
  proof (rule hash_collision_budget_bind_on_outcomes
      [where n=0 and n'="?B"])
  show "hash_range_budget 0
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))"
    unfolding hash_range_budget_def assert_def
    by (auto simp: throw_no_outcome)
  show "hash_collision_budget 0
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))"
    unfolding hash_collision_budget_def hash_new_collision_event_def
      hash_map_new_output_collision_def hash_collision_budget_value_def
      assert_def
    by (simp add: wp_event_def wpsimps)
next
  fix s x t
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
    "hash_range_budget
      (sum_list
        (take (ceil_log (to_nat dg + 1))
          (drop 0 (composition_fri_budgets budgets))) +
        ceil_log (to_nat dg + 1))
      (staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) [])"
    by (rule hash_range_budget_staged_composition_fri_program
        [OF controlled len])
  have le:
    "sum_list
        (take (ceil_log (to_nat dg + 1))
          (drop 0 (composition_fri_budgets budgets))) +
        ceil_log (to_nat dg + 1) \<le>
      sum_list (composition_fri_budgets budgets) +
        ceil_log (maxDegree + 1)"
    using round_bound sum_list_take_le[of "ceil_log (to_nat dg + 1)"
        "composition_fri_budgets budgets"]
    by simp
  show "hash_range_budget
    (sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1))
    (staged_composition_fri_program A dg 0
      (ceil_log (to_nat dg + 1)) [])"
    by (rule hash_range_budget_mono[OF le exact])
next
  fix s x t
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
    "hash_collision_budget
      (sum_list
        (take (ceil_log (to_nat dg + 1))
          (drop 0 (composition_fri_budgets budgets))) +
        ceil_log (to_nat dg + 1))
      (staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) [])"
    by (rule hash_collision_budget_staged_composition_fri_program
        [OF controlled len])
  have le:
    "sum_list
        (take (ceil_log (to_nat dg + 1))
          (drop 0 (composition_fri_budgets budgets))) +
        ceil_log (to_nat dg + 1) \<le>
      sum_list (composition_fri_budgets budgets) +
        ceil_log (maxDegree + 1)"
    using round_bound sum_list_take_le[of "ceil_log (to_nat dg + 1)"
        "composition_fri_budgets budgets"]
    by simp
  show "hash_collision_budget
    (sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1))
    (staged_composition_fri_program A dg 0
      (ceil_log (to_nat dg + 1)) [])"
    by (rule hash_collision_budget_mono[OF le exact])
  qed
  then show ?thesis by simp
qed

lemma hash_target_program_guarded_staged_composition_fri_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (sum_list (composition_fri_budgets budgets) +
        ceil_log (maxDegree + 1))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
proof -
  let ?B =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  have "hash_target_program B (0 + ?B)
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
      (\<lambda>_. staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) []))"
  proof (rule hash_target_program_bind_on_outcomes
      [where n=0 and n'="?B"])
    show "hash_target_program B 0
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))"
      by (rule hash_target_program_assert)
  next
    fix s x t
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
      "hash_target_program B
        (sum_list
          (take (ceil_log (to_nat dg + 1))
            (drop 0 (composition_fri_budgets budgets))) +
          ceil_log (to_nat dg + 1))
        (staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])"
      by (rule hash_target_program_staged_composition_fri_program
          [OF controlled len])
    have le:
      "sum_list
          (take (ceil_log (to_nat dg + 1))
            (drop 0 (composition_fri_budgets budgets))) +
          ceil_log (to_nat dg + 1) \<le>
        sum_list (composition_fri_budgets budgets) +
          ceil_log (maxDegree + 1)"
      using round_bound sum_list_take_le[of "ceil_log (to_nat dg + 1)"
          "composition_fri_budgets budgets"]
      by simp
    show "hash_target_program B
      (sum_list (composition_fri_budgets budgets) +
        ceil_log (maxDegree + 1))
      (staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) [])"
      by (rule hash_target_program_mono[OF le exact])
  qed
  then show ?thesis by simp
qed

lemma hash_target_program_staged_alpha_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (staged_alpha_search_queries budgets 0)
      (staged_alpha_prefix_program A)"
proof -
  let ?trace_root = "trace_root_budget budgets"
  let ?trace_fri =
    "sum_list (trace_fri_budgets budgets) + ceil_log clength"
  let ?trace_final = "trace_final_budget budgets"
  have trace_root_target:
    "hash_target_program B ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have trace_fri_target:
    "hash_target_program B ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_target_program B
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          ceil_log clength)
        (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_target_program_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final_target:
    "\<And>bs. hash_target_program B ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have after_trace_final_record:
    "\<And>fr trace_roots trace_bs trace_final.
      hash_target_program B 0
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
  proof -
    fix fr trace_roots trace_bs trace_final
    have "hash_target_program B (0 + 0)
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
      by (rule hash_target_program_bind)
        (rule hash_target_program_record_staged_message,
          rule hash_target_program_return)
    then show
      "hash_target_program B 0
        (record_staged_message trace_final \<bind>
          (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))"
      by simp
  qed
  have after_trace_final:
    "\<And>fr trace_roots trace_bs.
      hash_target_program B (?trace_final + 0)
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final.
            record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
    by (rule hash_target_program_bind)
      (rule trace_final_target, rule after_trace_final_record)
  have after_trace_fri:
    "\<And>fr. hash_target_program B (?trace_fri + (?trace_final + 0))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final.
              record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))))"
  proof (rule hash_target_program_bind)
    fix fr
    show "hash_target_program B ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_target)
  next
    fix fr x
    show "hash_target_program B (?trace_final + 0)
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final.
            record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have target:
        "hash_target_program B (?trace_final + 0)
          (trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final.
              record_staged_message trace_final \<bind>
                (\<lambda>_. return
                  (fr, trace_roots, trace_bs, trace_final))))"
        by (rule hash_target_program_bind)
          (rule trace_final_target, rule after_trace_final_record)
      show ?thesis
        unfolding Pair using target by simp
    qed
  qed
  have after_trace_root_record:
    "\<And>fr. hash_target_program B (0 + (?trace_fri + (?trace_final + 0)))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                record_staged_message trace_final \<bind>
                  (\<lambda>_. return
                    (fr, trace_roots, trace_bs, trace_final))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule after_trace_fri)
  have whole:
    "hash_target_program B
      (?trace_root + (0 + (?trace_fri + (?trace_final + 0))))
      (staged_alpha_prefix_program A)"
    unfolding staged_alpha_prefix_program_def
    by (rule hash_target_program_bind)
      (rule trace_root_target, rule after_trace_root_record)
  show ?thesis
    using whole
    unfolding staged_alpha_search_queries_def
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma staged_alpha_prefix_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (staged_alpha_prefix_program A)
      (hash_new_output_hit_event B s) s \<le>
      staged_phase_target_error B
        (staged_alpha_search_queries budgets 0)"
proof -
  have budget:
    "hash_target_budget B (staged_alpha_search_queries budgets 0)
      (staged_alpha_prefix_program A)"
    using hash_target_program_staged_alpha_prefix_program[OF wf controlled]
    unfolding hash_target_program_def by simp
  show ?thesis
    using budget unfolding hash_target_budget_def
      staged_phase_target_error_def by blast
qed

lemma hash_target_program_staged_alpha_challenge_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> length spec"
  shows
    "hash_target_program B (staged_alpha_search_queries budgets i)
      (staged_alpha_challenge_prefix_program A i)"
proof -
  let ?alpha_prefix = "staged_alpha_search_queries budgets 0"
  have prefix_target:
    "hash_target_program B ?alpha_prefix (staged_alpha_prefix_program A)"
    by (rule hash_target_program_staged_alpha_prefix_program[OF wf controlled])
  have alpha_target:
    "\<And>prefix. hash_target_program B i
      (staged_alpha_program i \<bind>
        (\<lambda>as_prefix. return (prefix, as_prefix)))"
  proof -
    fix prefix
    have "hash_target_program B (i + 0)
        (staged_alpha_program i \<bind>
          (\<lambda>as_prefix. return (prefix, as_prefix)))"
      by (rule hash_target_program_bind)
        (rule hash_target_program_staged_alpha_program,
         rule hash_target_program_return)
    then show "hash_target_program B i
      (staged_alpha_program i \<bind>
        (\<lambda>as_prefix. return (prefix, as_prefix)))"
      by simp
  qed
  have whole:
    "hash_target_program B (?alpha_prefix + i)
      (staged_alpha_challenge_prefix_program A i)"
    unfolding staged_alpha_challenge_prefix_program_def
    by (rule hash_target_program_bind[OF prefix_target alpha_target])
  show ?thesis
    using whole i_bound
    unfolding staged_alpha_search_queries_def
    by simp
qed

lemma staged_alpha_prefix_target_hit_bound_i:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> length spec"
  shows
    "wp_event (staged_alpha_challenge_prefix_program A i)
      (hash_new_output_hit_event B s) s \<le>
      staged_phase_target_error B
        (staged_alpha_search_queries budgets i)"
proof -
  have budget:
    "hash_target_budget B (staged_alpha_search_queries budgets i)
      (staged_alpha_challenge_prefix_program A i)"
    using hash_target_program_staged_alpha_challenge_prefix_program
        [OF wf controlled i_bound]
    unfolding hash_target_program_def by simp
  show ?thesis
    using budget unfolding hash_target_budget_def
      staged_phase_target_error_def by blast
qed

lemma hash_target_program_staged_composition_fri_vector_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (staged_composition_fri_vector_search_queries budgets)
      (staged_composition_fri_vector_program A)"
proof -
  let ?alpha_prefix = "staged_alpha_search_queries budgets 0"
  let ?alpha = "length spec"
  let ?degree = "degree_budget budgets"
  let ?composition =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  have alpha_prefix_target:
    "hash_target_program B ?alpha_prefix (staged_alpha_prefix_program A)"
    by (rule hash_target_program_staged_alpha_prefix_program[OF wf controlled])
  have alpha_target:
    "hash_target_program B ?alpha (staged_alpha_program (length spec))"
    by (rule hash_target_program_staged_alpha_program)
  have degree_target:
    "\<And>as. hash_target_program B ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have guarded_return:
    "\<And>dg. hash_target_program B (?composition + 0)
      ((assert
          (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [])) \<bind>
        (\<lambda>x. case x of (_, composition_bs) \<Rightarrow>
          return (dg, composition_bs)))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_guarded_staged_composition_fri_program
        [OF wf controlled], simp add: hash_target_program_return
        split: prod.splits)
  have after_record:
    "\<And>dg. hash_target_program B (0 + (?composition + 0))
      (record_staged_message dg \<bind>
        (\<lambda>_. (assert
            (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])) \<bind>
          (\<lambda>x. case x of (_, composition_bs) \<Rightarrow>
            return (dg, composition_bs))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule guarded_return)
  have after_degree:
    "\<And>as. hash_target_program B
      (?degree + (0 + (?composition + 0)))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
            assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                composition_rounds [] \<bind>
                (\<lambda>(_, composition_bs). return (dg, composition_bs))))))"
    unfolding Let_def
  proof (rule hash_target_program_bind)
    fix as
    show "hash_target_program B ?degree (degree_stage A as)"
      by (rule degree_target)
  next
    fix as dg
    show "hash_target_program B (0 + (?composition + 0))
      (record_staged_message dg \<bind>
        (\<lambda>_. assert
          (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [] \<bind>
            (\<lambda>(_, composition_bs). return (dg, composition_bs)))))"
      using after_record[of dg] by (simp add: sm_bind_assoc)
  qed
  have after_alpha:
    "\<And>x. hash_target_program B
      (?alpha + (?degree + (0 + (?composition + 0))))
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
              assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                composition_rounds [] \<bind>
                (\<lambda>(_, composition_bs). return (dg, composition_bs)))))))"
  proof (rule hash_target_program_bind)
    fix x
    show "hash_target_program B ?alpha
      (staged_alpha_program (length spec))"
      by (rule alpha_target)
  next
    fix x as
    show "hash_target_program B (?degree + (0 + (?composition + 0)))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1)
            in assert
              (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                composition_rounds [] \<bind>
                (\<lambda>(_, composition_bs). return (dg, composition_bs))))))"
      by (rule after_degree)
  qed
  have whole:
    "hash_target_program B
      (?alpha_prefix +
        (?alpha + (?degree + (0 + (?composition + 0)))))
      (staged_composition_fri_vector_program A)"
    unfolding staged_composition_fri_vector_program_def
  proof (rule hash_target_program_bind)
    show "hash_target_program B ?alpha_prefix
      (staged_alpha_prefix_program A)"
      by (rule alpha_prefix_target)
  next
    fix x
    show "hash_target_program B
      (?alpha + (?degree + (0 + (?composition + 0))))
      (case x of
        (a, b, trace_bs, c) \<Rightarrow>
          staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. let composition_rounds =
                ceil_log (to_nat dg + 1)
                in assert
                  (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_. staged_composition_fri_program A dg 0
                    composition_rounds [] \<bind>
                    (\<lambda>(r, composition_bs).
                      return (dg, composition_bs)))))))"
      using after_alpha by (cases x) simp
  qed
  show ?thesis
    using whole
    unfolding staged_composition_fri_vector_search_queries_def
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma staged_composition_fri_vector_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (staged_composition_fri_vector_program A)
      (hash_new_output_hit_event B s) s \<le>
      staged_phase_target_error B
        (staged_composition_fri_vector_search_queries budgets)"
proof -
  have budget:
    "hash_target_budget B
      (staged_composition_fri_vector_search_queries budgets)
      (staged_composition_fri_vector_program A)"
    using hash_target_program_staged_composition_fri_vector_program
        [OF wf controlled]
    unfolding hash_target_program_def by simp
  show ?thesis
    using budget unfolding hash_target_budget_def
      staged_phase_target_error_def by blast
qed

lemma hash_target_program_staged_trace_fri_challenge_prefix_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < length (trace_fri_budgets budgets)"
  shows
    "hash_target_program B
      (staged_trace_fri_search_queries budgets i)
      (staged_trace_fri_challenge_prefix_program A i)"
proof -
  let ?trace_root = "trace_root_budget budgets"
  let ?completed = "sum_list (take i (trace_fri_budgets budgets)) + i"
  let ?current = "trace_fri_budgets budgets ! i"
  have trace_root_target:
    "hash_target_program B ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have completed_target:
    "hash_target_program B ?completed
      (staged_trace_fri_program A 0 i [])"
  proof -
    have len: "0 + i \<le> length (trace_fri_budgets budgets)"
      using i_bound by simp
    have exact:
      "hash_target_program B
        (sum_list (take i (drop 0 (trace_fri_budgets budgets))) + i)
        (staged_trace_fri_program A 0 i [])"
      by (rule hash_target_program_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis by simp
  qed
  have current_target:
    "\<And>trace_bs. hash_target_program B ?current
      (trace_fri_root_stage A i trace_bs)"
    using controlled i_bound unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have after_current_record:
    "\<And>fr trace_bs root. hash_target_program B 0
      (record_staged_message root \<bind>
        (\<lambda>_. return (fr, trace_bs, root)))"
  proof -
    fix fr trace_bs root
    have "hash_target_program B (0 + 0)
      (record_staged_message root \<bind>
        (\<lambda>_. return (fr, trace_bs, root)))"
      by (rule hash_target_program_bind)
        (rule hash_target_program_record_staged_message,
          rule hash_target_program_return)
    then show "hash_target_program B 0
      (record_staged_message root \<bind>
        (\<lambda>_. return (fr, trace_bs, root)))"
      by simp
  qed
  have after_current:
    "\<And>fr trace_bs. hash_target_program B (?current + 0)
      (trace_fri_root_stage A i trace_bs \<bind>
        (\<lambda>root. record_staged_message root \<bind>
          (\<lambda>_. return (fr, trace_bs, root))))"
    by (rule hash_target_program_bind)
      (rule current_target, rule after_current_record)
  have after_completed:
    "\<And>fr. hash_target_program B (?completed + (?current + 0))
      (staged_trace_fri_program A 0 i [] \<bind>
        (\<lambda>(_, trace_bs).
          trace_fri_root_stage A i trace_bs \<bind>
            (\<lambda>root. record_staged_message root \<bind>
              (\<lambda>_. return (fr, trace_bs, root)))))"
  proof (rule hash_target_program_bind)
    fix fr
    show "hash_target_program B ?completed
      (staged_trace_fri_program A 0 i [])"
      by (rule completed_target)
  next
    fix fr x
    show "hash_target_program B (?current + 0)
      (case x of (_, trace_bs) \<Rightarrow>
        trace_fri_root_stage A i trace_bs \<bind>
          (\<lambda>root. record_staged_message root \<bind>
            (\<lambda>_. return (fr, trace_bs, root))))"
    proof (cases x)
      case (Pair roots trace_bs)
      have target:
        "hash_target_program B (?current + 0)
          (trace_fri_root_stage A i trace_bs \<bind>
            (\<lambda>root. record_staged_message root \<bind>
              (\<lambda>_. return (fr, trace_bs, root))))"
        by (rule after_current)
      show ?thesis
        unfolding Pair using target by simp
    qed
  qed
  have after_trace_root_record:
    "\<And>fr. hash_target_program B (0 + (?completed + (?current + 0)))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 i [] \<bind>
          (\<lambda>(_, trace_bs).
            trace_fri_root_stage A i trace_bs \<bind>
              (\<lambda>root. record_staged_message root \<bind>
                (\<lambda>_. return (fr, trace_bs, root))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule after_completed)
  have whole:
    "hash_target_program B
      (?trace_root + (0 + (?completed + (?current + 0))))
      (staged_trace_fri_challenge_prefix_program A i)"
    unfolding staged_trace_fri_challenge_prefix_program_def
    by (rule hash_target_program_bind)
      (rule trace_root_target, rule after_trace_root_record)
  have sum_eq:
    "?current + sum_list (take i (trace_fri_budgets budgets)) =
      sum_list (take (Suc i) (trace_fri_budgets budgets))"
  proof -
    have "take (Suc i) (trace_fri_budgets budgets) =
        take i (trace_fri_budgets budgets) @
        [trace_fri_budgets budgets ! i]"
      by (rule take_Suc_conv_app_nth[OF i_bound])
    then show ?thesis by simp
  qed
  show ?thesis
    using whole
    unfolding staged_trace_fri_search_queries_def
    by (simp add: sum_eq add.assoc add.commute add.left_commute)
qed

lemma staged_trace_fri_prefix_target_hit_bound:
  assumes controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < length (trace_fri_budgets budgets)"
  shows
    "wp_event (staged_trace_fri_challenge_prefix_program A i)
      (hash_new_output_hit_event B s) s \<le>
      staged_phase_target_error B
        (staged_trace_fri_search_queries budgets i)"
proof -
  have budget:
    "hash_target_budget B (staged_trace_fri_search_queries budgets i)
      (staged_trace_fri_challenge_prefix_program A i)"
    using hash_target_program_staged_trace_fri_challenge_prefix_program
        [OF controlled i_bound]
    unfolding hash_target_program_def by simp
  show ?thesis
    using budget unfolding hash_target_budget_def
      staged_phase_target_error_def by blast
qed

lemma hash_target_program_staged_composition_fri_challenge_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log (maxDegree + 1)"
  shows
    "hash_target_program B
      (staged_composition_fri_search_queries budgets i)
      (staged_composition_fri_challenge_prefix_program A i)"
proof -
  let ?alpha_prefix = "staged_alpha_search_queries budgets 0"
  let ?alpha = "length spec"
  let ?degree = "degree_budget budgets"
  let ?completed =
    "sum_list (take i (composition_fri_budgets budgets)) + i"
  let ?current = "composition_fri_budgets budgets ! i"
  have comp_i_bound: "i < length (composition_fri_budgets budgets)"
    using wf i_bound unfolding staged_budget_wellformed_def by simp
  have alpha_prefix_target:
    "hash_target_program B ?alpha_prefix (staged_alpha_prefix_program A)"
    by (rule hash_target_program_staged_alpha_prefix_program[OF wf controlled])
  have alpha_target:
    "hash_target_program B ?alpha (staged_alpha_program (length spec))"
    by (rule hash_target_program_staged_alpha_program)
  have degree_target:
    "\<And>as. hash_target_program B ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have completed_target:
    "\<And>dg. hash_target_program B ?completed
      (staged_composition_fri_program A dg 0 i [])"
  proof -
    fix dg
    have len: "0 + i \<le> length (composition_fri_budgets budgets)"
      using comp_i_bound by simp
    have exact:
      "hash_target_program B
        (sum_list (take i (drop 0 (composition_fri_budgets budgets))) + i)
        (staged_composition_fri_program A dg 0 i [])"
      by (rule hash_target_program_staged_composition_fri_program
          [OF controlled len])
    then show
      "hash_target_program B ?completed
        (staged_composition_fri_program A dg 0 i [])"
      by simp
  qed
  have current_target:
    "\<And>dg composition_bs. hash_target_program B ?current
      (composition_fri_root_stage A dg i composition_bs)"
    using controlled comp_i_bound
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have after_current_record:
    "\<And>dg composition_bs root. hash_target_program B 0
      (record_staged_message root \<bind>
        (\<lambda>_. return (dg, composition_bs, root)))"
  proof -
    fix dg composition_bs root
    have "hash_target_program B (0 + 0)
      (record_staged_message root \<bind>
        (\<lambda>_. return (dg, composition_bs, root)))"
      by (rule hash_target_program_bind)
        (rule hash_target_program_record_staged_message,
          rule hash_target_program_return)
    then show
      "hash_target_program B 0
        (record_staged_message root \<bind>
          (\<lambda>_. return (dg, composition_bs, root)))"
      by simp
  qed
  have after_current:
    "\<And>dg composition_bs. hash_target_program B (?current + 0)
      (composition_fri_root_stage A dg i composition_bs \<bind>
        (\<lambda>root. record_staged_message root \<bind>
          (\<lambda>_. return (dg, composition_bs, root))))"
    by (rule hash_target_program_bind)
      (rule current_target, rule after_current_record)
  have after_completed:
    "\<And>dg. hash_target_program B (?completed + (?current + 0))
      (staged_composition_fri_program A dg 0 i [] \<bind>
        (\<lambda>(_, composition_bs).
          composition_fri_root_stage A dg i composition_bs \<bind>
            (\<lambda>root. record_staged_message root \<bind>
              (\<lambda>_. return (dg, composition_bs, root)))))"
  proof (rule hash_target_program_bind)
    fix dg
    show "hash_target_program B ?completed
      (staged_composition_fri_program A dg 0 i [])"
      by (rule completed_target)
  next
    fix dg x
    show "hash_target_program B (?current + 0)
      (case x of (_, composition_bs) \<Rightarrow>
        composition_fri_root_stage A dg i composition_bs \<bind>
          (\<lambda>root. record_staged_message root \<bind>
            (\<lambda>_. return (dg, composition_bs, root))))"
    proof (cases x)
      case (Pair roots composition_bs)
      have target:
        "hash_target_program B (?current + 0)
          (composition_fri_root_stage A dg i composition_bs \<bind>
            (\<lambda>root. record_staged_message root \<bind>
              (\<lambda>_. return (dg, composition_bs, root))))"
        by (rule after_current)
      show ?thesis
        unfolding Pair using target by simp
    qed
  qed
  have after_second_assert:
    "\<And>dg. hash_target_program B (0 + (?completed + (?current + 0)))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0 i [] \<bind>
          (\<lambda>(_, composition_bs).
            composition_fri_root_stage A dg i composition_bs \<bind>
              (\<lambda>root. record_staged_message root \<bind>
                (\<lambda>_. return (dg, composition_bs, root))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_assert, rule after_completed)
  have after_first_assert:
    "\<And>dg. hash_target_program B
      (0 + (0 + (?completed + (?current + 0))))
      (assert (Suc i \<le> ceil_log (to_nat dg + 1)) \<bind>
        (\<lambda>_. assert
          (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0 i [] \<bind>
            (\<lambda>(_, composition_bs).
              composition_fri_root_stage A dg i composition_bs \<bind>
                (\<lambda>root. record_staged_message root \<bind>
                  (\<lambda>_. return (dg, composition_bs, root)))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_assert, rule after_second_assert)
  have after_degree_record:
    "\<And>dg. hash_target_program B
      (0 + (0 + (0 + (?completed + (?current + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. assert (Suc i \<le> ceil_log (to_nat dg + 1)) \<bind>
          (\<lambda>_. assert
            (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0 i [] \<bind>
              (\<lambda>(_, composition_bs).
                composition_fri_root_stage A dg i composition_bs \<bind>
                  (\<lambda>root. record_staged_message root \<bind>
                    (\<lambda>_. return (dg, composition_bs, root))))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule after_first_assert)
  have after_degree:
    "\<And>as. hash_target_program B
      (?degree + (0 + (0 + (0 + (?completed + (?current + 0))))))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
            assert (Suc i \<le> composition_rounds) \<bind>
            (\<lambda>_. assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0 i [] \<bind>
                (\<lambda>(_, composition_bs).
                  composition_fri_root_stage A dg i composition_bs \<bind>
                    (\<lambda>root. record_staged_message root \<bind>
                      (\<lambda>_. return (dg, composition_bs, root)))))))))"
    unfolding Let_def
    by (rule hash_target_program_bind)
      (rule degree_target, rule after_degree_record)
  have after_alpha:
    "\<And>x. hash_target_program B
      (?alpha + (?degree + (0 + (0 + (0 + (?completed + (?current + 0)))))))
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
              assert (Suc i \<le> composition_rounds) \<bind>
              (\<lambda>_. assert
                (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0 i [] \<bind>
                  (\<lambda>(_, composition_bs).
                    composition_fri_root_stage A dg i composition_bs \<bind>
                      (\<lambda>root. record_staged_message root \<bind>
                        (\<lambda>_. return
                          (dg, composition_bs, root))))))))))"
    by (rule hash_target_program_bind)
      (rule alpha_target, rule after_degree)
  have after_alpha_prefix:
    "hash_target_program B
      (?alpha_prefix +
        (?alpha + (?degree +
          (0 + (0 + (0 + (?completed + (?current + 0))))))))
      (staged_composition_fri_challenge_prefix_program A i)"
    unfolding staged_composition_fri_challenge_prefix_program_def
  proof (rule hash_target_program_bind)
    show "hash_target_program B ?alpha_prefix
      (staged_alpha_prefix_program A)"
      by (rule alpha_prefix_target)
  next
    fix x
    show "hash_target_program B
      (?alpha + (?degree +
        (0 + (0 + (0 + (?completed + (?current + 0)))))))
      (case x of (_, _, trace_bs, _) \<Rightarrow>
        staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
                assert (Suc i \<le> composition_rounds) \<bind>
                (\<lambda>_. assert
                  (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_. staged_composition_fri_program A dg 0 i [] \<bind>
                    (\<lambda>(_, composition_bs).
                      composition_fri_root_stage A dg i composition_bs \<bind>
                        (\<lambda>root. record_staged_message root \<bind>
                          (\<lambda>_. return
                            (dg, composition_bs, root))))))))))"
    proof (cases x)
      case (fields a b c d)
      have target:
        "hash_target_program B
          (?alpha + (?degree +
            (0 + (0 + (0 + (?completed + (?current + 0)))))))
          (staged_alpha_program (length spec) \<bind>
            (\<lambda>as. degree_stage A as \<bind>
              (\<lambda>dg. record_staged_message dg \<bind>
                (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
                  assert (Suc i \<le> composition_rounds) \<bind>
                  (\<lambda>_. assert
                    (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0 i [] \<bind>
                      (\<lambda>(_, composition_bs).
                        composition_fri_root_stage A dg i composition_bs \<bind>
                          (\<lambda>root. record_staged_message root \<bind>
                            (\<lambda>_. return
                              (dg, composition_bs, root))))))))))"
        by (rule after_alpha)
      show ?thesis
        unfolding fields
        using target
        by (simp add: add.assoc add.commute add.left_commute)
    qed
  qed
  have sum_eq:
    "?current + sum_list (take i (composition_fri_budgets budgets)) =
      sum_list (take (Suc i) (composition_fri_budgets budgets))"
  proof -
    have "take (Suc i) (composition_fri_budgets budgets) =
        take i (composition_fri_budgets budgets) @
        [composition_fri_budgets budgets ! i]"
      by (rule take_Suc_conv_app_nth[OF comp_i_bound])
    then show ?thesis by simp
  qed
  show ?thesis
    using after_alpha_prefix
    unfolding staged_composition_fri_search_queries_def
      staged_alpha_search_queries_def
    by (simp add: sum_eq add.assoc add.commute add.left_commute)
qed

lemma staged_composition_fri_prefix_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log (maxDegree + 1)"
  shows
    "wp_event (staged_composition_fri_challenge_prefix_program A i)
      (hash_new_output_hit_event B s) s \<le>
      staged_phase_target_error B
        (staged_composition_fri_search_queries budgets i)"
proof -
  have budget:
    "hash_target_budget B (staged_composition_fri_search_queries budgets i)
      (staged_composition_fri_challenge_prefix_program A i)"
    using
      hash_target_program_staged_composition_fri_challenge_prefix_program
        [OF wf controlled i_bound]
    unfolding hash_target_program_def by simp
  show ?thesis
    using budget unfolding hash_target_budget_def
      staged_phase_target_error_def by blast
qed

lemma hash_target_program_staged_query_challenge_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "hash_target_program B
      (staged_query_search_queries budgets i)
      (staged_query_challenge_prefix_program A i)"
proof -
  let ?alpha_prefix = "staged_alpha_search_queries budgets 0"
  let ?alpha = "length spec"
  let ?degree = "degree_budget budgets"
  let ?composition_fri =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  let ?query = "sum_list (take i (query_opening_budgets budgets)) + i"
  have alpha_prefix_target:
    "hash_target_program B ?alpha_prefix (staged_alpha_prefix_program A)"
    by (rule hash_target_program_staged_alpha_prefix_program[OF wf controlled])
  have alpha_target:
    "hash_target_program B ?alpha (staged_alpha_program (length spec))"
    by (rule hash_target_program_staged_alpha_program)
  have degree_target:
    "\<And>as. hash_target_program B ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have composition_fri_target:
    "\<And>dg. hash_target_program B ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_target_program_guarded_staged_composition_fri_program
        [OF wf controlled])
  have composition_final_target:
    "\<And>dg bs. hash_target_program B ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have query_target:
    "hash_target_program B ?query (staged_query_program A 0 i)"
  proof -
    have len: "0 + i \<le> length (query_opening_budgets budgets)"
      using wf i_bound unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_target_program B
        (sum_list (take i (drop 0 (query_opening_budgets budgets))) + i)
        (staged_query_program A 0 i)"
      by (rule hash_target_program_staged_query_program
          [OF controlled len])
    then show ?thesis by simp
  qed
  have after_query:
    "\<And>dg composition_final. hash_target_program B (?query + 0)
      (staged_query_program A 0 i \<bind>
        (\<lambda>query_chunks.
          return (dg, composition_final, query_chunks)))"
    by (rule hash_target_program_bind)
      (rule query_target, rule hash_target_program_return)
  have after_composition_final_record:
    "\<And>dg composition_final. hash_target_program B (0 + (?query + 0))
      (record_staged_message composition_final \<bind>
        (\<lambda>_. staged_query_program A 0 i \<bind>
          (\<lambda>query_chunks.
            return (dg, composition_final, query_chunks))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule after_query)
  have after_composition_final:
    "\<And>dg composition_bs. hash_target_program B
      (?composition_final + (0 + (?query + 0)))
      (composition_final_stage A dg composition_bs \<bind>
        (\<lambda>composition_final.
          record_staged_message composition_final \<bind>
            (\<lambda>_. staged_query_program A 0 i \<bind>
              (\<lambda>query_chunks.
                return (dg, composition_final, query_chunks)))))"
    by (rule hash_target_program_bind)
      (rule composition_final_target, rule after_composition_final_record)
  have after_composition_fri:
    "\<And>dg. hash_target_program B
      (?composition_fri + (?composition_final + (0 + (?query + 0))))
      ((assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])) \<bind>
        (\<lambda>(_, composition_bs).
          composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 i \<bind>
                  (\<lambda>query_chunks.
                    return (dg, composition_final, query_chunks))))))"
  proof (rule hash_target_program_bind)
    fix dg
    show "hash_target_program B ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_target)
  next
    fix dg x
    show "hash_target_program B
      (?composition_final + (0 + (?query + 0)))
      (case x of (_, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 i \<bind>
                (\<lambda>query_chunks.
                  return (dg, composition_final, query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have target:
        "hash_target_program B
          (?composition_final + (0 + (?query + 0)))
          (composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 i \<bind>
                  (\<lambda>query_chunks.
                    return (dg, composition_final, query_chunks)))))"
        by (rule after_composition_final)
      show ?thesis
        unfolding Pair using target by simp
    qed
  qed
  have after_degree_record:
    "\<And>dg. hash_target_program B
      (0 + (?composition_fri + (?composition_final + (0 + (?query + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. (assert
          (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [])) \<bind>
          (\<lambda>(_, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. staged_query_program A 0 i \<bind>
                    (\<lambda>query_chunks.
                      return (dg, composition_final, query_chunks)))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message,
        rule after_composition_fri)
  have after_degree_record_expanded:
    "\<And>dg. hash_target_program B
      (0 + (?composition_fri + (?composition_final + (0 + (?query + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. assert
          (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [] \<bind>
            (\<lambda>(_, composition_bs).
              composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  record_staged_message composition_final \<bind>
                    (\<lambda>_. staged_query_program A 0 i \<bind>
                      (\<lambda>query_chunks.
                        return (dg, composition_final, query_chunks))))))))"
    using after_degree_record
    by (simp add: sm_bind_assoc split: prod.splits)
  have after_degree:
    "\<And>as. hash_target_program B
      (?degree +
        (0 + (?composition_fri + (?composition_final + (0 + (?query + 0))))))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
            assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              composition_rounds [] \<bind>
              (\<lambda>(_, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                      (\<lambda>_. staged_query_program A 0 i \<bind>
                        (\<lambda>query_chunks.
                          return
                            (dg, composition_final, query_chunks)))))))))"
    unfolding Let_def
    by (rule hash_target_program_bind)
      (rule degree_target, rule after_degree_record_expanded)
  have after_alpha:
    "\<And>x. hash_target_program B
      (?alpha +
        (?degree +
          (0 + (?composition_fri +
            (?composition_final + (0 + (?query + 0)))))))
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
              assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                composition_rounds [] \<bind>
                (\<lambda>(_, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                        (\<lambda>_. staged_query_program A 0 i \<bind>
                          (\<lambda>query_chunks.
                            return
                              (dg, composition_final, query_chunks))))))))))"
    by (rule hash_target_program_bind)
      (rule alpha_target, rule after_degree)
  have after_alpha_prefix:
    "hash_target_program B
      (?alpha_prefix +
        (?alpha +
          (?degree +
            (0 + (?composition_fri +
              (?composition_final + (0 + (?query + 0))))))))
      (staged_query_challenge_prefix_program A i)"
    unfolding staged_query_challenge_prefix_program_def
  proof (rule hash_target_program_bind)
    show "hash_target_program B ?alpha_prefix
      (staged_alpha_prefix_program A)"
      by (rule alpha_prefix_target)
  next
    fix x
    show "hash_target_program B
      (?alpha +
        (?degree +
          (0 + (?composition_fri +
            (?composition_final + (0 + (?query + 0)))))))
      (case x of (_, _, trace_bs, _) \<Rightarrow>
        staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
                assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  composition_rounds [] \<bind>
                  (\<lambda>(_, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                          (\<lambda>_. staged_query_program A 0 i \<bind>
                            (\<lambda>query_chunks.
                              return
                                (dg, composition_final,
                                  query_chunks))))))))))"
    proof (cases x)
      case (fields a b c d)
      have target:
        "hash_target_program B
          (?alpha +
            (?degree +
              (0 + (?composition_fri +
                (?composition_final + (0 + (?query + 0)))))))
          (staged_alpha_program (length spec) \<bind>
            (\<lambda>as. degree_stage A as \<bind>
              (\<lambda>dg. record_staged_message dg \<bind>
                (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
                  assert
                    (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_. staged_composition_fri_program A dg 0
                    composition_rounds [] \<bind>
                    (\<lambda>(_, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 i \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (dg, composition_final,
                                    query_chunks))))))))))"
        by (rule after_alpha)
      show ?thesis
        unfolding fields
        using target
        by (simp add: add.assoc add.commute add.left_commute)
    qed
  qed
  show ?thesis
    using after_alpha_prefix
    unfolding staged_query_search_queries_def staged_alpha_search_queries_def
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_range_budget_staged_query_challenge_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "hash_range_budget
      (staged_query_search_queries budgets i)
      (staged_query_challenge_prefix_program A i)"
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
    "hash_range_budget ?alpha_prefix (staged_alpha_prefix_program A)"
    by (rule hash_range_budget_staged_alpha_prefix_program
        [OF wf controlled])
  have alpha: "hash_range_budget ?alpha (staged_alpha_program (length spec))"
    by (rule hash_range_budget_staged_alpha_program)
  have degree:
    "\<And>as. hash_range_budget ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have composition_fri:
    "\<And>dg. hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_range_budget_guarded_staged_composition_fri_program
        [OF wf controlled])
  have composition_final:
    "\<And>dg bs. hash_range_budget ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have query: "hash_range_budget ?query (staged_query_program A 0 i)"
  proof -
    have len: "0 + i \<le> length (query_opening_budgets budgets)"
      using wf i_bound unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_range_budget
        (sum_list (take i (drop 0 (query_opening_budgets budgets))) + i)
        (staged_query_program A 0 i)"
      by (rule hash_range_budget_staged_query_program[OF controlled len])
    then show ?thesis by simp
  qed
  have after_query:
    "\<And>dg composition_final. hash_range_budget (?query + 0)
      (staged_query_program A 0 i \<bind>
        (\<lambda>query_chunks. return (dg, composition_final, query_chunks)))"
    by (rule hash_range_budget_bind)
      (rule query, rule hash_range_budget_return)
  have after_composition_final_record:
    "\<And>dg composition_final. hash_range_budget (0 + (?query + 0))
      (record_staged_message composition_final \<bind>
        (\<lambda>_. staged_query_program A 0 i \<bind>
          (\<lambda>query_chunks. return
            (dg, composition_final, query_chunks))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message, rule after_query)
  have after_composition_final:
    "\<And>dg bs. hash_range_budget
      (?composition_final + (0 + (?query + 0)))
      (composition_final_stage A dg bs \<bind>
        (\<lambda>composition_final.
          record_staged_message composition_final \<bind>
            (\<lambda>_. staged_query_program A 0 i \<bind>
              (\<lambda>query_chunks. return
                (dg, composition_final, query_chunks)))))"
    by (rule hash_range_budget_bind)
      (rule composition_final, rule after_composition_final_record)
  have after_composition_fri:
    "\<And>dg. hash_range_budget
      (?composition_fri + (?composition_final + (0 + (?query + 0))))
      ((assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])) \<bind>
        (\<lambda>(_, composition_bs).
          composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 i \<bind>
                  (\<lambda>query_chunks. return
                    (dg, composition_final, query_chunks))))))"
  proof (rule hash_range_budget_bind)
    fix dg
    show "hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri)
  next
    fix dg x
    show "hash_range_budget
      (?composition_final + (0 + (?query + 0)))
      (case x of (_, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 i \<bind>
                (\<lambda>query_chunks. return
                  (dg, composition_final, query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have step:
        "hash_range_budget
          (?composition_final + (0 + (?query + 0)))
          (composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 i \<bind>
                  (\<lambda>query_chunks. return
                    (dg, composition_final, query_chunks)))))"
        by (rule after_composition_final)
      show ?thesis
        unfolding Pair using step by simp
    qed
  qed
  have after_degree_record:
    "\<And>dg. hash_range_budget
      (0 + (?composition_fri + (?composition_final + (0 + (?query + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. (assert
          (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [])) \<bind>
          (\<lambda>(_, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. staged_query_program A 0 i \<bind>
                    (\<lambda>query_chunks. return
                      (dg, composition_final, query_chunks)))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule after_composition_fri)
  have after_degree_record_expanded:
    "\<And>dg. hash_range_budget
      (0 + (?composition_fri + (?composition_final + (0 + (?query + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. assert
          (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [] \<bind>
            (\<lambda>(_, composition_bs).
              composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  record_staged_message composition_final \<bind>
                    (\<lambda>_. staged_query_program A 0 i \<bind>
                      (\<lambda>query_chunks. return
                        (dg, composition_final, query_chunks))))))))"
    using after_degree_record
    by (simp add: sm_bind_assoc split: prod.splits)
  have after_degree:
    "\<And>as. hash_range_budget
      (?degree +
        (0 + (?composition_fri +
          (?composition_final + (0 + (?query + 0))))))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
            assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              composition_rounds [] \<bind>
              (\<lambda>(_, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                      (\<lambda>_. staged_query_program A 0 i \<bind>
                        (\<lambda>query_chunks. return
                          (dg, composition_final, query_chunks)))))))))"
    unfolding Let_def
    by (rule hash_range_budget_bind)
      (rule degree, rule after_degree_record_expanded)
  have after_alpha:
    "\<And>x. hash_range_budget
      (?alpha +
        (?degree +
          (0 + (?composition_fri +
            (?composition_final + (0 + (?query + 0)))))))
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
              assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                composition_rounds [] \<bind>
                (\<lambda>(_, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                        (\<lambda>_. staged_query_program A 0 i \<bind>
                          (\<lambda>query_chunks. return
                            (dg, composition_final, query_chunks))))))))))"
    by (rule hash_range_budget_bind)
      (rule alpha, rule after_degree)
  have after_alpha_prefix:
    "hash_range_budget
      (?alpha_prefix +
        (?alpha +
          (?degree +
            (0 + (?composition_fri +
              (?composition_final + (0 + (?query + 0))))))))
      (staged_query_challenge_prefix_program A i)"
    unfolding staged_query_challenge_prefix_program_def
  proof (rule hash_range_budget_bind)
    show "hash_range_budget ?alpha_prefix
      (staged_alpha_prefix_program A)"
      by (rule alpha_prefix)
  next
    fix x
    show "hash_range_budget
      (?alpha +
        (?degree +
          (0 + (?composition_fri +
            (?composition_final + (0 + (?query + 0)))))))
      (case x of (_, _, trace_bs, _) \<Rightarrow>
        staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
                assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  composition_rounds [] \<bind>
                  (\<lambda>(_, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                          (\<lambda>_. staged_query_program A 0 i \<bind>
                            (\<lambda>query_chunks. return
                              (dg, composition_final,
                                query_chunks))))))))))"
    proof (cases x)
      case (fields a b c d)
      have step:
        "hash_range_budget
          (?alpha +
            (?degree +
              (0 + (?composition_fri +
                (?composition_final + (0 + (?query + 0)))))))
          (staged_alpha_program (length spec) \<bind>
            (\<lambda>as. degree_stage A as \<bind>
              (\<lambda>dg. record_staged_message dg \<bind>
                (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
                  assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_. staged_composition_fri_program A dg 0
                    composition_rounds [] \<bind>
                    (\<lambda>(_, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 i \<bind>
                              (\<lambda>query_chunks. return
                                (dg, composition_final,
                                  query_chunks))))))))))"
          by (rule after_alpha)
      show ?thesis
        unfolding fields using step
        by (simp add: add.assoc add.commute add.left_commute)
    qed
  qed
  show ?thesis
    using after_alpha_prefix
    unfolding staged_query_search_queries_def staged_alpha_search_queries_def
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_collision_budget_staged_query_challenge_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "hash_collision_budget
      (staged_query_search_queries budgets i)
      (staged_query_challenge_prefix_program A i)"
proof -
  let ?alpha_prefix = "staged_alpha_search_queries budgets 0"
  let ?alpha = "length spec"
  let ?degree = "degree_budget budgets"
  let ?composition_fri =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  let ?query = "sum_list (take i (query_opening_budgets budgets)) + i"
  have alpha_prefix_range:
    "hash_range_budget ?alpha_prefix (staged_alpha_prefix_program A)"
    by (rule hash_range_budget_staged_alpha_prefix_program
        [OF wf controlled])
  have alpha_prefix_coll:
    "hash_collision_budget ?alpha_prefix (staged_alpha_prefix_program A)"
    by (rule hash_collision_budget_staged_alpha_prefix_program
        [OF wf controlled])
  have alpha_range:
    "hash_range_budget ?alpha (staged_alpha_program (length spec))"
    by (rule hash_range_budget_staged_alpha_program)
  have alpha_coll:
    "hash_collision_budget ?alpha (staged_alpha_program (length spec))"
    by (rule hash_collision_budget_staged_alpha_program)
  have degree_range:
    "\<And>as. hash_range_budget ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have degree_coll:
    "\<And>as. hash_collision_budget ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have composition_fri_range:
    "\<And>dg. hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_range_budget_guarded_staged_composition_fri_program
        [OF wf controlled])
  have composition_fri_coll:
    "\<And>dg. hash_collision_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_collision_budget_guarded_staged_composition_fri_program
        [OF wf controlled])
  have composition_final_range:
    "\<And>dg bs. hash_range_budget ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have composition_final_coll:
    "\<And>dg bs. hash_collision_budget ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have query_range: "hash_range_budget ?query (staged_query_program A 0 i)"
  proof -
    have len: "0 + i \<le> length (query_opening_budgets budgets)"
      using wf i_bound unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_range_budget
        (sum_list (take i (drop 0 (query_opening_budgets budgets))) + i)
        (staged_query_program A 0 i)"
      by (rule hash_range_budget_staged_query_program[OF controlled len])
    then show ?thesis by simp
  qed
  have query_coll: "hash_collision_budget ?query (staged_query_program A 0 i)"
  proof -
    have len: "0 + i \<le> length (query_opening_budgets budgets)"
      using wf i_bound unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_collision_budget
        (sum_list (take i (drop 0 (query_opening_budgets budgets))) + i)
        (staged_query_program A 0 i)"
      by (rule hash_collision_budget_staged_query_program[OF controlled len])
    then show ?thesis by simp
  qed
  have after_query_range:
    "\<And>dg composition_final. hash_range_budget (?query + 0)
      (staged_query_program A 0 i \<bind>
        (\<lambda>query_chunks. return (dg, composition_final, query_chunks)))"
    by (rule hash_range_budget_bind)
      (rule query_range, rule hash_range_budget_return)
  have after_query_coll:
    "\<And>dg composition_final. hash_collision_budget (?query + 0)
      (staged_query_program A 0 i \<bind>
        (\<lambda>query_chunks. return (dg, composition_final, query_chunks)))"
    by (rule hash_collision_budget_bind)
      (rule query_range, rule query_coll,
        rule hash_range_budget_return, rule hash_collision_budget_return)
  have after_composition_final_record_range:
    "\<And>dg composition_final. hash_range_budget (0 + (?query + 0))
      (record_staged_message composition_final \<bind>
        (\<lambda>_. staged_query_program A 0 i \<bind>
          (\<lambda>query_chunks. return
            (dg, composition_final, query_chunks))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message, rule after_query_range)
  have after_composition_final_record_coll:
    "\<And>dg composition_final. hash_collision_budget (0 + (?query + 0))
      (record_staged_message composition_final \<bind>
        (\<lambda>_. staged_query_program A 0 i \<bind>
          (\<lambda>query_chunks. return
            (dg, composition_final, query_chunks))))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule hash_collision_budget_record_staged_message,
        rule after_query_range, rule after_query_coll)
  have after_composition_final_range:
    "\<And>dg bs. hash_range_budget
      (?composition_final + (0 + (?query + 0)))
      (composition_final_stage A dg bs \<bind>
        (\<lambda>composition_final.
          record_staged_message composition_final \<bind>
            (\<lambda>_. staged_query_program A 0 i \<bind>
              (\<lambda>query_chunks. return
                (dg, composition_final, query_chunks)))))"
    by (rule hash_range_budget_bind)
      (rule composition_final_range,
        rule after_composition_final_record_range)
  have after_composition_final_coll:
    "\<And>dg bs. hash_collision_budget
      (?composition_final + (0 + (?query + 0)))
      (composition_final_stage A dg bs \<bind>
        (\<lambda>composition_final.
          record_staged_message composition_final \<bind>
            (\<lambda>_. staged_query_program A 0 i \<bind>
              (\<lambda>query_chunks. return
                (dg, composition_final, query_chunks)))))"
    by (rule hash_collision_budget_bind)
      (rule composition_final_range, rule composition_final_coll,
        rule after_composition_final_record_range,
        rule after_composition_final_record_coll)
  have after_composition_fri_range:
    "\<And>dg. hash_range_budget
      (?composition_fri + (?composition_final + (0 + (?query + 0))))
      ((assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])) \<bind>
        (\<lambda>(_, composition_bs).
          composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 i \<bind>
                  (\<lambda>query_chunks. return
                    (dg, composition_final, query_chunks))))))"
  proof (rule hash_range_budget_bind)
    fix dg
    show "hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_range)
  next
    fix dg x
    show "hash_range_budget
      (?composition_final + (0 + (?query + 0)))
      (case x of (_, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 i \<bind>
                (\<lambda>query_chunks. return
                  (dg, composition_final, query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have step:
        "hash_range_budget
          (?composition_final + (0 + (?query + 0)))
          (composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 i \<bind>
                  (\<lambda>query_chunks. return
                    (dg, composition_final, query_chunks)))))"
        by (rule after_composition_final_range)
      show ?thesis
        unfolding Pair using step by simp
    qed
  qed
  have after_composition_fri_coll:
    "\<And>dg. hash_collision_budget
      (?composition_fri + (?composition_final + (0 + (?query + 0))))
      ((assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])) \<bind>
        (\<lambda>(_, composition_bs).
          composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 i \<bind>
                  (\<lambda>query_chunks. return
                    (dg, composition_final, query_chunks))))))"
  proof (rule hash_collision_budget_bind)
    fix dg
    show "hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_range)
    show "hash_collision_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_coll)
  next
    fix dg x
    show "hash_range_budget
      (?composition_final + (0 + (?query + 0)))
      (case x of (_, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 i \<bind>
                (\<lambda>query_chunks. return
                  (dg, composition_final, query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have step:
        "hash_range_budget
          (?composition_final + (0 + (?query + 0)))
          (composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 i \<bind>
                  (\<lambda>query_chunks. return
                    (dg, composition_final, query_chunks)))))"
        by (rule after_composition_final_range)
      show ?thesis
        unfolding Pair using step by simp
    qed
    show "hash_collision_budget
      (?composition_final + (0 + (?query + 0)))
      (case x of (_, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 i \<bind>
                (\<lambda>query_chunks. return
                  (dg, composition_final, query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have step:
        "hash_collision_budget
          (?composition_final + (0 + (?query + 0)))
          (composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 i \<bind>
                  (\<lambda>query_chunks. return
                    (dg, composition_final, query_chunks)))))"
        by (rule after_composition_final_coll)
      show ?thesis
        unfolding Pair using step by simp
    qed
  qed
  have after_composition_fri_range_expanded:
    "\<And>dg. hash_range_budget
      (?composition_fri + (?composition_final + (0 + (?query + 0))))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [] \<bind>
          (\<lambda>(_, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. staged_query_program A 0 i \<bind>
                    (\<lambda>query_chunks. return
                      (dg, composition_final, query_chunks)))))))"
    using after_composition_fri_range
    by (simp add: sm_bind_assoc split: prod.splits)
  have after_composition_fri_coll_expanded:
    "\<And>dg. hash_collision_budget
      (?composition_fri + (?composition_final + (0 + (?query + 0))))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [] \<bind>
          (\<lambda>(_, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. staged_query_program A 0 i \<bind>
                    (\<lambda>query_chunks. return
                      (dg, composition_final, query_chunks)))))))"
    using after_composition_fri_coll
    by (simp add: sm_bind_assoc split: prod.splits)
  have after_degree_record_range:
    "\<And>dg. hash_range_budget
      (0 + (?composition_fri + (?composition_final + (0 + (?query + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. assert
          (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [] \<bind>
            (\<lambda>(_, composition_bs).
              composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  record_staged_message composition_final \<bind>
                    (\<lambda>_. staged_query_program A 0 i \<bind>
                      (\<lambda>query_chunks. return
                        (dg, composition_final, query_chunks))))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule after_composition_fri_range_expanded)
  have after_degree_record_coll:
    "\<And>dg. hash_collision_budget
      (0 + (?composition_fri + (?composition_final + (0 + (?query + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. assert
          (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [] \<bind>
            (\<lambda>(_, composition_bs).
              composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  record_staged_message composition_final \<bind>
                    (\<lambda>_. staged_query_program A 0 i \<bind>
                      (\<lambda>query_chunks. return
                        (dg, composition_final, query_chunks))))))))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule hash_collision_budget_record_staged_message,
        rule after_composition_fri_range_expanded,
        rule after_composition_fri_coll_expanded)
  have after_degree_range:
    "\<And>as. hash_range_budget
      (?degree +
        (0 + (?composition_fri +
          (?composition_final + (0 + (?query + 0))))))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
            assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              composition_rounds [] \<bind>
              (\<lambda>(_, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                      (\<lambda>_. staged_query_program A 0 i \<bind>
                        (\<lambda>query_chunks. return
                          (dg, composition_final, query_chunks)))))))))"
    unfolding Let_def
    by (rule hash_range_budget_bind)
      (rule degree_range, rule after_degree_record_range)
  have after_degree_coll:
    "\<And>as. hash_collision_budget
      (?degree +
        (0 + (?composition_fri +
          (?composition_final + (0 + (?query + 0))))))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
            assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              composition_rounds [] \<bind>
              (\<lambda>(_, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                      (\<lambda>_. staged_query_program A 0 i \<bind>
                        (\<lambda>query_chunks. return
                          (dg, composition_final, query_chunks)))))))))"
    unfolding Let_def
    by (rule hash_collision_budget_bind)
      (rule degree_range, rule degree_coll,
        rule after_degree_record_range, rule after_degree_record_coll)
  have after_alpha_range:
    "\<And>x. hash_range_budget
      (?alpha +
        (?degree +
          (0 + (?composition_fri +
            (?composition_final + (0 + (?query + 0)))))))
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
              assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                composition_rounds [] \<bind>
                (\<lambda>(_, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                        (\<lambda>_. staged_query_program A 0 i \<bind>
                          (\<lambda>query_chunks. return
                            (dg, composition_final, query_chunks))))))))))"
    by (rule hash_range_budget_bind)
      (rule alpha_range, rule after_degree_range)
  have after_alpha_coll:
    "\<And>x. hash_collision_budget
      (?alpha +
        (?degree +
          (0 + (?composition_fri +
            (?composition_final + (0 + (?query + 0)))))))
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
              assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                composition_rounds [] \<bind>
                (\<lambda>(_, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                        (\<lambda>_. staged_query_program A 0 i \<bind>
                          (\<lambda>query_chunks. return
                            (dg, composition_final, query_chunks))))))))))"
    by (rule hash_collision_budget_bind)
      (rule alpha_range, rule alpha_coll,
        rule after_degree_range, rule after_degree_coll)
  have after_alpha_prefix:
    "hash_collision_budget
      (?alpha_prefix +
        (?alpha +
          (?degree +
            (0 + (?composition_fri +
              (?composition_final + (0 + (?query + 0))))))))
      (staged_query_challenge_prefix_program A i)"
    unfolding staged_query_challenge_prefix_program_def
  proof (rule hash_collision_budget_bind)
    show "hash_range_budget ?alpha_prefix
      (staged_alpha_prefix_program A)"
      by (rule alpha_prefix_range)
    show "hash_collision_budget ?alpha_prefix
      (staged_alpha_prefix_program A)"
      by (rule alpha_prefix_coll)
  next
    fix x
    show "hash_range_budget
      (?alpha +
        (?degree +
          (0 + (?composition_fri +
            (?composition_final + (0 + (?query + 0)))))))
      (case x of (_, _, trace_bs, _) \<Rightarrow>
        staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
                assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  composition_rounds [] \<bind>
                  (\<lambda>(_, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                          (\<lambda>_. staged_query_program A 0 i \<bind>
                            (\<lambda>query_chunks. return
                              (dg, composition_final,
                                query_chunks))))))))))"
    proof (cases x)
      case (fields a b c d)
      show ?thesis
        unfolding fields using after_alpha_range
        by (simp add: add.assoc add.commute add.left_commute)
    qed
    show "hash_collision_budget
      (?alpha +
        (?degree +
          (0 + (?composition_fri +
            (?composition_final + (0 + (?query + 0)))))))
      (case x of (_, _, trace_bs, _) \<Rightarrow>
        staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1) in
                assert (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  composition_rounds [] \<bind>
                  (\<lambda>(_, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                          (\<lambda>_. staged_query_program A 0 i \<bind>
                            (\<lambda>query_chunks. return
                              (dg, composition_final,
                                query_chunks))))))))))"
    proof (cases x)
      case (fields a b c d)
      show ?thesis
        unfolding fields using after_alpha_coll
        by (simp add: add.assoc add.commute add.left_commute)
    qed
  qed
  show ?thesis
    using after_alpha_prefix
    unfolding staged_query_search_queries_def staged_alpha_search_queries_def
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma staged_query_prefix_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (staged_query_challenge_prefix_program A i)
      (hash_new_output_hit_event B s) s \<le>
      staged_phase_target_error B
        (staged_query_search_queries budgets i)"
proof -
  have budget:
    "hash_target_budget B (staged_query_search_queries budgets i)
      (staged_query_challenge_prefix_program A i)"
    using hash_target_program_staged_query_challenge_prefix_program
        [OF wf controlled i_bound]
    unfolding hash_target_program_def by simp
  show ?thesis
    using budget unfolding hash_target_budget_def
      staged_phase_target_error_def by blast
qed

end

end
