theory Staged_Security_Experiment_RO_Budgets
  imports Staged_Security_Experiment_Budgets
begin

context soundness
begin

lemma hash_range_budget_ro_staged_alpha_program:
  "hash_range_budget (2 * n) (ro_staged_alpha_program n)"
proof (induction n)
  case 0
  then show ?case by (simp add: hash_range_budget_return)
next
  case (Suc n)
  have challenge: "hash_range_budget 1 receive_alpha_challenge"
    by (rule hash_range_budget_receive_alpha_challenge)
  have record_msg: "hash_range_budget 1 (ro_record_staged_message a)" for a
    by (rule hash_range_budget_ro_record_staged_message)
  have tail_return:
    "hash_range_budget (2 * n + 0)
      (ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))" for a
    by (rule hash_range_budget_bind)
      (rule Suc.IH, rule hash_range_budget_return)
  have after_record:
    "hash_range_budget (1 + (2 * n + 0))
      (ro_record_staged_message a \<bind>
        (\<lambda>_. ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))" for a
    by (rule hash_range_budget_bind)
      (rule record_msg, rule tail_return)
  have "hash_range_budget (1 + (1 + (2 * n + 0)))
      (ro_staged_alpha_program (Suc n))"
    unfolding ro_staged_alpha_program.simps
    by (rule hash_range_budget_bind)
      (rule challenge, rule after_record)
  then show ?case by simp
qed

lemma hash_collision_budget_ro_staged_alpha_program:
  "hash_collision_budget (2 * n) (ro_staged_alpha_program n)"
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
    "hash_range_budget 1 (ro_record_staged_message a)" for a
    by (rule hash_range_budget_ro_record_staged_message)
  have record_coll:
    "hash_collision_budget 1 (ro_record_staged_message a)" for a
    by (rule hash_collision_budget_ro_record_staged_message)
  have tail_return_range:
    "hash_range_budget (2 * n + 0)
      (ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))" for a
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_staged_alpha_program,
        rule hash_range_budget_return)
  have tail_return_coll:
    "hash_collision_budget (2 * n + 0)
      (ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))" for a
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_ro_staged_alpha_program, rule Suc.IH,
        rule hash_range_budget_return, rule hash_collision_budget_return)
  have after_record_range:
    "hash_range_budget (1 + (2 * n + 0))
      (ro_record_staged_message a \<bind>
        (\<lambda>_. ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))" for a
    by (rule hash_range_budget_bind)
      (rule record_range, rule tail_return_range)
  have after_record_coll:
    "hash_collision_budget (1 + (2 * n + 0))
      (ro_record_staged_message a \<bind>
        (\<lambda>_. ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))" for a
    by (rule hash_collision_budget_bind)
      (rule record_range, rule record_coll, rule tail_return_range,
        rule tail_return_coll)
  have "hash_collision_budget (1 + (1 + (2 * n + 0)))
      (ro_staged_alpha_program (Suc n))"
    unfolding ro_staged_alpha_program.simps
    by (rule hash_collision_budget_bind)
      (rule challenge_range, rule challenge_coll, rule after_record_range,
        rule after_record_coll)
  then show ?case by simp
qed

lemma hash_target_program_ro_staged_alpha_program:
  "hash_target_program B (2 * n) (ro_staged_alpha_program n)"
proof (induction n)
  case 0
  then show ?case by (simp add: hash_target_program_return)
next
  case (Suc n)
  have challenge: "hash_target_program B 1 receive_alpha_challenge"
    by (rule hash_target_program_receive_alpha_challenge)
  have record_msg:
    "hash_target_program B 1 (ro_record_staged_message a)" for a
    by (rule hash_target_program_ro_record_staged_message)
  have tail_return:
    "hash_target_program B (2 * n + 0)
      (ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))" for a
    by (rule hash_target_program_bind)
      (rule Suc.IH, rule hash_target_program_return)
  have after_record:
    "hash_target_program B (1 + (2 * n + 0))
      (ro_record_staged_message a \<bind>
        (\<lambda>_. ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))" for a
    by (rule hash_target_program_bind)
      (rule record_msg, rule tail_return)
  have "hash_target_program B (1 + (1 + (2 * n + 0)))
      (ro_staged_alpha_program (Suc n))"
    unfolding ro_staged_alpha_program.simps
    by (rule hash_target_program_bind)
      (rule challenge, rule after_record)
  then show ?case by simp
qed

lemma hash_relation_program_ro_staged_alpha_program:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b (2 * n) (ro_staged_alpha_program n)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: hash_relation_program_zero[OF hash_map_preserving_return])
next
  case (Suc n)
  have challenge:
    "hash_relation_program R b 1 receive_alpha_challenge"
    by (rule hash_relation_program_receive_alpha_challenge[OF fibers])
  have record_msg:
    "hash_relation_program R b 1 (ro_record_staged_message a)" for a
    by (rule hash_relation_program_ro_record_staged_message[OF fibers])
  have tail_return:
    "hash_relation_program R b (2 * n + 0)
      (ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as)))" for a
    by (rule hash_relation_program_bind)
      (rule Suc.IH,
        rule hash_relation_program_zero[OF hash_map_preserving_return])
  have after_record:
    "hash_relation_program R b (1 + (2 * n + 0))
      (ro_record_staged_message a \<bind>
        (\<lambda>_. ro_staged_alpha_program n \<bind> (\<lambda>as. return (a # as))))" for a
    by (rule hash_relation_program_bind)
      (rule record_msg, rule tail_return)
  have "hash_relation_program R b (1 + (1 + (2 * n + 0)))
      (ro_staged_alpha_program (Suc n))"
    unfolding ro_staged_alpha_program.simps
    by (rule hash_relation_program_bind)
      (rule challenge, rule after_record)
  then show ?case by simp
qed

lemma hash_range_budget_ro_staged_trace_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
  shows
    "hash_range_budget
      (sum_list (take n (drop i (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A i n bs)"
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
    "\<And>root. hash_range_budget 1 (ro_record_staged_message root)"
    by (rule hash_range_budget_ro_record_staged_message)
  have challenge: "hash_range_budget 1 receive_trace_fri_challenge"
    by (rule hash_range_budget_receive_trace_fri_challenge)
  have tail:
    "\<And>b. hash_range_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>b root. hash_range_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + 2 * n + 0)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_range_budget_bind)
      (rule tail, simp add: hash_range_budget_return split: prod.splits)
  have after_challenge:
    "\<And>root. hash_range_budget
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          2 * n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b. ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_range_budget_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_range_budget
      (1 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b. ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_range_budget_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_range_budget
      (trace_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_trace_fri_program A i (Suc n) bs)"
    unfolding ro_staged_trace_fri_program.simps
    by (rule hash_range_budget_bind)
      (rule stage, rule after_record)
  have budget_eq:
    "trace_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              2 * n + 0))) =
      sum_list (take (Suc n) (drop i (trace_fri_budgets budgets))) + 2 * Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_collision_budget_ro_staged_trace_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
  shows
    "hash_collision_budget
      (sum_list (take n (drop i (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A i n bs)"
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
    "\<And>root. hash_range_budget 1 (ro_record_staged_message root)"
    by (rule hash_range_budget_ro_record_staged_message)
  have record_coll:
    "\<And>root. hash_collision_budget 1 (ro_record_staged_message root)"
    by (rule hash_collision_budget_ro_record_staged_message)
  have challenge_range: "hash_range_budget 1 receive_trace_fri_challenge"
    by (rule hash_range_budget_receive_trace_fri_challenge)
  have challenge_coll: "hash_collision_budget 1 receive_trace_fri_challenge"
    by (rule hash_collision_budget_receive_trace_fri_challenge)
  have tail_range:
    "\<And>b. hash_range_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b]))"
    by (rule hash_range_budget_ro_staged_trace_fri_program[OF controlled])
      (use Suc.prems in simp)
  have tail_coll:
    "\<And>b. hash_collision_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return_range:
    "\<And>b root. hash_range_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + 2 * n + 0)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_range_budget_bind)
      (rule tail_range, simp add: hash_range_budget_return split: prod.splits)
  have tail_return_coll:
    "\<And>b root. hash_collision_budget
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + 2 * n + 0)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_collision_budget_bind)
      (rule tail_range, rule tail_coll,
        simp add: hash_range_budget_return split: prod.splits,
        simp add: hash_collision_budget_return split: prod.splits)
  have after_challenge_range:
    "\<And>root. hash_range_budget
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          2 * n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b. ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_range_budget_bind)
      (rule challenge_range, rule tail_return_range)
  have after_challenge_coll:
    "\<And>root. hash_collision_budget
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          2 * n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b. ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_collision_budget_bind)
      (rule challenge_range, rule challenge_coll, rule tail_return_range,
        rule tail_return_coll)
  have after_record_range:
    "\<And>root. hash_range_budget
      (1 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b. ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_range_budget_bind)
      (rule record_range, rule after_challenge_range)
  have after_record_coll:
    "\<And>root. hash_collision_budget
      (1 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b. ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_collision_budget_bind)
      (rule record_range, rule record_coll, rule after_challenge_range,
        rule after_challenge_coll)
  have whole:
    "hash_collision_budget
      (trace_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_trace_fri_program A i (Suc n) bs)"
    unfolding ro_staged_trace_fri_program.simps
    by (rule hash_collision_budget_bind)
      (rule stage_range, rule stage_coll, rule after_record_range,
        rule after_record_coll)
  have budget_eq:
    "trace_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              2 * n + 0))) =
      sum_list (take (Suc n) (drop i (trace_fri_budgets budgets))) + 2 * Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_range_budget_ro_staged_composition_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
  shows
    "hash_range_budget
      (sum_list (take n (drop i (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg i n bs)"
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
    "\<And>root. hash_range_budget 1 (ro_record_staged_message root)"
    by (rule hash_range_budget_ro_record_staged_message)
  have challenge:
    "hash_range_budget 1 receive_composition_fri_challenge"
    by (rule hash_range_budget_receive_composition_fri_challenge)
  have tail:
    "\<And>b. hash_range_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>b root. hash_range_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n + 0)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_range_budget_bind)
      (rule tail, simp add: hash_range_budget_return split: prod.splits)
  have after_challenge:
    "\<And>root. hash_range_budget
      (1 +
        (sum_list
          (take n (drop (Suc i) (composition_fri_budgets budgets))) +
          2 * n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b. ro_staged_composition_fri_program A dg (Suc i) n
          (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_range_budget_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_range_budget
      (1 +
        (1 +
          (sum_list
            (take n (drop (Suc i) (composition_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_composition_fri_challenge \<bind>
          (\<lambda>b. ro_staged_composition_fri_program A dg (Suc i) n
            (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_range_budget_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_range_budget
      (composition_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_composition_fri_program A dg i (Suc n) bs)"
    unfolding ro_staged_composition_fri_program.simps
    by (rule hash_range_budget_bind)
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

lemma hash_collision_budget_ro_staged_composition_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
  shows
    "hash_collision_budget
      (sum_list (take n (drop i (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg i n bs)"
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
    "\<And>root. hash_range_budget 1 (ro_record_staged_message root)"
    by (rule hash_range_budget_ro_record_staged_message)
  have record_coll:
    "\<And>root. hash_collision_budget 1 (ro_record_staged_message root)"
    by (rule hash_collision_budget_ro_record_staged_message)
  have challenge_range:
    "hash_range_budget 1 receive_composition_fri_challenge"
    by (rule hash_range_budget_receive_composition_fri_challenge)
  have challenge_coll:
    "hash_collision_budget 1 receive_composition_fri_challenge"
    by (rule hash_collision_budget_receive_composition_fri_challenge)
  have tail_range:
    "\<And>b. hash_range_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b]))"
    by (rule hash_range_budget_ro_staged_composition_fri_program
        [OF controlled])
      (use Suc.prems in simp)
  have tail_coll:
    "\<And>b. hash_collision_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return_range:
    "\<And>b root. hash_range_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n + 0)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_range_budget_bind)
      (rule tail_range, simp add: hash_range_budget_return split: prod.splits)
  have tail_return_coll:
    "\<And>b root. hash_collision_budget
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n + 0)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b]) \<bind>
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
          2 * n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b. ro_staged_composition_fri_program A dg (Suc i) n
          (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_range_budget_bind)
      (rule challenge_range, rule tail_return_range)
  have after_challenge_coll:
    "\<And>root. hash_collision_budget
      (1 +
        (sum_list
          (take n (drop (Suc i) (composition_fri_budgets budgets))) +
          2 * n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b. ro_staged_composition_fri_program A dg (Suc i) n
          (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_collision_budget_bind)
      (rule challenge_range, rule challenge_coll, rule tail_return_range,
        rule tail_return_coll)
  have after_record_range:
    "\<And>root. hash_range_budget
      (1 +
        (1 +
          (sum_list
            (take n (drop (Suc i) (composition_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_composition_fri_challenge \<bind>
          (\<lambda>b. ro_staged_composition_fri_program A dg (Suc i) n
            (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_range_budget_bind)
      (rule record_range, rule after_challenge_range)
  have after_record_coll:
    "\<And>root. hash_collision_budget
      (1 +
        (1 +
          (sum_list
            (take n (drop (Suc i) (composition_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_composition_fri_challenge \<bind>
          (\<lambda>b. ro_staged_composition_fri_program A dg (Suc i) n
            (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_collision_budget_bind)
      (rule record_range, rule record_coll, rule after_challenge_range,
        rule after_challenge_coll)
  have whole:
    "hash_collision_budget
      (composition_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_composition_fri_program A dg i (Suc n) bs)"
    unfolding ro_staged_composition_fri_program.simps
    by (rule hash_collision_budget_bind)
      (rule stage_range, rule stage_coll, rule after_record_range,
        rule after_record_coll)
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

lemma hash_target_program_ro_staged_trace_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
  shows
    "hash_target_program B
      (sum_list (take n (drop i (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A i n bs)"
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
    "\<And>root. hash_target_program B 1 (ro_record_staged_message root)"
    by (rule hash_target_program_ro_record_staged_message)
  have challenge: "hash_target_program B 1 receive_trace_fri_challenge"
    by (rule hash_target_program_receive_trace_fri_challenge)
  have tail:
    "\<And>b. hash_target_program B
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>b root. hash_target_program B
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + 2 * n + 0)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_target_program_bind)
      (rule tail, simp add: hash_target_program_return split: prod.splits)
  have after_challenge:
    "\<And>root. hash_target_program B
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          2 * n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b. ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_target_program_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_target_program B
      (1 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b. ro_staged_trace_fri_program A (Suc i) n (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_target_program_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_target_program B
      (trace_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_trace_fri_program A i (Suc n) bs)"
    unfolding ro_staged_trace_fri_program.simps
    by (rule hash_target_program_bind)
      (rule stage, rule after_record)
  have budget_eq:
    "trace_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              2 * n + 0))) =
      sum_list (take (Suc n) (drop i (trace_fri_budgets budgets))) + 2 * Suc n"
    using sum_list_take_Suc_drop[OF i_bound, of n] by simp
  show ?case
    using whole unfolding budget_eq .
qed

lemma hash_target_program_ro_staged_composition_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
  shows
    "hash_target_program B
      (sum_list (take n (drop i (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg i n bs)"
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
    "\<And>root. hash_target_program B 1 (ro_record_staged_message root)"
    by (rule hash_target_program_ro_record_staged_message)
  have challenge:
    "hash_target_program B 1 receive_composition_fri_challenge"
    by (rule hash_target_program_receive_composition_fri_challenge)
  have tail:
    "\<And>b. hash_target_program B
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b]))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>b root. hash_target_program B
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n + 0)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b]) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_target_program_bind)
      (rule tail, simp add: hash_target_program_return split: prod.splits)
  have after_challenge:
    "\<And>root. hash_target_program B
      (1 +
        (sum_list
          (take n (drop (Suc i) (composition_fri_budgets budgets))) +
          2 * n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b. ro_staged_composition_fri_program A dg (Suc i) n
          (bs @ [b]) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_target_program_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_target_program B
      (1 +
        (1 +
          (sum_list
            (take n (drop (Suc i) (composition_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_composition_fri_challenge \<bind>
          (\<lambda>b. ro_staged_composition_fri_program A dg (Suc i) n
            (bs @ [b]) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_target_program_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_target_program B
      (composition_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_composition_fri_program A dg i (Suc n) bs)"
    unfolding ro_staged_composition_fri_program.simps
    by (rule hash_target_program_bind)
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

lemma hash_relation_program_ro_staged_trace_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (sum_list (take n (drop i (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A i n bs)"
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
    "\<And>root. hash_relation_program R b 1 (ro_record_staged_message root)"
    by (rule hash_relation_program_ro_record_staged_message[OF fibers])
  have challenge:
    "hash_relation_program R b 1 receive_trace_fri_challenge"
    by (rule hash_relation_program_receive_trace_fri_challenge[OF fibers])
  have tail:
    "\<And>root b'. hash_relation_program R b
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) + 2 * n)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b']))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>root b'. hash_relation_program R b
      (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
        2 * n + 0)
      (ro_staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
        (\<lambda>(roots, bs'). return (root # roots, bs')))"
    by (rule hash_relation_program_bind)
      (rule tail,
        simp add: hash_relation_program_zero[OF hash_map_preserving_return]
          split: prod.splits)
  have after_challenge:
    "\<And>root. hash_relation_program R b
      (1 +
        (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
          2 * n + 0))
      (receive_trace_fri_challenge \<bind>
        (\<lambda>b'. ro_staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_relation_program_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_relation_program R b
      (1 +
        (1 +
          (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
            2 * n + 0)))
      (ro_record_staged_message root \<bind>
        (\<lambda>_. receive_trace_fri_challenge \<bind>
          (\<lambda>b'. ro_staged_trace_fri_program A (Suc i) n (bs @ [b']) \<bind>
            (\<lambda>(roots, bs'). return (root # roots, bs')))))"
    by (rule hash_relation_program_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_relation_program R b
      (trace_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list (take n (drop (Suc i) (trace_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_trace_fri_program A i (Suc n) bs)"
    unfolding ro_staged_trace_fri_program.simps
    by (rule hash_relation_program_bind)
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

lemma hash_relation_program_ro_staged_composition_fri_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (sum_list (take n (drop i (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg i n bs)"
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
    "\<And>root. hash_relation_program R b 1 (ro_record_staged_message root)"
    by (rule hash_relation_program_ro_record_staged_message[OF fibers])
  have challenge:
    "hash_relation_program R b 1 receive_composition_fri_challenge"
    by (rule
        hash_relation_program_receive_composition_fri_challenge[OF fibers])
  have tail:
    "\<And>root b'. hash_relation_program R b
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b']))"
    by (rule Suc.IH) (use Suc.prems in simp)
  have tail_return:
    "\<And>root b'. hash_relation_program R b
      (sum_list
        (take n (drop (Suc i) (composition_fri_budgets budgets))) + 2 * n + 0)
      (ro_staged_composition_fri_program A dg (Suc i) n (bs @ [b']) \<bind>
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
          2 * n + 0))
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b'. ro_staged_composition_fri_program A dg (Suc i) n
          (bs @ [b']) \<bind>
          (\<lambda>(roots, bs'). return (root # roots, bs'))))"
    by (rule hash_relation_program_bind)
      (rule challenge, rule tail_return)
  have after_record:
    "\<And>root. hash_relation_program R b
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
    by (rule hash_relation_program_bind)
      (rule record_budget, rule after_challenge)
  have whole:
    "hash_relation_program R b
      (composition_fri_budgets budgets ! i +
        (1 +
          (1 +
            (sum_list
              (take n (drop (Suc i) (composition_fri_budgets budgets))) +
              2 * n + 0))))
      (ro_staged_composition_fri_program A dg i (Suc n) bs)"
    unfolding ro_staged_composition_fri_program.simps
    by (rule hash_relation_program_bind)
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

lemma hash_range_budget_guarded_ro_staged_composition_fri_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (sum_list (composition_fri_budgets budgets) +
        2 * ceil_log (maxDegree + 1))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
proof -
  let ?B =
    "sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1)"
  have "hash_range_budget (0 + ?B)
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
      (\<lambda>_. ro_staged_composition_fri_program A dg 0
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
        2 * ceil_log (to_nat dg + 1))
      (ro_staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) [])"
    by (rule hash_range_budget_ro_staged_composition_fri_program
        [OF controlled len])
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
  show "hash_range_budget
    (sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1))
    (ro_staged_composition_fri_program A dg 0
      (ceil_log (to_nat dg + 1)) [])"
    by (rule hash_range_budget_mono[OF le exact])
  qed
  then show ?thesis by simp
qed

lemma hash_collision_budget_guarded_ro_staged_composition_fri_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (sum_list (composition_fri_budgets budgets) +
        2 * ceil_log (maxDegree + 1))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
proof -
  let ?B =
    "sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1)"
  have "hash_collision_budget (0 + ?B)
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
      (\<lambda>_. ro_staged_composition_fri_program A dg 0
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
        2 * ceil_log (to_nat dg + 1))
      (ro_staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) [])"
    by (rule hash_range_budget_ro_staged_composition_fri_program
        [OF controlled len])
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
  show "hash_range_budget
    (sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1))
    (ro_staged_composition_fri_program A dg 0
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
        2 * ceil_log (to_nat dg + 1))
      (ro_staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) [])"
    by (rule hash_collision_budget_ro_staged_composition_fri_program
        [OF controlled len])
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
  show "hash_collision_budget
    (sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1))
    (ro_staged_composition_fri_program A dg 0
      (ceil_log (to_nat dg + 1)) [])"
    by (rule hash_collision_budget_mono[OF le exact])
  qed
  then show ?thesis by simp
qed

lemma hash_target_program_guarded_ro_staged_composition_fri_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (sum_list (composition_fri_budgets budgets) +
        2 * ceil_log (maxDegree + 1))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
proof -
  let ?B =
    "sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1)"
  have "hash_target_program B (0 + ?B)
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
      (\<lambda>_. ro_staged_composition_fri_program A dg 0
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
          2 * ceil_log (to_nat dg + 1))
        (ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])"
      by (rule hash_target_program_ro_staged_composition_fri_program
          [OF controlled len])
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
    show "hash_target_program B
      (sum_list (composition_fri_budgets budgets) +
        2 * ceil_log (maxDegree + 1))
      (ro_staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) [])"
      by (rule hash_target_program_mono[OF le exact])
  qed
  then show ?thesis by simp
qed

lemma hash_relation_program_guarded_ro_staged_composition_fri_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (sum_list (composition_fri_budgets budgets) +
        2 * ceil_log (maxDegree + 1))
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
proof -
  let ?B =
    "sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1)"
  have "hash_relation_program R b (0 + ?B)
    (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
      (\<lambda>_. ro_staged_composition_fri_program A dg 0
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
          2 * ceil_log (to_nat dg + 1))
        (ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])"
      by (rule hash_relation_program_ro_staged_composition_fri_program
          [OF controlled len fibers])
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
    show "hash_relation_program R b ?B
      (ro_staged_composition_fri_program A dg 0
        (ceil_log (to_nat dg + 1)) [])"
      by (rule hash_relation_program_mono[OF le exact])
  qed
  then show ?thesis by simp
qed

definition ro_checked_query_round_transcript_bound :: nat where
  "ro_checked_query_round_transcript_bound =
    query_decommitment_transcript_length 0 +
    fri_layers_transcript_length (ceil_log clength) (clength * scale) +
    fri_layers_transcript_length (ceil_log (maxDegree + 1))
      (clength * scale)"

lemma fri_layers_transcript_length_mono_layers:
  assumes "m \<le> n"
  shows "fri_layers_transcript_length m len \<le>
    fri_layers_transcript_length n len"
  using assms
proof (induction m arbitrary: n len)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then obtain n' where n_eq: "n = Suc n'"
    by (cases n) simp_all
  have "m \<le> n'"
    using Suc.prems n_eq by simp
  then have tail:
    "fri_layers_transcript_length m (len div 2) \<le>
      fri_layers_transcript_length n' (len div 2)"
    by (rule Suc.IH)
  show ?case
    unfolding n_eq using tail by simp
qed

lemma verifier_query_round_transcript_length_le_ro_checked_query_round_transcript_bound:
  assumes trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots \<le> ceil_log (maxDegree + 1)"
  shows
    "verifier_query_round_transcript_length 0 trace_roots
      composition_roots \<le> ro_checked_query_round_transcript_bound"
  unfolding verifier_query_round_transcript_length_def
    ro_checked_query_round_transcript_bound_def
  using trace_len
    fri_layers_transcript_length_mono_layers[OF composition_len,
      of "clength * scale"]
  by simp

lemma hash_range_budget_ro_checked_staged_query_program_closed:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots \<le> ceil_log (maxDegree + 1)"
  shows
    "hash_range_budget
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
    "hash_range_budget ?exact
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
    by (rule hash_range_budget_ro_checked_staged_query_program
        [OF controlled bound])
  have len_le:
    "verifier_query_round_transcript_length 0 trace_roots composition_roots \<le>
      ro_checked_query_round_transcript_bound"
    by (rule
        verifier_query_round_transcript_length_le_ro_checked_query_round_transcript_bound
        [OF trace_len composition_len])
  have le: "?exact \<le> ?closed"
    using len_le by simp
  show ?thesis
    by (rule hash_range_budget_mono[OF le exact])
qed

lemma hash_collision_budget_ro_checked_staged_query_program_closed:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots \<le> ceil_log (maxDegree + 1)"
  shows
    "hash_collision_budget
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
    "hash_collision_budget ?exact
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
    by (rule hash_collision_budget_ro_checked_staged_query_program
        [OF controlled bound])
  have len_le:
    "verifier_query_round_transcript_length 0 trace_roots composition_roots \<le>
      ro_checked_query_round_transcript_bound"
    by (rule
        verifier_query_round_transcript_length_le_ro_checked_query_round_transcript_bound
        [OF trace_len composition_len])
  have le: "?exact \<le> ?closed"
    using len_le by simp
  show ?thesis
    by (rule hash_collision_budget_mono[OF le exact])
qed

lemma hash_target_program_ro_checked_staged_query_program_closed:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots \<le> ceil_log (maxDegree + 1)"
  shows
    "hash_target_program B
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
    "hash_target_program B ?exact
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
    by (rule hash_target_program_ro_checked_staged_query_program
        [OF controlled bound])
  have len_le:
    "verifier_query_round_transcript_length 0 trace_roots composition_roots \<le>
      ro_checked_query_round_transcript_bound"
    by (rule
        verifier_query_round_transcript_length_le_ro_checked_query_round_transcript_bound
        [OF trace_len composition_len])
  have le: "?exact \<le> ?closed"
    using len_le by simp
  show ?thesis
    by (rule hash_target_program_mono[OF le exact])
qed

lemma hash_relation_program_ro_checked_staged_query_program_closed:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
    and trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots \<le> ceil_log (maxDegree + 1)"
  shows
    "hash_relation_program R b
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
    "hash_relation_program R b ?exact
      (ro_checked_staged_query_program A trace_roots composition_roots i n)"
    by (rule hash_relation_program_ro_checked_staged_query_program
        [OF controlled bound fibers])
  have len_le:
    "verifier_query_round_transcript_length 0 trace_roots composition_roots \<le>
      ro_checked_query_round_transcript_bound"
    by (rule
        verifier_query_round_transcript_length_le_ro_checked_query_round_transcript_bound
        [OF trace_len composition_len])
  have le: "?exact \<le> ?closed"
    using len_le by simp
  show ?thesis
    by (rule hash_relation_program_mono[OF le exact])
qed

end

end
