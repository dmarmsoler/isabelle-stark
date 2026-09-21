(*  Title:      Stark/Soundness_Merkle_Prefix_Target_Staged.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Merkle_Prefix_Target_Staged
  imports
    Soundness_Merkle_Prefix_Target
    Soundness_Oracle_Dynamic_Target
begin

text \<open>
  Staged wrappers for the prefix-fixed Merkle target reduction.  Trace and
  composition paths share one two-root target set fixed before the current
  query challenge is received.
\<close>

context soundness
begin

definition query_prefix_merkle_roots
  :: "'f staged_query_prefix_data \<Rightarrow> 'f set"
where
  "query_prefix_merkle_roots prefix =
    insert (sqp_trace_root prefix)
      (if sqp_composition_fri_roots prefix = []
       then {}
       else {hd (sqp_composition_fri_roots prefix)})"

lemma finite_query_prefix_merkle_roots[simp]:
  "finite (query_prefix_merkle_roots prefix)"
  unfolding query_prefix_merkle_roots_def by simp

lemma card_query_prefix_merkle_roots_le:
  "card (query_prefix_merkle_roots prefix) \<le> 2"
  unfolding query_prefix_merkle_roots_def
  by (cases "sqp_composition_fri_roots prefix = []")
    (simp_all add: card_insert_if)

definition checked_staged_security_with_query_prefix_current_path_prefix_target_hit_at
where
  "checked_staged_security_with_query_prefix_current_path_prefix_target_hit_at
      i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        hash_map_new_output_hit
          (merkle_prefix_path_targets
            (query_prefix_merkle_roots prefix) prefix_state)
          prefix_state final_state)"

definition checked_staged_security_with_query_prefix_final_collision_hit_at
where
  "checked_staged_security_with_query_prefix_final_collision_hit_at i out
      \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        hash_map_output_collision final_state)"

lemma checked_staged_security_with_query_prefix_structured_path_imp_collision_or_prefix_target_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i out \<or>
       checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i out"
  shows
    "checked_staged_security_with_query_prefix_final_collision_hit_at i out \<or>
     checked_staged_security_with_query_prefix_current_path_prefix_target_hit_at
       i out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_query_prefix_current_trace_path_output_hit_at_def
      checked_staged_security_with_query_prefix_current_composition_path_output_hit_at_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
    "out =
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)"
    by (cases packed) (auto split: prod.splits)
  have support':
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    using support unfolding out_eq .
  have ext: "prefix_state \<le> final_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_prefix_extends_final
        [OF wf controlled i_bound support'])
  have trace_root_eq:
    "staged_trace_root data = sqp_trace_root prefix"
    using support'
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
      checked_staged_after_query_prefix_receive_with_verifier_def
      checked_staged_after_query_prefix_receive_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have composition_roots_eq:
    "staged_composition_fri_roots data =
      sqp_composition_fri_roots prefix"
    using support'
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
      checked_staged_after_query_prefix_receive_with_verifier_def
      checked_staged_after_query_prefix_receive_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  from hit show ?thesis
  proof
    assume trace_hit:
      "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out"
    then obtain opn :: "'f authenticated_opening" where
      root: "opening_root opn = staged_trace_root data"
      and len: "opening_length opn = scale * clength"
      and auth: "authenticated_opening_in final_state opn"
      and path_hit:
        "hash_map_new_output_hit
          (merkle_path_target_roots final_state
            (staged_trace_root data)
            (scale * clength)
            (opening_index opn)
            (opening_value opn)
            (opening_path opn))
          prefix_state final_state"
      using out_eq
      by (auto simp add:
        checked_staged_security_with_query_prefix_current_trace_path_output_hit_at_def)
    have opening_hit:
      "hash_map_new_output_hit
        (merkle_path_target_roots final_state
          (opening_root opn)
          (opening_length opn)
          (opening_index opn)
          (opening_value opn)
          (opening_path opn))
        prefix_state final_state"
      using root len path_hit by simp
    from authenticated_opening_target_hit_imp_collision_or_prefix_target_hit
        [OF ext auth opening_hit]
    show ?thesis
    proof
      assume collision: "hash_map_output_collision final_state"
      have
        "checked_staged_security_with_query_prefix_final_collision_hit_at i out"
        unfolding out_eq
          checked_staged_security_with_query_prefix_final_collision_hit_at_def
        using collision by simp
      then show ?thesis by simp
    next
      assume target:
        "hash_map_new_output_hit
          (merkle_prefix_path_targets {opening_root opn} prefix_state)
          prefix_state final_state"
      have roots_subset:
        "{opening_root opn} \<subseteq> query_prefix_merkle_roots prefix"
        using root trace_root_eq
        unfolding query_prefix_merkle_roots_def by simp
      have target_subset:
        "merkle_prefix_path_targets {opening_root opn} prefix_state
          \<subseteq>
         merkle_prefix_path_targets
          (query_prefix_merkle_roots prefix) prefix_state"
        by (rule merkle_prefix_path_targets_mono[OF roots_subset])
      have target':
        "hash_map_new_output_hit
          (merkle_prefix_path_targets
            (query_prefix_merkle_roots prefix) prefix_state)
          prefix_state final_state"
        by (rule hash_map_new_output_hit_subset[OF target_subset target])
      have
        "checked_staged_security_with_query_prefix_current_path_prefix_target_hit_at
          i out"
        unfolding out_eq
          checked_staged_security_with_query_prefix_current_path_prefix_target_hit_at_def
        using target' by simp
      then show ?thesis by simp
    qed
  next
    assume composition_hit:
      "checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i out"
    then obtain opn :: "'f authenticated_opening" where
      nonempty: "staged_composition_fri_roots data \<noteq> []"
      and root:
        "opening_root opn = hd (staged_composition_fri_roots data)"
      and len: "opening_length opn = scale * clength"
      and auth: "authenticated_opening_in final_state opn"
      and path_hit:
        "hash_map_new_output_hit
          (merkle_path_target_roots final_state
            (hd (staged_composition_fri_roots data))
            (scale * clength)
            (opening_index opn)
            (opening_value opn)
            (opening_path opn))
          prefix_state final_state"
      using out_eq
      by (auto simp add:
        checked_staged_security_with_query_prefix_current_composition_path_output_hit_at_def)
    have opening_hit:
      "hash_map_new_output_hit
        (merkle_path_target_roots final_state
          (opening_root opn)
          (opening_length opn)
          (opening_index opn)
          (opening_value opn)
          (opening_path opn))
        prefix_state final_state"
      using root len path_hit by simp
    from authenticated_opening_target_hit_imp_collision_or_prefix_target_hit
        [OF ext auth opening_hit]
    show ?thesis
    proof
      assume collision: "hash_map_output_collision final_state"
      have
        "checked_staged_security_with_query_prefix_final_collision_hit_at i out"
        unfolding out_eq
          checked_staged_security_with_query_prefix_final_collision_hit_at_def
        using collision by simp
      then show ?thesis by simp
    next
      assume target:
        "hash_map_new_output_hit
          (merkle_prefix_path_targets {opening_root opn} prefix_state)
          prefix_state final_state"
      have prefix_nonempty:
        "sqp_composition_fri_roots prefix \<noteq> []"
        using nonempty composition_roots_eq by simp
      have roots_subset:
        "{opening_root opn} \<subseteq> query_prefix_merkle_roots prefix"
        using root composition_roots_eq prefix_nonempty
        unfolding query_prefix_merkle_roots_def by simp
      have target_subset:
        "merkle_prefix_path_targets {opening_root opn} prefix_state
          \<subseteq>
         merkle_prefix_path_targets
          (query_prefix_merkle_roots prefix) prefix_state"
        by (rule merkle_prefix_path_targets_mono[OF roots_subset])
      have target':
        "hash_map_new_output_hit
          (merkle_prefix_path_targets
            (query_prefix_merkle_roots prefix) prefix_state)
          prefix_state final_state"
        by (rule hash_map_new_output_hit_subset[OF target_subset target])
      have
        "checked_staged_security_with_query_prefix_current_path_prefix_target_hit_at
          i out"
        unfolding out_eq
          checked_staged_security_with_query_prefix_current_path_prefix_target_hit_at_def
        using target' by simp
      then show ?thesis by simp
    qed
  qed
qed


definition staged_query_prefix_tail_hash_queries
  :: "staged_budgets \<Rightarrow> nat \<Rightarrow> nat"
where
  "staged_query_prefix_tail_hash_queries budgets i =
    1 +
    query_opening_budgets budgets ! i +
    (sum_list
      (take (rounds - Suc i)
        (drop (Suc i) (query_opening_budgets budgets))) +
      (rounds - Suc i)) +
    verifier_hash_query_budget"

lemma hash_target_program_checked_staged_after_query_prefix_receive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "hash_target_program B
      (query_opening_budgets budgets ! i +
        (sum_list
          (take (rounds - Suc i)
            (drop (Suc i) (query_opening_budgets budgets))) +
          (rounds - Suc i)))
      (checked_staged_after_query_prefix_receive A i prefix_pack)"
proof -
  obtain prefix prefix_state raw where pack_eq:
    "prefix_pack = ((prefix, prefix_state), raw)"
    by (cases prefix_pack; cases "fst prefix_pack") auto
  let ?suffix =
    "sum_list
      (take (rounds - Suc i)
        (drop (Suc i) (query_opening_budgets budgets))) +
      (rounds - Suc i)"
  have i_len: "i < length (query_opening_budgets budgets)"
    using wf i_bound
    unfolding staged_budget_wellformed_def by simp
  have current:
    "hash_target_program B (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_len
    unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have suffix_bound:
    "Suc i + (rounds - Suc i) \<le>
      length (query_opening_budgets budgets)"
    using wf i_bound
    unfolding staged_budget_wellformed_def by simp
  have suffix:
    "hash_target_program B ?suffix
      (checked_staged_query_program A
        (sqp_trace_fri_roots prefix)
        (sqp_composition_fri_roots prefix)
        (Suc i) (rounds - Suc i))"
    by (rule hash_target_program_checked_staged_query_program
        [OF controlled suffix_bound])
  have suffix_return:
    "\<And>chunk. hash_target_program B (?suffix + 0)
      (checked_staged_query_program A
        (sqp_trace_fri_roots prefix)
        (sqp_composition_fri_roots prefix)
        (Suc i) (rounds - Suc i) \<bind>
       (\<lambda>suffix_chunks.
         return
          \<lparr>staged_trace_root = sqp_trace_root prefix,
           staged_trace_fri_roots = sqp_trace_fri_roots prefix,
           staged_trace_fri_challenges = sqp_trace_fri_challenges prefix,
           staged_trace_final = sqp_trace_final prefix,
           staged_alphas = sqp_alphas prefix,
           staged_degree = sqp_degree prefix,
           staged_composition_fri_roots =
             sqp_composition_fri_roots prefix,
           staged_composition_fri_challenges =
             sqp_composition_fri_challenges prefix,
           staged_composition_final = sqp_composition_final prefix,
           staged_query_chunks =
             sqp_query_chunks prefix @ chunk # suffix_chunks\<rparr>))"
    by (rule hash_target_program_bind)
      (rule suffix, rule hash_target_program_return)
  have record_tail:
    "\<And>chunk. hash_target_program B (0 + (?suffix + 0))
      (record_staged_messages chunk \<bind>
       (\<lambda>_. checked_staged_query_program A
        (sqp_trace_fri_roots prefix)
        (sqp_composition_fri_roots prefix)
        (Suc i) (rounds - Suc i) \<bind>
       (\<lambda>suffix_chunks.
         return
          \<lparr>staged_trace_root = sqp_trace_root prefix,
           staged_trace_fri_roots = sqp_trace_fri_roots prefix,
           staged_trace_fri_challenges = sqp_trace_fri_challenges prefix,
           staged_trace_final = sqp_trace_final prefix,
           staged_alphas = sqp_alphas prefix,
           staged_degree = sqp_degree prefix,
           staged_composition_fri_roots =
             sqp_composition_fri_roots prefix,
           staged_composition_fri_challenges =
             sqp_composition_fri_challenges prefix,
           staged_composition_final = sqp_composition_final prefix,
           staged_query_chunks =
             sqp_query_chunks prefix @ chunk # suffix_chunks\<rparr>)))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_messages, rule suffix_return)
  have assert_tail:
    "\<And>chunk. hash_target_program B (0 + (0 + (?suffix + 0)))
      (assert
        (verifier_query_round_chunk (index (to_nat raw))
          (sqp_trace_fri_roots prefix)
          (sqp_composition_fri_roots prefix) chunk) \<bind>
       (\<lambda>_. record_staged_messages chunk \<bind>
       (\<lambda>_. checked_staged_query_program A
        (sqp_trace_fri_roots prefix)
        (sqp_composition_fri_roots prefix)
        (Suc i) (rounds - Suc i) \<bind>
       (\<lambda>suffix_chunks.
         return
          \<lparr>staged_trace_root = sqp_trace_root prefix,
           staged_trace_fri_roots = sqp_trace_fri_roots prefix,
           staged_trace_fri_challenges = sqp_trace_fri_challenges prefix,
           staged_trace_final = sqp_trace_final prefix,
           staged_alphas = sqp_alphas prefix,
           staged_degree = sqp_degree prefix,
           staged_composition_fri_roots =
             sqp_composition_fri_roots prefix,
           staged_composition_fri_challenges =
             sqp_composition_fri_challenges prefix,
           staged_composition_final = sqp_composition_final prefix,
           staged_query_chunks =
             sqp_query_chunks prefix @ chunk # suffix_chunks\<rparr>))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_assert, rule record_tail)
  have whole:
    "hash_target_program B
      (query_opening_budgets budgets ! i +
        (0 + (0 + (?suffix + 0))))
      (query_opening_stage A i raw \<bind>
       (\<lambda>chunk. assert
        (verifier_query_round_chunk (index (to_nat raw))
          (sqp_trace_fri_roots prefix)
          (sqp_composition_fri_roots prefix) chunk) \<bind>
       (\<lambda>_. record_staged_messages chunk \<bind>
       (\<lambda>_. checked_staged_query_program A
        (sqp_trace_fri_roots prefix)
        (sqp_composition_fri_roots prefix)
        (Suc i) (rounds - Suc i) \<bind>
       (\<lambda>suffix_chunks.
         return
          \<lparr>staged_trace_root = sqp_trace_root prefix,
           staged_trace_fri_roots = sqp_trace_fri_roots prefix,
           staged_trace_fri_challenges = sqp_trace_fri_challenges prefix,
           staged_trace_final = sqp_trace_final prefix,
           staged_alphas = sqp_alphas prefix,
           staged_degree = sqp_degree prefix,
           staged_composition_fri_roots =
             sqp_composition_fri_roots prefix,
           staged_composition_fri_challenges =
             sqp_composition_fri_challenges prefix,
           staged_composition_final = sqp_composition_final prefix,
           staged_query_chunks =
             sqp_query_chunks prefix @ chunk # suffix_chunks\<rparr>)))))"
    by (rule hash_target_program_bind)
      (rule current, rule assert_tail)
  show ?thesis
    using whole
    unfolding checked_staged_after_query_prefix_receive_def pack_eq Let_def
    by simp
qed



definition verifier_state_transfer_with_saved
  :: "'f list \<Rightarrow>
      ('f protocol_channel, 'f protocol_channel) state_monad"
where
  "verifier_state_transfer_with_saved tr =
    get \<bind> (\<lambda>s.
      put (verifier_state_from_adversary s tr) \<bind>
        (\<lambda>_. return s))"

lemma hash_map_preserving_verifier_state_transfer_with_saved:
  "hash_map_preserving (verifier_state_transfer_with_saved tr)"
  unfolding verifier_state_transfer_with_saved_def
    hash_map_preserving_def
  by (auto elim!: set_dist_bindE)
lemma hash_target_program_checked_staged_after_query_prefix_receive_with_verifier:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "hash_target_program B
      (query_opening_budgets budgets ! i +
        (sum_list
          (take (rounds - Suc i)
            (drop (Suc i) (query_opening_budgets budgets))) +
          (rounds - Suc i)) +
        verifier_hash_query_budget)
      (checked_staged_after_query_prefix_receive_with_verifier A i
        prefix_pack)"
proof -
  let ?builder =
    "query_opening_budgets budgets ! i +
      (sum_list
        (take (rounds - Suc i)
          (drop (Suc i) (query_opening_budgets budgets))) +
        (rounds - Suc i))"
  have builder:
    "hash_target_program B ?builder
      (checked_staged_after_query_prefix_receive A i prefix_pack)"
    by (rule
        hash_target_program_checked_staged_after_query_prefix_receive
          [OF wf controlled i_bound])
  have transfer:
    "\<And>data. hash_target_program B 0
      (verifier_state_transfer_with_saved
        (staged_proof_transcript data))"
    by (rule hash_map_preserving_imp_hash_target_program_zero)
      (rule hash_map_preserving_verifier_state_transfer_with_saved)
  have verify_return:
    "\<And>data saved. hash_target_program B
      (verifier_hash_query_budget + 0)
      (verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_verify_monad,
       rule hash_target_program_return)
  have verifier_tail:
    "\<And>data. hash_target_program B
      (0 + (verifier_hash_query_budget + 0))
      (verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule hash_target_program_bind)
      (rule transfer, rule verify_return)
  have whole:
    "hash_target_program B
      (?builder + (0 + (verifier_hash_query_budget + 0)))
      (checked_staged_after_query_prefix_receive A i prefix_pack \<bind>
        (\<lambda>data.
          verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>saved. verify_monad \<bind>
            (\<lambda>result. return ((data, saved), result)))))"
    by (rule hash_target_program_bind)
      (rule builder, rule verifier_tail)
  show ?thesis
    using whole
    unfolding
      checked_staged_after_query_prefix_receive_with_verifier_def
      verifier_state_transfer_with_saved_def
    by (simp add: sm_bind_assoc)
qed


definition checked_staged_query_prefix_continuation_with_state
where
  "checked_staged_query_prefix_continuation_with_state A i prefix_pack =
    receive_query_index_challenge \<bind> (\<lambda>raw.
    get \<bind> (\<lambda>raw_state.
    checked_staged_after_query_prefix_receive_with_verifier A i
      (prefix_pack, raw) \<bind>
    (\<lambda>out. return (((prefix_pack, raw), raw_state), out))))"

lemma checked_staged_security_experiment_with_query_prefix_data_state_decomp_before_receive:
  "checked_staged_security_experiment_with_query_prefix_data_state A i =
    checked_staged_query_prefix_with_state A i \<bind>
      checked_staged_query_prefix_continuation_with_state A i"
  unfolding
    checked_staged_security_experiment_with_query_prefix_data_state_def
    checked_staged_query_prefix_receive_with_state_def
    checked_staged_query_prefix_continuation_with_state_def
  by (simp add: sm_bind_assoc)

lemma hash_target_program_checked_staged_query_prefix_continuation_with_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "hash_target_program B
      (staged_query_prefix_tail_hash_queries budgets i)
      (checked_staged_query_prefix_continuation_with_state A i
        prefix_pack)"
proof -
  let ?after =
    "query_opening_budgets budgets ! i +
      (sum_list
        (take (rounds - Suc i)
          (drop (Suc i) (query_opening_budgets budgets))) +
        (rounds - Suc i)) +
      verifier_hash_query_budget"
  have receive:
    "hash_target_program B 1 receive_query_index_challenge"
    by (rule hash_target_program_receive_query_index_challenge)
  have after:
    "\<And>raw. hash_target_program B ?after
      (checked_staged_after_query_prefix_receive_with_verifier A i
        (prefix_pack, raw))"
    by (rule
        hash_target_program_checked_staged_after_query_prefix_receive_with_verifier
          [OF wf controlled i_bound])
  have after_return:
    "\<And>raw raw_state. hash_target_program B (?after + 0)
      (checked_staged_after_query_prefix_receive_with_verifier A i
        (prefix_pack, raw) \<bind>
       (\<lambda>out. return (((prefix_pack, raw), raw_state), out)))"
    by (rule hash_target_program_bind)
      (rule after, rule hash_target_program_return)
  have get_after:
    "\<And>raw. hash_target_program B (0 + (?after + 0))
      (get \<bind> (\<lambda>raw_state.
       checked_staged_after_query_prefix_receive_with_verifier A i
        (prefix_pack, raw) \<bind>
       (\<lambda>out. return (((prefix_pack, raw), raw_state), out))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_get, rule after_return)
  have whole:
    "hash_target_program B (1 + (0 + (?after + 0)))
      (receive_query_index_challenge \<bind> (\<lambda>raw.
       get \<bind> (\<lambda>raw_state.
       checked_staged_after_query_prefix_receive_with_verifier A i
        (prefix_pack, raw) \<bind>
       (\<lambda>out. return (((prefix_pack, raw), raw_state), out)))))"
    by (rule hash_target_program_bind)
      (rule receive, rule get_after)
  show ?thesis
    using whole
    unfolding
      checked_staged_query_prefix_continuation_with_state_def
      staged_query_prefix_tail_hash_queries_def
    by simp
qed


definition checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at
where
  "checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at
      i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        \<not> hash_map_output_collision prefix_state \<and>
        hash_map_new_output_hit
          (merkle_prefix_path_targets
            (query_prefix_merkle_roots prefix) prefix_state)
          prefix_state final_state)"

lemma checked_staged_security_with_query_prefix_structured_path_imp_collision_or_clean_prefix_target_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i out \<or>
       checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i out"
  shows
    "checked_staged_security_with_query_prefix_final_collision_hit_at i out \<or>
     checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at
       i out"
proof -
  have base:
    "checked_staged_security_with_query_prefix_final_collision_hit_at i out \<or>
     checked_staged_security_with_query_prefix_current_path_prefix_target_hit_at
       i out"
    by (rule
        checked_staged_security_with_query_prefix_structured_path_imp_collision_or_prefix_target_on_support
          [OF wf controlled i_bound support hit])
  from base show ?thesis
  proof
    assume
      "checked_staged_security_with_query_prefix_final_collision_hit_at i out"
    then show ?thesis by simp
  next
    assume target:
      "checked_staged_security_with_query_prefix_current_path_prefix_target_hit_at
        i out"
    then obtain prefix prefix_state raw raw_state data attacker_state result
        final_state where out_eq:
      "out =
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state)"
      unfolding
        checked_staged_security_with_query_prefix_current_path_prefix_target_hit_at_def
      by (cases out) (auto split: prod.splits)
    have support':
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
      using support unfolding out_eq .
    have ext: "prefix_state \<le> final_state"
      by (rule
          checked_staged_security_experiment_with_query_prefix_data_state_prefix_extends_final
          [OF wf controlled i_bound support'])
    show ?thesis
    proof (cases "hash_map_output_collision prefix_state")
      case True
      have final_collision: "hash_map_output_collision final_state"
        by (rule hash_map_output_collision_mono[OF True ext])
      have
        "checked_staged_security_with_query_prefix_final_collision_hit_at i out"
        unfolding out_eq
          checked_staged_security_with_query_prefix_final_collision_hit_at_def
        using final_collision by simp
      then show ?thesis by simp
    next
      case False
      have
        "checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at
          i out"
        using target False
        unfolding out_eq
          checked_staged_security_with_query_prefix_current_path_prefix_target_hit_at_def
          checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at_def
        by simp
      then show ?thesis by simp
    qed
  qed
qed


definition staged_merkle_prefix_target_error
  :: "staged_budgets \<Rightarrow> nat \<Rightarrow> prob"
where
  "staged_merkle_prefix_target_error budgets i =
    nnreal
      (staged_query_prefix_tail_hash_queries budgets i *
        (2 + 2 * staged_query_search_queries budgets i)) /
      nnreal size"

lemma checked_staged_query_prefix_continuation_with_state_outcomeE:
  assumes outcome:
    "Some (y, final_state) \<in>
      set_dist
        (execute
          (checked_staged_query_prefix_continuation_with_state A i
            prefix_pack)
          s)"
  obtains raw raw_state tail_out where
    "y = (((prefix_pack, raw), raw_state), tail_out)"
  using outcome
  unfolding checked_staged_query_prefix_continuation_with_state_def
  by (auto elim!: set_dist_bindE)

lemma card_query_prefix_merkle_targets_le_on_clean_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
    and support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute
            (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision prefix_state"
  shows
    "card
      (merkle_prefix_path_targets
        (query_prefix_merkle_roots prefix) prefix_state)
      \<le> 2 + 2 * staged_query_search_queries budgets i"
proof -
  have range:
    "hash_range_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_prefix_with_state A i)"
    by (rule
        hash_range_budget_checked_staged_query_prefix_with_state
          [OF wf controlled i_bound])
  have output_card':
    "card (hash_map_output_values prefix_state) \<le>
      card (hash_map_output_values adversary_initial_state) +
        staged_query_search_queries budgets i"
    using range support
    unfolding hash_range_budget_def by blast
  have output_card:
    "card (hash_map_output_values prefix_state) \<le>
      staged_query_search_queries budgets i"
    using output_card' by simp
  have target_card:
    "card
      (merkle_prefix_path_targets
        (query_prefix_merkle_roots prefix) prefix_state)
      \<le>
      card (query_prefix_merkle_roots prefix) +
        2 * card (hash_map_output_values prefix_state)"
    by (rule card_merkle_prefix_path_targets_le_if_no_collision)
      (simp_all add: clean)
  have roots_card:
    "card (query_prefix_merkle_roots prefix) \<le> 2"
    by (rule card_query_prefix_merkle_roots_le)
  show ?thesis
    using target_card roots_card output_card by linarith
qed


lemma checked_staged_query_prefix_clean_target_imp_new_output_on_continuation_support:
  assumes support:
    "out \<in>
      set_dist
        (execute
          (checked_staged_query_prefix_continuation_with_state A i
            (prefix, prefix_state))
          prefix_state)"
    and target:
      "checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at
        i out"
  shows
    "hash_new_output_hit_event
      (merkle_prefix_path_targets
        (query_prefix_merkle_roots prefix) prefix_state)
      prefix_state out"
proof (cases out)
  case None
  then show ?thesis
    using target
    unfolding
      checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at_def
      hash_new_output_hit_event_def
    by simp
next
  case (Some packed)
  then obtain y final_state where packed_eq: "packed = (y, final_state)"
    by (cases packed) simp
  have outcome:
    "Some (y, final_state) \<in>
      set_dist
        (execute
          (checked_staged_query_prefix_continuation_with_state A i
            (prefix, prefix_state))
          prefix_state)"
    using support Some packed_eq by simp
  from checked_staged_query_prefix_continuation_with_state_outcomeE
      [OF outcome]
  obtain raw raw_state tail_out where y_eq:
    "y = ((((prefix, prefix_state), raw), raw_state), tail_out)" .
  show ?thesis
    using target
    unfolding Some packed_eq y_eq
      checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at_def
      hash_new_output_hit_event_def
    by (cases tail_out) (auto split: prod.splits)
qed


lemma checked_staged_security_with_query_prefix_clean_prefix_target_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at
        i)
      adversary_initial_state
      \<le> staged_merkle_prefix_target_error budgets i"
proof -
  let ?M = "checked_staged_query_prefix_with_state A i"
  let ?K = "checked_staged_query_prefix_continuation_with_state A i"
  let ?E =
    "checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at
      i"
  have decomp:
    "checked_staged_security_experiment_with_query_prefix_data_state A i =
      ?M \<bind> ?K"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_decomp_before_receive)
  show ?thesis
    unfolding decomp
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?E None"
      unfolding
        checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at_def
      by simp
  next
    fix x t
    assume head:
      "Some (x, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
    obtain prefix prefix_state where x_eq:
      "x = (prefix, prefix_state)"
      by (cases x) simp
    have head':
      "Some ((prefix, prefix_state), t) \<in>
        set_dist (execute ?M adversary_initial_state)"
      using head unfolding x_eq .
    have t_eq: "t = prefix_state"
      by (rule
          checked_staged_query_prefix_with_state_outcome_state[OF head'])
    show
      "wp_event (?K x) ?E t \<le>
        staged_merkle_prefix_target_error budgets i"
      unfolding x_eq t_eq
    proof (cases "hash_map_output_collision prefix_state")
      case True
      have impossible:
        "\<And>out. out \<in>
          set_dist
            (execute (?K (prefix, prefix_state)) prefix_state) \<Longrightarrow>
          ?E out \<Longrightarrow> False"
      proof -
        fix out
        assume out_support:
          "out \<in>
            set_dist
              (execute (?K (prefix, prefix_state)) prefix_state)"
          and event: "?E out"
        show False
        proof (cases out)
          case None
          then show False
            using event
            unfolding
              checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at_def
            by simp
        next
          case (Some packed)
          then obtain y final_state where packed_eq:
            "packed = (y, final_state)"
            by (cases packed) simp
          have outcome:
            "Some (y, final_state) \<in>
              set_dist
                (execute (?K (prefix, prefix_state)) prefix_state)"
            using out_support Some packed_eq by simp
          from checked_staged_query_prefix_continuation_with_state_outcomeE
              [OF outcome]
          obtain raw raw_state tail_out where y_eq:
            "y = ((((prefix, prefix_state), raw), raw_state), tail_out)" .
          show False
            using event True
            unfolding Some packed_eq y_eq
              checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at_def
            by (cases tail_out) (auto split: prod.splits)
        qed
      qed
      have le_false:
        "wp_event (?K (prefix, prefix_state)) ?E prefix_state \<le>
          wp_event (?K (prefix, prefix_state)) (\<lambda>_. False) prefix_state"
        by (rule wp_event_mono_on_support) (use impossible in blast)
      have false_zero:
        "wp_event (?K (prefix, prefix_state)) (\<lambda>_. False) prefix_state = 0"
        by (simp add: wp_event_def wp_def)
      have event_le_zero:
        "wp_event (?K (prefix, prefix_state)) ?E prefix_state \<le> 0"
        using le_false false_zero by simp
      have zero:
        "wp_event (?K (prefix, prefix_state)) ?E prefix_state = 0"
        by (rule antisym[OF event_le_zero]) simp
      show
        "wp_event (?K (prefix, prefix_state)) ?E prefix_state \<le>
          staged_merkle_prefix_target_error budgets i"
        unfolding zero staged_merkle_prefix_target_error_def
        by simp
    next
      case False
      let ?B =
        "merkle_prefix_path_targets
          (query_prefix_merkle_roots prefix) prefix_state"
      let ?n = "staged_query_prefix_tail_hash_queries budgets i"
      have head_canonical:
        "Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist (execute ?M adversary_initial_state)"
        using head' t_eq by simp
      have card_bound:
        "card ?B \<le> 2 + 2 * staged_query_search_queries budgets i"
        by (rule card_query_prefix_merkle_targets_le_on_clean_support
            [OF wf controlled _ head_canonical False])
          (use i_bound in simp)
      have numerator_bound:
        "?n * card ?B \<le>
          ?n * (2 + 2 * staged_query_search_queries budgets i)"
        by (rule mult_left_mono[OF card_bound]) simp
      have program:
        "hash_target_program ?B ?n
          (?K (prefix, prefix_state))"
        by (rule
            hash_target_program_checked_staged_query_prefix_continuation_with_state
              [OF wf controlled i_bound])
      have event_bound:
        "wp_event (?K (prefix, prefix_state)) ?E prefix_state \<le>
          wp_event (?K (prefix, prefix_state))
            (hash_new_output_hit_event ?B prefix_state)
            prefix_state"
        by (rule wp_event_mono_on_support)
          (blast intro:
            checked_staged_query_prefix_clean_target_imp_new_output_on_continuation_support)
      also have "... \<le> hash_target_budget_value ?B ?n"
        using program
        unfolding hash_target_program_def hash_target_budget_def
        by blast
      also have "... \<le> staged_merkle_prefix_target_error budgets i"
        unfolding hash_target_budget_value_def
          staged_merkle_prefix_target_error_def
        by (rule nnreal_nat_divide_right_mono[OF numerator_bound])
      finally have bound:
        "wp_event (?K (prefix, prefix_state)) ?E prefix_state \<le>
          staged_merkle_prefix_target_error budgets i" .
      show
        "wp_event (?K (prefix, prefix_state)) ?E prefix_state \<le>
          staged_merkle_prefix_target_error budgets i"
        by (rule bound)
    qed
  qed
qed


definition final_hash_collision_event
  :: "(('r \<times> ('f, 'a) protocol_channel_scheme) option) \<Rightarrow> bool"
where
  "final_hash_collision_event out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (_, t) \<Rightarrow> hash_map_output_collision t)"

lemma hash_collision_budget_checked_staged_security_experiment_with_data_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget)
      (checked_staged_security_experiment_with_data_state A)"
proof -
  let ?head =
    "staged_attacker_query_budget budgets + staged_challenge_query_budget"
  have transfer_range:
    "\<And>data. hash_range_budget 0
      (verifier_state_transfer_with_saved (staged_proof_transcript data))"
    by (rule hash_map_preserving_imp_hash_range_budget_zero_semantic)
      (rule hash_map_preserving_verifier_state_transfer_with_saved)
  have transfer_collision:
    "\<And>data. hash_collision_budget 0
      (verifier_state_transfer_with_saved (staged_proof_transcript data))"
    by (rule hash_map_preserving_imp_hash_collision_budget_zero_semantic)
      (rule hash_map_preserving_verifier_state_transfer_with_saved)
  have verify_return_range:
    "\<And>data saved. hash_range_budget (verifier_hash_query_budget + 0)
      (verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_verify_monad, rule hash_range_budget_return)
  have verify_return_collision:
    "\<And>data saved. hash_collision_budget (verifier_hash_query_budget + 0)
      (verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_verify_monad,
       rule hash_collision_budget_verify_monad,
       rule hash_range_budget_return,
       rule hash_collision_budget_return)
  have cont_range:
    "\<And>data. hash_range_budget (0 + (verifier_hash_query_budget + 0))
      (verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule hash_range_budget_bind)
      (rule transfer_range, rule verify_return_range)
  have cont_collision:
    "\<And>data. hash_collision_budget (0 + (verifier_hash_query_budget + 0))
      (verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule hash_collision_budget_bind)
      (rule transfer_range, rule transfer_collision,
       rule verify_return_range, rule verify_return_collision)
  have whole:
    "hash_collision_budget
      (?head + (0 + (verifier_hash_query_budget + 0)))
      (checked_staged_transcript_program A \<bind>
        (\<lambda>data.
          verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>saved. verify_monad \<bind>
            (\<lambda>result. return ((data, saved), result)))))"
    by (rule hash_collision_budget_bind)
      (rule
        hash_range_budget_checked_staged_transcript_program[OF wf controlled],
       rule
        hash_collision_budget_checked_staged_transcript_program[OF wf controlled],
       rule cont_range, rule cont_collision)
  show ?thesis
    using whole
    unfolding checked_staged_security_experiment_with_data_state_def
      verifier_state_transfer_with_saved_def
    by (simp add: sm_bind_assoc add.assoc)
qed

lemma checked_staged_security_with_data_state_final_collision_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      final_hash_collision_event adversary_initial_state
      \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  let ?q =
    "staged_attacker_query_budget budgets +
      staged_challenge_query_budget + verifier_hash_query_budget"
  have budget:
    "hash_collision_budget ?q
      (checked_staged_security_experiment_with_data_state A)"
    by (rule
        hash_collision_budget_checked_staged_security_experiment_with_data_state
          [OF wf controlled])
  have collision':
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state
      \<le>
      hash_collision_budget_value
        (card (hash_map_output_values adversary_initial_state)) ?q"
    using budget adversary_initial_state_no_output_collision
    unfolding hash_collision_budget_def by blast
  have collision:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state
      \<le> hash_collision_budget_value 0 ?q"
    using collision' by simp
  have event_eq:
    "hash_new_collision_event adversary_initial_state =
      final_hash_collision_event"
    by (rule ext)
      (simp add: hash_new_collision_event_def
        hash_map_new_output_collision_def final_hash_collision_event_def
        split: option.splits prod.splits)
  show ?thesis
    using collision unfolding event_eq .
qed

lemma checked_staged_security_with_query_prefix_final_collision_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_final_collision_hit_at i)
      adversary_initial_state
      \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have query_data_eq:
    "wp_event (checked_staged_security_experiment_with_data_state A)
        final_hash_collision_event adversary_initial_state =
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_final_collision_hit_at i)
        adversary_initial_state"
    using
      checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound, where A=A and E=final_hash_collision_event]
    unfolding final_hash_collision_event_def
      checked_staged_security_with_query_prefix_final_collision_hit_at_def
    by (simp split: option.splits prod.splits)
  have data_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      final_hash_collision_event adversary_initial_state
      \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_final_collision_bound
          [OF wf controlled])
  show ?thesis
    using data_bound unfolding query_data_eq .
qed

lemma checked_staged_security_with_query_prefix_structured_path_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out.
        checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i out \<or>
        checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i out)
      adversary_initial_state
      \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      staged_merkle_prefix_target_error budgets i"
proof -
  let ?M =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?P =
    "checked_staged_security_with_query_prefix_final_collision_hit_at i"
  let ?T =
    "checked_staged_security_with_query_prefix_current_path_clean_prefix_target_hit_at
      i"
  have reduce:
    "wp_event ?M
      (\<lambda>out.
        checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i out \<or>
        checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i out)
      adversary_initial_state
      \<le> wp_event ?M (\<lambda>out. ?P out \<or> ?T out) adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit:
      "checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i out \<or>
       checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i out"
    show "?P out \<or> ?T out"
      by (rule
          checked_staged_security_with_query_prefix_structured_path_imp_collision_or_clean_prefix_target_on_support
            [OF wf controlled i_bound support hit])
  qed
  also have "... \<le>
      wp_event ?M ?P adversary_initial_state +
      wp_event ?M ?T adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      staged_merkle_prefix_target_error budgets i"
    by (rule add_mono)
      (rule
        checked_staged_security_with_query_prefix_final_collision_bound
          [OF wf controlled i_bound],
       rule
        checked_staged_security_with_query_prefix_clean_prefix_target_bound
          [OF wf controlled i_bound])
  finally show ?thesis .
qed


lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_bound_from_prefix_and_closed_structured_paths:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
          i)
        adversary_initial_state \<le> prefix_error"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i)
      adversary_initial_state
      \<le>
      prefix_error +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      staged_merkle_prefix_target_error budgets i"
proof -
  let ?M =
    "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?prefix =
    "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
      i"
  let ?structured =
    "\<lambda>out.
      checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
        i out \<or>
      checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
        i out"
  have reduce:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i)
      adversary_initial_state
      \<le>
      wp_event ?M (\<lambda>out. ?prefix out \<or> ?structured out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit:
      "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i out"
    show "?prefix out \<or> ?structured out"
      using
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_imp_prefix_or_structured_path_on_support
          [OF wf controlled i_bound support hit]
      by blast
  qed
  also have "... \<le>
      wp_event ?M ?prefix adversary_initial_state +
      wp_event ?M ?structured adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      prefix_error +
      (hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
       staged_merkle_prefix_target_error budgets i)"
    by (rule add_mono)
      (rule prefix_bound,
       rule
        checked_staged_security_with_query_prefix_structured_path_bound
          [OF wf controlled i_bound])
  finally show ?thesis
    by (simp add: add.assoc)
qed
end

end
