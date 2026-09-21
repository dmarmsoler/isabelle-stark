(*  Title:      Stark/Soundness_FRI_First_Root_Augmented_Experiment.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_Augmented_Experiment
  imports
    Soundness_FRI_Prechallenge_Selected_Query_Product
    Soundness_Merkle_Prefix_Target_Staged
begin

text \<open>
  This proof-only augmented experiment carries the actual trace/first-FRI-root
  prefix and its hash state through the checked continuation.  Its projection is
  the existing checked experiment; the extra data is used only to bound the
  Merkle target set selected by the actual probabilistic execution.  No
  protocol state or behavior is changed.
\<close>

context soundness
begin

lemma wp_event_bind_output_state_dependent_new_output_bound_by_target_budget:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes none: "\<not> E None"
    and event_imp:
      "\<And>x t out. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        out \<in> set_dist (execute (k x) t) \<Longrightarrow>
        E out \<Longrightarrow> hash_new_output_hit_event (B x t) t out"
    and budget:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_target_budget (B x t) n (k x)"
    and value_bound:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_target_budget_value (B x t) n \<le> C"
  shows "wp_event (m \<bind> k) E s \<le> C"
proof (rule wp_event_bind_bound_by_cont
    [where Q=E and m=m and k=k and s=s and C=C])
  show "\<not> E None"
    by (rule none)
next
  fix x t
  assume head: "Some (x, t) \<in> set_dist (execute m s)"
  have "wp_event (k x) E t \<le>
      wp_event (k x) (hash_new_output_hit_event (B x t) t) t"
    by (rule wp_event_mono_on_support)
      (use head event_imp in blast)
  also have "... \<le> hash_target_budget_value (B x t) n"
    using budget[OF head] unfolding hash_target_budget_def by blast
  also have "... \<le> C"
    by (rule value_bound[OF head])
  finally show "wp_event (k x) E t \<le> C" .
qed

lemma hash_range_budget_staged_trace_fri_challenge_prefix_program:
  assumes controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < length (trace_fri_budgets budgets)"
  shows
    "hash_range_budget
      (staged_trace_fri_search_queries budgets i)
      (staged_trace_fri_challenge_prefix_program A i)"
proof -
  let ?trace_root = "trace_root_budget budgets"
  let ?completed = "sum_list (take i (trace_fri_budgets budgets)) + i"
  let ?current = "trace_fri_budgets budgets ! i"
  have trace_root_range:
    "hash_range_budget ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have completed_range:
    "hash_range_budget ?completed
      (staged_trace_fri_program A 0 i [])"
  proof -
    have len: "0 + i \<le> length (trace_fri_budgets budgets)"
      using i_bound by simp
    have exact:
      "hash_range_budget
        (sum_list (take i (drop 0 (trace_fri_budgets budgets))) + i)
        (staged_trace_fri_program A 0 i [])"
      by (rule hash_range_budget_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis by simp
  qed
  have current_range:
    "\<And>trace_bs. hash_range_budget ?current
      (trace_fri_root_stage A i trace_bs)"
    using controlled i_bound unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have after_current_record:
    "\<And>(fr :: 'f) (trace_bs :: 'f list) (root :: 'f).
      hash_range_budget 0
        (record_staged_message root \<bind>
          (\<lambda>_. return (fr, trace_bs, root)))"
  proof -
    fix fr :: 'f and trace_bs :: "'f list" and root :: 'f
    have zero:
      "hash_range_budget (0 + 0)
        (record_staged_message root \<bind>
          (\<lambda>_. return (fr, trace_bs, root)))"
      by (rule hash_range_budget_bind)
        (rule hash_range_budget_record_staged_message,
         rule hash_range_budget_return)
    show "hash_range_budget 0
      (record_staged_message root \<bind>
        (\<lambda>_. return (fr, trace_bs, root)))"
      using zero by simp
  qed
  have after_current:
    "\<And>(fr :: 'f) (trace_bs :: 'f list).
      hash_range_budget (?current + 0)
        (trace_fri_root_stage A i trace_bs \<bind>
          (\<lambda>root. record_staged_message root \<bind>
            (\<lambda>_. return (fr, trace_bs, root))))"
    by (rule hash_range_budget_bind)
      (rule current_range, rule after_current_record)
  have after_completed:
    "\<And>(fr :: 'f). hash_range_budget (?completed + (?current + 0))
      (staged_trace_fri_program A 0 i [] \<bind>
        (\<lambda>(_, trace_bs).
          trace_fri_root_stage A i trace_bs \<bind>
            (\<lambda>root. record_staged_message root \<bind>
              (\<lambda>_. return (fr, trace_bs, root)))))"
  proof (rule hash_range_budget_bind)
    fix fr :: 'f
    show "hash_range_budget ?completed
      (staged_trace_fri_program A 0 i [])"
      by (rule completed_range)
  next
    fix fr :: 'f and x :: "'f list \<times> 'f list"
    show "hash_range_budget (?current + 0)
      (case x of (_, trace_bs) \<Rightarrow>
        trace_fri_root_stage A i trace_bs \<bind>
          (\<lambda>root. record_staged_message root \<bind>
            (\<lambda>_. return (fr, trace_bs, root))))"
    proof (cases x)
      case (Pair roots trace_bs)
      have range:
        "hash_range_budget (?current + 0)
          (trace_fri_root_stage A i trace_bs \<bind>
            (\<lambda>root. record_staged_message root \<bind>
              (\<lambda>_. return (fr, trace_bs, root))))"
        by (rule after_current)
      show ?thesis
        unfolding Pair using range by simp
    qed
  qed
  have after_trace_root_record:
    "\<And>(fr :: 'f). hash_range_budget (0 + (?completed + (?current + 0)))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 i [] \<bind>
          (\<lambda>(_, trace_bs).
            trace_fri_root_stage A i trace_bs \<bind>
              (\<lambda>root. record_staged_message root \<bind>
                (\<lambda>_. return (fr, trace_bs, root))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message, rule after_completed)
  have whole:
    "hash_range_budget
      (?trace_root + (0 + (?completed + (?current + 0))))
      (staged_trace_fri_challenge_prefix_program A i)"
    unfolding staged_trace_fri_challenge_prefix_program_def
    by (rule hash_range_budget_bind)
      (rule trace_root_range, rule after_trace_root_record)
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

definition checked_staged_after_first_trace_fri_root_with_prefix_state
  :: "'f staged_adversary \<Rightarrow> ('f \<times> 'f list \<times> 'f) \<Rightarrow>
      ((((('f \<times> 'f list \<times> 'f) \<times> 'f protocol_channel) \<times>
          ('f staged_proof_data \<times> 'f protocol_channel)) \<times> unit list),
        'f protocol_channel) state_monad"
where
  "checked_staged_after_first_trace_fri_root_with_prefix_state A prefix =
    get \<bind> (\<lambda>prefix_state.
      checked_staged_after_first_trace_fri_root_program A prefix \<bind> (\<lambda>data.
        verifier_state_transfer_with_saved (staged_proof_transcript data) \<bind>
          (\<lambda>attacker_state.
            verify_monad \<bind> (\<lambda>result.
              return
                (((prefix, prefix_state), (data, attacker_state)),
                  result)))))"

definition checked_staged_security_experiment_with_first_trace_fri_root_prefix
  :: "'f staged_adversary \<Rightarrow>
      ((((('f \<times> 'f list \<times> 'f) \<times> 'f protocol_channel) \<times>
          ('f staged_proof_data \<times> 'f protocol_channel)) \<times> unit list),
        'f protocol_channel) state_monad"
where
  "checked_staged_security_experiment_with_first_trace_fri_root_prefix A =
    staged_trace_fri_challenge_prefix_program A 0 \<bind>
      checked_staged_after_first_trace_fri_root_with_prefix_state A"

definition first_trace_fri_root_prefix_merkle_targets
  :: "('f \<times> 'f list \<times> 'f) \<Rightarrow> 'f protocol_channel \<Rightarrow> 'f set"
where
  "first_trace_fri_root_prefix_merkle_targets prefix prefix_state =
    (case prefix of (fr, _, first_root) \<Rightarrow>
      if hash_map_output_collision prefix_state then {}
      else merkle_prefix_path_targets {fr, first_root} prefix_state)"

definition staged_security_with_first_trace_fri_root_prefix_merkle_target_hit
where
  "staged_security_with_first_trace_fri_root_prefix_merkle_target_hit out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some ((((prefix, prefix_state), (data, attacker_state)), result),
        final_state) \<Rightarrow>
        hash_map_new_output_hit
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
          prefix_state final_state)"

definition first_trace_fri_root_prefix_merkle_target_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "first_trace_fri_root_prefix_merkle_target_error budgets =
    nnreal
      ((staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) *
        (2 + 2 * staged_trace_fri_search_queries budgets 0)) /
      nnreal size"

lemma staged_trace_fri_challenge_prefix_zero_target_card_bound:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and head:
      "Some (prefix, prefix_state) \<in>
        set_dist
          (execute (staged_trace_fri_challenge_prefix_program A 0)
            adversary_initial_state)"
  shows
    "card
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
      \<le> 2 + 2 * staged_trace_fri_search_queries budgets 0"
proof -
  have i_bound: "0 < length (trace_fri_budgets budgets)"
    using nonempty wf
    unfolding staged_budget_wellformed_def
    by simp
  have range:
    "hash_range_budget
      (staged_trace_fri_search_queries budgets 0)
      (staged_trace_fri_challenge_prefix_program A 0)"
    by (rule
        hash_range_budget_staged_trace_fri_challenge_prefix_program
          [OF controlled i_bound])
  have output_values_initial:
    "card (hash_map_output_values prefix_state) \<le>
      card (hash_map_output_values adversary_initial_state) +
        staged_trace_fri_search_queries budgets 0"
    using range head
    unfolding hash_range_budget_def
    by blast
  have output_values_bound:
    "card (hash_map_output_values prefix_state) \<le>
      staged_trace_fri_search_queries budgets 0"
    using output_values_initial by simp
  obtain fr trace_bs first_root where prefix_eq:
    "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  show ?thesis
  proof (cases "hash_map_output_collision prefix_state")
    case True
    then show ?thesis
      unfolding first_trace_fri_root_prefix_merkle_targets_def prefix_eq
      by simp
  next
    case False
    have targets:
      "card (merkle_prefix_path_targets {fr, first_root} prefix_state) \<le>
        card {fr, first_root} +
          2 * card (hash_map_output_values prefix_state)"
      by (rule card_merkle_prefix_path_targets_le_if_no_collision)
        (simp_all add: False)
    have roots: "card {fr, first_root} \<le> 2"
      by (simp add: card_insert_if)
    have
      "card (merkle_prefix_path_targets {fr, first_root} prefix_state) \<le>
        2 + 2 * staged_trace_fri_search_queries budgets 0"
      using targets roots output_values_bound by linarith
    then show ?thesis
      unfolding first_trace_fri_root_prefix_merkle_targets_def prefix_eq
      using False by simp
  qed
qed

lemma hash_target_program_checked_staged_after_first_trace_fri_root_with_prefix_state:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget)
      (checked_staged_after_first_trace_fri_root_with_prefix_state A prefix)"
proof -
  let ?builder =
    "staged_attacker_query_budget budgets + staged_challenge_query_budget"
  have builder:
    "hash_target_program B ?builder
      (checked_staged_after_first_trace_fri_root_program A prefix)"
    by (rule
        hash_target_program_checked_staged_after_first_trace_fri_root_program
          [OF nonempty wf controlled])
  have transfer:
    "\<And>data. hash_target_program B 0
      (verifier_state_transfer_with_saved
        (staged_proof_transcript data))"
    by (rule hash_map_preserving_imp_hash_target_program_zero)
      (rule hash_map_preserving_verifier_state_transfer_with_saved)
  have verify_return:
    "\<And>prefix_state data attacker_state.
      hash_target_program B (verifier_hash_query_budget + 0)
        (verify_monad \<bind> (\<lambda>result.
          return
            (((prefix, prefix_state), (data, attacker_state)), result)))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_verify_monad,
       rule hash_target_program_return)
  have after_transfer:
    "\<And>prefix_state data.
      hash_target_program B (0 + (verifier_hash_query_budget + 0))
        (verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>attacker_state.
            verify_monad \<bind> (\<lambda>result.
              return
                (((prefix, prefix_state), (data, attacker_state)),
                  result))))"
    by (rule hash_target_program_bind)
      (rule transfer, rule verify_return)
  have after_builder:
    "\<And>prefix_state.
      hash_target_program B
        (?builder + (0 + (verifier_hash_query_budget + 0)))
        (checked_staged_after_first_trace_fri_root_program A prefix \<bind>
          (\<lambda>data.
            verifier_state_transfer_with_saved
                (staged_proof_transcript data) \<bind>
              (\<lambda>attacker_state.
                verify_monad \<bind> (\<lambda>result.
                  return
                    (((prefix, prefix_state), (data, attacker_state)),
                      result)))))"
    by (rule hash_target_program_bind)
      (rule builder, rule after_transfer)
  have whole:
    "hash_target_program B
      (0 + (?builder + (0 + (verifier_hash_query_budget + 0))))
      (get \<bind> (\<lambda>prefix_state.
        checked_staged_after_first_trace_fri_root_program A prefix \<bind>
          (\<lambda>data.
            verifier_state_transfer_with_saved
                (staged_proof_transcript data) \<bind>
              (\<lambda>attacker_state.
                verify_monad \<bind> (\<lambda>result.
                  return
                    (((prefix, prefix_state), (data, attacker_state)),
                      result))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_get, rule after_builder)
  show ?thesis
    using whole
    unfolding
      checked_staged_after_first_trace_fri_root_with_prefix_state_def
    by (simp add: add.assoc)
qed

lemma checked_staged_after_first_trace_fri_root_with_prefix_state_outcomeE:
  assumes outcome:
    "Some (y, final_state) \<in>
      set_dist
        (execute
          (checked_staged_after_first_trace_fri_root_with_prefix_state
            A prefix)
          prefix_state)"
  obtains data attacker_state result where
    "y = (((prefix, prefix_state), (data, attacker_state)), result)"
  using outcome
  unfolding
    checked_staged_after_first_trace_fri_root_with_prefix_state_def
    verifier_state_transfer_with_saved_def
  by (auto elim!: set_dist_bindE)


lemma checked_staged_security_first_trace_fri_root_prefix_merkle_target_bound:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_first_trace_fri_root_prefix A)
      staged_security_with_first_trace_fri_root_prefix_merkle_target_hit
      adversary_initial_state
      \<le> first_trace_fri_root_prefix_merkle_target_error budgets"
proof -
  let ?M = "staged_trace_fri_challenge_prefix_program A 0"
  let ?K =
    "checked_staged_after_first_trace_fri_root_with_prefix_state A"
  let ?E =
    "staged_security_with_first_trace_fri_root_prefix_merkle_target_hit"
  let ?n =
    "staged_attacker_query_budget budgets +
      staged_challenge_query_budget + verifier_hash_query_budget"
  show ?thesis
    unfolding
      checked_staged_security_experiment_with_first_trace_fri_root_prefix_def
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_by_target_budget
        [where
          B=first_trace_fri_root_prefix_merkle_targets and
          n="?n" and
          C="first_trace_fri_root_prefix_merkle_target_error budgets"])
    show "\<not> ?E None"
      unfolding
        staged_security_with_first_trace_fri_root_prefix_merkle_target_hit_def
      by simp
  next
    fix prefix prefix_state out
    assume head:
      "Some (prefix, prefix_state) \<in>
        set_dist (execute ?M adversary_initial_state)"
      and out_support:
        "out \<in> set_dist (execute (?K prefix) prefix_state)"
      and event: "?E out"
    show
      "hash_new_output_hit_event
        (first_trace_fri_root_prefix_merkle_targets
          prefix prefix_state)
        prefix_state out"
    proof (cases out)
      case None
      then show ?thesis
        using event
        unfolding
          staged_security_with_first_trace_fri_root_prefix_merkle_target_hit_def
          hash_new_output_hit_event_def
        by simp
    next
      case (Some packed)
      then obtain y final_state where packed_eq:
        "packed = (y, final_state)"
        by (cases packed) simp
      have outcome:
        "Some (y, final_state) \<in>
          set_dist (execute (?K prefix) prefix_state)"
        using out_support Some packed_eq by simp
      from
        checked_staged_after_first_trace_fri_root_with_prefix_state_outcomeE
          [OF outcome]
      obtain data attacker_state result where y_eq:
        "y = (((prefix, prefix_state), (data, attacker_state)), result)" .
      show ?thesis
        using event
        unfolding Some packed_eq y_eq
          staged_security_with_first_trace_fri_root_prefix_merkle_target_hit_def
          hash_new_output_hit_event_def
        by simp
    qed
  next
    fix prefix prefix_state
    assume head:
      "Some (prefix, prefix_state) \<in>
        set_dist (execute ?M adversary_initial_state)"
    show
      "hash_target_budget
        (first_trace_fri_root_prefix_merkle_targets
          prefix prefix_state)
        ?n (?K prefix)"
      by (rule hash_target_program_budget)
        (rule
          hash_target_program_checked_staged_after_first_trace_fri_root_with_prefix_state
            [OF nonempty wf controlled])
  next
    fix prefix prefix_state
    assume head:
      "Some (prefix, prefix_state) \<in>
        set_dist (execute ?M adversary_initial_state)"
    have card_bound:
      "card
          (first_trace_fri_root_prefix_merkle_targets
            prefix prefix_state)
        \<le> 2 + 2 * staged_trace_fri_search_queries budgets 0"
      by (rule
          staged_trace_fri_challenge_prefix_zero_target_card_bound
            [OF nonempty wf controlled head])
    have numerator_bound:
      "?n *
          card
            (first_trace_fri_root_prefix_merkle_targets
              prefix prefix_state)
        \<le> ?n *
          (2 + 2 * staged_trace_fri_search_queries budgets 0)"
      by (rule mult_left_mono[OF card_bound]) simp
    show
      "hash_target_budget_value
          (first_trace_fri_root_prefix_merkle_targets
            prefix prefix_state)
          ?n
        \<le> first_trace_fri_root_prefix_merkle_target_error budgets"
      unfolding hash_target_budget_value_def
        first_trace_fri_root_prefix_merkle_target_error_def
      by (rule nnreal_nat_divide_right_mono[OF numerator_bound])
  qed
qed


lemma checked_staged_security_experiment_with_first_trace_fri_root_prefix_projection:
  assumes nonempty: "0 < ceil_log clength"
  shows
    "checked_staged_security_experiment_with_first_trace_fri_root_prefix A \<bind>
        (\<lambda>(((prefix, prefix_state), (data, attacker_state)), result).
          return ((data, attacker_state), result)) =
      checked_staged_security_experiment_with_data_state A"
proof -
  have decomp:
    "checked_staged_transcript_program A =
      staged_trace_fri_challenge_prefix_program A 0 \<bind>
        checked_staged_after_first_trace_fri_root_program A"
    by (rule
        checked_staged_transcript_program_first_trace_fri_root_decomp
          [OF nonempty])
  show ?thesis
    unfolding
      checked_staged_security_experiment_with_first_trace_fri_root_prefix_def
      checked_staged_after_first_trace_fri_root_with_prefix_state_def
      verifier_state_transfer_with_saved_def
      checked_staged_security_experiment_with_data_state_def
      decomp
    by (simp add: sm_bind_assoc split_def sm_bind_get_ignore)
qed

definition staged_security_with_first_trace_fri_root_prefix_collision
  where
  "staged_security_with_first_trace_fri_root_prefix_collision out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some ((((prefix, prefix_state), (data, attacker_state)), result),
        final_state) \<Rightarrow>
        hash_map_output_collision prefix_state)"


lemma staged_security_with_first_trace_fri_root_prefix_collision_imp_final_on_support:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_first_trace_fri_root_prefix
              A)
            adversary_initial_state)"
    and collision:
      "staged_security_with_first_trace_fri_root_prefix_collision out"
  shows "final_hash_collision_event out"
proof (cases out)
  case None
  then show ?thesis
    using collision
    unfolding
      staged_security_with_first_trace_fri_root_prefix_collision_def
      final_hash_collision_event_def
    by simp
next
  case (Some packed)
  then obtain y final_state where packed_eq: "packed = (y, final_state)"
    by (cases packed) simp
  obtain prefix prefix_state data attacker_state result where y_eq:
    "y = (((prefix, prefix_state), (data, attacker_state)), result)"
    by (cases y) (auto split: prod.splits)
  have prefix_collision: "hash_map_output_collision prefix_state"
    using collision
    unfolding Some packed_eq y_eq
      staged_security_with_first_trace_fri_root_prefix_collision_def
    by simp
  have support_some:
    "Some (y, final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_first_trace_fri_root_prefix
            A)
          adversary_initial_state)"
    using support Some packed_eq by simp
  from support_some obtain observed observed_state where
      head:
        "Some (observed, observed_state) \<in>
          set_dist
            (execute (staged_trace_fri_challenge_prefix_program A 0)
              adversary_initial_state)"
    and tail:
      "Some (y, final_state) \<in>
        set_dist
          (execute
            (checked_staged_after_first_trace_fri_root_with_prefix_state
              A observed)
            observed_state)"
    unfolding
      checked_staged_security_experiment_with_first_trace_fri_root_prefix_def
    by (auto elim!: set_dist_bindE)
  from
    checked_staged_after_first_trace_fri_root_with_prefix_state_outcomeE
      [OF tail]
  obtain data' attacker_state' result' where tail_y:
    "y = (((observed, observed_state), (data', attacker_state')), result')" .
  have observed_state_eq: "observed_state = prefix_state"
    using y_eq tail_y by simp
  have program:
    "hash_target_program {}
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget)
      (checked_staged_after_first_trace_fri_root_with_prefix_state
        A observed)"
    by (rule
        hash_target_program_checked_staged_after_first_trace_fri_root_with_prefix_state
          [OF nonempty wf controlled])
  have ext_program:
    "hash_extension_preserving
      (checked_staged_after_first_trace_fri_root_with_prefix_state
        A observed)"
    by (rule hash_target_program_extension[OF program])
  have ext: "prefix_state \<le> final_state"
    using ext_program tail observed_state_eq
    unfolding hash_extension_preserving_def
    by blast
  have final_collision: "hash_map_output_collision final_state"
    by (rule hash_map_output_collision_mono[OF prefix_collision ext])
  show ?thesis
    unfolding Some packed_eq final_hash_collision_event_def
    using final_collision by simp
qed


lemma checked_staged_security_first_trace_fri_root_prefix_collision_bound:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_first_trace_fri_root_prefix A)
      staged_security_with_first_trace_fri_root_prefix_collision
      adversary_initial_state
      \<le> hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  let ?augmented =
    "checked_staged_security_experiment_with_first_trace_fri_root_prefix A"
  let ?project = "\<lambda>x. (snd (fst x), snd x)"
  have event_mono:
    "wp_event ?augmented
        staged_security_with_first_trace_fri_root_prefix_collision
        adversary_initial_state
      \<le> wp_event ?augmented final_hash_collision_event
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (blast intro:
        staged_security_with_first_trace_fri_root_prefix_collision_imp_final_on_support
          [OF nonempty wf controlled])
  have projection:
    "?augmented \<bind> (\<lambda>x. return (?project x)) =
      checked_staged_security_experiment_with_data_state A"
    using
      checked_staged_security_experiment_with_first_trace_fri_root_prefix_projection
        [OF nonempty, of A]
    by (simp add: split_def)
  have projected_collision:
    "wp_event ?augmented final_hash_collision_event adversary_initial_state =
      wp_event (checked_staged_security_experiment_with_data_state A)
        final_hash_collision_event adversary_initial_state"
  proof -
    have pred_eq:
      "(\<lambda>out. case out of
          None \<Rightarrow> final_hash_collision_event None
        | Some (x, t) \<Rightarrow>
            final_hash_collision_event (Some (?project x, t))) =
       final_hash_collision_event"
      by (rule ext)
        (simp add: final_hash_collision_event_def
          split: option.splits prod.splits)
    have
      "wp_event (?augmented \<bind> (\<lambda>x. return (?project x)))
          final_hash_collision_event adversary_initial_state =
        wp_event ?augmented final_hash_collision_event adversary_initial_state"
      by (subst wp_event_bind_return_map) (simp add: pred_eq)
    then show ?thesis
      unfolding projection by simp
  qed
  have final_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
        final_hash_collision_event adversary_initial_state
      \<le> hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_final_collision_bound
          [OF wf controlled])
  show ?thesis
    by (rule order_trans[OF event_mono])
      (unfold projected_collision, rule final_bound)
qed



end
end
