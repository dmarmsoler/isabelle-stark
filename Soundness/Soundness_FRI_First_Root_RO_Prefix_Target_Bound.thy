(*  Title:      Stark/Soundness_FRI_First_Root_RO_Prefix_Target_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Prefix_Target_Bound
  imports Soundness_FRI_First_Root_RO_Prequery_Bound
begin

text \<open>
  The prefix Merkle target is selected after the first trace-FRI root has been
  absorbed.  Its range bound therefore counts both domain-separated absorption
  queries in the prefix before applying a target budget to the remaining run.
\<close>

context soundness
begin

lemma hash_target_program_of_projection:
  fixes m :: "('x, 'f protocol_channel) state_monad"
    and n :: "('y, 'f protocol_channel) state_monad"
    and project :: "'x \<Rightarrow> 'y"
  assumes projection:
      "m \<bind> (\<lambda>x. return (project x)) = n"
    and program: "hash_target_program B q n"
  shows "hash_target_program B q m"
proof -
  have extension_n: "hash_extension_preserving n"
    using program unfolding hash_target_program_def by blast
  have extension_m: "hash_extension_preserving m"
    unfolding hash_extension_preserving_def
  proof (intro allI impI)
    fix s x t
    assume out: "Some (x, t) \<in> set_dist (execute m s)"
    have projected:
      "Some (project x, t) \<in>
        set_dist (execute (m \<bind> (\<lambda>x. return (project x))) s)"
      by (rule set_dist_bindI[OF out]) simp
    have projected_n:
      "Some (project x, t) \<in> set_dist (execute n s)"
      using projected unfolding projection .
    show "s \<le> t"
      using extension_n projected_n
      unfolding hash_extension_preserving_def
      by blast
  qed
  have budget_n: "hash_target_budget B q n"
    using program unfolding hash_target_program_def by blast
  have budget_m: "hash_target_budget B q m"
    unfolding hash_target_budget_def
  proof
    fix s :: "'f protocol_channel"
    let ?E = "hash_new_output_hit_event B s"
    have event_map:
      "(\<lambda>out. case out of
        None \<Rightarrow> ?E None
      | Some (x, t) \<Rightarrow> ?E (Some (project x, t))) = ?E"
      unfolding hash_new_output_hit_event_def
      by (rule ext) (auto split: option.splits prod.splits)
    have mapped:
      "wp_event (m \<bind> (\<lambda>x. return (project x))) ?E s =
        wp_event m ?E s"
      by (subst wp_event_bind_return_map)
        (simp only: event_map)
    have "wp_event n ?E s \<le> hash_target_budget_value B q"
      using budget_n unfolding hash_target_budget_def by blast
    then show "wp_event m ?E s \<le> hash_target_budget_value B q"
      using mapped unfolding projection by simp
  qed
  show ?thesis
    unfolding hash_target_program_def
    using extension_m budget_m
    by blast
qed


lemma hash_range_budget_ro_staged_first_trace_fri_root_prefix_program:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget (staged_trace_fri_search_queries budgets 0 + 2)
      (ro_staged_first_trace_fri_root_prefix_program A)"
proof -
  have index_bound: "0 < length (trace_fri_budgets budgets)"
    using nonempty wf
    unfolding staged_budget_wellformed_def
    by simp
  have root:
    "hash_range_budget (trace_root_budget budgets) (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have first:
    "hash_range_budget (trace_fri_budgets budgets ! 0)
      (trace_fri_root_stage A 0 [])"
    using controlled index_bound unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have after_first:
    "\<And>fr. hash_range_budget
      (trace_fri_budgets budgets ! 0 + (1 + (0 + 0)))
      (trace_fri_root_stage A 0 [] \<bind>
        (\<lambda>first_root. ro_record_staged_message first_root \<bind>
          (\<lambda>_. get \<bind>
            (\<lambda>prefix_state. return ((fr, [], first_root), prefix_state)))))"
    by (rule hash_range_budget_bind)
      (rule first, rule hash_range_budget_bind,
       rule hash_range_budget_ro_record_staged_message,
       rule hash_range_budget_bind,
       rule hash_range_budget_get, rule hash_range_budget_return)
  have after_root:
    "\<And>fr. hash_range_budget
      (1 + (trace_fri_budgets budgets ! 0 + (1 + (0 + 0))))
      (ro_record_staged_message fr \<bind>
        (\<lambda>_. trace_fri_root_stage A 0 [] \<bind>
          (\<lambda>first_root. ro_record_staged_message first_root \<bind>
            (\<lambda>_. get \<bind>
              (\<lambda>prefix_state.
                return ((fr, [], first_root), prefix_state))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_record_staged_message, rule after_first)
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  have whole:
    "hash_range_budget
      (trace_root_budget budgets +
        (1 + (trace_fri_budgets budgets ! 0 + (1 + (0 + 0)))))
      (ro_staged_first_trace_fri_root_prefix_program A)"
    unfolding ro_staged_first_trace_fri_root_prefix_program_def
    apply (rule hash_range_budget_bind)
     apply (rule root)
    using after_root
    by (simp add: rounds_eq)
  have take_eq:
    "take (Suc 0) (trace_fri_budgets budgets) =
      take 0 (trace_fri_budgets budgets) @
        [trace_fri_budgets budgets ! 0]"
    by (rule take_Suc_conv_app_nth[OF index_bound])
  have budget_eq:
    "trace_root_budget budgets +
        (1 + (trace_fri_budgets budgets ! 0 + (1 + (0 + 0)))) =
      staged_trace_fri_search_queries budgets 0 + 2"
    unfolding staged_trace_fri_search_queries_def
    using take_eq by simp
  show ?thesis
    using whole unfolding budget_eq .
qed

lemma ro_staged_first_trace_fri_root_prefix_target_card_bound:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and head:
      "Some ((prefix, prefix_state), t) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
  shows
    "card (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
      \<le> 2 + 2 * (staged_trace_fri_search_queries budgets 0 + 2)"
proof -
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  have state_eq: "t = prefix_state"
    using head
    unfolding ro_staged_first_trace_fri_root_prefix_program_def
    by (auto simp: rounds_eq elim!: set_dist_bindE)
  have range:
    "hash_range_budget (staged_trace_fri_search_queries budgets 0 + 2)
      (ro_staged_first_trace_fri_root_prefix_program A)"
    by (rule
      hash_range_budget_ro_staged_first_trace_fri_root_prefix_program[
        OF nonempty wf controlled])
  have output_values_initial:
    "card (hash_map_output_values prefix_state) \<le>
      card (hash_map_output_values adversary_initial_state) +
        (staged_trace_fri_search_queries budgets 0 + 2)"
    using range head state_eq
    unfolding hash_range_budget_def
    by blast
  have output_values_bound:
    "card (hash_map_output_values prefix_state) \<le>
      staged_trace_fri_search_queries budgets 0 + 2"
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
    have doubled:
      "2 * card (hash_map_output_values prefix_state) \<le>
        2 * (staged_trace_fri_search_queries budgets 0 + 2)"
      by (rule mult_left_mono[OF output_values_bound]) simp
    have
      "card (merkle_prefix_path_targets {fr, first_root} prefix_state) \<le>
        2 + 2 * (staged_trace_fri_search_queries budgets 0 + 2)"
      by (rule order_trans[OF targets add_mono[OF roots doubled]])
    then show ?thesis
      unfolding first_trace_fri_root_prefix_merkle_targets_def prefix_eq
      using False by simp
  qed
qed


definition ro_checked_staged_after_first_root_hash_query_budget_for
  :: "staged_budgets \<Rightarrow> nat"
where
  "ro_checked_staged_after_first_root_hash_query_budget_for budgets =
    1 +
      ((sum_list
          (take (ceil_log clength - 1)
            (drop 1 (trace_fri_budgets budgets))) +
        2 * (ceil_log clength - 1)) +
      (trace_final_budget budgets +
        (1 +
          (2 * length spec +
            (degree_budget budgets +
              (1 +
                ((sum_list (composition_fri_budgets budgets) +
                    2 * ceil_log (maxDegree + 1)) +
                  (composition_final_budget budgets + (1 + 0)))))))))"

lemma hash_target_program_ro_checked_staged_after_first_trace_fri_root_prefix:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (ro_checked_staged_after_first_root_hash_query_budget_for budgets)
      (ro_checked_staged_after_first_trace_fri_root_prefix_program A prefix)"
proof -
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  let ?trace_fri =
    "sum_list
        (take (ceil_log clength - 1)
          (drop 1 (trace_fri_budgets budgets))) +
      2 * (ceil_log clength - 1)"
  let ?trace_final = "trace_final_budget budgets"
  let ?alpha = "2 * length spec"
  let ?degree = "degree_budget budgets"
  let ?composition_fri =
    "sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  have trace_len:
    "1 + (ceil_log clength - 1) \<le> length (trace_fri_budgets budgets)"
    using nonempty wf
    unfolding staged_budget_wellformed_def
    by simp
  have trace_fri_program:
    "\<And>bs. hash_target_program B ?trace_fri
      (ro_staged_trace_fri_program A 1 (ceil_log clength - 1) bs)"
    by (rule hash_target_program_ro_staged_trace_fri_program[
      OF controlled trace_len])
  have trace_fri_program_n:
    "\<And>bs. hash_target_program B
      (sum_list
          (take (Suc n - 1)
            (drop 1 (trace_fri_budgets budgets))) +
        2 * (Suc n - 1))
      (ro_staged_trace_fri_program A 1 n bs)"
    using trace_fri_program rounds_eq by simp
  have trace_final_program:
    "\<And>bs. hash_target_program B ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have alpha_program:
    "hash_target_program B ?alpha
      (ro_staged_alpha_program (length spec))"
    by (rule hash_target_program_ro_staged_alpha_program)
  have degree_program:
    "\<And>as. hash_target_program B ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have composition_fri_program:
    "\<And>dg. hash_target_program B ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_target_program_guarded_ro_staged_composition_fri_program[
      OF wf controlled])
  have composition_final_program:
    "\<And>dg bs. hash_target_program B ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  obtain fr trace_bs first_root where prefix_eq:
    "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  show ?thesis
    unfolding prefix_eq
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def
      ro_checked_staged_after_first_root_hash_query_budget_for_def
      Let_def split_def rounds_eq
  apply (simp only: nat.case prod.sel)
  apply (rule hash_target_program_bind)
   apply (rule hash_target_program_receive_trace_fri_challenge)
  subgoal for b
    apply (rule hash_target_program_bind)
     apply (rule trace_fri_program_n)
    subgoal for trace_pair
      apply (cases trace_pair)
      apply (rule hash_target_program_bind)
       apply (rule trace_final_program)
      subgoal for trace_final
        apply (rule hash_target_program_bind)
         apply (rule hash_target_program_ro_record_staged_message)
        subgoal
          apply (rule hash_target_program_bind)
           apply (rule alpha_program)
          subgoal for as
            apply (rule hash_target_program_bind)
             apply (rule degree_program)
            subgoal for dg
              apply (rule hash_target_program_bind)
               apply (rule hash_target_program_ro_record_staged_message)
              subgoal
                apply (subst sm_bind_assoc[symmetric])
                apply (rule hash_target_program_bind)
                 apply (rule composition_fri_program)
                subgoal for composition_pair
                  apply (cases composition_pair)
                  apply (rule hash_target_program_bind)
                   apply (rule composition_final_program)
                  subgoal for composition_final
                    apply (rule hash_target_program_bind)
                     apply (rule hash_target_program_ro_record_staged_message)
                    apply (rule hash_target_program_return)
                    done
                  done
                done
              done
            done
          done
        done
      done
    done
  done
qed


lemma hash_target_program_ro_checked_staged_query_program_with_witnesses_closed:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots \<le> ceil_log (maxDegree + 1)"
  shows
    "hash_target_program B
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)
      (ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots query_state 0 rounds)"
proof (rule hash_target_program_of_projection[
    where project="\<lambda>(raws, query_states, chunks). chunks"
      and n="ro_checked_staged_query_program A trace_roots
        composition_roots 0 rounds"])
  show
    "ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots query_state 0 rounds \<bind>
        (\<lambda>x. return (case x of
          (raws, query_states, chunks) \<Rightarrow> chunks)) =
      ro_checked_staged_query_program A trace_roots composition_roots 0 rounds"
    using ro_checked_staged_query_program_with_witnesses_projection[
      of A trace_roots composition_roots query_state 0 rounds]
    by (simp add: split_def)
  have len: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have exact:
    "hash_target_program B
      (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
        rounds + rounds * ro_checked_query_round_transcript_bound)
      (ro_checked_staged_query_program A trace_roots composition_roots
        0 rounds)"
    by (rule hash_target_program_ro_checked_staged_query_program_closed[
          OF controlled len trace_len composition_len])
  then show
    "hash_target_program B
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)
      (ro_checked_staged_query_program A trace_roots composition_roots
        0 rounds)"
    using wf unfolding staged_budget_wellformed_def by simp
qed


lemma ro_checked_staged_after_first_trace_fri_root_prefix_program_output_lengths:
  assumes nonempty: "0 < ceil_log clength"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              (fr, trace_bs, first_root))
            s)"
  shows
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
      length (staged_composition_fri_roots data) \<le>
        ceil_log (maxDegree + 1)"
proof -
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  from outcome obtain b s1 trace_roots trace_bs' s2
      trace_final as dg s7 s8 composition_roots composition_bs s9
      composition_final where
    trace_out:
      "Some ((trace_roots, trace_bs'), s2) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A 1
              (ceil_log clength - 1) (trace_bs @ [b]))
            s1)"
    and assert_out:
      "Some ((), s8) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))
            s7)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s9) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])
            s8)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = first_root # trace_roots,
         staged_trace_fri_challenges = trace_bs',
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = []\<rparr>"
    using outcome
    unfolding
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def
    by (auto simp: rounds_eq Let_def
      elim!: set_dist_bindE split: prod.splits)
  have trace_exact: "length trace_roots = ceil_log clength - 1"
    using ro_staged_trace_fri_program_output_lengths[OF trace_out]
    by blast
  have trace_len:
    "length (first_root # trace_roots) = ceil_log clength"
    using nonempty trace_exact by simp
  have composition_exact:
    "length composition_roots = ceil_log (to_nat dg + 1)"
    using ro_staged_composition_fri_program_output_lengths[OF composition_out]
    by blast
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_len:
    "length composition_roots \<le> ceil_log (maxDegree + 1)"
    using composition_exact round_bound by simp
  show ?thesis
    using data_eq trace_len composition_len by simp
qed


definition ro_checked_staged_after_first_root_with_query_hash_query_budget_for ::
  "staged_budgets \<Rightarrow> nat" where
  "ro_checked_staged_after_first_root_with_query_hash_query_budget_for budgets =
    ro_checked_staged_after_first_root_hash_query_budget_for budgets +
      (0 +
        (sum_list (query_opening_budgets budgets) + rounds +
          rounds * ro_checked_query_round_transcript_bound + 0))"


definition ro_checked_staged_after_first_root_with_query_witnesses_program
  :: "'f staged_adversary \<Rightarrow>
      (('f \<times> 'f list \<times> 'f) \<times> 'f protocol_channel) \<Rightarrow>
      ((('f \<times> 'f list \<times> 'f) \<times> 'f protocol_channel) \<times>
        'f staged_proof_data \<times> 'f protocol_channel \<times>
        'f list \<times> 'f protocol_channel list,
       'f protocol_channel) state_monad"
where
  "ro_checked_staged_after_first_root_with_query_witnesses_program
      A prefix_with_state =
    do {
      data \<leftarrow> ro_checked_staged_after_first_trace_fri_root_prefix_program A
        (fst prefix_with_state);
      query_start \<leftarrow> get;
      (raws, query_states, query_chunks) \<leftarrow>
        ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds;
      return
        (prefix_with_state,
          data\<lparr>staged_query_chunks := query_chunks\<rparr>,
          query_start, raws, query_states)
    }"


lemma ro_checked_staged_transcript_program_with_first_root_prefix_decomposition:
  "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A =
    ro_staged_first_trace_fri_root_prefix_program A \<bind>
      ro_checked_staged_after_first_root_with_query_witnesses_program A"
  unfolding
    ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
    ro_checked_staged_first_root_query_head_program_def
    ro_checked_staged_after_first_root_with_query_witnesses_program_def
  by (simp add: sm_bind_assoc split_def)


lemma hash_target_program_ro_checked_staged_after_first_root_with_query_witnesses:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (ro_checked_staged_after_first_root_with_query_hash_query_budget_for
        budgets)
      (ro_checked_staged_after_first_root_with_query_witnesses_program
        A prefix_with_state)"
proof -
  let ?header =
    "ro_checked_staged_after_first_root_hash_query_budget_for budgets"
  let ?query =
    "sum_list (query_opening_budgets budgets) + rounds +
      rounds * ro_checked_query_round_transcript_bound"
  have header:
    "hash_target_program B ?header
      (ro_checked_staged_after_first_trace_fri_root_prefix_program A
        (fst prefix_with_state))"
    by (rule
      hash_target_program_ro_checked_staged_after_first_trace_fri_root_prefix[
        OF nonempty wf controlled])
  have whole:
    "hash_target_program B (?header + (0 + (?query + 0)))
      (ro_checked_staged_after_first_root_with_query_witnesses_program
        A prefix_with_state)"
    unfolding ro_checked_staged_after_first_root_with_query_witnesses_program_def
  proof (rule hash_target_program_bind_on_outcomes[OF header])
    fix s data t
    assume out:
      "Some (data, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              (fst prefix_with_state))
            s)"
    obtain fr trace_bs first_root where prefix_eq:
      "fst prefix_with_state = (fr, trace_bs, first_root)"
      by (cases "fst prefix_with_state") auto
    have lengths:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
        length (staged_composition_fri_roots data) \<le>
          ceil_log (maxDegree + 1)"
      by (rule
        ro_checked_staged_after_first_trace_fri_root_prefix_program_output_lengths[
          OF nonempty])
        (use out prefix_eq in simp)
    show
      "hash_target_program B (0 + (?query + 0))
        (get \<bind>
          (\<lambda>query_start.
            ro_checked_staged_query_program_with_witnesses A
                (staged_trace_fri_roots data)
                (staged_composition_fri_roots data)
                query_start 0 rounds \<bind>
              (\<lambda>(raws, query_states, query_chunks).
                return
                  (prefix_with_state,
                    data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                    query_start, raws, query_states))))"
      apply (rule hash_target_program_bind)
       apply (rule hash_target_program_get)
      subgoal for query_start
        apply (rule hash_target_program_bind)
         apply (rule
          hash_target_program_ro_checked_staged_query_program_with_witnesses_closed[
            OF wf controlled conjunct1[OF lengths]
              conjunct2[OF lengths]])
        subgoal for query_result
          by (cases query_result)
            (simp add: hash_target_program_return)
        done
      done
  qed
  show ?thesis
    using whole
    unfolding
      ro_checked_staged_after_first_root_with_query_hash_query_budget_for_def
    by simp
qed


definition ro_checked_staged_first_root_prefix_merkle_target_error
  :: "staged_budgets \<Rightarrow> prob" where
  "ro_checked_staged_first_root_prefix_merkle_target_error budgets =
    nnreal
      (ro_checked_staged_after_first_root_with_query_hash_query_budget_for
          budgets *
        (2 + 2 * (staged_trace_fri_search_queries budgets 0 + 2))) /
      nnreal size"


lemma wp_ro_checked_staged_first_root_prefix_merkle_target_hit_bound:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_first_root_prefix_merkle_target_hit
      adversary_initial_state
    \<le> ro_checked_staged_first_root_prefix_merkle_target_error budgets"
proof -
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  let ?M = "ro_staged_first_trace_fri_root_prefix_program A"
  let ?K =
    "ro_checked_staged_after_first_root_with_query_witnesses_program A"
  let ?E = "ro_checked_staged_first_root_prefix_merkle_target_hit"
  let ?n =
    "ro_checked_staged_after_first_root_with_query_hash_query_budget_for
      budgets"
  have decomposition:
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A = ?M \<bind> ?K"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_prefix_decomposition)
  show ?thesis
    unfolding decomposition
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_by_target_budget[
        where
          B="\<lambda>prefix_with_state t.
            first_trace_fri_root_prefix_merkle_targets
              (fst prefix_with_state) (snd prefix_with_state)" and
          n="?n" and
          C="ro_checked_staged_first_root_prefix_merkle_target_error budgets"])
    show "\<not> ?E None"
      unfolding ro_checked_staged_first_root_prefix_merkle_target_hit_def
      by simp
  next
    fix prefix_with_state t out
    assume head:
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
      and out_support: "out \<in> set_dist (execute (?K prefix_with_state) t)"
      and event: "?E out"
    obtain prefix prefix_state where prefix_with_state_eq:
      "prefix_with_state = (prefix, prefix_state)"
      by (cases prefix_with_state) simp
    have state_eq: "t = prefix_state"
      using head
      unfolding prefix_with_state_eq
        ro_staged_first_trace_fri_root_prefix_program_def
      by (auto simp: rounds_eq elim!: set_dist_bindE)
    show
      "hash_new_output_hit_event
        (first_trace_fri_root_prefix_merkle_targets
          (fst prefix_with_state) (snd prefix_with_state))
        t out"
      using event out_support state_eq
      unfolding prefix_with_state_eq
        ro_checked_staged_first_root_prefix_merkle_target_hit_def
        hash_new_output_hit_event_def
        ro_checked_staged_after_first_root_with_query_witnesses_program_def
      by (cases out)
        (auto elim!: set_dist_bindE split: prod.splits)
  next
    fix prefix_with_state t
    assume head:
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
    show
      "hash_target_budget
        (first_trace_fri_root_prefix_merkle_targets
          (fst prefix_with_state) (snd prefix_with_state))
        ?n (?K prefix_with_state)"
      by (rule hash_target_program_budget)
        (rule
          hash_target_program_ro_checked_staged_after_first_root_with_query_witnesses[
            OF nonempty wf controlled])
  next
    fix prefix_with_state t
    assume head:
      "Some (prefix_with_state, t) \<in>
        set_dist (execute ?M adversary_initial_state)"
    obtain prefix prefix_state where prefix_with_state_eq:
      "prefix_with_state = (prefix, prefix_state)"
      by (cases prefix_with_state) simp
    have card_bound:
      "card
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        \<le> 2 + 2 * (staged_trace_fri_search_queries budgets 0 + 2)"
      by (rule
        ro_staged_first_trace_fri_root_prefix_target_card_bound[
          OF nonempty wf controlled])
        (use head prefix_with_state_eq in simp)
    have numerator_bound:
      "?n * card
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        \<le> ?n *
          (2 + 2 * (staged_trace_fri_search_queries budgets 0 + 2))"
      by (rule mult_left_mono[OF card_bound]) simp
    show
      "hash_target_budget_value
          (first_trace_fri_root_prefix_merkle_targets
            (fst prefix_with_state) (snd prefix_with_state))
          ?n
        \<le> ro_checked_staged_first_root_prefix_merkle_target_error budgets"
      unfolding prefix_with_state_eq hash_target_budget_value_def
        ro_checked_staged_first_root_prefix_merkle_target_error_def
      apply (simp only: fst_conv snd_conv)
      apply (rule nnreal_nat_divide_right_mono)
      apply (rule numerator_bound)
      done
  qed
qed


end
end
