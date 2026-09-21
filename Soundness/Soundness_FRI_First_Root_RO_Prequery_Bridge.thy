(*  Title:      Stark/Soundness_FRI_First_Root_RO_Prequery_Bridge.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Prequery_Bridge
  imports Soundness_FRI_First_Root_RO_Adaptive_Query_Budget
begin

text \<open>
  Event-side bridge for the first-root prequery branch.  Conceptual Merkle
  tables are stable along a hash-map extension unless a first-fresh path output
  hits the prefix-fixed target set.  The remaining lemmas reconstruct the
  absorbed transcript prefix that determines each actual query-index key.
\<close>

context soundness
begin

lemma authenticated_value_at_prefix_stable_if_no_target:
  assumes ext: "s \<le> t"
    and no_hit:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {rt} s) s t"
  shows "authenticated_value_at t rt len i v \<longleftrightarrow>
    authenticated_value_at s rt len i v"
proof
  assume final: "authenticated_value_at t rt len i v"
  from authenticated_value_atE[OF final]
  obtain opn where
    auth: "authenticated_opening_in t opn"
    and root: "opening_root opn = rt"
    and len_eq: "opening_length opn = len"
    and idx: "opening_index opn = i"
    and val: "opening_value opn = v"
    by blast
  have bound:
    "merkle_path_bound rt len i v (opening_path opn) t"
    using auth root len_eq idx val
    unfolding authenticated_opening_in_def
    by simp
  have prefix_bound: "merkle_path_bound rt len i v (opening_path opn) s"
    using merkle_path_bound_pullback_or_prefix_target_hit[OF ext bound]
      no_hit
    by blast
  have prefix_bound_opn:
    "merkle_path_bound
      (opening_root opn) (opening_length opn)
      (opening_index opn) (opening_value opn) (opening_path opn) s"
    using prefix_bound root len_eq idx val
    by simp
  have prefix_auth: "authenticated_opening_in s opn"
    using auth prefix_bound_opn
    unfolding authenticated_opening_in_def
    by simp
  show "authenticated_value_at s rt len i v"
    by (rule authenticated_value_atI[OF prefix_auth root len_eq idx val])
next
  assume prefix: "authenticated_value_at s rt len i v"
  show "authenticated_value_at t rt len i v"
    by (rule authenticated_value_at_mono[OF prefix ext])
qed

lemma conceptual_opening_value_prefix_stable_if_no_target:
  assumes ext: "s \<le> t"
    and no_hit:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {rt} s) s t"
  shows "conceptual_opening_value t rt len i =
    conceptual_opening_value s rt len i"
proof -
  have pred_eq:
    "(\<lambda>v. authenticated_value_at t rt len i v) =
      (\<lambda>v. authenticated_value_at s rt len i v)"
    by (simp add: fun_eq_iff
      authenticated_value_at_prefix_stable_if_no_target[OF ext no_hit])
  show ?thesis
    unfolding conceptual_opening_value_def
    using pred_eq by simp
qed

lemma conceptual_table_prefix_stable_if_no_target:
  assumes ext: "s \<le> t"
    and no_hit:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {rt} s) s t"
  shows "conceptual_table t rt len = conceptual_table s rt len"
  unfolding conceptual_table_def
  using conceptual_opening_value_prefix_stable_if_no_target[OF ext no_hit]
  by simp

lemma ro_checked_staged_query_program_with_witnesses_prefix_chain:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and outcome:
      "Some ((raws, query_states, chunks), t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots query_state i n)
            query_state)"
    and j_bound: "j < n"
  shows
    "ro_absorb_lookup_chain t (PState query_state)
      (List.concat (take j chunks)) (PState (query_states ! j))"
  using bound outcome j_bound
proof (induction n arbitrary: i query_state t raws query_states chunks j)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(2)
  obtain raw chunk raws_tail query_states_tail chunks_tail
      s1 s2 s_assert s3 where
    challenge_out:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge query_state)"
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
    and query_states_eq: "query_states = query_state # query_states_tail"
    and chunks_eq: "chunks = chunk # chunks_tail"
    unfolding ro_checked_staged_query_program_with_witnesses.simps Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have assert_eq: "s_assert = s2"
    using assert_out
    unfolding assert_def
    by (cases
        "verifier_query_round_chunk (index (to_nat raw))
          trace_roots composition_roots chunk")
      (simp_all add: throw_no_outcome)
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by blast
  have challenge_state: "PState s1 = PState query_state"
    using receive_query_index_challenge_outcome[OF challenge_out]
    by simp
  have stage_state: "PState s2 = PState s1"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have record_out':
    "Some ((), s3) \<in>
      set_dist (execute (ro_record_staged_messages chunk) s2)"
    using record_out assert_eq by simp
  have record_props:
    "ro_absorb_lookup_chain s3 (PState s2) chunk (PState s3) \<and>
      s2 \<le> s3"
    by (rule ro_record_staged_messages_absorb_lookup_chain[OF record_out'])
  have tail_bound:
    "Suc i + n \<le> length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_props: "s3 \<le> t"
    using ro_checked_staged_query_program_with_witnesses_outcome[
        OF controlled tail_bound rest_out]
    by blast
  show ?case
  proof (cases j)
    case 0
    then show ?thesis
      unfolding query_states_eq chunks_eq
      by simp
  next
    case (Suc k)
    have k_bound: "k < n"
      using Suc.prems(3) unfolding Suc by simp
    have tail_chain:
      "ro_absorb_lookup_chain t (PState s3)
        (List.concat (take k chunks_tail))
        (PState (query_states_tail ! k))"
      by (rule Suc.IH[OF tail_bound rest_out k_bound])
    have head_chain:
      "ro_absorb_lookup_chain t (PState query_state) chunk (PState s3)"
    proof -
      have lifted:
        "ro_absorb_lookup_chain t (PState s2) chunk (PState s3)"
        by (rule ro_absorb_lookup_chain_mono[
              OF conjunct1[OF record_props] tail_props])
      show ?thesis
        using lifted challenge_state stage_state by simp
    qed
    have combined:
      "ro_absorb_lookup_chain t (PState query_state)
        (chunk @ List.concat (take k chunks_tail))
        (PState (query_states_tail ! k))"
      by (rule ro_absorb_lookup_chain_append[OF head_chain tail_chain])
    show ?thesis
      unfolding query_states_eq chunks_eq Suc
      using combined by simp
  qed
qed

lemma ro_staged_first_trace_fri_root_prefix_program_chain:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some (((fr, trace_bs, first_root), prefix_state), t) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A) s)"
  shows
    "trace_bs = [] \<and> prefix_state = t \<and> s \<le> t \<and>
      ro_absorb_lookup_chain t (PState s) [fr, first_root] (PState t) \<and>
      PQueryCounter t = PQueryCounter s"
proof -
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  from outcome obtain s1 s2 s3 s4 where
    root_out:
      "Some (fr, s1) \<in> set_dist (execute (trace_root_stage A) s)"
    and root_record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message fr) s1)"
    and first_out:
      "Some (first_root, s3) \<in>
        set_dist (execute (trace_fri_root_stage A 0 []) s2)"
    and first_record_out:
      "Some ((), s4) \<in>
        set_dist (execute (ro_record_staged_message first_root) s3)"
    and trace_bs_eq: "trace_bs = []"
    and prefix_state_eq: "prefix_state = s4"
    and t_eq: "t = s4"
    unfolding ro_staged_first_trace_fri_root_prefix_program_def rounds_eq
    by (auto elim!: set_dist_bindE)
  have root_controlled:
    "controlled_ro_program (trace_root_budget budgets) (trace_root_stage A)"
    using controlled
    unfolding staged_adversary_controlled_def
    by blast
  have root_ext: "s \<le> s1"
    using controlled_ro_program_extension[OF root_controlled] root_out
    unfolding hash_extension_preserving_def
    by blast
  have root_state: "PState s1 = PState s"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp
  have root_record:
    "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) fr) =
        Some (PState s2) \<and>
      s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF root_record_out])
  have i_bound: "0 < length (trace_fri_budgets budgets)"
    using wf nonempty
    unfolding staged_budget_wellformed_def
    by simp
  have first_controlled:
    "controlled_ro_program (trace_fri_budgets budgets ! 0)
      (trace_fri_root_stage A 0 [])"
    using controlled i_bound
    unfolding staged_adversary_controlled_def
    by blast
  have first_ext: "s2 \<le> s3"
    using controlled_ro_program_extension[OF first_controlled] first_out
    unfolding hash_extension_preserving_def
    by blast
  have first_state: "PState s3 = PState s2"
    using controlled_stage_outcome_fields[OF first_controlled first_out]
    by simp
  have first_record:
    "fmlookup (HashMap s4)
        (TranscriptAbsorb (PState s3) first_root) =
        Some (PState s4) \<and>
      s3 \<le> s4"
    by (rule
      ro_record_staged_message_absorb_lookup_state[OF first_record_out])
  have root_chain_s2:
    "ro_absorb_lookup_chain s2 (PState s) [fr] (PState s2)"
    using root_record root_state by auto
  have s2_s4: "s2 \<le> s4"
    by (rule hash_ext_trans[OF first_ext conjunct2[OF first_record]])
  have root_chain_s4:
    "ro_absorb_lookup_chain s4 (PState s) [fr] (PState s2)"
    by (rule ro_absorb_lookup_chain_mono[OF root_chain_s2 s2_s4])
  have first_chain_s4:
    "ro_absorb_lookup_chain s4 (PState s2) [first_root] (PState s4)"
    using first_record first_state by auto
  have chain':
    "ro_absorb_lookup_chain s4 (PState s)
      ([fr] @ [first_root]) (PState s4)"
    by (rule ro_absorb_lookup_chain_append[
          OF root_chain_s4 first_chain_s4])
  have chain:
    "ro_absorb_lookup_chain s4 (PState s) [fr, first_root] (PState s4)"
    using chain' by simp
  have ext: "s \<le> s4"
    by (rule hash_ext_trans[OF root_ext])
      (rule hash_ext_trans[OF conjunct2[OF root_record] s2_s4])
  have root_counter: "PQueryCounter s1 = PQueryCounter s"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp
  have root_record_counter: "PQueryCounter s2 = PQueryCounter s1"
    using ro_record_staged_message_hash_extends_query_counter[
      OF root_record_out]
    by simp
  have first_counter: "PQueryCounter s3 = PQueryCounter s2"
    using controlled_stage_outcome_fields[OF first_controlled first_out]
    by simp
  have first_record_counter: "PQueryCounter s4 = PQueryCounter s3"
    using ro_record_staged_message_hash_extends_query_counter[
      OF first_record_out]
    by simp
  have counter: "PQueryCounter s4 = PQueryCounter s"
    using root_counter root_record_counter first_counter first_record_counter
    by simp
  show ?thesis
    using trace_bs_eq prefix_state_eq t_eq ext chain counter
    by simp
qed

lemma ro_staged_first_trace_fri_root_prefix_program_zero_chain:
  assumes controlled: "staged_adversary_controlled budgets A"
    and zero: "ceil_log clength = 0"
    and outcome:
      "Some (((fr, trace_bs, first_root), prefix_state), t) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A) s)"
  shows
    "trace_bs = [] \<and> first_root = fr \<and> prefix_state = t \<and> s \<le> t \<and>
      ro_absorb_lookup_chain t (PState s) [fr] (PState t) \<and>
      PQueryCounter t = PQueryCounter s"
proof -
  from outcome obtain s1 s2 where
    root_out:
      "Some (fr, s1) \<in> set_dist (execute (trace_root_stage A) s)"
    and root_record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message fr) s1)"
    and trace_bs_eq: "trace_bs = []"
    and first_root_eq: "first_root = fr"
    and prefix_state_eq: "prefix_state = s2"
    and t_eq: "t = s2"
    unfolding ro_staged_first_trace_fri_root_prefix_program_def zero
    by (auto elim!: set_dist_bindE)
  have root_controlled:
      "controlled_ro_program (trace_root_budget budgets) (trace_root_stage A)"
    using controlled
    unfolding staged_adversary_controlled_def
    by blast
  have root_ext: "s \<le> s1"
    using controlled_ro_program_extension[OF root_controlled] root_out
    unfolding hash_extension_preserving_def
    by blast
  have root_state: "PState s1 = PState s"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp
  have root_record:
      "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) fr) =
          Some (PState s2) \<and>
       s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF root_record_out])
  have chain:
      "ro_absorb_lookup_chain s2 (PState s) [fr] (PState s2)"
    using root_record root_state by auto
  have ext: "s \<le> s2"
    by (rule hash_ext_trans[OF root_ext conjunct2[OF root_record]])
  have root_counter: "PQueryCounter s1 = PQueryCounter s"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp
  have root_record_counter: "PQueryCounter s2 = PQueryCounter s1"
    using ro_record_staged_message_hash_extends_query_counter[
      OF root_record_out]
    by simp
  show ?thesis
    using trace_bs_eq first_root_eq prefix_state_eq t_eq ext chain
      root_counter root_record_counter
    by simp
qed

lemma ro_checked_staged_transcript_program_with_first_root_witnesses_projection_outcome:
  assumes nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            s)"
  shows
    "Some ((data, query_start, raws, query_states), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_query_witnesses A)
          s)"
proof -
  have mapped:
    "Some ((data, query_start, raws, query_states), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A \<bind>
            (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
              return (data, query_start, raws, query_states)))
          s)"
  proof (rule set_dist_bindI[OF outcome])
    show
      "Some ((data, query_start, raws, query_states), attacker_state) \<in>
        set_dist
          (execute
            (case (((prefix, prefix_state), data, query_start, raws, query_states))
             of (prefix_with_state, data, query_start, raws, query_states) \<Rightarrow>
               return (data, query_start, raws, query_states))
            attacker_state)"
      by simp
  qed
  show ?thesis
    using mapped
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_projection[
        OF nonempty, of A]
    by simp
qed

lemma ro_checked_staged_transcript_program_with_first_root_projection_outcome:
  assumes nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            s)"
  shows
    "Some (data, attacker_state) \<in>
      set_dist (execute (ro_checked_staged_transcript_program A) s)"
proof -
  have witnesses:
    "Some ((data, query_start, raws, query_states), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_query_witnesses A)
          s)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_witnesses_projection_outcome[
        OF nonempty outcome])
  have mapped:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_query_witnesses A \<bind>
            (\<lambda>(data, query_start, raws, query_states). return data))
          s)"
  proof (rule set_dist_bindI[OF witnesses])
    show
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (case ((data, query_start, raws, query_states))
             of (data, query_start, raws, query_states) \<Rightarrow> return data)
            attacker_state)"
      by simp
  qed
  show ?thesis
    using mapped
      ro_checked_staged_transcript_program_with_query_witnesses_projection[of A]
    by simp
qed

lemma
  ro_checked_staged_transcript_program_with_first_root_witnesses_projection_outcome_all_rounds:
  assumes outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            s)"
  shows
    "Some ((data, query_start, raws, query_states), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_query_witnesses A)
          s)"
proof -
  have mapped:
    "Some ((data, query_start, raws, query_states), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A \<bind>
            (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
              return (data, query_start, raws, query_states)))
          s)"
  proof (rule set_dist_bindI[OF outcome])
    show
      "Some ((data, query_start, raws, query_states), attacker_state) \<in>
        set_dist
          (execute
            (case (((prefix, prefix_state), data, query_start, raws, query_states))
             of (prefix_with_state, data, query_start, raws, query_states) \<Rightarrow>
               return (data, query_start, raws, query_states))
            attacker_state)"
      by simp
  qed
  show ?thesis
    using mapped
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_projection_all_rounds[
        of A]
    by simp
qed

lemma
  ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds:
  assumes outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            s)"
  shows
    "Some (data, attacker_state) \<in>
      set_dist (execute (ro_checked_staged_transcript_program A) s)"
proof -
  have witnesses:
    "Some ((data, query_start, raws, query_states), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_query_witnesses A)
          s)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_witnesses_projection_outcome_all_rounds[
        OF outcome])
  have mapped:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_query_witnesses A \<bind>
            (\<lambda>(data, query_start, raws, query_states). return data))
          s)"
  proof (rule set_dist_bindI[OF witnesses])
    show
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (case ((data, query_start, raws, query_states))
             of (data, query_start, raws, query_states) \<Rightarrow> return data)
            attacker_state)"
      by simp
  qed
  show ?thesis
    using mapped
      ro_checked_staged_transcript_program_with_query_witnesses_projection[of A]
    by simp
qed

lemma ro_checked_staged_transcript_program_with_first_root_outcomeE:
  assumes outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            s)"
  obtains head_data query_chunks prefix_final where
    "Some ((prefix, prefix_state), prefix_final) \<in>
      set_dist
        (execute (ro_staged_first_trace_fri_root_prefix_program A) s)"
    "Some (head_data, query_start) \<in>
      set_dist
        (execute
          (ro_checked_staged_after_first_trace_fri_root_prefix_program A prefix)
          prefix_final)"
    "Some ((raws, query_states, query_chunks), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program_with_witnesses A
            (staged_trace_fri_roots head_data)
            (staged_composition_fri_roots head_data)
            query_start 0 rounds)
          query_start)"
    "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
  using outcome
  unfolding
    ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
    ro_checked_staged_first_root_query_head_program_def
  by (auto elim!: set_dist_bindE split: prod.splits)

lemma ro_absorb_lookup_chain_start_functional_if_clean:
  assumes clean: "\<not> hash_map_output_collision s"
    and left: "ro_absorb_lookup_chain s start_left xs final"
    and right: "ro_absorb_lookup_chain s start_right xs final"
  shows "start_left = start_right"
  using left right
proof (induction xs arbitrary: start_left start_right final rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  from ro_absorb_lookup_chain_snoc[OF snoc.prems(1)]
  obtain mid_left where
    prefix_left: "ro_absorb_lookup_chain s start_left xs mid_left"
    and lookup_left:
      "fmlookup (HashMap s) (TranscriptAbsorb mid_left x) = Some final"
    by blast
  from ro_absorb_lookup_chain_snoc[OF snoc.prems(2)]
  obtain mid_right where
    prefix_right: "ro_absorb_lookup_chain s start_right xs mid_right"
    and lookup_right:
      "fmlookup (HashMap s) (TranscriptAbsorb mid_right x) = Some final"
    by blast
  have key_eq:
    "TranscriptAbsorb mid_left x = TranscriptAbsorb mid_right x"
    by (rule hash_map_lookup_key_unique_if_no_output_collision[
          OF clean lookup_left lookup_right])
  have mid_eq: "mid_left = mid_right"
    using key_eq by simp
  show ?case
    by (rule snoc.IH[OF prefix_left])
      (use prefix_right mid_eq in simp)
qed

lemma ro_checked_staged_query_program_with_witnesses_absorb_lookup_chain:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and outcome:
      "Some ((raws, query_states, chunks), t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots query_state i n)
            query_state)"
  shows
    "ro_absorb_lookup_chain t (PState query_state)
        (List.concat chunks) (PState t) \<and>
      query_state \<le> t"
proof -
  have mapped:
    "Some (chunks, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots query_state i n \<bind>
            (\<lambda>(raws, query_states, chunks). return chunks))
          query_state)"
  proof (rule set_dist_bindI[OF outcome])
    show
      "Some (chunks, t) \<in>
        set_dist
          (execute
            (case ((raws, query_states, chunks))
             of (raws, query_states, chunks) \<Rightarrow> return chunks)
            t)"
      by simp
  qed
  have ordinary:
    "Some (chunks, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots
            composition_roots i n)
          query_state)"
    using mapped
      ro_checked_staged_query_program_with_witnesses_projection[
        of A trace_roots composition_roots query_state i n]
    by simp
  show ?thesis
    by (rule ro_checked_staged_query_program_absorb_lookup_chain[
          OF controlled bound ordinary])
qed

lemma ro_checked_staged_after_first_trace_fri_root_prefix_program_fields:
  assumes nonempty: "0 < ceil_log clength"
    and outcome:
    "Some (data, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_after_first_trace_fri_root_prefix_program A
            (fr, trace_bs, first_root))
          s)"
  shows
    "staged_trace_root data = fr \<and>
      (\<exists>roots. staged_trace_fri_roots data = first_root # roots)"
proof -
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  show ?thesis
    using outcome
    unfolding ro_checked_staged_after_first_trace_fri_root_prefix_program_def
      rounds_eq
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
qed

lemma ro_checked_staged_after_first_trace_fri_root_prefix_program_zero_fields:
  assumes zero: "ceil_log clength = 0"
    and outcome:
    "Some (data, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_after_first_trace_fri_root_prefix_program A
            (fr, trace_bs, first_root))
          s)"
  shows
    "staged_trace_root data = fr \<and>
      staged_trace_fri_roots data = [] \<and>
      staged_trace_fri_challenges data = []"
  using outcome
  unfolding ro_checked_staged_after_first_trace_fri_root_prefix_program_def zero
  by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)

lemma ro_checked_staged_transcript_program_with_first_root_query_state_chain:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and j_bound: "j < rounds"
  obtains fr first_root rest prefix_hash where
    "prefix = (fr, [], first_root)"
    "ro_absorb_lookup_chain attacker_state
      (PState adversary_initial_state) [fr, first_root] prefix_hash"
    "ro_absorb_lookup_chain attacker_state prefix_hash rest
      (PState (query_states ! j))"
proof -
  from ro_checked_staged_transcript_program_with_first_root_outcomeE[OF outcome]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute
            (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A prefix)
            prefix_final)"
    and query_out:
      "Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots head_data)
              (staged_composition_fri_roots head_data)
              query_start 0 rounds)
            query_start)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    by blast
  obtain fr trace_bs first_root where prefix_eq:
    "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  have prefix_props:
    "trace_bs = [] \<and> prefix_state = prefix_final"
    using ro_staged_first_trace_fri_root_prefix_program_chain[
      OF wf controlled nonempty prefix_out[unfolded prefix_eq]]
    by blast
  have trace_bs_eq: "trace_bs = []"
    using prefix_props by blast
  have after_fields:
    "staged_trace_root head_data = fr \<and>
      (\<exists>roots. staged_trace_fri_roots head_data = first_root # roots)"
    by (rule
      ro_checked_staged_after_first_trace_fri_root_prefix_program_fields[
        OF nonempty])
      (use after_out prefix_eq in simp)
  obtain trace_roots where
    trace_root_eq: "staged_trace_root data = fr"
    and trace_roots_eq:
      "staged_trace_fri_roots data = first_root # trace_roots"
    using after_fields data_eq by auto
  have original_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program A)
          adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty outcome])
  have full_chain:
    "ro_absorb_lookup_chain attacker_state
      (PState adversary_initial_state)
      (staged_proof_transcript data) (PState attacker_state)"
    using ro_checked_staged_transcript_program_absorb_lookup_chain[
      OF wf controlled original_out]
    by blast
  let ?header =
    "verifier_header_messages
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)"
  have transcript_eq:
    "staged_proof_transcript data = ?header @ List.concat query_chunks"
    unfolding staged_proof_transcript_def data_eq
    by simp
  from ro_absorb_lookup_chain_append_split[
      OF full_chain[unfolded transcript_eq]]
  obtain header_end where
    header_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state) ?header header_end"
    and query_tail:
      "ro_absorb_lookup_chain attacker_state header_end
        (List.concat query_chunks) (PState attacker_state)"
    by blast
  have query_bound:
    "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_full:
    "ro_absorb_lookup_chain attacker_state (PState query_start)
        (List.concat query_chunks) (PState attacker_state)"
    using ro_checked_staged_query_program_with_witnesses_absorb_lookup_chain[
      OF controlled query_bound query_out]
    by blast
  have header_end_eq: "header_end = PState query_start"
    by (rule ro_absorb_lookup_chain_start_functional_if_clean[
      OF clean query_tail query_full])
  have header_chain':
    "ro_absorb_lookup_chain attacker_state
      (PState adversary_initial_state) ?header (PState query_start)"
    using header_chain header_end_eq by simp
  have query_prefix:
    "ro_absorb_lookup_chain attacker_state (PState query_start)
      (List.concat (take j query_chunks)) (PState (query_states ! j))"
    by (rule ro_checked_staged_query_program_with_witnesses_prefix_chain[
      OF controlled query_bound query_out j_bound])
  have combined:
    "ro_absorb_lookup_chain attacker_state
      (PState adversary_initial_state)
      (?header @ List.concat (take j query_chunks))
      (PState (query_states ! j))"
    by (rule ro_absorb_lookup_chain_append[OF header_chain' query_prefix])
  let ?header_rest =
    "trace_roots @ [staged_trace_final data] @ staged_alphas data @
      [staged_degree data] @ staged_composition_fri_roots data @
      [staged_composition_final data]"
  have header_eq: "?header = [fr, first_root] @ ?header_rest"
    unfolding verifier_header_messages_def trace_root_eq trace_roots_eq
    by simp
  have combined':
    "ro_absorb_lookup_chain attacker_state
      (PState adversary_initial_state)
      ([fr, first_root] @
        (?header_rest @ List.concat (take j query_chunks)))
      (PState (query_states ! j))"
    using combined unfolding header_eq by simp
  from ro_absorb_lookup_chain_append_split[OF combined']
  obtain prefix_hash where
    prefix_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state) [fr, first_root] prefix_hash"
    and rest_chain:
      "ro_absorb_lookup_chain attacker_state prefix_hash
        (?header_rest @ List.concat (take j query_chunks))
        (PState (query_states ! j))"
    by blast
  show thesis
    by (rule that[OF _ prefix_chain rest_chain])
      (use prefix_eq trace_bs_eq in simp)
qed

lemma ro_absorb_lookup_chain_cong_hash_map:
  assumes "HashMap s = HashMap t"
  shows "ro_absorb_lookup_chain s start xs final =
    ro_absorb_lookup_chain t start xs final"
  using assms
  by (induction xs arbitrary: start) auto

lemma first_root_absorbed_query_relation_bounded_activeI:
  assumes map_bound: "card (fmdom' (HashMap attacker_state)) \<le> L"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values attacker_state"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and no_merkle:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {fr, first_root} prefix_state)
        prefix_state attacker_state"
    and prefix_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state) [fr, first_root] prefix_hash"
    and rest_chain:
      "ro_absorb_lookup_chain attacker_state prefix_hash rest
        (PState (query_states ! j))"
    and trace_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_trace_table
          (fr, [], first_root) prefix_state)"
    and first_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table
          (fr, [], first_root) prefix_state)"
    and distinct:
      "first_trace_fri_root_prefix_trace_table
          (fr, [], first_root) prefix_state \<noteq>
        first_trace_fri_root_prefix_first_table
          (fr, [], first_root) prefix_state"
    and raws_len: "length raws = rounds"
    and raws_in:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        first_trace_fri_root_prefix_base_agreement_query_lists
          (fr, [], first_root) prefix_state"
    and j_bound: "j < rounds"
    and lookup:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge j (PState (query_states ! j))) =
        Some (raws ! j)"
  shows
    "hash_state_relation_active
      (first_root_absorbed_query_relation_bounded L)
      (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j)))
      (raws ! j)"
proof -
  have fr_targets:
    "merkle_prefix_path_targets {fr} prefix_state \<subseteq>
      merkle_prefix_path_targets {fr, first_root} prefix_state"
    by (rule merkle_prefix_path_targets_mono) auto
  have first_targets:
    "merkle_prefix_path_targets {first_root} prefix_state \<subseteq>
      merkle_prefix_path_targets {fr, first_root} prefix_state"
    by (rule merkle_prefix_path_targets_mono) auto
  have no_fr:
    "\<not> hash_map_new_output_hit
      (merkle_prefix_path_targets {fr} prefix_state)
      prefix_state attacker_state"
  proof
    assume hit:
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {fr} prefix_state)
        prefix_state attacker_state"
    have
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {fr, first_root} prefix_state)
        prefix_state attacker_state"
      by (rule hash_map_new_output_hit_subset[OF fr_targets hit])
    then show False using no_merkle by contradiction
  qed
  have no_first:
    "\<not> hash_map_new_output_hit
      (merkle_prefix_path_targets {first_root} prefix_state)
      prefix_state attacker_state"
  proof
    assume hit:
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {first_root} prefix_state)
        prefix_state attacker_state"
    have
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {fr, first_root} prefix_state)
        prefix_state attacker_state"
      by (rule hash_map_new_output_hit_subset[OF first_targets hit])
    then show False using no_merkle by contradiction
  qed
  let ?final = "channel_for_hash_map (HashMap attacker_state)"
  have final_map: "HashMap ?final = HashMap attacker_state"
    unfolding channel_for_hash_map_def by simp
  have trace_table_final:
    "first_trace_fri_root_prefix_trace_table
        (fr, [], first_root) ?final =
      first_trace_fri_root_prefix_trace_table
        (fr, [], first_root) prefix_state"
  proof -
    have final_attacker:
      "conceptual_table ?final fr (scale * clength) =
        conceptual_table attacker_state fr (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have attacker_prefix:
      "conceptual_table attacker_state fr (scale * clength) =
        conceptual_table prefix_state fr (scale * clength)"
      by (rule conceptual_table_prefix_stable_if_no_target[
        OF prefix_ext no_fr])
    show ?thesis
      unfolding first_trace_fri_root_prefix_trace_table_def
      using final_attacker attacker_prefix by simp
  qed
  have first_table_final:
    "first_trace_fri_root_prefix_first_table
        (fr, [], first_root) ?final =
      first_trace_fri_root_prefix_first_table
        (fr, [], first_root) prefix_state"
  proof -
    have final_attacker:
      "conceptual_table ?final first_root (scale * clength) =
        conceptual_table attacker_state first_root (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have attacker_prefix:
      "conceptual_table attacker_state first_root (scale * clength) =
        conceptual_table prefix_state first_root (scale * clength)"
      by (rule conceptual_table_prefix_stable_if_no_target[
        OF prefix_ext no_first])
    show ?thesis
      unfolding first_trace_fri_root_prefix_first_table_def
      using final_attacker attacker_prefix by simp
  qed
  have agreement_final:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
      first_trace_fri_root_prefix_base_agreement_query_lists
        (fr, [], first_root) ?final"
    using raws_in trace_table_final first_table_final
    unfolding first_trace_fri_root_prefix_base_agreement_query_lists_def
    by simp
  have prefix_chain_final:
    "ro_absorb_lookup_chain ?final
      (PState adversary_initial_state) [fr, first_root] prefix_hash"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule prefix_chain)
  have rest_chain_final:
    "ro_absorb_lookup_chain ?final prefix_hash rest
      (PState (query_states ! j))"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule rest_chain)
  have clean_final: "\<not> hash_map_output_collision ?final"
    using clean final_map
    unfolding hash_map_output_collision_def by simp
  have no_initial_final:
    "PState adversary_initial_state \<notin> hash_map_output_values ?final"
    using no_initial final_map
    unfolding hash_map_output_values_def by simp
  have trace_low_final:
    "trace_table_low_degree
      (first_trace_fri_root_prefix_trace_table
        (fr, [], first_root) ?final)"
    using trace_low trace_table_final by simp
  have first_low_final:
    "trace_table_low_degree
      (first_trace_fri_root_prefix_first_table
        (fr, [], first_root) ?final)"
    using first_low first_table_final by simp
  have distinct_final:
    "first_trace_fri_root_prefix_trace_table
        (fr, [], first_root) ?final \<noteq>
      first_trace_fri_root_prefix_first_table
        (fr, [], first_root) ?final"
    using distinct trace_table_final first_table_final by simp
  have relation:
    "first_root_absorbed_query_relation
      (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j)))
      (raws ! j)"
    unfolding first_root_absorbed_query_relation_def Let_def
    using clean_final no_initial_final prefix_chain_final rest_chain_final
      trace_low_final first_low_final distinct_final raws_len agreement_final
      j_bound
    by blast
  show ?thesis
    unfolding hash_state_relation_active_def
      first_root_absorbed_query_relation_bounded_def
    using map_bound lookup relation
    by simp
qed

lemma first_root_prequery_good_imp_bounded_relation_transition:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and prequery:
      "ro_checked_staged_first_root_dependent_query_start_prequery_hit
        first_trace_fri_root_prefix_base_agreement_query_lists
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
    and trace_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_trace_table prefix prefix_state)"
    and first_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
    and distinct:
      "first_trace_fri_root_prefix_trace_table prefix prefix_state \<noteq>
        first_trace_fri_root_prefix_first_table prefix prefix_state"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values attacker_state"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and no_merkle:
      "\<not> hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state attacker_state"
    and map_bound: "card (fmdom' (HashMap attacker_state)) \<le> L"
    and query_start_counter: "PQueryCounter query_start = 0"
  shows
    "hash_state_relation_transition
      (first_root_absorbed_query_relation_bounded L)
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have outcome_props:
    "length raws = rounds \<and>
      length query_states = rounds \<and>
      length (staged_query_chunks data) = rounds \<and>
      query_start \<le> attacker_state \<and>
      (\<forall>j < rounds.
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raws ! j))"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled outcome])
  have witness_props:
    "length raws = rounds \<and>
      length query_states = rounds \<and>
      length (staged_query_chunks data) = rounds \<and>
      query_start \<le> attacker_state \<and>
      PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
      (\<forall>j < rounds.
        query_states ! j \<le> attacker_state \<and>
        PQueryCounter (query_states ! j) =
          PQueryCounter query_start + j \<and>
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raws ! j) \<and>
        verifier_query_round_chunk
          (index (to_nat (raws ! j)))
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)) \<and>
      (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
    by (rule ro_checked_staged_transcript_program_with_query_witnesses_outcome[
      OF wf controlled
        ro_checked_staged_transcript_program_with_first_root_witnesses_projection_outcome[
          OF nonempty outcome]])
  have prequery_props:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        first_trace_fri_root_prefix_base_agreement_query_lists
          prefix prefix_state \<and>
      (\<exists>j < rounds.
        fmlookup (HashMap query_start)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raws ! j))"
    using prequery
    unfolding
      ro_checked_staged_first_root_dependent_query_start_prequery_hit_def
    by simp
  then obtain j where
    raws_in:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        first_trace_fri_root_prefix_base_agreement_query_lists
          prefix prefix_state"
    and j_bound: "j < rounds"
    and lookup_start:
      "fmlookup (HashMap query_start)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raws ! j)"
    by blast
  obtain fr first_root rest prefix_hash where
    prefix_eq: "prefix = (fr, [], first_root)"
    and prefix_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state) [fr, first_root] prefix_hash"
    and rest_chain:
      "ro_absorb_lookup_chain attacker_state prefix_hash rest
        (PState (query_states ! j))"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_query_state_chain[
        OF wf controlled nonempty outcome clean j_bound])
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision attacker_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_ext])
    then show False using clean by contradiction
  qed
  have no_merkle':
    "\<not> hash_map_new_output_hit
      (merkle_prefix_path_targets {fr, first_root} prefix_state)
      prefix_state attacker_state"
    using no_merkle prefix_clean
    unfolding prefix_eq first_trace_fri_root_prefix_merkle_targets_def
    by simp
  have counter_j: "PQueryCounter (query_states ! j) = j"
    using witness_props query_start_counter j_bound by simp
  have query_start_ext: "query_start \<le> attacker_state"
    using outcome_props by blast
  have lookup_final_raw:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j))) =
      Some (raws ! j)"
  proof -
    have lifted:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raws ! j)"
      by (rule hash_extension_lookup[OF lookup_start query_start_ext])
    show ?thesis
      using lifted counter_j by simp
  qed
  have active:
    "hash_state_relation_active
      (first_root_absorbed_query_relation_bounded L)
      (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j)))
      (raws ! j)"
    by (rule first_root_absorbed_query_relation_bounded_activeI[
      OF map_bound clean no_initial prefix_ext no_merkle'
        prefix_chain rest_chain])
      (use trace_low first_low distinct raws_in outcome_props prefix_eq
        j_bound lookup_final_raw in auto)
  have inactive_initial:
    "\<not> hash_state_relation_active
      (first_root_absorbed_query_relation_bounded L)
      (HashMap adversary_initial_state)
      (QueryIndexChallenge j (PState (query_states ! j)))
      (raws ! j)"
    unfolding hash_state_relation_active_def adversary_initial_state_def
    by simp
  show ?thesis
    unfolding hash_state_relation_transition_def
    using active inactive_initial by blast
qed

lemma ro_checked_staged_after_first_trace_fri_root_prefix_program_facts:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              (fr, trace_bs, first_root))
            s)"
  shows "s \<le> t \<and> PQueryCounter t = PQueryCounter s"
proof -
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  from outcome obtain b s1 trace_roots trace_bs' s2
      trace_final s3 s4 as s5 dg s6 s7 s8
      composition_roots composition_bs s9
      composition_final s10 s11 where
    challenge_out:
      "Some (b, s1) \<in>
        set_dist (execute receive_trace_fri_challenge s)"
    and trace_out:
      "Some ((trace_roots, trace_bs'), s2) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A 1
              (ceil_log clength - 1) (trace_bs @ [b]))
            s1)"
    and trace_final_out:
      "Some (trace_final, s3) \<in>
        set_dist (execute (trace_final_stage A trace_bs') s2)"
    and trace_final_record_out:
      "Some ((), s4) \<in>
        set_dist (execute (ro_record_staged_message trace_final) s3)"
    and alpha_out:
      "Some (as, s5) \<in>
        set_dist (execute (ro_staged_alpha_program (length spec)) s4)"
    and degree_out:
      "Some (dg, s6) \<in>
        set_dist (execute (degree_stage A as) s5)"
    and degree_record_out:
      "Some ((), s7) \<in>
        set_dist (execute (ro_record_staged_message dg) s6)"
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
    and composition_final_out:
      "Some (composition_final, s10) \<in>
        set_dist
          (execute
            (composition_final_stage A dg composition_bs)
            s9)"
    and composition_final_record_out:
      "Some ((), s11) \<in>
        set_dist
          (execute
            (ro_record_staged_message composition_final)
            s10)"
    and t_eq: "t = s11"
    using outcome
    unfolding
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def
      rounds_eq
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
  have challenge_ext: "s \<le> s1"
    using receive_trace_fri_challenge_outcome[OF challenge_out] by simp
  have challenge_counter: "PQueryCounter s1 = PQueryCounter s"
    using receive_trace_fri_challenge_counter_outcome[OF challenge_out]
    by simp
  have trace_bound:
    "1 + (ceil_log clength - 1) \<le> length (trace_fri_budgets budgets)"
    using nonempty wf
    unfolding staged_budget_wellformed_def
    by simp
  have trace_props:
    "ro_absorb_lookup_chain s2 (PState s1) trace_roots (PState s2) \<and>
      s1 \<le> s2"
    by (rule ro_staged_trace_fri_program_absorb_lookup_chain[
      OF controlled trace_bound trace_out])
  have trace_counter: "PQueryCounter s2 = PQueryCounter s1"
    by (rule ro_staged_trace_fri_program_query_counter[
      OF controlled trace_bound trace_out])
  have trace_final_controlled:
    "controlled_ro_program (trace_final_budget budgets)
      (trace_final_stage A trace_bs')"
    using controlled
    unfolding staged_adversary_controlled_def
    by blast
  have trace_final_ext: "s2 \<le> s3"
    using controlled_ro_program_extension[
      OF trace_final_controlled] trace_final_out
    unfolding hash_extension_preserving_def
    by blast
  have trace_final_counter: "PQueryCounter s3 = PQueryCounter s2"
    using controlled_stage_outcome_fields[
      OF trace_final_controlled trace_final_out]
    by simp
  have trace_record_props: "s3 \<le> s4"
    using ro_record_staged_message_absorb_lookup_state[
      OF trace_final_record_out]
    by blast
  have trace_record_counter: "PQueryCounter s4 = PQueryCounter s3"
    using ro_record_staged_message_hash_extends_query_counter[
      OF trace_final_record_out]
    by simp
  have alpha_props:
    "ro_absorb_lookup_chain s5 (PState s4) as (PState s5) \<and> s4 \<le> s5"
    by (rule ro_staged_alpha_program_absorb_lookup_chain[OF alpha_out])
  have alpha_counter: "PQueryCounter s5 = PQueryCounter s4"
    by (rule ro_staged_alpha_program_query_counter[OF alpha_out])
  have degree_controlled:
    "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled
    unfolding staged_adversary_controlled_def
    by blast
  have degree_ext: "s5 \<le> s6"
    using controlled_ro_program_extension[OF degree_controlled] degree_out
    unfolding hash_extension_preserving_def
    by blast
  have degree_counter: "PQueryCounter s6 = PQueryCounter s5"
    using controlled_stage_outcome_fields[OF degree_controlled degree_out]
    by simp
  have degree_record_ext: "s6 \<le> s7"
    using ro_record_staged_message_absorb_lookup_state[
      OF degree_record_out]
    by blast
  have degree_record_counter: "PQueryCounter s7 = PQueryCounter s6"
    using ro_record_staged_message_hash_extends_query_counter[
      OF degree_record_out]
    by simp
  have s8_eq: "s8 = s7"
    using assert_out
    unfolding assert_def
    by (cases
      "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_bound:
    "0 + ceil_log (to_nat dg + 1) \<le>
      length (composition_fri_budgets budgets)"
    using assert_out wf
    unfolding assert_def staged_budget_wellformed_def
    by (cases
      "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_props:
    "ro_absorb_lookup_chain s9 (PState s8) composition_roots
        (PState s9) \<and>
      s8 \<le> s9"
    by (rule ro_staged_composition_fri_program_absorb_lookup_chain[
      OF controlled composition_bound composition_out])
  have composition_counter: "PQueryCounter s9 = PQueryCounter s8"
    by (rule ro_staged_composition_fri_program_query_counter[
      OF controlled composition_bound composition_out])
  have composition_final_controlled:
    "controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg composition_bs)"
    using controlled
    unfolding staged_adversary_controlled_def
    by blast
  have composition_final_ext: "s9 \<le> s10"
    using controlled_ro_program_extension[
      OF composition_final_controlled] composition_final_out
    unfolding hash_extension_preserving_def
    by blast
  have composition_final_counter: "PQueryCounter s10 = PQueryCounter s9"
    using controlled_stage_outcome_fields[
      OF composition_final_controlled composition_final_out]
    by simp
  have composition_record_ext: "s10 \<le> s11"
    using ro_record_staged_message_absorb_lookup_state[
      OF composition_final_record_out]
    by blast
  have composition_record_counter: "PQueryCounter s11 = PQueryCounter s10"
    using ro_record_staged_message_hash_extends_query_counter[
      OF composition_final_record_out]
    by simp
  have ext: "s \<le> s11"
    using challenge_ext conjunct2[OF trace_props] trace_final_ext
      trace_record_props conjunct2[OF alpha_props] degree_ext
      degree_record_ext s8_eq conjunct2[OF composition_props]
      composition_final_ext composition_record_ext
    by (metis hash_ext_trans)
  have counter: "PQueryCounter s11 = PQueryCounter s"
    using challenge_counter trace_counter trace_final_counter
      trace_record_counter alpha_counter degree_counter
      degree_record_counter s8_eq composition_counter
      composition_final_counter composition_record_counter
    by simp
  show ?thesis
    using ext counter t_eq by simp
qed

lemma ro_checked_staged_transcript_program_with_first_root_good_fields:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
  shows "prefix_state \<le> attacker_state \<and> PQueryCounter query_start = 0"
proof -
  from ro_checked_staged_transcript_program_with_first_root_outcomeE[OF outcome]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute
            (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A prefix)
            prefix_final)"
    and query_out:
      "Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots head_data)
              (staged_composition_fri_roots head_data)
              query_start 0 rounds)
            query_start)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    by blast
  obtain fr trace_bs first_root where prefix_eq:
    "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  have prefix_props:
    "prefix_state = prefix_final \<and>
      adversary_initial_state \<le> prefix_final \<and>
      PQueryCounter prefix_final = PQueryCounter adversary_initial_state"
    using ro_staged_first_trace_fri_root_prefix_program_chain[
      OF wf controlled nonempty prefix_out[unfolded prefix_eq]]
    by blast
  have after_props:
    "prefix_final \<le> query_start \<and>
      PQueryCounter query_start = PQueryCounter prefix_final"
    by (rule ro_checked_staged_after_first_trace_fri_root_prefix_program_facts[
      OF nonempty wf controlled after_out[unfolded prefix_eq]])
  have query_ext: "query_start \<le> attacker_state"
    using
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled outcome]
    by blast
  have prefix_ext: "prefix_state \<le> attacker_state"
    using prefix_props after_props query_ext
    by (metis hash_ext_trans)
  have query_counter: "PQueryCounter query_start = 0"
    using prefix_props after_props
    unfolding adversary_initial_state_def
    by simp
  show ?thesis
    using prefix_ext query_counter by blast
qed

lemma ro_checked_staged_transcript_program_with_first_root_map_domain_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision attacker_state"
  shows
    "card (fmdom' (HashMap attacker_state)) \<le>
      ro_checked_staged_transcript_hash_query_budget_for budgets"
proof -
  have original_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program A)
          adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty outcome])
  have output_bound:
    "card (hash_map_output_values attacker_state) \<le>
      card (hash_map_output_values adversary_initial_state) +
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    using hash_range_budget_ro_checked_staged_transcript_program[
      OF wf controlled] original_out
    unfolding hash_range_budget_def
    by blast
  have initial_empty:
    "hash_map_output_values adversary_initial_state = {}"
    unfolding adversary_initial_state_def hash_map_output_values_def
    by simp
  have output_bound':
    "card (hash_map_output_values attacker_state) \<le>
      ro_checked_staged_transcript_hash_query_budget_for budgets"
    using output_bound initial_empty by simp
  have domain_output:
    "card (fmdom' (HashMap attacker_state)) \<le>
      card (hash_map_output_values attacker_state)"
    by (rule card_fmdom_le_hash_map_output_values_if_no_collision[OF clean])
  show ?thesis
    using domain_output output_bound' by simp
qed

lemma ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision attacker_state"
  shows
    "card (fmdom' (HashMap attacker_state)) \<le>
      ro_checked_staged_transcript_hash_query_budget_for budgets"
proof -
  have original_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program A)
          adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have output_bound:
    "card (hash_map_output_values attacker_state) \<le>
      card (hash_map_output_values adversary_initial_state) +
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    using hash_range_budget_ro_checked_staged_transcript_program[
      OF wf controlled] original_out
    unfolding hash_range_budget_def
    by blast
  have initial_empty:
    "hash_map_output_values adversary_initial_state = {}"
    unfolding adversary_initial_state_def hash_map_output_values_def
    by simp
  have output_bound':
    "card (hash_map_output_values attacker_state) \<le>
      ro_checked_staged_transcript_hash_query_budget_for budgets"
    using output_bound initial_empty by simp
  have domain_output:
    "card (fmdom' (HashMap attacker_state)) \<le>
      card (hash_map_output_values attacker_state)"
    by (rule card_fmdom_le_hash_map_output_values_if_no_collision[OF clean])
  show ?thesis
    using domain_output output_bound' by simp
qed


lemma first_root_prequery_good_imp_budgeted_relation_transition:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and prequery:
      "ro_checked_staged_first_root_dependent_query_start_prequery_hit
        first_trace_fri_root_prefix_base_agreement_query_lists
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
    and trace_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_trace_table prefix prefix_state)"
    and first_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
    and distinct:
      "first_trace_fri_root_prefix_trace_table prefix prefix_state \<noteq>
        first_trace_fri_root_prefix_first_table prefix prefix_state"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values attacker_state"
    and no_merkle:
      "\<not> hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state attacker_state"
  shows
    "hash_state_relation_transition
      (first_root_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have fields:
    "prefix_state \<le> attacker_state \<and> PQueryCounter query_start = 0"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_good_fields[
        OF wf controlled nonempty outcome])
  have map_bound:
    "card (fmdom' (HashMap attacker_state)) \<le>
      ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound[
        OF wf controlled nonempty outcome clean])
  show ?thesis
    by (rule first_root_prequery_good_imp_bounded_relation_transition[
      OF wf controlled nonempty outcome prequery trace_low first_low distinct
        clean no_initial conjunct1[OF fields] no_merkle map_bound
        conjunct2[OF fields]])
qed

end
end
