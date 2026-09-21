theory Staged_Security_Experiment_RO_Query_State_Bridge
  imports Staged_Security_Experiment_RO_Checked_Replay
begin

context soundness
begin

lemma ro_staged_trace_fri_program_query_counter:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
    and outcome:
      "Some ((roots, bs'), t) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A i n bs) s)"
  shows "PQueryCounter t = PQueryCounter s"
  using bound outcome
proof (induction n arbitrary: i bs s roots bs' t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(2) obtain root s1 s2 b s3 roots_tail bs_tail where
    stage_out:
      "Some (root, s1) \<in>
        set_dist (execute (trace_fri_root_stage A i bs) s)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in>
        set_dist (execute receive_trace_fri_challenge s2)"
    and tail_out:
      "Some ((roots_tail, bs_tail), t) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A (Suc i) n (bs @ [b])) s3)"
    unfolding ro_staged_trace_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  have i_bound: "i < length (trace_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have c1: "PQueryCounter s1 = PQueryCounter s"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have c2: "PQueryCounter s2 = PQueryCounter s1"
    using ro_record_staged_message_hash_extends_query_counter[OF record_out]
    by simp
  have c3: "PQueryCounter s3 = PQueryCounter s2"
    using receive_trace_fri_challenge_counter_outcome[OF challenge_out]
    by simp
  have tail_bound: "Suc i + n \<le> length (trace_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have ctail: "PQueryCounter t = PQueryCounter s3"
    by (rule Suc.IH[OF tail_bound tail_out])
  show ?case
    using ctail c3 c2 c1 by simp
qed

lemma ro_staged_alpha_program_query_counter:
  assumes outcome:
    "Some (as, t) \<in> set_dist (execute (ro_staged_alpha_program n) s)"
  shows "PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction n arbitrary: as s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain a s1 s2 as_tail where
    challenge_out:
      "Some (a, s1) \<in> set_dist (execute receive_alpha_challenge s)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message a) s1)"
    and tail_out:
      "Some (as_tail, t) \<in>
        set_dist (execute (ro_staged_alpha_program n) s2)"
    unfolding ro_staged_alpha_program.simps
    by (auto elim!: set_dist_bindE)
  have c1: "PQueryCounter s1 = PQueryCounter s"
    using receive_alpha_challenge_counter_outcome[OF challenge_out]
    by simp
  have c2: "PQueryCounter s2 = PQueryCounter s1"
    using ro_record_staged_message_hash_extends_query_counter[OF record_out]
    by simp
  have ctail: "PQueryCounter t = PQueryCounter s2"
    by (rule Suc.IH[OF tail_out])
  show ?case
    using ctail c2 c1 by simp
qed

lemma ro_staged_composition_fri_program_query_counter:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
    and outcome:
      "Some ((roots, bs'), t) \<in>
        set_dist
          (execute (ro_staged_composition_fri_program A dg i n bs) s)"
  shows "PQueryCounter t = PQueryCounter s"
  using bound outcome
proof (induction n arbitrary: i bs s roots bs' t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(2) obtain root s1 s2 b s3 roots_tail bs_tail where
    stage_out:
      "Some (root, s1) \<in>
        set_dist (execute (composition_fri_root_stage A dg i bs) s)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in>
        set_dist (execute receive_composition_fri_challenge s2)"
    and tail_out:
      "Some ((roots_tail, bs_tail), t) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg (Suc i) n
              (bs @ [b])) s3)"
    unfolding ro_staged_composition_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  have i_bound: "i < length (composition_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have c1: "PQueryCounter s1 = PQueryCounter s"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have c2: "PQueryCounter s2 = PQueryCounter s1"
    using ro_record_staged_message_hash_extends_query_counter[OF record_out]
    by simp
  have c3: "PQueryCounter s3 = PQueryCounter s2"
    using receive_composition_fri_challenge_counter_outcome[OF challenge_out]
    by simp
  have tail_bound: "Suc i + n \<le> length (composition_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have ctail: "PQueryCounter t = PQueryCounter s3"
    by (rule Suc.IH[OF tail_bound tail_out])
  show ?case
    using ctail c3 c2 c1 by simp
qed


lemma ro_checked_staged_transcript_program_header_absorb_lookup_chainE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, sent) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A) s)"
  obtains query_start where
    "Some (staged_query_chunks data, sent) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data) 0 rounds)
          query_start)"
    "ro_absorb_lookup_chain sent (PState s)
      (verifier_header_messages
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data))
      (PState query_start)"
    "PQueryCounter query_start = PQueryCounter s"
    "query_start \<le> sent"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3
      trace_final s4 s5 as s6 dg s7 s8 s9
      composition_roots composition_bs s10 composition_final s11 s12
      query_chunks where
    root_out:
      "Some (fr, s1) \<in> set_dist (execute (trace_root_stage A) s)"
    and root_record_out:
      "Some ((), s2) \<in> set_dist (execute (ro_record_staged_message fr) s1)"
    and trace_out:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and trace_final_out:
      "Some (trace_final, s4) \<in>
        set_dist (execute (trace_final_stage A trace_bs) s3)"
    and trace_final_record_out:
      "Some ((), s5) \<in>
        set_dist (execute (ro_record_staged_message trace_final) s4)"
    and alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (ro_staged_alpha_program (length spec)) s5)"
    and degree_out:
      "Some (dg, s7) \<in> set_dist (execute (degree_stage A as) s6)"
    and degree_record_out:
      "Some ((), s8) \<in> set_dist (execute (ro_record_staged_message dg) s7)"
    and assert_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1))) s8)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s9)"
    and composition_final_out:
      "Some (composition_final, s11) \<in>
        set_dist
          (execute (composition_final_stage A dg composition_bs) s10)"
    and composition_final_record_out:
      "Some ((), s12) \<in>
        set_dist
          (execute (ro_record_staged_message composition_final) s11)"
    and query_out:
      "Some (query_chunks, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              0 rounds) s12)"
    and data_eq:
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
    unfolding ro_checked_staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have root_controlled:
    "controlled_ro_program (trace_root_budget budgets) (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have root_stage_ext: "s \<le> s1"
    using controlled_ro_program_extension[OF root_controlled] root_out
    unfolding hash_extension_preserving_def by blast
  have root_stage_state: "PState s1 = PState s"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp
  have root_record_props:
    "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) fr) =
      Some (PState s2) \<and> s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF root_record_out])
  have root_chain_s2:
    "ro_absorb_lookup_chain s2 (PState s) [fr] (PState s2)"
    using root_record_props root_stage_state by auto
  have trace_bound:
    "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have trace_props:
    "ro_absorb_lookup_chain s3 (PState s2) trace_roots (PState s3) \<and>
      s2 \<le> s3"
    by (rule ro_staged_trace_fri_program_absorb_lookup_chain
        [OF controlled trace_bound trace_out])
  have trace_final_controlled:
    "controlled_ro_program (trace_final_budget budgets)
      (trace_final_stage A trace_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have trace_final_stage_ext: "s3 \<le> s4"
    using controlled_ro_program_extension[OF trace_final_controlled]
      trace_final_out
    unfolding hash_extension_preserving_def by blast
  have trace_final_stage_state: "PState s4 = PState s3"
    using controlled_stage_outcome_fields
        [OF trace_final_controlled trace_final_out]
    by simp
  have trace_final_record_props:
    "fmlookup (HashMap s5) (TranscriptAbsorb (PState s4) trace_final) =
      Some (PState s5) \<and> s4 \<le> s5"
    by (rule ro_record_staged_message_absorb_lookup_state
        [OF trace_final_record_out])
  have trace_final_chain_s5:
    "ro_absorb_lookup_chain s5 (PState s3) [trace_final] (PState s5)"
    using trace_final_record_props trace_final_stage_state by auto
  have alpha_props:
    "ro_absorb_lookup_chain s6 (PState s5) as (PState s6) \<and> s5 \<le> s6"
    by (rule ro_staged_alpha_program_absorb_lookup_chain[OF alpha_out])
  have degree_controlled:
    "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have degree_stage_ext: "s6 \<le> s7"
    using controlled_ro_program_extension[OF degree_controlled] degree_out
    unfolding hash_extension_preserving_def by blast
  have degree_stage_state: "PState s7 = PState s6"
    using controlled_stage_outcome_fields[OF degree_controlled degree_out]
    by simp
  have degree_record_props:
    "fmlookup (HashMap s8) (TranscriptAbsorb (PState s7) dg) =
      Some (PState s8) \<and> s7 \<le> s8"
    by (rule ro_record_staged_message_absorb_lookup_state
        [OF degree_record_out])
  have degree_chain_s8:
    "ro_absorb_lookup_chain s8 (PState s6) [dg] (PState s8)"
    using degree_record_props degree_stage_state by auto
  have s9_eq: "s9 = s8"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_round_bound:
    "0 + ceil_log (to_nat dg + 1) \<le>
      length (composition_fri_budgets budgets)"
    using assert_out wf unfolding assert_def staged_budget_wellformed_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_props_s9:
    "ro_absorb_lookup_chain s10 (PState s9) composition_roots
      (PState s10) \<and> s9 \<le> s10"
    by (rule ro_staged_composition_fri_program_absorb_lookup_chain
        [OF controlled composition_round_bound composition_out])
  have composition_props:
    "ro_absorb_lookup_chain s10 (PState s8) composition_roots
      (PState s10) \<and> s8 \<le> s10"
    using composition_props_s9 s9_eq by simp
  have composition_final_controlled:
    "controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg composition_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_stage_ext: "s10 \<le> s11"
    using controlled_ro_program_extension[OF composition_final_controlled]
      composition_final_out
    unfolding hash_extension_preserving_def by blast
  have composition_final_stage_state: "PState s11 = PState s10"
    using controlled_stage_outcome_fields
        [OF composition_final_controlled composition_final_out]
    by simp
  have composition_final_record_props:
    "fmlookup (HashMap s12)
      (TranscriptAbsorb (PState s11) composition_final) =
      Some (PState s12) \<and> s11 \<le> s12"
    by (rule ro_record_staged_message_absorb_lookup_state
        [OF composition_final_record_out])
  have composition_final_chain_s12:
    "ro_absorb_lookup_chain s12 (PState s10) [composition_final]
      (PState s12)"
    using composition_final_record_props composition_final_stage_state by auto
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_props:
    "ro_absorb_lookup_chain sent (PState s12) (List.concat query_chunks)
      (PState sent) \<and> s12 \<le> sent"
    by (rule ro_checked_staged_query_program_absorb_lookup_chain
        [OF controlled query_bound query_out])

  have ext_s_s2: "s \<le> s2"
    by (rule hash_ext_trans[OF root_stage_ext conjunct2[OF root_record_props]])
  have ext_s3_s5: "s3 \<le> s5"
    by (rule hash_ext_trans[OF trace_final_stage_ext
          conjunct2[OF trace_final_record_props]])
  have ext_s6_s8: "s6 \<le> s8"
    by (rule hash_ext_trans[OF degree_stage_ext
          conjunct2[OF degree_record_props]])
  have ext_s10_s12: "s10 \<le> s12"
    by (rule hash_ext_trans[OF composition_final_stage_ext
          conjunct2[OF composition_final_record_props]])
  have ext_s2_sent: "s2 \<le> sent"
    by (rule hash_ext_trans[OF conjunct2[OF trace_props]])
      (rule hash_ext_trans[OF ext_s3_s5],
        rule hash_ext_trans[OF conjunct2[OF alpha_props]],
        rule hash_ext_trans[OF ext_s6_s8],
        rule hash_ext_trans[OF conjunct2[OF composition_props]],
        rule hash_ext_trans[OF ext_s10_s12 conjunct2[OF query_props]])
  have ext_s3_sent: "s3 \<le> sent"
    by (rule hash_ext_trans[OF ext_s3_s5])
      (rule hash_ext_trans[OF conjunct2[OF alpha_props]],
        rule hash_ext_trans[OF ext_s6_s8],
        rule hash_ext_trans[OF conjunct2[OF composition_props]],
        rule hash_ext_trans[OF ext_s10_s12 conjunct2[OF query_props]])
  have ext_s5_sent: "s5 \<le> sent"
    by (rule hash_ext_trans[OF conjunct2[OF alpha_props]])
      (rule hash_ext_trans[OF ext_s6_s8],
        rule hash_ext_trans[OF conjunct2[OF composition_props]],
        rule hash_ext_trans[OF ext_s10_s12 conjunct2[OF query_props]])
  have ext_s6_sent: "s6 \<le> sent"
    by (rule hash_ext_trans[OF ext_s6_s8])
      (rule hash_ext_trans[OF conjunct2[OF composition_props]],
        rule hash_ext_trans[OF ext_s10_s12 conjunct2[OF query_props]])
  have ext_s8_sent: "s8 \<le> sent"
    by (rule hash_ext_trans[OF conjunct2[OF composition_props]])
      (rule hash_ext_trans[OF ext_s10_s12 conjunct2[OF query_props]])
  have ext_s10_sent: "s10 \<le> sent"
    by (rule hash_ext_trans[OF ext_s10_s12 conjunct2[OF query_props]])
  have root_chain_sent:
    "ro_absorb_lookup_chain sent (PState s) [fr] (PState s2)"
    by (rule ro_absorb_lookup_chain_mono[OF root_chain_s2 ext_s2_sent])
  have trace_chain_sent:
    "ro_absorb_lookup_chain sent (PState s2) trace_roots (PState s3)"
    by (rule ro_absorb_lookup_chain_mono[OF conjunct1[OF trace_props]
          ext_s3_sent])
  have trace_final_chain_sent:
    "ro_absorb_lookup_chain sent (PState s3) [trace_final] (PState s5)"
    by (rule ro_absorb_lookup_chain_mono
        [OF trace_final_chain_s5 ext_s5_sent])
  have alpha_chain_sent:
    "ro_absorb_lookup_chain sent (PState s5) as (PState s6)"
    by (rule ro_absorb_lookup_chain_mono[OF conjunct1[OF alpha_props]
          ext_s6_sent])
  have degree_chain_sent:
    "ro_absorb_lookup_chain sent (PState s6) [dg] (PState s8)"
    by (rule ro_absorb_lookup_chain_mono[OF degree_chain_s8 ext_s8_sent])
  have composition_chain_sent:
    "ro_absorb_lookup_chain sent (PState s8) composition_roots (PState s10)"
    by (rule ro_absorb_lookup_chain_mono[OF conjunct1[OF composition_props]
          ext_s10_sent])
  have composition_final_chain_sent:
    "ro_absorb_lookup_chain sent (PState s10) [composition_final]
      (PState s12)"
    by (rule ro_absorb_lookup_chain_mono
        [OF composition_final_chain_s12 conjunct2[OF query_props]])
  have chain_1:
    "ro_absorb_lookup_chain sent (PState s) ([fr] @ trace_roots)
      (PState s3)"
    by (rule ro_absorb_lookup_chain_append[OF root_chain_sent
          trace_chain_sent])
  have chain_2:
    "ro_absorb_lookup_chain sent (PState s)
      ([fr] @ trace_roots @ [trace_final]) (PState s5)"
    using ro_absorb_lookup_chain_append[OF chain_1
          trace_final_chain_sent]
    by simp
  have chain_3:
    "ro_absorb_lookup_chain sent (PState s)
      ([fr] @ trace_roots @ [trace_final] @ as) (PState s6)"
    using ro_absorb_lookup_chain_append[OF chain_2 alpha_chain_sent]
    by simp
  have chain_4:
    "ro_absorb_lookup_chain sent (PState s)
      ([fr] @ trace_roots @ [trace_final] @ as @ [dg]) (PState s8)"
    using ro_absorb_lookup_chain_append[OF chain_3 degree_chain_sent]
    by simp
  have chain_5:
    "ro_absorb_lookup_chain sent (PState s)
      ([fr] @ trace_roots @ [trace_final] @ as @ [dg] @
        composition_roots) (PState s10)"
    using ro_absorb_lookup_chain_append[OF chain_4 composition_chain_sent]
    by simp
  have header_chain:
    "ro_absorb_lookup_chain sent (PState s)
      ([fr] @ trace_roots @ [trace_final] @ as @ [dg] @
        composition_roots @ [composition_final]) (PState s12)"
    using ro_absorb_lookup_chain_append[OF chain_5
          composition_final_chain_sent]
    by simp

  have root_stage_counter: "PQueryCounter s1 = PQueryCounter s"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp
  have root_record_counter: "PQueryCounter s2 = PQueryCounter s1"
    using ro_record_staged_message_hash_extends_query_counter[OF root_record_out]
    by simp
  have trace_counter: "PQueryCounter s3 = PQueryCounter s2"
    by (rule ro_staged_trace_fri_program_query_counter
        [OF controlled trace_bound trace_out])
  have trace_final_stage_counter: "PQueryCounter s4 = PQueryCounter s3"
    using controlled_stage_outcome_fields
        [OF trace_final_controlled trace_final_out]
    by simp
  have trace_final_record_counter: "PQueryCounter s5 = PQueryCounter s4"
    using ro_record_staged_message_hash_extends_query_counter
        [OF trace_final_record_out]
    by simp
  have alpha_counter: "PQueryCounter s6 = PQueryCounter s5"
    by (rule ro_staged_alpha_program_query_counter[OF alpha_out])
  have degree_stage_counter: "PQueryCounter s7 = PQueryCounter s6"
    using controlled_stage_outcome_fields[OF degree_controlled degree_out]
    by simp
  have degree_record_counter: "PQueryCounter s8 = PQueryCounter s7"
    using ro_record_staged_message_hash_extends_query_counter
        [OF degree_record_out]
    by simp
  have s9_counter: "PQueryCounter s9 = PQueryCounter s8"
    using s9_eq by simp
  have composition_counter: "PQueryCounter s10 = PQueryCounter s9"
    by (rule ro_staged_composition_fri_program_query_counter
        [OF controlled composition_round_bound composition_out])
  have composition_final_stage_counter:
    "PQueryCounter s11 = PQueryCounter s10"
    using controlled_stage_outcome_fields
        [OF composition_final_controlled composition_final_out]
    by simp
  have composition_final_record_counter:
    "PQueryCounter s12 = PQueryCounter s11"
    using ro_record_staged_message_hash_extends_query_counter
        [OF composition_final_record_out]
    by simp
  have query_start_counter: "PQueryCounter s12 = PQueryCounter s"
    using composition_final_record_counter composition_final_stage_counter
      composition_counter s9_counter degree_record_counter
      degree_stage_counter alpha_counter trace_final_record_counter
      trace_final_stage_counter trace_counter root_record_counter
      root_stage_counter
    by simp

  show ?thesis
  proof (rule that[of s12])
    show "Some (staged_query_chunks data, sent) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data) 0 rounds)
          s12)"
      using query_out data_eq by simp
    show "ro_absorb_lookup_chain sent (PState s)
      (verifier_header_messages
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data))
      (PState s12)"
      using header_chain unfolding data_eq verifier_header_messages_def by simp
    show "PQueryCounter s12 = PQueryCounter s"
      by (rule query_start_counter)
    show "s12 \<le> sent"
      using query_props by simp
  qed
qed

lemma ro_checked_staged_transcript_program_header_absorb_read_replay_support_from_verifier_stateE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, sent) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
  obtains query_start where
    "Some (staged_query_chunks data, sent) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data) 0 rounds)
          query_start)"
    "Some
      (verifier_header_messages
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data),
       (verifier_state_from_adversary sent (staged_proof_transcript data))
        \<lparr>PState := PState query_start,
          PTranscript := List.concat (staged_query_chunks data)\<rparr>)
      \<in> set_dist
        (execute
          (ntimes protocol_absorb_read
            (length
              (verifier_header_messages
                (staged_trace_root data)
                (staged_trace_fri_roots data)
                (staged_trace_final data)
                (staged_alphas data)
                (staged_degree data)
                (staged_composition_fri_roots data)
                (staged_composition_final data))))
          (verifier_state_from_adversary sent
            (staged_proof_transcript data)))"
    "query_start \<le> sent"
    "PQueryCounter query_start = 0"
proof -
  from ro_checked_staged_transcript_program_header_absorb_lookup_chainE
      [OF wf controlled outcome]
  obtain query_start where
    query_out:
      "Some (staged_query_chunks data, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data) 0 rounds)
            query_start)"
    and chain:
      "ro_absorb_lookup_chain sent (PState adversary_initial_state)
        (verifier_header_messages
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data))
        (PState query_start)"
    and query_counter:
      "PQueryCounter query_start = PQueryCounter adversary_initial_state"
    and query_ext: "query_start \<le> sent"
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
  let ?r = "verifier_state_from_adversary sent (staged_proof_transcript data)"
  have start_ext: "sent \<le> ?r"
    unfolding verifier_state_from_adversary_def less_eq_hash_ext_def
      less_eq_fmap_def
    by simp
  have start_state: "PState ?r = PState adversary_initial_state"
    by (simp add: adversary_initial_state_def)
  have start_tr:
    "PTranscript ?r = ?header @ List.concat (staged_query_chunks data)"
    unfolding staged_proof_transcript_def by simp
  have replay:
    "Some (?header,
       ?r\<lparr>PState := PState query_start,
          PTranscript := List.concat (staged_query_chunks data)\<rparr>) \<in>
      set_dist (execute (ntimes protocol_absorb_read (length ?header)) ?r)"
    by (rule ro_absorb_lookup_chain_replay_support_from_extension
        [OF chain start_ext start_state start_tr])
  have query_counter_zero: "PQueryCounter query_start = 0"
    using query_counter by simp
  show ?thesis
    by (rule that[OF query_out replay query_ext query_counter_zero])
qed

lemma ro_checked_staged_transcript_program_header_replay_query_witnessesE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, sent) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
  obtains query_start raw_idxs query_idxs query_states where
    "Some (staged_query_chunks data, sent) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data) 0 rounds)
          query_start)"
    "Some
      (verifier_header_messages
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data),
       (verifier_state_from_adversary sent (staged_proof_transcript data))
        \<lparr>PState := PState query_start,
          PTranscript := List.concat (staged_query_chunks data)\<rparr>)
      \<in> set_dist
        (execute
          (ntimes protocol_absorb_read
            (length
              (verifier_header_messages
                (staged_trace_root data)
                (staged_trace_fri_roots data)
                (staged_trace_final data)
                (staged_alphas data)
                (staged_degree data)
                (staged_composition_fri_roots data)
                (staged_composition_final data))))
          (verifier_state_from_adversary sent
            (staged_proof_transcript data)))"
    "query_start \<le> sent"
    "PQueryCounter query_start = 0"
    "length raw_idxs = rounds"
    "length query_states = rounds"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length (staged_query_chunks data) = rounds"
    "PQueryCounter sent = PQueryCounter query_start + rounds"
    "\<forall>j < rounds.
      query_states ! j \<le> sent \<and>
      PQueryCounter (query_states ! j) = PQueryCounter query_start + j \<and>
      fmlookup (HashMap sent)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raw_idxs ! j) \<and>
      verifier_query_round_chunk (query_idxs ! j)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! j)"
    "\<forall>idx \<in> set query_idxs. idx < clength * scale"
proof -
  from ro_checked_staged_transcript_program_header_absorb_read_replay_support_from_verifier_stateE
      [OF wf controlled outcome]
  obtain query_start where
    query_out:
      "Some (staged_query_chunks data, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data) 0 rounds)
            query_start)"
    and replay:
      "Some
        (verifier_header_messages
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data),
         (verifier_state_from_adversary sent (staged_proof_transcript data))
          \<lparr>PState := PState query_start,
            PTranscript := List.concat (staged_query_chunks data)\<rparr>)
        \<in> set_dist
          (execute
            (ntimes protocol_absorb_read
              (length
                (verifier_header_messages
                  (staged_trace_root data)
                  (staged_trace_fri_roots data)
                  (staged_trace_final data)
                  (staged_alphas data)
                  (staged_degree data)
                  (staged_composition_fri_roots data)
                  (staged_composition_final data))))
            (verifier_state_from_adversary sent
              (staged_proof_transcript data)))"
    and query_start_ext: "query_start \<le> sent"
    and query_start_counter: "PQueryCounter query_start = 0"
    by blast
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  from ro_checked_staged_query_program_outcome_with_raws
      [OF controlled query_bound query_out]
  obtain raw_idxs query_idxs query_states where
    len_raw: "length raw_idxs = rounds"
    and len_states: "length query_states = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length (staged_query_chunks data) = rounds"
    and query_ext: "query_start \<le> sent"
    and query_count:
      "PQueryCounter sent = PQueryCounter query_start + rounds"
    and query_props:
      "\<forall>j < rounds.
        query_states ! j \<le> sent \<and>
        PQueryCounter (query_states ! j) = PQueryCounter query_start + j \<and>
        fmlookup (HashMap sent)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raw_idxs ! j) \<and>
        verifier_query_round_chunk (query_idxs ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)"
    and idx_bound: "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by blast
  show ?thesis
    by (rule that[OF query_out replay query_start_ext query_start_counter
          len_raw len_states query_idxs_eq len_chunks query_count
          query_props idx_bound])
qed

end

end
