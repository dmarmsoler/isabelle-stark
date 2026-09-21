theory Soundness_FRI_Conditioned_Challenge_Outcome_Bridge
  imports Stark.Soundness_FRI_Conditioned_Challenge_Relation
begin

context soundness
begin

lemma ro_staged_trace_fri_program_challenge_prefix:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
    and outcome:
      "Some ((roots, bs'), t) \<in>
        set_dist (execute (ro_staged_trace_fri_program A i n bs) s)"
  shows
    "\<exists>sampled.
      bs' = bs @ sampled \<and>
      length roots = n \<and>
      length sampled = n \<and>
      (\<forall>j < n. \<exists>final.
        ro_absorb_lookup_chain t (PState s) (take (Suc j) roots) final \<and>
        fmlookup (HashMap t)
          (TraceFriChallenge (PTraceFriCounter s + j) final) =
          Some (sampled ! j))"
  proof -
  show ?thesis
    using outcome bound controlled
  proof (induction n arbitrary: i bs s roots bs' t)
    case 0
    then show ?case
      by (intro exI[where x="[]"]) simp
  next
    case (Suc n)
    from Suc.prems(1) obtain root s1 s2 b s3 roots_tail bs_tail where
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
      and roots_eq: "roots = root # roots_tail"
      and bs'_eq: "bs' = bs_tail"
      unfolding ro_staged_trace_fri_program.simps
      by (auto elim!: set_dist_bindE split: prod.splits)
    have i_bound: "i < length (trace_fri_budgets budgets)"
      using Suc.prems(2) by simp
    have tail_bound:
        "Suc i + n \<le> length (trace_fri_budgets budgets)"
      using Suc.prems(2) by simp
    have stage_controlled:
        "controlled_ro_program (trace_fri_budgets budgets ! i)
          (trace_fri_root_stage A i bs)"
      using Suc.prems(3) i_bound
      unfolding staged_adversary_controlled_def by blast
    have stage_fields:
        "PState s1 = PState s"
        "PTraceFriCounter s1 = PTraceFriCounter s"
      using controlled_stage_outcome_fields[OF stage_controlled stage_out]
      by simp_all
    have record_props:
        "fmlookup (HashMap s2)
          (TranscriptAbsorb (PState s1) root) = Some (PState s2) \<and>
         s1 \<le> s2"
      by (rule ro_record_staged_message_absorb_lookup_state[OF record_out])
    have record_counter:
        "PTraceFriCounter s2 = PTraceFriCounter s1"
      using ro_record_staged_message_counter_preserves[OF record_out]
      by simp
    have challenge_props:
        "s2 \<le> s3 \<and>
         PState s3 = PState s2 \<and>
         fmlookup (HashMap s3)
           (TraceFriChallenge (PTraceFriCounter s2) (PState s2)) = Some b"
      using receive_trace_fri_challenge_outcome[OF challenge_out]
      by simp
    have challenge_counter:
        "PTraceFriCounter s3 = Suc (PTraceFriCounter s2)"
      using receive_trace_fri_challenge_counter_outcome[OF challenge_out]
      by simp
    have tail_props:
        "ro_absorb_lookup_chain t (PState s3) roots_tail (PState t) \<and>
         s3 \<le> t"
      by (rule ro_staged_trace_fri_program_absorb_lookup_chain[
        OF Suc.prems(3) tail_bound tail_out])
    from Suc.IH[OF tail_out tail_bound Suc.prems(3)]
    obtain sampled_tail where
      bs_tail_eq: "bs_tail = (bs @ [b]) @ sampled_tail"
      and roots_tail_len: "length roots_tail = n"
      and sampled_tail_len: "length sampled_tail = n"
      and tail_prefix:
        "\<forall>j<n. \<exists>final.
          ro_absorb_lookup_chain t (PState s3)
            (take (Suc j) roots_tail) final \<and>
          fmlookup (HashMap t)
            (TraceFriChallenge (PTraceFriCounter s3 + j) final) =
            Some (sampled_tail ! j)"
      by blast
    have s2_t: "s2 \<le> t"
      by (rule hash_ext_trans[
        OF conjunct1[OF challenge_props] conjunct2[OF tail_props]])
    have head_absorb:
        "fmlookup (HashMap t)
          (TranscriptAbsorb (PState s) root) = Some (PState s2)"
      using hash_extension_lookup[OF conjunct1[OF record_props] s2_t]
        stage_fields
      by simp
    have head_chain:
        "ro_absorb_lookup_chain t (PState s) [root] (PState s2)"
      using head_absorb by simp
    have challenge_lookup:
        "fmlookup (HashMap t)
          (TraceFriChallenge (PTraceFriCounter s) (PState s2)) = Some b"
      using hash_extension_lookup[
          OF conjunct2[OF conjunct2[OF challenge_props]]
            conjunct2[OF tail_props]]
        stage_fields record_counter
      by simp
    have prefixes:
        "\<forall>j<Suc n. \<exists>final.
          ro_absorb_lookup_chain t (PState s)
            (take (Suc j) (root # roots_tail)) final \<and>
          fmlookup (HashMap t)
            (TraceFriChallenge (PTraceFriCounter s + j) final) =
            Some ((b # sampled_tail) ! j)"
    proof (intro allI impI)
      fix j
      assume j_bound: "j < Suc n"
      show "\<exists>final.
          ro_absorb_lookup_chain t (PState s)
            (take (Suc j) (root # roots_tail)) final \<and>
          fmlookup (HashMap t)
            (TraceFriChallenge (PTraceFriCounter s + j) final) =
            Some ((b # sampled_tail) ! j)"
      proof (cases j)
        case 0
        then show ?thesis
          using head_chain challenge_lookup by auto
      next
        case (Suc k)
        have k_bound: "k < n"
          using j_bound Suc by simp
        from tail_prefix k_bound obtain final where
          tail_chain:
            "ro_absorb_lookup_chain t (PState s3)
              (take (Suc k) roots_tail) final"
          and tail_lookup:
            "fmlookup (HashMap t)
              (TraceFriChallenge (PTraceFriCounter s3 + k) final) =
              Some (sampled_tail ! k)"
          by blast
        have tail_chain_s2:
            "ro_absorb_lookup_chain t (PState s2)
              (take (Suc k) roots_tail) final"
          using tail_chain challenge_props by simp
        have appended:
            "ro_absorb_lookup_chain t (PState s)
              ([root] @ take (Suc k) roots_tail) final"
          by (rule ro_absorb_lookup_chain_append[OF head_chain tail_chain_s2])
        show ?thesis
          using appended tail_lookup Suc challenge_counter record_counter
            stage_fields
          by auto
      qed
    qed
    show ?case
      apply (rule exI[where x="b # sampled_tail"])
      using bs'_eq bs_tail_eq roots_eq roots_tail_len sampled_tail_len prefixes
      by simp
  qed


qed



lemma ro_staged_composition_fri_program_challenge_prefix:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
    and outcome:
      "Some ((roots, bs'), t) \<in>
        set_dist
          (execute (ro_staged_composition_fri_program A dg i n bs) s)"
  shows
    "\<exists>sampled.
      bs' = bs @ sampled \<and>
      length roots = n \<and>
      length sampled = n \<and>
      (\<forall>j < n. \<exists>final.
        ro_absorb_lookup_chain t (PState s) (take (Suc j) roots) final \<and>
        fmlookup (HashMap t)
          (CompositionFriChallenge (PCompositionFriCounter s + j) final) =
          Some (sampled ! j))"
proof -
  show ?thesis
    using outcome bound controlled
  proof (induction n arbitrary: i bs s roots bs' t)
    case 0
    then show ?case
      by (intro exI[where x="[]"]) simp
  next
    case (Suc n)
    from Suc.prems(1) obtain root s1 s2 b s3 roots_tail bs_tail where
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
                (bs @ [b]))
              s3)"
      and roots_eq: "roots = root # roots_tail"
      and bs'_eq: "bs' = bs_tail"
      unfolding ro_staged_composition_fri_program.simps
      by (auto elim!: set_dist_bindE split: prod.splits)
    have i_bound: "i < length (composition_fri_budgets budgets)"
      using Suc.prems(2) by simp
    have tail_bound:
        "Suc i + n \<le> length (composition_fri_budgets budgets)"
      using Suc.prems(2) by simp
    have stage_controlled:
        "controlled_ro_program (composition_fri_budgets budgets ! i)
          (composition_fri_root_stage A dg i bs)"
      using Suc.prems(3) i_bound
      unfolding staged_adversary_controlled_def by blast
    have stage_fields:
        "PState s1 = PState s"
        "PCompositionFriCounter s1 = PCompositionFriCounter s"
      using controlled_stage_outcome_fields[OF stage_controlled stage_out]
      by simp_all
    have record_props:
        "fmlookup (HashMap s2)
          (TranscriptAbsorb (PState s1) root) = Some (PState s2) \<and>
         s1 \<le> s2"
      by (rule ro_record_staged_message_absorb_lookup_state[OF record_out])
    have record_counter:
        "PCompositionFriCounter s2 = PCompositionFriCounter s1"
      using ro_record_staged_message_counter_preserves[OF record_out]
      by simp
    have challenge_props:
        "s2 \<le> s3 \<and>
         PState s3 = PState s2 \<and>
         fmlookup (HashMap s3)
           (CompositionFriChallenge
             (PCompositionFriCounter s2) (PState s2)) = Some b"
      using receive_composition_fri_challenge_outcome[OF challenge_out]
      by simp
    have challenge_counter:
        "PCompositionFriCounter s3 =
          Suc (PCompositionFriCounter s2)"
      using receive_composition_fri_challenge_counter_outcome[OF challenge_out]
      by simp
    have tail_props:
        "ro_absorb_lookup_chain t (PState s3) roots_tail (PState t) \<and>
         s3 \<le> t"
      by (rule ro_staged_composition_fri_program_absorb_lookup_chain[
        OF Suc.prems(3) tail_bound tail_out])
    from Suc.IH[OF tail_out tail_bound Suc.prems(3)]
    obtain sampled_tail where
      bs_tail_eq: "bs_tail = (bs @ [b]) @ sampled_tail"
      and roots_tail_len: "length roots_tail = n"
      and sampled_tail_len: "length sampled_tail = n"
      and tail_prefix:
        "\<forall>j<n. \<exists>final.
          ro_absorb_lookup_chain t (PState s3)
            (take (Suc j) roots_tail) final \<and>
          fmlookup (HashMap t)
            (CompositionFriChallenge
              (PCompositionFriCounter s3 + j) final) =
            Some (sampled_tail ! j)"
      by blast
    have s2_t: "s2 \<le> t"
      by (rule hash_ext_trans[
        OF conjunct1[OF challenge_props] conjunct2[OF tail_props]])
    have head_absorb:
        "fmlookup (HashMap t)
          (TranscriptAbsorb (PState s) root) = Some (PState s2)"
      using hash_extension_lookup[OF conjunct1[OF record_props] s2_t]
        stage_fields
      by simp
    have head_chain:
        "ro_absorb_lookup_chain t (PState s) [root] (PState s2)"
      using head_absorb by simp
    have challenge_lookup:
        "fmlookup (HashMap t)
          (CompositionFriChallenge
            (PCompositionFriCounter s) (PState s2)) = Some b"
      using hash_extension_lookup[
          OF conjunct2[OF conjunct2[OF challenge_props]]
            conjunct2[OF tail_props]]
        stage_fields record_counter
      by simp
    have prefixes:
        "\<forall>j<Suc n. \<exists>final.
          ro_absorb_lookup_chain t (PState s)
            (take (Suc j) (root # roots_tail)) final \<and>
          fmlookup (HashMap t)
            (CompositionFriChallenge
              (PCompositionFriCounter s + j) final) =
            Some ((b # sampled_tail) ! j)"
    proof (intro allI impI)
      fix j
      assume j_bound: "j < Suc n"
      show "\<exists>final.
          ro_absorb_lookup_chain t (PState s)
            (take (Suc j) (root # roots_tail)) final \<and>
          fmlookup (HashMap t)
            (CompositionFriChallenge
              (PCompositionFriCounter s + j) final) =
            Some ((b # sampled_tail) ! j)"
      proof (cases j)
        case 0
        then show ?thesis
          using head_chain challenge_lookup by auto
      next
        case (Suc k)
        have k_bound: "k < n"
          using j_bound Suc by simp
        from tail_prefix k_bound obtain final where
          tail_chain:
            "ro_absorb_lookup_chain t (PState s3)
              (take (Suc k) roots_tail) final"
          and tail_lookup:
            "fmlookup (HashMap t)
              (CompositionFriChallenge
                (PCompositionFriCounter s3 + k) final) =
              Some (sampled_tail ! k)"
          by blast
        have tail_chain_s2:
            "ro_absorb_lookup_chain t (PState s2)
              (take (Suc k) roots_tail) final"
          using tail_chain challenge_props by simp
        have appended:
            "ro_absorb_lookup_chain t (PState s)
              ([root] @ take (Suc k) roots_tail) final"
          by (rule ro_absorb_lookup_chain_append[OF head_chain tail_chain_s2])
        show ?thesis
          using appended tail_lookup Suc challenge_counter record_counter
            stage_fields
          by auto
      qed
    qed
    show ?case
      apply (rule exI[where x="b # sampled_tail"])
      using bs'_eq bs_tail_eq roots_eq roots_tail_len sampled_tail_len prefixes
      by simp
  qed
qed


lemma ro_checked_staged_transcript_program_conditioned_challenge_prefixes:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
  shows
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     (\<forall>j < length (staged_trace_fri_roots data). \<exists>final.
       ro_absorb_lookup_chain t (PState adversary_initial_state)
         (staged_trace_root data #
           take (Suc j) (staged_trace_fri_roots data)) final \<and>
       fmlookup (HashMap t) (TraceFriChallenge j final) =
         Some (staged_trace_fri_challenges data ! j)) \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (Suc (to_nat (staged_degree data))) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (Suc (to_nat (staged_degree data))) \<and>
     (\<forall>j < length (staged_composition_fri_roots data). \<exists>final.
       ro_absorb_lookup_chain t (PState adversary_initial_state)
         (composition_fri_challenge_prefix_messages
           (staged_trace_root data)
           (staged_trace_fri_roots data)
           (staged_trace_final data)
           (staged_alphas data)
           (staged_degree data)
           (staged_composition_fri_roots data) j) final \<and>
       fmlookup (HashMap t) (CompositionFriChallenge j final) =
         Some (staged_composition_fri_challenges data ! j))"
  proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3
      trace_final s4 s5 as s6 dg s7 s8 s9
      composition_roots composition_bs s10 composition_final s11 s12
      query_chunks where
    root_out:
      "Some (fr, s1) \<in>
        set_dist
          (execute (trace_root_stage A) adversary_initial_state)"
    and root_record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message fr) s1)"
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
      "Some (dg, s7) \<in>
        set_dist (execute (degree_stage A as) s6)"
    and degree_record_out:
      "Some ((), s8) \<in>
        set_dist (execute (ro_record_staged_message dg) s7)"
    and assert_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))
            s8)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])
            s9)"
    and composition_final_out:
      "Some (composition_final, s11) \<in>
        set_dist
          (execute
            (composition_final_stage A dg composition_bs) s10)"
    and composition_final_record_out:
      "Some ((), s12) \<in>
        set_dist
          (execute (ro_record_staged_message composition_final) s11)"
    and query_out:
      "Some (query_chunks, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots
              composition_roots 0 rounds)
            s12)"
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
  have trace_bound:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have composition_bound:
      "0 + ceil_log (to_nat dg + 1) \<le>
        length (composition_fri_budgets budgets)"
    using wf assert_out
    unfolding staged_budget_wellformed_def assert_def
    by (cases
      "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  from ro_staged_trace_fri_program_challenge_prefix[
      OF controlled trace_bound trace_out]
  obtain trace_sampled where
    trace_bs_eq: "trace_bs = [] @ trace_sampled"
    and trace_roots_len: "length trace_roots = ceil_log clength"
    and trace_sampled_len: "length trace_sampled = ceil_log clength"
    and trace_prefix:
      "\<forall>j<ceil_log clength. \<exists>final.
        ro_absorb_lookup_chain s3 (PState s2)
          (take (Suc j) trace_roots) final \<and>
        fmlookup (HashMap s3)
          (TraceFriChallenge (PTraceFriCounter s2 + j) final) =
          Some (trace_sampled ! j)"
    by blast
  have trace_bs_sampled: "trace_bs = trace_sampled"
    using trace_bs_eq by simp
  from ro_staged_composition_fri_program_challenge_prefix[
      OF controlled composition_bound composition_out]
  obtain composition_sampled where
    composition_bs_eq: "composition_bs = [] @ composition_sampled"
    and composition_roots_len:
      "length composition_roots = ceil_log (to_nat dg + 1)"
    and composition_sampled_len:
      "length composition_sampled = ceil_log (to_nat dg + 1)"
    and composition_prefix:
      "\<forall>j<ceil_log (to_nat dg + 1). \<exists>final.
        ro_absorb_lookup_chain s10 (PState s9)
          (take (Suc j) composition_roots) final \<and>
        fmlookup (HashMap s10)
          (CompositionFriChallenge
            (PCompositionFriCounter s9 + j) final) =
          Some (composition_sampled ! j)"
    by blast
  have composition_bs_sampled: "composition_bs = composition_sampled"
    using composition_bs_eq by simp
  have alpha_len: "length as = length spec"
    by (rule ro_staged_alpha_program_output_length[OF alpha_out])

  have root_controlled:
      "controlled_ro_program (trace_root_budget budgets) (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have root_fields:
      "PState s1 = PState adversary_initial_state"
      "PTraceFriCounter s1 = PTraceFriCounter adversary_initial_state"
      "PCompositionFriCounter s1 =
        PCompositionFriCounter adversary_initial_state"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by blast+
  have root_record:
      "fmlookup (HashMap s2)
        (TranscriptAbsorb (PState s1) fr) = Some (PState s2) \<and>
       s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF root_record_out])
  have root_record_counters:
      "PTraceFriCounter s2 = PTraceFriCounter s1 \<and>
       PCompositionFriCounter s2 = PCompositionFriCounter s1"
    using ro_record_staged_message_counter_preserves[OF root_record_out]
    by simp
  have root_chain_s2:
      "ro_absorb_lookup_chain s2 (PState adversary_initial_state)
        [fr] (PState s2)"
    using root_record root_fields by auto

  have trace_props:
      "ro_absorb_lookup_chain s3 (PState s2) trace_roots (PState s3) \<and>
       s2 \<le> s3"
    by (rule ro_staged_trace_fri_program_absorb_lookup_chain[
      OF controlled trace_bound trace_out])
  have trace_counters:
      "PCompositionFriCounter s3 = PCompositionFriCounter s2"
    using ro_staged_trace_fri_program_counters[
      OF controlled trace_bound trace_out]
    by simp

  have trace_final_controlled:
      "controlled_ro_program (trace_final_budget budgets)
        (trace_final_stage A trace_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have trace_final_stage:
      "s3 \<le> s4"
      "PState s4 = PState s3"
      "PCompositionFriCounter s4 = PCompositionFriCounter s3"
    using controlled_ro_program_extension[
        OF trace_final_controlled] trace_final_out
      controlled_stage_outcome_fields[
        OF trace_final_controlled trace_final_out]
    unfolding hash_extension_preserving_def
    by blast+
  have trace_final_record:
      "fmlookup (HashMap s5)
        (TranscriptAbsorb (PState s4) trace_final) = Some (PState s5) \<and>
       s4 \<le> s5"
    by (rule ro_record_staged_message_absorb_lookup_state[
      OF trace_final_record_out])
  have trace_final_record_counter:
      "PCompositionFriCounter s5 = PCompositionFriCounter s4"
    using ro_record_staged_message_counter_preserves[
      OF trace_final_record_out]
    by simp
  have trace_final_chain_s5:
      "ro_absorb_lookup_chain s5 (PState s3)
        [trace_final] (PState s5)"
    apply (simp only: ro_absorb_lookup_chain.simps)
    apply (rule exI[where x="PState s5"])
    using conjunct1[OF trace_final_record] trace_final_stage(2)
    by simp

  have alpha_props:
      "ro_absorb_lookup_chain s6 (PState s5) as (PState s6) \<and>
       s5 \<le> s6"
    by (rule ro_staged_alpha_program_absorb_lookup_chain[OF alpha_out])
  have alpha_counter:
      "PCompositionFriCounter s6 = PCompositionFriCounter s5"
    using ro_staged_alpha_program_counters[OF alpha_out] by simp

  have degree_controlled:
      "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have degree_stage:
      "s6 \<le> s7"
      "PState s7 = PState s6"
      "PCompositionFriCounter s7 = PCompositionFriCounter s6"
    using controlled_ro_program_extension[OF degree_controlled] degree_out
      controlled_stage_outcome_fields[OF degree_controlled degree_out]
    unfolding hash_extension_preserving_def
    by blast+
  have degree_record:
      "fmlookup (HashMap s8)
        (TranscriptAbsorb (PState s7) dg) = Some (PState s8) \<and>
       s7 \<le> s8"
    by (rule ro_record_staged_message_absorb_lookup_state[
      OF degree_record_out])
  have degree_record_counter:
      "PCompositionFriCounter s8 = PCompositionFriCounter s7"
    using ro_record_staged_message_counter_preserves[OF degree_record_out]
    by simp
  have degree_chain_s8:
      "ro_absorb_lookup_chain s8 (PState s6) [dg] (PState s8)"
    using degree_record degree_stage by auto
  have s9_eq: "s9 = s8"
    by (rule assert_unit_outcomeD(2)[OF assert_out])

  have composition_props:
      "ro_absorb_lookup_chain s10 (PState s9)
          composition_roots (PState s10) \<and>
       s9 \<le> s10"
    by (rule ro_staged_composition_fri_program_absorb_lookup_chain[
      OF controlled composition_bound composition_out])

  have composition_final_controlled:
      "controlled_ro_program (composition_final_budget budgets)
        (composition_final_stage A dg composition_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_stage_ext: "s10 \<le> s11"
    using controlled_ro_program_extension[
      OF composition_final_controlled] composition_final_out
    unfolding hash_extension_preserving_def by blast
  have composition_final_record_ext: "s11 \<le> s12"
    using ro_record_staged_message_absorb_lookup_state[
      OF composition_final_record_out]
    by blast
  have query_bound:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_ext: "s12 \<le> t"
    using ro_checked_staged_query_program_absorb_lookup_chain[
      OF controlled query_bound query_out]
    by blast

  have s10_t: "s10 \<le> t"
    by (meson composition_final_stage_ext composition_final_record_ext
      query_ext hash_ext_trans)
  have s9_t: "s9 \<le> t"
    by (rule hash_ext_trans[OF conjunct2[OF composition_props] s10_t])
  have s8_t: "s8 \<le> t"
    using s9_t s9_eq by simp
  have s6_s8: "s6 \<le> s8"
    by (rule hash_ext_trans[OF degree_stage(1) conjunct2[OF degree_record]])
  have s6_t: "s6 \<le> t"
    by (rule hash_ext_trans[OF s6_s8 s8_t])
  have s5_t: "s5 \<le> t"
    by (rule hash_ext_trans[OF conjunct2[OF alpha_props] s6_t])
  have s3_s5: "s3 \<le> s5"
    by (rule hash_ext_trans[
      OF trace_final_stage(1) conjunct2[OF trace_final_record]])
  have s3_t: "s3 \<le> t"
    by (rule hash_ext_trans[OF s3_s5 s5_t])
  have s2_t: "s2 \<le> t"
    by (rule hash_ext_trans[OF conjunct2[OF trace_props] s3_t])

  have trace_start_counter: "PTraceFriCounter s2 = 0"
    using root_fields root_record_counters
    unfolding adversary_initial_state_def by simp
  have composition_start_counter: "PCompositionFriCounter s9 = 0"
    using root_fields root_record_counters trace_counters trace_final_stage
      trace_final_record_counter alpha_counter degree_stage
      degree_record_counter s9_eq
    unfolding adversary_initial_state_def by simp

  have root_chain_t:
      "ro_absorb_lookup_chain t (PState adversary_initial_state)
        [fr] (PState s2)"
    by (rule ro_absorb_lookup_chain_mono[OF root_chain_s2 s2_t])
  have trace_chain_t:
      "ro_absorb_lookup_chain t (PState s2)
        trace_roots (PState s3)"
    by (rule ro_absorb_lookup_chain_mono[
      OF conjunct1[OF trace_props] s3_t])
  have trace_final_chain_t:
      "ro_absorb_lookup_chain t (PState s3)
        [trace_final] (PState s5)"
    by (rule ro_absorb_lookup_chain_mono[OF trace_final_chain_s5 s5_t])
  have alpha_chain_t:
      "ro_absorb_lookup_chain t (PState s5) as (PState s6)"
    by (rule ro_absorb_lookup_chain_mono[
      OF conjunct1[OF alpha_props] s6_t])
  have degree_chain_t:
      "ro_absorb_lookup_chain t (PState s6) [dg] (PState s8)"
    by (rule ro_absorb_lookup_chain_mono[OF degree_chain_s8 s8_t])
  have precomposition_chain:
      "ro_absorb_lookup_chain t (PState adversary_initial_state)
        (fr # trace_roots @ [trace_final] @ as @ [dg]) (PState s8)"
  proof -
    have c1:
        "ro_absorb_lookup_chain t (PState adversary_initial_state)
          ([fr] @ trace_roots) (PState s3)"
      by (rule ro_absorb_lookup_chain_append[OF root_chain_t trace_chain_t])
    have c2:
        "ro_absorb_lookup_chain t (PState adversary_initial_state)
          (([fr] @ trace_roots) @ [trace_final]) (PState s5)"
      by (rule ro_absorb_lookup_chain_append[OF c1 trace_final_chain_t])
    have c3:
        "ro_absorb_lookup_chain t (PState adversary_initial_state)
          ((([fr] @ trace_roots) @ [trace_final]) @ as) (PState s6)"
      by (rule ro_absorb_lookup_chain_append[OF c2 alpha_chain_t])
    have c4:
        "ro_absorb_lookup_chain t (PState adversary_initial_state)
          (((([fr] @ trace_roots) @ [trace_final]) @ as) @ [dg])
          (PState s8)"
      by (rule ro_absorb_lookup_chain_append[OF c3 degree_chain_t])
    show ?thesis
      using c4 by simp
  qed

  have trace_result:
      "\<forall>j<length trace_roots. \<exists>final.
        ro_absorb_lookup_chain t (PState adversary_initial_state)
          (fr # take (Suc j) trace_roots) final \<and>
        fmlookup (HashMap t) (TraceFriChallenge j final) =
          Some (trace_bs ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length trace_roots"
    have j_round: "j < ceil_log clength"
      using j_bound trace_roots_len by simp
    from trace_prefix j_round obtain final where
      prefix_chain_s3:
        "ro_absorb_lookup_chain s3 (PState s2)
          (take (Suc j) trace_roots) final"
      and lookup_s3:
        "fmlookup (HashMap s3)
          (TraceFriChallenge (PTraceFriCounter s2 + j) final) =
          Some (trace_sampled ! j)"
      by blast
    have prefix_chain_t:
        "ro_absorb_lookup_chain t (PState s2)
          (take (Suc j) trace_roots) final"
      by (rule ro_absorb_lookup_chain_mono[OF prefix_chain_s3 s3_t])
    have chain:
        "ro_absorb_lookup_chain t (PState adversary_initial_state)
          ([fr] @ take (Suc j) trace_roots) final"
      by (rule ro_absorb_lookup_chain_append[OF root_chain_t prefix_chain_t])
    have lookup_t:
        "fmlookup (HashMap t) (TraceFriChallenge j final) =
          Some (trace_bs ! j)"
      using hash_extension_lookup[OF lookup_s3 s3_t]
        trace_start_counter trace_bs_sampled
      by simp
    show "\<exists>final.
        ro_absorb_lookup_chain t (PState adversary_initial_state)
          (fr # take (Suc j) trace_roots) final \<and>
        fmlookup (HashMap t) (TraceFriChallenge j final) =
          Some (trace_bs ! j)"
      apply (rule exI[where x=final])
      apply (rule conjI)
       using chain apply simp
      using lookup_t by simp
  qed

  have composition_result:
      "\<forall>j<length composition_roots. \<exists>final.
        ro_absorb_lookup_chain t (PState adversary_initial_state)
          (composition_fri_challenge_prefix_messages
            fr trace_roots trace_final as dg composition_roots j) final \<and>
        fmlookup (HashMap t) (CompositionFriChallenge j final) =
          Some (composition_bs ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length composition_roots"
    have j_round: "j < ceil_log (to_nat dg + 1)"
      using j_bound composition_roots_len by simp
    from composition_prefix j_round obtain final where
      prefix_chain_s10:
        "ro_absorb_lookup_chain s10 (PState s9)
          (take (Suc j) composition_roots) final"
      and lookup_s10:
        "fmlookup (HashMap s10)
          (CompositionFriChallenge
            (PCompositionFriCounter s9 + j) final) =
          Some (composition_sampled ! j)"
      by blast
    have prefix_chain_t:
        "ro_absorb_lookup_chain t (PState s8)
          (take (Suc j) composition_roots) final"
      using ro_absorb_lookup_chain_mono[OF prefix_chain_s10 s10_t] s9_eq
      by simp
    have chain:
        "ro_absorb_lookup_chain t (PState adversary_initial_state)
          ((fr # trace_roots @ [trace_final] @ as @ [dg]) @
            take (Suc j) composition_roots) final"
      by (rule ro_absorb_lookup_chain_append[
        OF precomposition_chain prefix_chain_t])
    have chain':
        "ro_absorb_lookup_chain t (PState adversary_initial_state)
          (composition_fri_challenge_prefix_messages
            fr trace_roots trace_final as dg composition_roots j) final"
      using chain
      unfolding composition_fri_challenge_prefix_messages_def by simp
    have lookup_t:
        "fmlookup (HashMap t) (CompositionFriChallenge j final) =
          Some (composition_bs ! j)"
      using hash_extension_lookup[OF lookup_s10 s10_t]
        composition_start_counter composition_bs_sampled
      by simp
    show "\<exists>final.
        ro_absorb_lookup_chain t (PState adversary_initial_state)
          (composition_fri_challenge_prefix_messages
            fr trace_roots trace_final as dg composition_roots j) final \<and>
        fmlookup (HashMap t) (CompositionFriChallenge j final) =
          Some (composition_bs ! j)"
      using chain' lookup_t by blast
  qed

  show ?thesis
    using trace_roots_len trace_sampled_len trace_bs_sampled trace_result
      alpha_len composition_roots_len composition_sampled_len
      composition_bs_sampled composition_result data_eq
    by simp
qed


lemma checked_builder_trace_online_bad_imp_conditioned_relation_active:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision t"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values t"
    and hit:
      "\<exists>j < length (staged_trace_fri_roots data).
        staged_trace_fri_challenges data ! j \<in>
          fri_online_bad_challenges (clength - 1) j t
            (staged_trace_fri_roots data ! j)"
  shows
    "\<exists>x y.
      hash_state_relation_active
        conditioned_trace_fri_bad_challenge_relation (HashMap t) x y"
proof -
  from hit obtain j where
    j_bound: "j < length (staged_trace_fri_roots data)"
    and bad:
      "staged_trace_fri_challenges data ! j \<in>
        fri_online_bad_challenges (clength - 1) j t
          (staged_trace_fri_roots data ! j)"
    by blast
  have prefixes:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength \<and>
       (\<forall>j < length (staged_trace_fri_roots data). \<exists>final.
         ro_absorb_lookup_chain t (PState adversary_initial_state)
           (staged_trace_root data #
             take (Suc j) (staged_trace_fri_roots data)) final \<and>
         fmlookup (HashMap t) (TraceFriChallenge j final) =
           Some (staged_trace_fri_challenges data ! j))"
    using ro_checked_staged_transcript_program_conditioned_challenge_prefixes[
      OF wf controlled outcome]
    by blast
  from prefixes j_bound obtain final where
    chain:
      "ro_absorb_lookup_chain t (PState adversary_initial_state)
        (staged_trace_root data #
          take (Suc j) (staged_trace_fri_roots data)) final"
    and lookup:
      "fmlookup (HashMap t) (TraceFriChallenge j final) =
        Some (staged_trace_fri_challenges data ! j)"
    by blast
  have final_map:
      "HashMap (channel_for_hash_map (HashMap t)) = HashMap t"
    unfolding channel_for_hash_map_def adversary_initial_state_def by simp
  have chain_map:
      "ro_absorb_lookup_chain (channel_for_hash_map (HashMap t))
        (PState adversary_initial_state)
        (staged_trace_root data #
          take (Suc j) (staged_trace_fri_roots data)) final"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule chain)
  have clean_map:
      "\<not> hash_map_output_collision (channel_for_hash_map (HashMap t))"
    using clean final_map unfolding hash_map_output_collision_def by simp
  have no_initial_map:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (HashMap t))"
    using no_initial final_map unfolding hash_map_output_values_def by simp
  have bad_map:
      "staged_trace_fri_challenges data ! j \<in>
        fri_online_bad_challenges (clength - 1) j
          (channel_for_hash_map (HashMap t))
          (staged_trace_fri_roots data ! j)"
  proof -
    have tables:
        "conceptual_table (channel_for_hash_map (HashMap t)) =
          conceptual_table t"
      by (rule ext)+
        (rule conceptual_table_cong_hash_map[OF final_map])
    show ?thesis
      using bad unfolding fri_online_bad_challenges_def
        fri_online_conceptual_layer_def tables
      by simp
  qed
  have rel:
      "conditioned_trace_fri_bad_challenge_relation
        (HashMap t)
        (TraceFriChallenge j final)
        (staged_trace_fri_challenges data ! j)"
    unfolding conditioned_trace_fri_bad_challenge_relation_def Let_def
    apply (intro conjI)
     apply (rule clean_map)
     apply (rule no_initial_map)
    apply (rule exI[where x="staged_trace_root data"])
    apply (rule exI[where x="staged_trace_fri_roots data"])
    apply (rule exI[where x=final])
    apply (rule exI[where x=j])
    using prefixes j_bound chain_map bad_map
    by simp
  have active:
      "hash_state_relation_active
        conditioned_trace_fri_bad_challenge_relation
        (HashMap t)
        (TraceFriChallenge j final)
        (staged_trace_fri_challenges data ! j)"
    unfolding hash_state_relation_active_def using lookup rel by blast
  show ?thesis
    using active by blast
qed


lemma checked_builder_composition_online_bad_imp_conditioned_relation_active:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision t"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values t"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and hit:
      "\<exists>j < length (staged_composition_fri_roots data).
        staged_composition_fri_challenges data ! j \<in>
          fri_online_bad_challenges (to_nat (staged_degree data)) j t
            (staged_composition_fri_roots data ! j)"
  shows
    "\<exists>x y.
      hash_state_relation_active
        conditioned_composition_fri_bad_challenge_relation (HashMap t) x y"
proof -
  from hit obtain j where
    j_bound: "j < length (staged_composition_fri_roots data)"
    and bad:
      "staged_composition_fri_challenges data ! j \<in>
        fri_online_bad_challenges (to_nat (staged_degree data)) j t
          (staged_composition_fri_roots data ! j)"
    by blast
  have prefixes:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_alphas data) = length spec \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (Suc (to_nat (staged_degree data))) \<and>
       (\<forall>j < length (staged_composition_fri_roots data). \<exists>final.
         ro_absorb_lookup_chain t (PState adversary_initial_state)
           (composition_fri_challenge_prefix_messages
             (staged_trace_root data)
             (staged_trace_fri_roots data)
             (staged_trace_final data)
             (staged_alphas data)
             (staged_degree data)
             (staged_composition_fri_roots data) j) final \<and>
         fmlookup (HashMap t) (CompositionFriChallenge j final) =
           Some (staged_composition_fri_challenges data ! j))"
    using ro_checked_staged_transcript_program_conditioned_challenge_prefixes[
      OF wf controlled outcome]
    by blast
  from prefixes j_bound obtain final where
    chain:
      "ro_absorb_lookup_chain t (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data) j) final"
    and lookup:
      "fmlookup (HashMap t) (CompositionFriChallenge j final) =
        Some (staged_composition_fri_challenges data ! j)"
    by blast
  have final_map:
      "HashMap (channel_for_hash_map (HashMap t)) = HashMap t"
    unfolding channel_for_hash_map_def adversary_initial_state_def by simp
  have chain_map:
      "ro_absorb_lookup_chain (channel_for_hash_map (HashMap t))
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data) j) final"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule chain)
  have clean_map:
      "\<not> hash_map_output_collision (channel_for_hash_map (HashMap t))"
    using clean final_map unfolding hash_map_output_collision_def by simp
  have no_initial_map:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (HashMap t))"
    using no_initial final_map unfolding hash_map_output_values_def by simp
  have bad_map:
      "staged_composition_fri_challenges data ! j \<in>
        fri_online_bad_challenges (to_nat (staged_degree data)) j
          (channel_for_hash_map (HashMap t))
          (staged_composition_fri_roots data ! j)"
  proof -
    have tables:
        "conceptual_table (channel_for_hash_map (HashMap t)) =
          conceptual_table t"
      by (rule ext)+
        (rule conceptual_table_cong_hash_map[OF final_map])
    show ?thesis
      using bad unfolding fri_online_bad_challenges_def
        fri_online_conceptual_layer_def tables
      by simp
  qed
  have rel:
      "conditioned_composition_fri_bad_challenge_relation
        (HashMap t)
        (CompositionFriChallenge j final)
        (staged_composition_fri_challenges data ! j)"
    unfolding conditioned_composition_fri_bad_challenge_relation_def Let_def
    apply (intro conjI)
     apply (rule clean_map)
     apply (rule no_initial_map)
    apply (rule exI[where x="staged_trace_root data"])
    apply (rule exI[where x="staged_trace_fri_roots data"])
    apply (rule exI[where x="staged_trace_final data"])
    apply (rule exI[where x="staged_alphas data"])
    apply (rule exI[where x="staged_degree data"])
    apply (rule exI[where x="staged_composition_fri_roots data"])
    apply (rule exI[where x=final])
    apply (rule exI[where x=j])
    using prefixes degree_bound j_bound chain_map bad_map
    by simp
  have active:
      "hash_state_relation_active
        conditioned_composition_fri_bad_challenge_relation
        (HashMap t)
        (CompositionFriChallenge j final)
        (staged_composition_fri_challenges data ! j)"
    unfolding hash_state_relation_active_def using lookup rel by blast
  show ?thesis
    using active by blast
qed


lemma conditioned_relation_active_imp_bounded_initial_transition:
  assumes active: "\<exists>x y. hash_state_relation_active R M x y"
    and domain: "card (fmdom' M) \<le> L"
  shows
    "hash_state_relation_transition
      (conditioned_fri_relation_bounded L R)
      (HashMap adversary_initial_state) M"
proof -
  from active obtain x y where
    active_xy: "hash_state_relation_active R M x y"
    by blast
  have bounded_active:
      "hash_state_relation_active
        (conditioned_fri_relation_bounded L R) M x y"
    using active_xy domain
    unfolding hash_state_relation_active_def
      conditioned_fri_relation_bounded_def
    by blast
  have inactive_initial:
      "\<not> hash_state_relation_active
        (conditioned_fri_relation_bounded L R)
        (HashMap adversary_initial_state) x y"
    unfolding hash_state_relation_active_def adversary_initial_state_def
    by simp
  show ?thesis
    unfolding hash_state_relation_transition_def
    using bounded_active inactive_initial by blast
qed

lemma checked_builder_trace_online_bad_imp_bounded_relation_transition:
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
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values attacker_state"
    and hit:
      "\<exists>j < length (staged_trace_fri_roots data).
        staged_trace_fri_challenges data ! j \<in>
          fri_online_bad_challenges (clength - 1) j attacker_state
            (staged_trace_fri_roots data ! j)"
  shows
    "hash_state_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        conditioned_trace_fri_bad_challenge_relation)
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have active:
      "\<exists>x y.
        hash_state_relation_active
          conditioned_trace_fri_bad_challenge_relation
          (HashMap attacker_state) x y"
    by (rule checked_builder_trace_online_bad_imp_conditioned_relation_active[
      OF wf controlled original_out clean no_initial hit])
  have domain:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds[
        OF wf controlled outcome clean])
  show ?thesis
    by (rule conditioned_relation_active_imp_bounded_initial_transition[
      OF active domain])
qed

lemma checked_builder_composition_online_bad_imp_bounded_relation_transition:
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
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values attacker_state"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and hit:
      "\<exists>j < length (staged_composition_fri_roots data).
        staged_composition_fri_challenges data ! j \<in>
          fri_online_bad_challenges (to_nat (staged_degree data)) j
            attacker_state
            (staged_composition_fri_roots data ! j)"
  shows
    "hash_state_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        conditioned_composition_fri_bad_challenge_relation)
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have active:
      "\<exists>x y.
        hash_state_relation_active
          conditioned_composition_fri_bad_challenge_relation
          (HashMap attacker_state) x y"
    by (rule
      checked_builder_composition_online_bad_imp_conditioned_relation_active[
        OF wf controlled original_out clean no_initial degree_bound hit])
  have domain:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds[
        OF wf controlled outcome clean])
  show ?thesis
    by (rule conditioned_relation_active_imp_bounded_initial_transition[
      OF active domain])
qed
end

end
