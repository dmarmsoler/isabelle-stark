theory Staged_Security_Experiment_RO_Verify_Header_Replay
  imports Staged_Security_Experiment_RO_Query_Rounds_Replay
begin

context soundness
begin

text \<open>
  Header replay primitives for the absorbing verifier.  These facts identify
  verifier-side RO header reads against final-map lookups produced by the
  checked RO transcript builder.
\<close>

lemma protocol_absorb_read_counter_preserves:
  fixes s t :: "'f protocol_channel"
  assumes outcome: "Some (x, t) \<in> set_dist (execute protocol_absorb_read s)"
  shows
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
proof (cases "PTranscript s")
  case Nil
  then show ?thesis
    using outcome
    unfolding protocol_absorb_read_def assert_def
    by (auto simp: throw_no_Some_set_dist elim!: set_dist_bindE)
next
  case (Cons z zs)
  let ?s0 = "s\<lparr>PTranscript := []\<rparr>"
  have s_eq: "s = ?s0\<lparr>PTranscript := z # zs\<rparr>"
    using Cons by simp
  have outcome':
    "Some (x, t) \<in>
      set_dist (execute protocol_absorb_read (?s0\<lparr>PTranscript := z # zs\<rparr>))"
    using outcome s_eq by simp
  from protocol_absorb_read_cons_outcome[OF outcome'] obtain h u where
    hash_out:
      "Some (h, u) \<in>
        set_dist
          (execute (hash (TranscriptAbsorb (PState ?s0) z))
            (?s0\<lparr>PTranscript := z # zs\<rparr>))"
    and t_eq: "t = u\<lparr>PState := h, PTranscript := zs\<rparr>"
    by blast
  have counters_u:
    "PTraceFriCounter u = PTraceFriCounter s \<and>
     PCompositionFriCounter u = PCompositionFriCounter s \<and>
     PAlphaCounter u = PAlphaCounter s \<and>
     PQueryCounter u = PQueryCounter s"
    using protocol_hash_channel_preserves(3-6)[OF hash_out] s_eq
    by simp
  show ?thesis
    unfolding t_eq using counters_u by simp
qed

lemma ro_record_staged_message_counter_preserves:
  assumes outcome:
    "Some ((), t) \<in> set_dist (execute (ro_record_staged_message x) s)"
  shows
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  obtain h u where
    t_eq: "t = u\<lparr>PState := h, PTranscript := PTranscript u @ [x]\<rparr>"
    and counters_u:
      "PTraceFriCounter u = PTraceFriCounter s \<and>
       PCompositionFriCounter u = PCompositionFriCounter s \<and>
       PAlphaCounter u = PAlphaCounter s \<and>
       PQueryCounter u = PQueryCounter s"
  proof (rule ro_record_staged_message_outcome[OF outcome])
    fix h u
    assume "Some (h, u) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState s) x)) s)"
      and t_eq':
        "t = u\<lparr>PState := h, PTranscript := PTranscript u @ [x]\<rparr>"
      and "PState u = PState s"
      and "PTranscript u = PTranscript s"
      and trace_counter: "PTraceFriCounter u = PTraceFriCounter s"
      and composition_counter:
        "PCompositionFriCounter u = PCompositionFriCounter s"
      and alpha_counter: "PAlphaCounter u = PAlphaCounter s"
      and query_counter: "PQueryCounter u = PQueryCounter s"
      and "s \<le> u"
    show ?thesis
      by (rule that[OF t_eq'])
        (use trace_counter composition_counter alpha_counter query_counter
          in simp)
  qed
  show ?thesis
    unfolding t_eq using counters_u by simp
qed

lemma controlled_ro_record_staged_message_absorb_read_sync:
  fixes builder staged sent verifier verifier' :: "'f protocol_channel"
    and stage :: "('f, 'f protocol_channel) state_monad"
  assumes controlled: "controlled_ro_program q stage"
    and stage_out:
      "Some (x, staged) \<in> set_dist (execute stage builder)"
    and record_out:
      "Some ((), sent) \<in>
        set_dist (execute (ro_record_staged_message x) staged)"
    and sent_ext: "sent \<le> verifier"
    and state_eq: "PState verifier = PState builder"
    and transcript_prefix: "PTranscript verifier = x # rest"
    and verifier_out:
      "Some (y, verifier') \<in> set_dist (execute protocol_absorb_read verifier)"
  shows
    "y = x \<and>
     PState verifier' = PState sent \<and>
     PTranscript verifier' = rest \<and>
     verifier \<le> verifier' \<and>
     PTraceFriCounter verifier' = PTraceFriCounter verifier \<and>
     PCompositionFriCounter verifier' = PCompositionFriCounter verifier \<and>
     PAlphaCounter verifier' = PAlphaCounter verifier \<and>
     PQueryCounter verifier' = PQueryCounter verifier"
proof -
  have staged_state:
    "PState staged = PState builder"
    using controlled_ro_program_preserves_protocol_fields[OF controlled]
      stage_out
    unfolding protocol_fields_preserving_def by blast
  obtain h u where
    hash_out:
      "Some (h, u) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState staged) x)) staged)"
    and sent_eq:
      "sent = u\<lparr>PState := h, PTranscript := PTranscript u @ [x]\<rparr>"
  proof (rule ro_record_staged_message_outcome[OF record_out])
    fix h u
    assume hash_out':
      "Some (h, u) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState staged) x)) staged)"
      and sent_eq':
        "sent = u\<lparr>PState := h, PTranscript := PTranscript u @ [x]\<rparr>"
      and "PState u = PState staged"
      and "PTranscript u = PTranscript staged"
      and "PTraceFriCounter u = PTraceFriCounter staged"
      and "PCompositionFriCounter u = PCompositionFriCounter staged"
      and "PAlphaCounter u = PAlphaCounter staged"
      and "PQueryCounter u = PQueryCounter staged"
      and "staged \<le> u"
    show ?thesis
      by (rule that[OF hash_out' sent_eq'])
  qed
  have lookup_sent:
    "fmlookup (HashMap sent) (TranscriptAbsorb (PState staged) x) =
      Some (PState sent)"
    using protocol_merkle.hash_outcome(2)[OF hash_out] sent_eq by simp
  have lookup_verifier:
    "fmlookup (HashMap verifier) (TranscriptAbsorb (PState verifier) x) =
      Some (PState sent)"
  proof -
    have "fmlookup (HashMap verifier)
        (TranscriptAbsorb (PState staged) x) = Some (PState sent)"
      by (rule hash_extension_lookup[OF lookup_sent sent_ext])
    then show ?thesis
      using staged_state state_eq by simp
  qed
  have absorb_props:
    "y = x \<and> PState verifier' = PState sent \<and>
     PTranscript verifier' = rest \<and> verifier \<le> verifier'"
    by (rule protocol_absorb_read_known_nonempty_outcome
        [OF transcript_prefix lookup_verifier verifier_out])
  have counters:
    "PTraceFriCounter verifier' = PTraceFriCounter verifier \<and>
     PCompositionFriCounter verifier' = PCompositionFriCounter verifier \<and>
     PAlphaCounter verifier' = PAlphaCounter verifier \<and>
     PQueryCounter verifier' = PQueryCounter verifier"
    by (rule protocol_absorb_read_counter_preserves[OF verifier_out])
  show ?thesis
    using absorb_props counters by simp
qed

lemma ro_checked_staged_transcript_program_outcomeE:
  assumes outcome:
    "Some (data, sent) \<in>
      set_dist (execute (ro_checked_staged_transcript_program A) s)"
  obtains fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 s12 query_chunks where
    "Some (fr, s1) \<in> set_dist (execute (trace_root_stage A) s)"
    "Some ((), s2) \<in> set_dist (execute (ro_record_staged_message fr) s1)"
    "Some ((trace_roots, trace_bs), s3) \<in>
      set_dist
        (execute
          (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    "Some (trace_final, s4) \<in>
      set_dist (execute (trace_final_stage A trace_bs) s3)"
    "Some ((), s5) \<in>
      set_dist (execute (ro_record_staged_message trace_final) s4)"
    "Some (as, s6) \<in>
      set_dist (execute (ro_staged_alpha_program (length spec)) s5)"
    "Some (dg, s7) \<in> set_dist (execute (degree_stage A as) s6)"
    "Some ((), s8) \<in> set_dist (execute (ro_record_staged_message dg) s7)"
    "Some ((), s9) \<in>
      set_dist
        (execute
          (assert
            (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1))) s8)"
    "Some ((composition_roots, composition_bs), s10) \<in>
      set_dist
        (execute
          (ro_staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) []) s9)"
    "Some (composition_final, s11) \<in>
      set_dist
        (execute (composition_final_stage A dg composition_bs) s10)"
    "Some ((), s12) \<in>
      set_dist
        (execute (ro_record_staged_message composition_final) s11)"
    "Some (query_chunks, sent) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots composition_roots
            0 rounds) s12)"
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
  using outcome
  unfolding ro_checked_staged_transcript_program_def Let_def
  by (auto elim!: set_dist_bindE split: prod.splits)

lemma ro_verify_monad_outcomeE:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some (result, t) \<in> set_dist (execute ro_verify_monad s)"
  obtains fr trace_pairs f_final alphas dg composition_pairs final
      s1 s2 s3 s4 s5 s6 s7 s8 where
    "Some (fr, s1) \<in> set_dist (execute protocol_absorb_read s)"
    "Some (trace_pairs, s2) \<in>
      set_dist
        (execute (ntimes ro_receive_trace_fri_commits (ceil_log clength))
          s1)"
    "Some (f_final, s3) \<in> set_dist (execute protocol_absorb_read s2)"
    "Some (alphas, s4) \<in>
      set_dist
        (execute (mmap (replicate (length spec) ro_alpha_round)) s3)"
    "Some (dg, s5) \<in> set_dist (execute protocol_absorb_read s4)"
    "Some ((), s6) \<in>
      set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
    "Some (composition_pairs, s7) \<in>
      set_dist
        (execute
          (ntimes ro_receive_composition_fri_commits
            (ceil_log (to_nat dg + 1))) s6)"
    "Some (final, s8) \<in> set_dist (execute protocol_absorb_read s7)"
    "Some (result, t) \<in>
      set_dist
        (execute
          (ntimes
            (ro_verifier_query_round_program fr trace_pairs f_final alphas
              composition_pairs final) rounds) s8)"
  using outcome
  unfolding ro_verify_monad_def
  by (auto elim!: set_dist_bindE split: prod.splits)

lemma assert_unit_outcomeD:
  assumes outcome: "Some ((), t) \<in> set_dist (execute (assert P) s)"
  shows "P" and "t = s"
  using outcome
  unfolding assert_def
  by (cases P; auto simp: throw_no_Some_set_dist)+

lemma ro_staged_trace_fri_program_counters:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
    and outcome:
      "Some ((roots, bs'), sent) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A i n bs) builder)"
  shows
    "PTraceFriCounter sent = PTraceFriCounter builder + n \<and>
     PCompositionFriCounter sent = PCompositionFriCounter builder \<and>
     PAlphaCounter sent = PAlphaCounter builder \<and>
     PQueryCounter sent = PQueryCounter builder"
  using bound outcome controlled
proof (induction n arbitrary: i bs roots bs' builder sent)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems(2) obtain root s1 s2 b s3 roots_tail bs_tail where
    stage_out:
      "Some (root, s1) \<in>
        set_dist (execute (trace_fri_root_stage A i bs) builder)"
    and record_out:
      "Some ((), s2) \<in> set_dist (execute (ro_record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in> set_dist (execute receive_trace_fri_challenge s2)"
    and tail_out:
      "Some ((roots_tail, bs_tail), sent) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A (Suc i) n (bs @ [b])) s3)"
    unfolding ro_staged_trace_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  have i_bound: "i < length (trace_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_bound: "Suc i + n \<le> length (trace_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
    using Suc.prems(3) i_bound
    unfolding staged_adversary_controlled_def by blast
  have stage_fields:
    "PTraceFriCounter s1 = PTraceFriCounter builder"
    "PCompositionFriCounter s1 = PCompositionFriCounter builder"
    "PAlphaCounter s1 = PAlphaCounter builder"
    "PQueryCounter s1 = PQueryCounter builder"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp_all
  have record_counters:
    "PTraceFriCounter s2 = PTraceFriCounter s1 \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
     PAlphaCounter s2 = PAlphaCounter s1 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    by (rule ro_record_staged_message_counter_preserves[OF record_out])
  have challenge_counters:
    "PTraceFriCounter s3 = Suc (PTraceFriCounter s2) \<and>
     PCompositionFriCounter s3 = PCompositionFriCounter s2 \<and>
     PAlphaCounter s3 = PAlphaCounter s2 \<and>
     PQueryCounter s3 = PQueryCounter s2"
    by (rule receive_trace_fri_challenge_counter_outcome[OF challenge_out])
  have tail_counters:
    "PTraceFriCounter sent = PTraceFriCounter s3 + n \<and>
     PCompositionFriCounter sent = PCompositionFriCounter s3 \<and>
     PAlphaCounter sent = PAlphaCounter s3 \<and>
     PQueryCounter sent = PQueryCounter s3"
    by (rule Suc.IH[OF tail_bound tail_out Suc.prems(3)])
  show ?case
    using stage_fields record_counters challenge_counters tail_counters
    by simp
qed

lemma ro_staged_alpha_program_counters:
  assumes outcome:
    "Some (as, sent) \<in> set_dist (execute (ro_staged_alpha_program n) builder)"
  shows
    "PTraceFriCounter sent = PTraceFriCounter builder \<and>
     PCompositionFriCounter sent = PCompositionFriCounter builder \<and>
     PAlphaCounter sent = PAlphaCounter builder + n \<and>
     PQueryCounter sent = PQueryCounter builder"
  using outcome
proof (induction n arbitrary: as builder sent)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems obtain a s1 s2 as_tail where
    challenge_out:
      "Some (a, s1) \<in> set_dist (execute receive_alpha_challenge builder)"
    and record_out:
      "Some ((), s2) \<in> set_dist (execute (ro_record_staged_message a) s1)"
    and tail_out:
      "Some (as_tail, sent) \<in>
        set_dist (execute (ro_staged_alpha_program n) s2)"
    unfolding ro_staged_alpha_program.simps
    by (auto elim!: set_dist_bindE)
  have challenge_counters:
    "PTraceFriCounter s1 = PTraceFriCounter builder \<and>
     PCompositionFriCounter s1 = PCompositionFriCounter builder \<and>
     PAlphaCounter s1 = Suc (PAlphaCounter builder) \<and>
     PQueryCounter s1 = PQueryCounter builder"
    by (rule receive_alpha_challenge_counter_outcome[OF challenge_out])
  have record_counters:
    "PTraceFriCounter s2 = PTraceFriCounter s1 \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
     PAlphaCounter s2 = PAlphaCounter s1 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    by (rule ro_record_staged_message_counter_preserves[OF record_out])
  have tail_counters:
    "PTraceFriCounter sent = PTraceFriCounter s2 \<and>
     PCompositionFriCounter sent = PCompositionFriCounter s2 \<and>
     PAlphaCounter sent = PAlphaCounter s2 + n \<and>
     PQueryCounter sent = PQueryCounter s2"
    by (rule Suc.IH[OF tail_out])
  show ?case
    using challenge_counters record_counters tail_counters
    by simp
qed

lemma ro_staged_composition_fri_program_counters:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
    and outcome:
      "Some ((roots, bs'), sent) \<in>
        set_dist
          (execute (ro_staged_composition_fri_program A dg i n bs) builder)"
  shows
    "PTraceFriCounter sent = PTraceFriCounter builder \<and>
     PCompositionFriCounter sent = PCompositionFriCounter builder + n \<and>
     PAlphaCounter sent = PAlphaCounter builder \<and>
     PQueryCounter sent = PQueryCounter builder"
  using bound outcome controlled
proof (induction n arbitrary: i bs roots bs' builder sent)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems(2) obtain root s1 s2 b s3 roots_tail bs_tail where
    stage_out:
      "Some (root, s1) \<in>
        set_dist (execute (composition_fri_root_stage A dg i bs) builder)"
    and record_out:
      "Some ((), s2) \<in> set_dist (execute (ro_record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in> set_dist (execute receive_composition_fri_challenge s2)"
    and tail_out:
      "Some ((roots_tail, bs_tail), sent) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg (Suc i) n
              (bs @ [b])) s3)"
    unfolding ro_staged_composition_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  have i_bound: "i < length (composition_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_bound: "Suc i + n \<le> length (composition_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
    using Suc.prems(3) i_bound
    unfolding staged_adversary_controlled_def by blast
  have stage_fields:
    "PTraceFriCounter s1 = PTraceFriCounter builder"
    "PCompositionFriCounter s1 = PCompositionFriCounter builder"
    "PAlphaCounter s1 = PAlphaCounter builder"
    "PQueryCounter s1 = PQueryCounter builder"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp_all
  have record_counters:
    "PTraceFriCounter s2 = PTraceFriCounter s1 \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
     PAlphaCounter s2 = PAlphaCounter s1 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    by (rule ro_record_staged_message_counter_preserves[OF record_out])
  have challenge_counters:
    "PTraceFriCounter s3 = PTraceFriCounter s2 \<and>
     PCompositionFriCounter s3 = Suc (PCompositionFriCounter s2) \<and>
     PAlphaCounter s3 = PAlphaCounter s2 \<and>
     PQueryCounter s3 = PQueryCounter s2"
    by (rule receive_composition_fri_challenge_counter_outcome[OF challenge_out])
  have tail_counters:
    "PTraceFriCounter sent = PTraceFriCounter s3 \<and>
     PCompositionFriCounter sent = PCompositionFriCounter s3 + n \<and>
     PAlphaCounter sent = PAlphaCounter s3 \<and>
     PQueryCounter sent = PQueryCounter s3"
    by (rule Suc.IH[OF tail_bound tail_out Suc.prems(3)])
  show ?case
    using stage_fields record_counters challenge_counters tail_counters
    by simp
qed

lemma ro_receive_trace_fri_commits_known_outcome:
  fixes r t :: "'f protocol_channel"
    and root root' b b' absorbed :: 'f
    and rest :: "'f list"
  assumes tr: "PTranscript r = root # rest"
    and absorb_lookup:
      "fmlookup (HashMap r) (TranscriptAbsorb (PState r) root) =
        Some absorbed"
    and challenge_lookup:
      "fmlookup (HashMap r)
        (TraceFriChallenge (PTraceFriCounter r) absorbed) = Some b"
    and outcome:
      "Some ((b', root'), t) \<in>
        set_dist (execute ro_receive_trace_fri_commits r)"
  shows
    "b' = b \<and>
     root' = root \<and>
     PState t = absorbed \<and>
     PTranscript t = rest \<and>
     r \<le> t \<and>
     PTraceFriCounter t = Suc (PTraceFriCounter r) \<and>
     PCompositionFriCounter t = PCompositionFriCounter r \<and>
     PAlphaCounter t = PAlphaCounter r \<and>
     PQueryCounter t = PQueryCounter r"
proof -
  from outcome obtain r1 where
    absorb_out:
      "Some (root', r1) \<in> set_dist (execute protocol_absorb_read r)"
    and challenge_out:
      "Some (b', t) \<in> set_dist (execute receive_trace_fri_challenge r1)"
    unfolding ro_receive_trace_fri_commits_def ro_receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  have absorb_props:
    "root' = root \<and> PState r1 = absorbed \<and>
     PTranscript r1 = rest \<and> r \<le> r1"
    by (rule protocol_absorb_read_known_nonempty_outcome
        [OF tr absorb_lookup absorb_out])
  have absorb_counters:
    "PTraceFriCounter r1 = PTraceFriCounter r \<and>
     PCompositionFriCounter r1 = PCompositionFriCounter r \<and>
     PAlphaCounter r1 = PAlphaCounter r \<and>
     PQueryCounter r1 = PQueryCounter r"
    by (rule protocol_absorb_read_counter_preserves[OF absorb_out])
  have challenge_lookup_r1:
    "fmlookup (HashMap r1)
      (TraceFriChallenge (PTraceFriCounter r1) (PState r1)) = Some b"
  proof -
    have lookup_ext:
      "fmlookup (HashMap r1)
        (TraceFriChallenge (PTraceFriCounter r) absorbed) = Some b"
      by (rule hash_extension_lookup[OF challenge_lookup])
        (use absorb_props in simp)
    then show ?thesis
      using absorb_props absorb_counters by simp
  qed
  have challenge_known:
    "b' = b \<and> PState t = PState r1 \<and>
     PTranscript t = PTranscript r1 \<and> r1 \<le> t"
    by (rule receive_trace_fri_challenge_known_outcome
        [OF challenge_lookup_r1 challenge_out])
  have challenge_counters:
    "PTraceFriCounter t = Suc (PTraceFriCounter r1) \<and>
     PCompositionFriCounter t = PCompositionFriCounter r1 \<and>
     PAlphaCounter t = PAlphaCounter r1 \<and>
     PQueryCounter t = PQueryCounter r1"
    by (rule receive_trace_fri_challenge_counter_outcome[OF challenge_out])
  have ext_r_r1: "r \<le> r1"
    using absorb_props by simp
  have ext_r1_t: "r1 \<le> t"
    using challenge_known by simp
  have ext: "r \<le> t"
    by (rule hash_ext_trans[OF ext_r_r1 ext_r1_t])
  show ?thesis
    using absorb_props absorb_counters challenge_known challenge_counters ext
    by simp
qed

lemma ro_staged_trace_fri_program_ro_receive_trace_fri_commits_sync:
  fixes builder sent verifier verifier' :: "'f protocol_channel"
    and rest :: "'f list"
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
    and builder_out:
      "Some ((roots, bs'), sent) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A i n bs) builder)"
    and sent_ext: "sent \<le> verifier"
    and state_eq: "PState verifier = PState builder"
    and trace_counter_eq:
      "PTraceFriCounter verifier = PTraceFriCounter builder"
    and composition_counter_eq:
      "PCompositionFriCounter verifier = PCompositionFriCounter builder"
    and alpha_counter_eq:
      "PAlphaCounter verifier = PAlphaCounter builder"
    and query_counter_eq:
      "PQueryCounter verifier = PQueryCounter builder"
    and transcript_prefix: "PTranscript verifier = roots @ rest"
    and verifier_out:
      "Some (pairs, verifier') \<in>
        set_dist (execute (ntimes ro_receive_trace_fri_commits n) verifier)"
  shows
    "\<exists>challenges.
      bs' = bs @ challenges \<and>
      pairs = zip challenges roots \<and>
      PState verifier' = PState sent \<and>
      PTranscript verifier' = rest \<and>
      verifier \<le> verifier' \<and>
      PTraceFriCounter verifier' = PTraceFriCounter builder + n \<and>
      PCompositionFriCounter verifier' = PCompositionFriCounter builder \<and>
      PAlphaCounter verifier' = PAlphaCounter builder \<and>
      PQueryCounter verifier' = PQueryCounter builder"
  using bound builder_out sent_ext state_eq trace_counter_eq
    composition_counter_eq alpha_counter_eq query_counter_eq transcript_prefix
    verifier_out controlled
proof (induction n arbitrary: i bs roots bs' builder sent verifier verifier'
    pairs rest)
  case 0
  then show ?case
    by (auto intro: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(2) obtain root s1 s2 b s3 roots_tail bs_tail where
    stage_out:
      "Some (root, s1) \<in>
        set_dist (execute (trace_fri_root_stage A i bs) builder)"
    and record_out:
      "Some ((), s2) \<in> set_dist (execute (ro_record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in> set_dist (execute receive_trace_fri_challenge s2)"
    and tail_out:
      "Some ((roots_tail, bs_tail), sent) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A (Suc i) n (bs @ [b])) s3)"
    and roots_eq: "roots = root # roots_tail"
    and bs'_eq: "bs' = bs_tail"
    unfolding ro_staged_trace_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  from Suc.prems(10) obtain b' root' verifier_mid pairs_tail where
    verifier_head:
      "Some ((b', root'), verifier_mid) \<in>
        set_dist (execute ro_receive_trace_fri_commits verifier)"
    and verifier_tail:
      "Some (pairs_tail, verifier') \<in>
        set_dist (execute (ntimes ro_receive_trace_fri_commits n) verifier_mid)"
    and pairs_eq: "pairs = (b', root') # pairs_tail"
    by (auto elim!: set_dist_bindE split: prod.splits)
  have i_bound: "i < length (trace_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_bound: "Suc i + n \<le> length (trace_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
    using Suc.prems(11) i_bound
    unfolding staged_adversary_controlled_def by blast
  have stage_ext: "builder \<le> s1"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have stage_fields:
    "PState s1 = PState builder"
    "PTraceFriCounter s1 = PTraceFriCounter builder"
    "PCompositionFriCounter s1 = PCompositionFriCounter builder"
    "PAlphaCounter s1 = PAlphaCounter builder"
    "PQueryCounter s1 = PQueryCounter builder"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp_all
  have record_lookup_ext:
    "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) root) =
      Some (PState s2) \<and> s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF record_out])
  have record_counters:
    "PTraceFriCounter s2 = PTraceFriCounter s1 \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
     PAlphaCounter s2 = PAlphaCounter s1 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    by (rule ro_record_staged_message_counter_preserves[OF record_out])
  have challenge_props:
    "s2 \<le> s3 \<and> PState s3 = PState s2 \<and>
     PTranscript s3 = PTranscript s2 \<and>
     fmlookup (HashMap s3)
       (TraceFriChallenge (PTraceFriCounter s2) (PState s2)) = Some b"
    using receive_trace_fri_challenge_outcome[OF challenge_out] by simp
  have challenge_counters:
    "PTraceFriCounter s3 = Suc (PTraceFriCounter s2) \<and>
     PCompositionFriCounter s3 = PCompositionFriCounter s2 \<and>
     PAlphaCounter s3 = PAlphaCounter s2 \<and>
     PQueryCounter s3 = PQueryCounter s2"
    by (rule receive_trace_fri_challenge_counter_outcome[OF challenge_out])
  have tail_builder_props:
    "ro_absorb_lookup_chain sent (PState s3) roots_tail (PState sent) \<and>
      s3 \<le> sent"
    by (rule ro_staged_trace_fri_program_absorb_lookup_chain
        [OF Suc.prems(11) tail_bound tail_out])
  have ext_s2_sent: "s2 \<le> sent"
    by (rule hash_ext_trans[OF conjunct1[OF challenge_props]
          conjunct2[OF tail_builder_props]])
  have absorb_lookup_sent:
    "fmlookup (HashMap sent) (TranscriptAbsorb (PState s1) root) =
      Some (PState s2)"
    by (rule hash_extension_lookup[OF conjunct1[OF record_lookup_ext]
          ext_s2_sent])
  have absorb_lookup_verifier:
    "fmlookup (HashMap verifier) (TranscriptAbsorb (PState verifier) root) =
      Some (PState s2)"
    using hash_extension_lookup[OF absorb_lookup_sent Suc.prems(3)]
      stage_fields Suc.prems(4)
    by simp
  have challenge_lookup_sent:
    "fmlookup (HashMap sent)
       (TraceFriChallenge (PTraceFriCounter s2) (PState s2)) = Some b"
    by (rule hash_extension_lookup
        [OF conjunct2[OF conjunct2[OF conjunct2[OF challenge_props]]]
          conjunct2[OF tail_builder_props]])
  have challenge_lookup_verifier_old:
    "fmlookup (HashMap verifier)
       (TraceFriChallenge (PTraceFriCounter s2) (PState s2)) = Some b"
    by (rule hash_extension_lookup[OF challenge_lookup_sent Suc.prems(3)])
  have challenge_lookup_verifier:
    "fmlookup (HashMap verifier)
       (TraceFriChallenge (PTraceFriCounter verifier) (PState s2)) = Some b"
    using challenge_lookup_verifier_old record_counters stage_fields
      Suc.prems(5)
    by simp
  have tr_verifier: "PTranscript verifier = root # (roots_tail @ rest)"
    using Suc.prems(9) roots_eq by simp
  have head_sync:
    "b' = b \<and>
     root' = root \<and>
     PState verifier_mid = PState s2 \<and>
     PTranscript verifier_mid = roots_tail @ rest \<and>
     verifier \<le> verifier_mid \<and>
     PTraceFriCounter verifier_mid = Suc (PTraceFriCounter verifier) \<and>
     PCompositionFriCounter verifier_mid = PCompositionFriCounter verifier \<and>
     PAlphaCounter verifier_mid = PAlphaCounter verifier \<and>
     PQueryCounter verifier_mid = PQueryCounter verifier"
    by (rule ro_receive_trace_fri_commits_known_outcome
        [OF tr_verifier absorb_lookup_verifier challenge_lookup_verifier
          verifier_head])
  have sent_ext_tail: "sent \<le> verifier_mid"
    by (rule hash_ext_trans[OF Suc.prems(3)]) (use head_sync in simp)
  have state_tail: "PState verifier_mid = PState s3"
    using head_sync challenge_props by simp
  have trace_counter_tail:
    "PTraceFriCounter verifier_mid = PTraceFriCounter s3"
    using head_sync challenge_counters record_counters stage_fields Suc.prems(5)
    by simp
  have composition_counter_tail:
    "PCompositionFriCounter verifier_mid = PCompositionFriCounter s3"
    using head_sync challenge_counters record_counters stage_fields Suc.prems(6)
    by simp
  have alpha_counter_tail:
    "PAlphaCounter verifier_mid = PAlphaCounter s3"
    using head_sync challenge_counters record_counters stage_fields Suc.prems(7)
    by simp
  have query_counter_tail:
    "PQueryCounter verifier_mid = PQueryCounter s3"
    using head_sync challenge_counters record_counters stage_fields Suc.prems(8)
    by simp
  have tail_sync:
    "\<exists>challenges_tail.
      bs_tail = (bs @ [b]) @ challenges_tail \<and>
      pairs_tail = zip challenges_tail roots_tail \<and>
      PState verifier' = PState sent \<and>
      PTranscript verifier' = rest \<and>
      verifier_mid \<le> verifier' \<and>
      PTraceFriCounter verifier' = PTraceFriCounter s3 + n \<and>
      PCompositionFriCounter verifier' = PCompositionFriCounter s3 \<and>
      PAlphaCounter verifier' = PAlphaCounter s3 \<and>
      PQueryCounter verifier' = PQueryCounter s3"
    by (rule Suc.IH[OF tail_bound tail_out sent_ext_tail state_tail
          trace_counter_tail composition_counter_tail alpha_counter_tail
          query_counter_tail _ verifier_tail Suc.prems(11)])
      (use head_sync in simp)
  from tail_sync obtain challenges_tail where
    bs_tail_eq: "bs_tail = (bs @ [b]) @ challenges_tail"
    and pairs_tail_eq: "pairs_tail = zip challenges_tail roots_tail"
    and final_state: "PState verifier' = PState sent"
    and final_tr: "PTranscript verifier' = rest"
    and tail_ext: "verifier_mid \<le> verifier'"
    and final_trace_counter:
      "PTraceFriCounter verifier' = PTraceFriCounter s3 + n"
    and final_composition_counter:
      "PCompositionFriCounter verifier' = PCompositionFriCounter s3"
    and final_alpha_counter: "PAlphaCounter verifier' = PAlphaCounter s3"
    and final_query_counter: "PQueryCounter verifier' = PQueryCounter s3"
    by blast
  have verifier_ext: "verifier \<le> verifier'"
    by (rule hash_ext_trans[OF _ tail_ext]) (use head_sync in simp)
  have final_trace_counter_builder:
    "PTraceFriCounter verifier' = PTraceFriCounter builder + Suc n"
    using final_trace_counter challenge_counters record_counters stage_fields
    by simp
  have final_other_counters:
    "PCompositionFriCounter verifier' = PCompositionFriCounter builder \<and>
     PAlphaCounter verifier' = PAlphaCounter builder \<and>
     PQueryCounter verifier' = PQueryCounter builder"
    using final_composition_counter final_alpha_counter final_query_counter
      challenge_counters record_counters stage_fields
    by simp
  show ?case
  proof (intro exI conjI)
    show "bs' = bs @ (b # challenges_tail)"
      using bs'_eq bs_tail_eq by simp
    show "pairs = zip (b # challenges_tail) roots"
      using pairs_eq pairs_tail_eq roots_eq head_sync by simp
    show "PState verifier' = PState sent"
      by (rule final_state)
    show "PTranscript verifier' = rest"
      by (rule final_tr)
    show "verifier \<le> verifier'"
      by (rule verifier_ext)
    show "PTraceFriCounter verifier' = PTraceFriCounter builder + Suc n"
      by (rule final_trace_counter_builder)
    show "PCompositionFriCounter verifier' = PCompositionFriCounter builder"
      using final_other_counters by simp
    show "PAlphaCounter verifier' = PAlphaCounter builder"
      using final_other_counters by simp
    show "PQueryCounter verifier' = PQueryCounter builder"
      using final_other_counters by simp
  qed
qed

lemma ro_receive_composition_fri_commits_known_outcome:  fixes r t :: "'f protocol_channel"
    and root root' b b' absorbed :: 'f
    and rest :: "'f list"
  assumes tr: "PTranscript r = root # rest"
    and absorb_lookup:
      "fmlookup (HashMap r) (TranscriptAbsorb (PState r) root) =
        Some absorbed"
    and challenge_lookup:
      "fmlookup (HashMap r)
        (CompositionFriChallenge (PCompositionFriCounter r) absorbed) = Some b"
    and outcome:
      "Some ((b', root'), t) \<in>
        set_dist (execute ro_receive_composition_fri_commits r)"
  shows
    "b' = b \<and>
     root' = root \<and>
     PState t = absorbed \<and>
     PTranscript t = rest \<and>
     r \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter r \<and>
     PCompositionFriCounter t = Suc (PCompositionFriCounter r) \<and>
     PAlphaCounter t = PAlphaCounter r \<and>
     PQueryCounter t = PQueryCounter r"
proof -
  from outcome obtain r1 where
    absorb_out:
      "Some (root', r1) \<in> set_dist (execute protocol_absorb_read r)"
    and challenge_out:
      "Some (b', t) \<in>
        set_dist (execute receive_composition_fri_challenge r1)"
    unfolding ro_receive_composition_fri_commits_def
      ro_receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  have absorb_props:
    "root' = root \<and> PState r1 = absorbed \<and>
     PTranscript r1 = rest \<and> r \<le> r1"
    by (rule protocol_absorb_read_known_nonempty_outcome
        [OF tr absorb_lookup absorb_out])
  have absorb_counters:
    "PTraceFriCounter r1 = PTraceFriCounter r \<and>
     PCompositionFriCounter r1 = PCompositionFriCounter r \<and>
     PAlphaCounter r1 = PAlphaCounter r \<and>
     PQueryCounter r1 = PQueryCounter r"
    by (rule protocol_absorb_read_counter_preserves[OF absorb_out])
  have challenge_lookup_r1:
    "fmlookup (HashMap r1)
      (CompositionFriChallenge (PCompositionFriCounter r1) (PState r1)) =
        Some b"
  proof -
    have lookup_ext:
      "fmlookup (HashMap r1)
        (CompositionFriChallenge (PCompositionFriCounter r) absorbed) =
          Some b"
      by (rule hash_extension_lookup[OF challenge_lookup])
        (use absorb_props in simp)
    then show ?thesis
      using absorb_props absorb_counters by simp
  qed
  have challenge_known:
    "b' = b \<and> PState t = PState r1 \<and>
     PTranscript t = PTranscript r1 \<and> r1 \<le> t"
    by (rule receive_composition_fri_challenge_known_outcome
        [OF challenge_lookup_r1 challenge_out])
  have challenge_counters:
    "PTraceFriCounter t = PTraceFriCounter r1 \<and>
     PCompositionFriCounter t = Suc (PCompositionFriCounter r1) \<and>
     PAlphaCounter t = PAlphaCounter r1 \<and>
     PQueryCounter t = PQueryCounter r1"
    by (rule receive_composition_fri_challenge_counter_outcome[OF challenge_out])
  have ext_r_r1: "r \<le> r1"
    using absorb_props by simp
  have ext_r1_t: "r1 \<le> t"
    using challenge_known by simp
  have ext: "r \<le> t"
    by (rule hash_ext_trans[OF ext_r_r1 ext_r1_t])
  show ?thesis
    using absorb_props absorb_counters challenge_known challenge_counters ext
    by simp
qed
lemma ro_alpha_round_known_outcome:
  fixes r t :: "'f protocol_channel"
    and rest :: "'f list"
    and a a' absorbed :: 'f
  assumes tr: "PTranscript r = a # rest"
    and challenge_lookup:
      "fmlookup (HashMap r)
        (AlphaChallenge (PAlphaCounter r) (PState r)) = Some a"
    and absorb_lookup:
      "fmlookup (HashMap r) (TranscriptAbsorb (PState r) a) =
        Some absorbed"
    and outcome:
      "Some (a', t) \<in> set_dist (execute ro_alpha_round r)"
  shows
    "a' = a \<and>
     PState t = absorbed \<and>
     PTranscript t = rest \<and>
     r \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter r \<and>
     PCompositionFriCounter t = PCompositionFriCounter r \<and>
     PAlphaCounter t = Suc (PAlphaCounter r) \<and>
     PQueryCounter t = PQueryCounter r"
proof -
  from outcome obtain a0 r1 a1 r2 where
    challenge_out:
      "Some (a0, r1) \<in> set_dist (execute receive_alpha_challenge r)"
    and absorb_out:
      "Some (a1, r2) \<in> set_dist (execute protocol_absorb_read r1)"
    and assert_out:
      "Some ((), t) \<in> set_dist (execute (assert (a0 = a1)) r2)"
    and a'_eq: "a' = a1"
    unfolding ro_alpha_round_def
    by (auto elim!: set_dist_bindE)
  have challenge_known:
    "a0 = a \<and> PState r1 = PState r \<and>
     PTranscript r1 = PTranscript r \<and> r \<le> r1"
    by (rule receive_alpha_challenge_known_outcome
        [OF challenge_lookup challenge_out])
  have challenge_counters:
    "PTraceFriCounter r1 = PTraceFriCounter r \<and>
     PCompositionFriCounter r1 = PCompositionFriCounter r \<and>
     PAlphaCounter r1 = Suc (PAlphaCounter r) \<and>
     PQueryCounter r1 = PQueryCounter r"
    by (rule receive_alpha_challenge_counter_outcome[OF challenge_out])
  have absorb_lookup_r1:
    "fmlookup (HashMap r1) (TranscriptAbsorb (PState r1) a) =
      Some absorbed"
  proof -
    have lookup_ext:
      "fmlookup (HashMap r1) (TranscriptAbsorb (PState r) a) =
        Some absorbed"
      by (rule hash_extension_lookup[OF absorb_lookup])
        (use challenge_known in simp)
    then show ?thesis
      using challenge_known by simp
  qed
  have absorb_props:
    "a1 = a \<and> PState r2 = absorbed \<and>
     PTranscript r2 = rest \<and> r1 \<le> r2"
    by (rule protocol_absorb_read_known_nonempty_outcome
        [OF _ absorb_lookup_r1 absorb_out])
      (use tr challenge_known in simp)
  have absorb_counters:
    "PTraceFriCounter r2 = PTraceFriCounter r1 \<and>
     PCompositionFriCounter r2 = PCompositionFriCounter r1 \<and>
     PAlphaCounter r2 = PAlphaCounter r1 \<and>
     PQueryCounter r2 = PQueryCounter r1"
    by (rule protocol_absorb_read_counter_preserves[OF absorb_out])
  have t_eq: "t = r2"
    using assert_out challenge_known absorb_props
    unfolding assert_def by simp
  have ext_r_r1: "r \<le> r1"
    using challenge_known by simp
  have ext_r1_r2: "r1 \<le> r2"
    using absorb_props by simp
  have ext_r_r2: "r \<le> r2"
    by (rule hash_ext_trans[OF ext_r_r1 ext_r1_r2])
  show ?thesis
    using a'_eq challenge_counters absorb_counters absorb_props t_eq ext_r_r2
    by simp
qed

lemma ro_staged_alpha_program_ro_alpha_round_sync:
  fixes builder sent verifier verifier' :: "'f protocol_channel"
    and rest :: "'f list"
  assumes builder_out:
      "Some (as, sent) \<in> set_dist (execute (ro_staged_alpha_program n) builder)"
    and sent_ext: "sent \<le> verifier"
    and state_eq: "PState verifier = PState builder"
    and trace_counter_eq:
      "PTraceFriCounter verifier = PTraceFriCounter builder"
    and composition_counter_eq:
      "PCompositionFriCounter verifier = PCompositionFriCounter builder"
    and alpha_counter_eq:
      "PAlphaCounter verifier = PAlphaCounter builder"
    and query_counter_eq:
      "PQueryCounter verifier = PQueryCounter builder"
    and transcript_prefix: "PTranscript verifier = as @ rest"
    and verifier_out:
      "Some (as', verifier') \<in>
        set_dist (execute (mmap (replicate n ro_alpha_round)) verifier)"
  shows
    "as' = as \<and>
     PState verifier' = PState sent \<and>
     PTranscript verifier' = rest \<and>
     verifier \<le> verifier' \<and>
     PTraceFriCounter verifier' = PTraceFriCounter builder \<and>
     PCompositionFriCounter verifier' = PCompositionFriCounter builder \<and>
     PAlphaCounter verifier' = PAlphaCounter builder + n \<and>
     PQueryCounter verifier' = PQueryCounter builder"
  using builder_out sent_ext state_eq trace_counter_eq composition_counter_eq
    alpha_counter_eq query_counter_eq transcript_prefix verifier_out
proof (induction n arbitrary: as builder sent verifier verifier' as' rest)
  case 0
  then show ?case
    by (auto intro: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(1) obtain a s1 s2 as_tail where
    challenge_out:
      "Some (a, s1) \<in> set_dist (execute receive_alpha_challenge builder)"
    and record_out:
      "Some ((), s2) \<in> set_dist (execute (ro_record_staged_message a) s1)"
    and tail_out:
      "Some (as_tail, sent) \<in>
        set_dist (execute (ro_staged_alpha_program n) s2)"
    and as_eq: "as = a # as_tail"
    unfolding ro_staged_alpha_program.simps
    by (auto elim!: set_dist_bindE)
  from Suc.prems(9) obtain a' verifier_mid as_tail' where
    verifier_head:
      "Some (a', verifier_mid) \<in> set_dist (execute ro_alpha_round verifier)"
    and verifier_tail:
      "Some (as_tail', verifier') \<in>
        set_dist (execute (mmap (replicate n ro_alpha_round)) verifier_mid)"
    and as'_eq: "as' = a' # as_tail'"
    by (auto elim!: set_dist_bindE)
  have challenge_props:
    "builder \<le> s1 \<and> PState s1 = PState builder \<and>
     PTranscript s1 = PTranscript builder \<and>
     fmlookup (HashMap s1)
       (AlphaChallenge (PAlphaCounter builder) (PState builder)) = Some a"
    using receive_alpha_challenge_outcome[OF challenge_out] by simp
  have challenge_counters:
    "PTraceFriCounter s1 = PTraceFriCounter builder \<and>
     PCompositionFriCounter s1 = PCompositionFriCounter builder \<and>
     PAlphaCounter s1 = Suc (PAlphaCounter builder) \<and>
     PQueryCounter s1 = PQueryCounter builder"
    by (rule receive_alpha_challenge_counter_outcome[OF challenge_out])
  have record_lookup_ext:
    "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) a) =
      Some (PState s2) \<and> s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF record_out])
  have record_counters:
    "PTraceFriCounter s2 = PTraceFriCounter s1 \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
     PAlphaCounter s2 = PAlphaCounter s1 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    by (rule ro_record_staged_message_counter_preserves[OF record_out])
  have tail_builder_props:
    "ro_absorb_lookup_chain sent (PState s2) as_tail (PState sent) \<and>
      s2 \<le> sent"
    by (rule ro_staged_alpha_program_absorb_lookup_chain[OF tail_out])
  have challenge_lookup_sent:
    "fmlookup (HashMap sent)
       (AlphaChallenge (PAlphaCounter builder) (PState builder)) = Some a"
    by (rule hash_extension_lookup
        [OF conjunct2[OF conjunct2[OF conjunct2[OF challenge_props]]]])
      (rule hash_ext_trans[OF conjunct2[OF record_lookup_ext]
          conjunct2[OF tail_builder_props]])
  have challenge_lookup_verifier:
    "fmlookup (HashMap verifier)
       (AlphaChallenge (PAlphaCounter verifier) (PState verifier)) = Some a"
    using hash_extension_lookup[OF challenge_lookup_sent Suc.prems(2)]
      Suc.prems(3) Suc.prems(6)
    by simp
  have absorb_lookup_sent:
    "fmlookup (HashMap sent) (TranscriptAbsorb (PState s1) a) =
      Some (PState s2)"
    by (rule hash_extension_lookup[OF conjunct1[OF record_lookup_ext]
          conjunct2[OF tail_builder_props]])
  have absorb_lookup_verifier:
    "fmlookup (HashMap verifier) (TranscriptAbsorb (PState verifier) a) =
      Some (PState s2)"
    using hash_extension_lookup[OF absorb_lookup_sent Suc.prems(2)]
      Suc.prems(3) challenge_props
    by simp
  have tr_verifier: "PTranscript verifier = a # (as_tail @ rest)"
    using Suc.prems(8) as_eq by simp
  have head_sync:
    "a' = a \<and>
     PState verifier_mid = PState s2 \<and>
     PTranscript verifier_mid = as_tail @ rest \<and>
     verifier \<le> verifier_mid \<and>
     PTraceFriCounter verifier_mid = PTraceFriCounter verifier \<and>
     PCompositionFriCounter verifier_mid = PCompositionFriCounter verifier \<and>
     PAlphaCounter verifier_mid = Suc (PAlphaCounter verifier) \<and>
     PQueryCounter verifier_mid = PQueryCounter verifier"
    by (rule ro_alpha_round_known_outcome
        [OF tr_verifier challenge_lookup_verifier absorb_lookup_verifier
          verifier_head])
  have sent_ext_tail: "sent \<le> verifier_mid"
    by (rule hash_ext_trans[OF Suc.prems(2)]) (use head_sync in simp)
  have state_tail: "PState verifier_mid = PState s2"
    using head_sync by simp
  have trace_counter_tail:
    "PTraceFriCounter verifier_mid = PTraceFriCounter s2"
    using head_sync challenge_counters record_counters Suc.prems(4) by simp
  have composition_counter_tail:
    "PCompositionFriCounter verifier_mid = PCompositionFriCounter s2"
    using head_sync challenge_counters record_counters Suc.prems(5) by simp
  have alpha_counter_tail:
    "PAlphaCounter verifier_mid = PAlphaCounter s2"
    using head_sync challenge_counters record_counters Suc.prems(6) by simp
  have query_counter_tail:
    "PQueryCounter verifier_mid = PQueryCounter s2"
    using head_sync challenge_counters record_counters Suc.prems(7) by simp
  have tail_sync:
    "as_tail' = as_tail \<and>
     PState verifier' = PState sent \<and>
     PTranscript verifier' = rest \<and>
     verifier_mid \<le> verifier' \<and>
     PTraceFriCounter verifier' = PTraceFriCounter s2 \<and>
     PCompositionFriCounter verifier' = PCompositionFriCounter s2 \<and>
     PAlphaCounter verifier' = PAlphaCounter s2 + n \<and>
     PQueryCounter verifier' = PQueryCounter s2"
    by (rule Suc.IH[OF tail_out sent_ext_tail state_tail
          trace_counter_tail composition_counter_tail alpha_counter_tail
          query_counter_tail _ verifier_tail])
      (use head_sync in simp)
  have tail_ext: "verifier_mid \<le> verifier'"
    using tail_sync by simp
  have head_ext: "verifier \<le> verifier_mid"
    using head_sync by simp
  have verifier_ext: "verifier \<le> verifier'"
    by (rule hash_ext_trans[OF head_ext tail_ext])
  show ?case
    using as'_eq as_eq head_sync tail_sync verifier_ext challenge_counters
      record_counters
    by simp
qed

lemma ro_staged_composition_fri_program_ro_receive_composition_fri_commits_sync:
  fixes builder sent verifier verifier' :: "'f protocol_channel"
    and rest :: "'f list"
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
    and builder_out:
      "Some ((roots, bs'), sent) \<in>
        set_dist
          (execute (ro_staged_composition_fri_program A dg i n bs) builder)"
    and sent_ext: "sent \<le> verifier"
    and state_eq: "PState verifier = PState builder"
    and trace_counter_eq:
      "PTraceFriCounter verifier = PTraceFriCounter builder"
    and composition_counter_eq:
      "PCompositionFriCounter verifier = PCompositionFriCounter builder"
    and alpha_counter_eq:
      "PAlphaCounter verifier = PAlphaCounter builder"
    and query_counter_eq:
      "PQueryCounter verifier = PQueryCounter builder"
    and transcript_prefix: "PTranscript verifier = roots @ rest"
    and verifier_out:
      "Some (pairs, verifier') \<in>
        set_dist (execute (ntimes ro_receive_composition_fri_commits n) verifier)"
  shows
    "\<exists>challenges.
      bs' = bs @ challenges \<and>
      pairs = zip challenges roots \<and>
      PState verifier' = PState sent \<and>
      PTranscript verifier' = rest \<and>
      verifier \<le> verifier' \<and>
      PTraceFriCounter verifier' = PTraceFriCounter builder \<and>
      PCompositionFriCounter verifier' = PCompositionFriCounter builder + n \<and>
      PAlphaCounter verifier' = PAlphaCounter builder \<and>
      PQueryCounter verifier' = PQueryCounter builder"
  using bound builder_out sent_ext state_eq trace_counter_eq
    composition_counter_eq alpha_counter_eq query_counter_eq transcript_prefix
    verifier_out controlled
proof (induction n arbitrary: i bs roots bs' builder sent verifier verifier'
    pairs rest)
  case 0
  then show ?case
    by (auto intro: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(2) obtain root s1 s2 b s3 roots_tail bs_tail where
    stage_out:
      "Some (root, s1) \<in>
        set_dist (execute (composition_fri_root_stage A dg i bs) builder)"
    and record_out:
      "Some ((), s2) \<in> set_dist (execute (ro_record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in>
        set_dist (execute receive_composition_fri_challenge s2)"
    and tail_out:
      "Some ((roots_tail, bs_tail), sent) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg (Suc i) n
              (bs @ [b])) s3)"
    and roots_eq: "roots = root # roots_tail"
    and bs'_eq: "bs' = bs_tail"
    unfolding ro_staged_composition_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  from Suc.prems(10) obtain b' root' verifier_mid pairs_tail where
    verifier_head:
      "Some ((b', root'), verifier_mid) \<in>
        set_dist (execute ro_receive_composition_fri_commits verifier)"
    and verifier_tail:
      "Some (pairs_tail, verifier') \<in>
        set_dist
          (execute (ntimes ro_receive_composition_fri_commits n)
            verifier_mid)"
    and pairs_eq: "pairs = (b', root') # pairs_tail"
    by (auto elim!: set_dist_bindE split: prod.splits)
  have i_bound: "i < length (composition_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_bound: "Suc i + n \<le> length (composition_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
    using Suc.prems(11) i_bound
    unfolding staged_adversary_controlled_def by blast
  have stage_ext: "builder \<le> s1"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have stage_fields:
    "PState s1 = PState builder"
    "PTraceFriCounter s1 = PTraceFriCounter builder"
    "PCompositionFriCounter s1 = PCompositionFriCounter builder"
    "PAlphaCounter s1 = PAlphaCounter builder"
    "PQueryCounter s1 = PQueryCounter builder"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp_all
  have record_lookup_ext:
    "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) root) =
      Some (PState s2) \<and> s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF record_out])
  have record_counters:
    "PTraceFriCounter s2 = PTraceFriCounter s1 \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
     PAlphaCounter s2 = PAlphaCounter s1 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    by (rule ro_record_staged_message_counter_preserves[OF record_out])
  have challenge_props:
    "s2 \<le> s3 \<and> PState s3 = PState s2 \<and>
     PTranscript s3 = PTranscript s2 \<and>
     fmlookup (HashMap s3)
       (CompositionFriChallenge (PCompositionFriCounter s2) (PState s2)) =
       Some b"
    using receive_composition_fri_challenge_outcome[OF challenge_out]
    by simp
  have challenge_counters:
    "PTraceFriCounter s3 = PTraceFriCounter s2 \<and>
     PCompositionFriCounter s3 = Suc (PCompositionFriCounter s2) \<and>
     PAlphaCounter s3 = PAlphaCounter s2 \<and>
     PQueryCounter s3 = PQueryCounter s2"
    by (rule receive_composition_fri_challenge_counter_outcome
        [OF challenge_out])
  have tail_builder_props:
    "ro_absorb_lookup_chain sent (PState s3) roots_tail (PState sent) \<and>
      s3 \<le> sent"
    by (rule ro_staged_composition_fri_program_absorb_lookup_chain
        [OF Suc.prems(11) tail_bound tail_out])
  have ext_s2_sent: "s2 \<le> sent"
    by (rule hash_ext_trans[OF conjunct1[OF challenge_props]
          conjunct2[OF tail_builder_props]])
  have absorb_lookup_sent:
    "fmlookup (HashMap sent) (TranscriptAbsorb (PState s1) root) =
      Some (PState s2)"
    by (rule hash_extension_lookup[OF conjunct1[OF record_lookup_ext]
          ext_s2_sent])
  have absorb_lookup_verifier:
    "fmlookup (HashMap verifier) (TranscriptAbsorb (PState verifier) root) =
      Some (PState s2)"
    using hash_extension_lookup[OF absorb_lookup_sent Suc.prems(3)]
      stage_fields Suc.prems(4)
    by simp
  have challenge_lookup_sent:
    "fmlookup (HashMap sent)
       (CompositionFriChallenge (PCompositionFriCounter s2) (PState s2)) =
       Some b"
    by (rule hash_extension_lookup
        [OF conjunct2[OF conjunct2[OF conjunct2[OF challenge_props]]]
          conjunct2[OF tail_builder_props]])
  have challenge_lookup_verifier_old:
    "fmlookup (HashMap verifier)
       (CompositionFriChallenge (PCompositionFriCounter s2) (PState s2)) =
       Some b"
    by (rule hash_extension_lookup[OF challenge_lookup_sent Suc.prems(3)])
  have challenge_lookup_verifier:
    "fmlookup (HashMap verifier)
       (CompositionFriChallenge (PCompositionFriCounter verifier) (PState s2)) =
       Some b"
    using challenge_lookup_verifier_old record_counters stage_fields
      Suc.prems(6)
    by simp
  have tr_verifier: "PTranscript verifier = root # (roots_tail @ rest)"
    using Suc.prems(9) roots_eq by simp
  have head_sync:
    "b' = b \<and>
     root' = root \<and>
     PState verifier_mid = PState s2 \<and>
     PTranscript verifier_mid = roots_tail @ rest \<and>
     verifier \<le> verifier_mid \<and>
     PTraceFriCounter verifier_mid = PTraceFriCounter verifier \<and>
     PCompositionFriCounter verifier_mid = Suc (PCompositionFriCounter verifier) \<and>
     PAlphaCounter verifier_mid = PAlphaCounter verifier \<and>
     PQueryCounter verifier_mid = PQueryCounter verifier"
    by (rule ro_receive_composition_fri_commits_known_outcome
        [OF tr_verifier absorb_lookup_verifier challenge_lookup_verifier
          verifier_head])
  have sent_ext_tail: "sent \<le> verifier_mid"
    by (rule hash_ext_trans[OF Suc.prems(3)]) (use head_sync in simp)
  have state_tail: "PState verifier_mid = PState s3"
    using head_sync challenge_props by simp
  have trace_counter_tail:
    "PTraceFriCounter verifier_mid = PTraceFriCounter s3"
    using head_sync challenge_counters record_counters stage_fields Suc.prems(5)
    by simp
  have composition_counter_tail:
    "PCompositionFriCounter verifier_mid = PCompositionFriCounter s3"
    using head_sync challenge_counters record_counters stage_fields Suc.prems(6)
    by simp
  have alpha_counter_tail:
    "PAlphaCounter verifier_mid = PAlphaCounter s3"
    using head_sync challenge_counters record_counters stage_fields Suc.prems(7)
    by simp
  have query_counter_tail:
    "PQueryCounter verifier_mid = PQueryCounter s3"
    using head_sync challenge_counters record_counters stage_fields Suc.prems(8)
    by simp
  have tail_sync:
    "\<exists>challenges_tail.
      bs_tail = (bs @ [b]) @ challenges_tail \<and>
      pairs_tail = zip challenges_tail roots_tail \<and>
      PState verifier' = PState sent \<and>
      PTranscript verifier' = rest \<and>
      verifier_mid \<le> verifier' \<and>
      PTraceFriCounter verifier' = PTraceFriCounter s3 \<and>
      PCompositionFriCounter verifier' = PCompositionFriCounter s3 + n \<and>
      PAlphaCounter verifier' = PAlphaCounter s3 \<and>
      PQueryCounter verifier' = PQueryCounter s3"
    by (rule Suc.IH[OF tail_bound tail_out sent_ext_tail state_tail
          trace_counter_tail composition_counter_tail alpha_counter_tail
          query_counter_tail _ verifier_tail Suc.prems(11)])
      (use head_sync in simp)
  from tail_sync obtain challenges_tail where
    bs_tail_eq: "bs_tail = (bs @ [b]) @ challenges_tail"
    and pairs_tail_eq: "pairs_tail = zip challenges_tail roots_tail"
    and final_state: "PState verifier' = PState sent"
    and final_tr: "PTranscript verifier' = rest"
    and tail_ext: "verifier_mid \<le> verifier'"
    and final_trace_counter:
      "PTraceFriCounter verifier' = PTraceFriCounter s3"
    and final_composition_counter:
      "PCompositionFriCounter verifier' = PCompositionFriCounter s3 + n"
    and final_alpha_counter: "PAlphaCounter verifier' = PAlphaCounter s3"
    and final_query_counter: "PQueryCounter verifier' = PQueryCounter s3"
    by blast
  have verifier_ext: "verifier \<le> verifier'"
    by (rule hash_ext_trans[OF _ tail_ext]) (use head_sync in simp)
  have final_composition_counter_builder:
    "PCompositionFriCounter verifier' =
      PCompositionFriCounter builder + Suc n"
    using final_composition_counter challenge_counters record_counters
      stage_fields
    by simp
  have final_other_counters:
    "PTraceFriCounter verifier' = PTraceFriCounter builder \<and>
     PAlphaCounter verifier' = PAlphaCounter builder \<and>
     PQueryCounter verifier' = PQueryCounter builder"
    using final_trace_counter final_alpha_counter final_query_counter
      challenge_counters record_counters stage_fields
    by simp
  show ?case
  proof (intro exI conjI)
    show "bs' = bs @ (b # challenges_tail)"
      using bs'_eq bs_tail_eq by simp
    show "pairs = zip (b # challenges_tail) roots"
      using pairs_eq pairs_tail_eq roots_eq head_sync by simp
    show "PState verifier' = PState sent"
      by (rule final_state)
    show "PTranscript verifier' = rest"
      by (rule final_tr)
    show "verifier \<le> verifier'"
      by (rule verifier_ext)
    show "PTraceFriCounter verifier' = PTraceFriCounter builder"
      using final_other_counters by simp
    show "PCompositionFriCounter verifier' =
      PCompositionFriCounter builder + Suc n"
      by (rule final_composition_counter_builder)
    show "PAlphaCounter verifier' = PAlphaCounter builder"
      using final_other_counters by simp
    show "PQueryCounter verifier' = PQueryCounter builder"
      using final_other_counters by simp
  qed
qed

lemma ro_checked_staged_transcript_program_ro_verify_monad_full_sync:
  fixes verifier_final :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and transcript_out:
      "Some (data, sent) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier_out:
      "Some (results, verifier_final) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary sent
              (staged_proof_transcript data)))"
  shows
    "(PState verifier_final = PState sent \<and>
      PTranscript verifier_final = [] \<and>
      verifier_state_from_adversary sent (staged_proof_transcript data) \<le>
        verifier_final \<and>
      PQueryCounter verifier_final = rounds) \<and>
     (\<exists>fr trace_pairs f_final as dg composition_pairs final
          verifier_query_state.
        fr = staged_trace_root data \<and>
        map fst trace_pairs = staged_trace_fri_challenges data \<and>
        map snd trace_pairs = staged_trace_fri_roots data \<and>
        f_final = staged_trace_final data \<and>
        as = staged_alphas data \<and>
        dg = staged_degree data \<and>
        to_nat dg \<le> maxDegree \<and>
        map fst composition_pairs =
          staged_composition_fri_challenges data \<and>
        map snd composition_pairs = staged_composition_fri_roots data \<and>
        final = staged_composition_final data \<and>
        Some (results, verifier_final) \<in>
          set_dist
            (execute
              (ntimes
                (ro_verifier_query_round_program fr trace_pairs f_final as
                  composition_pairs final)
                rounds)
              verifier_query_state) \<and>
        sent \<le> verifier_query_state \<and>
        PTranscript verifier_query_state =
          List.concat (staged_query_chunks data) \<and>
        PQueryCounter verifier_query_state = 0)"
proof -
  let ?start =
    "verifier_state_from_adversary sent (staged_proof_transcript data)"

  from transcript_out obtain fr s1 s2 trace_roots trace_bs s3
      trace_final s4 s5 as s6 dg s7 s8 s9 composition_roots
      composition_bs s10 composition_final s11 s12 query_chunks where
    root_out:
      "Some (fr, s1) \<in>
        set_dist (execute (trace_root_stage A) adversary_initial_state)"
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
    and builder_assert_out:
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
    by (rule ro_checked_staged_transcript_program_outcomeE)

  from verifier_out obtain fr_v trace_pairs trace_final_v as_v dg_v
      composition_pairs composition_final_v v1 v2 v3 v4 v5 v6 v7 v8 where
    verifier_root_out:
      "Some (fr_v, v1) \<in> set_dist (execute protocol_absorb_read ?start)"
    and verifier_trace_out:
      "Some (trace_pairs, v2) \<in>
        set_dist
          (execute (ntimes ro_receive_trace_fri_commits (ceil_log clength))
            v1)"
    and verifier_trace_final_out:
      "Some (trace_final_v, v3) \<in> set_dist (execute protocol_absorb_read v2)"
    and verifier_alpha_out:
      "Some (as_v, v4) \<in>
        set_dist
          (execute (mmap (replicate (length spec) ro_alpha_round)) v3)"
    and verifier_degree_out:
      "Some (dg_v, v5) \<in> set_dist (execute protocol_absorb_read v4)"
    and verifier_assert_out:
      "Some ((), v6) \<in>
        set_dist (execute (assert (to_nat dg_v \<le> maxDegree)) v5)"
    and verifier_composition_out:
      "Some (composition_pairs, v7) \<in>
        set_dist
          (execute
            (ntimes ro_receive_composition_fri_commits
              (ceil_log (to_nat dg_v + 1))) v6)"
    and verifier_composition_final_out:
      "Some (composition_final_v, v8) \<in> set_dist (execute protocol_absorb_read v7)"
    and verifier_query_out:
      "Some (results, verifier_final) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr_v trace_pairs
                trace_final_v as_v composition_pairs composition_final_v)
              rounds) v8)"
    by (rule ro_verify_monad_outcomeE)

  have root_controlled:
    "controlled_ro_program (trace_root_budget budgets) (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have trace_final_controlled:
    "controlled_ro_program (trace_final_budget budgets)
      (trace_final_stage A trace_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have degree_controlled:
    "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_controlled:
    "controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg composition_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast

  have trace_bound:
    "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have builder_assert_cond:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    by (rule assert_unit_outcomeD(1)[OF builder_assert_out])
  have s9_eq: "s9 = s8"
    by (rule assert_unit_outcomeD(2)[OF builder_assert_out])
  have composition_bound:
    "0 + ceil_log (to_nat dg + 1) \<le>
      length (composition_fri_budgets budgets)"
    using builder_assert_cond wf unfolding staged_budget_wellformed_def
    by simp

  have root_stage_ext: "adversary_initial_state \<le> s1"
    using controlled_ro_program_extension[OF root_controlled] root_out
    unfolding hash_extension_preserving_def by blast
  have root_stage_fields:
    "PState s1 = PState adversary_initial_state"
    "PTraceFriCounter s1 = PTraceFriCounter adversary_initial_state"
    "PCompositionFriCounter s1 = PCompositionFriCounter adversary_initial_state"
    "PAlphaCounter s1 = PAlphaCounter adversary_initial_state"
    "PQueryCounter s1 = PQueryCounter adversary_initial_state"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp_all
  have root_record_ext: "s1 \<le> s2"
    using ro_record_staged_message_absorb_lookup_state[OF root_record_out]
    by simp
  have root_record_counters:
    "PTraceFriCounter s2 = PTraceFriCounter s1 \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
     PAlphaCounter s2 = PAlphaCounter s1 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    by (rule ro_record_staged_message_counter_preserves[OF root_record_out])

  have trace_props:
    "ro_absorb_lookup_chain s3 (PState s2) trace_roots (PState s3) \<and>
      s2 \<le> s3"
    by (rule ro_staged_trace_fri_program_absorb_lookup_chain
        [OF controlled trace_bound trace_out])
  have trace_counters:
    "PTraceFriCounter s3 = PTraceFriCounter s2 + ceil_log clength \<and>
     PCompositionFriCounter s3 = PCompositionFriCounter s2 \<and>
     PAlphaCounter s3 = PAlphaCounter s2 \<and>
     PQueryCounter s3 = PQueryCounter s2"
    by (rule ro_staged_trace_fri_program_counters
        [OF controlled trace_bound trace_out])

  have trace_final_stage_ext: "s3 \<le> s4"
    using controlled_ro_program_extension[OF trace_final_controlled]
      trace_final_out
    unfolding hash_extension_preserving_def by blast
  have trace_final_stage_fields:
    "PState s4 = PState s3"
    "PTraceFriCounter s4 = PTraceFriCounter s3"
    "PCompositionFriCounter s4 = PCompositionFriCounter s3"
    "PAlphaCounter s4 = PAlphaCounter s3"
    "PQueryCounter s4 = PQueryCounter s3"
    using controlled_stage_outcome_fields
        [OF trace_final_controlled trace_final_out]
    by simp_all
  have trace_final_record_ext: "s4 \<le> s5"
    using ro_record_staged_message_absorb_lookup_state
        [OF trace_final_record_out]
    by simp
  have trace_final_record_counters:
    "PTraceFriCounter s5 = PTraceFriCounter s4 \<and>
     PCompositionFriCounter s5 = PCompositionFriCounter s4 \<and>
     PAlphaCounter s5 = PAlphaCounter s4 \<and>
     PQueryCounter s5 = PQueryCounter s4"
    by (rule ro_record_staged_message_counter_preserves
        [OF trace_final_record_out])

  have alpha_props:
    "ro_absorb_lookup_chain s6 (PState s5) as (PState s6) \<and> s5 \<le> s6"
    by (rule ro_staged_alpha_program_absorb_lookup_chain[OF alpha_out])
  have alpha_counters:
    "PTraceFriCounter s6 = PTraceFriCounter s5 \<and>
     PCompositionFriCounter s6 = PCompositionFriCounter s5 \<and>
     PAlphaCounter s6 = PAlphaCounter s5 + length spec \<and>
     PQueryCounter s6 = PQueryCounter s5"
    by (rule ro_staged_alpha_program_counters[OF alpha_out])

  have degree_stage_ext: "s6 \<le> s7"
    using controlled_ro_program_extension[OF degree_controlled] degree_out
    unfolding hash_extension_preserving_def by blast
  have degree_stage_fields:
    "PState s7 = PState s6"
    "PTraceFriCounter s7 = PTraceFriCounter s6"
    "PCompositionFriCounter s7 = PCompositionFriCounter s6"
    "PAlphaCounter s7 = PAlphaCounter s6"
    "PQueryCounter s7 = PQueryCounter s6"
    using controlled_stage_outcome_fields[OF degree_controlled degree_out]
    by simp_all
  have degree_record_ext: "s7 \<le> s8"
    using ro_record_staged_message_absorb_lookup_state[OF degree_record_out]
    by simp
  have degree_record_counters:
    "PTraceFriCounter s8 = PTraceFriCounter s7 \<and>
     PCompositionFriCounter s8 = PCompositionFriCounter s7 \<and>
     PAlphaCounter s8 = PAlphaCounter s7 \<and>
     PQueryCounter s8 = PQueryCounter s7"
    by (rule ro_record_staged_message_counter_preserves[OF degree_record_out])

  have composition_props_s9:
    "ro_absorb_lookup_chain s10 (PState s9) composition_roots
      (PState s10) \<and> s9 \<le> s10"
    by (rule ro_staged_composition_fri_program_absorb_lookup_chain
        [OF controlled composition_bound composition_out])
  have composition_props:
    "ro_absorb_lookup_chain s10 (PState s8) composition_roots
      (PState s10) \<and> s8 \<le> s10"
    using composition_props_s9 s9_eq by simp
  have composition_counters:
    "PTraceFriCounter s10 = PTraceFriCounter s9 \<and>
     PCompositionFriCounter s10 =
       PCompositionFriCounter s9 + ceil_log (to_nat dg + 1) \<and>
     PAlphaCounter s10 = PAlphaCounter s9 \<and>
     PQueryCounter s10 = PQueryCounter s9"
    by (rule ro_staged_composition_fri_program_counters
        [OF controlled composition_bound composition_out])

  have composition_final_stage_ext: "s10 \<le> s11"
    using controlled_ro_program_extension[OF composition_final_controlled]
      composition_final_out
    unfolding hash_extension_preserving_def by blast
  have composition_final_stage_fields:
    "PState s11 = PState s10"
    "PTraceFriCounter s11 = PTraceFriCounter s10"
    "PCompositionFriCounter s11 = PCompositionFriCounter s10"
    "PAlphaCounter s11 = PAlphaCounter s10"
    "PQueryCounter s11 = PQueryCounter s10"
    using controlled_stage_outcome_fields
        [OF composition_final_controlled composition_final_out]
    by simp_all
  have composition_final_record_ext: "s11 \<le> s12"
    using ro_record_staged_message_absorb_lookup_state
        [OF composition_final_record_out]
    by simp
  have composition_final_record_counters:
    "PTraceFriCounter s12 = PTraceFriCounter s11 \<and>
     PCompositionFriCounter s12 = PCompositionFriCounter s11 \<and>
     PAlphaCounter s12 = PAlphaCounter s11 \<and>
     PQueryCounter s12 = PQueryCounter s11"
    by (rule ro_record_staged_message_counter_preserves
        [OF composition_final_record_out])

  have query_props:
    "ro_absorb_lookup_chain sent (PState s12) (List.concat query_chunks)
      (PState sent) \<and> s12 \<le> sent"
    by (rule ro_checked_staged_query_program_absorb_lookup_chain
        [OF controlled query_bound query_out])

  have ext_s3_s5: "s3 \<le> s5"
    by (rule hash_ext_trans[OF trace_final_stage_ext
          trace_final_record_ext])
  have ext_s6_s8: "s6 \<le> s8"
    by (rule hash_ext_trans[OF degree_stage_ext degree_record_ext])
  have ext_s10_s12: "s10 \<le> s12"
    by (rule hash_ext_trans[OF composition_final_stage_ext
          composition_final_record_ext])
  have ext_s3_sent: "s3 \<le> sent"
    by (rule hash_ext_trans[OF ext_s3_s5])
      (rule hash_ext_trans[OF conjunct2[OF alpha_props]],
        rule hash_ext_trans[OF ext_s6_s8],
        rule hash_ext_trans[OF conjunct2[OF composition_props]],
        rule hash_ext_trans[OF ext_s10_s12 conjunct2[OF query_props]])
  have ext_s2_sent: "s2 \<le> sent"
    by (rule hash_ext_trans[OF conjunct2[OF trace_props] ext_s3_sent])
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
  have ext_s12_sent: "s12 \<le> sent"
    using query_props by simp

  have start_ext: "sent \<le> ?start"
    unfolding verifier_state_from_adversary_def less_eq_hash_ext_def
      less_eq_fmap_def
    by simp
  have s2_ext_start: "s2 \<le> ?start"
    by (rule hash_ext_trans[OF ext_s2_sent start_ext])
  have start_state: "PState ?start = PState adversary_initial_state"
    by simp
  have start_tr:
    "PTranscript ?start =
      fr # (trace_roots @ [trace_final] @ as @ [dg] @
        composition_roots @ [composition_final] @ List.concat query_chunks)"
    using data_eq
    unfolding staged_proof_transcript_def verifier_header_messages_def
    by simp

  have root_sync:
    "fr_v = fr \<and>
     PState v1 = PState s2 \<and>
     PTranscript v1 = trace_roots @ [trace_final] @ as @ [dg] @
       composition_roots @ [composition_final] @ List.concat query_chunks \<and>
     ?start \<le> v1 \<and>
     PTraceFriCounter v1 = PTraceFriCounter ?start \<and>
     PCompositionFriCounter v1 = PCompositionFriCounter ?start \<and>
     PAlphaCounter v1 = PAlphaCounter ?start \<and>
     PQueryCounter v1 = PQueryCounter ?start"
    by (rule controlled_ro_record_staged_message_absorb_read_sync
        [OF root_controlled root_out root_record_out s2_ext_start start_state
          start_tr verifier_root_out])
  have sent_ext_v1: "sent \<le> v1"
    by (rule hash_ext_trans[OF start_ext]) (use root_sync in simp)
  have s3_ext_v1: "s3 \<le> v1"
    by (rule hash_ext_trans[OF ext_s3_sent sent_ext_v1])
  have counters_v1_s2:
    "PTraceFriCounter v1 = PTraceFriCounter s2 \<and>
     PCompositionFriCounter v1 = PCompositionFriCounter s2 \<and>
     PAlphaCounter v1 = PAlphaCounter s2 \<and>
     PQueryCounter v1 = PQueryCounter s2"
    using root_sync root_stage_fields root_record_counters
    by simp

  have trace_sync:
    "\<exists>trace_challenges.
      trace_bs = [] @ trace_challenges \<and>
      trace_pairs = zip trace_challenges trace_roots \<and>
      PState v2 = PState s3 \<and>
      PTranscript v2 = [trace_final] @ as @ [dg] @ composition_roots @
        [composition_final] @ List.concat query_chunks \<and>
      v1 \<le> v2 \<and>
      PTraceFriCounter v2 = PTraceFriCounter s2 + ceil_log clength \<and>
      PCompositionFriCounter v2 = PCompositionFriCounter s2 \<and>
      PAlphaCounter v2 = PAlphaCounter s2 \<and>
      PQueryCounter v2 = PQueryCounter s2"
    by (rule ro_staged_trace_fri_program_ro_receive_trace_fri_commits_sync
        [OF controlled trace_bound trace_out s3_ext_v1 _ _ _ _ _ _
          verifier_trace_out])
      (use root_sync counters_v1_s2 in simp_all)
  then obtain trace_challenges where
    trace_bs_eq: "trace_bs = trace_challenges"
    and trace_pairs_eq: "trace_pairs = zip trace_challenges trace_roots"
    and v2_state: "PState v2 = PState s3"
    and v2_tr:
      "PTranscript v2 = [trace_final] @ as @ [dg] @ composition_roots @
        [composition_final] @ List.concat query_chunks"
    and v1_ext_v2: "v1 \<le> v2"
    and v2_trace_counter:
      "PTraceFriCounter v2 = PTraceFriCounter s2 + ceil_log clength"
    and v2_composition_counter:
      "PCompositionFriCounter v2 = PCompositionFriCounter s2"
    and v2_alpha_counter: "PAlphaCounter v2 = PAlphaCounter s2"
    and v2_query_counter: "PQueryCounter v2 = PQueryCounter s2"
    by auto
  have sent_ext_v2: "sent \<le> v2"
    by (rule hash_ext_trans[OF sent_ext_v1 v1_ext_v2])
  have s5_ext_v2: "s5 \<le> v2"
    by (rule hash_ext_trans[OF ext_s5_sent sent_ext_v2])
  have trace_final_tr_v2:
    "PTranscript v2 =
      trace_final # (as @ [dg] @ composition_roots @
        [composition_final] @ List.concat query_chunks)"
    using v2_tr by simp

  have trace_final_sync:
    "trace_final_v = trace_final \<and>
     PState v3 = PState s5 \<and>
     PTranscript v3 = as @ [dg] @ composition_roots @
       [composition_final] @ List.concat query_chunks \<and>
     v2 \<le> v3 \<and>
     PTraceFriCounter v3 = PTraceFriCounter v2 \<and>
     PCompositionFriCounter v3 = PCompositionFriCounter v2 \<and>
     PAlphaCounter v3 = PAlphaCounter v2 \<and>
     PQueryCounter v3 = PQueryCounter v2"
    by (rule controlled_ro_record_staged_message_absorb_read_sync
        [OF trace_final_controlled trace_final_out trace_final_record_out
          s5_ext_v2 v2_state trace_final_tr_v2 verifier_trace_final_out])
  have sent_ext_v3: "sent \<le> v3"
    by (rule hash_ext_trans[OF sent_ext_v2]) (use trace_final_sync in simp)
  have counters_v3_s5:
    "PTraceFriCounter v3 = PTraceFriCounter s5 \<and>
     PCompositionFriCounter v3 = PCompositionFriCounter s5 \<and>
     PAlphaCounter v3 = PAlphaCounter s5 \<and>
     PQueryCounter v3 = PQueryCounter s5"
    using trace_final_sync trace_counters trace_final_stage_fields
      trace_final_record_counters v2_trace_counter v2_composition_counter
      v2_alpha_counter v2_query_counter
    by simp
  have s6_ext_v3: "s6 \<le> v3"
    by (rule hash_ext_trans[OF ext_s6_sent sent_ext_v3])

  have alpha_tr_v3:
    "PTranscript v3 =
      as @ ([dg] @ composition_roots @ [composition_final] @
        List.concat query_chunks)"
    using trace_final_sync by simp
  have alpha_sync:
    "as_v = as \<and>
     PState v4 = PState s6 \<and>
     PTranscript v4 = [dg] @ composition_roots @ [composition_final] @
       List.concat query_chunks \<and>
     v3 \<le> v4 \<and>
     PTraceFriCounter v4 = PTraceFriCounter s5 \<and>
     PCompositionFriCounter v4 = PCompositionFriCounter s5 \<and>
     PAlphaCounter v4 = PAlphaCounter s5 + length spec \<and>
     PQueryCounter v4 = PQueryCounter s5"
    by (rule ro_staged_alpha_program_ro_alpha_round_sync
        [OF alpha_out s6_ext_v3 _ _ _ _ _ alpha_tr_v3 verifier_alpha_out])
      (use trace_final_sync counters_v3_s5 in simp_all)
  have sent_ext_v4: "sent \<le> v4"
    by (rule hash_ext_trans[OF sent_ext_v3]) (use alpha_sync in simp)
  have counters_v4_s6:
    "PTraceFriCounter v4 = PTraceFriCounter s6 \<and>
     PCompositionFriCounter v4 = PCompositionFriCounter s6 \<and>
     PAlphaCounter v4 = PAlphaCounter s6 \<and>
     PQueryCounter v4 = PQueryCounter s6"
    using alpha_sync alpha_counters by simp
  have s8_ext_v4: "s8 \<le> v4"
    by (rule hash_ext_trans[OF ext_s8_sent sent_ext_v4])

  have degree_tr_v4:
    "PTranscript v4 =
      dg # (composition_roots @ [composition_final] @
        List.concat query_chunks)"
    using alpha_sync by simp
  have degree_sync:
    "dg_v = dg \<and>
     PState v5 = PState s8 \<and>
     PTranscript v5 = composition_roots @ [composition_final] @
       List.concat query_chunks \<and>
     v4 \<le> v5 \<and>
     PTraceFriCounter v5 = PTraceFriCounter v4 \<and>
     PCompositionFriCounter v5 = PCompositionFriCounter v4 \<and>
     PAlphaCounter v5 = PAlphaCounter v4 \<and>
     PQueryCounter v5 = PQueryCounter v4"
    by (rule controlled_ro_record_staged_message_absorb_read_sync
        [OF degree_controlled degree_out degree_record_out s8_ext_v4 _
          degree_tr_v4 verifier_degree_out])
      (use alpha_sync in simp)
  have v6_eq: "v6 = v5"
    by (rule assert_unit_outcomeD(2)[OF verifier_assert_out])
  have degree_bound: "to_nat dg \<le> maxDegree"
    using assert_unit_outcomeD(1)[OF verifier_assert_out] degree_sync
    by simp
  have sent_ext_v5: "sent \<le> v5"
    by (rule hash_ext_trans[OF sent_ext_v4]) (use degree_sync in simp)
  have sent_ext_v6: "sent \<le> v6"
    using sent_ext_v5 v6_eq by simp
  have counters_v6_s9:
    "PTraceFriCounter v6 = PTraceFriCounter s9 \<and>
     PCompositionFriCounter v6 = PCompositionFriCounter s9 \<and>
     PAlphaCounter v6 = PAlphaCounter s9 \<and>
     PQueryCounter v6 = PQueryCounter s9"
    using degree_sync counters_v4_s6 degree_stage_fields degree_record_counters
      s9_eq v6_eq
    by simp
  have s10_ext_v6: "s10 \<le> v6"
    by (rule hash_ext_trans[OF ext_s10_sent sent_ext_v6])
  have composition_tr_v6:
    "PTranscript v6 = composition_roots @
      ([composition_final] @ List.concat query_chunks)"
    using degree_sync v6_eq by simp

  have composition_sync:
    "\<exists>composition_challenges.
      composition_bs = [] @ composition_challenges \<and>
      composition_pairs = zip composition_challenges composition_roots \<and>
      PState v7 = PState s10 \<and>
      PTranscript v7 = [composition_final] @ List.concat query_chunks \<and>
      v6 \<le> v7 \<and>
      PTraceFriCounter v7 = PTraceFriCounter s9 \<and>
      PCompositionFriCounter v7 =
        PCompositionFriCounter s9 + ceil_log (to_nat dg + 1) \<and>
      PAlphaCounter v7 = PAlphaCounter s9 \<and>
      PQueryCounter v7 = PQueryCounter s9"
    by (rule ro_staged_composition_fri_program_ro_receive_composition_fri_commits_sync
        [OF controlled composition_bound composition_out s10_ext_v6 _ _ _ _ _
          composition_tr_v6 _])
      (use degree_sync counters_v6_s9 s9_eq v6_eq verifier_composition_out in simp_all)
  then obtain composition_challenges where
    composition_bs_eq: "composition_bs = composition_challenges"
    and composition_pairs_eq:
      "composition_pairs = zip composition_challenges composition_roots"
    and v7_state: "PState v7 = PState s10"
    and v7_tr:
      "PTranscript v7 = [composition_final] @ List.concat query_chunks"
    and v6_ext_v7: "v6 \<le> v7"
    and v7_trace_counter: "PTraceFriCounter v7 = PTraceFriCounter s9"
    and v7_composition_counter:
      "PCompositionFriCounter v7 =
        PCompositionFriCounter s9 + ceil_log (to_nat dg + 1)"
    and v7_alpha_counter: "PAlphaCounter v7 = PAlphaCounter s9"
    and v7_query_counter: "PQueryCounter v7 = PQueryCounter s9"
    by auto
  have sent_ext_v7: "sent \<le> v7"
    by (rule hash_ext_trans[OF sent_ext_v6 v6_ext_v7])
  have s12_ext_v7: "s12 \<le> v7"
    by (rule hash_ext_trans[OF ext_s12_sent sent_ext_v7])
  have composition_final_tr_v7:
    "PTranscript v7 = composition_final # List.concat query_chunks"
    using v7_tr by simp

  have composition_final_sync:
    "composition_final_v = composition_final \<and>
     PState v8 = PState s12 \<and>
     PTranscript v8 = List.concat query_chunks \<and>
     v7 \<le> v8 \<and>
     PTraceFriCounter v8 = PTraceFriCounter v7 \<and>
     PCompositionFriCounter v8 = PCompositionFriCounter v7 \<and>
     PAlphaCounter v8 = PAlphaCounter v7 \<and>
     PQueryCounter v8 = PQueryCounter v7"
    by (rule controlled_ro_record_staged_message_absorb_read_sync
        [OF composition_final_controlled composition_final_out
          composition_final_record_out s12_ext_v7 v7_state
          composition_final_tr_v7 verifier_composition_final_out])
  have sent_ext_v8: "sent \<le> v8"
    by (rule hash_ext_trans[OF sent_ext_v7])
      (use composition_final_sync in simp)
  have start_ext_v1: "?start \<le> v1"
    using root_sync by simp
  have v2_ext_v3: "v2 \<le> v3"
    using trace_final_sync by simp
  have v3_ext_v4: "v3 \<le> v4"
    using alpha_sync by simp
  have v4_ext_v5: "v4 \<le> v5"
    using degree_sync by simp
  have v5_ext_v6: "v5 \<le> v6"
    using v6_eq by (simp add: hash_ext_refl)
  have v7_ext_v8: "v7 \<le> v8"
    using composition_final_sync by simp
  have start_ext_v2: "?start \<le> v2"
    by (rule hash_ext_trans[OF start_ext_v1 v1_ext_v2])
  have start_ext_v3: "?start \<le> v3"
    by (rule hash_ext_trans[OF start_ext_v2 v2_ext_v3])
  have start_ext_v4: "?start \<le> v4"
    by (rule hash_ext_trans[OF start_ext_v3 v3_ext_v4])
  have start_ext_v5: "?start \<le> v5"
    by (rule hash_ext_trans[OF start_ext_v4 v4_ext_v5])
  have start_ext_v6: "?start \<le> v6"
    by (rule hash_ext_trans[OF start_ext_v5 v5_ext_v6])
  have start_ext_v7: "?start \<le> v7"
    by (rule hash_ext_trans[OF start_ext_v6 v6_ext_v7])
  have start_ext_v8: "?start \<le> v8"
    by (rule hash_ext_trans[OF start_ext_v7 v7_ext_v8])
  have counters_v8_s12:
    "PTraceFriCounter v8 = PTraceFriCounter s12 \<and>
     PCompositionFriCounter v8 = PCompositionFriCounter s12 \<and>
     PAlphaCounter v8 = PAlphaCounter s12 \<and>
     PQueryCounter v8 = PQueryCounter s12"
    using composition_final_sync composition_counters
      composition_final_stage_fields composition_final_record_counters s9_eq
      v7_trace_counter v7_composition_counter v7_alpha_counter
      v7_query_counter
    by simp
  have query_counter_s12: "PQueryCounter s12 = 0"
    using root_stage_fields root_record_counters trace_counters
      trace_final_stage_fields trace_final_record_counters alpha_counters
      degree_stage_fields degree_record_counters s9_eq composition_counters
      composition_final_stage_fields composition_final_record_counters
    by simp

  have shape:
    "length trace_roots = ceil_log clength \<and>
     length trace_bs = ceil_log clength \<and>
     length composition_roots = ceil_log (to_nat dg + 1) \<and>
     length composition_bs = ceil_log (to_nat dg + 1)"
    using ro_checked_staged_transcript_program_outcome_shape[OF transcript_out]
      data_eq
    by simp
  have trace_challenges_eq: "map fst trace_pairs = trace_bs"
    using trace_pairs_eq trace_bs_eq shape by simp
  have trace_roots_eq: "trace_roots = map snd trace_pairs"
    using trace_pairs_eq trace_bs_eq shape by simp
  have composition_challenges_eq:
      "map fst composition_pairs = composition_bs"
    using composition_pairs_eq composition_bs_eq shape by simp
  have composition_roots_eq: "composition_roots = map snd composition_pairs"
    using composition_pairs_eq composition_bs_eq shape by simp

  have query_sync:
    "PState verifier_final = PState sent \<and>
     PTranscript verifier_final = [] \<and>
     v8 \<le> verifier_final \<and>
     PQueryCounter verifier_final = PQueryCounter s12 + rounds"
    by (rule ro_checked_staged_query_program_verifier_rounds_sync
        [OF controlled query_bound query_out sent_ext_v8 _ _ _
          trace_roots_eq composition_roots_eq _])
      (use composition_final_sync counters_v8_s12 verifier_query_out
        root_sync trace_final_sync alpha_sync degree_sync composition_sync
        in simp_all)
  have start_ext_final: "?start \<le> verifier_final"
    by (rule hash_ext_trans[OF start_ext_v8]) (use query_sync in simp)
  have header_sync:
      "\<exists>fr trace_pairs f_final as dg composition_pairs final
          verifier_query_state.
        fr = staged_trace_root data \<and>
        map fst trace_pairs = staged_trace_fri_challenges data \<and>
        map snd trace_pairs = staged_trace_fri_roots data \<and>
        f_final = staged_trace_final data \<and>
        as = staged_alphas data \<and>
        dg = staged_degree data \<and>
        to_nat dg \<le> maxDegree \<and>
        map fst composition_pairs =
          staged_composition_fri_challenges data \<and>
        map snd composition_pairs = staged_composition_fri_roots data \<and>
        final = staged_composition_final data \<and>
        Some (results, verifier_final) \<in>
          set_dist
            (execute
              (ntimes
                (ro_verifier_query_round_program fr trace_pairs f_final as
                  composition_pairs final)
                rounds)
              verifier_query_state) \<and>
        sent \<le> verifier_query_state \<and>
        PTranscript verifier_query_state =
          List.concat (staged_query_chunks data) \<and>
        PQueryCounter verifier_query_state = 0"
    apply (rule exI[of _ fr_v])
    apply (rule exI[of _ trace_pairs])
    apply (rule exI[of _ trace_final_v])
    apply (rule exI[of _ as_v])
    apply (rule exI[of _ dg_v])
    apply (rule exI[of _ composition_pairs])
    apply (rule exI[of _ composition_final_v])
    apply (rule exI[of _ v8])
    using root_sync trace_challenges_eq trace_roots_eq trace_final_sync
      alpha_sync degree_sync degree_bound composition_challenges_eq
      composition_roots_eq composition_final_sync verifier_query_out
      sent_ext_v8 counters_v8_s12 query_counter_s12 data_eq
    by simp
  show ?thesis
    using query_sync start_ext_final query_counter_s12 header_sync by simp
qed

lemma ro_checked_staged_transcript_program_ro_verify_monad_sync:
  fixes verifier_final :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and transcript_out:
      "Some (data, sent) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier_out:
      "Some (results, verifier_final) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary sent
              (staged_proof_transcript data)))"
  shows
    "PState verifier_final = PState sent \<and>
     PTranscript verifier_final = [] \<and>
     verifier_state_from_adversary sent (staged_proof_transcript data) \<le>
       verifier_final \<and>
     PQueryCounter verifier_final = rounds"
  using ro_checked_staged_transcript_program_ro_verify_monad_full_sync[
      OF wf controlled transcript_out verifier_out]
  by blast

lemma ro_absorb_checked_staged_security_experiment_with_data_state_outcome_sync:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
  shows
    "PState final_state = PState attacker_state \<and>
     PTranscript final_state = [] \<and>
     verifier_state_from_adversary attacker_state
       (staged_proof_transcript data) \<le> final_state \<and>
     PQueryCounter final_state = rounds"
proof -
  have builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    using ro_absorb_checked_staged_security_experiment_with_data_state_outcomeE
      [OF outcome]
    by blast+
  show ?thesis
    by (rule ro_checked_staged_transcript_program_ro_verify_monad_sync
        [OF wf controlled builder verifier])
qed

definition ro_absorb_checked_staged_security_with_data_state_final_sync ::
  "((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
      'f protocol_channel) option \<Rightarrow> bool"
where
  "ro_absorb_checked_staged_security_with_data_state_final_sync out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((data, attacker_state), _), final_state) \<Rightarrow>
        PState final_state = PState attacker_state \<and>
        PTranscript final_state = [] \<and>
        verifier_state_from_adversary attacker_state
          (staged_proof_transcript data) \<le> final_state \<and>
        PQueryCounter final_state = rounds)"

lemma ro_absorb_checked_staged_security_with_data_state_accepted_final_sync_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and accepted: "accepted out"
  shows "ro_absorb_checked_staged_security_with_data_state_final_sync out"
proof (cases out)
  case None
  with accepted show ?thesis
    unfolding accepted_def by simp
next
  case (Some z)
  obtain data_attacker result final_state where z_eq:
    "z = ((data_attacker, result), final_state)"
    by (cases z) auto
  obtain data attacker_state where data_attacker_eq:
    "data_attacker = (data, attacker_state)"
    by (cases data_attacker) auto
  have outcome_some:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    using outcome Some z_eq data_attacker_eq by simp
  have sync:
    "PState final_state = PState attacker_state \<and>
     PTranscript final_state = [] \<and>
     verifier_state_from_adversary attacker_state
       (staged_proof_transcript data) \<le> final_state \<and>
     PQueryCounter final_state = rounds"
    by (rule ro_absorb_checked_staged_security_experiment_with_data_state_outcome_sync
        [OF wf controlled outcome_some])
  show ?thesis
    unfolding ro_absorb_checked_staged_security_with_data_state_final_sync_def
    using Some z_eq data_attacker_eq sync by simp
qed

lemma ro_absorb_checked_staged_security_with_data_state_acceptance_le_final_sync:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
       accepted adversary_initial_state \<le>
     wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
       ro_absorb_checked_staged_security_with_data_state_final_sync
       adversary_initial_state"
  by (rule wp_event_mono_on_support)
     (use assms
        ro_absorb_checked_staged_security_with_data_state_accepted_final_sync_on_support
      in blast)

lemma ro_absorb_checked_staged_security_experiment_with_data_state_accepted_query_witnessesE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and accepted: "accepted out"
  obtains data attacker_state result final_state query_start raw_idxs query_idxs
      query_states where
    "out = Some (((data, attacker_state), result), final_state)"
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (ro_checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute ro_verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    "Some (staged_query_chunks data, attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data) 0 rounds)
          query_start)"
    "query_start \<le> attacker_state"
    "length raw_idxs = rounds"
    "length query_states = rounds"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length (staged_query_chunks data) = rounds"
    "PQueryCounter attacker_state = PQueryCounter query_start + rounds"
    "\<forall>j < rounds.
      query_states ! j \<le> attacker_state \<and>
      PQueryCounter (query_states ! j) = PQueryCounter query_start + j \<and>
      fmlookup (HashMap attacker_state)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raw_idxs ! j) \<and>
      verifier_query_round_chunk (query_idxs ! j)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! j)"
    "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    "PState final_state = PState attacker_state \<and>
     PTranscript final_state = [] \<and>
     verifier_state_from_adversary attacker_state
       (staged_proof_transcript data) \<le> final_state \<and>
     PQueryCounter final_state = rounds"
proof -
  from accepted obtain y where out_some: "out = Some y"
    unfolding accepted_def by (cases out) auto
  obtain data_attacker result final_state where y_eq:
    "y = ((data_attacker, result), final_state)"
    by (cases y) auto
  obtain data attacker_state where data_attacker_eq:
    "data_attacker = (data, attacker_state)"
    by (cases data_attacker) auto
  have out_eq: "out = Some (((data, attacker_state), result), final_state)"
    using out_some y_eq data_attacker_eq by simp
  have outcome_some:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    using outcome out_eq by simp
  show ?thesis
  proof (rule ro_absorb_checked_staged_security_experiment_with_data_state_outcomeE
      [OF outcome_some])
    assume builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
      and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    show ?thesis
    proof (rule ro_checked_staged_transcript_program_query_witnessesE
        [OF wf controlled builder])
      fix query_start raw_idxs query_idxs query_states
      assume query_out:
        "Some (staged_query_chunks data, attacker_state) \<in>
          set_dist
            (execute
              (ro_checked_staged_query_program A
                (staged_trace_fri_roots data)
                (staged_composition_fri_roots data) 0 rounds)
              query_start)"
        and len_raw: "length raw_idxs = rounds"
        and len_states: "length query_states = rounds"
        and query_idxs_eq:
          "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
        and len_chunks: "length (staged_query_chunks data) = rounds"
        and query_start_ext: "query_start \<le> attacker_state"
        and query_count:
          "PQueryCounter attacker_state = PQueryCounter query_start + rounds"
        and query_props:
          "\<forall>j < rounds.
            query_states ! j \<le> attacker_state \<and>
            PQueryCounter (query_states ! j) = PQueryCounter query_start + j \<and>
            fmlookup (HashMap attacker_state)
              (QueryIndexChallenge
                (PQueryCounter (query_states ! j))
                (PState (query_states ! j))) =
              Some (raw_idxs ! j) \<and>
            verifier_query_round_chunk (query_idxs ! j)
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data)
              (staged_query_chunks data ! j)"
        and idx_bound: "\<forall>idx \<in> set query_idxs. idx < clength * scale"
      have sync:
        "PState final_state = PState attacker_state \<and>
         PTranscript final_state = [] \<and>
         verifier_state_from_adversary attacker_state
           (staged_proof_transcript data) \<le> final_state \<and>
         PQueryCounter final_state = rounds"
        by (rule ro_absorb_checked_staged_security_experiment_with_data_state_outcome_sync
            [OF wf controlled outcome_some])
      show ?thesis
        by (rule that[OF out_eq builder verifier query_out query_start_ext
              len_raw len_states query_idxs_eq len_chunks query_count query_props
              idx_bound sync])
    qed
  qed
qed

end

end