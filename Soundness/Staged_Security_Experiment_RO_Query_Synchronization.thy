theory Staged_Security_Experiment_RO_Query_Synchronization
  imports Staged_Security_Experiment_RO_Query_State_Bridge
begin

context soundness
begin

text \<open>
  This layer synchronizes one checked builder query round with the verifier's
  domain-separated query-index challenge.  It keeps the concrete builder
  pre-round state as a witness, instead of reconstructing it from a
  deterministic transcript fold.
\<close>

lemma ro_checked_staged_query_program_Suc_synchronizationE:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + Suc n \<le> length (query_opening_budgets budgets)"
    and outcome:
      "Some (chunks, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              i (Suc n)) s)"
  obtains raw chunk chunks' s1 s2 s3 where
    "Some (raw, s1) \<in>
      set_dist (execute receive_query_index_challenge s)"
    "Some (chunk, s2) \<in>
      set_dist (execute (query_opening_stage A i raw) s1)"
    "verifier_query_round_chunk (index (to_nat raw))
      trace_roots composition_roots chunk"
    "Some ((), s3) \<in>
      set_dist (execute (ro_record_staged_messages chunk) s2)"
    "Some (chunks', t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots composition_roots
            (Suc i) n) s3)"
    "chunks = chunk # chunks'"
    "s \<le> s1"
    "PState s1 = PState s"
    "PQueryCounter s1 = Suc (PQueryCounter s)"
    "s3 \<le> t"
    "PQueryCounter s3 = Suc (PQueryCounter s)"
    "ro_absorb_lookup_chain t (PState s) chunk (PState s3)"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  from ro_checked_staged_query_program_Suc_outcomeE[OF outcome]
  obtain raw chunk chunks' s1 s2 s3 where
    challenge_out:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and stage_out:
      "Some (chunk, s2) \<in>
        set_dist (execute (query_opening_stage A i raw) s1)"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and record_out:
      "Some ((), s3) \<in>
        set_dist (execute (ro_record_staged_messages chunk) s2)"
    and rest_out:
      "Some (chunks', t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
    .
  have i_bound: "i < length (query_opening_budgets budgets)"
    using bound by simp
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have challenge_props:
    "s \<le> s1 \<and> PState s1 = PState s \<and>
      PTranscript s1 = PTranscript s \<and>
      fmlookup (HashMap s1)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule receive_query_index_challenge_outcome[OF challenge_out])
  have challenge_counter:
    "PQueryCounter s1 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF challenge_out]
    by simp
  have stage_ext: "s1 \<le> s2"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have stage_state: "PState s2 = PState s1"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have stage_counter: "PQueryCounter s2 = PQueryCounter s1"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have record_chain:
    "ro_absorb_lookup_chain s3 (PState s2) chunk (PState s3) \<and>
      s2 \<le> s3"
    by (rule ro_record_staged_messages_absorb_lookup_chain[OF record_out])
  have record_counter: "PQueryCounter s3 = PQueryCounter s2"
    using ro_record_staged_messages_hash_extends_query_counter[OF record_out]
    by simp
  have tail_bound:
    "Suc i + n \<le> length (query_opening_budgets budgets)"
    using bound by simp
  have tail_props:
    "ro_absorb_lookup_chain t (PState s3) (List.concat chunks')
      (PState t) \<and> s3 \<le> t"
    by (rule ro_checked_staged_query_program_absorb_lookup_chain
        [OF controlled tail_bound rest_out])
  have s1_t: "s1 \<le> t"
    by (rule hash_ext_trans[OF stage_ext])
      (rule hash_ext_trans[OF conjunct2[OF record_chain]
        conjunct2[OF tail_props]])
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF conjunct2[OF conjunct2[OF
          conjunct2[OF challenge_props]]] s1_t])
  have head_chain_t:
    "ro_absorb_lookup_chain t (PState s) chunk (PState s3)"
  proof -
    have chain:
      "ro_absorb_lookup_chain t (PState s2) chunk (PState s3)"
      by (rule ro_absorb_lookup_chain_mono[OF conjunct1[OF record_chain]
            conjunct2[OF tail_props]])
    show ?thesis
      using chain challenge_props stage_state by simp
  qed
  have counter_s3:
    "PQueryCounter s3 = Suc (PQueryCounter s)"
    using record_counter stage_counter challenge_counter by simp
  show ?thesis
    by (rule that[OF challenge_out stage_out chunk_shape record_out rest_out
          chunks_eq conjunct1[OF challenge_props]
          conjunct1[OF conjunct2[OF challenge_props]] challenge_counter
          conjunct2[OF tail_props] counter_s3 head_chain_t lookup_t])
qed


lemma receive_query_index_challenge_matches_extended_recorded_lookup:
  fixes builder sent vstate vstate' :: "'f protocol_channel"
  assumes recorded:
      "fmlookup (HashMap sent)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some raw"
    and sent_ext: "sent \<le> vstate"
    and state_eq: "PState vstate = PState builder"
    and counter_eq: "PQueryCounter vstate = PQueryCounter builder"
    and outcome:
      "Some (raw', vstate') \<in>
        set_dist (execute receive_query_index_challenge vstate)"
  shows
    "raw' = raw \<and>
      PState vstate' = PState builder \<and>
      PTranscript vstate' = PTranscript vstate \<and>
      vstate \<le> vstate' \<and>
      PQueryCounter vstate' = Suc (PQueryCounter builder) \<and>
      fmlookup (HashMap vstate')
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some raw"
proof -
  have lookup_vstate:
    "fmlookup (HashMap vstate)
      (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
      Some raw"
    by (rule hash_extension_lookup[OF recorded sent_ext])
  have lookup_current:
    "fmlookup (HashMap vstate)
      (QueryIndexChallenge (PQueryCounter vstate) (PState vstate)) =
      Some raw"
    using lookup_vstate state_eq counter_eq by simp
  have known:
    "raw' = raw \<and>
      PState vstate' = PState vstate \<and>
      PTranscript vstate' = PTranscript vstate \<and> vstate \<le> vstate'"
    by (rule receive_query_index_challenge_known_outcome
        [OF lookup_current outcome])
  have counter:
    "PQueryCounter vstate' = Suc (PQueryCounter vstate)"
    using receive_query_index_challenge_counter_outcome[OF outcome] by simp
  have lookup_vstate':
    "fmlookup (HashMap vstate')
      (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
      Some raw"
  proof -
    have ext: "vstate \<le> vstate'"
      using known by simp
    show ?thesis
      by (rule hash_extension_lookup[OF lookup_vstate ext])
  qed
  show ?thesis
    using known counter state_eq counter_eq lookup_vstate' by simp
qed

lemma ro_checked_staged_query_program_Suc_verifier_challenge_syncE:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + Suc n \<le> length (query_opening_budgets budgets)"
    and builder_out:
      "Some (chunks, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              i (Suc n)) builder)"
    and sent_ext: "sent \<le> verifier_state"
    and state_eq: "PState verifier_state = PState builder"
    and counter_eq: "PQueryCounter verifier_state = PQueryCounter builder"
    and verifier_out:
      "Some (raw', verifier_state') \<in>
        set_dist (execute receive_query_index_challenge verifier_state)"
  obtains raw chunk chunks' s1 s2 s3 where
    "raw' = raw"
    "Some (raw, s1) \<in>
      set_dist (execute receive_query_index_challenge builder)"
    "Some (chunk, s2) \<in>
      set_dist (execute (query_opening_stage A i raw) s1)"
    "verifier_query_round_chunk (index (to_nat raw))
      trace_roots composition_roots chunk"
    "Some ((), s3) \<in>
      set_dist (execute (ro_record_staged_messages chunk) s2)"
    "Some (chunks', sent) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots composition_roots
            (Suc i) n) s3)"
    "chunks = chunk # chunks'"
    "PState verifier_state' = PState builder"
    "PTranscript verifier_state' = PTranscript verifier_state"
    "verifier_state \<le> verifier_state'"
    "PQueryCounter verifier_state' = Suc (PQueryCounter builder)"
    "ro_absorb_lookup_chain sent (PState builder) chunk (PState s3)"
proof -
  from ro_checked_staged_query_program_Suc_synchronizationE
      [OF controlled bound builder_out]
  obtain raw chunk chunks' s1 s2 s3 where
    builder_challenge:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge builder)"
    and stage:
      "Some (chunk, s2) \<in>
        set_dist (execute (query_opening_stage A i raw) s1)"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and record_out:
      "Some ((), s3) \<in>
        set_dist (execute (ro_record_staged_messages chunk) s2)"
    and rest:
      "Some (chunks', sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
    and builder_ext: "builder \<le> s1"
    and builder_state_s1: "PState s1 = PState builder"
    and builder_counter_s1:
      "PQueryCounter s1 = Suc (PQueryCounter builder)"
    and s3_sent: "s3 \<le> sent"
    and counter_s3: "PQueryCounter s3 = Suc (PQueryCounter builder)"
    and chain: "ro_absorb_lookup_chain sent (PState builder) chunk (PState s3)"
    and recorded:
      "fmlookup (HashMap sent)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) = Some raw"
    .
  have match:
    "raw' = raw \<and>
      PState verifier_state' = PState builder \<and>
      PTranscript verifier_state' = PTranscript verifier_state \<and>
      verifier_state \<le> verifier_state' \<and>
      PQueryCounter verifier_state' = Suc (PQueryCounter builder) \<and>
      fmlookup (HashMap verifier_state')
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some raw"
    by (rule receive_query_index_challenge_matches_extended_recorded_lookup
        [OF recorded sent_ext state_eq counter_eq verifier_out])
  show ?thesis
    by (rule that[OF conjunct1[OF match] builder_challenge stage chunk_shape
          record_out rest chunks_eq])
      (use match chain in simp_all)
qed

end

end
