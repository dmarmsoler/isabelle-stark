theory Staged_Security_Experiment_RO_Query_Rounds_Replay
  imports Staged_Security_Experiment_RO_Query_Round_Replay
begin

context soundness
begin

text \<open>
  Multi-round replay facts for the absorbing verifier.  This layer keeps the
  induction over query rounds separate from the single-round transcript and
  random-oracle lookup-chain analysis.
\<close>

lemma ro_checked_staged_query_record_state_counter:
  fixes builder s1 s2 s3 :: "'f protocol_channel"
  assumes controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < length (query_opening_budgets budgets)"
    and challenge:
      "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge builder)"
    and stage:
      "Some (chunk, s2) \<in> set_dist (execute (query_opening_stage A i raw) s1)"
    and record_out:
      "Some ((), s3) \<in> set_dist (execute (ro_record_staged_messages chunk) s2)"
  shows "PQueryCounter s3 = Suc (PQueryCounter builder)"
proof -
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have challenge_counter:
    "PQueryCounter s1 = Suc (PQueryCounter builder)"
    using receive_query_index_challenge_counter_outcome[OF challenge]
    by simp
  have stage_counter: "PQueryCounter s2 = PQueryCounter s1"
    using controlled_stage_outcome_fields[OF stage_controlled stage]
    by simp
  have record_counter: "PQueryCounter s3 = PQueryCounter s2"
    using ro_record_staged_messages_hash_extends_query_counter[OF record_out]
    by simp
  show ?thesis
    using challenge_counter stage_counter record_counter by simp
qed

lemma ro_checked_staged_query_program_verifier_rounds_sync:
  fixes builder sent verifier_state verifier_state' :: "'f protocol_channel"
    and rest :: "'f list"
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and builder_out:
      "Some (chunks, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              i n) builder)"
    and sent_ext: "sent \<le> verifier_state"
    and state_eq: "PState verifier_state = PState builder"
    and counter_eq: "PQueryCounter verifier_state = PQueryCounter builder"
    and transcript_prefix:
      "PTranscript verifier_state = List.concat chunks @ rest"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and verifier_out:
      "Some (results, verifier_state') \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              n)
            verifier_state)"
  shows
    "PState verifier_state' = PState sent \<and>
     PTranscript verifier_state' = rest \<and>
     verifier_state \<le> verifier_state' \<and>
     PQueryCounter verifier_state' = PQueryCounter builder + n"
  using bound builder_out sent_ext state_eq counter_eq transcript_prefix
    verifier_out
proof (induction n arbitrary: i chunks builder verifier_state verifier_state'
    results sent)
  case 0
  then show ?case
    by (auto intro: hash_ext_refl)
next
  case (Suc n)
  let ?round = "ro_verifier_query_round_program fr f_fl f_final as fl final"
  from Suc.prems(7) obtain verifier_mid results' where
    verifier_decomp:
      "Some ((), verifier_mid) \<in> set_dist (execute ?round verifier_state)"
    and verifier_tail:
      "Some (results', verifier_state') \<in>
        set_dist (execute (ntimes ?round n) verifier_mid)"
    and results_eq: "results = () # results'"
    by (auto elim!: set_dist_bindE)
  from ro_checked_staged_query_program_Suc_verifier_round_syncE
      [OF controlled Suc.prems(1) Suc.prems(2) Suc.prems(3)
        Suc.prems(4) Suc.prems(5) Suc.prems(6)
        trace_roots_eq composition_roots_eq verifier_decomp]
  obtain raw chunk chunks' s1 s2 s3 where
    builder_challenge:
      "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge builder)"
    and stage:
      "Some (chunk, s2) \<in> set_dist (execute (query_opening_stage A i raw) s1)"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw)) trace_roots composition_roots chunk"
    and record_out:
      "Some ((), s3) \<in> set_dist (execute (ro_record_staged_messages chunk) s2)"
    and rest_out:
      "Some (chunks', sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
    and state_mid: "PState verifier_mid = PState s3"
    and transcript_mid: "PTranscript verifier_mid = List.concat chunks' @ rest"
    and verifier_step_ext: "verifier_state \<le> verifier_mid"
    and counter_mid_builder:
      "PQueryCounter verifier_mid = Suc (PQueryCounter builder)"
    and builder_chain:
      "ro_absorb_lookup_chain sent (PState builder) chunk (PState s3)"
    .
  have tail_bound: "Suc i + n \<le> length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have counter_s3:
    "PQueryCounter s3 = Suc (PQueryCounter builder)"
    by (rule ro_checked_staged_query_record_state_counter
        [OF controlled i_bound builder_challenge stage record_out])
  have sent_ext_tail: "sent \<le> verifier_mid"
    by (rule hash_ext_trans[OF Suc.prems(3) verifier_step_ext])
  have counter_eq_tail:
    "PQueryCounter verifier_mid = PQueryCounter s3"
    using counter_mid_builder counter_s3 by simp
  have tail_sync:
    "PState verifier_state' = PState sent \<and>
     PTranscript verifier_state' = rest \<and>
     verifier_mid \<le> verifier_state' \<and>
     PQueryCounter verifier_state' = PQueryCounter s3 + n"
    by (rule Suc.IH[OF tail_bound rest_out sent_ext_tail state_mid
          counter_eq_tail transcript_mid verifier_tail])
  have verifier_tail_ext: "verifier_mid \<le> verifier_state'"
    using tail_sync by simp
  have verifier_ext: "verifier_state \<le> verifier_state'"
    by (rule hash_ext_trans[OF verifier_step_ext verifier_tail_ext])
  have counter_final:
    "PQueryCounter verifier_state' = PQueryCounter builder + Suc n"
    using tail_sync counter_s3 by simp
  show ?case
    using tail_sync verifier_ext counter_final by simp
qed

lemma ro_checked_staged_query_program_verifier_rounds_syncE:
  fixes builder sent verifier_state verifier_state' :: "'f protocol_channel"
    and rest :: "'f list"
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and builder_out:
      "Some (chunks, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              i n) builder)"
    and sent_ext: "sent \<le> verifier_state"
    and state_eq: "PState verifier_state = PState builder"
    and counter_eq: "PQueryCounter verifier_state = PQueryCounter builder"
    and transcript_prefix:
      "PTranscript verifier_state = List.concat chunks @ rest"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and verifier_out:
      "Some (results, verifier_state') \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              n)
            verifier_state)"
  obtains
    "PState verifier_state' = PState sent"
    "PTranscript verifier_state' = rest"
    "verifier_state \<le> verifier_state'"
    "PQueryCounter verifier_state' = PQueryCounter builder + n"
proof -
  have sync:
    "PState verifier_state' = PState sent \<and>
     PTranscript verifier_state' = rest \<and>
     verifier_state \<le> verifier_state' \<and>
     PQueryCounter verifier_state' = PQueryCounter builder + n"
    by (rule ro_checked_staged_query_program_verifier_rounds_sync
        [OF controlled bound builder_out sent_ext state_eq counter_eq
          transcript_prefix trace_roots_eq composition_roots_eq verifier_out])
  show ?thesis
    by (rule that) (use sync in simp_all)
qed

lemma ro_checked_staged_transcript_program_verifier_query_rounds_sync_from_query_start:
  fixes query_start sent verifier_state verifier_state' :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and transcript_out:
      "Some (data, sent) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    and query_out:
      "Some (staged_query_chunks data, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data) 0 rounds)
            query_start)"
    and query_start_ext: "query_start \<le> sent"
    and query_start_counter: "PQueryCounter query_start = 0"
    and verifier_state_def:
      "verifier_state =
        (verifier_state_from_adversary sent (staged_proof_transcript data))
          \<lparr>PState := PState query_start,
            PTranscript := List.concat (staged_query_chunks data)\<rparr>"
    and verifier_out:
      "Some (results, verifier_state') \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program
                (staged_trace_root data)
                (zip (staged_trace_fri_challenges data)
                  (staged_trace_fri_roots data))
                (staged_trace_final data)
                (staged_alphas data)
                (zip (staged_composition_fri_challenges data)
                  (staged_composition_fri_roots data))
                (staged_composition_final data))
              rounds)
            verifier_state)"
  shows
    "PState verifier_state' = PState sent \<and>
     PTranscript verifier_state' = [] \<and>
     verifier_state \<le> verifier_state' \<and>
     PQueryCounter verifier_state' = rounds"
proof -
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have shape:
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     ceil_log (to_nat (staged_degree data) + 1) \<le>
       ceil_log (maxDegree + 1) \<and>
     length (staged_query_chunks data) = rounds"
    by (rule ro_checked_staged_transcript_program_outcome_shape[OF transcript_out])
  have trace_roots_eq:
    "staged_trace_fri_roots data =
      map snd
        (zip (staged_trace_fri_challenges data)
          (staged_trace_fri_roots data))"
    using shape by simp
  have composition_roots_eq:
    "staged_composition_fri_roots data =
      map snd
        (zip (staged_composition_fri_challenges data)
          (staged_composition_fri_roots data))"
    using shape by simp
  have sent_ext: "sent \<le> verifier_state"
    unfolding verifier_state_def verifier_state_from_adversary_def
      less_eq_hash_ext_def less_eq_fmap_def
    by simp
  have state_eq: "PState verifier_state = PState query_start"
    unfolding verifier_state_def by simp
  have counter_eq: "PQueryCounter verifier_state = PQueryCounter query_start"
    using query_start_counter
    unfolding verifier_state_def verifier_state_from_adversary_def by simp
  have transcript_prefix:
    "PTranscript verifier_state = List.concat (staged_query_chunks data) @ []"
    unfolding verifier_state_def by simp
  have sync:
    "PState verifier_state' = PState sent \<and>
     PTranscript verifier_state' = [] \<and>
     verifier_state \<le> verifier_state' \<and>
     PQueryCounter verifier_state' = PQueryCounter query_start + rounds"
    by (rule ro_checked_staged_query_program_verifier_rounds_sync
        [OF controlled query_bound query_out sent_ext state_eq counter_eq
          transcript_prefix trace_roots_eq composition_roots_eq verifier_out])
  show ?thesis
    using sync query_start_counter by simp
qed

end

end
