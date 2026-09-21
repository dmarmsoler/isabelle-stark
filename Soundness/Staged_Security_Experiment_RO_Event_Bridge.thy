theory Staged_Security_Experiment_RO_Event_Bridge
  imports Staged_Security_Experiment_RO_Verify_Header_Replay
begin

context soundness
begin

text \<open>
  Route-facing support predicates for the absorbing checked verifier.  These
  package the actual RO query-state witnesses exported by the checked builder,
  instead of reusing the legacy deterministic
  @{term state_after_query_chunks} model.
\<close>

definition ro_absorb_checked_staged_security_with_data_state_query_witnesses ::
  "((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
      'f protocol_channel) option \<Rightarrow> bool"
where
  "ro_absorb_checked_staged_security_with_data_state_query_witnesses out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((data, attacker_state), _), final_state) \<Rightarrow>
        (\<exists>query_start raw_idxs query_idxs query_states.
          query_start \<le> attacker_state \<and>
          length raw_idxs = rounds \<and>
          length query_states = rounds \<and>
          query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
          length (staged_query_chunks data) = rounds \<and>
          PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
          (\<forall>j < rounds.
            query_states ! j \<le> attacker_state \<and>
            PQueryCounter (query_states ! j) =
              PQueryCounter query_start + j \<and>
            fmlookup (HashMap attacker_state)
              (QueryIndexChallenge
                (PQueryCounter (query_states ! j))
                (PState (query_states ! j))) =
              Some (raw_idxs ! j) \<and>
            verifier_query_round_chunk (query_idxs ! j)
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data)
              (staged_query_chunks data ! j)) \<and>
          (\<forall>idx \<in> set query_idxs. idx < clength * scale) \<and>
          PState final_state = PState attacker_state \<and>
          PTranscript final_state = [] \<and>
          verifier_state_from_adversary attacker_state
            (staged_proof_transcript data) \<le> final_state \<and>
          PQueryCounter final_state = rounds))"

lemma ro_absorb_checked_staged_security_with_data_state_query_witnessesE:
  assumes
    "ro_absorb_checked_staged_security_with_data_state_query_witnesses out"
  obtains data attacker_state result final_state query_start raw_idxs query_idxs
      query_states where
    "out = Some (((data, attacker_state), result), final_state)"
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
    "PState final_state = PState attacker_state"
    "PTranscript final_state = []"
    "verifier_state_from_adversary attacker_state
       (staged_proof_transcript data) \<le> final_state"
    "PQueryCounter final_state = rounds"
proof (cases out)
  case None
  with assms show ?thesis
    unfolding ro_absorb_checked_staged_security_with_data_state_query_witnesses_def
    by simp
next
  case (Some z)
  obtain data_attacker result final_state where z_eq:
    "z = ((data_attacker, result), final_state)"
    by (cases z) auto
  obtain data attacker_state where data_attacker_eq:
    "data_attacker = (data, attacker_state)"
    by (cases data_attacker) auto
  have witness:
    "\<exists>query_start raw_idxs query_idxs query_states.
      query_start \<le> attacker_state \<and>
      length raw_idxs = rounds \<and>
      length query_states = rounds \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length (staged_query_chunks data) = rounds \<and>
      PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
      (\<forall>j < rounds.
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
          (staged_query_chunks data ! j)) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale) \<and>
      PState final_state = PState attacker_state \<and>
      PTranscript final_state = [] \<and>
      verifier_state_from_adversary attacker_state
        (staged_proof_transcript data) \<le> final_state \<and>
      PQueryCounter final_state = rounds"
    using assms Some z_eq data_attacker_eq
    unfolding ro_absorb_checked_staged_security_with_data_state_query_witnesses_def
    by simp
  from witness obtain query_start raw_idxs query_idxs query_states where
    query_start_ext: "query_start \<le> attacker_state"
    and len_raw: "length raw_idxs = rounds"
    and len_states: "length query_states = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length (staged_query_chunks data) = rounds"
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
    and state_eq: "PState final_state = PState attacker_state"
    and transcript_empty: "PTranscript final_state = []"
    and start_ext:
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data) \<le> final_state"
    and final_counter: "PQueryCounter final_state = rounds"
    by blast
  have out_eq: "out = Some (((data, attacker_state), result), final_state)"
    using Some z_eq data_attacker_eq by simp
  show ?thesis
    by (rule that[OF out_eq query_start_ext len_raw len_states
          query_idxs_eq len_chunks query_count query_props idx_bound state_eq
          transcript_empty start_ext final_counter])
qed

lemma ro_absorb_checked_staged_security_with_data_state_accepted_query_witnesses_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and accepted: "accepted out"
  shows "ro_absorb_checked_staged_security_with_data_state_query_witnesses out"
proof (rule ro_absorb_checked_staged_security_experiment_with_data_state_accepted_query_witnessesE
    [OF wf controlled outcome accepted])
  fix data attacker_state result final_state query_start raw_idxs query_idxs
      query_states
  assume out_eq: "out = Some (((data, attacker_state), result), final_state)"
    and query_start_ext: "query_start \<le> attacker_state"
    and len_raw: "length raw_idxs = rounds"
    and len_states: "length query_states = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length (staged_query_chunks data) = rounds"
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
    and sync:
      "PState final_state = PState attacker_state \<and>
       PTranscript final_state = [] \<and>
       verifier_state_from_adversary attacker_state
         (staged_proof_transcript data) \<le> final_state \<and>
       PQueryCounter final_state = rounds"
  have body:
    "query_start \<le> attacker_state \<and>
     length raw_idxs = rounds \<and>
     length query_states = rounds \<and>
     query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
     length (staged_query_chunks data) = rounds \<and>
     PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
     (\<forall>j < rounds.
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
         (staged_query_chunks data ! j)) \<and>
     (\<forall>idx \<in> set query_idxs. idx < clength * scale) \<and>
     PState final_state = PState attacker_state \<and>
     PTranscript final_state = [] \<and>
     verifier_state_from_adversary attacker_state
       (staged_proof_transcript data) \<le> final_state \<and>
     PQueryCounter final_state = rounds"
  proof (intro conjI)
    show "query_start \<le> attacker_state"
      by (rule query_start_ext)
    show "length raw_idxs = rounds"
      by (rule len_raw)
    show "length query_states = rounds"
      by (rule len_states)
    show "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
      by (rule query_idxs_eq)
    show "length (staged_query_chunks data) = rounds"
      by (rule len_chunks)
    show "PQueryCounter attacker_state = PQueryCounter query_start + rounds"
      by (rule query_count)
    show "\<forall>j < rounds.
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
      by (rule query_props)
    show "\<forall>idx \<in> set query_idxs. idx < clength * scale"
      by (rule idx_bound)
    show "PState final_state = PState attacker_state"
      using sync by simp
    show "PTranscript final_state = []"
      using sync by simp
    show "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data) \<le> final_state"
      using sync by simp
    show "PQueryCounter final_state = rounds"
      using sync by simp
  qed
  then have witness:
    "\<exists>query_start raw_idxs query_idxs query_states.
      query_start \<le> attacker_state \<and>
      length raw_idxs = rounds \<and>
      length query_states = rounds \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length (staged_query_chunks data) = rounds \<and>
      PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
      (\<forall>j < rounds.
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
          (staged_query_chunks data ! j)) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale) \<and>
      PState final_state = PState attacker_state \<and>
      PTranscript final_state = [] \<and>
      verifier_state_from_adversary attacker_state
        (staged_proof_transcript data) \<le> final_state \<and>
      PQueryCounter final_state = rounds"
    by blast
  then show ?thesis
    unfolding ro_absorb_checked_staged_security_with_data_state_query_witnesses_def
      out_eq
    by simp
qed

lemma ro_absorb_checked_staged_security_with_data_state_acceptance_le_query_witnesses:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
       accepted adversary_initial_state \<le>
     wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
       ro_absorb_checked_staged_security_with_data_state_query_witnesses
       adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume out_support:
    "out \<in> set_dist
      (execute
        (ro_absorb_checked_staged_security_experiment_with_data_state A)
        adversary_initial_state)"
    and out_accepted: "accepted out"
  show "ro_absorb_checked_staged_security_with_data_state_query_witnesses out"
    by (rule ro_absorb_checked_staged_security_with_data_state_accepted_query_witnesses_on_support
        [OF wf controlled out_support out_accepted])
qed


lemma ro_absorb_checked_staged_security_with_data_state_query_witnesses_imp_accepted:
  assumes
    "ro_absorb_checked_staged_security_with_data_state_query_witnesses out"
  shows "accepted out"
  using assms
  unfolding ro_absorb_checked_staged_security_with_data_state_query_witnesses_def
    accepted_def
  by (cases out) (auto split: prod.splits)

lemma ro_absorb_checked_staged_security_with_data_state_query_witnesses_le_acceptance:
  "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
     ro_absorb_checked_staged_security_with_data_state_query_witnesses
     adversary_initial_state \<le>
   wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
     accepted adversary_initial_state"
  by (rule wp_event_mono)
    (rule ro_absorb_checked_staged_security_with_data_state_query_witnesses_imp_accepted)

lemma ro_absorb_checked_staged_security_with_data_state_acceptance_eq_query_witnesses:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
       accepted adversary_initial_state =
     wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
       ro_absorb_checked_staged_security_with_data_state_query_witnesses
       adversary_initial_state"
  by (rule order_antisym)
    (rule ro_absorb_checked_staged_security_with_data_state_acceptance_le_query_witnesses
      [OF wf controlled],
     rule ro_absorb_checked_staged_security_with_data_state_query_witnesses_le_acceptance)
end

end
