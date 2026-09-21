(*  Title:      Stark/Staged_Security_Experiment_RO_Query_List_Event.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_RO_Query_List_Event
  imports
    Staged_Security_Experiment_RO_Event_Bridge
    Soundness_FRI_Sampled_Interface
begin

text \<open>
  Query-index-list events for the absorbing checked verifier.  This is the
  RO-facing replacement surface for legacy query-list events whose lookup path
  was phrased with @{term state_after_query_chunks}.
\<close>

context soundness
begin

definition ro_absorb_checked_staged_security_with_data_state_query_index_list_hit
  :: "nat list set \<Rightarrow>
      (((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
          'f protocol_channel) option \<Rightarrow> bool)"
where
  "ro_absorb_checked_staged_security_with_data_state_query_index_list_hit Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((data, attacker_state), _), final_state) \<Rightarrow>
        (\<exists>query_start raw_idxs query_idxs query_states.
          query_start \<le> attacker_state \<and>
          length raw_idxs = rounds \<and>
          length query_states = rounds \<and>
          query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
          query_idxs \<in> Q \<and>
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

lemma ro_absorb_checked_staged_security_with_data_state_query_index_list_hit_imp_query_witnesses:
  assumes
    "ro_absorb_checked_staged_security_with_data_state_query_index_list_hit Q out"
  shows "ro_absorb_checked_staged_security_with_data_state_query_witnesses out"
  using assms
  unfolding
    ro_absorb_checked_staged_security_with_data_state_query_index_list_hit_def
    ro_absorb_checked_staged_security_with_data_state_query_witnesses_def
  by (auto split: option.splits prod.splits)

lemma ro_absorb_checked_staged_security_with_data_state_query_index_list_hit_mono:
  assumes subset: "Q \<subseteq> Q'"
    and hit:
      "ro_absorb_checked_staged_security_with_data_state_query_index_list_hit
        Q out"
  shows
    "ro_absorb_checked_staged_security_with_data_state_query_index_list_hit
      Q' out"
  using subset hit
  unfolding
    ro_absorb_checked_staged_security_with_data_state_query_index_list_hit_def
  by (auto split: option.splits prod.splits)

lemma ro_absorb_checked_staged_security_with_data_state_query_witnesses_imp_query_index_list_space_hit:
  assumes witnesses:
    "ro_absorb_checked_staged_security_with_data_state_query_witnesses out"
  shows
    "ro_absorb_checked_staged_security_with_data_state_query_index_list_hit
      fri_query_index_list_space out"
proof (rule
    ro_absorb_checked_staged_security_with_data_state_query_witnessesE
      [OF witnesses])
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
    and state_eq: "PState final_state = PState attacker_state"
    and transcript_empty: "PTranscript final_state = []"
    and start_ext:
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data) \<le> final_state"
    and final_counter: "PQueryCounter final_state = rounds"
  have len_query_idxs: "length query_idxs = rounds"
    using query_idxs_eq len_raw by simp
  have set_query_idxs: "set query_idxs \<subseteq> query_sample_space"
  proof
    fix idx
    assume idx_in: "idx \<in> set query_idxs"
    then obtain raw where raw_in: "raw \<in> set raw_idxs"
      and idx_eq: "idx = index (to_nat raw)"
      using query_idxs_eq by auto
    show "idx \<in> query_sample_space"
      unfolding idx_eq query_sample_space_def
      using index_less_query_sample_space by simp
  qed
  have query_space: "query_idxs \<in> fri_query_index_list_space"
    unfolding fri_query_index_list_space_def
    using len_query_idxs set_query_idxs by simp
  have witness:
    "\<exists>query_start raw_idxs query_idxs query_states.
      query_start \<le> attacker_state \<and>
      length raw_idxs = rounds \<and>
      length query_states = rounds \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      query_idxs \<in> fri_query_index_list_space \<and>
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
  proof (intro exI conjI)
    show "query_start \<le> attacker_state"
      by (rule query_start_ext)
    show "length raw_idxs = rounds"
      by (rule len_raw)
    show "length query_states = rounds"
      by (rule len_states)
    show "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
      by (rule query_idxs_eq)
    show "query_idxs \<in> fri_query_index_list_space"
      by (rule query_space)
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
      by (rule state_eq)
    show "PTranscript final_state = []"
      by (rule transcript_empty)
    show "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data) \<le> final_state"
      by (rule start_ext)
    show "PQueryCounter final_state = rounds"
      by (rule final_counter)
  qed
  show
    "ro_absorb_checked_staged_security_with_data_state_query_index_list_hit
      fri_query_index_list_space out"
    unfolding
      ro_absorb_checked_staged_security_with_data_state_query_index_list_hit_def
      out_eq
    using witness by simp
qed

lemma ro_absorb_checked_staged_security_with_data_state_query_witnesses_eq_query_index_list_space_hit:
  "ro_absorb_checked_staged_security_with_data_state_query_witnesses out \<longleftrightarrow>
   ro_absorb_checked_staged_security_with_data_state_query_index_list_hit
     fri_query_index_list_space out"
  using
    ro_absorb_checked_staged_security_with_data_state_query_index_list_hit_imp_query_witnesses
    ro_absorb_checked_staged_security_with_data_state_query_witnesses_imp_query_index_list_space_hit
  by blast

lemma ro_absorb_checked_staged_security_with_data_state_acceptance_eq_query_index_list_space_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
       accepted adversary_initial_state =
     wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
       (ro_absorb_checked_staged_security_with_data_state_query_index_list_hit
         fri_query_index_list_space)
       adversary_initial_state"
  unfolding
    ro_absorb_checked_staged_security_with_data_state_query_witnesses_eq_query_index_list_space_hit[symmetric]
  by (rule
      ro_absorb_checked_staged_security_with_data_state_acceptance_eq_query_witnesses
        [OF wf controlled])

end

end
