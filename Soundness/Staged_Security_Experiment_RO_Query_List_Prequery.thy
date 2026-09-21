(*  Title:      Stark/Staged_Security_Experiment_RO_Query_List_Prequery.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_RO_Query_List_Prequery
  imports
    Staged_Security_Experiment_RO_Query_List_Event
    Soundness_FRI_Query_List_Prequery
begin

text \<open>
  RO-native prequery accounting for query-index-list events.  This layer keeps
  the query keys phrased in terms of the actual absorbing-route query states,
  not @{term state_after_query_chunks}.
\<close>

context soundness
begin

definition ro_absorb_checked_query_index_list_relation
  :: "'f staged_adversary \<Rightarrow> nat list set \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "ro_absorb_checked_query_index_list_relation A Q x y \<longleftrightarrow>
    (\<exists>out data attacker_state result final_state query_start raw_idxs
        query_idxs query_states j.
      out \<in>
        set_dist
          (execute (ro_absorb_checked_staged_security_experiment_with_data_state A)
            adversary_initial_state) \<and>
      out = Some (((data, attacker_state), result), final_state) \<and>
      query_start \<le> attacker_state \<and>
      length raw_idxs = rounds \<and>
      length query_states = rounds \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      query_idxs \<in> Q \<and>
      length (staged_query_chunks data) = rounds \<and>
      PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
      j < rounds \<and>
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
        (staged_query_chunks data ! j) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale) \<and>
      PState final_state = PState attacker_state \<and>
      PTranscript final_state = [] \<and>
      verifier_state_from_adversary attacker_state
        (staged_proof_transcript data) \<le> final_state \<and>
      PQueryCounter final_state = rounds \<and>
      x = QueryIndexChallenge
        (PQueryCounter (query_states ! j))
        (PState (query_states ! j)) \<and>
      y = raw_idxs ! j)"

lemma ro_absorb_checked_query_index_list_relation_fiber_card_bound:
  "card {y. ro_absorb_checked_query_index_list_relation A Q x y} \<le>
    query_index_raw_list_relation_fiber_bound Q"
proof -
  let ?values =
    "(\<Union>i < rounds. query_index_raw_list_position_values Q i)"
  have subset:
    "{y. ro_absorb_checked_query_index_list_relation A Q x y} \<subseteq> ?values"
    unfolding ro_absorb_checked_query_index_list_relation_def
      query_index_raw_list_position_values_def
      query_index_raw_list_preimage_def
    by blast
  have finite_values: "finite ?values"
    by simp
  have "card {y. ro_absorb_checked_query_index_list_relation A Q x y}
      \<le> card ?values"
    by (rule card_mono[OF finite_values subset])
  also have "... \<le>
      (\<Sum>i < rounds. card (query_index_raw_list_position_values Q i))"
    by (rule card_UN_le) simp
  also have "... = query_index_raw_list_relation_fiber_bound Q"
    unfolding query_index_raw_list_relation_fiber_bound_def by simp
  finally show ?thesis .
qed

definition ro_checked_staged_transcript_query_index_list_fresh_hit
  :: "nat list set \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
where
  "ro_checked_staged_transcript_query_index_list_fresh_hit Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (data, attacker_state) \<Rightarrow>
        (\<exists>query_start raw_idxs query_states.
          query_start \<le> attacker_state \<and>
          length raw_idxs = rounds \<and>
          length query_states = rounds \<and>
          map (\<lambda>raw. index (to_nat raw)) raw_idxs \<in> Q \<and>
          length (staged_query_chunks data) = rounds \<and>
          PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
          (\<forall>j < rounds.
            query_states ! j \<le> attacker_state \<and>
            PQueryCounter (query_states ! j) =
              PQueryCounter query_start + j \<and>
            fmlookup (HashMap (query_states ! j))
              (QueryIndexChallenge
                (PQueryCounter (query_states ! j))
                (PState (query_states ! j))) = None \<and>
            fmlookup (HashMap attacker_state)
              (QueryIndexChallenge
                (PQueryCounter (query_states ! j))
                (PState (query_states ! j))) =
              Some (raw_idxs ! j) \<and>
            verifier_query_round_chunk (index (to_nat (raw_idxs ! j)))
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data)
              (staged_query_chunks data ! j)) \<and>
          (\<forall>raw \<in> set raw_idxs. index (to_nat raw) < clength * scale)))"

definition ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit
  :: "nat list set \<Rightarrow>
      (((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
          'f protocol_channel) option \<Rightarrow> bool)"
where
  "ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit Q out \<longleftrightarrow>
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
            fmlookup (HashMap (query_states ! j))
              (QueryIndexChallenge
                (PQueryCounter (query_states ! j))
                (PState (query_states ! j))) = None \<and>
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

definition ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit
  :: "'f staged_adversary \<Rightarrow> nat list set \<Rightarrow>
      (((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
          'f protocol_channel) option \<Rightarrow> bool)"
where
  "ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit A Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((_, attacker_state), _), _) \<Rightarrow>
        hash_relation_hit
          (ro_absorb_checked_query_index_list_relation A Q)
          adversary_initial_state attacker_state)"

lemma ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
      (ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit A Q)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (ro_checked_staged_transcript_hash_query_budget_for budgets)"
proof -
  let ?R = "ro_absorb_checked_query_index_list_relation A Q"
  let ?B = "query_index_raw_list_relation_fiber_bound Q"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have program:
    "hash_relation_program ?R ?B ?q
      (ro_checked_staged_transcript_program A)"
    by (rule hash_relation_program_ro_checked_staged_transcript_program
        [OF wf controlled])
      (rule ro_absorb_checked_query_index_list_relation_fiber_card_bound)
  have head_bound:
    "wp_event (ro_checked_staged_transcript_program A)
      (hash_relation_hit_event ?R adversary_initial_state)
      adversary_initial_state \<le> hash_relation_budget_value ?B ?q"
    using program unfolding hash_relation_program_def hash_relation_budget_def
    by blast
  show ?thesis
    unfolding ro_absorb_checked_staged_security_experiment_with_data_state_def
  proof (rule wp_event_bind_bound_by_head_event[OF head_bound])
    show "ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit A Q None \<Longrightarrow>
      hash_relation_hit_event ?R adversary_initial_state None"
      unfolding
        ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit_def
        hash_relation_hit_event_def
      by simp
  next
    fix data attacker_state out
    assume out_support:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>s. put
                (verifier_state_from_adversary s
                  (staged_proof_transcript data)) \<bind>
                (\<lambda>_. ro_verify_monad \<bind>
                  (\<lambda>result. return ((data, s), result)))))
            attacker_state)"
      and prequery:
        "ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit A Q out"
    show "hash_relation_hit_event ?R adversary_initial_state
        (Some (data, attacker_state))"
      using out_support prequery
      unfolding
        ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit_def
        hash_relation_hit_event_def
      by (auto simp: wpsimps elim!: set_dist_bindE split: option.splits prod.splits)
  qed
qed

lemma ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_bound_from_transcript:
  "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
      (ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit Q)
      adversary_initial_state \<le>
    wp_event (ro_checked_staged_transcript_program A)
      (ro_checked_staged_transcript_query_index_list_fresh_hit Q)
      adversary_initial_state"
  unfolding ro_absorb_checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_head_event)
  show "wp_event (ro_checked_staged_transcript_program A)
      (ro_checked_staged_transcript_query_index_list_fresh_hit Q)
      adversary_initial_state
      \<le> wp_event (ro_checked_staged_transcript_program A)
        (ro_checked_staged_transcript_query_index_list_fresh_hit Q)
        adversary_initial_state"
    by simp
next
  show "ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit Q None \<Longrightarrow>
    ro_checked_staged_transcript_query_index_list_fresh_hit Q None"
    unfolding
      ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit_def
      ro_checked_staged_transcript_query_index_list_fresh_hit_def
    by simp
next
  fix data attacker_state out
  assume out_support:
    "out \<in>
      set_dist
        (execute
          (get \<bind>
            (\<lambda>s. put
              (verifier_state_from_adversary s
                (staged_proof_transcript data)) \<bind>
              (\<lambda>_. ro_verify_monad \<bind>
                (\<lambda>result. return ((data, s), result)))))
          attacker_state)"
    and fresh:
      "ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit Q out"
  show "ro_checked_staged_transcript_query_index_list_fresh_hit Q
      (Some (data, attacker_state))"
  proof (cases out)
    case None
    then show ?thesis
      using fresh
      unfolding
        ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit_def
      by simp
  next
    case (Some full)
    then obtain saved_data saved_attacker result final_state where out_eq:
      "out = Some (((saved_data, saved_attacker), result), final_state)"
      by (cases full) (auto split: prod.splits)
    have saved_eq: "saved_data = data \<and> saved_attacker = attacker_state"
      using out_support
      unfolding out_eq
      by (auto simp: wpsimps elim!: set_dist_bindE
          split: option.splits prod.splits)
    have full_fresh_exact:
      "\<exists>query_start raw_idxs query_idxs query_states.
        query_start \<le> saved_attacker \<and>
        length raw_idxs = rounds \<and>
        length query_states = rounds \<and>
        query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
        query_idxs \<in> Q \<and>
        length (staged_query_chunks saved_data) = rounds \<and>
        PQueryCounter saved_attacker = PQueryCounter query_start + rounds \<and>
        (\<forall>j < rounds.
          query_states ! j \<le> saved_attacker \<and>
          PQueryCounter (query_states ! j) =
            PQueryCounter query_start + j \<and>
          fmlookup (HashMap (query_states ! j))
            (QueryIndexChallenge
              (PQueryCounter (query_states ! j))
              (PState (query_states ! j))) = None \<and>
          fmlookup (HashMap saved_attacker)
            (QueryIndexChallenge
              (PQueryCounter (query_states ! j))
              (PState (query_states ! j))) =
            Some (raw_idxs ! j) \<and>
          verifier_query_round_chunk (query_idxs ! j)
            (staged_trace_fri_roots saved_data)
            (staged_composition_fri_roots saved_data)
            (staged_query_chunks saved_data ! j)) \<and>
        (\<forall>idx \<in> set query_idxs. idx < clength * scale) \<and>
        PState final_state = PState saved_attacker \<and>
        PTranscript final_state = [] \<and>
        verifier_state_from_adversary saved_attacker
          (staged_proof_transcript saved_data) \<le> final_state \<and>
        PQueryCounter final_state = rounds"
      using fresh
      unfolding out_eq
        ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit_def
      by simp
    from full_fresh_exact obtain query_start raw_idxs query_idxs query_states where
      query_start_ext: "query_start \<le> saved_attacker"
      and len_raw: "length raw_idxs = rounds"
      and len_states: "length query_states = rounds"
      and query_idxs_eq:
        "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
      and query_in: "query_idxs \<in> Q"
      and len_chunks: "length (staged_query_chunks saved_data) = rounds"
      and query_count:
        "PQueryCounter saved_attacker =
          PQueryCounter query_start + rounds"
      and query_props:
        "\<forall>j < rounds.
          query_states ! j \<le> saved_attacker \<and>
          PQueryCounter (query_states ! j) =
            PQueryCounter query_start + j \<and>
          fmlookup (HashMap (query_states ! j))
            (QueryIndexChallenge
              (PQueryCounter (query_states ! j))
              (PState (query_states ! j))) = None \<and>
          fmlookup (HashMap saved_attacker)
            (QueryIndexChallenge
              (PQueryCounter (query_states ! j))
              (PState (query_states ! j))) =
            Some (raw_idxs ! j) \<and>
          verifier_query_round_chunk (query_idxs ! j)
            (staged_trace_fri_roots saved_data)
            (staged_composition_fri_roots saved_data)
            (staged_query_chunks saved_data ! j)"
      and idx_bound: "\<forall>idx \<in> set query_idxs. idx < clength * scale"
      by blast
    have query_in_raw:
      "map (\<lambda>raw. index (to_nat raw)) raw_idxs \<in> Q"
      using query_idxs_eq query_in by simp
    have witness_ex:
      "\<exists>query_start raw_idxs query_states.
        query_start \<le> attacker_state \<and>
        length raw_idxs = rounds \<and>
        length query_states = rounds \<and>
        map (\<lambda>raw. index (to_nat raw)) raw_idxs \<in> Q \<and>
        length (staged_query_chunks data) = rounds \<and>
        PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
        (\<forall>j < rounds.
          query_states ! j \<le> attacker_state \<and>
          PQueryCounter (query_states ! j) =
            PQueryCounter query_start + j \<and>
          fmlookup (HashMap (query_states ! j))
            (QueryIndexChallenge
              (PQueryCounter (query_states ! j))
              (PState (query_states ! j))) = None \<and>
          fmlookup (HashMap attacker_state)
            (QueryIndexChallenge
              (PQueryCounter (query_states ! j))
              (PState (query_states ! j))) =
            Some (raw_idxs ! j) \<and>
          verifier_query_round_chunk (index (to_nat (raw_idxs ! j)))
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)
            (staged_query_chunks data ! j)) \<and>
        (\<forall>raw \<in> set raw_idxs. index (to_nat raw) < clength * scale)"
      by (intro exI[of _ query_start] exI[of _ raw_idxs]
          exI[of _ query_states] conjI)
        (use saved_eq query_start_ext len_raw len_states query_idxs_eq
          query_in len_chunks query_count query_props idx_bound in auto)
    show ?thesis
      unfolding ro_checked_staged_transcript_query_index_list_fresh_hit_def
      using witness_ex by simp
  qed
qed

lemma ro_absorb_checked_staged_security_with_data_state_query_index_list_hit_imp_fresh_or_prequery:
  assumes support:
    "out \<in>
      set_dist
        (execute (ro_absorb_checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    and hit:
      "ro_absorb_checked_staged_security_with_data_state_query_index_list_hit
        Q out"
  shows
    "ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit
        Q out \<or>
     ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit
        A Q out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      ro_absorb_checked_staged_security_with_data_state_query_index_list_hit_def
    by simp
next
  case (Some full)
  then obtain data attacker_state result final_state where out_eq:
    "out = Some (((data, attacker_state), result), final_state)"
    by (cases full) (auto split: prod.splits)
  have witness_ex:
    "\<exists>query_start raw_idxs query_idxs query_states.
      query_start \<le> attacker_state \<and>
      length raw_idxs = rounds \<and>
      length query_states = rounds \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      query_idxs \<in> Q \<and>
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
    using hit
    unfolding out_eq
      ro_absorb_checked_staged_security_with_data_state_query_index_list_hit_def
    by simp
  from witness_ex obtain query_start raw_idxs query_idxs query_states where
    query_start_ext: "query_start \<le> attacker_state"
    and len_raw: "length raw_idxs = rounds"
    and len_states: "length query_states = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and query_in: "query_idxs \<in> Q"
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
  show ?thesis
  proof (cases
      "\<forall>j < rounds.
        fmlookup (HashMap (query_states ! j))
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) = None")
    case True
    have fresh_witness:
      "\<exists>query_start raw_idxs query_idxs query_states.
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
          fmlookup (HashMap (query_states ! j))
            (QueryIndexChallenge
              (PQueryCounter (query_states ! j))
              (PState (query_states ! j))) = None \<and>
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
      by (intro exI[of _ query_start] exI[of _ raw_idxs]
          exI[of _ query_idxs] exI[of _ query_states] conjI)
        (use query_start_ext len_raw len_states query_idxs_eq query_in
          len_chunks query_count query_props True idx_bound state_eq
          transcript_empty start_ext final_counter in auto)
    show ?thesis
      unfolding
        ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit_def
        out_eq
      using fresh_witness by simp
  next
    case False
    then obtain j where j_bound: "j < rounds"
      and lookup_not_none:
        "fmlookup (HashMap (query_states ! j))
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) \<noteq> None"
      by blast
    let ?key =
      "QueryIndexChallenge
        (PQueryCounter (query_states ! j))
        (PState (query_states ! j))"
    obtain old_raw where lookup_query_state:
      "fmlookup (HashMap (query_states ! j)) ?key = Some old_raw"
      using lookup_not_none by (cases
        "fmlookup (HashMap (query_states ! j)) ?key") auto
    have query_state_ext: "query_states ! j \<le> attacker_state"
      using query_props j_bound by blast
    have lookup_attacker:
      "fmlookup (HashMap attacker_state) ?key = Some (raw_idxs ! j)"
      using query_props j_bound by blast
    have old_raw_eq: "old_raw = raw_idxs ! j"
    proof -
      have "fmlookup (HashMap attacker_state) ?key = Some old_raw"
        by (rule hash_extension_lookup
            [OF lookup_query_state query_state_ext])
      then show ?thesis
        using lookup_attacker by simp
    qed
    have raw_in: "raw_idxs \<in> query_index_raw_list_preimage Q"
      unfolding query_index_raw_list_preimage_def
      using len_raw query_idxs_eq query_in by blast
    have rel:
      "ro_absorb_checked_query_index_list_relation A Q ?key (raw_idxs ! j)"
      unfolding ro_absorb_checked_query_index_list_relation_def
      by (intro exI[of _ out] exI[of _ data] exI[of _ attacker_state]
          exI[of _ result] exI[of _ final_state]
          exI[of _ query_start] exI[of _ raw_idxs]
          exI[of _ query_idxs] exI[of _ query_states]
          exI[of _ j] conjI)
        (use support out_eq query_start_ext len_raw len_states query_idxs_eq
          query_in len_chunks query_count j_bound query_props idx_bound
          state_eq transcript_empty start_ext final_counter in auto)
    have initial_none:
      "fmlookup (HashMap adversary_initial_state) ?key = None"
      by (simp add: adversary_initial_state_def)
    have rel_hit:
      "hash_relation_hit
        (ro_absorb_checked_query_index_list_relation A Q)
        adversary_initial_state attacker_state"
      unfolding hash_relation_hit_def
      by (intro exI[of _ ?key] exI[of _ "raw_idxs ! j"] conjI)
        (use initial_none lookup_attacker rel in simp_all)
    show ?thesis
      unfolding
        ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit_def
        out_eq
      using rel_hit by simp
  qed
qed

lemma ro_absorb_checked_staged_security_with_data_state_query_index_list_hit_bound_from_fresh:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fresh_bound:
      "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
        (ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit Q)
        adversary_initial_state \<le> F"
  shows
    "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
      (ro_absorb_checked_staged_security_with_data_state_query_index_list_hit Q)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (ro_checked_staged_transcript_hash_query_budget_for budgets)"
proof -
  have split:
    "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
      (ro_absorb_checked_staged_security_with_data_state_query_index_list_hit Q)
      adversary_initial_state \<le>
     wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit Q out \<or>
        ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit A Q out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (ro_absorb_checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
        "ro_absorb_checked_staged_security_with_data_state_query_index_list_hit Q out"
    show
      "ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit Q out \<or>
       ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit A Q out"
      by (rule
          ro_absorb_checked_staged_security_with_data_state_query_index_list_hit_imp_fresh_or_prequery
          [OF support hit])
  qed
  also have "... \<le>
      wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
        (ro_absorb_checked_staged_security_with_data_state_query_index_list_fresh_hit Q)
        adversary_initial_state +
      wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
        (ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit A Q)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      F +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (ro_checked_staged_transcript_hash_query_budget_for budgets)"
    by (rule add_mono)
      (rule fresh_bound,
       rule ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_bound
        [OF wf controlled])
  finally show ?thesis .
qed

end

end
