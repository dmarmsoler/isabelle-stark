(*  Title:      Stark/Staged_Security_Experiment_RO_Query_List_Transcript_Product.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_RO_Query_List_Transcript_Product
  imports Stark.Staged_Security_Experiment_RO_Query_List_Actual_Product
begin

context soundness
begin

definition ro_checked_staged_transcript_prefix_program
  :: "'f staged_adversary \<Rightarrow>
      ('f staged_proof_data, 'f protocol_channel) state_monad"
where
  "ro_checked_staged_transcript_prefix_program A =
    do {
      fr \<leftarrow> trace_root_stage A;
      ro_record_staged_message fr;
      (trace_roots, trace_bs) \<leftarrow>
        ro_staged_trace_fri_program A 0 (ceil_log clength) [];
      trace_final \<leftarrow> trace_final_stage A trace_bs;
      ro_record_staged_message trace_final;
      as \<leftarrow> ro_staged_alpha_program (length spec);
      dg \<leftarrow> degree_stage A as;
      ro_record_staged_message dg;
      let composition_rounds = ceil_log (to_nat dg + 1);
      assert (composition_rounds \<le> ceil_log (maxDegree + 1));
      (composition_roots, composition_bs) \<leftarrow>
        ro_staged_composition_fri_program A dg 0 composition_rounds [];
      composition_final \<leftarrow> composition_final_stage A dg composition_bs;
      ro_record_staged_message composition_final;
      return
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = []\<rparr>
    }"

definition ro_checked_staged_transcript_program_with_query_witnesses
  :: "'f staged_adversary \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel \<times>
        'f list \<times> 'f protocol_channel list,
       'f protocol_channel) state_monad"
where
  "ro_checked_staged_transcript_program_with_query_witnesses A =
    do {
      data \<leftarrow> ro_checked_staged_transcript_prefix_program A;
      query_start \<leftarrow> get;
      (raws, query_states, query_chunks) \<leftarrow>
        ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds;
      return
        (data\<lparr>staged_query_chunks := query_chunks\<rparr>,
          query_start, raws, query_states)
    }"

lemma ro_checked_staged_transcript_program_prefix_decomposition:
  "ro_checked_staged_transcript_program A =
    do {
      data \<leftarrow> ro_checked_staged_transcript_prefix_program A;
      query_chunks \<leftarrow>
        ro_checked_staged_query_program A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          0 rounds;
      return (data\<lparr>staged_query_chunks := query_chunks\<rparr>)
    }"
  unfolding ro_checked_staged_transcript_program_def
    ro_checked_staged_transcript_prefix_program_def
  by (simp add: Let_def sm_bind_assoc split_def)

lemma ro_checked_staged_transcript_program_with_query_witnesses_projection:
  "ro_checked_staged_transcript_program_with_query_witnesses A \<bind>
      (\<lambda>(data, query_start, raws, query_states). return data) =
    ro_checked_staged_transcript_program A"
proof -
  have query_map:
    "\<And>(data :: 'f staged_proof_data) query_start.
      ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          return (data\<lparr>staged_query_chunks := query_chunks\<rparr>)) =
      ro_checked_staged_query_program A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          0 rounds \<bind>
        (\<lambda>query_chunks.
          return (data\<lparr>staged_query_chunks := query_chunks\<rparr>))"
  proof -
    fix data :: "'f staged_proof_data"
    fix query_start
    have
      "ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          return (data\<lparr>staged_query_chunks := query_chunks\<rparr>)) =
       (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks). return query_chunks)) \<bind>
        (\<lambda>query_chunks.
          return (data\<lparr>staged_query_chunks := query_chunks\<rparr>))"
      by (simp add: sm_bind_assoc split_def)
    also have "... =
      ro_checked_staged_query_program A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          0 rounds \<bind>
        (\<lambda>query_chunks.
          return (data\<lparr>staged_query_chunks := query_chunks\<rparr>))"
      by (simp only:
          ro_checked_staged_query_program_with_witnesses_projection)
    finally show
      "ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          return (data\<lparr>staged_query_chunks := query_chunks\<rparr>)) =
      ro_checked_staged_query_program A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          0 rounds \<bind>
        (\<lambda>query_chunks.
          return (data\<lparr>staged_query_chunks := query_chunks\<rparr>))"
      .
  qed
  have query_map':
    "\<And>(data :: 'f staged_proof_data) query_start.
      ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>x. return
          (data\<lparr>staged_query_chunks := snd (snd x)\<rparr>)) =
      ro_checked_staged_query_program A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          0 rounds \<bind>
        (\<lambda>query_chunks.
          return (data\<lparr>staged_query_chunks := query_chunks\<rparr>))"
    using query_map by (simp add: split_def)
  have get_query_map:
    "\<And>(data :: 'f staged_proof_data).
      get \<bind>
        (\<lambda>query_start.
          ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data)
              query_start 0 rounds \<bind>
            (\<lambda>x. return
              (data\<lparr>staged_query_chunks := snd (snd x)\<rparr>))) =
      ro_checked_staged_query_program A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          0 rounds \<bind>
        (\<lambda>query_chunks.
          return (data\<lparr>staged_query_chunks := query_chunks\<rparr>))"
    by (simp add: query_map' sm_bind_get_ignore)
  show ?thesis
    unfolding ro_checked_staged_transcript_program_with_query_witnesses_def
    by (simp add: sm_bind_assoc split_def get_query_map
        ro_checked_staged_transcript_program_prefix_decomposition)
qed

definition
  ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
  :: "nat list set \<Rightarrow>
      (('f staged_proof_data \<times> 'f protocol_channel \<times>
        'f list \<times> 'f protocol_channel list) \<times>
       'f protocol_channel) option \<Rightarrow> bool"
where
  "ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
      Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some ((data, query_start, raws, query_states), attacker_state) \<Rightarrow>
        ro_query_witnesses_query_index_list_fresh_hit Q
          (Some ((raws, query_states, staged_query_chunks data),
            attacker_state)))"

lemma
  ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit_None
  [simp]:
  "\<not> ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
      Q None"
  unfolding
    ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit_def
  by simp

lemma
  wp_ro_checked_staged_query_program_with_witnesses_return_transcript_fresh_bound:
  "wp_event
    (ro_checked_staged_query_program_with_witnesses A
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        s 0 rounds \<bind>
      (\<lambda>(raws, query_states, query_chunks).
        return
          (data\<lparr>staged_query_chunks := query_chunks\<rparr>,
            s, raws, query_states)))
    (ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
      Q)
    s \<le>
    nnreal (card (query_index_raw_list_preimage Q)) *
      (1 / nnreal size) ^ rounds"
proof -
  have event_map:
    "(\<lambda>out. case out of
      None \<Rightarrow>
        ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
          Q None
    | Some (p, t) \<Rightarrow>
        ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
          Q
          (Some
            ((data\<lparr>staged_query_chunks := snd (snd p)\<rparr>,
              s, fst p, fst (snd p)), t))) =
      ro_query_witnesses_query_index_list_fresh_hit Q"
    by (rule ext)
      (auto simp:
        ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit_def
        split: option.splits prod.splits)
  have
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          s 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          return
            (data\<lparr>staged_query_chunks := query_chunks\<rparr>,
              s, raws, query_states)))
      (ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
        Q)
      s =
    wp_event
      (ro_checked_staged_query_program_with_witnesses A
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        s 0 rounds)
      (ro_query_witnesses_query_index_list_fresh_hit Q)
      s"
    by (simp add: wp_event_bind_return_map split_def event_map)
  also have "... \<le>
    nnreal (card (query_index_raw_list_preimage Q)) *
      (1 / nnreal size) ^ rounds"
    by (rule
        wp_ro_checked_staged_query_program_with_witnesses_query_index_list_fresh_bound)
  finally show ?thesis .
qed

lemma
  wp_ro_checked_staged_transcript_program_with_query_witnesses_query_index_list_fresh_bound:
  "wp_event
    (ro_checked_staged_transcript_program_with_query_witnesses A)
    (ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
      Q)
    s \<le>
    nnreal (card (query_index_raw_list_preimage Q)) *
      (1 / nnreal size) ^ rounds"
  unfolding ro_checked_staged_transcript_program_with_query_witnesses_def
proof (rule wp_event_bind_bound_by_cont)
  show
    "\<not> ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
      Q None"
    by simp
next
  fix data prefix_state
  assume prefix_support:
    "Some (data, prefix_state) \<in>
      set_dist
        (execute (ro_checked_staged_transcript_prefix_program A) s)"
  show
    "wp_event
      (do {
        query_start \<leftarrow> get;
        (raws, query_states, query_chunks) \<leftarrow>
          ro_checked_staged_query_program_with_witnesses A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)
            query_start 0 rounds;
        return
          (data\<lparr>staged_query_chunks := query_chunks\<rparr>,
            query_start, raws, query_states)
      })
      (ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
        Q)
      prefix_state \<le>
      nnreal (card (query_index_raw_list_preimage Q)) *
        (1 / nnreal size) ^ rounds"
  proof (rule wp_event_bind_bound_by_cont)
    show
      "\<not> ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
        Q None"
      by simp
  next
    fix query_start query_state
    assume get_support:
      "Some (query_start, query_state) \<in>
        set_dist (execute get prefix_state)"
    have query_start_eq: "query_start = query_state"
      using get_support by simp
    show
      "wp_event
        (ro_checked_staged_query_program_with_witnesses A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)
            query_start 0 rounds \<bind>
          (\<lambda>(raws, query_states, query_chunks).
            return
              (data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                query_start, raws, query_states)))
        (ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
          Q)
        query_state \<le>
        nnreal (card (query_index_raw_list_preimage Q)) *
          (1 / nnreal size) ^ rounds"
      unfolding query_start_eq
      by (rule
          wp_ro_checked_staged_query_program_with_witnesses_return_transcript_fresh_bound)
  qed
qed

lemma ro_checked_staged_transcript_program_with_query_witnesses_outcome:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((data, query_start, raws, query_states), t) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_query_witnesses A)
            s)"
  shows
    "length raws = rounds \<and>
     length query_states = rounds \<and>
     length (staged_query_chunks data) = rounds \<and>
     query_start \<le> t \<and>
     PQueryCounter t = PQueryCounter query_start + rounds \<and>
     (\<forall>j < rounds.
       query_states ! j \<le> t \<and>
       PQueryCounter (query_states ! j) =
         PQueryCounter query_start + j \<and>
       fmlookup (HashMap t)
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
proof -
  from outcome obtain prefix_data query_chunks where
    prefix_out:
      "Some (prefix_data, query_start) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_prefix_program A) s)"
    and query_out:
      "Some ((raws, query_states, query_chunks), t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots prefix_data)
              (staged_composition_fri_roots prefix_data)
              query_start 0 rounds)
            query_start)"
    and data_eq:
      "data = prefix_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    unfolding
      ro_checked_staged_transcript_program_with_query_witnesses_def
    by (auto elim!: set_dist_bindE split: prod.splits)

  have query_bound:
    "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_result:
    "length raws = rounds \<and>
     length query_states = rounds \<and>
     length query_chunks = rounds \<and>
     query_start \<le> t \<and>
     PQueryCounter t = PQueryCounter query_start + rounds \<and>
     (\<forall>j < rounds.
       query_states ! j \<le> t \<and>
       PQueryCounter (query_states ! j) =
         PQueryCounter query_start + j \<and>
       fmlookup (HashMap t)
         (QueryIndexChallenge
           (PQueryCounter (query_states ! j))
           (PState (query_states ! j))) =
         Some (raws ! j) \<and>
       verifier_query_round_chunk
         (index (to_nat (raws ! j)))
         (staged_trace_fri_roots prefix_data)
         (staged_composition_fri_roots prefix_data)
         (query_chunks ! j)) \<and>
     (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
    by (rule
        ro_checked_staged_query_program_with_witnesses_outcome
          [OF controlled query_bound query_out])
  have len_raws: "length raws = rounds"
    using query_result by blast
  have len_states: "length query_states = rounds"
    using query_result by blast
  have len_chunks: "length query_chunks = rounds"
    using query_result by blast
  have query_start_ext: "query_start \<le> t"
    using query_result by blast
  have query_count:
    "PQueryCounter t = PQueryCounter query_start + rounds"
    using query_result by blast
  have query_props:
    "\<forall>j < rounds.
      query_states ! j \<le> t \<and>
      PQueryCounter (query_states ! j) =
        PQueryCounter query_start + j \<and>
      fmlookup (HashMap t)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raws ! j) \<and>
      verifier_query_round_chunk
        (index (to_nat (raws ! j)))
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! j)"
    proof (intro allI impI)
    fix j
    assume j_bound: "j < rounds"
    have prop_j:
      "query_states ! j \<le> t \<and>
       PQueryCounter (query_states ! j) =
         PQueryCounter query_start + j \<and>
       fmlookup (HashMap t)
         (QueryIndexChallenge
           (PQueryCounter (query_states ! j))
           (PState (query_states ! j))) =
         Some (raws ! j) \<and>
       verifier_query_round_chunk
         (index (to_nat (raws ! j)))
         (staged_trace_fri_roots prefix_data)
         (staged_composition_fri_roots prefix_data)
         (query_chunks ! j)"
      using query_result j_bound by blast
    show
      "query_states ! j \<le> t \<and>
       PQueryCounter (query_states ! j) =
         PQueryCounter query_start + j \<and>
       fmlookup (HashMap t)
         (QueryIndexChallenge
           (PQueryCounter (query_states ! j))
           (PState (query_states ! j))) =
         Some (raws ! j) \<and>
       verifier_query_round_chunk
         (index (to_nat (raws ! j)))
         (staged_trace_fri_roots data)
         (staged_composition_fri_roots data)
         (staged_query_chunks data ! j)"
    proof (intro conjI)
      show "query_states ! j \<le> t"
        using prop_j by blast
      show "PQueryCounter (query_states ! j) =
        PQueryCounter query_start + j"
        using prop_j by blast
      show
        "fmlookup (HashMap t)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raws ! j)"
        using prop_j by blast
      show
        "verifier_query_round_chunk
          (index (to_nat (raws ! j)))
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)"
        using prop_j data_eq by simp
    qed
  qed
  have raw_bound:
    "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
    using query_result by blast
  show ?thesis
  proof (intro conjI)
    show "length raws = rounds"
      by (rule len_raws)
    show "length query_states = rounds"
      by (rule len_states)
    show "length (staged_query_chunks data) = rounds"
      using len_chunks data_eq by simp
    show "query_start \<le> t"
      by (rule query_start_ext)
    show "PQueryCounter t = PQueryCounter query_start + rounds"
      by (rule query_count)
    show
      "\<forall>j<rounds.
        query_states ! j \<le> t \<and>
        PQueryCounter (query_states ! j) =
          PQueryCounter query_start + j \<and>
        fmlookup (HashMap t)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raws ! j) \<and>
        verifier_query_round_chunk
          (index (to_nat (raws ! j)))
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)"
      by (rule query_props)
    show "\<forall>raw\<in>set raws. index (to_nat raw) < clength * scale"
      by (rule raw_bound)
  qed
qed

end

end
