(*  Title:      Stark/Soundness_FRI_First_Root_RO_Actual_Agreement.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Actual_Agreement
  imports Soundness_FRI_First_Root_RO_Authenticated_Openings
begin

context soundness
begin

lemma ro_checked_staged_query_program_with_witnesses_projection_outcome:
  assumes outcome:
    "Some ((raws, query_states, chunks), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program_with_witnesses A trace_roots
            composition_roots s i n)
          s)"
  shows
    "Some (chunks, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots
            composition_roots i n)
          s)"
proof -
  have mapped:
    "Some (chunks, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots s i n \<bind>
            (\<lambda>(raws, query_states, chunks). return chunks))
          s)"
    by (rule set_dist_bindI[OF outcome]) simp
  show ?thesis
    using mapped
      ro_checked_staged_query_program_with_witnesses_projection[
        of A trace_roots composition_roots s i n]
    by simp
qed

lemma ro_checked_staged_query_program_Suc_verifier_round_sync_lookupE:
  fixes builder sent verifier_state verifier_state' :: "'f protocol_channel"
    and rest :: "'f list"
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
    and transcript_prefix:
      "PTranscript verifier_state = List.concat chunks @ rest"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and verifier_out:
      "Some ((), verifier_state') \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            verifier_state)"
  obtains raw chunk chunks' s1 s2 s3 where
    "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge builder)"
    "Some (chunk, s2) \<in> set_dist (execute (query_opening_stage A i raw) s1)"
    "verifier_query_round_chunk (index (to_nat raw)) trace_roots composition_roots chunk"
    "Some ((), s3) \<in> set_dist (execute (ro_record_staged_messages chunk) s2)"
    "Some (chunks', sent) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots composition_roots
            (Suc i) n) s3)"
    "chunks = chunk # chunks'"
    "PState verifier_state' = PState s3"
    "PTranscript verifier_state' = List.concat chunks' @ rest"
    "verifier_state \<le> verifier_state'"
    "PQueryCounter verifier_state' = Suc (PQueryCounter builder)"
    "ro_absorb_lookup_chain sent (PState builder) chunk (PState s3)"
    "fmlookup (HashMap sent)
      (QueryIndexChallenge (PQueryCounter builder) (PState builder)) = Some raw"
proof -
  from ro_checked_staged_query_program_Suc_verifier_round_syncE[
      OF controlled bound builder_out sent_ext state_eq counter_eq
        transcript_prefix trace_roots_eq composition_roots_eq verifier_out]
  obtain raw chunk chunks' s1 s2 s3 where
    challenge:
      "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge builder)"
    and stage:
      "Some (chunk, s2) \<in> set_dist (execute (query_opening_stage A i raw) s1)"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and record_out:
      "Some ((), s3) \<in> set_dist (execute (ro_record_staged_messages chunk) s2)"
    and tail:
      "Some (chunks', sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
    and state_mid: "PState verifier_state' = PState s3"
    and transcript_mid:
      "PTranscript verifier_state' = List.concat chunks' @ rest"
    and verifier_ext: "verifier_state \<le> verifier_state'"
    and counter_mid:
      "PQueryCounter verifier_state' = Suc (PQueryCounter builder)"
    and head_chain:
      "ro_absorb_lookup_chain sent (PState builder) chunk (PState s3)"
    .
  have i_bound: "i < length (query_opening_budgets budgets)"
    using bound by simp
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have challenge_props:
    "builder \<le> s1 \<and>
      PState s1 = PState builder \<and>
      PTranscript s1 = PTranscript builder \<and>
      fmlookup (HashMap s1)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some raw"
    by (rule receive_query_index_challenge_outcome[OF challenge])
  have stage_ext: "s1 \<le> s2"
    using controlled_ro_program_extension[OF stage_controlled] stage
    unfolding hash_extension_preserving_def by blast
  have record_out_ext: "s2 \<le> s3"
    using ro_record_staged_messages_hash_extends_query_counter[OF record_out]
    by simp
  have tail_bound:
    "Suc i + n \<le> length (query_opening_budgets budgets)"
    using bound by simp
  have tail_ext: "s3 \<le> sent"
    using ro_checked_staged_query_program_absorb_lookup_chain[
      OF controlled tail_bound tail]
    by simp
  have s1_sent: "s1 \<le> sent"
    by (rule hash_ext_trans[OF stage_ext])
      (rule hash_ext_trans[OF record_out_ext tail_ext])
  have recorded:
    "fmlookup (HashMap sent)
      (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
      Some raw"
    by (rule hash_extension_lookup)
      (use challenge_props s1_sent in simp_all)
  show ?thesis
    by (rule that[OF challenge stage chunk_shape record_out tail chunks_eq
          state_mid transcript_mid verifier_ext counter_mid head_chain recorded])
qed

lemma ro_checked_staged_query_program_with_witnesses_verifier_authenticated_openings:
  fixes builder sent verifier_state verifier_final :: "'f protocol_channel"
    and rest :: "'f list"
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and builder_out:
      "Some ((raws, query_states, chunks), sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots builder i n)
            builder)"
    and sent_ext: "sent \<le> verifier_state"
    and state_eq: "PState verifier_state = PState builder"
    and counter_eq: "PQueryCounter verifier_state = PQueryCounter builder"
    and transcript_prefix:
      "PTranscript verifier_state = List.concat chunks @ rest"
    and f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and verifier_out:
      "Some (results, verifier_final) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              n)
            verifier_state)"
  shows
    "\<exists>trace_openings_at first_openings_at.
      verifier_state \<le> verifier_final \<and>
      length raws = n \<and>
      length query_states = n \<and>
      length chunks = n \<and>
      (\<forall>j < n.
        map opening_index (trace_openings_at j) =
          powers_scaled (index (to_nat (raws ! j))) \<and>
        partial_authenticated_table fr (scale * clength)
          (trace_openings_at j) verifier_final \<and>
        map opening_index (first_openings_at j) =
          [index (to_nat (raws ! j)),
            fri_sibling_index (scale * clength)
              (index (to_nat (raws ! j)))] \<and>
        partial_authenticated_table rt (scale * clength)
          (first_openings_at j) verifier_final \<and>
        opening_value (trace_openings_at j ! 0) =
          opening_value (first_openings_at j ! 0))"
  using bound builder_out sent_ext state_eq counter_eq transcript_prefix verifier_out
proof (induction n arbitrary: i builder sent verifier_state verifier_final
    raws query_states chunks results)
  case 0
  then show ?case
    by (intro exI[of _ "\<lambda>_. []"] exI[of _ "\<lambda>_. []"])
      (auto intro: hash_ext_refl)
next
  case (Suc n)
  let ?round =
    "ro_verifier_query_round_program fr f_fl f_final as fl final"
  from Suc.prems(2)
  obtain witness_raw witness_chunk raws_tail query_states_tail chunks_tail
      ws1 ws2 ws_assert ws3 where
    witness_challenge:
      "Some (witness_raw, ws1) \<in>
        set_dist (execute receive_query_index_challenge builder)"
    and witness_stage:
      "Some (witness_chunk, ws2) \<in>
        set_dist (execute (query_opening_stage A i witness_raw) ws1)"
    and witness_assert:
      "Some ((), ws_assert) \<in>
        set_dist
          (execute
            (assert
              (verifier_query_round_chunk (index (to_nat witness_raw))
                trace_roots composition_roots witness_chunk))
            ws2)"
    and witness_record:
      "Some ((), ws3) \<in>
        set_dist (execute (ro_record_staged_messages witness_chunk) ws_assert)"
    and witness_tail:
      "Some ((raws_tail, query_states_tail, chunks_tail), sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots ws3 (Suc i) n)
            ws3)"
    and raws_eq: "raws = witness_raw # raws_tail"
    and query_states_eq: "query_states = builder # query_states_tail"
    and chunks_eq: "chunks = witness_chunk # chunks_tail"
    unfolding ro_checked_staged_query_program_with_witnesses.simps Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have witness_assert_props:
    "ws_assert = ws2 \<and>
      verifier_query_round_chunk (index (to_nat witness_raw))
        trace_roots composition_roots witness_chunk"
    using witness_assert
    unfolding assert_def
    by (cases
        "verifier_query_round_chunk (index (to_nat witness_raw))
          trace_roots composition_roots witness_chunk")
      (simp_all add: throw_no_outcome)
  have ws_assert_eq: "ws_assert = ws2"
    using witness_assert_props by simp
  have witness_record':
    "Some ((), ws3) \<in>
      set_dist (execute (ro_record_staged_messages witness_chunk) ws2)"
    using witness_record ws_assert_eq by simp

  from Suc.prems(7)
  obtain verifier_mid results_tail where
    verifier_head:
      "Some ((), verifier_mid) \<in>
        set_dist (execute ?round verifier_state)"
    and verifier_tail:
      "Some (results_tail, verifier_final) \<in>
        set_dist (execute (ntimes ?round n) verifier_mid)"
    and results_eq: "results = () # results_tail"
    by (auto elim!: set_dist_bindE)

  have ordinary:
    "Some (chunks, sent) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots
            composition_roots i (Suc n))
          builder)"
    by (rule
        ro_checked_staged_query_program_with_witnesses_projection_outcome[
          OF Suc.prems(2)])

  from ro_checked_staged_query_program_Suc_verifier_round_sync_lookupE[
      where budgets=budgets and A=A and i=i and n=n
        and builder=builder and sent=sent
        and verifier_state=verifier_state and verifier_state'=verifier_mid
        and chunks=chunks and rest=rest
        and trace_roots=trace_roots and composition_roots=composition_roots
        and f_fl=f_fl and fl=fl and fr=fr and f_final=f_final
        and as=as and final=final,
      OF controlled Suc.prems(1) ordinary Suc.prems(3) Suc.prems(4)
        Suc.prems(5) Suc.prems(6) trace_roots_eq composition_roots_eq
        verifier_head]
  obtain sync_raw sync_chunk sync_chunks ss1 ss2 ss3 where
    sync_challenge:
      "Some (sync_raw, ss1) \<in>
        set_dist (execute receive_query_index_challenge builder)"
    and sync_stage:
      "Some (sync_chunk, ss2) \<in>
        set_dist (execute (query_opening_stage A i sync_raw) ss1)"
    and sync_chunk_shape:
      "verifier_query_round_chunk (index (to_nat sync_raw))
        trace_roots composition_roots sync_chunk"
    and sync_record:
      "Some ((), ss3) \<in>
        set_dist (execute (ro_record_staged_messages sync_chunk) ss2)"
    and sync_tail:
      "Some (sync_chunks, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n) ss3)"
    and sync_chunks_eq: "chunks = sync_chunk # sync_chunks"
    and state_mid_sync: "PState verifier_mid = PState ss3"
    and transcript_mid:
      "PTranscript verifier_mid = List.concat sync_chunks @ rest"
    and verifier_step_ext: "verifier_state \<le> verifier_mid"
    and counter_mid:
      "PQueryCounter verifier_mid = Suc (PQueryCounter builder)"
    and sync_head_chain:
      "ro_absorb_lookup_chain sent (PState builder) sync_chunk (PState ss3)"
    and sync_recorded:
      "fmlookup (HashMap sent)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some sync_raw"
    .

  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_bound:
    "Suc i + n \<le> length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have witness_stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i witness_raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have witness_challenge_props:
    "builder \<le> ws1 \<and>
      PState ws1 = PState builder \<and>
      PTranscript ws1 = PTranscript builder \<and>
      fmlookup (HashMap ws1)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some witness_raw"
    by (rule receive_query_index_challenge_outcome[OF witness_challenge])
  have witness_challenge_state: "PState ws1 = PState builder"
    using witness_challenge_props by simp
  have witness_stage_ext: "ws1 \<le> ws2"
    using controlled_ro_program_extension[OF witness_stage_controlled]
      witness_stage
    unfolding hash_extension_preserving_def by blast
  have witness_stage_state: "PState ws2 = PState ws1"
    using controlled_stage_outcome_fields[
      OF witness_stage_controlled witness_stage]
    by simp
  have witness_record_chain:
    "ro_absorb_lookup_chain ws3 (PState ws2) witness_chunk (PState ws3) \<and>
      ws2 \<le> ws3"
    by (rule ro_record_staged_messages_absorb_lookup_chain[
          OF witness_record'])
  have witness_tail_ordinary:
    "Some (chunks_tail, sent) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots composition_roots
            (Suc i) n)
          ws3)"
    by (rule
        ro_checked_staged_query_program_with_witnesses_projection_outcome[
          OF witness_tail])
  have witness_tail_ext: "ws3 \<le> sent"
    using ro_checked_staged_query_program_absorb_lookup_chain[
      OF controlled tail_bound witness_tail_ordinary]
    by simp
  have ws1_sent: "ws1 \<le> sent"
    by (rule hash_ext_trans[OF witness_stage_ext])
      (rule hash_ext_trans[
        OF conjunct2[OF witness_record_chain] witness_tail_ext])
  have witness_recorded:
    "fmlookup (HashMap sent)
      (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
      Some witness_raw"
    by (rule hash_extension_lookup)
      (use witness_challenge_props ws1_sent in simp_all)
  have sync_raw_eq: "sync_raw = witness_raw"
    using sync_recorded witness_recorded by simp
  have sync_chunk_eq: "sync_chunk = witness_chunk"
    and sync_chunks_tail_eq: "sync_chunks = chunks_tail"
    using sync_chunks_eq chunks_eq by simp_all

  have witness_head_chain:
    "ro_absorb_lookup_chain sent (PState builder) witness_chunk (PState ws3)"
  proof -
    have chain:
      "ro_absorb_lookup_chain sent (PState ws2) witness_chunk (PState ws3)"
      by (rule ro_absorb_lookup_chain_mono[
            OF conjunct1[OF witness_record_chain] witness_tail_ext])
    show ?thesis
      using chain witness_challenge_state witness_stage_state by simp
  qed
  have head_state_eq: "PState ss3 = PState ws3"
  proof -
    have sync_chain:
      "ro_absorb_lookup_chain sent (PState builder) witness_chunk (PState ss3)"
      using sync_head_chain sync_chunk_eq by simp
    show ?thesis
      by (rule ro_absorb_lookup_chain_functional[
            OF sync_chain witness_head_chain])
  qed
  have witness_counter_ws3:
    "PQueryCounter ws3 = Suc (PQueryCounter builder)"
    by (rule ro_checked_staged_query_record_state_counter[
          OF controlled i_bound witness_challenge witness_stage
            witness_record'])
  have sent_mid: "sent \<le> verifier_mid"
    by (rule hash_ext_trans[OF Suc.prems(3) verifier_step_ext])
  have tail_state_eq: "PState verifier_mid = PState ws3"
    using state_mid_sync head_state_eq by simp
  have tail_counter_eq:
    "PQueryCounter verifier_mid = PQueryCounter ws3"
    using counter_mid witness_counter_ws3 by simp
  have tail_transcript:
    "PTranscript verifier_mid = List.concat chunks_tail @ rest"
    using transcript_mid sync_chunks_tail_eq by simp

  from ro_verifier_query_round_program_authenticated_trace_first_fri_openings[
      OF f_fl_eq verifier_head]
  obtain auth_raw auth_idx fv trace_openings first_openings where
    auth_idx_eq: "auth_idx = index (to_nat auth_raw)"
    and auth_lookup:
      "fmlookup (HashMap verifier_mid)
        (QueryIndexChallenge
          (PQueryCounter verifier_state) (PState verifier_state)) =
        Some auth_raw"
    and trace_len:
      "length trace_openings = length (powers_scaled auth_idx)"
    and trace_values: "map opening_value trace_openings = fv"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled auth_idx"
    and trace_table_mid:
      "partial_authenticated_table fr (scale * clength)
        trace_openings verifier_mid"
    and first_table_mid:
      "partial_authenticated_table rt (scale * clength)
        first_openings verifier_mid"
    and first_indices:
      "map opening_index first_openings =
        [auth_idx, fri_sibling_index (scale * clength) auth_idx]"
    and first_len: "length first_openings = 2"
    and same_value:
      "opening_value (trace_openings ! 0) =
        opening_value (first_openings ! 0)"
    .
  have witness_lookup_mid:
    "fmlookup (HashMap verifier_mid)
      (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
      Some witness_raw"
    by (rule hash_extension_lookup[OF witness_recorded sent_mid])
  have auth_raw_eq: "auth_raw = witness_raw"
    using auth_lookup witness_lookup_mid Suc.prems(4) Suc.prems(5)
    by simp
  have auth_idx_eq_witness:
    "auth_idx = index (to_nat witness_raw)"
    using auth_idx_eq auth_raw_eq by simp

  from Suc.IH[OF tail_bound witness_tail sent_mid tail_state_eq
      tail_counter_eq tail_transcript verifier_tail]
  obtain trace_tail_at first_tail_at where
    tail_result:
      "verifier_mid \<le> verifier_final \<and>
        length raws_tail = n \<and>
        length query_states_tail = n \<and>
        length chunks_tail = n \<and>
        (\<forall>j < n.
          map opening_index (trace_tail_at j) =
            powers_scaled (index (to_nat (raws_tail ! j))) \<and>
          partial_authenticated_table fr (scale * clength)
            (trace_tail_at j) verifier_final \<and>
          map opening_index (first_tail_at j) =
            [index (to_nat (raws_tail ! j)),
              fri_sibling_index (scale * clength)
                (index (to_nat (raws_tail ! j)))] \<and>
          partial_authenticated_table rt (scale * clength)
            (first_tail_at j) verifier_final \<and>
          opening_value (trace_tail_at j ! 0) =
            opening_value (first_tail_at j ! 0))"
    by blast
  have verifier_mid_final: "verifier_mid \<le> verifier_final"
    using tail_result by simp
  have trace_table_final:
    "partial_authenticated_table fr (scale * clength)
      trace_openings verifier_final"
    by (rule partial_authenticated_table_mono[
          OF trace_table_mid verifier_mid_final])
  have first_table_final:
    "partial_authenticated_table rt (scale * clength)
      first_openings verifier_final"
    by (rule partial_authenticated_table_mono[
          OF first_table_mid verifier_mid_final])

  have verifier_ext_final: "verifier_state \<le> verifier_final"
    by (rule hash_ext_trans[OF verifier_step_ext verifier_mid_final])
  have tail_lengths:
    "length raws_tail = n \<and>
      length query_states_tail = n \<and>
      length chunks_tail = n"
    using tail_result by simp
  have tail_evidence:
    "\<forall>j < n.
      map opening_index (trace_tail_at j) =
        powers_scaled (index (to_nat (raws_tail ! j))) \<and>
      partial_authenticated_table fr (scale * clength)
        (trace_tail_at j) verifier_final \<and>
      map opening_index (first_tail_at j) =
        [index (to_nat (raws_tail ! j)),
          fri_sibling_index (scale * clength)
            (index (to_nat (raws_tail ! j)))] \<and>
      partial_authenticated_table rt (scale * clength)
        (first_tail_at j) verifier_final \<and>
      opening_value (trace_tail_at j ! 0) =
        opening_value (first_tail_at j ! 0)"
    using tail_result by simp
  let ?trace_at =
    "\<lambda>j. case j of 0 \<Rightarrow> trace_openings | Suc k \<Rightarrow> trace_tail_at k"
  let ?first_at =
    "\<lambda>j. case j of 0 \<Rightarrow> first_openings | Suc k \<Rightarrow> first_tail_at k"
  have all_evidence:
    "\<forall>j < Suc n.
      map opening_index (?trace_at j) =
        powers_scaled (index (to_nat (raws ! j))) \<and>
      partial_authenticated_table fr (scale * clength)
        (?trace_at j) verifier_final \<and>
      map opening_index (?first_at j) =
        [index (to_nat (raws ! j)),
          fri_sibling_index (scale * clength)
            (index (to_nat (raws ! j)))] \<and>
      partial_authenticated_table rt (scale * clength)
        (?first_at j) verifier_final \<and>
      opening_value (?trace_at j ! 0) =
        opening_value (?first_at j ! 0)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show
      "map opening_index (?trace_at j) =
          powers_scaled (index (to_nat (raws ! j))) \<and>
        partial_authenticated_table fr (scale * clength)
          (?trace_at j) verifier_final \<and>
        map opening_index (?first_at j) =
          [index (to_nat (raws ! j)),
            fri_sibling_index (scale * clength)
              (index (to_nat (raws ! j)))] \<and>
        partial_authenticated_table rt (scale * clength)
          (?first_at j) verifier_final \<and>
        opening_value (?trace_at j ! 0) =
          opening_value (?first_at j ! 0)"
    proof (cases j)
      case 0
      show ?thesis
        using trace_indices trace_table_final first_indices first_table_final
          same_value auth_idx_eq_witness raws_eq
        unfolding 0
        by simp
    next
      case (Suc k)
      have k_bound: "k < n"
        using j_bound Suc by simp
      have tail_at_k:
        "map opening_index (trace_tail_at k) =
            powers_scaled (index (to_nat (raws_tail ! k))) \<and>
          partial_authenticated_table fr (scale * clength)
            (trace_tail_at k) verifier_final \<and>
          map opening_index (first_tail_at k) =
            [index (to_nat (raws_tail ! k)),
              fri_sibling_index (scale * clength)
                (index (to_nat (raws_tail ! k)))] \<and>
          partial_authenticated_table rt (scale * clength)
            (first_tail_at k) verifier_final \<and>
          opening_value (trace_tail_at k ! 0) =
            opening_value (first_tail_at k ! 0)"
        by (rule tail_evidence[rule_format, OF k_bound])
      show ?thesis
        using tail_at_k raws_eq
        unfolding Suc
        by simp
    qed
  qed
  show ?case
    by (intro exI[of _ ?trace_at] exI[of _ ?first_at])
      (use verifier_ext_final tail_lengths raws_eq query_states_eq chunks_eq
        all_evidence in simp)
qed

end
end
