(*  Title:      Stark/Soundness_FRI_Trace_Replay_Gaps.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Replay_Gaps
  imports
    Soundness_FRI_Trace_Residuals
    Soundness_FRI_Composition_Replay_Gaps
begin

text \<open>
  Narrow downstream layer for trace header-tied replay gaps.  This mirrors the
  composition replay-gap layer without growing the already-large trace residual
  theory.
\<close>

context soundness
begin

lemma accepted_fri_opening_transcript_trace_layer_arithmetic:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and layer_bound: "layer_idx < length trace_bs"
  shows "2 dvd fri_evidence_layer_len trace_roots layer_idx"
    and "fri_evidence_layer_len trace_roots layer_idx * 2 ^ layer_idx =
      clength * scale"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have bs_len: "length trace_bs = length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings] .
  have roots_bound: "layer_idx < length trace_roots"
    using layer_bound bs_len by simp
  have roots_le: "length trace_roots \<le> N"
  proof -
    have len: "length trace_roots = ceil_log clength"
      using accepted_fri_opening_transcript_shapes(1)[OF fri_openings] .
    have "clength \<le> clength * scale"
      using scale_pos by simp
    also have "... = 2 ^ N"
      by (rule eval_power)
    finally have "ceil_log clength \<le> N"
      by (rule ceil_log_le_power)
    then show ?thesis
      using len by simp
  qed
  have suc_le: "Suc layer_idx \<le> N"
    using roots_bound roots_le by simp
  have dvd_eval_suc: "(2::nat) ^ Suc layer_idx dvd clength * scale"
    using le_imp_power_dvd[OF suc_le] eval_power by simp
  show "2 dvd fri_evidence_layer_len trace_roots layer_idx"
    unfolding fri_evidence_layer_len_def
    by (rule fri_layer_lengths_even_if_dvd[OF roots_bound dvd_eval_suc])
  have le_N: "layer_idx \<le> N"
    using roots_bound roots_le by simp
  have dvd_eval: "(2::nat) ^ layer_idx dvd clength * scale"
    using le_imp_power_dvd[OF le_N] eval_power by simp
  show "fri_evidence_layer_len trace_roots layer_idx *
      2 ^ layer_idx = clength * scale"
    unfolding fri_evidence_layer_len_def
    by (rule fri_layer_lengths_round_product_if_dvd
      [OF roots_bound dvd_eval])
qed

lemma accepted_fri_opening_transcript_trace_evidence_layer_idx_bound:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length trace_roots"
  shows
    "fri_evidence_layer_idx trace_roots query_idxs round_idx layer_idx <
     fri_evidence_layer_len trace_roots layer_idx"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have roots_le: "length trace_roots \<le> N"
  proof -
    have len: "length trace_roots = ceil_log clength"
      using accepted_fri_opening_transcript_shapes(1)[OF fri_openings] .
    have "clength \<le> clength * scale"
      using scale_pos by simp
    also have "... = 2 ^ N"
      by (rule eval_power)
    finally have "ceil_log clength \<le> N"
      by (rule ceil_log_le_power)
    then show ?thesis
      using len by simp
  qed
  have query_bound: "query_idxs ! round_idx < clength * scale"
    by (rule accepted_fri_opening_transcript_query_idx_bound
        [OF fri_openings])
      (use round_bound in simp)
  have idx_bound:
    "fri_layer_indices (length trace_roots) (query_idxs ! round_idx)
       (clength * scale) ! layer_idx <
     fri_layer_lengths (length trace_roots) (clength * scale) ! layer_idx"
    by (rule fri_layer_indices_nth_bound
        [OF query_bound layer_bound eval_power roots_le])
  then show ?thesis
    unfolding fri_evidence_layer_idx_def fri_evidence_layer_len_def by simp
qed

lemma trace_fri_header_tied_next_value_replay_gap_imp_merkle_or_slot_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and gap: "trace_fri_header_tied_next_value_replay_gap s out"
  shows
    "partial_merkle_inconsistency_bad s out \<or>
     trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s out"
proof -
  from gap have sampled:
    "trace_fri_header_tied_sampled_next_value_conflict s out"
    unfolding trace_fri_header_tied_next_value_replay_gap_def by simp
  from sampled obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        fri_dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and generic:
      "generic_fri_sampled_next_value_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers"
    unfolding trace_fri_header_tied_sampled_next_value_conflict_def by blast
  from generic_fri_sampled_next_value_conflictE[OF generic]
  obtain round_idx round_idx' layer_idx v v'
    where round_bound: "round_idx < length fri_query_idxs"
      and round_bound': "round_idx' < length fri_query_idxs"
      and layer_bound: "layer_idx < length trace_bs"
      and same_idx:
        "fri_evidence_next_idx trace_roots fri_query_idxs round_idx
          layer_idx =
         fri_evidence_next_idx trace_roots fri_query_idxs round_idx'
          layer_idx"
      and forced:
        "generic_fri_round_forced_next_value trace_roots trace_bs
          fri_query_idxs trace_round_layers round_idx layer_idx v"
      and forced':
        "generic_fri_round_forced_next_value trace_roots trace_bs
          fri_query_idxs trace_round_layers round_idx' layer_idx v'"
      and neq: "v \<noteq> v'"
    by blast
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  have len_bs_roots: "length trace_bs = length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings] .
  have layer_bound_roots: "layer_idx < length trace_roots"
    using layer_bound len_bs_roots by simp
  have len_query: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes(7)[OF fri_openings] .
  have raw_bound:
    "fri_evidence_layer_idx trace_roots fri_query_idxs round_idx layer_idx <
     fri_evidence_layer_len trace_roots layer_idx"
    by (rule accepted_fri_opening_transcript_trace_evidence_layer_idx_bound
        [OF fri_openings round_bound layer_bound_roots])
  have raw_bound':
    "fri_evidence_layer_idx trace_roots fri_query_idxs round_idx' layer_idx <
     fri_evidence_layer_len trace_roots layer_idx"
    by (rule accepted_fri_opening_transcript_trace_evidence_layer_idx_bound
        [OF fri_openings round_bound' layer_bound_roots])
  have even_len: "2 dvd fri_evidence_layer_len trace_roots layer_idx"
    by (rule accepted_fri_opening_transcript_trace_layer_arithmetic(1)
        [OF fri_openings layer_bound])
  have round_product:
    "fri_evidence_layer_len trace_roots layer_idx * 2 ^ layer_idx =
      clength * scale"
    by (rule accepted_fri_opening_transcript_trace_layer_arithmetic(2)
        [OF fri_openings layer_bound])
  have auth_step:
    "\<And>i j.
      i < length fri_query_idxs \<Longrightarrow>
      j < length trace_bs \<Longrightarrow>
      generic_fri_transcript_step_with_authenticated_chunk trace_roots
        trace_bs fri_query_idxs trace_round_layers final_state i j"
  proof -
    fix i j
    assume i_bound: "i < length fri_query_idxs"
      and j_bound: "j < length trace_bs"
    have i_rounds: "i < rounds"
      using i_bound len_query by simp
    have j_roots: "j < length trace_roots"
      using j_bound len_bs_roots by simp
    show
      "generic_fri_transcript_step_with_authenticated_chunk trace_roots
        trace_bs fri_query_idxs trace_round_layers final_state i j"
      by (rule
          accepted_fri_opening_transcript_trace_step_with_authenticated_chunk_at_raw
          [OF fri_openings out_eq i_rounds j_roots])
  qed
  show ?thesis
  proof (cases
      "generic_fri_sampled_same_layer_opening_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers")
    case True
    have route:
      "partial_merkle_inconsistency_bad s (Some (result, final_state)) \<or>
       generic_fri_authenticated_slot_recorded_chunk_gap trace_roots
        fri_query_idxs trace_round_layers final_state"
      by (rule generic_fri_sampled_same_layer_conflict_imp_merkle_or_slot_gap
          [OF True len_bs_roots auth_step])
    then show ?thesis
    proof
      assume "partial_merkle_inconsistency_bad s (Some (result, final_state))"
      then show ?thesis
        using out_eq by simp
    next
      assume slot_gap:
        "generic_fri_authenticated_slot_recorded_chunk_gap trace_roots
          fri_query_idxs trace_round_layers final_state"
      have route_slot_gap:
        "trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s out"
        unfolding trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_def
        by (intro exI conjI)
          (rule out_eq, rule fri_openings, rule header, rule partial, rule cand,
            rule not_low, rule slot_gap)
      then show ?thesis by simp
    qed
  next
    case False
    then have no_same:
      "\<not> generic_fri_sampled_same_layer_opening_conflict trace_roots
        trace_bs fri_query_idxs trace_round_layers"
      by simp
    have "v = v'"
      by (rule generic_fri_forced_next_value_eq_if_no_same_layer_conflict
          [OF no_same round_bound round_bound' layer_bound even_len
            raw_bound raw_bound' round_product same_idx forced forced'])
    then show ?thesis
      using neq by simp
  qed
qed

lemma wp_trace_fri_header_tied_next_value_replay_gap_bound_from_merkle_and_slot:
  fixes M A :: prob
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and slot_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s \<le> A"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> M + A"
proof -
  let ?P = "partial_merkle_inconsistency_bad s"
  let ?Q = "trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s"
  have event_le:
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le>
     wp_event verify_monad (\<lambda>out. ?P out \<or> ?Q out) s"
    by (rule wp_event_mono_on_support)
      (rule
        trace_fri_header_tied_next_value_replay_gap_imp_merkle_or_slot_on_support)
  also have "... \<le> wp_event verify_monad ?P s +
      wp_event verify_monad ?Q s"
    by (rule wp_event_union_bound)
  also have "... \<le> M + A"
    by (intro add_mono merkle_bound slot_bound)
  finally show ?thesis .
qed

lemma verifier_query_round_after_index_trace_successor_recorded_step_from_previous:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
    and recorded:
      "query_round_fri_layer_transcripts (index (to_nat raw))
        (map snd f_fl) (map snd fl) round_chunk trace_layers
        composition_layers"
    and transcript: "PTranscript s = round_chunk @ PTranscript t"
    and j_bound: "Suc j < length f_fl"
    and all_layer_bounds:
      "\<And>k. k < length f_fl \<Longrightarrow>
        0 < fri_layer_lengths (length f_fl) (clength * scale) ! k \<and>
        fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! k <
        fri_layer_lengths (length f_fl) (clength * scale) ! k"
    and previous_step:
      "fri_layer_step_evidence (snd (f_fl ! j)) (fst (f_fl ! j))
        (fri_layer_lengths (length f_fl) (clength * scale) ! j)
        (fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! j)
        (2 ^ j)
        (fri_sibling_index
          (fri_layer_lengths (length f_fl) (clength * scale) ! j)
          (fri_layer_indices (length f_fl) (index (to_nat raw))
            (clength * scale) ! j))
        xp xp_path xn xn_path
        (fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! j mod
          (fri_layer_lengths (length f_fl) (clength * scale) ! j div 2))
        v
        (trace_layers ! j)"
  shows
    "\<exists>xp_path' xn' xn_path' next_value.
      fri_layer_step_evidence (snd (f_fl ! Suc j)) (fst (f_fl ! Suc j))
        (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j)
        (fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! Suc j)
        (2 ^ Suc j)
        (fri_sibling_index
          (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j)
          (fri_layer_indices (length f_fl) (index (to_nat raw))
            (clength * scale) ! Suc j))
        v xp_path' xn' xn_path'
        (fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! Suc j mod
          (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j div 2))
        next_value
        (trace_layers ! Suc j)"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold
            (?idx, cp_eval as fv (h ^ ?idx * shift), clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  from check_decommit_on_query_outcome[OF query_decommit]
  obtain query_paths query_chunk where
    query_chunk_shape:
      "query_decommitment_transcript ?idx fv query_paths query_chunk"
    and tr_s: "PTranscript s = query_chunk @ PTranscript s1"
    by blast
  from receive_query_commits_layers_outcome[OF trace_fri]
  obtain trace_layer_chunks trace_fri_chunk where
    trace_layers_actual:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layer_chunks trace_fri_chunk"
    and tr_s1: "PTranscript s1 = trace_fri_chunk @ PTranscript s2"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  from receive_query_commits_layers_outcome[OF comp_fri]
  obtain comp_layer_chunks comp_fri_chunk where
    comp_layers_actual:
      "fri_layers_transcript (length fl) (clength * scale)
        comp_layer_chunks comp_fri_chunk"
    and tr_s3: "PTranscript s3 = comp_fri_chunk @ PTranscript s4"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  let ?actual_chunk = "query_chunk @ trace_fri_chunk @ comp_fri_chunk"
  have actual_recorded:
    "query_round_fri_layer_transcripts ?idx (map snd f_fl) (map snd fl)
      ?actual_chunk trace_layer_chunks comp_layer_chunks"
    unfolding query_round_fri_layer_transcripts_def
    by (intro exI[of _ query_chunk] exI[of _ trace_fri_chunk]
        exI[of _ comp_fri_chunk] exI[of _ fv] exI[of _ query_paths] conjI)
      (use query_chunk_shape trace_layers_actual comp_layers_actual in
        \<open>simp_all add: mult.commute\<close>)
  have actual_transcript:
    "PTranscript s = ?actual_chunk @ PTranscript t"
    using tr_s tr_s1 tr_s3 s3_eq t_eq by simp
  have actual_chunk_eq: "?actual_chunk = round_chunk"
    using actual_transcript transcript by simp
  have trace_layer_chunks_eq:
    "trace_layer_chunks = trace_layers"
    by (rule query_round_fri_layer_transcripts_unique(1)
        [OF actual_recorded[unfolded actual_chunk_eq] recorded])
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  have map_eq:
    "receive_query_commits f_fl = map fri_layer_opening_step f_fl"
    unfolding receive_query_commits_def fri_layer_opening_step_def
    by (simp add: fun_eq_iff split: prod.splits)
  have previous_step_actual:
    "fri_layer_step_evidence (snd (f_fl ! j)) (fst (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) ?idx (clength * scale) ! j)
      (1 * 2 ^ j)
      (fri_sibling_index
        (fri_layer_lengths (length f_fl) (clength * scale) ! j)
        (fri_layer_indices (length f_fl) ?idx (clength * scale) ! j))
      xp xp_path xn xn_path
      (fri_layer_indices (length f_fl) ?idx (clength * scale) ! j mod
        (fri_layer_lengths (length f_fl) (clength * scale) ! j div 2))
      v
      (trace_layer_chunks ! j)"
    using previous_step trace_layer_chunks_eq by simp
  from mfold_fri_layer_opening_successor_recorded_step_from_previous
      [OF trace_fri[unfolded map_eq] trace_layers_actual tr_s1 idx_bound
        all_layer_bounds j_bound previous_step_actual]
  obtain sxp_path sxn sxn_path snext where succ_actual:
    "fri_layer_step_evidence (snd (f_fl ! Suc j)) (fst (f_fl ! Suc j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j)
      (fri_layer_indices (length f_fl) ?idx (clength * scale) ! Suc j)
      (1 * 2 ^ Suc j)
      (fri_sibling_index
        (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j)
        (fri_layer_indices (length f_fl) ?idx (clength * scale) ! Suc j))
      v sxp_path sxn sxn_path
      (fri_layer_indices (length f_fl) ?idx (clength * scale) ! Suc j mod
        (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j div 2))
      snext
      (trace_layer_chunks ! Suc j)"
    by blast
  have succ:
    "fri_layer_step_evidence (snd (f_fl ! Suc j)) (fst (f_fl ! Suc j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j)
      (fri_layer_indices (length f_fl) ?idx (clength * scale) ! Suc j)
      (2 ^ Suc j)
      (fri_sibling_index
        (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j)
        (fri_layer_indices (length f_fl) ?idx (clength * scale) ! Suc j))
      v sxp_path sxn sxn_path
      (fri_layer_indices (length f_fl) ?idx (clength * scale) ! Suc j mod
        (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j div 2))
      snext
      (trace_layers ! Suc j)"
    using succ_actual trace_layer_chunks_eq by simp
  show ?thesis
    using succ by blast
qed

lemma accepted_fri_opening_transcript_trace_successor_recorded_step_from_previous_at:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "i < rounds"
    and layer_bound: "Suc j < length trace_roots"
    and all_layer_bounds:
      "\<And>raw k. k < length trace_roots \<Longrightarrow>
        0 < fri_layer_lengths (length trace_roots)
          (clength * scale) ! k \<and>
        fri_layer_indices (length trace_roots) (index (to_nat raw))
          (clength * scale) ! k <
        fri_layer_lengths (length trace_roots) (clength * scale) ! k"
    and previous_step:
      "fri_layer_step_evidence (trace_roots ! j)
        (trace_bs ! j)
        (fri_evidence_layer_len trace_roots j)
        (fri_evidence_layer_idx trace_roots query_idxs i j)
        (2 ^ j)
        (fri_sibling_index (fri_evidence_layer_len trace_roots j)
          (fri_evidence_layer_idx trace_roots query_idxs i j))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots query_idxs i j)
        v
        (trace_round_layers ! i ! j)"
  shows
    "\<exists>xp_path' xn' xn_path' next_value.
      fri_layer_step_evidence (trace_roots ! Suc j)
        (trace_bs ! Suc j)
        (fri_evidence_layer_len trace_roots (Suc j))
        (fri_evidence_layer_idx trace_roots query_idxs i (Suc j))
        (2 ^ Suc j)
        (fri_sibling_index
          (fri_evidence_layer_len trace_roots (Suc j))
          (fri_evidence_layer_idx trace_roots query_idxs i
            (Suc j)))
        v xp_path' xn' xn_path'
        (fri_evidence_next_idx trace_roots query_idxs i (Suc j))
        next_value
        (trace_round_layers ! i ! Suc j)"
proof -
  from fri_openings obtain result' final_state' fr f_fl as fl query_state
      raw_idxs query_chunks where
    out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and trace_bs_eq: "trace_bs = map fst f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and outcome:
      "Some (result', final_state') \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr f_fl trace_final as fl
              composition_final)
            rounds)
          query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state'"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    and recorded:
      "\<And>i. i < rounds \<Longrightarrow>
        query_round_fri_layer_transcripts (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)
          (trace_round_layers ! i) (composition_round_layers ! i)"
    unfolding accepted_fri_opening_transcript_def by blast
  have result_eq: "result' = result"
    using out_def out_eq by simp
  have final_state_eq: "final_state' = final_state"
    using out_def out_eq by simp
  have outcome':
    "Some (result, final_state) \<in>
      set_dist (execute
        (ntimes
          (verifier_query_round_program fr f_fl trace_final as fl
            composition_final)
          rounds)
        query_state)"
    using outcome result_eq final_state_eq by simp
  let ?round =
    "verifier_query_round_program fr f_fl trace_final as fl composition_final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome' round_bound]
  obtain prefix x suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in>
        set_dist (execute (ntimes ?round i) query_state)"
    and round:
      "Some (x, s_suc) \<in> set_dist (execute ?round s_i)"
    and suffix:
      "Some (suffix, final_state) \<in>
        set_dist (execute (ntimes ?round (rounds - Suc i)) s_suc)"
    by blast
  have x_eq: "x = ()"
    by (cases x) simp
  show ?thesis
  proof (rule query_opening_ntimes_prefix_transcript_state_alignment
      [OF prefix])
    fix prefix_query_idxs prefix_chunks
    assume len_prefix_idxs: "length prefix_query_idxs = i"
      and len_prefix_chunks: "length prefix_chunks = i"
      and transcript_prefix:
        "PTranscript query_state =
          List.concat prefix_chunks @ PTranscript s_i"
      and state_i:
        "PState s_i =
          state_after_query_chunks (PState query_state) prefix_chunks i"
      and counter_i: "PQueryCounter s_i = PQueryCounter query_state + i"
      and prefix_ext: "query_state \<le> s_i"
      and prefix_rounds:
        "\<And>k. k < i \<Longrightarrow>
          verifier_query_round_chunk (prefix_query_idxs ! k)
            (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    from round[unfolded x_eq verifier_query_round_program_alt_def]
    obtain raw s0 where
      raw_out:
        "Some (raw, s0) \<in>
          set_dist (execute receive_query_index_challenge s_i)"
      and after:
        "Some ((), s_suc) \<in>
          set_dist (execute
            (verifier_query_round_after_index_program fr f_fl trace_final as
              fl composition_final raw) s0)"
      by (auto elim!: set_dist_bindE)
    have tr_s0: "PTranscript s0 = PTranscript s_i"
      using receive_query_index_challenge_outcome[OF raw_out] by simp
    show ?thesis
    proof (rule verifier_query_round_program_outcome[OF round[unfolded x_eq]])
      fix raw' idx chunk
      assume idx_eq: "idx = index (to_nat raw')"
        and chunk_shape:
          "verifier_query_round_chunk idx (map snd f_fl) (map snd fl)
            chunk"
        and transcript_round:
          "PTranscript s_i = chunk @ PTranscript s_suc"
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw'"
      have raw_eq': "raw = raw'"
      proof -
        have lookup_s0:
          "fmlookup (HashMap s0)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw"
          using receive_query_index_challenge_outcome[OF raw_out] by simp
        have s0_suc: "s0 \<le> s_suc"
          using verifier_query_round_after_index_program_outcome[OF after]
          by simp
        have lookup_suc_raw:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw"
          using hash_extension_lookup[OF lookup_s0 s0_suc] .
        show ?thesis
          using lookup_suc lookup_suc_raw by simp
      qed
      show ?thesis
      proof (rule query_opening_ntimes_suffix_transcript_state_alignment
          [OF suffix])
        fix suffix_query_idxs suffix_chunks
        assume len_suffix_idxs:
            "length suffix_query_idxs = rounds - Suc i"
          and len_suffix_chunks:
            "length suffix_chunks = rounds - Suc i"
          and transcript_suffix:
            "PTranscript s_suc =
              List.concat suffix_chunks @ PTranscript final_state"
          and suffix_ext: "s_suc \<le> final_state"
          and suffix_rounds:
            "\<And>k. k < rounds - Suc i \<Longrightarrow>
              verifier_query_round_chunk (suffix_query_idxs ! k)
                (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
        let ?selected_chunks = "prefix_chunks @ chunk # suffix_chunks"
        have len_selected_chunks: "length ?selected_chunks = rounds"
          using len_prefix_chunks len_suffix_chunks round_bound by simp
        have selected_chunk_lens:
          "\<And>k. k < rounds \<Longrightarrow>
            length (?selected_chunks ! k) =
              verifier_query_round_transcript_length (query_idxs ! k)
                (map snd f_fl) (map snd fl)"
        proof -
          fix k
          assume k_bound: "k < rounds"
          show
            "length (?selected_chunks ! k) =
              verifier_query_round_transcript_length (query_idxs ! k)
                (map snd f_fl) (map snd fl)"
          proof (cases "k < i")
            case True
            have nth_eq: "?selected_chunks ! k = prefix_chunks ! k"
              using True len_prefix_chunks by (simp add: nth_append)
            have
              "length (prefix_chunks ! k) =
                verifier_query_round_transcript_length
                  (prefix_query_idxs ! k) (map snd f_fl) (map snd fl)"
              by (rule verifier_query_round_chunk_length
                  [OF prefix_rounds[OF True]])
            then show ?thesis
              using nth_eq
              by (simp add:
                  verifier_query_round_transcript_length_index_irrelevant)
          next
            case False
            show ?thesis
            proof (cases "k = i")
              case True
              have nth_eq: "?selected_chunks ! k = chunk"
                using True len_prefix_chunks by (simp add: nth_append)
              have
                "length chunk =
                  verifier_query_round_transcript_length idx
                    (map snd f_fl) (map snd fl)"
                by (rule verifier_query_round_chunk_length[OF chunk_shape])
              then show ?thesis
                using nth_eq
                by (simp add:
                    verifier_query_round_transcript_length_index_irrelevant)
            next
              case False
              let ?k = "k - Suc i"
              have ge: "Suc i \<le> k"
                using \<open>\<not> k < i\<close> False by linarith
              have k_bound': "?k < rounds - Suc i"
                using ge k_bound by linarith
              have nth_eq: "?selected_chunks ! k = suffix_chunks ! ?k"
                using ge len_prefix_chunks by (simp add: nth_append)
              have
                "length (suffix_chunks ! ?k) =
                  verifier_query_round_transcript_length
                    (suffix_query_idxs ! ?k) (map snd f_fl) (map snd fl)"
                by (rule verifier_query_round_chunk_length
                    [OF suffix_rounds[OF k_bound']])
              then show ?thesis
                using nth_eq
                by (simp add:
                    verifier_query_round_transcript_length_index_irrelevant)
            qed
          qed
        qed
        have query_chunk_f:
          "\<And>k. k < rounds \<Longrightarrow>
            verifier_query_round_chunk (query_idxs ! k)
              (map snd f_fl) (map snd fl) (query_chunks ! k)"
          using query_chunk trace_roots_eq composition_roots_eq by simp
        have query_chunk_lens:
          "\<And>k. k < rounds \<Longrightarrow>
            length (query_chunks ! k) =
              verifier_query_round_transcript_length (query_idxs ! k)
                (map snd f_fl) (map snd fl)"
          using query_chunk_f verifier_query_round_chunk_length by blast
        have selected_transcript:
          "PTranscript query_state =
            List.concat ?selected_chunks @ PTranscript final_state"
          using transcript_prefix transcript_round transcript_suffix by simp
        have concat_eq: "List.concat ?selected_chunks = List.concat query_chunks"
          using selected_transcript transcript_query final_state_eq by simp
        have chunks_eq: "?selected_chunks = query_chunks"
        proof -
          have same_lens:
            "\<And>k. k < length ?selected_chunks \<Longrightarrow>
              length (?selected_chunks ! k) = length (query_chunks ! k)"
            using selected_chunk_lens query_chunk_lens len_selected_chunks
            by simp
          have concat_eq_empty:
            "List.concat ?selected_chunks @ [] = List.concat query_chunks"
            using concat_eq by simp
          have len_eq: "length ?selected_chunks = length query_chunks"
            using len_selected_chunks len_query_chunks by simp
          have "?selected_chunks = query_chunks \<and> ([] :: 'f list) = []"
            by (rule concat_append_eq_concat_same_chunk_lengths
                [OF len_eq same_lens concat_eq_empty])
          then show ?thesis
            by simp
        qed
        have prefix_state_eq:
          "state_after_query_chunks (PState query_state) prefix_chunks i =
            state_after_query_chunks (PState query_state) query_chunks i"
        proof -
          have
            "state_after_query_chunks (PState query_state) ?selected_chunks i =
              state_after_query_chunks (PState query_state) prefix_chunks i"
            by (rule state_after_query_chunks_append_prefix
                [OF len_prefix_chunks])
          then show ?thesis
            using chunks_eq by simp
        qed
        have lookup_final:
          "fmlookup (HashMap final_state)
            (QueryIndexChallenge (PQueryCounter query_state + i)
              (state_after_query_chunks (PState query_state) query_chunks i)) =
          Some raw'"
        proof -
          have lookup_suc':
            "fmlookup (HashMap s_suc)
              (QueryIndexChallenge (PQueryCounter query_state + i)
                (state_after_query_chunks (PState query_state)
                  prefix_chunks i)) =
            Some raw'"
            using lookup_suc state_i counter_i by simp
          have lookup_final_prefix:
            "fmlookup (HashMap final_state)
              (QueryIndexChallenge (PQueryCounter query_state + i)
                (state_after_query_chunks (PState query_state)
                  prefix_chunks i)) =
            Some raw'"
            using hash_extension_lookup[OF lookup_suc' suffix_ext] .
          show ?thesis
            using lookup_final_prefix prefix_state_eq by simp
        qed
        have raw_idx_eq: "raw' = raw_idxs ! i"
          using lookup_final replay_lookup[OF round_bound] final_state_eq
          by simp
        have idx_eq_query: "idx = query_idxs ! i"
          using idx_eq raw_idx_eq query_idxs_eq len_raw round_bound by simp
        have selected_i: "?selected_chunks ! i = chunk"
          using len_prefix_chunks by (simp add: nth_append)
        have chunk_i_eq: "chunk = query_chunks ! i"
          using chunks_eq selected_i by simp
        have recorded_i:
          "query_round_fri_layer_transcripts (index (to_nat raw))
            (map snd f_fl) (map snd fl) chunk (trace_round_layers ! i)
            (composition_round_layers ! i)"
          using recorded[OF round_bound] idx_eq idx_eq_query raw_eq'
            chunk_i_eq trace_roots_eq composition_roots_eq
          by simp
        have tr_s0_suc:
          "PTranscript s0 = chunk @ PTranscript s_suc"
          using tr_s0 transcript_round by simp
        have suc_j_bound_fl: "Suc j < length f_fl"
          using layer_bound trace_roots_eq by simp
        have all_layer_bounds_fl:
          "\<And>k. k < length f_fl \<Longrightarrow>
            0 < fri_layer_lengths (length f_fl) (clength * scale) ! k \<and>
            fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! k <
            fri_layer_lengths (length f_fl) (clength * scale) ! k"
          using all_layer_bounds trace_roots_eq by simp
        have raw_idx_query: "index (to_nat raw) = query_idxs ! i"
          using idx_eq idx_eq_query raw_eq' by simp
        have previous_step_fl:
          "fri_layer_step_evidence (snd (f_fl ! j)) (fst (f_fl ! j))
            (fri_layer_lengths (length f_fl) (clength * scale) ! j)
            (fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! j)
            (2 ^ j)
            (fri_sibling_index
              (fri_layer_lengths (length f_fl) (clength * scale) ! j)
              (fri_layer_indices (length f_fl) (index (to_nat raw))
                (clength * scale) ! j))
            xp xp_path xn xn_path
            (fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! j mod
              (fri_layer_lengths (length f_fl) (clength * scale) ! j div 2))
            v
            (trace_round_layers ! i ! j)"
          using previous_step trace_roots_eq trace_bs_eq raw_idx_query
            layer_bound
          unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
            fri_evidence_next_idx_def
          by simp
        from verifier_query_round_after_index_trace_successor_recorded_step_from_previous
            [OF after recorded_i tr_s0_suc suc_j_bound_fl
              all_layer_bounds_fl previous_step_fl]
        obtain sxp_path sxn sxn_path snext where succ_fl:
          "fri_layer_step_evidence (snd (f_fl ! Suc j))
            (fst (f_fl ! Suc j))
            (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j)
            (fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! Suc j)
            (2 ^ Suc j)
            (fri_sibling_index
              (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j)
              (fri_layer_indices (length f_fl) (index (to_nat raw))
                (clength * scale) ! Suc j))
            v sxp_path sxn sxn_path
            (fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! Suc j mod
              (fri_layer_lengths (length f_fl) (clength * scale) ! Suc j
                div 2))
            snext
            (trace_round_layers ! i ! Suc j)"
          by blast
        have succ:
          "fri_layer_step_evidence (trace_roots ! Suc j)
            (trace_bs ! Suc j)
            (fri_evidence_layer_len trace_roots (Suc j))
            (fri_evidence_layer_idx trace_roots query_idxs i (Suc j))
            (2 ^ Suc j)
            (fri_sibling_index
              (fri_evidence_layer_len trace_roots (Suc j))
              (fri_evidence_layer_idx trace_roots query_idxs i
                (Suc j)))
            v sxp_path sxn sxn_path
            (fri_evidence_next_idx trace_roots query_idxs i (Suc j))
            snext
            (trace_round_layers ! i ! Suc j)"
          using succ_fl trace_roots_eq trace_bs_eq raw_idx_query layer_bound
          unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
            fri_evidence_next_idx_def
          by simp
        show ?thesis
          using succ by blast
      qed
    qed
  qed
qed

lemma trace_fri_header_tied_successor_replay_gap_imp_merkle_or_slot_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and gap: "trace_fri_header_tied_successor_replay_gap s out"
  shows
    "partial_merkle_inconsistency_bad s out \<or>
     trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s out"
proof -
  from gap have sampled:
    "trace_fri_header_tied_sampled_successor_opening_conflict s out"
    unfolding trace_fri_header_tied_successor_replay_gap_def by simp
  from sampled obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and generic:
      "generic_fri_sampled_successor_opening_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers"
    unfolding trace_fri_header_tied_sampled_successor_opening_conflict_def
    by blast
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  have len_bs_roots: "length trace_bs = length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings] .
  have len_query: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes(7)[OF fri_openings] .
  have all_layer_bounds:
    "\<And>raw k. k < length trace_roots \<Longrightarrow>
      0 < fri_layer_lengths (length trace_roots)
        (clength * scale) ! k \<and>
      fri_layer_indices (length trace_roots) (index (to_nat raw))
        (clength * scale) ! k <
      fri_layer_lengths (length trace_roots) (clength * scale) ! k"
    by (rule accepted_fri_opening_transcript_trace_raw_layer_bound
        [OF fri_openings])
  have source_step:
    "\<And>source_round layer_idx v.
      source_round < length fri_query_idxs \<Longrightarrow>
      Suc layer_idx < length trace_bs \<Longrightarrow>
      generic_fri_round_forced_next_value trace_roots trace_bs
        fri_query_idxs trace_round_layers source_round layer_idx v \<Longrightarrow>
      \<exists>xp_path xn xn_path.
        fri_layer_step_evidence
          (trace_roots ! Suc layer_idx)
          (trace_bs ! Suc layer_idx)
          (fri_evidence_layer_len trace_roots (Suc layer_idx))
          (fri_evidence_layer_idx trace_roots fri_query_idxs
            source_round (Suc layer_idx))
          (2 ^ Suc layer_idx)
          (fri_sibling_index
            (fri_evidence_layer_len trace_roots (Suc layer_idx))
            (fri_evidence_layer_idx trace_roots fri_query_idxs
              source_round (Suc layer_idx)))
          v xp_path xn xn_path
          (fri_evidence_next_idx trace_roots fri_query_idxs
            source_round (Suc layer_idx))
          (fri_evidence_next_value trace_roots trace_bs
            fri_query_idxs source_round (Suc layer_idx) v xn)
          (trace_round_layers ! source_round ! Suc layer_idx)"
  proof -
    fix source_round layer_idx v
    assume source_round_bound: "source_round < length fri_query_idxs"
      and layer_bound': "Suc layer_idx < length trace_bs"
      and forced:
        "generic_fri_round_forced_next_value trace_roots trace_bs
          fri_query_idxs trace_round_layers source_round layer_idx v"
    have source_round_rounds: "source_round < rounds"
      using source_round_bound len_query by simp
    have layer_bound_roots: "Suc layer_idx < length trace_roots"
      using layer_bound' len_bs_roots by simp
    from forced obtain fxp fxp_path fxn fxn_path where previous_step:
      "fri_layer_step_evidence (trace_roots ! layer_idx)
        (trace_bs ! layer_idx)
        (fri_evidence_layer_len trace_roots layer_idx)
        (fri_evidence_layer_idx trace_roots fri_query_idxs
          source_round layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len trace_roots layer_idx)
          (fri_evidence_layer_idx trace_roots fri_query_idxs
            source_round layer_idx))
        fxp fxp_path fxn fxn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs
          source_round layer_idx)
        v
        (trace_round_layers ! source_round ! layer_idx)"
      unfolding generic_fri_round_forced_next_value_def by blast
    from accepted_fri_opening_transcript_trace_successor_recorded_step_from_previous_at
        [OF fri_openings out_eq source_round_rounds layer_bound_roots
          all_layer_bounds previous_step]
    obtain sxp_path sxn sxn_path snext where succ:
      "fri_layer_step_evidence (trace_roots ! Suc layer_idx)
        (trace_bs ! Suc layer_idx)
        (fri_evidence_layer_len trace_roots (Suc layer_idx))
        (fri_evidence_layer_idx trace_roots fri_query_idxs
          source_round (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len trace_roots (Suc layer_idx))
          (fri_evidence_layer_idx trace_roots fri_query_idxs
            source_round (Suc layer_idx)))
        v sxp_path sxn sxn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs
          source_round (Suc layer_idx))
        snext
        (trace_round_layers ! source_round ! Suc layer_idx)"
      by blast
    have snext_eq:
      "snext =
        fri_evidence_next_value trace_roots trace_bs
          fri_query_idxs source_round (Suc layer_idx) v sxn"
      using fri_layer_step_evidenceD(3)[OF succ]
      unfolding fri_evidence_next_value_def by simp
    show
      "\<exists>xp_path xn xn_path.
        fri_layer_step_evidence
          (trace_roots ! Suc layer_idx)
          (trace_bs ! Suc layer_idx)
          (fri_evidence_layer_len trace_roots (Suc layer_idx))
          (fri_evidence_layer_idx trace_roots fri_query_idxs
            source_round (Suc layer_idx))
          (2 ^ Suc layer_idx)
          (fri_sibling_index
            (fri_evidence_layer_len trace_roots (Suc layer_idx))
            (fri_evidence_layer_idx trace_roots fri_query_idxs
              source_round (Suc layer_idx)))
          v xp_path xn xn_path
          (fri_evidence_next_idx trace_roots fri_query_idxs
            source_round (Suc layer_idx))
          (fri_evidence_next_value trace_roots trace_bs
            fri_query_idxs source_round (Suc layer_idx) v xn)
          (trace_round_layers ! source_round ! Suc layer_idx)"
      using succ snext_eq by blast
  qed
  have same_layer:
    "generic_fri_sampled_same_layer_opening_conflict trace_roots trace_bs
      fri_query_idxs trace_round_layers"
    by (rule generic_fri_sampled_successor_conflict_imp_same_layer_with_source_steps
        [OF generic len_bs_roots source_step])
  have auth_step:
    "\<And>i j.
      i < length fri_query_idxs \<Longrightarrow>
      j < length trace_bs \<Longrightarrow>
      generic_fri_transcript_step_with_authenticated_chunk trace_roots
        trace_bs fri_query_idxs trace_round_layers final_state i j"
  proof -
    fix i j
    assume i_bound: "i < length fri_query_idxs"
      and j_bound: "j < length trace_bs"
    have i_rounds: "i < rounds"
      using i_bound len_query by simp
    have j_roots: "j < length trace_roots"
      using j_bound len_bs_roots by simp
    show
      "generic_fri_transcript_step_with_authenticated_chunk trace_roots
        trace_bs fri_query_idxs trace_round_layers final_state i j"
      by (rule
          accepted_fri_opening_transcript_trace_step_with_authenticated_chunk_at_raw
          [OF fri_openings out_eq i_rounds j_roots])
  qed
  have route:
    "partial_merkle_inconsistency_bad s (Some (result, final_state)) \<or>
     generic_fri_authenticated_slot_recorded_chunk_gap trace_roots
      fri_query_idxs trace_round_layers final_state"
    by (rule generic_fri_sampled_same_layer_conflict_imp_merkle_or_slot_gap
        [OF same_layer len_bs_roots auth_step])
  then show ?thesis
  proof
    assume "partial_merkle_inconsistency_bad s (Some (result, final_state))"
    then show ?thesis
      using out_eq by simp
  next
    assume slot_gap:
      "generic_fri_authenticated_slot_recorded_chunk_gap trace_roots
        fri_query_idxs trace_round_layers final_state"
    have route_slot_gap:
      "trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s out"
      unfolding trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_def
      by (intro exI conjI)
        (rule out_eq, rule fri_openings, rule header, rule partial, rule cand,
          rule not_low, rule slot_gap)
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_header_tied_successor_replay_gap_bound_from_merkle_and_slot:
  fixes M A :: prob
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and slot_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s \<le> A"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> M + A"
proof -
  let ?P = "partial_merkle_inconsistency_bad s"
  let ?Q = "trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s"
  have event_le:
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le>
     wp_event verify_monad (\<lambda>out. ?P out \<or> ?Q out) s"
    by (rule wp_event_mono_on_support)
      (rule
        trace_fri_header_tied_successor_replay_gap_imp_merkle_or_slot_on_support)
  also have "... \<le> wp_event verify_monad ?P s +
      wp_event verify_monad ?Q s"
    by (rule wp_event_union_bound)
  also have "... \<le> M + A"
    by (intro add_mono merkle_bound slot_bound)
  finally show ?thesis .
qed

end

end
