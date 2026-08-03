(*  Title:      Stark/Soundness_FRI_Query_Openings.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_Openings
  imports
    Soundness_FRI
    Soundness_Query_Transcript_Openings
begin

text \<open>
  Bridge from the FRI opening transcript evidence to the authenticated trace
  openings for the exact verifier-derived query-index list.
\<close>

context soundness
begin

lemma accepted_fri_opening_transcript_trace_openings_for_query_indices:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and out_eq: "out = Some (result, final_state)"
  obtains trace_openings where
    "accepted_with_partial_trace_openings s out fr query_idxs trace_openings"
proof -
  let ?P =
    "\<lambda>i openings. map opening_index openings =
        powers_scaled (query_idxs ! i) \<and>
      partial_authenticated_table fr (scale * clength) openings final_state"
  have len_query_idxs: "length query_idxs = rounds"
    by (rule accepted_fri_opening_transcript_shapes(7)[OF fri_openings])
  from fri_openings obtain result' final_state' fr' f_fl header_as fl
      query_state raw_idxs query_chunks
  where out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and header':
      "verifier_header_transcript s fr' trace_roots trace_final header_as dg
        composition_roots composition_final (PTranscript query_state)"
    and query_out:
      "Some (result', final_state') \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl trace_final header_as fl
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
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    unfolding accepted_fri_opening_transcript_def
    by blast
  have final_state_eq: "final_state' = final_state"
    using out_def out_eq by simp
  have fr_eq: "fr' = fr"
    using verifier_header_transcript_unique[OF header' header] by simp
  have ex_round: "\<And>i. i < rounds \<Longrightarrow> \<exists>openings. ?P i openings"
  proof -
    fix i
    assume i_bound: "i < rounds"
    show "\<exists>openings. ?P i openings"
    proof (rule
        ntimes_verifier_query_rounds_selected_trace_openings_aligned_with_replay_at
        [OF query_out i_bound len_raw query_idxs_eq len_query_chunks])
      show "PTranscript query_state =
          List.concat query_chunks @ PTranscript final_state'"
        by (rule transcript_query)
      show "\<And>j. j < rounds \<Longrightarrow>
          verifier_query_round_chunk (query_idxs ! j)
            (map snd f_fl) (map snd fl) (query_chunks ! j)"
        using query_chunk trace_roots_eq composition_roots_eq by simp
      show "\<And>j. j < rounds \<Longrightarrow>
          fmlookup (HashMap final_state')
            (QueryIndexChallenge (PQueryCounter query_state + j)
              (state_after_query_chunks
                (PState query_state) query_chunks j)) =
          Some (raw_idxs ! j)"
        using replay_lookup by simp
    next
      fix openings
      assume
        "map opening_index openings = powers_scaled (query_idxs ! i)"
        "partial_authenticated_table fr' (scale * clength) openings
          final_state'"
      then show ?thesis
        using fr_eq final_state_eq by blast
    qed
  qed
  let ?w = "\<lambda>i. SOME openings. ?P i openings"
  let ?trace_openings = "map ?w [0..<rounds]"
  have len_trace: "length ?trace_openings = rounds"
    by simp
  have props: "\<And>i. i < rounds \<Longrightarrow> ?P i (?trace_openings ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have "?P i (?w i)"
      by (rule someI_ex[OF ex_round[OF i_bound]])
    then show "?P i (?trace_openings ! i)"
      using i_bound by simp
  qed
  have partial:
    "accepted_with_partial_trace_openings s out fr query_idxs
      ?trace_openings"
    unfolding accepted_with_partial_trace_openings_def accepted_def
    by (intro conjI exI[of _ result] exI[of _ final_state])
      (use out_eq len_query_idxs len_trace props in auto)
  show ?thesis
    by (rule that[OF partial])
qed

end

end
