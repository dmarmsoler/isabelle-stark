(*  Title:      Stark/Soundness_FRI_Raw_Layer_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Raw_Layer_Bounds
  imports Soundness_FRI_Authenticated_Route
begin

text \<open>
  Small reusable bounds for FRI layer indices derived from accepted verifier
  transcripts.  These keep later replay proofs from repeatedly rebuilding the
  same @{term fri_layer_raw_bound} arithmetic.
\<close>

context soundness
begin

lemma accepted_fri_opening_transcript_trace_raw_layer_bound:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and layer_bound: "j < length trace_roots"
  shows
    "\<And>raw.
      0 < fri_layer_lengths (length trace_roots) (clength * scale) ! j \<and>
      fri_layer_indices (length trace_roots) (index (to_nat raw))
        (clength * scale) ! j <
      fri_layer_lengths (length trace_roots) (clength * scale) ! j"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have trace_roots_le: "length trace_roots \<le> N"
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
  show "\<And>raw.
      0 < fri_layer_lengths (length trace_roots) (clength * scale) ! j \<and>
      fri_layer_indices (length trace_roots) (index (to_nat raw))
        (clength * scale) ! j <
      fri_layer_lengths (length trace_roots) (clength * scale) ! j"
    by (rule fri_layer_raw_bound[OF layer_bound eval_power trace_roots_le])
qed

lemma accepted_fri_opening_transcript_composition_raw_layer_bound:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and layer_bound: "j < length composition_roots"
  shows
    "\<And>raw.
      0 < fri_layer_lengths (length composition_roots) (clength * scale) ! j \<and>
      fri_layer_indices (length composition_roots) (index (to_nat raw))
        (clength * scale) ! j <
      fri_layer_lengths (length composition_roots) (clength * scale) ! j"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have composition_roots_le: "length composition_roots \<le> N"
  proof -
    have len: "length composition_roots = ceil_log (to_nat dg + 1)"
      using accepted_fri_opening_transcript_shapes(3)[OF fri_openings] .
    have "to_nat dg + 1 \<le> clength * scale"
      using degree_bound maxDegree_less_eval_domain by linarith
    also have "... = 2 ^ N"
      by (rule eval_power)
    finally have "ceil_log (to_nat dg + 1) \<le> N"
      by (rule ceil_log_le_power)
    then show ?thesis
      using len by simp
  qed
  show "\<And>raw.
      0 < fri_layer_lengths (length composition_roots)
          (clength * scale) ! j \<and>
      fri_layer_indices (length composition_roots) (index (to_nat raw))
        (clength * scale) ! j <
      fri_layer_lengths (length composition_roots) (clength * scale) ! j"
    by (rule fri_layer_raw_bound
        [OF layer_bound eval_power composition_roots_le])
qed

lemma accepted_fri_opening_transcript_trace_step_with_authenticated_chunk_at_raw:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "i < rounds"
    and layer_bound: "j < length trace_roots"
  shows
    "generic_fri_transcript_step_with_authenticated_chunk trace_roots
      trace_bs query_idxs trace_round_layers final_state i j"
  by (rule accepted_fri_opening_transcript_trace_step_with_authenticated_chunk_at
      [OF fri_openings out_eq round_bound layer_bound])
    (rule accepted_fri_opening_transcript_trace_raw_layer_bound
      [OF fri_openings layer_bound])

lemma accepted_fri_opening_transcript_composition_step_with_authenticated_chunk_at_raw:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and round_bound: "i < rounds"
    and layer_bound: "j < length composition_roots"
  shows
    "generic_fri_transcript_step_with_authenticated_chunk composition_roots
      composition_bs query_idxs composition_round_layers final_state i j"
  by (rule
      accepted_fri_opening_transcript_composition_step_with_authenticated_chunk_at
      [OF fri_openings out_eq round_bound layer_bound])
    (rule accepted_fri_opening_transcript_composition_raw_layer_bound
      [OF fri_openings degree_bound layer_bound])

end

end
