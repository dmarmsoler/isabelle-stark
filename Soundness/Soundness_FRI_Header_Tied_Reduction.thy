(*  Title:      Stark/Soundness_FRI_Header_Tied_Reduction.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Header_Tied_Reduction
  imports Soundness_FRI_Verifier_Tied
begin

text \<open>
  Header-tied trace FRI reductions.

  The active public route uses trace candidates tied to the verifier header
  root.  This layer mirrors the verifier-tied sampled/missing decomposition
  without widening back to arbitrary authenticated roots.
\<close>

context soundness
begin

lemma trace_fri_bad_with_header_tied_partial_candidate_None[simp]:
  "\<not> trace_fri_bad_with_header_tied_partial_candidate s None"
  unfolding trace_fri_bad_with_header_tied_partial_candidate_def
    accepted_fri_opening_transcript_def
  by simp

definition trace_fri_bad_with_header_tied_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_header_tied_sampled_layer_chain s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        doms layers.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers)"

definition trace_fri_header_tied_missing_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_missing_sampled_layer_chain s out \<longleftrightarrow>
    trace_fri_bad_with_header_tied_partial_candidate s out \<and>
    \<not> trace_fri_bad_with_header_tied_sampled_layer_chain s out"

definition trace_fri_header_tied_sampled_layer_assignment_obstruction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_sampled_layer_assignment_obstruction s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_layer_assignment_obstruction
        trace_table_low_degree trace_table (clength - 1) trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers)"

definition trace_fri_header_tied_sampled_assignment_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_sampled_assignment_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_assignment_conflict trace_table trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers)"

lemma trace_fri_header_tied_sampled_assignment_conflict_imp_sampled:
  assumes
    "trace_fri_header_tied_sampled_assignment_conflict s out"
  shows "trace_fri_sampled_assignment_conflict s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
  where fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and conflict:
      "generic_fri_sampled_assignment_conflict trace_table trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers"
    unfolding trace_fri_header_tied_sampled_assignment_conflict_def
    by blast
  have evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr fri_query_idxs trace_openings
      trace_table"
    unfolding trace_fri_partial_candidate_opening_evidence_def
      trace_fri_partial_candidate_evidence_def
    by (intro conjI fri_openings partial cand not_low)
  show ?thesis
    unfolding trace_fri_sampled_assignment_conflict_def
    by (intro exI conjI)
      (rule evidence, rule conflict)
qed

lemma wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_sampled:
  assumes sampled_bound:
    "wp_event verify_monad (trace_fri_sampled_assignment_conflict s) s \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s \<le> C"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s \<le>
      wp_event verify_monad (trace_fri_sampled_assignment_conflict s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_sampled_assignment_conflict_imp_sampled)
  then show ?thesis
    by (rule order_trans[OF _ sampled_bound])
qed

lemma trace_fri_header_tied_missing_sampled_imp_assignment_obstruction:
  assumes missing:
    "trace_fri_header_tied_missing_sampled_layer_chain s out"
  shows
    "trace_fri_header_tied_sampled_layer_assignment_obstruction s out"
proof -
  have bad:
    "trace_fri_bad_with_header_tied_partial_candidate s out"
    and not_sampled:
      "\<not> trace_fri_bad_with_header_tied_sampled_layer_chain s out"
    using missing
    unfolding trace_fri_header_tied_missing_sampled_layer_chain_def
    by blast+
  from bad obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
  where fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    unfolding trace_fri_bad_with_header_tied_partial_candidate_def
    by blast
  have partial_generic:
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
    by (rule accepted_fri_opening_transcript_trace_generic_partial_evidence
        [OF fri_openings])
  have no_chain:
    "\<And>doms layers. \<not>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
  proof
    fix doms layers
    assume chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
    have "trace_fri_bad_with_header_tied_sampled_layer_chain s out"
      unfolding trace_fri_bad_with_header_tied_sampled_layer_chain_def
      by (intro exI conjI)
        (rule fri_openings, rule header, rule partial, rule cand,
          rule not_low, rule chain)
    then show False
      using not_sampled by contradiction
  qed
  have obstruction:
    "generic_fri_sampled_layer_assignment_obstruction
      trace_table_low_degree trace_table (clength - 1) trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers"
    unfolding generic_fri_sampled_layer_assignment_obstruction_def
    using partial_generic no_chain by blast
  show ?thesis
    unfolding trace_fri_header_tied_sampled_layer_assignment_obstruction_def
    by (intro exI conjI)
      (rule fri_openings, rule header, rule partial, rule cand,
        rule not_low, rule obstruction)
qed

lemma trace_fri_header_tied_assignment_obstruction_imp_conflict_or_zero:
  assumes obstruction:
    "trace_fri_header_tied_sampled_layer_assignment_obstruction s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict s out \<or>
     trace_fri_header_tied_zero_round_final_obstruction s out"
proof -
  obtain trace_roots trace_bs' trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
  where fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs'
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and generic:
    "generic_fri_sampled_layer_assignment_obstruction
      trace_table_low_degree trace_table (clength - 1) trace_roots
      trace_bs' trace_final fri_query_idxs trace_round_layers"
    using obstruction
    unfolding trace_fri_header_tied_sampled_layer_assignment_obstruction_def
    by blast
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have trace_rounds_le: "length trace_bs' \<le> N"
  proof -
    have len: "length trace_bs' = ceil_log clength"
      using accepted_fri_opening_transcript_shapes(1,2)[OF fri_openings]
      by simp
    have "clength \<le> clength * scale"
      using scale_pos by simp
    also have "... = 2 ^ N"
      by (rule eval_power)
    finally have "ceil_log clength \<le> N"
      by (rule ceil_log_le_power)
    then show ?thesis
      using len by simp
  qed
  have query_bounds':
    "\<And>round_idx. round_idx < length fri_query_idxs \<Longrightarrow>
      fri_query_idxs ! round_idx < clength * scale"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length fri_query_idxs"
    have "fri_query_idxs ! round_idx \<in> set fri_query_idxs"
      using round_bound by simp
    then show "fri_query_idxs ! round_idx < clength * scale"
      by (rule accepted_fri_opening_transcript_query_idx_bound
          [OF fri_openings])
  qed
  have split:
    "generic_fri_sampled_assignment_conflict trace_table trace_roots
        trace_bs' trace_final fri_query_idxs trace_round_layers \<or>
      length trace_bs' = 0 \<and>
        \<not> fri_final_constant_consistent trace_table trace_final"
    by (rule
        generic_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final
          [OF generic query_bounds' eval_power trace_rounds_le])
  then show ?thesis
  proof
    assume conflict:
      "generic_fri_sampled_assignment_conflict trace_table trace_roots
        trace_bs' trace_final fri_query_idxs trace_round_layers"
    then show ?thesis
      unfolding trace_fri_header_tied_sampled_assignment_conflict_def
      by (intro disjI1 exI conjI)
        (rule fri_openings, rule header, rule partial, rule cand,
          rule not_low, rule conflict)
  next
    assume zero:
      "length trace_bs' = 0 \<and>
        \<not> fri_final_constant_consistent trace_table trace_final"
    then show ?thesis
      unfolding trace_fri_header_tied_zero_round_final_obstruction_def
      by (intro disjI2 exI conjI)
        (rule fri_openings, rule header, rule partial, rule cand,
          rule not_low,
          simp_all)
  qed
qed

lemma wp_trace_fri_header_tied_missing_sampled_bound_from_assignment_obstruction:
  assumes assignment_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_layer_assignment_obstruction s) s
      \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_missing_sampled_layer_chain s) s \<le> M"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_missing_sampled_layer_chain s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_layer_assignment_obstruction s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_missing_sampled_imp_assignment_obstruction)
  then show ?thesis
    by (rule order_trans[OF _ assignment_bound])
qed

lemma wp_trace_fri_header_tied_bound_from_sampled_and_missing:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and missing_bound:
      "wp_event verify_monad
      (trace_fri_header_tied_missing_sampled_layer_chain s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> R + M"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
      wp_event verify_monad
        (\<lambda>out. trace_fri_bad_with_header_tied_sampled_layer_chain s out \<or>
          trace_fri_header_tied_missing_sampled_layer_chain s out) s"
    unfolding trace_fri_header_tied_missing_sampled_layer_chain_def
    by (rule wp_event_mono) blast
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_sampled_layer_chain s) s +
      wp_event verify_monad
        (trace_fri_header_tied_missing_sampled_layer_chain s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (rule add_mono[OF sampled_bound missing_bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_assignment_obstruction_bound_from_conflict_and_zero:
  assumes conflict_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
      "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_layer_assignment_obstruction s) s
      \<le> C + Z"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sampled_layer_assignment_obstruction s) s
    \<le> wp_event verify_monad
      (\<lambda>out. trace_fri_header_tied_sampled_assignment_conflict s out \<or>
        trace_fri_header_tied_zero_round_final_obstruction s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_assignment_obstruction_imp_conflict_or_zero)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict s) s +
      wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> C + Z"
    by (rule add_mono[OF conflict_bound zero_bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_bound_from_sampled_conflict_and_zero:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and conflict_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s
      \<le> R + (C + Z)"
  by (rule wp_trace_fri_header_tied_bound_from_sampled_and_missing
        [OF sampled_bound
          wp_trace_fri_header_tied_missing_sampled_bound_from_assignment_obstruction
            [OF wp_trace_fri_header_tied_assignment_obstruction_bound_from_conflict_and_zero
              [OF conflict_bound zero_bound]]])

lemma trace_fri_bad_with_header_tied_partial_candidates_staged_bound:
  assumes verifier_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> C"
  by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    (simp_all add: verifier_bound)

lemma wp_trace_fri_header_tied_zero_round_bound_from_checked_and_merkle:
  assumes checked_bound:
    "wp_event verify_monad
      (trace_fri_zero_round_checked_final_obstruction s) s \<le> Z"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z + M"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le>
      wp_event verify_monad
        (\<lambda>out. trace_fri_zero_round_checked_final_obstruction s out \<or>
          partial_merkle_inconsistency_bad s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_zero_round_final_obstruction_imp_checked_or_merkle)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_zero_round_checked_final_obstruction s) s +
      wp_event verify_monad (partial_merkle_inconsistency_bad s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> Z + M"
    by (rule add_mono[OF checked_bound merkle_bound])
  finally show ?thesis .
qed

end

end
