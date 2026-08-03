(*  Title:      Stark/Soundness_FRI_Trace_Transcript_Consistent.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Transcript_Consistent
  imports Soundness_FRI_Trace_Candidate_Blocker
begin

text \<open>
  Trace-only verifier-consumed FRI evidence.

  The broad reachable trace FRI predicate is root-parametric: it accepts any
  authenticated trace root present in the final verifier state.  This layer
  names the verifier-consumed alternative, where the trace root and query
  indices are those appearing in the accepted FRI opening transcript.  It does
  not change the protocol or the public theorem interface.
\<close>

context soundness
begin

definition accepted_with_partial_trace_openings_verifier_consumed
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list list \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> bool"
where
  "accepted_with_partial_trace_openings_verifier_consumed s out
      trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final query_idxs trace_round_layers
      composition_round_layers fr as trace_openings \<longleftrightarrow>
    accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers \<and>
    (\<exists>rest.
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest) \<and>
    accepted_with_partial_trace_openings s out fr query_idxs trace_openings"

lemma accepted_with_partial_trace_openings_verifier_consumedD:
  assumes
    "accepted_with_partial_trace_openings_verifier_consumed s out
      trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final query_idxs trace_round_layers
      composition_round_layers fr as trace_openings"
  shows
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    "\<exists>rest. verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    "accepted_with_partial_trace_openings s out fr query_idxs trace_openings"
  using assms
  unfolding accepted_with_partial_trace_openings_verifier_consumed_def
  by simp_all

definition trace_fri_bad_with_verifier_consumed_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_verifier_consumed_partial_candidate s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings trace_table.
      accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table)"

lemma trace_fri_bad_with_verifier_consumed_imp_header_tied:
  assumes "trace_fri_bad_with_verifier_consumed_partial_candidate s out"
  shows "trace_fri_bad_with_header_tied_partial_candidate s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings trace_table where
    consumed:
      "accepted_with_partial_trace_openings_verifier_consumed s out
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    unfolding trace_fri_bad_with_verifier_consumed_partial_candidate_def
    by blast
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers"
    by (rule accepted_with_partial_trace_openings_verifier_consumedD(1)
        [OF consumed])
  from accepted_with_partial_trace_openings_verifier_consumedD(2)[OF consumed]
  obtain rest where header:
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    by blast
  have partial:
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    by (rule accepted_with_partial_trace_openings_verifier_consumedD(3)
        [OF consumed])
  show ?thesis
    unfolding trace_fri_bad_with_header_tied_partial_candidate_def
    by (intro exI conjI)
      (rule fri_openings, rule header, rule partial, rule candidate,
        rule not_low)
qed

lemma trace_fri_bad_with_header_tied_imp_verifier_consumed:
  assumes "trace_fri_bad_with_header_tied_partial_candidate s out"
  shows "trace_fri_bad_with_verifier_consumed_partial_candidate s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table where
    fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    unfolding trace_fri_bad_with_header_tied_partial_candidate_def
    by blast
  have consumed:
    "accepted_with_partial_trace_openings_verifier_consumed s out
      trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings"
    unfolding accepted_with_partial_trace_openings_verifier_consumed_def
    by (intro conjI exI)
      (rule fri_openings, rule header, rule partial)
  show ?thesis
    unfolding trace_fri_bad_with_verifier_consumed_partial_candidate_def
    by (intro exI conjI)
      (rule consumed, rule candidate, rule not_low)
qed

lemma trace_fri_bad_with_verifier_consumed_iff_header_tied:
  "trace_fri_bad_with_verifier_consumed_partial_candidate s out
    \<longleftrightarrow> trace_fri_bad_with_header_tied_partial_candidate s out"
proof
  assume "trace_fri_bad_with_verifier_consumed_partial_candidate s out"
  then show "trace_fri_bad_with_header_tied_partial_candidate s out"
    by (rule trace_fri_bad_with_verifier_consumed_imp_header_tied)
next
  assume "trace_fri_bad_with_header_tied_partial_candidate s out"
  then show "trace_fri_bad_with_verifier_consumed_partial_candidate s out"
    by (rule trace_fri_bad_with_header_tied_imp_verifier_consumed)
qed

lemma trace_fri_header_tied_reduction_verifier_consumed_bound:
  assumes "trace_fri_header_tied_reduction s"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_verifier_consumed_partial_candidate s) s \<le>
      trace_fri_error"
proof -
  have mono:
    "wp_event verify_monad
      (trace_fri_bad_with_verifier_consumed_partial_candidate s) s \<le>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s"
    by (rule wp_event_mono)
      (rule trace_fri_bad_with_verifier_consumed_imp_header_tied)
  also have "... \<le> trace_fri_error"
    by (rule trace_fri_header_tied_reductionD[OF assms])
  finally show ?thesis .
qed

lemma trace_fri_verifier_consumed_reduction_staged_bound:
  assumes reductions:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_header_tied_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_verifier_consumed_partial_candidate)
      adversary_initial_state \<le> trace_fri_error"
proof -
  have mono:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_verifier_consumed_partial_candidate)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume consumed:
      "staged_security_with_data_state_verifier_event
        trace_fri_bad_with_verifier_consumed_partial_candidate out"
    then show
      "staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate out"
    proof (cases out)
      case None
      then show ?thesis
        using consumed
        unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some payload)
      obtain data attacker_state result final_state where payload:
        "payload = (((data, attacker_state), result), final_state)"
        by (cases payload) auto
      have consumed':
        "trace_fri_bad_with_verifier_consumed_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (Some (result, final_state))"
        using consumed Some payload
        unfolding staged_security_with_data_state_verifier_event_def
        by simp
      have header:
        "trace_fri_bad_with_header_tied_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (Some (result, final_state))"
        by (rule trace_fri_bad_with_verifier_consumed_imp_header_tied
            [OF consumed'])
      show ?thesis
        using Some payload header
        unfolding staged_security_with_data_state_verifier_event_def
        by simp
    qed
  qed
  also have "... \<le> trace_fri_error"
    by (rule trace_fri_header_tied_reduction_staged_bound[OF reductions])
  finally show ?thesis .
qed

end

end
