(*  Title:      Stark/Soundness_FRI_Full_Cover_Active_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Full_Cover_Active_Bounds
  imports
    Soundness_FRI_Obligation_Normalization
    Soundness_FRI_Full_Cover_Domains
begin

text \<open>
  Compact active-route bridges for the full-cover FRI split.

  The imported layers already prove:
  \<^item> a full-cover challenge-list/envelope bound;
  \<^item> a missing-full-cover domain split;
  \<^item> active trace/composition residual adapters.

  This theory only packages those ingredients in the shape consumed by the
  same-run public soundness route.  It does not add protocol assumptions or
  change the FRI model.
\<close>

context soundness
begin

lemma wp_trace_fri_header_tied_sampled_layer_chain_bound_from_envelope_domain_split:
  assumes future: "trace_fri_future_fresh s"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and challenge_bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> R"
    and proximity:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and domain_length:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_length_failure s) s \<le> DL"
    and sampled_domain:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_sampled_domain_failure s) s \<le> SD"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s
      \<le> R + (P + I + (I + DL) + (I + SD))"
proof (rule
    wp_trace_fri_header_tied_sampled_layer_chain_bound_from_full_cover_and_missing)
  show "wp_event verify_monad
      (trace_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    by (rule wp_trace_fri_bad_with_full_cover_layer_chain_bound_from_envelope
        [OF future envelope subset challenge_bound])
  show "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + (I + DL) + (I + SD)"
    by (rule wp_trace_fri_sampled_missing_full_cover_bound_from_domain_split
        [OF proximity index domain_length sampled_domain])
qed

lemma wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_envelope_domain_split:
  assumes future: "composition_fri_future_fresh s"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and challenge_bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> R"
    and proximity:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure s bad) s
        \<le> P"
    and index:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and domain_length:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_length_failure s) s
        \<le> DL"
    and sampled_domain:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_sampled_domain_failure s) s
        \<le> SD"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s
      \<le> R + (P + I + (I + DL) + (I + SD))"
proof (rule
    wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_full_cover_and_missing)
  show "wp_event verify_monad
      (composition_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    by (rule
        wp_composition_fri_bad_with_full_cover_layer_chain_bound_from_envelope
        [OF future envelope subset challenge_bound])
  show "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + (I + DL) + (I + SD)"
    by (rule
        wp_composition_fri_sampled_missing_full_cover_bound_from_domain_split
        [OF proximity index domain_length sampled_domain])
qed

lemma wp_trace_fri_header_tied_sampled_layer_chain_bound_from_envelope_witness_domain:
  assumes future: "trace_fri_future_fresh s"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and challenge_bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> R"
    and proximity:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and witness_length:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_witness_length_failure s) s \<le> W"
    and domain:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s
      \<le> R + (P + I + W + D)"
proof (rule
    wp_trace_fri_header_tied_sampled_layer_chain_bound_from_full_cover_and_missing)
  show "wp_event verify_monad
      (trace_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    by (rule wp_trace_fri_bad_with_full_cover_layer_chain_bound_from_envelope
        [OF future envelope subset challenge_bound])
  show "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s \<le> P + I + W + D"
    by (rule
        wp_trace_fri_sampled_missing_full_cover_bound_from_witness_length_subcases
        [OF proximity index witness_length domain])
qed

lemma wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_envelope_witness_domain:
  assumes future: "composition_fri_future_fresh s"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and challenge_bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> R"
    and proximity:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure s bad) s
        \<le> P"
    and index:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and witness_length:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_witness_length_failure s) s
        \<le> W"
    and domain:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s
      \<le> R + (P + I + W + D)"
proof (rule
    wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_full_cover_and_missing)
  show "wp_event verify_monad
      (composition_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    by (rule
        wp_composition_fri_bad_with_full_cover_layer_chain_bound_from_envelope
        [OF future envelope subset challenge_bound])
  show "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + W + D"
    by (rule
        wp_composition_fri_sampled_missing_full_cover_bound_from_witness_length_subcases
        [OF proximity index witness_length domain])
qed

lemma trace_fri_header_tied_residual_obligations_from_envelope_domain_split_without_head_slot_and_selected_zero:
  assumes future: "trace_fri_future_fresh s"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and challenge_bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> R"
    and proximity:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and domain_length:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_length_failure s) s \<le> DL"
    and sampled_domain:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_sampled_domain_failure s) s \<le> SD"
    and zero:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> z_b"
    and merkle:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and structural:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s
        \<le> h_b"
    and next_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> n_b"
    and successor:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> s_b"
    and total:
      "(R + (P + I + (I + DL) + (I + SD))) +
        (((((p_b + h_b) + p_b) + n_b + s_b +
          (p_b + 0 + 0)) + p_b) + 0 + z_b)
        \<le> trace_fri_error"
  shows
    "trace_fri_header_tied_residual_obligations s
      (R + (P + I + (I + DL) + (I + SD))) z_b 0 p_b h_b p_b
      n_b s_b 0"
  by (rule
      trace_fri_header_tied_residual_obligations_from_bounds_without_head_slot_and_selected_zero)
    (rule
      wp_trace_fri_header_tied_sampled_layer_chain_bound_from_envelope_domain_split
      [OF future envelope subset challenge_bound proximity index
        domain_length sampled_domain],
     rule zero, rule merkle, rule structural, rule next_bound,
     rule successor, rule total)

lemma composition_fri_verifier_tied_residual_obligations_from_envelope_domain_split_slot_zero:
  assumes future: "composition_fri_future_fresh s"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and challenge_bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> R"
    and proximity:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure s bad) s
        \<le> P"
    and index:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and domain_length:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_length_failure s) s
        \<le> DL"
    and sampled_domain:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_sampled_domain_failure s) s
        \<le> SD"
    and merkle:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and next_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap s) s \<le> n_b"
    and successor:
      "wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap s) s \<le> s_b"
    and final_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap s) s \<le> g_b"
    and total:
      "(R + (P + I + (I + DL) + (I + SD))) +
        (((p_b + 0) + n_b + s_b + g_b + p_b) + 0)
        \<le> composition_fri_error"
  shows
    "composition_fri_verifier_tied_residual_obligations s
      (R + (P + I + (I + DL) + (I + SD))) 0 p_b n_b s_b g_b"
  by (rule composition_fri_verifier_tied_residual_obligations_from_bounds_slot_zero)
    (rule
      wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_envelope_domain_split
      [OF future envelope subset challenge_bound proximity index
        domain_length sampled_domain],
     rule merkle, rule next_bound, rule successor, rule final_bound,
     rule total)

lemma trace_fri_header_tied_residual_obligations_from_envelope_witness_domain_without_head_slot_and_selected_zero:
  assumes future: "trace_fri_future_fresh s"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and challenge_bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> R"
    and proximity:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and witness_length:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_witness_length_failure s) s \<le> W"
    and domain:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and zero:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> z_b"
    and merkle:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and structural:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s
        \<le> h_b"
    and next_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> n_b"
    and successor:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> s_b"
    and total:
      "(R + (P + I + W + D)) +
        (((((p_b + h_b) + p_b) + n_b + s_b +
          (p_b + 0 + 0)) + p_b) + 0 + z_b)
        \<le> trace_fri_error"
  shows
    "trace_fri_header_tied_residual_obligations s
      (R + (P + I + W + D)) z_b 0 p_b h_b p_b n_b s_b 0"
  by (rule
      trace_fri_header_tied_residual_obligations_from_bounds_without_head_slot_and_selected_zero)
    (rule
      wp_trace_fri_header_tied_sampled_layer_chain_bound_from_envelope_witness_domain
      [OF future envelope subset challenge_bound proximity index
        witness_length domain],
     rule zero, rule merkle, rule structural, rule next_bound,
     rule successor, rule total)

lemma composition_fri_verifier_tied_residual_obligations_from_envelope_witness_domain_slot_zero:
  assumes future: "composition_fri_future_fresh s"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and challenge_bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> R"
    and proximity:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure s bad) s
        \<le> P"
    and index:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and witness_length:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_witness_length_failure s) s
        \<le> W"
    and domain:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and merkle:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and next_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap s) s \<le> n_b"
    and successor:
      "wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap s) s \<le> s_b"
    and final_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap s) s \<le> g_b"
    and total:
      "(R + (P + I + W + D)) +
        (((p_b + 0) + n_b + s_b + g_b + p_b) + 0)
        \<le> composition_fri_error"
  shows
    "composition_fri_verifier_tied_residual_obligations s
      (R + (P + I + W + D)) 0 p_b n_b s_b g_b"
  by (rule composition_fri_verifier_tied_residual_obligations_from_bounds_slot_zero)
    (rule
      wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_envelope_witness_domain
      [OF future envelope subset challenge_bound proximity index
        witness_length domain],
     rule merkle, rule next_bound, rule successor, rule final_bound,
     rule total)

end

end
