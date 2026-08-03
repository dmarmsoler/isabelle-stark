(*  Title:      Stark/Soundness_FRI_Authenticated_Route.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Authenticated_Route
  imports Soundness_FRI_Layer_Replay
begin

text \<open>
  Route-level FRI events that keep the existing public reduction shape but
  refine the sampled same-layer branch to carry authenticated Merkle evidence.
\<close>

context soundness
begin

lemma fri_first_layer_raw_bound:
  assumes roots_nonempty: "0 < length roots"
  shows
    "0 < fri_layer_lengths (length roots) (clength * scale) ! 0 \<and>
     fri_layer_indices (length roots) (index (to_nat raw))
       (clength * scale) ! 0 <
     fri_layer_lengths (length roots) (clength * scale) ! 0"
proof -
  have idx_bound: "index (to_nat raw) < clength * scale"
  proof -
    have "index (to_nat raw) < query_sample_space_size"
      by (rule index_less_query_sample_space)
    also have "... \<le> clength * scale"
      by (rule query_sample_space_size_le_domain)
    finally show ?thesis .
  qed
  show ?thesis
    using roots_nonempty idx_bound clength_pos scale_pos
    by (cases roots) simp_all
qed

lemma fri_layer_raw_bound:
  assumes layer_bound: "j < length roots"
    and eval_power: "clength * scale = 2 ^ N"
    and roots_rounds: "length roots \<le> N"
  shows
    "0 < fri_layer_lengths (length roots) (clength * scale) ! j \<and>
     fri_layer_indices (length roots) (index (to_nat raw))
       (clength * scale) ! j <
     fri_layer_lengths (length roots) (clength * scale) ! j"
proof -
  have idx_bound: "index (to_nat raw) < clength * scale"
  proof -
    have "index (to_nat raw) < query_sample_space_size"
      by (rule index_less_query_sample_space)
    also have "... \<le> clength * scale"
      by (rule query_sample_space_size_le_domain)
    finally show ?thesis .
  qed
  have idx_layer:
    "fri_layer_indices (length roots) (index (to_nat raw))
       (clength * scale) ! j <
     fri_layer_lengths (length roots) (clength * scale) ! j"
    by (rule fri_layer_indices_nth_bound
        [OF idx_bound layer_bound eval_power roots_rounds])
  have len_pos:
    "0 < fri_layer_lengths (length roots) (clength * scale) ! j"
    using idx_layer by linarith
  show ?thesis
    using len_pos idx_layer by simp
qed

definition trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        result final_state.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      out = Some (result, final_state) \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers final_state)"

definition trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out \<longleftrightarrow>
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
      generic_fri_sampled_assignment_conflict_without_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers)"

definition trace_fri_header_tied_sampled_base_opening_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_sampled_base_opening_conflict s out \<longleftrightarrow>
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
      generic_fri_sampled_base_opening_conflict trace_table trace_roots
        trace_bs fri_query_idxs trace_round_layers)"

definition trace_fri_header_tied_sampled_next_value_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_sampled_next_value_conflict s out \<longleftrightarrow>
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
      generic_fri_sampled_next_value_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers)"

definition trace_fri_header_tied_sampled_successor_opening_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_sampled_successor_opening_conflict s out \<longleftrightarrow>
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
      generic_fri_sampled_successor_opening_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers)"

definition trace_fri_header_tied_sampled_final_value_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_sampled_final_value_conflict s out \<longleftrightarrow>
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
      generic_fri_sampled_final_value_conflict trace_roots trace_bs
        trace_final fri_query_idxs trace_round_layers)"

lemma trace_fri_header_tied_without_same_imp_branch:
  assumes
    "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out"
  shows
    "trace_fri_header_tied_sampled_base_opening_conflict s out \<or>
     trace_fri_header_tied_sampled_next_value_conflict s out \<or>
     trace_fri_header_tied_sampled_successor_opening_conflict s out \<or>
     trace_fri_header_tied_sampled_final_value_conflict s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
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
    and without:
      "generic_fri_sampled_assignment_conflict_without_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers"
    unfolding
      trace_fri_header_tied_sampled_assignment_conflict_without_same_layer_def
    by blast
  have split:
    "generic_fri_sampled_base_opening_conflict trace_table trace_roots
      trace_bs fri_query_idxs trace_round_layers \<or>
     generic_fri_sampled_next_value_conflict trace_roots trace_bs
      fri_query_idxs trace_round_layers \<or>
     generic_fri_sampled_successor_opening_conflict trace_roots trace_bs
      fri_query_idxs trace_round_layers \<or>
     generic_fri_sampled_final_value_conflict trace_roots trace_bs
      trace_final fri_query_idxs trace_round_layers"
    by (rule generic_fri_sampled_assignment_conflict_without_same_layer_split
        [OF without])
  then show ?thesis
  proof
    assume base:
      "generic_fri_sampled_base_opening_conflict trace_table trace_roots
        trace_bs fri_query_idxs trace_round_layers"
    then show ?thesis
      unfolding trace_fri_header_tied_sampled_base_opening_conflict_def
      by (intro disjI1 exI conjI)
        (rule fri_openings, rule header, rule partial, rule cand,
          rule not_low, rule base)
  next
    assume rest_split:
      "generic_fri_sampled_next_value_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers \<or>
       generic_fri_sampled_successor_opening_conflict trace_roots trace_bs
        fri_query_idxs trace_round_layers \<or>
       generic_fri_sampled_final_value_conflict trace_roots trace_bs
        trace_final fri_query_idxs trace_round_layers"
    then show ?thesis
    proof
      assume next_conflict:
        "generic_fri_sampled_next_value_conflict trace_roots trace_bs
          fri_query_idxs trace_round_layers"
      then show ?thesis
        unfolding trace_fri_header_tied_sampled_next_value_conflict_def
        by (intro disjI2 disjI1 exI conjI)
          (rule fri_openings, rule header, rule partial, rule cand,
            rule not_low, rule next_conflict)
    next
      assume rest_split':
        "generic_fri_sampled_successor_opening_conflict trace_roots trace_bs
          fri_query_idxs trace_round_layers \<or>
         generic_fri_sampled_final_value_conflict trace_roots trace_bs
          trace_final fri_query_idxs trace_round_layers"
      then show ?thesis
      proof
        assume successor:
          "generic_fri_sampled_successor_opening_conflict trace_roots
            trace_bs fri_query_idxs trace_round_layers"
        then show ?thesis
          unfolding
            trace_fri_header_tied_sampled_successor_opening_conflict_def
          by (intro disjI2 disjI2 disjI1 exI conjI)
            (rule fri_openings, rule header, rule partial, rule cand,
              rule not_low, rule successor)
      next
        assume final_conflict:
          "generic_fri_sampled_final_value_conflict trace_roots trace_bs
            trace_final fri_query_idxs trace_round_layers"
        then show ?thesis
          unfolding trace_fri_header_tied_sampled_final_value_conflict_def
          by (intro disjI2 disjI2 disjI2 exI conjI)
            (rule fri_openings, rule header, rule partial, rule cand,
              rule not_low, rule final_conflict)
      qed
    qed
  qed
qed

lemma wp_trace_fri_header_tied_without_same_bound_from_branches:
  assumes base_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_base_opening_conflict s) s \<le> B"
    and next_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_next_value_conflict s) s \<le> N"
    and successor_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_successor_opening_conflict s) s \<le> S"
    and final_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_final_value_conflict s) s \<le> F"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> B + N + S + F"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_sampled_base_opening_conflict s out \<or>
          trace_fri_header_tied_sampled_next_value_conflict s out \<or>
          trace_fri_header_tied_sampled_successor_opening_conflict s out \<or>
          trace_fri_header_tied_sampled_final_value_conflict s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_without_same_imp_branch)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_base_opening_conflict s) s +
      wp_event verify_monad
        (trace_fri_header_tied_sampled_next_value_conflict s) s +
      wp_event verify_monad
        (trace_fri_header_tied_sampled_successor_opening_conflict s) s +
      wp_event verify_monad
        (trace_fri_header_tied_sampled_final_value_conflict s) s"
    by (rule wp_event_union_bound4)
  also have "... \<le> B + N + S + F"
    by (intro add_mono base_bound next_bound successor_bound final_bound)
  finally show ?thesis .
qed

lemma trace_fri_header_tied_without_sameI_base:
  assumes "trace_fri_header_tied_sampled_base_opening_conflict s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding trace_fri_header_tied_sampled_base_opening_conflict_def
    trace_fri_header_tied_sampled_assignment_conflict_without_same_layer_def
  by (blast intro:
      generic_fri_sampled_assignment_conflict_without_same_layerI_base)

lemma trace_fri_header_tied_without_sameI_next:
  assumes "trace_fri_header_tied_sampled_next_value_conflict s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding trace_fri_header_tied_sampled_next_value_conflict_def
    trace_fri_header_tied_sampled_assignment_conflict_without_same_layer_def
  by (blast intro:
      generic_fri_sampled_assignment_conflict_without_same_layerI_next)

lemma trace_fri_header_tied_without_sameI_successor:
  assumes "trace_fri_header_tied_sampled_successor_opening_conflict s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding trace_fri_header_tied_sampled_successor_opening_conflict_def
    trace_fri_header_tied_sampled_assignment_conflict_without_same_layer_def
  by (blast intro:
      generic_fri_sampled_assignment_conflict_without_same_layerI_successor)

lemma trace_fri_header_tied_without_sameI_final:
  assumes "trace_fri_header_tied_sampled_final_value_conflict s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding trace_fri_header_tied_sampled_final_value_conflict_def
    trace_fri_header_tied_sampled_assignment_conflict_without_same_layer_def
  by (blast intro:
      generic_fri_sampled_assignment_conflict_without_same_layerI_final)

lemma trace_fri_header_tied_without_same_iff_branches:
  "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer s out
    \<longleftrightarrow>
   trace_fri_header_tied_sampled_base_opening_conflict s out \<or>
   trace_fri_header_tied_sampled_next_value_conflict s out \<or>
   trace_fri_header_tied_sampled_successor_opening_conflict s out \<or>
   trace_fri_header_tied_sampled_final_value_conflict s out"
  using trace_fri_header_tied_without_same_imp_branch
    trace_fri_header_tied_without_sameI_base
    trace_fri_header_tied_without_sameI_next
    trace_fri_header_tied_without_sameI_successor
    trace_fri_header_tied_without_sameI_final
  by blast

lemma trace_fri_header_tied_base_conflict_obtains_authenticated_first_chunk:
  assumes base:
    "trace_fri_header_tied_sampled_base_opening_conflict
      s (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      round_idx xp xp_path xn xn_path auth_chunk
  where
    "accepted_fri_opening_transcript s (Some (result, final_state))
      trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr fri_query_idxs trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "\<not> trace_table_low_degree trace_table"
    "round_idx < length fri_query_idxs"
    "0 < length trace_bs"
    "fri_layer_step_evidence
      (trace_roots ! 0)
      (trace_bs ! 0)
      (fri_evidence_layer_len trace_roots 0)
      (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
      1
      (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
      xp xp_path xn xn_path
      (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
      (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
        round_idx 0 xp xn)
      (trace_round_layers ! round_idx ! 0)"
    "\<not> fri_opening_matches_table
      (fri_evidence_layer_len trace_roots 0)
      (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
      trace_table xp xn"
    "fri_layer_chunk_authenticated (trace_roots ! 0)
      (fri_evidence_layer_len trace_roots 0)
      (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
      auth_chunk final_state"
proof -
  from base obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
    where fri_openings:
      "accepted_fri_opening_transcript s (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr fri_query_idxs trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and generic:
      "generic_fri_sampled_base_opening_conflict trace_table trace_roots
        trace_bs fri_query_idxs trace_round_layers"
    unfolding trace_fri_header_tied_sampled_base_opening_conflict_def
    by blast
  from generic obtain round_idx xp xp_path xn xn_path where
    trace_bs_nonempty: "0 < length trace_bs"
    and round_bound: "round_idx < length fri_query_idxs"
    and step:
      "fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0)"
    and no_match:
      "\<not> fri_opening_matches_table
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        trace_table xp xn"
    unfolding generic_fri_sampled_base_opening_conflict_def
    by blast
  have roots_nonempty: "0 < length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings]
      trace_bs_nonempty by simp
  have round_bound_rounds: "round_idx < rounds"
    using round_bound accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
    by simp
  obtain auth_chunk where auth:
    "fri_layer_chunk_authenticated (trace_roots ! 0)
      (fri_evidence_layer_len trace_roots 0)
      (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
      auth_chunk final_state"
  proof -
    have layer_bound: "0 < length trace_roots"
      by (rule roots_nonempty)
    have raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length trace_roots) (clength * scale) ! 0 \<and>
        fri_layer_indices (length trace_roots) (index (to_nat raw))
          (clength * scale) ! 0 <
        fri_layer_lengths (length trace_roots) (clength * scale) ! 0"
      by (rule fri_first_layer_raw_bound[OF roots_nonempty])
    from accepted_fri_opening_transcript_trace_step_with_authenticated_chunk_at
        [OF fri_openings refl round_bound_rounds layer_bound raw_layer]
    obtain auth_chunk where
      "generic_fri_transcript_step_with_authenticated_chunk trace_roots
        trace_bs fri_query_idxs trace_round_layers final_state round_idx 0"
      by blast
    then obtain auth_chunk where
      "fri_layer_chunk_authenticated (trace_roots ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        auth_chunk final_state"
      by (rule generic_fri_transcript_step_with_authenticated_chunkE)
    then show ?thesis
      by (rule that)
  qed
  show ?thesis
    by (rule that[OF fri_openings header partial cand not_low round_bound
          trace_bs_nonempty step no_match auth])
qed

lemma trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer_imp_header_tied:
  assumes
    "trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
  shows "trace_fri_header_tied_sampled_assignment_conflict s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      result final_state
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and conflict:
      "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers final_state"
    unfolding
      trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
    by blast
  have sampled:
    "generic_fri_sampled_assignment_conflict trace_table trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers"
    by (rule
        generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_imp_sampled
        [OF conflict])
  show ?thesis
    unfolding trace_fri_header_tied_sampled_assignment_conflict_def
    by (intro exI conjI)
      (rule fri_openings, rule header, rule partial, rule cand,
        rule not_low, rule sampled)
qed

lemma wp_trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer_bound_from_header_tied:
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> C"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer_imp_header_tied)
  then show ?thesis
    by (rule order_trans[OF _ header_bound])
qed

definition trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks
      s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        result final_state.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      out = Some (result, final_state) \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state)"

lemma trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks_imp_partial_merkle:
  assumes
    "trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks
      s out"
  shows "partial_merkle_inconsistency_bad s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table result
      final_state
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and conflict:
      "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    unfolding
      trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks_def
    by blast
  have len: "length trace_bs = length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings] .
  have "partial_merkle_inconsistency_bad s (Some (result, final_state))"
    by (rule
        generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_imp_partial_merkle
        [OF conflict len])
  then show ?thesis
    by (simp add: out_eq)
qed

lemma wp_trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks_bound_from_partial_merkle:
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks s)
      s \<le> M"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks s)
      s \<le> wp_event verify_monad (partial_merkle_inconsistency_bad s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks_imp_partial_merkle)
  then show ?thesis
    by (rule order_trans[OF _ merkle_bound])
qed

lemma trace_fri_header_tied_authenticated_conflict_imp_without_same_or_same_layer:
  assumes
    "trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out \<or>
     trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table result
      final_state
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and conflict:
      "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers final_state"
    unfolding
      trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
    by blast
  have split:
    "generic_fri_sampled_assignment_conflict_without_same_layer
      trace_table trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers \<or>
     generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    by (rule
        generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_split
        [OF conflict])
  then show ?thesis
  proof
    assume without:
      "generic_fri_sampled_assignment_conflict_without_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers"
    then show ?thesis
      unfolding
        trace_fri_header_tied_sampled_assignment_conflict_without_same_layer_def
      by (intro disjI1 exI conjI)
        (rule fri_openings, rule header, rule partial, rule cand,
          rule not_low, rule without)
  next
    assume same:
      "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    then show ?thesis
      unfolding
        trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks_def
      by (intro disjI2 exI conjI)
        (rule fri_openings, rule out_eq, rule header, rule partial,
          rule cand, rule not_low, rule same)
  qed
qed

lemma trace_fri_header_tied_authenticated_conflictI_without_same:
  assumes
    "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
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
    and without:
      "generic_fri_sampled_assignment_conflict_without_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers"
    unfolding
      trace_fri_header_tied_sampled_assignment_conflict_without_same_layer_def
    by blast
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  have conflict:
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      trace_table trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers final_state"
    by (rule
        generic_fri_sampled_assignment_conflict_with_authenticated_same_layerI_without
        [OF without])
  show ?thesis
    unfolding
      trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
    by (intro exI conjI)
      (rule fri_openings, rule out_eq, rule header, rule partial, rule cand,
        rule not_low, rule conflict)
qed

lemma trace_fri_header_tied_authenticated_conflictI_same_layer:
  assumes
    "trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table result
      final_state
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and same:
      "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    unfolding
      trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks_def
    by blast
  have conflict:
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      trace_table trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers final_state"
    by (rule
        generic_fri_sampled_assignment_conflict_with_authenticated_same_layerI_same
        [OF same])
  show ?thesis
    unfolding
      trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
    by (intro exI conjI)
      (rule fri_openings, rule out_eq, rule header, rule partial, rule cand,
        rule not_low, rule conflict)
qed

lemma trace_fri_header_tied_authenticated_conflict_iff:
  "trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out \<longleftrightarrow>
    trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out \<or>
    trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks s out"
  using trace_fri_header_tied_authenticated_conflict_imp_without_same_or_same_layer
    trace_fri_header_tied_authenticated_conflictI_without_same
    trace_fri_header_tied_authenticated_conflictI_same_layer
  by blast

lemma wp_trace_fri_header_tied_authenticated_conflict_bound_from_without_same_and_merkle:
  assumes without_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> W"
    and merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> W + M"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
            s out \<or>
          trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks
            s out) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_authenticated_conflict_imp_without_same_or_same_layer)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer s)
        s +
      wp_event verify_monad
        (trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks s)
        s"
    by (rule wp_event_union_bound)
  also have "... \<le> W + M"
    by (rule add_mono[OF without_bound
          wp_trace_fri_header_tied_same_layer_conflict_with_authenticated_chunks_bound_from_partial_merkle
            [OF merkle_bound]])
  finally show ?thesis .
qed

definition trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table result
        final_state.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      out = Some (result, final_state) \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers final_state)"

lemma trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_imp_verifier_tied:
  assumes
    "trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
  shows "trace_fri_verifier_tied_sampled_assignment_conflict s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table result
      final_state
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and conflict:
      "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        trace_table trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers final_state"
    unfolding
      trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
    by blast
  have sampled:
    "generic_fri_sampled_assignment_conflict trace_table trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers"
    by (rule
        generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_imp_sampled
        [OF conflict])
  show ?thesis
    unfolding trace_fri_verifier_tied_sampled_assignment_conflict_def
    by (intro exI conjI)
      (rule fri_openings, rule partial, rule cand, rule not_low,
        rule sampled)
qed

lemma wp_trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_bound_from_verifier_tied:
  assumes verifier_bound:
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> C"
proof -
  have "wp_event verify_monad
      (trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le>
      wp_event verify_monad
        (trace_fri_verifier_tied_sampled_assignment_conflict s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_imp_verifier_tied)
  then show ?thesis
    by (rule order_trans[OF _ verifier_bound])
qed

definition trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
      s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr trace_openings trace_table result
        final_state.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      out = Some (result, final_state) \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state)"

lemma trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_imp_partial_merkle:
  assumes
    "trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
      s out"
  shows "partial_merkle_inconsistency_bad s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table result
      final_state
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and conflict:
      "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        trace_roots trace_bs fri_query_idxs trace_round_layers final_state"
    unfolding
      trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_def
    by blast
  have len: "length trace_bs = length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings] .
  have "partial_merkle_inconsistency_bad s (Some (result, final_state))"
    by (rule
        generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_imp_partial_merkle
        [OF conflict len])
  then show ?thesis
    by (simp add: out_eq)
qed

lemma wp_trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_bound_from_partial_merkle:
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks s)
      s \<le> M"
proof -
  have "wp_event verify_monad
      (trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks s)
      s \<le> wp_event verify_monad (partial_merkle_inconsistency_bad s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_imp_partial_merkle)
  then show ?thesis
    by (rule order_trans[OF _ merkle_bound])
qed

definition composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table result final_state.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      out = Some (result, final_state) \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        composition_table composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        final_state)"

definition composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_assignment_conflict_without_same_layer
        composition_table composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers)"

definition composition_fri_verifier_tied_sampled_base_opening_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_sampled_base_opening_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_base_opening_conflict composition_table
        composition_roots composition_bs fri_query_idxs
        composition_round_layers)"

definition composition_fri_verifier_tied_sampled_next_value_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_sampled_next_value_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_next_value_conflict composition_roots
        composition_bs fri_query_idxs composition_round_layers)"

definition composition_fri_verifier_tied_sampled_successor_opening_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_sampled_successor_opening_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_successor_opening_conflict composition_roots
        composition_bs fri_query_idxs composition_round_layers)"

definition composition_fri_verifier_tied_sampled_final_value_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_sampled_final_value_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_final_value_conflict composition_roots
        composition_bs composition_final fri_query_idxs
        composition_round_layers)"

lemma composition_fri_verifier_tied_without_same_imp_branch:
  assumes
    "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out"
  shows
    "composition_fri_verifier_tied_sampled_base_opening_conflict s out \<or>
     composition_fri_verifier_tied_sampled_next_value_conflict s out \<or>
     composition_fri_verifier_tied_sampled_successor_opening_conflict
      s out \<or>
     composition_fri_verifier_tied_sampled_final_value_conflict s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and without:
      "generic_fri_sampled_assignment_conflict_without_same_layer
        composition_table composition_roots composition_bs composition_final
        fri_query_idxs composition_round_layers"
    unfolding
      composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer_def
    by blast
  have split:
    "generic_fri_sampled_base_opening_conflict composition_table
      composition_roots composition_bs fri_query_idxs
      composition_round_layers \<or>
     generic_fri_sampled_next_value_conflict composition_roots
      composition_bs fri_query_idxs composition_round_layers \<or>
     generic_fri_sampled_successor_opening_conflict composition_roots
      composition_bs fri_query_idxs composition_round_layers \<or>
     generic_fri_sampled_final_value_conflict composition_roots
      composition_bs composition_final fri_query_idxs
      composition_round_layers"
    by (rule generic_fri_sampled_assignment_conflict_without_same_layer_split
        [OF without])
  then show ?thesis
  proof
    assume base:
      "generic_fri_sampled_base_opening_conflict composition_table
        composition_roots composition_bs fri_query_idxs
        composition_round_layers"
    then show ?thesis
      unfolding composition_fri_verifier_tied_sampled_base_opening_conflict_def
      by (intro disjI1 exI conjI)
        (rule fri_openings, rule aligned, rule trace_cand, rule comp_cand,
          rule trace_low, rule comp_not_low, rule base)
  next
    assume rest_split:
      "generic_fri_sampled_next_value_conflict composition_roots
        composition_bs fri_query_idxs composition_round_layers \<or>
       generic_fri_sampled_successor_opening_conflict composition_roots
        composition_bs fri_query_idxs composition_round_layers \<or>
       generic_fri_sampled_final_value_conflict composition_roots
        composition_bs composition_final fri_query_idxs
        composition_round_layers"
    then show ?thesis
    proof
      assume next_conflict:
        "generic_fri_sampled_next_value_conflict composition_roots
          composition_bs fri_query_idxs composition_round_layers"
      then show ?thesis
        unfolding
          composition_fri_verifier_tied_sampled_next_value_conflict_def
        by (intro disjI2 disjI1 exI conjI)
          (rule fri_openings, rule aligned, rule trace_cand, rule comp_cand,
            rule trace_low, rule comp_not_low, rule next_conflict)
    next
      assume rest_split':
        "generic_fri_sampled_successor_opening_conflict composition_roots
          composition_bs fri_query_idxs composition_round_layers \<or>
         generic_fri_sampled_final_value_conflict composition_roots
          composition_bs composition_final fri_query_idxs
          composition_round_layers"
      then show ?thesis
      proof
        assume successor:
          "generic_fri_sampled_successor_opening_conflict composition_roots
            composition_bs fri_query_idxs composition_round_layers"
        then show ?thesis
          unfolding
            composition_fri_verifier_tied_sampled_successor_opening_conflict_def
          by (intro disjI2 disjI2 disjI1 exI conjI)
            (rule fri_openings, rule aligned, rule trace_cand,
              rule comp_cand, rule trace_low, rule comp_not_low,
              rule successor)
      next
        assume final_conflict:
          "generic_fri_sampled_final_value_conflict composition_roots
            composition_bs composition_final fri_query_idxs
            composition_round_layers"
        then show ?thesis
          unfolding
            composition_fri_verifier_tied_sampled_final_value_conflict_def
          by (intro disjI2 disjI2 disjI2 exI conjI)
            (rule fri_openings, rule aligned, rule trace_cand,
              rule comp_cand, rule trace_low, rule comp_not_low,
              rule final_conflict)
      qed
    qed
  qed
qed

lemma wp_composition_fri_verifier_tied_without_same_bound_from_branches:
  assumes base_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_base_opening_conflict s) s \<le> B"
    and next_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_next_value_conflict s) s \<le> N"
    and successor_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_successor_opening_conflict s)
      s \<le> S"
    and final_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_final_value_conflict s) s \<le> F"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> B + N + S + F"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le>
      wp_event verify_monad
        (\<lambda>out.
          composition_fri_verifier_tied_sampled_base_opening_conflict
            s out \<or>
          composition_fri_verifier_tied_sampled_next_value_conflict
            s out \<or>
          composition_fri_verifier_tied_sampled_successor_opening_conflict
            s out \<or>
          composition_fri_verifier_tied_sampled_final_value_conflict
            s out) s"
    by (rule wp_event_mono)
      (rule composition_fri_verifier_tied_without_same_imp_branch)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_base_opening_conflict s) s +
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_next_value_conflict s) s +
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_successor_opening_conflict s)
        s +
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_final_value_conflict s) s"
    by (rule wp_event_union_bound4)
  also have "... \<le> B + N + S + F"
    by (intro add_mono base_bound next_bound successor_bound final_bound)
  finally show ?thesis .
qed

lemma composition_fri_verifier_tied_without_sameI_base:
  assumes "composition_fri_verifier_tied_sampled_base_opening_conflict s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding
    composition_fri_verifier_tied_sampled_base_opening_conflict_def
    composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer_def
  by (blast intro:
      generic_fri_sampled_assignment_conflict_without_same_layerI_base)

lemma composition_fri_verifier_tied_without_sameI_next:
  assumes "composition_fri_verifier_tied_sampled_next_value_conflict s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding
    composition_fri_verifier_tied_sampled_next_value_conflict_def
    composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer_def
  by (blast intro:
      generic_fri_sampled_assignment_conflict_without_same_layerI_next)

lemma composition_fri_verifier_tied_without_sameI_successor:
  assumes
    "composition_fri_verifier_tied_sampled_successor_opening_conflict s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding
    composition_fri_verifier_tied_sampled_successor_opening_conflict_def
    composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer_def
  by (blast intro:
      generic_fri_sampled_assignment_conflict_without_same_layerI_successor)

lemma composition_fri_verifier_tied_without_sameI_final:
  assumes "composition_fri_verifier_tied_sampled_final_value_conflict s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding
    composition_fri_verifier_tied_sampled_final_value_conflict_def
    composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer_def
  by (blast intro:
      generic_fri_sampled_assignment_conflict_without_same_layerI_final)

lemma composition_fri_verifier_tied_without_same_iff_branches:
  "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out
    \<longleftrightarrow>
   composition_fri_verifier_tied_sampled_base_opening_conflict s out \<or>
   composition_fri_verifier_tied_sampled_next_value_conflict s out \<or>
   composition_fri_verifier_tied_sampled_successor_opening_conflict s out \<or>
   composition_fri_verifier_tied_sampled_final_value_conflict s out"
  using composition_fri_verifier_tied_without_same_imp_branch
    composition_fri_verifier_tied_without_sameI_base
    composition_fri_verifier_tied_without_sameI_next
    composition_fri_verifier_tied_without_sameI_successor
    composition_fri_verifier_tied_without_sameI_final
  by blast

lemma composition_fri_verifier_tied_base_conflict_obtains_authenticated_first_chunk:
  assumes base:
    "composition_fri_verifier_tied_sampled_base_opening_conflict
      s (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table round_idx xp xp_path xn xn_path
      auth_chunk
  where
    "accepted_fri_opening_transcript s (Some (result, final_state))
      trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    "accepted_with_partial_initial_openings_aligned s
      (Some (result, final_state)) fr trace_roots trace_final as fri_dg
      composition_roots composition_final fri_query_idxs trace_openings
      composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "trace_table_low_degree trace_table"
    "\<not> composition_table_low_degree maxDegree composition_table"
    "round_idx < length fri_query_idxs"
    "0 < length composition_bs"
    "fri_layer_step_evidence
      (composition_roots ! 0)
      (composition_bs ! 0)
      (fri_evidence_layer_len composition_roots 0)
      (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
      1
      (fri_sibling_index (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0))
      xp xp_path xn xn_path
      (fri_evidence_next_idx composition_roots fri_query_idxs round_idx 0)
      (fri_evidence_next_value composition_roots composition_bs
        fri_query_idxs round_idx 0 xp xn)
      (composition_round_layers ! round_idx ! 0)"
    "\<not> fri_opening_matches_table
      (fri_evidence_layer_len composition_roots 0)
      (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
      composition_table xp xn"
    "fri_layer_chunk_authenticated (composition_roots ! 0)
      (fri_evidence_layer_len composition_roots 0)
      (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
      auth_chunk final_state"
proof -
  from base obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table
    where fri_openings:
      "accepted_fri_opening_transcript s (Some (result, final_state))
        trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s
        (Some (result, final_state)) fr trace_roots trace_final as fri_dg
        composition_roots composition_final fri_query_idxs trace_openings
        composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and generic:
      "generic_fri_sampled_base_opening_conflict composition_table
        composition_roots composition_bs fri_query_idxs
        composition_round_layers"
    unfolding composition_fri_verifier_tied_sampled_base_opening_conflict_def
    by blast
  from generic obtain round_idx xp xp_path xn xn_path where
    composition_bs_nonempty: "0 < length composition_bs"
    and round_bound: "round_idx < length fri_query_idxs"
    and step:
      "fri_layer_step_evidence
        (composition_roots ! 0)
        (composition_bs ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len composition_roots 0)
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx composition_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value composition_roots composition_bs
          fri_query_idxs round_idx 0 xp xn)
        (composition_round_layers ! round_idx ! 0)"
    and no_match:
      "\<not> fri_opening_matches_table
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        composition_table xp xn"
    unfolding generic_fri_sampled_base_opening_conflict_def
    by blast
  have roots_nonempty: "0 < length composition_roots"
    using accepted_fri_opening_transcript_shapes(4)[OF fri_openings]
      composition_bs_nonempty by simp
  have round_bound_rounds: "round_idx < rounds"
    using round_bound accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
    by simp
  obtain auth_chunk where auth:
    "fri_layer_chunk_authenticated (composition_roots ! 0)
      (fri_evidence_layer_len composition_roots 0)
      (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
      auth_chunk final_state"
  proof -
    have layer_bound: "0 < length composition_roots"
      by (rule roots_nonempty)
    have raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length composition_roots) (clength * scale) ! 0 \<and>
        fri_layer_indices (length composition_roots) (index (to_nat raw))
          (clength * scale) ! 0 <
        fri_layer_lengths (length composition_roots) (clength * scale) ! 0"
      by (rule fri_first_layer_raw_bound[OF roots_nonempty])
    from accepted_fri_opening_transcript_composition_step_with_authenticated_chunk_at
        [OF fri_openings refl round_bound_rounds layer_bound raw_layer]
    obtain auth_chunk where
      "generic_fri_transcript_step_with_authenticated_chunk composition_roots
        composition_bs fri_query_idxs composition_round_layers final_state
        round_idx 0"
      by blast
    then obtain auth_chunk where
      "fri_layer_chunk_authenticated (composition_roots ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        auth_chunk final_state"
      by (rule generic_fri_transcript_step_with_authenticated_chunkE)
    then show ?thesis
      by (rule that)
  qed
  show ?thesis
    by (rule that[OF fri_openings aligned trace_cand comp_cand trace_low
          comp_not_low round_bound composition_bs_nonempty step no_match auth])
qed

definition composition_fri_verifier_tied_authenticated_base_opening_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_authenticated_base_opening_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table round_idx xp xp_path xn xn_path
        result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      round_idx < length fri_query_idxs \<and>
      0 < length composition_bs \<and>
      fri_layer_step_evidence
        (composition_roots ! 0)
        (composition_bs ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len composition_roots 0)
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx composition_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value composition_roots composition_bs
          fri_query_idxs round_idx 0 xp xn)
        (composition_round_layers ! round_idx ! 0) \<and>
      \<not> fri_opening_matches_table
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        composition_table xp xn \<and>
      fri_layer_chunk_authenticated (composition_roots ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        (composition_round_layers ! round_idx ! 0) final_state)"

definition composition_fri_verifier_tied_base_chunk_auth_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_base_chunk_auth_gap s out \<longleftrightarrow>
    composition_fri_verifier_tied_sampled_base_opening_conflict s out \<and>
    \<not> composition_fri_verifier_tied_authenticated_base_opening_conflict
      s out"

lemma composition_fri_verifier_tied_sampled_base_imp_authenticated_or_auth_gap:
  assumes
    "composition_fri_verifier_tied_sampled_base_opening_conflict s out"
  shows
    "composition_fri_verifier_tied_authenticated_base_opening_conflict s out \<or>
     composition_fri_verifier_tied_base_chunk_auth_gap s out"
  using assms
  unfolding composition_fri_verifier_tied_base_chunk_auth_gap_def
  by blast

lemma wp_composition_fri_verifier_tied_sampled_base_bound_from_authenticated_and_auth_gap:
  fixes A G :: prob
  assumes authenticated_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_base_opening_conflict s)
      s \<le> A"
    and gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_base_chunk_auth_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_base_opening_conflict s) s
      \<le> A + G"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_base_opening_conflict s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          composition_fri_verifier_tied_authenticated_base_opening_conflict
            s out \<or>
          composition_fri_verifier_tied_base_chunk_auth_gap s out) s"
    by (rule wp_event_mono)
      (rule composition_fri_verifier_tied_sampled_base_imp_authenticated_or_auth_gap)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_base_opening_conflict s) s +
      wp_event verify_monad
        (composition_fri_verifier_tied_base_chunk_auth_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> A + G"
    by (intro add_mono authenticated_bound gap_bound)
  finally show ?thesis .
qed

lemma composition_fri_verifier_tied_authenticated_base_conflict_imp_sampled_base:
  assumes
    "composition_fri_verifier_tied_authenticated_base_opening_conflict s out"
  shows "composition_fri_verifier_tied_sampled_base_opening_conflict s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table round_idx xp xp_path xn xn_path
      result final_state
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and round_bound: "round_idx < length fri_query_idxs"
    and composition_bs_nonempty: "0 < length composition_bs"
    and step:
      "fri_layer_step_evidence
        (composition_roots ! 0)
        (composition_bs ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len composition_roots 0)
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx composition_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value composition_roots composition_bs
          fri_query_idxs round_idx 0 xp xn)
        (composition_round_layers ! round_idx ! 0)"
    and no_match:
      "\<not> fri_opening_matches_table
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        composition_table xp xn"
    and auth:
      "fri_layer_chunk_authenticated (composition_roots ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        (composition_round_layers ! round_idx ! 0) final_state"
    unfolding
      composition_fri_verifier_tied_authenticated_base_opening_conflict_def
    by auto
  have base:
    "generic_fri_sampled_base_opening_conflict composition_table
      composition_roots composition_bs fri_query_idxs composition_round_layers"
    unfolding generic_fri_sampled_base_opening_conflict_def
    by (intro exI[of _ round_idx] exI[of _ xp] exI[of _ xp_path]
        exI[of _ xn] exI[of _ xn_path] conjI)
      (use round_bound composition_bs_nonempty step no_match in auto)
  show ?thesis
    unfolding composition_fri_verifier_tied_sampled_base_opening_conflict_def
    by (intro exI conjI)
      (use out_eq fri_openings aligned trace_cand comp_cand trace_low
        comp_not_low base in auto)
qed

lemma composition_fri_verifier_tied_authenticated_base_conflict_imp_partial_merkle:
  assumes base:
    "composition_fri_verifier_tied_authenticated_base_opening_conflict
      s (Some (result, final_state))"
  shows
    "partial_merkle_inconsistency_bad s (Some (result, final_state))"
proof -
  show ?thesis
  proof (rule ccontr)
    assume no_bad:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
    obtain trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table round_idx xp xp_path xn xn_path
      where aligned:
        "accepted_with_partial_initial_openings_aligned s
          (Some (result, final_state)) fr trace_roots trace_final as fri_dg
          composition_roots composition_final fri_query_idxs trace_openings
          composition_openings"
      and comp_cand:
        "partial_composition_table_candidate composition_table
          composition_openings"
      and round_bound: "round_idx < length fri_query_idxs"
      and step:
        "fri_layer_step_evidence
          (composition_roots ! 0)
          (composition_bs ! 0)
          (fri_evidence_layer_len composition_roots 0)
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
          1
          (fri_sibling_index (fri_evidence_layer_len composition_roots 0)
            (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0))
          xp xp_path xn xn_path
          (fri_evidence_next_idx composition_roots fri_query_idxs round_idx 0)
          (fri_evidence_next_value composition_roots composition_bs
            fri_query_idxs round_idx 0 xp xn)
          (composition_round_layers ! round_idx ! 0)"
      and no_match:
        "\<not> fri_opening_matches_table
          (fri_evidence_layer_len composition_roots 0)
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
          composition_table xp xn"
      and auth:
        "fri_layer_chunk_authenticated (composition_roots ! 0)
          (fri_evidence_layer_len composition_roots 0)
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
          (composition_round_layers ! round_idx ! 0) final_state"
      using base
      unfolding
        composition_fri_verifier_tied_authenticated_base_opening_conflict_def
      by blast
    have initial:
      "accepted_with_partial_initial_openings s
        (Some (result, final_state)) fr trace_roots trace_final as fri_dg
        composition_roots composition_final fri_query_idxs trace_openings
        fri_query_idxs composition_openings"
      by (rule accepted_with_partial_initial_openings_aligned_imp_unaligned
          [OF aligned])
    have comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_roots) fri_query_idxs
        composition_openings"
      by (rule accepted_with_partial_initial_openings_shapes(4)
          [OF initial])
    have roots_nonempty: "composition_roots \<noteq> []"
      by (rule accepted_with_partial_initial_openings_shapes(1)[OF initial])
    have round_bound_rounds: "round_idx < rounds"
      using round_bound
        accepted_with_partial_composition_openings_shapes(1)[OF comp_partial]
      by simp
    let ?idx =
      "fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0"
    have idx_eq:
      "?idx = fri_query_idxs ! round_idx"
      unfolding fri_evidence_layer_idx_def
      using roots_nonempty by (cases composition_roots) simp_all
    have len_eq:
      "fri_evidence_layer_len composition_roots 0 = scale * clength"
      unfolding fri_evidence_layer_len_def
      using roots_nonempty by (cases composition_roots) simp_all
    have root_eq: "composition_roots ! 0 = hd composition_roots"
      using roots_nonempty by (cases composition_roots) simp_all
    have idxs:
      "map opening_index (composition_openings ! round_idx) =
        [?idx, fri_sibling_index (scale * clength) ?idx]"
      using accepted_with_partial_composition_openings_shapes(3)
          [OF comp_partial round_bound_rounds]
      unfolding idx_eq by simp
    have comp_value:
      "composition_table ! ?idx =
        opening_value ((composition_openings ! round_idx) ! 0)"
      by (rule partial_composition_table_candidate_query_value
          [OF comp_cand round_bound_rounds idxs])
    have len_openings: "length (composition_openings ! round_idx) = 2"
    proof -
      have "length (map opening_index (composition_openings ! round_idx)) =
        length [?idx, fri_sibling_index (scale * clength) ?idx]"
        using arg_cong[OF idxs, of length] by simp
      then show ?thesis by simp
    qed
    have opn0_in:
      "(composition_openings ! round_idx) ! 0
        \<in> set (composition_openings ! round_idx)"
      using len_openings by (cases "composition_openings ! round_idx") auto
    have opn1_in:
      "(composition_openings ! round_idx) ! 1
        \<in> set (composition_openings ! round_idx)"
      using len_openings
      by (cases "composition_openings ! round_idx"; cases "tl (composition_openings ! round_idx)")
        auto
    have comp_table:
      "partial_authenticated_table (hd composition_roots) (scale * clength)
        (composition_openings ! round_idx) final_state"
      using comp_partial round_bound_rounds
      unfolding accepted_with_partial_composition_openings_def by blast
    have opn0_auth:
      "authenticated_opening_in final_state
        ((composition_openings ! round_idx) ! 0)"
      using comp_table opn0_in
      unfolding partial_authenticated_table_def by blast
    have opn0_root:
      "opening_root ((composition_openings ! round_idx) ! 0) =
        composition_roots ! 0"
      using comp_table opn0_in root_eq
      unfolding partial_authenticated_table_def by simp
    have opn0_len:
      "opening_length ((composition_openings ! round_idx) ! 0) =
        fri_evidence_layer_len composition_roots 0"
      using comp_table opn0_in len_eq
      unfolding partial_authenticated_table_def by simp
    have opn0_idx:
      "opening_index ((composition_openings ! round_idx) ! 0) = ?idx"
      using idxs len_openings by (cases "composition_openings ! round_idx") auto
    have opn0_value: "opening_value ((composition_openings ! round_idx) ! 0) = xp"
    proof -
      from step have chunk:
        "fri_layer_opening_chunk
          (fri_evidence_layer_len composition_roots 0)
          xp xp_path xn xn_path
          (composition_round_layers ! round_idx ! 0)"
        unfolding fri_layer_step_evidence_def by blast
      from fri_layer_chunk_authenticated_matching_values[OF auth chunk]
      obtain xp_path' xn_path' where xp_auth:
        "authenticated_opening_in final_state
          \<lparr>opening_root = composition_roots ! 0,
           opening_length = fri_evidence_layer_len composition_roots 0,
           opening_index =
            fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0,
           opening_value = xp,
           opening_path = xp_path'\<rparr>"
        by (metis)
      have "opening_value ((composition_openings ! round_idx) ! 0) =
        opening_value
          \<lparr>opening_root = composition_roots ! 0,
           opening_length = fri_evidence_layer_len composition_roots 0,
           opening_index =
            fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0,
           opening_value = xp,
           opening_path = xp_path'\<rparr>"
        by (rule authenticated_openings_values_eq_if_no_partial_merkle
            [OF no_bad opn0_auth xp_auth])
          (use opn0_root opn0_len opn0_idx in simp_all)
      then show ?thesis by simp
    qed
    have comp_match_base: "composition_table ! ?idx = xp"
      using comp_value opn0_value by simp
    have comp_sibling:
      "composition_table ! fri_sibling_index (scale * clength) ?idx =
        opening_value ((composition_openings ! round_idx) ! 1)"
    proof -
      have vals:
        "map ((!) composition_table)
            [?idx, fri_sibling_index (scale * clength) ?idx] =
          map opening_value (composition_openings ! round_idx)"
        by (rule partial_composition_table_candidate_query_values
            [OF comp_cand round_bound_rounds idxs])
      have lhs:
        "map ((!) composition_table)
            [?idx, fri_sibling_index (scale * clength) ?idx] ! 1 =
          composition_table ! fri_sibling_index (scale * clength) ?idx"
        by simp
      have rhs:
        "map opening_value (composition_openings ! round_idx) ! 1 =
          opening_value ((composition_openings ! round_idx) ! 1)"
        using len_openings by simp
      show ?thesis
        using arg_cong[OF vals, of "\<lambda>xs. xs ! 1"] lhs rhs by simp
    qed
    have opn1_auth:
      "authenticated_opening_in final_state
        ((composition_openings ! round_idx) ! 1)"
      using comp_table opn1_in
      unfolding partial_authenticated_table_def by blast
    have opn1_root:
      "opening_root ((composition_openings ! round_idx) ! 1) =
        composition_roots ! 0"
      using comp_table opn1_in root_eq
      unfolding partial_authenticated_table_def by simp
    have opn1_len:
      "opening_length ((composition_openings ! round_idx) ! 1) =
        fri_evidence_layer_len composition_roots 0"
      using comp_table opn1_in len_eq
      unfolding partial_authenticated_table_def by simp
    have opn1_idx:
      "opening_index ((composition_openings ! round_idx) ! 1) =
        fri_sibling_index (fri_evidence_layer_len composition_roots 0) ?idx"
      using idxs len_openings len_eq
      by (cases "composition_openings ! round_idx"; cases "tl (composition_openings ! round_idx)")
        auto
    have opn1_value: "opening_value ((composition_openings ! round_idx) ! 1) = xn"
    proof -
      from step have chunk:
        "fri_layer_opening_chunk
          (fri_evidence_layer_len composition_roots 0)
          xp xp_path xn xn_path
          (composition_round_layers ! round_idx ! 0)"
        unfolding fri_layer_step_evidence_def by blast
      from fri_layer_chunk_authenticated_matching_values[OF auth chunk]
      obtain xp_path' xn_path' where xn_auth:
        "authenticated_opening_in final_state
          \<lparr>opening_root = composition_roots ! 0,
           opening_length = fri_evidence_layer_len composition_roots 0,
           opening_index =
            fri_sibling_index (fri_evidence_layer_len composition_roots 0)
              (fri_evidence_layer_idx composition_roots fri_query_idxs
                round_idx 0),
           opening_value = xn,
           opening_path = xn_path'\<rparr>"
        by (metis)
      have "opening_value ((composition_openings ! round_idx) ! 1) =
        opening_value
          \<lparr>opening_root = composition_roots ! 0,
           opening_length = fri_evidence_layer_len composition_roots 0,
           opening_index =
            fri_sibling_index (fri_evidence_layer_len composition_roots 0)
              (fri_evidence_layer_idx composition_roots fri_query_idxs
                round_idx 0),
           opening_value = xn,
           opening_path = xn_path'\<rparr>"
        by (rule authenticated_openings_values_eq_if_no_partial_merkle
            [OF no_bad opn1_auth xn_auth])
          (use opn1_root opn1_len opn1_idx in simp_all)
      then show ?thesis by simp
    qed
    have comp_match_sibling:
      "composition_table !
        fri_sibling_index (fri_evidence_layer_len composition_roots 0) ?idx =
       xn"
      using comp_sibling opn1_value len_eq by simp
    have idx_bound: "?idx < fri_evidence_layer_len composition_roots 0"
    proof -
      from auth obtain xp0 xp0_path xn0 xn0_path where
        "authenticated_opening_in final_state
          \<lparr>opening_root = composition_roots ! 0,
           opening_length = fri_evidence_layer_len composition_roots 0,
           opening_index = ?idx,
           opening_value = xp0,
           opening_path = xp0_path\<rparr>"
        by (rule fri_layer_chunk_authenticatedE)
      then show ?thesis
        unfolding authenticated_opening_in_def by simp
    qed
    have table_len:
      "fri_evidence_layer_len composition_roots 0 \<le>
        length composition_table"
      using partial_composition_table_candidateD(1)
          [OF comp_cand round_bound_rounds opn0_in]
      unfolding len_eq by simp
    have match:
      "fri_opening_matches_table
        (fri_evidence_layer_len composition_roots 0)
        ?idx composition_table xp xn"
      unfolding fri_opening_matches_table_def
      using idx_bound table_len comp_match_base comp_match_sibling
      by simp
    then show False
      using no_match by contradiction
  qed
qed

lemma wp_composition_fri_verifier_tied_authenticated_base_conflict_bound_by_partial_merkle:
  "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_base_opening_conflict s) s
    \<le> wp_event verify_monad (partial_merkle_inconsistency_bad s) s"
proof (rule wp_event_mono)
  fix out
  assume conflict:
    "composition_fri_verifier_tied_authenticated_base_opening_conflict s out"
  from conflict obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding composition_fri_verifier_tied_authenticated_base_opening_conflict_def
    by blast
  show "partial_merkle_inconsistency_bad s out"
    unfolding out_eq
    by (rule composition_fri_verifier_tied_authenticated_base_conflict_imp_partial_merkle)
      (use conflict out_eq in simp)
qed

lemma wp_composition_fri_verifier_tied_sampled_base_bound_from_partial_merkle_and_auth_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_base_chunk_auth_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_base_opening_conflict s) s
      \<le> wp_event verify_monad (partial_merkle_inconsistency_bad s) s + G"
proof (rule wp_composition_fri_verifier_tied_sampled_base_bound_from_authenticated_and_auth_gap)
  show "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_base_opening_conflict s) s
      \<le> wp_event verify_monad (partial_merkle_inconsistency_bad s) s"
    by (rule wp_composition_fri_verifier_tied_authenticated_base_conflict_bound_by_partial_merkle)
  show "wp_event verify_monad
      (composition_fri_verifier_tied_base_chunk_auth_gap s) s \<le> G"
    by (rule gap_bound)
qed

lemma wp_composition_fri_verifier_tied_without_same_bound_from_partial_merkle_auth_gap_and_branches:
  fixes G N S F :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_base_chunk_auth_gap s) s \<le> G"
    and next_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_next_value_conflict s) s \<le> N"
    and successor_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_successor_opening_conflict s)
        s \<le> S"
    and final_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_final_value_conflict s) s \<le> F"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> (wp_event verify_monad (partial_merkle_inconsistency_bad s) s + G) + N + S + F"
  by (rule wp_composition_fri_verifier_tied_without_same_bound_from_branches)
    (rule wp_composition_fri_verifier_tied_sampled_base_bound_from_partial_merkle_and_auth_gap
      [OF gap_bound],
     rule next_bound,
     rule successor_bound,
     rule final_bound)

lemma composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_imp_verifier_tied:
  assumes
    "composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
  shows "composition_fri_verifier_tied_sampled_assignment_conflict s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table result final_state
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and conflict:
      "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        composition_table composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        final_state"
    unfolding
      composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
    by blast
  have sampled:
    "generic_fri_sampled_assignment_conflict composition_table
      composition_roots composition_bs composition_final fri_query_idxs
      composition_round_layers"
    by (rule
        generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_imp_sampled
        [OF conflict])
  show ?thesis
    unfolding composition_fri_verifier_tied_sampled_assignment_conflict_def
    by (intro exI conjI)
      (rule fri_openings, rule aligned, rule trace_cand, rule comp_cand,
        rule trace_low, rule comp_not_low, rule sampled)
qed

lemma wp_composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_bound_from_verifier_tied:
  assumes verifier_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> C"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict s) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_imp_verifier_tied)
  then show ?thesis
    by (rule order_trans[OF _ verifier_bound])
qed

definition composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
      s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table result final_state.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      out = Some (result, final_state) \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        composition_roots composition_bs fri_query_idxs
        composition_round_layers final_state)"

lemma composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_imp_partial_merkle:
  assumes
    "composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
      s out"
  shows "partial_merkle_inconsistency_bad s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table result final_state
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and conflict:
      "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        composition_roots composition_bs fri_query_idxs
        composition_round_layers final_state"
    unfolding
      composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_def
    by blast
  have len: "length composition_bs = length composition_roots"
    using accepted_fri_opening_transcript_shapes(4)[OF fri_openings] .
  have "partial_merkle_inconsistency_bad s (Some (result, final_state))"
    by (rule
        generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_imp_partial_merkle
        [OF conflict len])
  then show ?thesis
    by (simp add: out_eq)
qed

lemma wp_composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_bound_from_partial_merkle:
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks s)
      s \<le> M"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks s)
      s \<le> wp_event verify_monad (partial_merkle_inconsistency_bad s) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_imp_partial_merkle)
  then show ?thesis
    by (rule order_trans[OF _ merkle_bound])
qed

lemma composition_fri_verifier_tied_authenticated_conflict_imp_without_same_or_same_layer:
  assumes
    "composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out \<or>
     composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
      s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table result final_state
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and conflict:
      "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        composition_table composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        final_state"
    unfolding
      composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
    by blast
  have split:
    "generic_fri_sampled_assignment_conflict_without_same_layer
      composition_table composition_roots composition_bs composition_final
      fri_query_idxs composition_round_layers \<or>
     generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      composition_roots composition_bs fri_query_idxs composition_round_layers
      final_state"
    by (rule
        generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_split
        [OF conflict])
  then show ?thesis
  proof
    assume without:
      "generic_fri_sampled_assignment_conflict_without_same_layer
        composition_table composition_roots composition_bs composition_final
        fri_query_idxs composition_round_layers"
    then show ?thesis
      unfolding
        composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer_def
      by (intro disjI1 exI conjI)
        (rule fri_openings, rule aligned, rule trace_cand, rule comp_cand,
          rule trace_low, rule comp_not_low, rule without)
  next
    assume same:
      "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        composition_roots composition_bs fri_query_idxs
        composition_round_layers final_state"
    then show ?thesis
      unfolding
        composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_def
      by (intro disjI2 exI conjI)
        (rule fri_openings, rule out_eq, rule aligned, rule trace_cand,
          rule comp_cand, rule trace_low, rule comp_not_low, rule same)
  qed
qed

lemma composition_fri_verifier_tied_authenticated_conflictI_without_same:
  assumes
    "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and without:
      "generic_fri_sampled_assignment_conflict_without_same_layer
        composition_table composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers"
    unfolding
      composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer_def
    by blast
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  have conflict:
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      composition_table composition_roots composition_bs composition_final
      fri_query_idxs composition_round_layers final_state"
    by (rule
        generic_fri_sampled_assignment_conflict_with_authenticated_same_layerI_without
        [OF without])
  show ?thesis
    unfolding
      composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
    by (intro exI conjI)
      (rule fri_openings, rule out_eq, rule aligned, rule trace_cand,
        rule comp_cand, rule trace_low, rule comp_not_low, rule conflict)
qed

lemma composition_fri_verifier_tied_authenticated_conflictI_same_layer:
  assumes
    "composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
      s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table result final_state
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and same:
      "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        composition_roots composition_bs fri_query_idxs
        composition_round_layers final_state"
    unfolding
      composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_def
    by blast
  have conflict:
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      composition_table composition_roots composition_bs composition_final
      fri_query_idxs composition_round_layers final_state"
    by (rule
        generic_fri_sampled_assignment_conflict_with_authenticated_same_layerI_same
        [OF same])
  show ?thesis
    unfolding
      composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
    by (intro exI conjI)
      (rule fri_openings, rule out_eq, rule aligned, rule trace_cand,
        rule comp_cand, rule trace_low, rule comp_not_low, rule conflict)
qed

lemma composition_fri_verifier_tied_authenticated_conflict_iff:
  "composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out \<longleftrightarrow>
    composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out \<or>
    composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
      s out"
  using composition_fri_verifier_tied_authenticated_conflict_imp_without_same_or_same_layer
    composition_fri_verifier_tied_authenticated_conflictI_without_same
    composition_fri_verifier_tied_authenticated_conflictI_same_layer
  by blast

lemma wp_composition_fri_verifier_tied_authenticated_conflict_bound_from_without_same_and_merkle:
  assumes without_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> W"
    and merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> W + M"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le>
      wp_event verify_monad
        (\<lambda>out.
          composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
            s out \<or>
          composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks
            s out) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_authenticated_conflict_imp_without_same_or_same_layer)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer s)
        s +
      wp_event verify_monad
        (composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks s)
        s"
    by (rule wp_event_union_bound)
  also have "... \<le> W + M"
    by (rule add_mono[OF without_bound
          wp_composition_fri_verifier_tied_same_layer_conflict_with_authenticated_chunks_bound_from_partial_merkle
            [OF merkle_bound]])
  finally show ?thesis .
qed

end

end
