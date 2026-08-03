(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Classification.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Classification
  imports Staged_Security_Experiment_Composition_Query_Prefix_Witness
begin

text \<open>
  Local classification lemmas for current-final-state partial-opening evidence.
  These lemmas deliberately live downstream of the fixed-witness bridge to avoid
  growing the size-sensitive prefix-witness theory.
\<close>

context soundness
begin

lemma trace_fri_bad_with_updated_partial_candidatesI:
  assumes updated:
      "accepted_with_partial_initial_openings s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
  shows "trace_fri_bad_with_partial_candidates s
    (Some (result, final_state))"
  using assms
  unfolding trace_fri_bad_with_partial_candidates_def by blast

lemma composition_fri_bad_with_updated_partial_candidatesI:
  assumes updated:
      "accepted_with_partial_initial_openings s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and not_comp_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
  shows "composition_fri_bad_with_partial_candidates s
    (Some (result, final_state))"
  using assms
  unfolding composition_fri_bad_with_partial_candidates_def by blast

lemma query_bad_with_updated_partial_candidatesI:
  assumes updated:
      "accepted_with_partial_initial_openings s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all: "\<not> all_queries_consistent trace_table composition_table as"
  shows "query_bad_with_partial_candidates s (Some (result, final_state))"
  using assms
  unfolding query_bad_with_partial_candidates_def by blast

lemma accepted_with_partial_initial_openings_update_round_candidate_classification:
  assumes partial:
      "accepted_with_partial_initial_openings s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad s (Some (result, final_state))"
    and i_bound: "i < rounds"
    and same_idx: "trace_query_idxs ! i = composition_query_idxs ! i"
    and consistent:
      "partial_query_openings_consistent trace_openings_i
        composition_openings_i as (trace_query_idxs ! i)"
    and trace_auth:
      "partial_authenticated_table fr (scale * clength) trace_openings_i
        final_state"
    and comp_auth:
      "partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) composition_openings_i final_state"
  shows
    "trace_fri_bad_with_partial_candidates s (Some (result, final_state)) \<or>
     composition_fri_bad_with_partial_candidates s
      (Some (result, final_state)) \<or>
     query_bad_with_partial_candidates s (Some (result, final_state)) \<or>
     (\<exists>trace_table composition_table.
      partial_trace_table_candidate trace_table
        (trace_openings[i := trace_openings_i]) \<and>
      partial_composition_table_candidate composition_table
        (composition_openings[i := composition_openings_i]) \<and>
      trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as)"
proof -
  let ?trace_openings = "trace_openings[i := trace_openings_i]"
  let ?composition_openings =
    "composition_openings[i := composition_openings_i]"
  have updated:
    "accepted_with_partial_initial_openings s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs ?trace_openings
      composition_query_idxs ?composition_openings"
    by (rule accepted_with_partial_initial_openings_update_round
        [OF partial i_bound same_idx consistent trace_auth comp_auth])
  obtain trace_table composition_table where trace_candidate:
      "partial_trace_table_candidate trace_table ?trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ?composition_openings"
    using accepted_with_partial_initial_openings_candidates_if_no_partial_merkle_bad
        [OF updated no_bad]
    by blast
  show ?thesis
  proof (cases "trace_table_low_degree trace_table")
    case False
    then have "trace_fri_bad_with_partial_candidates s
        (Some (result, final_state))"
      by (rule trace_fri_bad_with_updated_partial_candidatesI
          [OF updated trace_candidate])
    then show ?thesis by simp
  next
    case trace_low: True
    show ?thesis
    proof (cases "composition_table_low_degree maxDegree composition_table")
      case False
      then have "composition_fri_bad_with_partial_candidates s
          (Some (result, final_state))"
        by (rule composition_fri_bad_with_updated_partial_candidatesI
            [OF updated trace_candidate comp_candidate trace_low])
      then show ?thesis by simp
    next
      case comp_low: True
      show ?thesis
      proof (cases "all_queries_consistent trace_table composition_table as")
        case False
        then have "query_bad_with_partial_candidates s
            (Some (result, final_state))"
          by (rule query_bad_with_updated_partial_candidatesI
              [OF updated trace_candidate comp_candidate trace_low comp_low])
        then show ?thesis by simp
      next
        case True
        then show ?thesis
          using trace_candidate comp_candidate trace_low comp_low by blast
      qed
    qed
  qed
qed

lemma accepted_with_partial_initial_openings_aligned_consistent_update_round_candidate_classification:
  assumes partial:
      "accepted_with_partial_initial_openings_aligned_consistent s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad s (Some (result, final_state))"
    and i_bound: "i < rounds"
    and consistent:
      "partial_query_openings_consistent trace_openings_i
        composition_openings_i as (query_idxs ! i)"
    and trace_auth:
      "partial_authenticated_table fr (scale * clength) trace_openings_i
        final_state"
    and comp_auth:
      "partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) composition_openings_i final_state"
  shows
    "trace_fri_bad_with_partial_candidates s (Some (result, final_state)) \<or>
     composition_fri_bad_with_partial_candidates s
      (Some (result, final_state)) \<or>
     query_bad_with_partial_candidates s (Some (result, final_state)) \<or>
     (\<exists>trace_table composition_table.
      partial_trace_table_candidate trace_table
        (trace_openings[i := trace_openings_i]) \<and>
      partial_composition_table_candidate composition_table
        (composition_openings[i := composition_openings_i]) \<and>
      trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as)"
proof -
  have aligned:
    "accepted_with_partial_initial_openings_aligned s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    using partial
    unfolding accepted_with_partial_initial_openings_aligned_consistent_def
    by simp
  have unaligned:
    "accepted_with_partial_initial_openings s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings query_idxs
      composition_openings"
    by (rule accepted_with_partial_initial_openings_aligned_imp_unaligned
        [OF aligned])
  show ?thesis
    by (rule
        accepted_with_partial_initial_openings_update_round_candidate_classification
        [OF unaligned no_bad i_bound _ consistent trace_auth comp_auth])
      simp
qed

lemma accepted_with_partial_initial_openings_aligned_transcript_consistent_update_round_candidate_classification:
  assumes partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad s (Some (result, final_state))"
    and i_bound: "i < rounds"
    and consistent:
      "partial_query_openings_consistent trace_openings_i
        composition_openings_i as (query_idxs ! i)"
    and trace_auth:
      "partial_authenticated_table fr (scale * clength) trace_openings_i
        final_state"
    and comp_auth:
      "partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) composition_openings_i final_state"
  shows
    "trace_fri_bad_with_partial_candidates s (Some (result, final_state)) \<or>
     composition_fri_bad_with_partial_candidates s
      (Some (result, final_state)) \<or>
     query_bad_with_partial_candidates s (Some (result, final_state)) \<or>
     (\<exists>trace_table composition_table.
      partial_trace_table_candidate trace_table
        (trace_openings[i := trace_openings_i]) \<and>
      partial_composition_table_candidate composition_table
        (composition_openings[i := composition_openings_i]) \<and>
      trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as)"
proof -
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  show ?thesis
    by (rule
        accepted_with_partial_initial_openings_aligned_consistent_update_round_candidate_classification
        [OF aligned no_bad i_bound consistent trace_auth comp_auth])
qed

end

end
