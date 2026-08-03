(*  Title:      Stark/Soundness_FRI_Partial_Evidence.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Partial_Evidence
  imports Soundness_Relevant_Drift_Reachable_FRI
begin

text \<open>
  Normalized partial-opening FRI evidence predicates for the reachable-state
  FRI obligations.

  This theory is intentionally narrow.  It does not change the public
  soundness theorem path; it only factors the remaining reachable FRI
  obligations into explicit evidence predicates that later proofs can target.
\<close>

context soundness
begin

definition trace_fri_partial_candidate_evidence
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> nat list \<Rightarrow> 'f authenticated_opening list list \<Rightarrow>
      'f list \<Rightarrow> bool"
where
  "trace_fri_partial_candidate_evidence s out fr query_idxs
      trace_openings trace_table \<longleftrightarrow>
    accepted_with_partial_trace_openings s out fr query_idxs
      trace_openings \<and>
    partial_trace_table_candidate trace_table trace_openings \<and>
    \<not> trace_table_low_degree trace_table"

definition composition_fri_partial_candidate_evidence
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> nat list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> 'f list \<Rightarrow>
      'f list \<Rightarrow> bool"
where
  "composition_fri_partial_candidate_evidence s out fr f_fri_roots
      f_final as dg composition_fri_roots final trace_query_idxs
      trace_openings composition_query_idxs composition_openings trace_table
      composition_table \<longleftrightarrow>
    accepted_with_partial_initial_openings s out fr f_fri_roots f_final
      as dg composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings \<and>
    partial_trace_table_candidate trace_table trace_openings \<and>
    partial_composition_table_candidate composition_table
      composition_openings \<and>
    trace_table_low_degree trace_table \<and>
    \<not> composition_table_low_degree maxDegree composition_table"

lemma trace_fri_bad_with_reachable_partial_candidate_iff_evidence:
  "trace_fri_bad_with_reachable_partial_candidate s out \<longleftrightarrow>
    (\<exists>fr query_idxs trace_openings trace_table.
      trace_fri_partial_candidate_evidence s out fr query_idxs
        trace_openings trace_table)"
  unfolding trace_fri_bad_with_reachable_partial_candidate_def
    trace_fri_partial_candidate_evidence_def
  by blast

lemma composition_fri_bad_with_reachable_partial_candidate_iff_evidence:
  "composition_fri_bad_with_reachable_partial_candidate s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table.
      composition_fri_partial_candidate_evidence s out fr f_fri_roots
        f_final as dg composition_fri_roots final trace_query_idxs
        trace_openings composition_query_idxs composition_openings
        trace_table composition_table)"
  unfolding composition_fri_bad_with_reachable_partial_candidate_def
    composition_fri_partial_candidate_evidence_def
  by blast

lemma trace_fri_partial_candidate_evidenceI:
  assumes
    "accepted_with_partial_trace_openings s out fr query_idxs
      trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "\<not> trace_table_low_degree trace_table"
  shows
    "trace_fri_partial_candidate_evidence s out fr query_idxs
      trace_openings trace_table"
  using assms unfolding trace_fri_partial_candidate_evidence_def by blast

lemma trace_fri_partial_candidate_evidenceD:
  assumes
    "trace_fri_partial_candidate_evidence s out fr query_idxs
      trace_openings trace_table"
  shows
    "accepted_with_partial_trace_openings s out fr query_idxs
      trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "\<not> trace_table_low_degree trace_table"
  using assms unfolding trace_fri_partial_candidate_evidence_def by blast+

lemma trace_fri_bad_with_reachable_partial_candidateE:
  assumes "trace_fri_bad_with_reachable_partial_candidate s out"
  obtains fr query_idxs trace_openings trace_table where
    "trace_fri_partial_candidate_evidence s out fr query_idxs
      trace_openings trace_table"
  using assms
  unfolding trace_fri_bad_with_reachable_partial_candidate_iff_evidence
  by blast

lemma composition_fri_partial_candidate_evidenceI:
  assumes
    "accepted_with_partial_initial_openings s out fr f_fri_roots f_final
      as dg composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "trace_table_low_degree trace_table"
    "\<not> composition_table_low_degree maxDegree composition_table"
  shows
    "composition_fri_partial_candidate_evidence s out fr f_fri_roots
      f_final as dg composition_fri_roots final trace_query_idxs
      trace_openings composition_query_idxs composition_openings
      trace_table composition_table"
  using assms
  unfolding composition_fri_partial_candidate_evidence_def by blast

lemma composition_fri_partial_candidate_evidenceD:
  assumes
    "composition_fri_partial_candidate_evidence s out fr f_fri_roots
      f_final as dg composition_fri_roots final trace_query_idxs
      trace_openings composition_query_idxs composition_openings trace_table
      composition_table"
  shows
    "accepted_with_partial_initial_openings s out fr f_fri_roots f_final
      as dg composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "trace_table_low_degree trace_table"
    "\<not> composition_table_low_degree maxDegree composition_table"
  using assms
  unfolding composition_fri_partial_candidate_evidence_def by blast+

lemma composition_fri_bad_with_reachable_partial_candidateE:
  assumes "composition_fri_bad_with_reachable_partial_candidate s out"
  obtains fr f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table where
    "composition_fri_partial_candidate_evidence s out fr f_fri_roots
      f_final as dg composition_fri_roots final trace_query_idxs
      trace_openings composition_query_idxs composition_openings
      trace_table composition_table"
  using assms
  unfolding composition_fri_bad_with_reachable_partial_candidate_iff_evidence
  by blast

lemma trace_fri_reachable_partial_candidate_reductionD:
  assumes "trace_fri_reachable_partial_candidate_reduction_assumption s"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le>
      trace_fri_error"
  using assms
  unfolding trace_fri_reachable_partial_candidate_reduction_assumption_def
  by simp

lemma composition_fri_reachable_partial_candidate_reductionD:
  assumes "composition_fri_reachable_partial_candidate_reduction_assumption s"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le>
      composition_fri_error"
  using assms
  unfolding composition_fri_reachable_partial_candidate_reduction_assumption_def
  by simp

definition trace_fri_partial_candidate_opening_evidence
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list list \<Rightarrow>
      'f \<Rightarrow> nat list \<Rightarrow> 'f authenticated_opening list list \<Rightarrow>
      'f list \<Rightarrow> bool"
where
  "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table \<longleftrightarrow>
    accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers \<and>
    trace_fri_partial_candidate_evidence s out fr candidate_query_idxs
      trace_openings trace_table"

definition composition_fri_partial_candidate_opening_evidence
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list list \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> nat list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> 'f list \<Rightarrow>
      'f list \<Rightarrow> bool"
where
  "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table \<longleftrightarrow>
    accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      fri_dg opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers \<and>
    composition_fri_partial_candidate_evidence s out fr f_fri_roots
      f_final as dg composition_fri_roots final trace_query_idxs
      trace_openings composition_query_idxs composition_openings
      trace_table composition_table"

lemma trace_fri_partial_candidate_opening_evidenceD:
  assumes
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
  shows
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "trace_fri_partial_candidate_evidence s out fr candidate_query_idxs
      trace_openings trace_table"
  using assms
  unfolding trace_fri_partial_candidate_opening_evidence_def by blast+

lemma composition_fri_partial_candidate_opening_evidenceD:
  assumes
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
  shows
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    "composition_fri_partial_candidate_evidence s out fr f_fri_roots
      f_final as dg composition_fri_roots final trace_query_idxs
      trace_openings composition_query_idxs composition_openings
      trace_table composition_table"
  using assms
  unfolding composition_fri_partial_candidate_opening_evidence_def by blast+

lemma verify_monad_trace_fri_bad_extracts_opening_evidence:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bad:
    "trace_fri_bad_with_reachable_partial_candidate s
      (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  where
    "trace_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr candidate_query_idxs
      trace_openings trace_table"
proof -
  from verify_monad_accepted_fri_opening_transcript[OF outcome]
  obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers where fri_opening:
    "accepted_fri_opening_transcript s (Some (result, final_state))
      trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    by blast
  from trace_fri_bad_with_reachable_partial_candidateE[OF bad]
  obtain fr candidate_query_idxs trace_openings trace_table where evidence:
    "trace_fri_partial_candidate_evidence s
      (Some (result, final_state)) fr candidate_query_idxs trace_openings
      trace_table"
    by blast
  have combined:
    "trace_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr candidate_query_idxs
      trace_openings trace_table"
    unfolding trace_fri_partial_candidate_opening_evidence_def
    using fri_opening evidence by simp
  show ?thesis
    by (rule that[OF combined])
qed

lemma verify_monad_composition_fri_bad_extracts_opening_evidence:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bad:
    "composition_fri_bad_with_reachable_partial_candidate s
      (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final fri_dg opening_composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table
  where
    "composition_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table"
proof -
  from verify_monad_accepted_fri_opening_transcript[OF outcome]
  obtain trace_roots trace_bs trace_final fri_dg opening_composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers where fri_opening:
    "accepted_fri_opening_transcript s (Some (result, final_state))
      trace_roots trace_bs trace_final fri_dg opening_composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    by blast
  from composition_fri_bad_with_reachable_partial_candidateE[OF bad]
  obtain fr f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table where evidence:
    "composition_fri_partial_candidate_evidence s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
    by blast
  have combined:
    "composition_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table"
    unfolding composition_fri_partial_candidate_opening_evidence_def
    using fri_opening evidence by simp
  show ?thesis
    by (rule that[OF combined])
qed

lemma verify_monad_composition_fri_bad_extracts_opening_evidence_with_degree_bound:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bad:
    "composition_fri_bad_with_reachable_partial_candidate s
      (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final fri_dg opening_composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table
  where
    "composition_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table"
    and "to_nat fri_dg \<le> maxDegree"
proof (rule verify_monad_composition_fri_bad_extracts_opening_evidence
    [OF outcome bad])
  fix trace_roots trace_bs trace_final fri_dg opening_composition_roots
    composition_bs composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr f_fri_roots f_final as dg
    composition_fri_roots final trace_query_idxs trace_openings
    composition_query_idxs composition_openings trace_table composition_table
  assume evidence:
    "composition_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table"
  have fri_opening:
    "accepted_fri_opening_transcript s (Some (result, final_state))
      trace_roots trace_bs trace_final fri_dg opening_composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    using composition_fri_partial_candidate_opening_evidenceD(1)
      [OF evidence] .
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs fri_dg composition_bs"
    by (rule accepted_fri_opening_transcript_challenges[OF fri_opening])
  have degree_bound: "to_nat fri_dg \<le> maxDegree"
    by (rule verify_monad_accepted_fri_challenges_degree_bound
        [OF outcome challenges])
  show ?thesis
    by (rule that[OF evidence degree_bound])
qed

lemma verifier_query_round_after_index_final_checks:
  assumes outcome:
    "Some ((), t) \<in>
      set_dist
        (execute
          (verifier_query_round_after_index_program
            fr f_fl f_final as fl final raw) s)"
  obtains idx fv s1 f_i f_len f_pow s2 c_i c_len c_pow s4 where
    "idx = index (to_nat raw)"
    "Some (fv, s1) \<in>
      set_dist (execute (mmap (check_decommit_on_query fr idx)) s)"
    "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
      set_dist
        (execute
          (mfold (idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    "Some ((c_i, final, c_len, c_pow), s4) \<in>
      set_dist
        (execute
          (mfold (idx, cp_eval as fv (h ^ idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s2)"
    "t = s4"
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
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  obtain f_i f_x f_len f_pow where f_out_eq:
    "f_out = (f_i, f_x, f_len, f_pow)"
    by (cases f_out) auto
  have f_x_eq: "f_x = f_final"
    using assert_trace unfolding assert_def f_out_eq
    by (cases "f_x = f_final") (auto simp: throw_no_outcome)
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def f_out_eq f_x_eq by simp
  obtain c_i c_x c_len c_pow where c_out_eq:
    "c_out = (c_i, c_x, c_len, c_pow)"
    by (cases c_out) auto
  have c_x_eq: "c_x = final"
    using assert_comp unfolding assert_def c_out_eq
    by (cases "c_x = final") (auto simp: throw_no_outcome)
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def c_out_eq c_x_eq by simp
  have trace_fri':
    "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
      set_dist
        (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    using trace_fri f_out_eq f_x_eq by simp
  have comp_fri':
    "Some ((c_i, final, c_len, c_pow), s4) \<in>
      set_dist
        (execute
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s2)"
    using comp_fri c_out_eq c_x_eq s3_eq by simp
  show ?thesis
    by (rule that[OF refl query_decommit trace_fri' comp_fri' t_eq])
qed

lemma verifier_query_round_program_final_checks:
  assumes outcome:
    "Some ((), t) \<in>
      set_dist
        (execute
          (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx fv s0 s1 f_i f_len f_pow s2 c_i c_len c_pow s4
  where
    "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    "idx = index (to_nat raw)"
    "Some (fv, s1) \<in>
      set_dist (execute (mmap (check_decommit_on_query fr idx)) s0)"
    "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
      set_dist
        (execute
          (mfold (idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    "Some ((c_i, final, c_len, c_pow), s4) \<in>
      set_dist
        (execute
          (mfold (idx, cp_eval as fv (h ^ idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s2)"
    "t = s4"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    raw:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and after:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  from verifier_query_round_after_index_final_checks[OF after]
  obtain idx fv s1 f_i f_len f_pow s2 c_i c_len c_pow s4 where
    idx_eq: "idx = index (to_nat raw)"
    and query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr idx)) s0)"
    and trace_fri:
      "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
        set_dist
          (execute
            (mfold (idx, hd fv, clength * scale, 1)
              (receive_query_commits f_fl)) s1)"
    and comp_fri:
      "Some ((c_i, final, c_len, c_pow), s4) \<in>
        set_dist
          (execute
            (mfold (idx, cp_eval as fv (h ^ idx * shift),
                clength * scale, 1)
              (receive_query_commits fl)) s2)"
    and t_eq: "t = s4"
    by blast
  show ?thesis
    by (rule that[OF raw idx_eq query_decommit trace_fri comp_fri t_eq])
qed

end

end
