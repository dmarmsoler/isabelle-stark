(*  Title:      Stark/Soundness_Relevant_Drift_Reachable_FRI.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Relevant_Drift_Reachable_FRI
  imports Soundness_Relevant_Drift_Public
begin

text \<open>
  Reachable partial-candidate FRI interface for the refined relevant-drift
  migration path.

  This layer does not change the compatibility predicates
  \<^term>\<open>trace_fri_bad_with_partial_openings\<close> and
  \<^term>\<open>composition_fri_bad_with_partial_openings\<close>.  Instead it records the
  partial-candidate FRI obligations used by the aligned partial-opening route:
  the verifier has authenticated sampled openings, and the FRI low-degree
  interface rules out a low-degree violation for any candidate table compatible
  with those openings.
\<close>

context soundness
begin

definition trace_fri_bad_with_reachable_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_reachable_partial_candidate s out \<longleftrightarrow>
    (\<exists>fr query_idxs trace_openings trace_table.
      accepted_with_partial_trace_openings s out fr query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table)"

definition composition_fri_bad_with_reachable_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_bad_with_reachable_partial_candidate s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table.
      accepted_with_partial_initial_openings s out fr f_fri_roots f_final
        as dg composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table)"

definition trace_fri_reachable_partial_candidate_reduction_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "trace_fri_reachable_partial_candidate_reduction_assumption s \<longleftrightarrow>
    wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le>
      trace_fri_error"

definition composition_fri_reachable_partial_candidate_reduction_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "composition_fri_reachable_partial_candidate_reduction_assumption s
    \<longleftrightarrow>
    wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le>
      composition_fri_error"

lemma trace_fri_bad_with_partial_candidates_imp_reachable_partial_candidate:
  assumes "trace_fri_bad_with_partial_candidates s out"
  shows "trace_fri_bad_with_reachable_partial_candidate s out"
  using assms
  unfolding trace_fri_bad_with_partial_candidates_def
    trace_fri_bad_with_reachable_partial_candidate_def
    accepted_with_partial_initial_openings_def
  by blast

lemma composition_fri_bad_with_partial_candidates_imp_reachable_partial_candidate:
  assumes "composition_fri_bad_with_partial_candidates s out"
  shows "composition_fri_bad_with_reachable_partial_candidate s out"
  using assms
  unfolding composition_fri_bad_with_partial_candidates_def
    composition_fri_bad_with_reachable_partial_candidate_def
  by blast

lemma trace_fri_bad_with_empty_composition_header_candidates_imp_reachable_partial_candidate:
  assumes "trace_fri_bad_with_empty_composition_header_candidates s out"
  shows "trace_fri_bad_with_reachable_partial_candidate s out"
  using assms
  unfolding trace_fri_bad_with_empty_composition_header_candidates_def
    accepted_with_empty_composition_header_candidates_def
    trace_fri_bad_with_reachable_partial_candidate_def
  by blast

lemma trace_fri_bad_with_partial_candidates_not_None:
  "\<not> trace_fri_bad_with_partial_candidates s None"
  unfolding trace_fri_bad_with_partial_candidates_def
    accepted_with_partial_initial_openings_def accepted_def
  by simp

lemma composition_fri_bad_with_partial_candidates_not_None:
  "\<not> composition_fri_bad_with_partial_candidates s None"
  unfolding composition_fri_bad_with_partial_candidates_def
    accepted_with_partial_initial_openings_def accepted_def
  by simp

lemma trace_fri_bad_with_empty_composition_header_candidates_not_None:
  "\<not> trace_fri_bad_with_empty_composition_header_candidates s None"
  unfolding trace_fri_bad_with_empty_composition_header_candidates_def
    accepted_with_empty_composition_header_candidates_def accepted_def
  by simp

lemma trace_fri_bad_with_partial_candidates_bound_from_reachable_reduction:
  assumes
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_reachable_partial_candidate_reduction_assumption
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> trace_fri_error"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> trace_fri_bad_with_partial_candidates s None"
    by (rule trace_fri_bad_with_partial_candidates_not_None)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have reduction:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate ?s) ?s \<le>
      trace_fri_error"
    using assms[OF builder]
    unfolding trace_fri_reachable_partial_candidate_reduction_assumption_def
    by simp
  show "wp_event verify_monad (trace_fri_bad_with_partial_candidates ?s) ?s
      \<le> trace_fri_error"
    by (rule order_trans
        [OF _ reduction])
      (rule wp_event_mono,
        rule trace_fri_bad_with_partial_candidates_imp_reachable_partial_candidate)
qed

lemma composition_fri_bad_with_partial_candidates_bound_from_reachable_reduction:
  assumes
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_reachable_partial_candidate_reduction_assumption
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> composition_fri_error"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> composition_fri_bad_with_partial_candidates s None"
    by (rule composition_fri_bad_with_partial_candidates_not_None)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have reduction:
    "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate ?s) ?s \<le>
      composition_fri_error"
    using assms[OF builder]
    unfolding
      composition_fri_reachable_partial_candidate_reduction_assumption_def
    by simp
  show "wp_event verify_monad
      (composition_fri_bad_with_partial_candidates ?s) ?s \<le>
      composition_fri_error"
    by (rule order_trans
        [OF _ reduction])
      (rule wp_event_mono,
        rule
          composition_fri_bad_with_partial_candidates_imp_reachable_partial_candidate)
qed

lemma trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction:
  assumes
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_reachable_partial_candidate_reduction_assumption
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> trace_fri_bad_with_empty_composition_header_candidates s None"
    by (rule trace_fri_bad_with_empty_composition_header_candidates_not_None)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have reduction:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate ?s) ?s \<le>
      trace_fri_error"
    using assms[OF builder]
    unfolding trace_fri_reachable_partial_candidate_reduction_assumption_def
    by simp
  show "wp_event verify_monad
      (trace_fri_bad_with_empty_composition_header_candidates ?s) ?s \<le>
      trace_fri_error"
    by (rule order_trans
        [OF _ reduction])
      (rule wp_event_mono,
        rule
          trace_fri_bad_with_empty_composition_header_candidates_imp_reachable_partial_candidate)
qed

definition empty_header_low_degree_trace_candidate_nonunique
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "empty_header_low_degree_trace_candidate_nonunique s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table trace_table'.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      partial_trace_table_candidate trace_table' trace_openings \<and>
      trace_table \<noteq> trace_table' \<and>
      trace_table_low_degree trace_table \<and>
      trace_table_low_degree trace_table')"

definition empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit s out
    \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table trace_table' i.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      partial_trace_table_candidate trace_table' trace_openings \<and>
      trace_table \<noteq> trace_table' \<and>
      trace_table_low_degree trace_table \<and>
      trace_table_low_degree trace_table' \<and>
      i < rounds \<and>
      map ((!) trace_table) (powers_scaled (trace_query_idxs ! i)) =
        map ((!) trace_table') (powers_scaled (trace_query_idxs ! i)))"

definition empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit
      s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table trace_table' i.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      accepted_transcript_shape s out as trace_query_idxs \<and>
      partial_trace_table_candidate trace_table' trace_openings \<and>
      trace_table \<noteq> trace_table' \<and>
      trace_table_low_degree trace_table \<and>
      trace_table_low_degree trace_table' \<and>
      i < rounds \<and>
      map ((!) trace_table) (powers_scaled (trace_query_idxs ! i)) =
        map ((!) trace_table') (powers_scaled (trace_query_idxs ! i)))"

lemma empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_imp_query_agreement:
  assumes
    "empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit
      s out"
  shows
    "empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit
      s out"
  using assms
  unfolding
    empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit_def
    empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit_def
  by blast

definition trace_table_agreement_indices :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
where
  "trace_table_agreement_indices trace_table trace_table' =
    {idx \<in> query_sample_space.
      map ((!) trace_table) (powers_scaled idx) =
        map ((!) trace_table') (powers_scaled idx)}"

lemma empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreementE:
  assumes
    "empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit
      s out"
  obtains fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table trace_table' i
  where
    "accepted_with_empty_composition_header_candidates s out fr
      f_fri_roots f_final as dg final trace_query_idxs trace_openings
      trace_table composition_table"
    "accepted_transcript_shape s out as trace_query_idxs"
    "partial_trace_table_candidate trace_table' trace_openings"
    "trace_table \<noteq> trace_table'"
    "trace_table_low_degree trace_table"
    "trace_table_low_degree trace_table'"
    "i < rounds"
    "trace_query_idxs ! i \<in>
      trace_table_agreement_indices trace_table trace_table'"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table trace_table' i
    where empty:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and shape: "accepted_transcript_shape s out as trace_query_idxs"
    and cand': "partial_trace_table_candidate trace_table' trace_openings"
    and distinct: "trace_table \<noteq> trace_table'"
    and trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and i_bound: "i < rounds"
    and agree:
      "map ((!) trace_table) (powers_scaled (trace_query_idxs ! i)) =
        map ((!) trace_table') (powers_scaled (trace_query_idxs ! i))"
    using assms
    unfolding
      empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit_def
    by blast
  have len_query: "length trace_query_idxs = rounds"
    using accepted_transcript_shape_query_shapes(1)[OF shape] .
  have idx_mem: "trace_query_idxs ! i \<in> set trace_query_idxs"
    by (rule nth_mem) (use i_bound len_query in simp)
  have idx_sample: "trace_query_idxs ! i \<in> query_sample_space"
    by (rule accepted_transcript_shape_query_sample_space[OF shape idx_mem])
  have idx_agree:
    "trace_query_idxs ! i \<in>
      trace_table_agreement_indices trace_table trace_table'"
    using idx_sample agree unfolding trace_table_agreement_indices_def
    by simp
  show ?thesis
    by (rule that[OF empty shape cand' distinct trace_low trace'_low
          i_bound idx_agree])
qed

lemma trace_table_agreement_indices_card_bound:
  assumes trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows "card (trace_table_agreement_indices trace_table trace_table') <
    clength"
proof -
  from trace_low obtain f where deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    unfolding trace_table_low_degree_def by blast
  from trace'_low obtain f' where deg_f': "degree f' < clength"
    and trace_table': "trace_table' = map (poly f') eval_domain"
    unfolding trace_table_low_degree_def by blast
  let ?A = "trace_table_agreement_indices trace_table trace_table'"
  let ?R = "f - f'"
  have A_subset: "?A \<subseteq> query_sample_space"
    unfolding trace_table_agreement_indices_def by auto
  have finite_A: "finite ?A"
    unfolding trace_table_agreement_indices_def query_sample_space_def by simp
  have inj: "inj_on (\<lambda>idx. h ^ idx * shift) ?A"
  proof (intro inj_onI)
    fix i j
    assume i_in: "i \<in> ?A"
      and j_in: "j \<in> ?A"
      and eq: "h ^ i * shift = h ^ j * shift"
    have i_bound: "i < clength * scale"
      by (rule query_sample_space_less_domain[OF set_mp[OF A_subset i_in]])
    have j_bound: "j < clength * scale"
      by (rule query_sample_space_less_domain[OF set_mp[OF A_subset j_in]])
    have "h ^ i = h ^ j"
      using eq shift_nonzero by simp
    then show "i = j"
      by (rule h_power_inj_on_eval_domain[OF i_bound j_bound])
  qed
  have residual_nonzero: "?R \<noteq> 0"
  proof
    assume "?R = 0"
    then have "f = f'"
      by simp
    then show False
      using distinct trace_table trace_table' by simp
  qed
  have image_subset:
    "(\<lambda>idx. h ^ idx * shift) ` ?A \<subseteq> {x. poly ?R x = 0}"
  proof
    fix x
    assume x_in: "x \<in> (\<lambda>idx. h ^ idx * shift) ` ?A"
    then obtain idx where idx_in: "idx \<in> ?A"
      and x_eq: "x = h ^ idx * shift"
      by blast
    have idx_sample: "idx \<in> query_sample_space"
      by (rule set_mp[OF A_subset idx_in])
    have idx_bound: "idx < clength * scale"
      by (rule query_sample_space_less_domain[OF idx_sample])
    have agree:
      "map ((!) trace_table) (powers_scaled idx) =
        map ((!) trace_table') (powers_scaled idx)"
      using idx_in unfolding trace_table_agreement_indices_def by simp
    have ps0: "powers_scaled idx ! 0 = idx"
      using powers_pos unfolding powers_scaled_def by simp
    have len_ps: "0 < length (powers_scaled idx)"
      using powers_pos unfolding powers_scaled_def by simp
    have value_eq: "trace_table ! idx = trace_table' ! idx"
      using arg_cong[OF agree, of "\<lambda>xs. xs ! 0"] ps0 len_ps
      by simp
    have left:
      "trace_table ! idx = poly f (h ^ idx * shift)"
      using trace_table eval_domain_nth[OF idx_bound] idx_bound
        eval_domain_length by simp
    have right:
      "trace_table' ! idx = poly f' (h ^ idx * shift)"
      using trace_table' eval_domain_nth[OF idx_bound] idx_bound
        eval_domain_length by simp
    have "poly f (h ^ idx * shift) = poly f' (h ^ idx * shift)"
      using value_eq left right by simp
    then show "x \<in> {x. poly ?R x = 0}"
      using x_eq by simp
  qed
  have "card ?A = card ((\<lambda>idx. h ^ idx * shift) ` ?A)"
    by (simp add: card_image inj)
  also have "... \<le> card {x. poly ?R x = 0}"
    by (rule card_mono[OF poly_roots_finite[OF residual_nonzero]
          image_subset])
  also have "... \<le> degree ?R"
    by (rule card_poly_roots_bound[OF residual_nonzero])
  also have "... < clength"
    using deg_f deg_f' by (simp add: degree_diff_less)
  finally show ?thesis .
qed

lemma trace_table_agreement_indices_fraction_bound:
  assumes trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows "nnreal
      (card (trace_table_agreement_indices trace_table trace_table')) /
    nnreal (card query_sample_space) \<le>
    nnreal clength / nnreal (card query_sample_space)"
proof -
  have card_le:
    "card (trace_table_agreement_indices trace_table trace_table') \<le>
      clength"
    using trace_table_agreement_indices_card_bound
        [OF trace_low trace'_low distinct]
    by simp
  show ?thesis
    by (rule nnreal_nat_divide_right_mono[OF card_le])
qed

lemma trace_table_agreement_indices_query_envelope_bound:
  assumes trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows "nnreal
      (query_raw_preimage_card_envelope
        (card (trace_table_agreement_indices trace_table trace_table'))) /
    nnreal size \<le>
    nnreal (query_raw_preimage_card_envelope clength) / nnreal size"
proof -
  have card_le:
    "card (trace_table_agreement_indices trace_table trace_table') \<le>
      clength"
    using trace_table_agreement_indices_card_bound
        [OF trace_low trace'_low distinct]
    by simp
  have envelope_le:
    "query_raw_preimage_card_envelope
        (card (trace_table_agreement_indices trace_table trace_table')) \<le>
      query_raw_preimage_card_envelope clength"
    by (rule query_raw_preimage_card_envelope_mono[OF card_le])
  show ?thesis
    by (rule nnreal_nat_divide_right_mono[OF envelope_le])
qed

lemma checked_staged_query_prefix_trace_pair_agreement_hit_bound_by_prehit:
  assumes trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table'))
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table'))
      adversary_initial_state +
     nnreal (query_raw_preimage_card_envelope clength) / nnreal size"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    show
      "trace_table_agreement_indices trace_table trace_table'
          \<subseteq> query_sample_space \<and>
       nnreal
        (query_raw_preimage_card_envelope
          (card (trace_table_agreement_indices trace_table trace_table'))) /
       nnreal size \<le>
       nnreal (query_raw_preimage_card_envelope clength) / nnreal size"
      using trace_table_agreement_indices_query_envelope_bound
          [OF trace_low trace'_low distinct]
      unfolding trace_table_agreement_indices_def by auto
  qed
qed

definition checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_from_prefix
  :: "'f staged_adversary \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_from_prefix
      A trace_table trace_table' i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (\<exists>prefix prefix_state raw raw_state.
          Some (data, attacker_state) \<in>
            set_dist
              (execute (checked_staged_transcript_program A)
                adversary_initial_state) \<and>
          Some (((prefix, prefix_state), raw), raw_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_receive_with_state A i)
                adversary_initial_state) \<and>
          checked_staged_query_prefix_dynamic_index_hit
            (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table')
            (Some (((prefix, prefix_state), raw), raw_state))))"

lemma checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_from_prefixE:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_from_prefix
      A trace_table trace_table' i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains prefix prefix_state raw raw_state where
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "checked_staged_query_prefix_dynamic_index_hit
      (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table')
      (Some (((prefix, prefix_state), raw), raw_state))"
  using assms
proof -
  obtain prefix prefix_state raw raw_state where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (\<lambda>_ _. trace_table_agreement_indices trace_table trace_table')
        (Some (((prefix, prefix_state), raw), raw_state))"
    using assms
    unfolding
      checked_staged_security_with_actual_alpha_prefix_trace_pair_agreement_hit_from_prefix_def
    by simp blast
  show ?thesis
    by (rule that[OF builder prefix_receive hit])
qed

definition checked_staged_security_with_actual_alpha_prefix_empty_header_low_degree_prefix_agreement_hit
  :: "'f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_empty_header_low_degree_prefix_agreement_hit
      A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (let s =
          verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)
        in
          (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
              trace_openings trace_table composition_table trace_table' i
              prefix prefix_state raw raw_state.
            accepted_with_empty_composition_header_candidates s
              (Some (result, final_state)) fr f_fri_roots f_final as dg
              final trace_query_idxs trace_openings trace_table
              composition_table \<and>
            accepted_transcript_shape s (Some (result, final_state)) as
              trace_query_idxs \<and>
            partial_trace_table_candidate trace_table' trace_openings \<and>
            trace_table \<noteq> trace_table' \<and>
            trace_table_low_degree trace_table \<and>
            trace_table_low_degree trace_table' \<and>
            i < rounds \<and>
            Some (data, attacker_state) \<in>
              set_dist
                (execute (checked_staged_transcript_program A)
                  adversary_initial_state) \<and>
            Some (((prefix, prefix_state), raw), raw_state) \<in>
              set_dist
                (execute (checked_staged_query_prefix_receive_with_state A i)
                  adversary_initial_state) \<and>
            index (to_nat raw) \<in>
              trace_table_agreement_indices trace_table trace_table')))"

lemma empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_imp_prefix_agreement_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_empty_header_low_degree_prefix_agreement_hit
      A out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      checked_staged_security_with_actual_alpha_prefix_empty_header_low_degree_prefix_agreement_hit_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix alpha_prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have local_hit:
    "empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit
      ?s (Some (result, final_state))"
    using hit
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
    by simp
  from empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreementE
      [OF local_hit]
  obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table trace_table' i where
    empty:
      "accepted_with_empty_composition_header_candidates ?s
        (Some (result, final_state)) fr f_fri_roots f_final as dg final
        trace_query_idxs trace_openings trace_table composition_table"
    and shape:
      "accepted_transcript_shape ?s (Some (result, final_state)) as
        trace_query_idxs"
    and cand': "partial_trace_table_candidate trace_table' trace_openings"
    and distinct: "trace_table \<noteq> trace_table'"
    and trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and i_bound: "i < rounds"
    and idx_agree:
      "trace_query_idxs ! i \<in>
        trace_table_agreement_indices trace_table trace_table'"
    by blast
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support[unfolded out_eq]])
  from
    checked_staged_security_with_data_state_accepted_shape_query_prefix_receive_index
      [OF wf controlled data_support shape i_bound]
  obtain prefix prefix_state raw raw_state where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and raw_idx: "index (to_nat raw) = trace_query_idxs ! i"
    by blast
  have raw_agree:
    "index (to_nat raw) \<in>
      trace_table_agreement_indices trace_table trace_table'"
    using raw_idx idx_agree by simp
  have builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  proof -
    from checked_staged_security_experiment_with_data_state_outcomeE
        [OF data_support]
    show ?thesis by blast
  qed
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_empty_header_low_degree_prefix_agreement_hit_def
    apply (simp add: Let_def)
    by (intro exI[of _ fr] exI[of _ f_fri_roots]
        exI[of _ f_final] exI[of _ as] exI[of _ dg]
        exI[of _ final] exI[of _ trace_query_idxs]
        exI[of _ trace_openings] exI[of _ trace_table]
        exI[of _ composition_table] exI[of _ trace_table']
        exI[of _ i] exI[of _ prefix] exI[of _ prefix_state]
        exI[of _ raw] exI[of _ raw_state] conjI empty shape cand'
        distinct trace_low trace'_low i_bound builder prefix_receive
        raw_agree)
qed

lemma empty_header_low_degree_trace_candidate_nonunique_imp_query_agreement_hit:
  assumes "empty_header_low_degree_trace_candidate_nonunique s out"
  shows
    "empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit
      s out"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table trace_table' where empty:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and cand': "partial_trace_table_candidate trace_table' trace_openings"
    and distinct: "trace_table \<noteq> trace_table'"
    and trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    using assms
    unfolding empty_header_low_degree_trace_candidate_nonunique_def by blast
  have partial:
    "accepted_with_partial_trace_openings s out fr trace_query_idxs
      trace_openings"
    using empty unfolding accepted_with_empty_composition_header_candidates_def
    by blast
  have cand:
    "partial_trace_table_candidate trace_table trace_openings"
    using empty unfolding accepted_with_empty_composition_header_candidates_def
    by blast
  have idxs:
    "map opening_index (trace_openings ! 0) =
      powers_scaled (trace_query_idxs ! 0)"
    using accepted_with_partial_trace_openings_shapes(3)
        [OF partial rounds_positive] .
  have vals:
    "map ((!) trace_table) (powers_scaled (trace_query_idxs ! 0)) =
      map ((!) trace_table') (powers_scaled (trace_query_idxs ! 0))"
  proof -
    have left:
      "map ((!) trace_table) (powers_scaled (trace_query_idxs ! 0)) =
        map opening_value (trace_openings ! 0)"
      by (rule partial_trace_table_candidate_query_values
          [OF cand rounds_positive idxs])
    have right:
      "map ((!) trace_table') (powers_scaled (trace_query_idxs ! 0)) =
        map opening_value (trace_openings ! 0)"
      by (rule partial_trace_table_candidate_query_values
          [OF cand' rounds_positive idxs])
    show ?thesis
      using left right by simp
  qed
  show ?thesis
    unfolding
      empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit_def
    using empty cand' distinct trace_low trace'_low rounds_positive vals
    by blast
qed

lemma empty_header_low_degree_trace_candidate_nonunique_le_query_agreement_hit:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique)
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit)
    adversary_initial_state"
  by (rule wp_event_mono)
    (auto simp:
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      split: option.splits prod.splits
      dest:
        empty_header_low_degree_trace_candidate_nonunique_imp_query_agreement_hit)

lemma empty_header_partial_trace_candidate_nonunique_imp_trace_fri_or_low_degree_nonunique:
  assumes "empty_header_partial_trace_candidate_nonunique s out"
  shows
    "trace_fri_bad_with_empty_composition_header_candidates s out \<or>
     empty_header_low_degree_trace_candidate_nonunique s out"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs trace_openings
      trace_table composition_table where empty:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and not_singleton:
      "\<not> (\<exists>trace_table0.
        partial_trace_table_candidates trace_openings \<subseteq>
          {trace_table0})"
    using assms
    unfolding empty_header_partial_trace_candidate_nonunique_def by blast
  have trace_candidate:
    "trace_table \<in> partial_trace_table_candidates trace_openings"
    using empty
    unfolding accepted_with_empty_composition_header_candidates_def
      partial_trace_table_candidates_def
    by simp
  obtain trace_table' where trace_candidate':
      "trace_table' \<in> partial_trace_table_candidates trace_openings"
    and distinct: "trace_table \<noteq> trace_table'"
  proof -
    have "\<not> partial_trace_table_candidates trace_openings \<subseteq>
        {trace_table}"
      using not_singleton by blast
    then obtain trace_table' where
      "trace_table' \<in> partial_trace_table_candidates trace_openings"
      "trace_table' \<notin> {trace_table}"
      by blast
    then show ?thesis
      using that by blast
  qed
  show ?thesis
  proof (cases "trace_table_low_degree trace_table")
    case False
    then have "trace_fri_bad_with_empty_composition_header_candidates s out"
      unfolding trace_fri_bad_with_empty_composition_header_candidates_def
      using empty by blast
    then show ?thesis by simp
  next
    case trace_low: True
    show ?thesis
    proof (cases "trace_table_low_degree trace_table'")
      case False
      have empty':
        "accepted_with_empty_composition_header_candidates s out fr
          f_fri_roots f_final as dg final trace_query_idxs trace_openings
          trace_table' composition_table"
        using empty trace_candidate'
        unfolding accepted_with_empty_composition_header_candidates_def
          partial_trace_table_candidates_def
        by blast
      then have
        "trace_fri_bad_with_empty_composition_header_candidates s out"
        unfolding trace_fri_bad_with_empty_composition_header_candidates_def
        using False by blast
      then show ?thesis by simp
    next
      case trace'_low: True
      have "empty_header_low_degree_trace_candidate_nonunique s out"
        unfolding empty_header_low_degree_trace_candidate_nonunique_def
        using empty trace_candidate' distinct trace_low trace'_low
        unfolding partial_trace_table_candidates_def
        by blast
      then show ?thesis by simp
    qed
  qed
qed

definition empty_header_partial_trace_candidate_nonunique_transcript
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "empty_header_partial_trace_candidate_nonunique_transcript s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      accepted_transcript_shape s out as trace_query_idxs \<and>
      \<not> (\<exists>trace_table0.
        partial_trace_table_candidates trace_openings \<subseteq>
          {trace_table0}))"

lemma empty_header_partial_trace_candidate_nonunique_transcript_imp_trace_fri_or_low_degree_transcript_query_agreement:
  assumes "empty_header_partial_trace_candidate_nonunique_transcript s out"
  shows
    "trace_fri_bad_with_empty_composition_header_candidates s out \<or>
     empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit
      s out"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs trace_openings
      trace_table composition_table where empty:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and shape: "accepted_transcript_shape s out as trace_query_idxs"
    and not_singleton:
      "\<not> (\<exists>trace_table0.
        partial_trace_table_candidates trace_openings \<subseteq>
          {trace_table0})"
    using assms
    unfolding empty_header_partial_trace_candidate_nonunique_transcript_def
    by blast
  have trace_candidate:
    "trace_table \<in> partial_trace_table_candidates trace_openings"
    using empty
    unfolding accepted_with_empty_composition_header_candidates_def
      partial_trace_table_candidates_def
    by simp
  obtain trace_table' where trace_candidate':
      "trace_table' \<in> partial_trace_table_candidates trace_openings"
    and distinct: "trace_table \<noteq> trace_table'"
  proof -
    have "\<not> partial_trace_table_candidates trace_openings \<subseteq>
        {trace_table}"
      using not_singleton by blast
    then obtain trace_table' where
      "trace_table' \<in> partial_trace_table_candidates trace_openings"
      "trace_table' \<notin> {trace_table}"
      by blast
    then show ?thesis
      using that by blast
  qed
  show ?thesis
  proof (cases "trace_table_low_degree trace_table")
    case False
    then have "trace_fri_bad_with_empty_composition_header_candidates s out"
      unfolding trace_fri_bad_with_empty_composition_header_candidates_def
      using empty by blast
    then show ?thesis by simp
  next
    case trace_low: True
    show ?thesis
    proof (cases "trace_table_low_degree trace_table'")
      case False
      have empty':
        "accepted_with_empty_composition_header_candidates s out fr
          f_fri_roots f_final as dg final trace_query_idxs trace_openings
          trace_table' composition_table"
        using empty trace_candidate'
        unfolding accepted_with_empty_composition_header_candidates_def
          partial_trace_table_candidates_def
        by blast
      then have
        "trace_fri_bad_with_empty_composition_header_candidates s out"
        unfolding trace_fri_bad_with_empty_composition_header_candidates_def
        using False by blast
      then show ?thesis by simp
    next
      case trace'_low: True
      have idxs:
        "map opening_index (trace_openings ! 0) =
          powers_scaled (trace_query_idxs ! 0)"
      proof -
        have partial:
          "accepted_with_partial_trace_openings s out fr trace_query_idxs
            trace_openings"
          using empty
          unfolding accepted_with_empty_composition_header_candidates_def
          by blast
        show ?thesis
          using accepted_with_partial_trace_openings_shapes(3)
              [OF partial rounds_positive] .
      qed
      have vals:
        "map ((!) trace_table) (powers_scaled (trace_query_idxs ! 0)) =
          map ((!) trace_table') (powers_scaled (trace_query_idxs ! 0))"
      proof -
        have cand:
          "partial_trace_table_candidate trace_table trace_openings"
          using empty
          unfolding accepted_with_empty_composition_header_candidates_def
          by blast
        have cand':
          "partial_trace_table_candidate trace_table' trace_openings"
          using trace_candidate'
          unfolding partial_trace_table_candidates_def by simp
        have left:
          "map ((!) trace_table) (powers_scaled (trace_query_idxs ! 0)) =
            map opening_value (trace_openings ! 0)"
          by (rule partial_trace_table_candidate_query_values
              [OF cand rounds_positive idxs])
        have right:
          "map ((!) trace_table') (powers_scaled (trace_query_idxs ! 0)) =
            map opening_value (trace_openings ! 0)"
          by (rule partial_trace_table_candidate_query_values
              [OF cand' rounds_positive idxs])
        show ?thesis
          using left right by simp
      qed
      have
        "empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit
          s out"
        unfolding
          empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit_def
        using empty shape trace_candidate' distinct trace_low trace'_low
          rounds_positive vals
        unfolding partial_trace_table_candidates_def
        by blast
      then show ?thesis by simp
    qed
  qed
qed

lemma empty_header_partial_trace_candidate_nonunique_transcript_le_trace_fri_or_low_degree_transcript_query_agreement:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_partial_trace_candidate_nonunique_transcript)
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      trace_fri_bad_with_empty_composition_header_candidates)
    adversary_initial_state +
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit)
    adversary_initial_state"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?N =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_partial_trace_candidate_nonunique_transcript"
  let ?T =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      trace_fri_bad_with_empty_composition_header_candidates"
  let ?L =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit"
  have "wp_event ?M ?N adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?T out \<or> ?L out) adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        split: option.splits prod.splits
        dest:
          empty_header_partial_trace_candidate_nonunique_transcript_imp_trace_fri_or_low_degree_transcript_query_agreement)
  also have "... \<le>
      wp_event ?M ?T adversary_initial_state +
      wp_event ?M ?L adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

definition composition_alpha_partial_opening_union_hit_with_empty_header_transcript
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_alpha_partial_opening_union_hit_with_empty_header_transcript
      s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      accepted_transcript_shape s out as trace_query_idxs \<and>
      as \<in> partial_trace_opening_alpha_union_bad_sets trace_openings)"

lemma composition_alpha_partial_opening_union_hit_with_empty_header_transcript_imp_union_hit:
  assumes
    "composition_alpha_partial_opening_union_hit_with_empty_header_transcript
      s out"
  shows
    "composition_alpha_partial_opening_union_hit_with_empty_header s out"
  using assms
  unfolding
    composition_alpha_partial_opening_union_hit_with_empty_header_transcript_def
    composition_alpha_partial_opening_union_hit_with_empty_header_def
  by blast

definition composition_bad_with_empty_composition_header_candidates_transcript
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_bad_with_empty_composition_header_candidates_transcript
      s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table f.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      accepted_transcript_shape s out as trace_query_idxs \<and>
      degree f < clength \<and>
      trace_table = map (poly f) eval_domain \<and>
      violated_constraints f \<noteq> {} \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as)"

definition composition_degree_bad_with_empty_composition_header_candidates_transcript
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_degree_bad_with_empty_composition_header_candidates_transcript
      s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table f.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      accepted_transcript_shape s out as trace_query_idxs \<and>
      degree f < clength \<and>
      trace_table = map (poly f) eval_domain \<and>
      violated_constraints f \<noteq> {} \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as \<and>
      \<not> common_denominator_degree_bounds f as)"

definition composition_randomization_bad_with_empty_composition_header_candidates_transcript
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_randomization_bad_with_empty_composition_header_candidates_transcript
      s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table f.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      accepted_transcript_shape s out as trace_query_idxs \<and>
      degree f < clength \<and>
      trace_table = map (poly f) eval_domain \<and>
      violated_constraints f \<noteq> {} \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as \<and>
      common_denominator_degree_bounds f as \<and>
      random_combination_common_denominator_hides_violations f as)"

lemma composition_bad_with_empty_composition_header_candidates_transcript_split:
  assumes false_statement: "\<not> exists_valid_trace"
    and bad:
      "composition_bad_with_empty_composition_header_candidates_transcript
        s out"
  shows
    "composition_degree_bad_with_empty_composition_header_candidates_transcript
        s out \<or>
     composition_randomization_bad_with_empty_composition_header_candidates_transcript
        s out"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table f where partial:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and shape: "accepted_transcript_shape s out as trace_query_idxs"
    and deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    and violated: "violated_constraints f \<noteq> {}"
    and composition_low:
      "composition_table_low_degree maxDegree composition_table"
    and all_queries:
      "all_queries_consistent trace_table composition_table as"
    using bad
    unfolding
      composition_bad_with_empty_composition_header_candidates_transcript_def
    by blast
  show ?thesis
  proof (cases "common_denominator_degree_bounds f as")
    case False
    then have
      "composition_degree_bad_with_empty_composition_header_candidates_transcript
        s out"
      unfolding
        composition_degree_bad_with_empty_composition_header_candidates_transcript_def
      using partial shape deg_f trace_table violated composition_low
        all_queries
      by blast
    then show ?thesis by simp
  next
    case True
    note bounds = True
    have len_as: "length as = length spec"
    proof -
      obtain result final_state fr' f_fri_roots' f_final' dg'
          composition_fri_roots' final' rest' where
        "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
          composition_fri_roots' final' rest'"
        using shape
        by (elim accepted_transcript_shape_header_query_extraction)
      then show ?thesis
        by (rule verifier_header_transcript_shapes(3))
    qed
    have hides:
      "random_combination_common_denominator_hides_violations f as"
      by (rule random_combination_common_denominator_hides_from_queries
          [OF len_as false_statement deg_f trace_table composition_low
            all_queries bounds])
    have
      "composition_randomization_bad_with_empty_composition_header_candidates_transcript
        s out"
      unfolding
        composition_randomization_bad_with_empty_composition_header_candidates_transcript_def
      using partial shape deg_f trace_table violated composition_low
        all_queries bounds hides
      by blast
    then show ?thesis by simp
  qed
qed

lemma composition_degree_bad_with_empty_composition_header_candidates_transcript_imp_degree_bad:
  assumes
    "composition_degree_bad_with_empty_composition_header_candidates_transcript
      s out"
  shows
    "composition_degree_bad_with_empty_composition_header_candidates s out"
  using assms
  unfolding
    composition_degree_bad_with_empty_composition_header_candidates_transcript_def
    composition_degree_bad_with_empty_composition_header_candidates_def
  by blast

lemma composition_degree_bad_with_empty_composition_header_candidates_transcript_false:
  "\<not> composition_degree_bad_with_empty_composition_header_candidates_transcript
      s out"
  using
    composition_degree_bad_with_empty_composition_header_candidates_transcript_imp_degree_bad
    composition_degree_bad_with_empty_composition_header_candidates_false
  by blast

lemma composition_degree_bad_with_empty_composition_header_candidates_transcript_bound:
  "wp_event verify_monad
    (composition_degree_bad_with_empty_composition_header_candidates_transcript
      s) s \<le>
    0"
proof -
  have "composition_degree_bad_with_empty_composition_header_candidates_transcript
      s =
      (\<lambda>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
        False)"
    by (rule ext)
      (simp add:
        composition_degree_bad_with_empty_composition_header_candidates_transcript_false)
  then show ?thesis
    unfolding wp_event_def wp_def dist_expect_def by simp
qed

lemma composition_randomization_bad_with_empty_composition_header_candidates_transcript_imp_alpha_union_hit:
  assumes bad:
    "composition_randomization_bad_with_empty_composition_header_candidates_transcript
      s out"
  shows
    "composition_alpha_partial_opening_union_hit_with_empty_header_transcript
      s out"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table f where partial:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and shape: "accepted_transcript_shape s out as trace_query_idxs"
    and deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    and violated: "violated_constraints f \<noteq> {}"
    and bounds: "common_denominator_degree_bounds f as"
    and hides:
      "random_combination_common_denominator_hides_violations f as"
    using bad
    unfolding
      composition_randomization_bad_with_empty_composition_header_candidates_transcript_def
    by blast
  have as_in:
    "as \<in> common_denominator_hiding_alpha_space f"
  proof -
    obtain result final_state fr' f_fri_roots' f_final' dg'
        composition_fri_roots' final' rest' where header:
      "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
      using shape
      by (elim accepted_transcript_shape_header_query_extraction)
    have len_as: "length as = length spec"
      by (rule verifier_header_transcript_shapes(3)[OF header])
    show ?thesis
      using len_as hides
      unfolding common_denominator_hiding_alpha_space_def alpha_space_def
      by simp
  qed
  have candidate:
    "trace_table \<in> partial_trace_table_candidates trace_openings"
    using partial
    unfolding accepted_with_empty_composition_header_candidates_def
      partial_trace_table_candidates_def
    by simp
  have witness_eq: "low_degree_trace_witness trace_table = f"
    by (rule low_degree_trace_witness_eq[OF deg_f trace_table])
  have as_bad: "as \<in> composition_trace_bad_alpha_space trace_table"
    using deg_f trace_table violated bounds as_in
    unfolding composition_trace_bad_alpha_space_def witness_eq
    by simp
  have "as \<in> partial_trace_opening_alpha_union_bad_sets trace_openings"
    unfolding partial_trace_opening_alpha_union_bad_sets_def
    using candidate as_bad by blast
  then show ?thesis
    unfolding
      composition_alpha_partial_opening_union_hit_with_empty_header_transcript_def
    using partial shape by blast
qed

lemma composition_alpha_partial_opening_union_hit_with_empty_header_transcript_split:
  assumes hit:
    "composition_alpha_partial_opening_union_hit_with_empty_header_transcript
      s out"
  shows
    "composition_alpha_bad_set_hit_with_empty_composition_header_candidates
        s out \<or>
     empty_header_partial_trace_candidate_nonunique_transcript s out"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table where partial:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and shape: "accepted_transcript_shape s out as trace_query_idxs"
    and as_union:
      "as \<in> partial_trace_opening_alpha_union_bad_sets trace_openings"
    using hit
    unfolding
      composition_alpha_partial_opening_union_hit_with_empty_header_transcript_def
    by blast
  from as_union obtain trace_table' where candidate':
      "trace_table' \<in> partial_trace_table_candidates trace_openings"
    and as_bad': "as \<in> composition_trace_bad_alpha_space trace_table'"
    unfolding partial_trace_opening_alpha_union_bad_sets_def by blast
  have candidate:
    "trace_table \<in> partial_trace_table_candidates trace_openings"
    using partial
    unfolding accepted_with_empty_composition_header_candidates_def
      partial_trace_table_candidates_def
    by simp
  show ?thesis
  proof (cases
      "\<exists>trace_table0.
        partial_trace_table_candidates trace_openings \<subseteq>
          {trace_table0}")
    case True
    then obtain trace_table0 where subset:
      "partial_trace_table_candidates trace_openings \<subseteq>
        {trace_table0}"
      by blast
    have trace_eq: "trace_table = trace_table0"
      using subset candidate by blast
    have trace'_eq: "trace_table' = trace_table0"
      using subset candidate' by blast
    have "as \<in> composition_trace_bad_alpha_space trace_table"
      using as_bad' trace_eq trace'_eq by simp
    then have
      "composition_alpha_bad_set_hit_with_empty_composition_header_candidates
        s out"
      unfolding
        composition_alpha_bad_set_hit_with_empty_composition_header_candidates_def
      using partial by blast
    then show ?thesis by simp
  next
    case False
    have "empty_header_partial_trace_candidate_nonunique_transcript s out"
      unfolding empty_header_partial_trace_candidate_nonunique_transcript_def
      using partial shape False by blast
    then show ?thesis by simp
  qed
qed

definition checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      out \<longleftrightarrow>
    checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
      composition_trace_bad_alpha_space out \<and>
    checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header_transcript
      out"

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_le_fixed_or_nonunique_transcript:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
    adversary_initial_state +
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_partial_trace_candidate_nonunique_transcript)
    adversary_initial_state"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?fixed =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates"
  let ?nonunique =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_partial_trace_candidate_nonunique_transcript"
  have "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?fixed out \<or> ?nonunique out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_def
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        split: option.splits prod.splits
        dest:
          composition_alpha_partial_opening_union_hit_with_empty_header_transcript_split)
  also have "... \<le>
      wp_event ?M ?fixed adversary_initial_state +
      wp_event ?M ?nonunique adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_bound_from_fixed_and_nonunique_transcript:
  assumes fixed_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and nonunique_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          empty_header_partial_trace_candidate_nonunique_transcript)
        adversary_initial_state \<le> N"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      adversary_initial_state \<le> F + N"
  by (rule order_trans[
      OF
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_le_fixed_or_nonunique_transcript])
    (intro add_mono fixed_bound nonunique_bound)

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_le_relevant_drift:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
    adversary_initial_state"
  by (rule wp_event_mono)
    (auto simp:
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_def
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_def
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      split: option.splits prod.splits
      intro:
        composition_alpha_partial_opening_union_hit_with_empty_header_transcript_imp_union_hit)

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_bound_from_relevant_drift:
  assumes drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
        adversary_initial_state \<le> D"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      adversary_initial_state \<le> D"
  by (rule order_trans[
      OF
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_le_relevant_drift
        drift_bound])

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_le_fixed_or_trace_fri_or_low_degree_transcript:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
    adversary_initial_state +
   (wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      trace_fri_bad_with_empty_composition_header_candidates)
    adversary_initial_state +
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit)
    adversary_initial_state)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?fixed =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates"
  let ?nonunique =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_partial_trace_candidate_nonunique_transcript"
  let ?trace_fri =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      trace_fri_bad_with_empty_composition_header_candidates"
  let ?low_degree =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit"
  have split:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      adversary_initial_state \<le>
     wp_event ?M ?fixed adversary_initial_state +
     wp_event ?M ?nonunique adversary_initial_state"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_le_fixed_or_nonunique_transcript)
  have nonunique:
    "wp_event ?M ?nonunique adversary_initial_state \<le>
     wp_event ?M ?trace_fri adversary_initial_state +
     wp_event ?M ?low_degree adversary_initial_state"
    by (rule
        empty_header_partial_trace_candidate_nonunique_transcript_le_trace_fri_or_low_degree_transcript_query_agreement)
  show ?thesis
    by (rule order_trans[OF split])
      (intro add_mono order_refl nonunique)
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_bound_from_fixed_trace_fri_and_low_degree_transcript:
  assumes fixed_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and trace_fri_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> T"
    and low_degree_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          empty_header_low_degree_trace_candidate_nonunique_transcript_query_agreement_hit)
        adversary_initial_state \<le> L"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript
      adversary_initial_state \<le> F + (T + L)"
  by (rule order_trans[
      OF
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_transcript_le_fixed_or_trace_fri_or_low_degree_transcript])
    (intro add_mono fixed_bound add_mono trace_fri_bound low_degree_bound)

lemma empty_header_partial_trace_candidate_nonunique_le_trace_fri_or_low_degree_nonunique:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_partial_trace_candidate_nonunique)
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      trace_fri_bad_with_empty_composition_header_candidates)
    adversary_initial_state +
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique)
    adversary_initial_state"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?N =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_partial_trace_candidate_nonunique"
  let ?T =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      trace_fri_bad_with_empty_composition_header_candidates"
  let ?L =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique"
  have "wp_event ?M ?N adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?T out \<or> ?L out) adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        split: option.splits prod.splits
        dest:
          empty_header_partial_trace_candidate_nonunique_imp_trace_fri_or_low_degree_nonunique)
  also have "... \<le>
      wp_event ?M ?T adversary_initial_state +
      wp_event ?M ?L adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri:
  fixes D empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
        adversary_initial_state \<le> D"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_partial_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have comp_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> composition_fri_error"
    by (rule
        composition_fri_bad_with_partial_candidates_bound_from_reachable_reduction
        [OF composition_fri_reduction])
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound drift_bound empty_trace_fri_bound current_empty_bound])
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header:
  fixes F X empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and fixed_empty_alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (F + X) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
      adversary_initial_state \<le> F + X"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_bound_from_fixed_and_witnessed_cross
        [OF fixed_empty_alpha_bound cross_bound])
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound drift_bound
          current_empty_bound])
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_same_run_nonunique:
  fixes F N empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and fixed_empty_alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and nonunique_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          empty_header_partial_trace_candidate_nonunique)
        adversary_initial_state \<le> N"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (F + N) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
      adversary_initial_state \<le> F + N"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift_bound_from_fixed_and_nonunique
        [OF fixed_empty_alpha_bound nonunique_bound])
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound drift_bound
          current_empty_bound])
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_low_degree_nonunique:
  fixes F L empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and fixed_empty_alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and low_degree_nonunique_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          empty_header_low_degree_trace_candidate_nonunique)
        adversary_initial_state \<le> L"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (F + (trace_fri_error + L)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?T =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      trace_fri_bad_with_empty_composition_header_candidates"
  let ?L =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      empty_header_low_degree_trace_candidate_nonunique"
  have trace_fri_data_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        trace_fri_bad_with_empty_header_candidates_bound_from_reachable_reduction
        [OF trace_fri_reduction])
  have trace_fri_prefix_bound:
    "wp_event ?M ?T adversary_initial_state \<le> trace_fri_error"
  proof -
    have projected:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state =
       wp_event ?M ?T adversary_initial_state"
      by (rule
          checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection)
    show ?thesis
      using projected trace_fri_data_bound by simp
  qed
  have nonunique_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        empty_header_partial_trace_candidate_nonunique)
      adversary_initial_state \<le> trace_fri_error + L"
  proof (rule order_trans)
    show "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        empty_header_partial_trace_candidate_nonunique)
      adversary_initial_state \<le>
     wp_event ?M ?T adversary_initial_state +
     wp_event ?M ?L adversary_initial_state"
      by (rule
          empty_header_partial_trace_candidate_nonunique_le_trace_fri_or_low_degree_nonunique)
    show "... \<le> trace_fri_error + L"
      by (intro add_mono trace_fri_prefix_bound low_degree_nonunique_bound)
  qed
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_same_run_nonunique
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound fixed_empty_alpha_bound
          nonunique_bound current_empty_bound])
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_low_degree_nonunique_query_agreement:
  fixes F L empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and fixed_empty_alpha_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
        adversary_initial_state \<le> F"
    and low_degree_query_agreement_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          empty_header_low_degree_trace_candidate_nonunique_query_agreement_hit)
        adversary_initial_state \<le> L"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (F + (trace_fri_error + L)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have low_degree_nonunique_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        empty_header_low_degree_trace_candidate_nonunique)
      adversary_initial_state \<le> L"
    by (rule order_trans
        [OF empty_header_low_degree_trace_candidate_nonunique_le_query_agreement_hit
          low_degree_query_agreement_bound])
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_low_degree_nonunique
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound fixed_empty_alpha_bound
          low_degree_nonunique_bound current_empty_bound])
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_not_prefix:
  fixes X N empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> N"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      ((composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) + N) + X) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?P =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  have transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets
        [OF wf controlled])
  have prefix_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have fixed_empty_alpha_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
      adversary_initial_state \<le> ?P + N"
  proof (rule order_trans)
    show "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_bad_set_hit_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      wp_event ?M
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state +
      wp_event ?M
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_fixed_empty_alpha_hit_le_prefix_or_not_prefix
          [OF wf controlled])
    show "... \<le> ?P + N"
      by (intro add_mono prefix_bound not_prefix_bound)
  qed
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound fixed_empty_alpha_bound
          cross_bound current_empty_bound])
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_sampled_transcript:
  fixes X P R empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and sampled_transcript_new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      ((composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        (hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
         X + (P + R) + (P + R))) + X) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?N =
    "hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      X + (P + R) + (P + R)"
  have no_prefix_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_bound_from_sampled_transcript
        [OF data_pre_bound sampled_transcript_new_bound])
  have path_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_bound_from_sampled_transcript
        [OF data_pre_bound sampled_transcript_new_bound])
  have collision_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision_bound
        [OF wf controlled])
  have uncovered_bound:
    "wp_event ?M
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      adversary_initial_state \<le> X"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_witnessed_cross_or_merkle_bad
          cross_bound])
  have not_prefix_bound:
    "wp_event ?M
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?N"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_bound])
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_not_prefix
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound not_prefix_bound cross_bound
          current_empty_bound])
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_transcript_pre:
  fixes X P empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      ((composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        (hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
         X + (P + staged_concrete_transcript_target_error_bound) +
         (P + staged_concrete_transcript_target_error_bound))) + X) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have sampled_transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_sampled_transcript
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound cross_bound data_pre_bound
          sampled_transcript_new_bound current_empty_bound])
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_transcript_pre_and_split_cross:
  fixes S H P empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and sparse_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_sparse_cross_bad
        adversary_initial_state \<le> S"
    and merkle_side_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
        adversary_initial_state \<le> H"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      ((composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        (hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
         (S + H) + (P + staged_concrete_transcript_target_error_bound) +
         (P + staged_concrete_transcript_target_error_bound))) + (S + H)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have cross_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
      adversary_initial_state \<le> S + H"
  proof (rule order_trans)
    show "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witnessed_sparse_cross_bad
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
      adversary_initial_state"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad_le_sparse_or_merkle_side)
    show "... \<le> S + H"
      by (intro add_mono sparse_bound merkle_side_bound)
  qed
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_transcript_pre
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound cross_bound data_pre_bound
          current_empty_bound])
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_transcript_pre_and_split_cross_and_merkle_side:
  fixes S L K P empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        trace_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and composition_fri_reduction:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        composition_fri_reachable_partial_candidate_reduction_assumption
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and sparse_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_sparse_cross_bad
        adversary_initial_state \<le> S"
    and local_collision_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_local_collision_bad
        adversary_initial_state \<le> L"
    and coupling_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_coupling_bad
        adversary_initial_state \<le> K"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error + composition_fri_error +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      ((composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        (hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
         (S + (L + K)) + (P + staged_concrete_transcript_target_error_bound) +
         (P + staged_concrete_transcript_target_error_bound))) +
          (S + (L + K))) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have merkle_side_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
      adversary_initial_state \<le> L + K"
  proof (rule order_trans)
    show "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witnessed_local_collision_bad
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witnessed_coupling_bad
      adversary_initial_state"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_witnessed_merkle_side_bad_le_local_or_coupling)
    show "... \<le> L + K"
      by (intro add_mono local_collision_bound coupling_bound)
  qed
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_transcript_pre_and_split_cross
        [OF false_statement wf controlled trace_fri_reduction
          composition_fri_reduction round_bound sparse_bound
          merkle_side_bound data_pre_bound current_empty_bound])
qed

end

text \<open>
  These wrappers expose the broad witnessed cross/Merkle diagnostic split used
  during development of the reachable-FRI route.  They remain available only as
  internal plumbing; the public route should use aligned transcript-indexed
  wrappers that do not expose these diagnostic events.
\<close>

hide_fact
  soundness.stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri
  soundness.stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header
  soundness.stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_same_run_nonunique
  soundness.stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_low_degree_nonunique
  soundness.stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_low_degree_nonunique_query_agreement
  soundness.stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_not_prefix
  soundness.stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_sampled_transcript
  soundness.stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_transcript_pre
  soundness.stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_transcript_pre_and_split_cross
  soundness.stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_reachable_fri_split_empty_header_from_transcript_pre_and_split_cross_and_merkle_side

end
