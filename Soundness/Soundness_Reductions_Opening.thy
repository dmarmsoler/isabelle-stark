(*  Title:      Stark/Soundness_Reductions_Opening.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Reductions_Opening
  imports Soundness_Reductions_Partial
begin

text \<open>FRI opening algebraic covers and final reduction bounds.\<close>

context soundness
begin

text \<open>
  The multiround bad-set constructors above isolate the proof-only part of the
  FRI reductions: once an algebraic cover and the corresponding error-fraction
  bound are available, the existing opening-reduction assumptions follow
  directly.  The current transcript predicate records authenticated local
  openings, but it does not bind complete intermediate FRI layer tables.  Thus
  the algebraic cover is still an external FRI/table-binding theorem target
  unless the protocol model is extended with such tables or an equivalent
  binding interface.
\<close>

definition trace_fri_bad_challenge_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow> bool"
  where
    "trace_fri_bad_challenge_cover s bad_sets \<longleftrightarrow>
      (\<forall>out \<in> set_dist (execute verify_monad s).
        trace_fri_bad s out \<longrightarrow>
          trace_fri_challenge_set_hit s bad_sets out)"

definition composition_fri_bad_challenge_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> 'f list set) \<Rightarrow> bool"
  where
    "composition_fri_bad_challenge_cover s bad_sets \<longleftrightarrow>
      (\<forall>out \<in> set_dist (execute verify_monad s).
        composition_fri_bad s out \<longrightarrow>
          composition_fri_challenge_set_hit s bad_sets out)"

lemma trace_fri_opening_algebraic_cover_imp_bad_challenge_cover:
  assumes cover: "trace_fri_opening_algebraic_cover s bad_sets"
  shows "trace_fri_bad_challenge_cover s bad_sets"
  unfolding trace_fri_bad_challenge_cover_def
proof (intro ballI impI)
  fix out :: "(unit list \<times> ('f, 'a) protocol_channel_scheme) option"
  assume outcome: "out \<in> set_dist (execute verify_monad s)"
    and bad: "trace_fri_bad s out"
  then obtain trace_table composition_table as query_idxs where bound:
      "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
    and not_low: "\<not> trace_table_low_degree trace_table"
    unfolding trace_fri_bad_def by blast
  from accepted_with_bound_tables_imp_accepted[OF bound]
  obtain result final_state where out_eq: "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  have verify_out:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using outcome out_eq by simp
  from verify_monad_accepted_fri_opening_transcript[OF verify_out]
  obtain trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final query_idxs' trace_round_layers composition_round_layers
    where openings:
      "accepted_fri_opening_transcript s (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final query_idxs' trace_round_layers composition_round_layers"
    by blast
  have trace_bs_bad: "trace_bs \<in> bad_sets trace_table"
    using cover bound openings not_low out_eq
    unfolding trace_fri_opening_algebraic_cover_def by blast
  have challenges:
    "accepted_fri_challenges s out trace_bs dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF openings] out_eq by simp
  show "trace_fri_challenge_set_hit s bad_sets out"
    unfolding trace_fri_challenge_set_hit_def
    using bound challenges not_low trace_bs_bad by blast
qed

lemma composition_fri_opening_algebraic_cover_imp_bad_challenge_cover:
  assumes cover: "composition_fri_opening_algebraic_cover s bad_sets"
  shows "composition_fri_bad_challenge_cover s bad_sets"
  unfolding composition_fri_bad_challenge_cover_def
proof (intro ballI impI)
  fix out :: "(unit list \<times> ('f, 'a) protocol_channel_scheme) option"
  assume outcome: "out \<in> set_dist (execute verify_monad s)"
    and bad: "composition_fri_bad s out"
  then obtain trace_table composition_table as query_idxs where bound:
      "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
    and trace_low: "trace_table_low_degree trace_table"
    and not_low: "\<not> composition_table_low_degree maxDegree composition_table"
    unfolding composition_fri_bad_def by blast
  from accepted_with_bound_tables_imp_accepted[OF bound]
  obtain result final_state where out_eq: "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  have verify_out:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using outcome out_eq by simp
  from verify_monad_accepted_fri_opening_transcript[OF verify_out]
  obtain trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final query_idxs' trace_round_layers composition_round_layers
    where openings:
      "accepted_fri_opening_transcript s (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final query_idxs' trace_round_layers composition_round_layers"
    by blast
  have composition_bs_bad: "composition_bs \<in> bad_sets dg composition_table"
    using cover bound openings trace_low not_low out_eq
    unfolding composition_fri_opening_algebraic_cover_def by blast
  have challenges:
    "accepted_fri_challenges s out trace_bs dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF openings] out_eq by simp
  show "composition_fri_challenge_set_hit s bad_sets out"
    unfolding composition_fri_challenge_set_hit_def
    using bound challenges trace_low not_low composition_bs_bad by blast
qed

definition trace_fri_challenge_freshness_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "trace_fri_challenge_freshness_assumption s \<longleftrightarrow>
      (\<forall>bad_sets.
        trace_fri_bad_challenge_sets_bounded bad_sets \<longrightarrow>
        wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le>
          trace_fri_error)"

definition composition_fri_challenge_freshness_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "composition_fri_challenge_freshness_assumption s \<longleftrightarrow>
      (\<forall>bad_sets.
        composition_fri_bad_challenge_sets_bounded bad_sets \<longrightarrow>
        wp_event verify_monad
          (composition_fri_challenge_set_hit s bad_sets) s \<le>
          composition_fri_error)"

definition random_oracle_freshness_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "random_oracle_freshness_assumption s \<longleftrightarrow>
      alpha_challenge_freshness_assumption s \<and>
      query_index_freshness_assumption s \<and>
      trace_fri_challenge_freshness_assumption s \<and>
      composition_fri_challenge_freshness_assumption s"

lemma random_oracle_freshness_alpha:
  assumes "random_oracle_freshness_assumption s"
  shows "alpha_challenge_freshness_assumption s"
  using assms unfolding random_oracle_freshness_assumption_def by simp

lemma random_oracle_freshness_query:
  assumes "random_oracle_freshness_assumption s"
  shows "query_index_freshness_assumption s"
  using assms unfolding random_oracle_freshness_assumption_def by simp

lemma random_oracle_freshness_trace_fri:
  assumes "random_oracle_freshness_assumption s"
  shows "trace_fri_challenge_freshness_assumption s"
  using assms unfolding random_oracle_freshness_assumption_def by simp

lemma random_oracle_freshness_composition_fri:
  assumes "random_oracle_freshness_assumption s"
  shows "composition_fri_challenge_freshness_assumption s"
  using assms unfolding random_oracle_freshness_assumption_def by simp

lemma alpha_challenge_freshness_if_no_supported_pairwise_merkle_bad:
  assumes future: "alpha_future_fresh s"
    and no_bad: "\<not> alpha_supported_pairwise_merkle_bad s"
  shows "alpha_challenge_freshness_assumption s"
  unfolding alpha_challenge_freshness_assumption_def
proof (intro allI impI)
  fix bad_sets :: "'f list \<Rightarrow> 'f list set"
  assume subset:
      "\<forall>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bounded:
      "\<forall>trace_table.
        nnreal (card (bad_sets trace_table)) /
          nnreal (card alpha_space) \<le> composition_error_bound"
  show "wp_event verify_monad (alpha_bad_set_hit s bad_sets) s \<le>
      composition_error_bound"
  proof (rule wp_alpha_bad_set_hit_bound_via_supported_header_union
      [OF future])
    fix trace_table
    show "bad_sets trace_table \<subseteq> alpha_space"
      using subset by blast
  next
    fix fr f_fri_roots f_final
    have unique:
      "\<exists>trace_table.
        alpha_header_supported_trace_table_candidates s fr f_fri_roots
          f_final \<subseteq> {trace_table}"
      by (rule alpha_header_supported_candidate_unique_if_no_global_pairwise_merkle_bad
          [OF no_bad])
    show
      "nnreal
        (card
          (alpha_header_supported_union_bad_sets s bad_sets fr f_fri_roots
            f_final)) /
        nnreal (card alpha_space) \<le> composition_error_bound"
      by (rule alpha_header_supported_union_bad_sets_fraction_bound_if_unique_candidate
          [OF unique])
        (use subset bounded in blast)+
  qed
qed

lemma trace_fri_challenge_freshness_if_no_supported_pairwise_merkle_bad:
  assumes future: "trace_fri_future_fresh s"
    and no_bad: "\<not> trace_fri_supported_pairwise_merkle_bad s"
  shows "trace_fri_challenge_freshness_assumption s"
  unfolding trace_fri_challenge_freshness_assumption_def
proof (intro allI impI)
  fix bad_sets :: "'f list \<Rightarrow> 'f list set"
  assume bounded: "trace_fri_bad_challenge_sets_bounded bad_sets"
  show "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le>
      trace_fri_error"
    by (rule
        wp_trace_fri_challenge_set_hit_bound_if_no_supported_pairwise_merkle_bad
        [OF future no_bad bounded])
qed

lemma composition_fri_challenge_freshness_if_no_supported_pairwise_merkle_bad:
  assumes future: "composition_fri_future_fresh s"
    and no_bad: "\<not> composition_fri_supported_pairwise_merkle_bad s"
  shows "composition_fri_challenge_freshness_assumption s"
  unfolding composition_fri_challenge_freshness_assumption_def
proof (intro allI impI)
  fix bad_sets :: "'f \<Rightarrow> 'f list \<Rightarrow> 'f list set"
  assume bounded: "composition_fri_bad_challenge_sets_bounded bad_sets"
  show
    "wp_event verify_monad
      (composition_fri_challenge_set_hit s bad_sets) s \<le>
      composition_fri_error"
    by (rule
        wp_composition_fri_challenge_set_hit_bound_if_no_supported_pairwise_merkle_bad
        [OF future no_bad bounded])
qed

lemma verifier_initial_alpha_challenge_freshness_if_no_supported_pairwise_merkle_bad:
  assumes no_bad:
    "\<not> alpha_supported_pairwise_merkle_bad (verifier_initial_state tr)"
  shows "alpha_challenge_freshness_assumption (verifier_initial_state tr)"
  by (rule alpha_challenge_freshness_if_no_supported_pairwise_merkle_bad)
    (use no_bad in simp_all)

lemma verifier_initial_trace_fri_challenge_freshness_if_no_supported_pairwise_merkle_bad:
  assumes no_bad:
    "\<not> trace_fri_supported_pairwise_merkle_bad (verifier_initial_state tr)"
  shows
    "trace_fri_challenge_freshness_assumption (verifier_initial_state tr)"
  by (rule trace_fri_challenge_freshness_if_no_supported_pairwise_merkle_bad)
    (use no_bad in simp_all)

lemma verifier_initial_composition_fri_challenge_freshness_if_no_supported_pairwise_merkle_bad:
  assumes no_bad:
    "\<not> composition_fri_supported_pairwise_merkle_bad
      (verifier_initial_state tr)"
  shows
    "composition_fri_challenge_freshness_assumption
      (verifier_initial_state tr)"
  by (rule
      composition_fri_challenge_freshness_if_no_supported_pairwise_merkle_bad)
    (use no_bad in simp_all)

lemma alpha_challenge_freshness_if_no_pairwise_side_bad:
  assumes future: "alpha_future_fresh s"
    and no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "alpha_challenge_freshness_assumption s"
proof (rule alpha_challenge_freshness_if_no_supported_pairwise_merkle_bad
    [OF future])
  show "\<not> alpha_supported_pairwise_merkle_bad s"
    by (rule no_alpha_supported_pairwise_merkle_bad_if_no_pairwise_side_bad
        [OF no_collision no_coupling])
qed

lemma query_index_freshness_if_no_pairwise_side_bad:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "query_index_freshness_assumption s"
proof (rule query_index_freshness_if_no_query_supported_pairwise_merkle_bad
    [OF future raw_bound])
  show "\<not> query_supported_pairwise_merkle_bad s"
    by (rule no_query_supported_pairwise_merkle_bad_if_no_pairwise_side_bad
        [OF no_collision no_coupling])
qed

lemma trace_fri_challenge_freshness_if_no_pairwise_side_bad:
  assumes future: "trace_fri_future_fresh s"
    and no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "trace_fri_challenge_freshness_assumption s"
proof (rule trace_fri_challenge_freshness_if_no_supported_pairwise_merkle_bad
    [OF future])
  show "\<not> trace_fri_supported_pairwise_merkle_bad s"
    by (rule
        no_trace_fri_supported_pairwise_merkle_bad_if_no_pairwise_side_bad
        [OF no_collision no_coupling])
qed

lemma composition_fri_challenge_freshness_if_no_pairwise_side_bad:
  assumes future: "composition_fri_future_fresh s"
    and no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "composition_fri_challenge_freshness_assumption s"
proof (rule
    composition_fri_challenge_freshness_if_no_supported_pairwise_merkle_bad
    [OF future])
  show "\<not> composition_fri_supported_pairwise_merkle_bad s"
    by (rule
        no_composition_fri_supported_pairwise_merkle_bad_if_no_pairwise_side_bad
        [OF no_collision no_coupling])
qed

lemma random_oracle_freshness_if_no_pairwise_side_bad:
  assumes alpha_future: "alpha_future_fresh s"
    and query_future: "query_future_fresh s"
    and trace_future: "trace_fri_future_fresh s"
    and composition_future: "composition_fri_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "random_oracle_freshness_assumption s"
  unfolding random_oracle_freshness_assumption_def
proof (intro conjI)
  show "alpha_challenge_freshness_assumption s"
    by (rule alpha_challenge_freshness_if_no_pairwise_side_bad
        [OF alpha_future no_collision no_coupling])
  show "query_index_freshness_assumption s"
    by (rule query_index_freshness_if_no_pairwise_side_bad
        [OF query_future raw_bound no_collision no_coupling])
  show "trace_fri_challenge_freshness_assumption s"
    by (rule trace_fri_challenge_freshness_if_no_pairwise_side_bad
        [OF trace_future no_collision no_coupling])
  show "composition_fri_challenge_freshness_assumption s"
    by (rule composition_fri_challenge_freshness_if_no_pairwise_side_bad
        [OF composition_future no_collision no_coupling])
qed

lemma query_bad_bound_if_no_pairwise_side_bad:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "wp_event verify_monad (query_bad s) s \<le>
    nnreal rounds * query_error_bound"
proof -
  have query_fresh: "query_index_freshness_assumption s"
    by (rule query_index_freshness_if_no_pairwise_side_bad
        [OF future raw_bound no_collision no_coupling])
  show ?thesis
    by (rule query_bad_bound_from_phase4B[OF query_fresh])
qed

lemma query_bad_bound_if_no_pairwise_side_event_on_support:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and no_side:
      "\<And>out. out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
        \<not> supported_pairwise_side_bad s out"
  shows "wp_event verify_monad (query_bad s) s \<le>
    nnreal rounds * query_error_bound"
proof -
  have no_collision: "\<not> supported_hash_output_collision_possible s"
    by (rule
        no_supported_pairwise_side_bad_on_support_imp_no_hash_collision_possible
        [OF no_side])
  have no_coupling: "\<not> supported_pairwise_coupling_bad s"
    by (rule no_supported_pairwise_side_bad_on_support_imp_no_coupling_bad
        [OF no_side])
  show ?thesis
    by (rule query_bad_bound_if_no_pairwise_side_bad
        [OF future raw_bound no_collision no_coupling])
qed

lemma query_bad_bound_if_no_pairwise_side_event_on_support_from_sampler_wellformed:
  assumes future: "query_future_fresh s"
    and no_side:
      "\<And>out. out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
        \<not> supported_pairwise_side_bad s out"
  shows "wp_event verify_monad (query_bad s) s \<le>
    nnreal rounds * query_error_bound"
  by (rule query_bad_bound_if_no_pairwise_side_event_on_support
      [OF future query_index_raw_preimage_bound_from_sampler_wellformed
        no_side])

lemma composition_bad_bound_if_no_pairwise_side_bad:
  assumes wf: "spec_degree_wellformed"
    and future: "alpha_future_fresh s"
    and no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "wp_event verify_monad (composition_bad s) s \<le>
    composition_error_bound"
proof -
  have alpha_fresh: "alpha_challenge_freshness_assumption s"
    by (rule alpha_challenge_freshness_if_no_pairwise_side_bad
        [OF future no_collision no_coupling])
  show ?thesis
    by (rule composition_bad_bound_from_phase4A[OF wf alpha_fresh])
qed

lemma composition_bad_bound_if_no_pairwise_side_event_on_support:
  assumes wf: "spec_degree_wellformed"
    and future: "alpha_future_fresh s"
    and no_side:
      "\<And>out. out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
        \<not> supported_pairwise_side_bad s out"
  shows "wp_event verify_monad (composition_bad s) s \<le>
    composition_error_bound"
proof -
  have no_collision: "\<not> supported_hash_output_collision_possible s"
    by (rule
        no_supported_pairwise_side_bad_on_support_imp_no_hash_collision_possible
        [OF no_side])
  have no_coupling: "\<not> supported_pairwise_coupling_bad s"
    by (rule no_supported_pairwise_side_bad_on_support_imp_no_coupling_bad
        [OF no_side])
  show ?thesis
    by (rule composition_bad_bound_if_no_pairwise_side_bad
        [OF wf future no_collision no_coupling])
qed

lemma verifier_initial_random_oracle_freshness_if_sampler_wellformed_and_no_pairwise_side_bad:
  \<comment> \<open>The sampler wellformedness assumptions from the protocol locale bound the
      non-uniform modulo projection by its exact raw-preimage envelope.\<close>
  assumes no_collision:
      "\<not> supported_hash_output_collision_possible (verifier_initial_state tr)"
    and no_coupling:
      "\<not> supported_pairwise_coupling_bad (verifier_initial_state tr)"
  shows "random_oracle_freshness_assumption (verifier_initial_state tr)"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule random_oracle_freshness_if_no_pairwise_side_bad
        [OF _ _ _ _ raw_bound no_collision no_coupling])
      simp_all
qed

text \<open>
  The remaining soundness interfaces have the following status without changing
  the protocol.  The predicate \<^term>\<open>initial_merkle_binding_no_bad\<close> is a
  cryptographic/model boundary excluding accepted executions whose local
  Merkle openings cannot be extended to full committed tables.  The predicate
  \<^term>\<open>random_oracle_freshness_assumption\<close> is a random-oracle model boundary:
  its component projections are deterministic,
  but deriving freshness itself would require assumptions about the hash oracle,
  and deriving domain separation internally would require protocol labels that
  are not present in the current formalization.

  The two FRI reduction interfaces are proof obligations rather than protocol
  changes.  Each packages an opening-transcript algebraic cover with a bounded
  bad-challenge-set statement.  The lemmas below derive the verifier bad-event
  bounds directly from those opening-based interfaces.
\<close>

lemma trace_fri_bad_bound_from_opening_reduction:
  assumes reduction: "trace_fri_opening_reduction_assumption s"
    and fresh: "trace_fri_challenge_freshness_assumption s"
  shows "wp_event verify_monad (trace_fri_bad s) s \<le> trace_fri_error"
proof -
  from reduction obtain bad_sets where opening_cover:
      "trace_fri_opening_algebraic_cover s bad_sets"
    and bounded:
      "trace_fri_bad_challenge_sets_bounded bad_sets"
    by (rule trace_fri_opening_reductionE)
  have cover: "trace_fri_bad_challenge_cover s bad_sets"
    by (rule trace_fri_opening_algebraic_cover_imp_bad_challenge_cover
        [OF opening_cover])
  have "wp_event verify_monad (trace_fri_bad s) s \<le>
      wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s"
    by (rule wp_event_mono_on_support)
      (use cover in \<open>auto simp: trace_fri_bad_challenge_cover_def\<close>)
  also have "... \<le> trace_fri_error"
    using fresh bounded
    unfolding trace_fri_challenge_freshness_assumption_def by blast
  finally show ?thesis .
qed

lemma composition_fri_bad_bound_from_opening_reduction:
  assumes reduction: "composition_fri_opening_reduction_assumption s"
    and fresh: "composition_fri_challenge_freshness_assumption s"
  shows "wp_event verify_monad (composition_fri_bad s) s \<le>
    composition_fri_error"
proof -
  from reduction obtain bad_sets where opening_cover:
      "composition_fri_opening_algebraic_cover s bad_sets"
    and bounded:
      "composition_fri_bad_challenge_sets_bounded bad_sets"
    by (rule composition_fri_opening_reductionE)
  have cover: "composition_fri_bad_challenge_cover s bad_sets"
    by (rule composition_fri_opening_algebraic_cover_imp_bad_challenge_cover
        [OF opening_cover])
  have "wp_event verify_monad (composition_fri_bad s) s \<le>
      wp_event verify_monad
        (composition_fri_challenge_set_hit s bad_sets) s"
    by (rule wp_event_mono_on_support)
      (use cover in \<open>auto simp: composition_fri_bad_challenge_cover_def\<close>)
  also have "... \<le> composition_fri_error"
    using fresh bounded
    unfolding composition_fri_challenge_freshness_assumption_def by blast
  finally show ?thesis .
qed

lemma trace_fri_bad_with_partial_openings_bound_from_opening_reduction:
  assumes reduction: "trace_fri_opening_reduction_assumption s"
    and fresh: "trace_fri_challenge_freshness_assumption s"
  shows "wp_event verify_monad (trace_fri_bad_with_partial_openings s) s \<le>
    trace_fri_error"
proof -
  have "wp_event verify_monad (trace_fri_bad_with_partial_openings s) s \<le>
      wp_event verify_monad (trace_fri_bad s) s"
    by (rule wp_trace_fri_bad_with_partial_openings_le_trace_fri_bad)
  also have "... \<le> trace_fri_error"
    by (rule trace_fri_bad_bound_from_opening_reduction
        [OF reduction fresh])
  finally show ?thesis .
qed

lemma composition_fri_bad_with_partial_openings_bound_from_opening_reduction:
  assumes reduction: "composition_fri_opening_reduction_assumption s"
    and fresh: "composition_fri_challenge_freshness_assumption s"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_partial_openings s) s \<le>
      composition_fri_error"
proof -
  have "wp_event verify_monad
        (composition_fri_bad_with_partial_openings s) s \<le>
      wp_event verify_monad (composition_fri_bad s) s"
    by (rule
        wp_composition_fri_bad_with_partial_openings_le_composition_fri_bad)
  also have "... \<le> composition_fri_error"
    by (rule composition_fri_bad_bound_from_opening_reduction
        [OF reduction fresh])
  finally show ?thesis .
qed

lemma trace_fri_with_tables_bad_sets_bounded_if_error_ge_one:
  assumes error_ge_one: "1 \<le> trace_fri_error"
  shows "trace_fri_bad_challenge_sets_bounded
    (trace_fri_with_tables_bad_sets s)"
  unfolding trace_fri_bad_challenge_sets_bounded_def
proof (intro allI conjI)
  fix trace_table
  show "trace_fri_with_tables_bad_sets s trace_table \<subseteq>
      fri_challenge_space (ceil_log clength)"
    by (rule trace_fri_with_tables_bad_sets_subset)
  show "nnreal (card (trace_fri_with_tables_bad_sets s trace_table)) /
      nnreal (CARD('f) ^ ceil_log clength) \<le> trace_fri_error"
    by (rule order_trans
        [OF trace_fri_with_tables_bad_sets_fraction_le_one error_ge_one])
qed

lemma composition_fri_with_tables_bad_sets_bounded_if_error_ge_one:
  assumes error_ge_one: "1 \<le> composition_fri_error"
  shows "composition_fri_bad_challenge_sets_bounded
    (composition_fri_with_tables_bad_sets s)"
  unfolding composition_fri_bad_challenge_sets_bounded_def
proof (intro allI conjI)
  fix dg composition_table
  show "composition_fri_with_tables_bad_sets s dg composition_table \<subseteq>
      fri_challenge_space (ceil_log (to_nat dg + 1))"
    by (rule composition_fri_with_tables_bad_sets_subset)
  show "nnreal
      (card (composition_fri_with_tables_bad_sets s dg composition_table)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
      composition_fri_error"
    by (rule order_trans
        [OF composition_fri_with_tables_bad_sets_fraction_le_one error_ge_one])
qed

lemma trace_fri_bad_with_tables_bound_from_cover:
  assumes cover:
      "trace_fri_with_tables_opening_algebraic_cover s bad_sets"
    and bounded: "trace_fri_bad_challenge_sets_bounded bad_sets"
    and fresh: "trace_fri_challenge_freshness_assumption s"
  shows "wp_event verify_monad (trace_fri_bad_with_tables s) s \<le>
    trace_fri_error"
proof -
  have challenge_cover:
    "trace_fri_bad_with_tables_challenge_cover s bad_sets"
    by (rule trace_fri_with_tables_opening_algebraic_cover_imp_bad_challenge_cover
        [OF cover])
  have "wp_event verify_monad (trace_fri_bad_with_tables s) s \<le>
      wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s"
    by (rule wp_event_mono_on_support)
      (use challenge_cover in
        \<open>auto simp: trace_fri_bad_with_tables_challenge_cover_def\<close>)
  also have "... \<le> trace_fri_error"
    using fresh bounded
    unfolding trace_fri_challenge_freshness_assumption_def by blast
  finally show ?thesis .
qed

lemma composition_fri_bad_with_tables_bound_from_cover:
  assumes cover:
      "composition_fri_with_tables_opening_algebraic_cover s bad_sets"
    and bounded: "composition_fri_bad_challenge_sets_bounded bad_sets"
    and fresh: "composition_fri_challenge_freshness_assumption s"
  shows "wp_event verify_monad (composition_fri_bad_with_tables s) s \<le>
    composition_fri_error"
proof -
  have challenge_cover:
    "composition_fri_bad_with_tables_challenge_cover s bad_sets"
    by (rule
        composition_fri_with_tables_opening_algebraic_cover_imp_bad_challenge_cover
        [OF cover])
  have "wp_event verify_monad (composition_fri_bad_with_tables s) s \<le>
      wp_event verify_monad
        (composition_fri_challenge_set_hit s bad_sets) s"
    by (rule wp_event_mono_on_support)
      (use challenge_cover in
        \<open>auto simp: composition_fri_bad_with_tables_challenge_cover_def\<close>)
  also have "... \<le> composition_fri_error"
    using fresh bounded
    unfolding composition_fri_challenge_freshness_assumption_def by blast
  finally show ?thesis .
qed

definition trace_fri_with_tables_opening_reduction_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "trace_fri_with_tables_opening_reduction_assumption s \<longleftrightarrow>
      (\<exists>bad_sets.
        trace_fri_with_tables_opening_algebraic_cover s bad_sets \<and>
        trace_fri_bad_challenge_sets_bounded bad_sets)"

definition composition_fri_with_tables_opening_reduction_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "composition_fri_with_tables_opening_reduction_assumption s \<longleftrightarrow>
      (\<exists>bad_sets.
        composition_fri_with_tables_opening_algebraic_cover s bad_sets \<and>
        composition_fri_bad_challenge_sets_bounded bad_sets)"

lemma trace_fri_with_tables_opening_reductionE:
  assumes "trace_fri_with_tables_opening_reduction_assumption s"
  obtains bad_sets
  where "trace_fri_with_tables_opening_algebraic_cover s bad_sets"
    and "trace_fri_bad_challenge_sets_bounded bad_sets"
  using assms
  unfolding trace_fri_with_tables_opening_reduction_assumption_def by blast

lemma composition_fri_with_tables_opening_reductionE:
  assumes "composition_fri_with_tables_opening_reduction_assumption s"
  obtains bad_sets
  where "composition_fri_with_tables_opening_algebraic_cover s bad_sets"
    and "composition_fri_bad_challenge_sets_bounded bad_sets"
  using assms
  unfolding composition_fri_with_tables_opening_reduction_assumption_def
  by blast

lemma trace_fri_bad_with_tables_bound_from_opening_reduction:
  assumes reduction:
      "trace_fri_with_tables_opening_reduction_assumption s"
    and fresh: "trace_fri_challenge_freshness_assumption s"
  shows "wp_event verify_monad (trace_fri_bad_with_tables s) s \<le>
    trace_fri_error"
proof -
  from reduction obtain bad_sets where cover:
      "trace_fri_with_tables_opening_algebraic_cover s bad_sets"
    and bounded: "trace_fri_bad_challenge_sets_bounded bad_sets"
    by (rule trace_fri_with_tables_opening_reductionE)
  show ?thesis
    by (rule trace_fri_bad_with_tables_bound_from_cover
        [OF cover bounded fresh])
qed

lemma composition_fri_bad_with_tables_bound_from_opening_reduction:
  assumes reduction:
      "composition_fri_with_tables_opening_reduction_assumption s"
    and fresh: "composition_fri_challenge_freshness_assumption s"
  shows "wp_event verify_monad (composition_fri_bad_with_tables s) s \<le>
    composition_fri_error"
proof -
  from reduction obtain bad_sets where cover:
      "composition_fri_with_tables_opening_algebraic_cover s bad_sets"
    and bounded: "composition_fri_bad_challenge_sets_bounded bad_sets"
    by (rule composition_fri_with_tables_opening_reductionE)
  show ?thesis
    by (rule composition_fri_bad_with_tables_bound_from_cover
        [OF cover bounded fresh])
qed

end

end
