(*  Title:      Stark/Soundness_Reductions_Composition.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Reductions_Composition
  imports Soundness_Reductions_Trace
begin

text \<open>Composition-table, query-header, and supported candidate reductions.\<close>

context soundness
begin

definition trace_fri_bad_challenge_sets_bounded
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow> bool"
  where
    "trace_fri_bad_challenge_sets_bounded bad_sets \<longleftrightarrow>
      (\<forall>trace_table.
        bad_sets trace_table \<subseteq> fri_challenge_space (ceil_log clength) \<and>
        nnreal (card (bad_sets trace_table)) /
          nnreal (CARD('f) ^ ceil_log clength) \<le> trace_fri_error)"

definition composition_fri_bad_challenge_sets_bounded
  :: "('f \<Rightarrow> 'f list \<Rightarrow> 'f list set) \<Rightarrow> bool"
  where
    "composition_fri_bad_challenge_sets_bounded bad_sets \<longleftrightarrow>
      (\<forall>dg composition_table.
        bad_sets dg composition_table \<subseteq>
          fri_challenge_space (ceil_log (to_nat dg + 1)) \<and>
        nnreal (card (bad_sets dg composition_table)) /
          nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
          composition_fri_error)"

lemma wp_trace_fri_challenge_set_hit_bound_if_supported_partial_root_candidate_unique_or_collision:
  fixes H :: prob
  assumes future: "trace_fri_future_fresh s"
    and unique:
      "\<And>fr.
        \<exists>trace_table.
          trace_fri_supported_root_partial_trace_table_candidates s fr \<subseteq>
            {trace_table}"
    and bounded: "trace_fri_bad_challenge_sets_bounded bad_sets"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le>
      trace_fri_error + H"
proof -
  have union_bound:
    "\<And>fr.
      nnreal
        (card
          (trace_fri_supported_root_partial_union_bad_sets s bad_sets fr)) /
      nnreal (CARD('f) ^ ceil_log clength) \<le> trace_fri_error"
  proof -
    fix fr
    show
      "nnreal
        (card
          (trace_fri_supported_root_partial_union_bad_sets s bad_sets fr)) /
      nnreal (CARD('f) ^ ceil_log clength) \<le> trace_fri_error"
      by (rule
          trace_fri_supported_root_partial_union_bad_sets_fraction_bound_if_unique_candidate
          [OF unique])
        (use bounded in
          \<open>auto simp: trace_fri_bad_challenge_sets_bounded_def\<close>)
  qed
  show ?thesis
    by (rule
        wp_trace_fri_challenge_set_hit_bound_via_supported_partial_union_or_collision
        [OF future union_bound collision_bound])
qed

lemma alpha_header_supported_partial_union_bad_sets_fraction_bound_if_unique_candidate:
  fixes C :: prob
  assumes unique:
      "\<exists>trace_table.
        alpha_header_supported_partial_trace_table_candidates s fr
          f_fri_roots f_final \<subseteq> {trace_table}"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bound:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space) \<le> C"
  shows
    "nnreal
      (card
        (alpha_header_supported_partial_union_bad_sets s bad_sets fr
          f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le> C"
proof -
  from unique obtain trace_table where candidates:
    "alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
      f_final \<subseteq> {trace_table}"
    by blast
  have union_subset:
    "alpha_header_supported_partial_union_bad_sets s bad_sets fr f_fri_roots
      f_final \<subseteq> bad_sets trace_table"
    unfolding alpha_header_supported_partial_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets trace_table)"
    by (rule finite_subset[OF subset finite_alpha_space])
  have card_le:
    "card
      (alpha_header_supported_partial_union_bad_sets s bad_sets fr
        f_fri_roots f_final) \<le>
      card (bad_sets trace_table)"
    by (rule card_mono[OF finite_bad union_subset])
  have "nnreal
        (card
          (alpha_header_supported_partial_union_bad_sets s bad_sets fr
            f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le>
      nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma wp_alpha_bad_set_hit_bound_if_supported_partial_header_candidate_unique_or_collision:
  fixes C H :: prob
  assumes future: "alpha_future_fresh s"
    and unique:
      "\<And>fr f_fri_roots f_final.
        \<exists>trace_table.
          alpha_header_supported_partial_trace_table_candidates s fr
            f_fri_roots f_final \<subseteq> {trace_table}"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bounded:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space) \<le>
        C"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows "wp_event verify_monad (alpha_bad_set_hit s bad_sets) s \<le> C + H"
proof -
  have union_bound:
    "\<And>fr f_fri_roots f_final.
      nnreal
        (card
          (alpha_header_supported_partial_union_bad_sets s bad_sets fr
            f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le> C"
  proof -
    fix fr f_fri_roots f_final
    show
      "nnreal
        (card
          (alpha_header_supported_partial_union_bad_sets s bad_sets fr
            f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le> C"
      by (rule
          alpha_header_supported_partial_union_bad_sets_fraction_bound_if_unique_candidate
          [OF unique subset bounded])
  qed
  show ?thesis
    by (rule wp_alpha_bad_set_hit_bound_via_supported_partial_union_or_collision
        [OF future subset union_bound collision_bound])
qed

lemma composition_randomization_bad_bound_if_alpha_header_supported_partial_candidate_unique_or_collision:
  fixes H :: prob
  assumes future: "alpha_future_fresh s"
    and unique:
      "\<And>fr f_fri_roots f_final.
        \<exists>trace_table.
          alpha_header_supported_partial_trace_table_candidates s fr
            f_fri_roots f_final \<subseteq> {trace_table}"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (composition_randomization_bad s) s \<le>
      composition_error_bound + H"
proof -
  have alpha_bound:
    "wp_event verify_monad
      (alpha_bad_set_hit s composition_trace_bad_alpha_space) s \<le>
      composition_error_bound + H"
    by (rule
        wp_alpha_bad_set_hit_bound_if_supported_partial_header_candidate_unique_or_collision
        [OF future unique composition_trace_bad_alpha_space_subset_alpha_space
          composition_trace_bad_alpha_space_fraction_bound_alpha_space
          collision_bound])
  have "wp_event verify_monad (composition_randomization_bad s) s \<le>
      wp_event verify_monad
        (alpha_bad_set_hit s composition_trace_bad_alpha_space) s"
    by (rule wp_event_mono)
      (rule composition_randomization_bad_imp_alpha_bad_set_hit)
  also have "... \<le> composition_error_bound + H"
    by (rule alpha_bound)
  finally show ?thesis .
qed

lemma wp_trace_fri_challenge_set_hit_bound_via_root_union:
  fixes C :: prob
  assumes future: "trace_fri_future_fresh s"
    and union_bound:
      "\<And>fr. nnreal
        (card (trace_fri_root_union_bad_sets s bad_sets fr)) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le> C"
proof -
  have root_bound:
    "wp_event verify_monad
      (trace_fri_root_list_set_hit s
        (trace_fri_root_union_bad_sets s bad_sets)) s \<le> C"
    by (rule wp_verify_monad_trace_fri_root_list_set_bound[OF future])
      (use trace_fri_root_union_bad_sets_subset union_bound in simp_all)
  have "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le>
      wp_event verify_monad
        (trace_fri_root_list_set_hit s
          (trace_fri_root_union_bad_sets s bad_sets)) s"
    by (rule wp_event_mono)
      (rule trace_fri_challenge_set_hit_imp_root_union_list_set_hit)
  also have "... \<le> C"
    by (rule root_bound)
  finally show ?thesis .
qed

lemma wp_trace_fri_challenge_set_hit_bound_via_supported_root_union:
  fixes C :: prob
  assumes future: "trace_fri_future_fresh s"
    and union_bound:
      "\<And>fr. nnreal
        (card (trace_fri_supported_root_union_bad_sets s bad_sets fr)) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le> C"
proof -
  have root_bound:
    "wp_event verify_monad
      (trace_fri_root_list_set_hit s
        (trace_fri_supported_root_union_bad_sets s bad_sets)) s \<le> C"
    by (rule wp_verify_monad_trace_fri_root_list_set_bound[OF future])
      (use trace_fri_supported_root_union_bad_sets_subset union_bound in
        simp_all)
  have "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le>
      wp_event verify_monad
        (trace_fri_root_list_set_hit s
          (trace_fri_supported_root_union_bad_sets s bad_sets)) s"
    by (rule wp_event_mono_on_support)
      (rule trace_fri_challenge_set_hit_imp_supported_root_union_list_set_hit)
  also have "... \<le> C"
    by (rule root_bound)
  finally show ?thesis .
qed

lemma trace_fri_root_union_bad_sets_fraction_bound_if_unique_candidate:
  fixes C :: prob
  assumes unique:
      "\<exists>trace_table.
        trace_fri_root_trace_table_candidates s fr \<subseteq> {trace_table}"
    and subset:
      "\<And>trace_table. bad_sets trace_table \<subseteq>
        fri_challenge_space (ceil_log clength)"
    and bound:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) /
          nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "nnreal (card (trace_fri_root_union_bad_sets s bad_sets fr)) /
      nnreal (CARD('f) ^ ceil_log clength) \<le> C"
proof -
  from unique obtain trace_table where candidates:
    "trace_fri_root_trace_table_candidates s fr \<subseteq> {trace_table}"
    by blast
  have union_subset:
    "trace_fri_root_union_bad_sets s bad_sets fr \<subseteq> bad_sets trace_table"
    unfolding trace_fri_root_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets trace_table)"
    by (rule finite_subset[OF subset finite_fri_challenge_space])
  have card_le:
    "card (trace_fri_root_union_bad_sets s bad_sets fr) \<le>
      card (bad_sets trace_table)"
    by (rule card_mono[OF finite_bad union_subset])
  have "nnreal (card (trace_fri_root_union_bad_sets s bad_sets fr)) /
      nnreal (CARD('f) ^ ceil_log clength) \<le>
      nnreal (card (bad_sets trace_table)) /
        nnreal (CARD('f) ^ ceil_log clength)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma trace_fri_supported_root_union_bad_sets_fraction_bound_if_unique_candidate:
  fixes C :: prob
  assumes unique:
      "\<exists>trace_table.
        trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
          {trace_table}"
    and subset:
      "\<And>trace_table. bad_sets trace_table \<subseteq>
        fri_challenge_space (ceil_log clength)"
    and bound:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) /
          nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "nnreal (card (trace_fri_supported_root_union_bad_sets s bad_sets fr)) /
      nnreal (CARD('f) ^ ceil_log clength) \<le> C"
proof -
  from unique obtain trace_table where candidates:
    "trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
      {trace_table}"
    by blast
  have union_subset:
    "trace_fri_supported_root_union_bad_sets s bad_sets fr \<subseteq>
      bad_sets trace_table"
    unfolding trace_fri_supported_root_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets trace_table)"
    by (rule finite_subset[OF subset finite_fri_challenge_space])
  have card_le:
    "card (trace_fri_supported_root_union_bad_sets s bad_sets fr) \<le>
      card (bad_sets trace_table)"
    by (rule card_mono[OF finite_bad union_subset])
  have "nnreal
        (card (trace_fri_supported_root_union_bad_sets s bad_sets fr)) /
      nnreal (CARD('f) ^ ceil_log clength) \<le>
      nnreal (card (bad_sets trace_table)) /
        nnreal (CARD('f) ^ ceil_log clength)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma composition_fri_challenge_set_hit_imp_list_set_hit:
  assumes hit: "composition_fri_challenge_set_hit s bad_sets out"
    and envelope:
      "\<And>dg composition_table. bad_sets dg composition_table \<subseteq> B dg"
  shows "composition_fri_challenge_list_set_hit s B out"
proof -
  from hit obtain trace_table composition_table as query_idxs trace_bs dg comp_bs
    where challenges:
      "accepted_fri_challenges s out trace_bs dg comp_bs"
    and comp_bad: "comp_bs \<in> bad_sets dg composition_table"
    unfolding composition_fri_challenge_set_hit_def by blast
  have "comp_bs \<in> B dg"
    using comp_bad envelope[of dg composition_table] by auto
  then show ?thesis
    unfolding composition_fri_challenge_list_set_hit_def
    using challenges by blast
qed

definition composition_fri_degree_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "composition_fri_degree_table_candidates s dg =
      {composition_table.
        \<exists>out trace_table as query_idxs trace_bs comp_bs.
          accepted_with_bound_tables s out trace_table composition_table
            as query_idxs \<and>
          accepted_fri_challenges s out trace_bs dg comp_bs}"

definition composition_fri_degree_union_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> 'f list set) \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "composition_fri_degree_union_bad_sets s bad_sets dg =
      {comp_bs \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
        \<exists>composition_table \<in> composition_fri_degree_table_candidates s dg.
          comp_bs \<in> bad_sets dg composition_table}"

lemma composition_fri_degree_union_bad_sets_subset:
  "composition_fri_degree_union_bad_sets s bad_sets dg \<subseteq>
    fri_challenge_space (ceil_log (to_nat dg + 1))"
  unfolding composition_fri_degree_union_bad_sets_def by auto

lemma composition_fri_challenge_set_hit_imp_degree_union_list_set_hit:
  assumes hit: "composition_fri_challenge_set_hit s bad_sets out"
  shows
    "composition_fri_challenge_list_set_hit s
      (composition_fri_degree_union_bad_sets s bad_sets) out"
proof -
  from hit obtain trace_table composition_table as query_idxs trace_bs dg comp_bs
    where bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and challenges: "accepted_fri_challenges s out trace_bs dg comp_bs"
    and comp_bs_bad: "comp_bs \<in> bad_sets dg composition_table"
    unfolding composition_fri_challenge_set_hit_def by blast
  have candidate:
    "composition_table \<in> composition_fri_degree_table_candidates s dg"
    unfolding composition_fri_degree_table_candidates_def
    using bound challenges by blast
  have comp_bs_space:
    "comp_bs \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
    by (rule accepted_fri_challenges_composition_space[OF challenges])
  have comp_bs_union:
    "comp_bs \<in> composition_fri_degree_union_bad_sets s bad_sets dg"
    unfolding composition_fri_degree_union_bad_sets_def
    using comp_bs_space candidate comp_bs_bad by blast
  show ?thesis
    unfolding composition_fri_challenge_list_set_hit_def
    using challenges comp_bs_union by blast
qed

lemma wp_composition_fri_challenge_set_hit_bound_via_degree_union:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and union_bound:
      "\<And>dg. nnreal
        (card (composition_fri_degree_union_bad_sets s bad_sets dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad (composition_fri_challenge_set_hit s bad_sets) s \<le>
      C"
proof -
  have list_bound:
    "wp_event verify_monad
      (composition_fri_challenge_list_set_hit s
        (composition_fri_degree_union_bad_sets s bad_sets)) s \<le> C"
    by (rule wp_verify_monad_composition_fri_challenge_list_set_bound[OF future])
      (use composition_fri_degree_union_bad_sets_subset union_bound in
        simp_all)
  have "wp_event verify_monad (composition_fri_challenge_set_hit s bad_sets) s \<le>
      wp_event verify_monad
        (composition_fri_challenge_list_set_hit s
          (composition_fri_degree_union_bad_sets s bad_sets)) s"
    by (rule wp_event_mono)
      (rule composition_fri_challenge_set_hit_imp_degree_union_list_set_hit)
  also have "... \<le> C"
    by (rule list_bound)
  finally show ?thesis .
qed

lemma composition_fri_degree_union_bad_sets_fraction_bound_if_unique_candidate:
  fixes C :: prob
  assumes unique:
      "\<exists>composition_table.
        composition_fri_degree_table_candidates s dg \<subseteq> {composition_table}"
    and subset:
      "\<And>composition_table. bad_sets dg composition_table \<subseteq>
        fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>composition_table.
        nnreal (card (bad_sets dg composition_table)) /
          nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "nnreal (card (composition_fri_degree_union_bad_sets s bad_sets dg)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
proof -
  from unique obtain composition_table where candidates:
    "composition_fri_degree_table_candidates s dg \<subseteq> {composition_table}"
    by blast
  have union_subset:
    "composition_fri_degree_union_bad_sets s bad_sets dg \<subseteq>
      bad_sets dg composition_table"
    unfolding composition_fri_degree_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets dg composition_table)"
    by (rule finite_subset[OF subset finite_fri_challenge_space])
  have card_le:
    "card (composition_fri_degree_union_bad_sets s bad_sets dg) \<le>
      card (bad_sets dg composition_table)"
    by (rule card_mono[OF finite_bad union_subset])
  have "nnreal (card (composition_fri_degree_union_bad_sets s bad_sets dg)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
      nnreal (card (bad_sets dg composition_table)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

definition composition_fri_supported_root_composition_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f list set"
  where
    "composition_fri_supported_root_composition_table_candidates s fr
      f_fri_roots f_final as dg composition_fri_roots =
      {composition_table.
        \<exists>out trace_table query_idxs trace_bs comp_bs final rest.
          out \<in> set_dist (execute verify_monad s) \<and>
          accepted_with_bound_tables s out trace_table composition_table as
            query_idxs \<and>
          accepted_fri_challenges s out trace_bs dg comp_bs \<and>
          verifier_header_transcript s fr f_fri_roots f_final as dg
            composition_fri_roots final rest}"

definition composition_fri_supported_root_composition_table_candidate_state
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "composition_fri_supported_root_composition_table_candidate_state s fr
      f_fri_roots f_final as dg composition_fri_roots composition_table
      final_state \<longleftrightarrow>
      (\<exists>result trace_table query_idxs trace_bs comp_bs final rest.
        Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
        accepted_with_bound_tables s (Some (result, final_state)) trace_table
          composition_table as query_idxs \<and>
        accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
          comp_bs \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest \<and>
        composition_fri_roots \<noteq> [] \<and>
        merkle_root_binds_table (hd composition_fri_roots) composition_table
          final_state)"

lemma composition_fri_supported_root_composition_table_candidates_iff_state:
  "composition_table \<in>
      composition_fri_supported_root_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots \<longleftrightarrow>
    (\<exists>final_state.
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state)"
proof
  assume candidate:
    "composition_table \<in>
      composition_fri_supported_root_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots"
  then obtain out trace_table query_idxs trace_bs comp_bs final rest where
    outcome: "out \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and challenges: "accepted_fri_challenges s out trace_bs dg comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding composition_fri_supported_root_composition_table_candidates_def
    by blast
  from bound obtain result final_state fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    out_eq: "out = Some (result, final_state)"
    and header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and comp_nonempty: "composition_fri_roots' \<noteq> []"
    and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots')
        composition_table final_state"
    unfolding accepted_with_bound_tables_def by blast
  have eqs:
    "fr' = fr \<and>
     f_fri_roots' = f_fri_roots \<and>
     f_final' = f_final \<and>
     dg' = dg \<and>
     composition_fri_roots' = composition_fri_roots \<and>
     final' = final \<and>
     rest' = rest"
    using verifier_header_transcript_unique[OF header' header] by simp
  have state:
    "composition_fri_supported_root_composition_table_candidate_state s fr
      f_fri_roots f_final as dg composition_fri_roots composition_table
      final_state"
    unfolding composition_fri_supported_root_composition_table_candidate_state_def
    by (intro exI[of _ result] exI[of _ trace_table]
        exI[of _ query_idxs] exI[of _ trace_bs] exI[of _ comp_bs]
        exI[of _ final] exI[of _ rest])
      (use outcome out_eq bound challenges header comp_nonempty comp_bind eqs
        in simp)
  then show
    "\<exists>final_state.
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state"
    by blast
next
  assume
    "\<exists>final_state.
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state"
  then obtain final_state result trace_table query_idxs trace_bs comp_bs final
      rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and challenges:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding composition_fri_supported_root_composition_table_candidate_state_def
    by blast
  show
    "composition_table \<in>
      composition_fri_supported_root_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots"
    unfolding composition_fri_supported_root_composition_table_candidates_def
    using outcome bound challenges header by blast
qed

definition composition_fri_supported_root_partial_composition_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f list set"
  where
    "composition_fri_supported_root_partial_composition_table_candidates s fr
      f_fri_roots f_final as dg composition_fri_roots =
      {composition_table.
        composition_fri_roots \<noteq> [] \<and>
        (\<exists>out query_idxs composition_openings trace_bs comp_bs final rest.
          out \<in> set_dist (execute verify_monad s) \<and>
          accepted_with_partial_composition_openings s out
            (hd composition_fri_roots) query_idxs composition_openings \<and>
          partial_composition_table_candidate composition_table
            composition_openings \<and>
          accepted_fri_challenges s out trace_bs dg comp_bs \<and>
          verifier_header_transcript s fr f_fri_roots f_final as dg
            composition_fri_roots final rest)}"

definition composition_fri_supported_root_partial_composition_table_candidate_state
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "composition_fri_supported_root_partial_composition_table_candidate_state
      s fr f_fri_roots f_final as dg composition_fri_roots composition_table
      final_state \<longleftrightarrow>
      composition_fri_roots \<noteq> [] \<and>
      (\<exists>result query_idxs composition_openings trace_bs comp_bs final rest.
        Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
        accepted_with_partial_composition_openings s
          (Some (result, final_state)) (hd composition_fri_roots) query_idxs
          composition_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings \<and>
        accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
          comp_bs \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest)"

lemma composition_fri_supported_root_partial_composition_table_candidates_iff_state:
  "composition_table \<in>
      composition_fri_supported_root_partial_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots \<longleftrightarrow>
    (\<exists>final_state.
      composition_fri_supported_root_partial_composition_table_candidate_state
        s fr f_fri_roots f_final as dg composition_fri_roots
        composition_table final_state)"
proof
  assume candidate:
    "composition_table \<in>
      composition_fri_supported_root_partial_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots"
  then obtain out query_idxs composition_openings trace_bs comp_bs final rest
    where comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome: "out \<in> set_dist (execute verify_monad s)"
    and partial:
      "accepted_with_partial_composition_openings s out
        (hd composition_fri_roots) query_idxs composition_openings"
    and table:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and challenges: "accepted_fri_challenges s out trace_bs dg comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding
      composition_fri_supported_root_partial_composition_table_candidates_def
    by blast
  from partial obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_with_partial_composition_openings_def by blast
  have outcome_some:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using outcome out_eq by simp
  have partial_some:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots) query_idxs
      composition_openings"
    using partial out_eq by simp
  have challenges_some:
    "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
      comp_bs"
    using challenges out_eq by simp
  have state:
    "composition_fri_supported_root_partial_composition_table_candidate_state
      s fr f_fri_roots f_final as dg composition_fri_roots
      composition_table final_state"
    unfolding
      composition_fri_supported_root_partial_composition_table_candidate_state_def
    using comp_nonempty outcome_some partial_some table challenges_some header
    by blast
  then show
    "\<exists>final_state.
      composition_fri_supported_root_partial_composition_table_candidate_state
        s fr f_fri_roots f_final as dg composition_fri_roots
        composition_table final_state"
    by blast
next
  assume
    "\<exists>final_state.
      composition_fri_supported_root_partial_composition_table_candidate_state
        s fr f_fri_roots f_final as dg composition_fri_roots
        composition_table final_state"
  then obtain final_state result query_idxs composition_openings trace_bs
      comp_bs final rest where
    comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots) query_idxs
        composition_openings"
    and table:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and challenges:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding
      composition_fri_supported_root_partial_composition_table_candidate_state_def
    by blast
  show
    "composition_table \<in>
      composition_fri_supported_root_partial_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots"
    unfolding
      composition_fri_supported_root_partial_composition_table_candidates_def
    using comp_nonempty outcome partial table challenges header by blast
qed

lemma composition_fri_supported_root_composition_table_candidate_state_imp_partial_candidate_state:
  assumes state:
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state"
    and clean: "\<not> hash_map_output_collision final_state"
  shows
    "composition_fri_supported_root_partial_composition_table_candidate_state
      s fr f_fri_roots f_final as dg composition_fri_roots composition_table
      final_state"
proof -
  from state obtain result trace_table query_idxs trace_bs comp_bs final rest
    where outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and challenges:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and bind:
      "merkle_root_binds_table (hd composition_fri_roots) composition_table
        final_state"
    unfolding composition_fri_supported_root_composition_table_candidate_state_def
    by blast
  from verify_monad_header_extraction[OF outcome]
  obtain fr' f_fl' f_final' as' dg' fl' final' query_state' where
    header':
      "verifier_header_transcript s fr' (map snd f_fl') f_final' as' dg'
        (map snd fl') final' (PTranscript query_state')"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl' f_final' as' fl'
                final') rounds)
            query_state')"
    by metis
  have eqs:
    "fr' = fr \<and>
     map snd f_fl' = f_fri_roots \<and>
     f_final' = f_final \<and>
     as' = as \<and>
     dg' = dg \<and>
     map snd fl' = composition_fri_roots \<and>
     final' = final \<and>
     PTranscript query_state' = rest"
    using verifier_header_transcript_unique[OF header' header] by simp
  then have fl_nonempty: "fl' \<noteq> []"
    using comp_nonempty by (cases fl') simp_all
  then obtain b composition_root fl_tail where fl_eq:
    "fl' = (b, composition_root) # fl_tail"
    by (cases fl') auto
  have root_eq: "composition_root = hd composition_fri_roots"
  proof -
    have map_eq: "map snd fl' = composition_fri_roots"
      using eqs by simp
    have cons_eq: "composition_root # map snd fl_tail = composition_fri_roots"
      using map_eq fl_eq by simp
    then have "hd composition_fri_roots = composition_root"
      by (metis list.sel(1))
    then show ?thesis by simp
  qed
  from query_rounds_accepted_with_partial_composition_openings
      [OF fl_eq query_out]
  obtain partial_query_idxs composition_openings where partial:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) composition_root partial_query_idxs
      composition_openings"
    by blast
  have partial_root:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots)
      partial_query_idxs composition_openings"
    using partial root_eq by simp
  have len_table: "length composition_table = scale * clength"
    using accepted_with_bound_tables_shapes(2)[OF bound]
    by (simp add: mult.commute)
  have table:
    "partial_composition_table_candidate composition_table
      composition_openings"
    by (rule accepted_bound_composition_table_partial_candidate_if_clean
        [OF bind len_table partial_root clean])
  show ?thesis
    unfolding
      composition_fri_supported_root_partial_composition_table_candidate_state_def
    using outcome partial_root table challenges header comp_nonempty by blast
qed

definition query_header_supported_partial_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> ('f list \<times> 'f list) set"
  where
    "query_header_supported_partial_table_candidates s fr f_fri_roots
      f_final as dg composition_fri_roots final =
      {(trace_table, composition_table).
        composition_fri_roots \<noteq> [] \<and>
        (\<exists>out trace_query_idxs composition_query_idxs trace_openings
            composition_openings rest.
          out \<in> set_dist (execute verify_monad s) \<and>
          accepted_with_partial_trace_openings s out fr trace_query_idxs
            trace_openings \<and>
          partial_trace_table_candidate trace_table trace_openings \<and>
          accepted_with_partial_composition_openings s out
            (hd composition_fri_roots) composition_query_idxs
            composition_openings \<and>
          partial_composition_table_candidate composition_table
            composition_openings \<and>
          verifier_header_transcript s fr f_fri_roots f_final as dg
            composition_fri_roots final rest)}"

definition query_header_supported_partial_table_candidate_state
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "query_header_supported_partial_table_candidate_state s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state \<longleftrightarrow>
      composition_fri_roots \<noteq> [] \<and>
      (\<exists>result trace_query_idxs composition_query_idxs trace_openings
          composition_openings rest.
        Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
        accepted_with_partial_trace_openings s
          (Some (result, final_state)) fr trace_query_idxs
          trace_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        accepted_with_partial_composition_openings s
          (Some (result, final_state)) (hd composition_fri_roots)
          composition_query_idxs composition_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest)"

lemma query_header_supported_partial_table_candidates_iff_state:
  "(trace_table, composition_table) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<longleftrightarrow>
    (\<exists>final_state.
      query_header_supported_partial_table_candidate_state s fr f_fri_roots
        f_final as dg composition_fri_roots final trace_table
        composition_table final_state)"
proof
  assume candidate:
    "(trace_table, composition_table) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
  then obtain out trace_query_idxs composition_query_idxs trace_openings
      composition_openings rest where
    comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome: "out \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s out fr trace_query_idxs
        trace_openings"
    and trace_table:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s out
        (hd composition_fri_roots) composition_query_idxs
        composition_openings"
    and comp_table:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding query_header_supported_partial_table_candidates_def by blast
  from trace_partial obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_with_partial_trace_openings_def by blast
  have outcome_some:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using outcome out_eq by simp
  have trace_partial_some:
    "accepted_with_partial_trace_openings s (Some (result, final_state)) fr
      trace_query_idxs trace_openings"
    using trace_partial out_eq by simp
  have comp_partial_some:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots)
      composition_query_idxs composition_openings"
    using comp_partial out_eq by simp
  have state:
    "query_header_supported_partial_table_candidate_state s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state"
    unfolding query_header_supported_partial_table_candidate_state_def
    using comp_nonempty outcome_some trace_partial_some trace_table
      comp_partial_some comp_table header
    by blast
  then show
    "\<exists>final_state.
      query_header_supported_partial_table_candidate_state s fr f_fri_roots
        f_final as dg composition_fri_roots final trace_table
        composition_table final_state"
    by blast
next
  assume
    "\<exists>final_state.
      query_header_supported_partial_table_candidate_state s fr f_fri_roots
        f_final as dg composition_fri_roots final trace_table
        composition_table final_state"
  then obtain final_state result trace_query_idxs composition_query_idxs
      trace_openings composition_openings rest where
    comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_table:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_table:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding query_header_supported_partial_table_candidate_state_def
    by blast
  show
    "(trace_table, composition_table) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_table_candidates_def
    using comp_nonempty outcome trace_partial trace_table comp_partial
      comp_table header
    by blast
qed

lemma query_header_supported_partial_table_candidate_state_hash_extends:
  assumes
    "query_header_supported_partial_table_candidate_state s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state"
  shows "s \<le> final_state"
proof -
  from assms obtain result trace_query_idxs composition_query_idxs
      trace_openings composition_openings rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    unfolding query_header_supported_partial_table_candidate_state_def
    by blast
  show ?thesis
    by (rule verify_monad_hash_extends[OF outcome])
qed

lemma query_header_supported_table_candidate_state_imp_partial_candidate_state:
  assumes state:
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
    and clean: "\<not> hash_map_output_collision final_state"
  shows
    "query_header_supported_partial_table_candidate_state s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state"
proof -
  from state obtain result query_idxs rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and trace_bind:
      "merkle_root_binds_table fr trace_table final_state"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots) composition_table
        final_state"
    unfolding query_header_supported_table_candidate_state_def by blast
  from verify_monad_header_extraction[OF outcome]
  obtain fr' f_fl f_final' as' dg' fl final' query_state where
    header':
      "verifier_header_transcript s fr' (map snd f_fl) f_final' as' dg'
        (map snd fl) final' (PTranscript query_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl f_final' as' fl
                final') rounds)
            query_state)"
    by metis
  have eqs:
    "fr' = fr \<and>
     map snd f_fl = f_fri_roots \<and>
     f_final' = f_final \<and>
     as' = as \<and>
     dg' = dg \<and>
     map snd fl = composition_fri_roots \<and>
     final' = final \<and>
     PTranscript query_state = rest"
    using verifier_header_transcript_unique[OF header' header] by simp
  obtain trace_query_idxs trace_openings where
    len_trace_query_idxs: "length trace_query_idxs = rounds"
    and len_trace_openings: "length trace_openings = rounds"
    and trace_indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (trace_openings ! i) =
          powers_scaled (trace_query_idxs ! i)"
    and trace_tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table fr'
          (scale * clength) (trace_openings ! i) final_state"
  proof (rule ntimes_verifier_query_rounds_authenticated_trace_openings_no_raws
      [OF query_out])
    fix trace_query_idxs trace_openings
    assume len_trace_query_idxs: "length trace_query_idxs = rounds"
      and len_trace_openings: "length trace_openings = rounds"
      and trace_indices:
        "\<And>i. i < rounds \<Longrightarrow>
          map opening_index (trace_openings ! i) =
          powers_scaled (trace_query_idxs ! i)"
      and trace_tables:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_authenticated_table fr'
            (scale * clength) (trace_openings ! i) final_state"
    show ?thesis
      by (rule that[OF len_trace_query_idxs len_trace_openings
            trace_indices trace_tables])
  qed
  have trace_partial:
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr trace_query_idxs trace_openings"
  proof -
    have all_indices:
      "\<forall>i < rounds.
        map opening_index (trace_openings ! i) =
          powers_scaled (trace_query_idxs ! i)"
      using trace_indices by blast
    have all_tables:
      "\<forall>i < rounds.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) final_state"
      using trace_tables eqs by simp
    show ?thesis
      unfolding accepted_with_partial_trace_openings_def accepted_def
      by (intro conjI exI[of _ result] exI[of _ final_state])
        (use len_trace_query_idxs len_trace_openings all_indices all_tables
          in simp_all)
  qed
  have trace_len: "length trace_table = scale * clength"
    using accepted_with_bound_tables_shapes(1)[OF bound] by simp
  have trace_candidate:
    "partial_trace_table_candidate trace_table trace_openings"
    by (rule accepted_bound_trace_table_partial_candidate_if_clean
        [OF trace_bind trace_len trace_partial clean])
  have fl_nonempty: "fl \<noteq> []"
    using comp_nonempty eqs by (cases fl) simp_all
  then obtain b composition_root fl_tail where fl_eq:
    "fl = (b, composition_root) # fl_tail"
    by (cases fl) auto
  have root_eq: "composition_root = hd composition_fri_roots"
  proof -
    have cons_eq: "composition_root # map snd fl_tail = composition_fri_roots"
      using eqs fl_eq by simp
    then have "hd composition_fri_roots = composition_root"
      by (metis list.sel(1))
    then show ?thesis by simp
  qed
  from query_rounds_accepted_with_partial_composition_openings
      [OF fl_eq query_out]
  obtain composition_query_idxs composition_openings where comp_partial':
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) composition_root composition_query_idxs
      composition_openings"
    by blast
  have comp_partial:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots)
      composition_query_idxs composition_openings"
    using comp_partial' root_eq by simp
  have comp_len: "length composition_table = scale * clength"
    using accepted_with_bound_tables_shapes(2)[OF bound]
    by (simp add: mult.commute)
  have comp_candidate:
    "partial_composition_table_candidate composition_table
      composition_openings"
    by (rule accepted_bound_composition_table_partial_candidate_if_clean
        [OF comp_bind comp_len comp_partial clean])
  show ?thesis
    unfolding query_header_supported_partial_table_candidate_state_def
    using comp_nonempty outcome trace_partial trace_candidate comp_partial
      comp_candidate header
    by blast
qed

lemma accepted_with_bound_tables_header_composition_fri_roots_nonempty:
  assumes bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  shows "composition_fri_roots \<noteq> []"
proof -
  from bound obtain result final_state fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    out_eq: "out = Some (result, final_state)"
    and header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and comp_nonempty': "composition_fri_roots' \<noteq> []"
    unfolding accepted_with_bound_tables_def by blast
  have "composition_fri_roots' = composition_fri_roots"
    using verifier_header_transcript_unique[OF header' header] by simp
  then show ?thesis
    using comp_nonempty' by simp
qed

definition query_header_supported_partial_union_good_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat set"
  where
    "query_header_supported_partial_union_good_sets s good_sets fr
      f_fri_roots f_final as dg composition_fri_roots final =
      {idx \<in> query_sample_space.
        \<exists>trace_table composition_table.
          (trace_table, composition_table) \<in>
            query_header_supported_partial_table_candidates s fr
              f_fri_roots f_final as dg composition_fri_roots final \<and>
          idx \<in> good_sets trace_table composition_table as}"

lemma query_header_supported_partial_union_good_sets_subset:
  "query_header_supported_partial_union_good_sets s good_sets fr f_fri_roots
      f_final as dg composition_fri_roots final \<subseteq> query_sample_space"
  unfolding query_header_supported_partial_union_good_sets_def by auto

lemma query_header_supported_partial_union_good_sets_fraction_bound_if_unique_candidate:
  assumes unique:
      "\<exists>trace_table composition_table.
        query_header_supported_partial_table_candidates s fr f_fri_roots
          f_final as dg composition_fri_roots final \<subseteq>
          {(trace_table, composition_table)}"
    and subset:
      "\<And>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and bound:
      "\<And>trace_table composition_table as.
        nnreal
          (query_raw_preimage_card_envelope
            (card (good_sets trace_table composition_table as))) /
          nnreal size \<le> query_error_bound"
  shows
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (query_header_supported_partial_union_good_sets s good_sets fr
            f_fri_roots f_final as dg composition_fri_roots final))) /
      nnreal size \<le> query_error_bound"
proof -
  from unique obtain trace_table composition_table where candidates:
    "query_header_supported_partial_table_candidates s fr f_fri_roots f_final
      as dg composition_fri_roots final \<subseteq>
      {(trace_table, composition_table)}"
    by blast
  have union_subset:
    "query_header_supported_partial_union_good_sets s good_sets fr
      f_fri_roots f_final as dg composition_fri_roots final \<subseteq>
      good_sets trace_table composition_table as"
    unfolding query_header_supported_partial_union_good_sets_def
    using candidates by auto
  have finite_good: "finite (good_sets trace_table composition_table as)"
    by (rule finite_subset[OF subset finite_query_sample_space])
  have card_le:
    "card
      (query_header_supported_partial_union_good_sets s good_sets fr
        f_fri_roots f_final as dg composition_fri_roots final) \<le>
      card (good_sets trace_table composition_table as)"
    by (rule card_mono[OF finite_good union_subset])
  have envelope_le:
    "query_raw_preimage_card_envelope
        (card
          (query_header_supported_partial_union_good_sets s good_sets fr
            f_fri_roots f_final as dg composition_fri_roots final)) \<le>
      query_raw_preimage_card_envelope
        (card (good_sets trace_table composition_table as))"
    by (rule query_raw_preimage_card_envelope_mono[OF card_le])
  have "nnreal
        (query_raw_preimage_card_envelope
          (card
            (query_header_supported_partial_union_good_sets s good_sets fr
              f_fri_roots f_final as dg composition_fri_roots final))) /
      nnreal size \<le>
      nnreal
        (query_raw_preimage_card_envelope
          (card (good_sets trace_table composition_table as))) /
        nnreal size"
    by (rule nnreal_nat_divide_right_mono[OF envelope_le])
  also have "... \<le> query_error_bound"
    by (rule bound)
  finally show ?thesis .
qed

lemma query_index_round_set_hit_at_imp_partial_union_or_collision:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and hit: "query_index_round_set_hit_at s good_sets i out"
  shows
    "query_header_rounds_any_index_set_hit s
      (query_header_supported_partial_union_good_sets s good_sets) out \<or>
     hash_map_output_collision_bad s out"
proof -
  from hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and i_bound: "i < rounds"
    and query_hit:
      "query_idxs ! i \<in> good_sets trace_table composition_table as"
    unfolding query_index_round_set_hit_at_def by blast
  from bound obtain result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    out_eq: "out = Some (result, final_state)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and trace_bind:
      "merkle_root_binds_table fr trace_table final_state"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots) composition_table
        final_state"
    unfolding accepted_with_bound_tables_def by blast
  show ?thesis
  proof (cases "hash_map_output_collision final_state")
    case True
    then have "hash_map_output_collision_bad s out"
      unfolding hash_map_output_collision_bad_def accepted_def out_eq by simp
    then show ?thesis by simp
  next
    case clean: False
    have state:
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
      unfolding query_header_supported_table_candidate_state_def
      by (intro exI[of _ result] exI[of _ query_idxs] exI[of _ rest])
        (use outcome out_eq bound header trace_bind comp_nonempty comp_bind
          in simp)
    have candidate:
      "(trace_table, composition_table) \<in>
        query_header_supported_partial_table_candidates s fr f_fri_roots
          f_final as dg composition_fri_roots final"
      using
        query_header_supported_table_candidate_state_imp_partial_candidate_state
          [OF state clean]
        query_header_supported_partial_table_candidates_iff_state
      by blast
    have len: "length query_idxs = rounds"
      by (rule accepted_with_bound_tables_shapes(4)[OF bound])
    have idx_mem: "query_idxs ! i \<in> set query_idxs"
      by (rule nth_mem) (use i_bound len in simp)
    have idx_sample: "query_idxs ! i \<in> query_sample_space"
      by (rule accepted_with_bound_tables_query_sample_space
          [OF bound idx_mem])
    have union_hit:
      "query_idxs ! i \<in>
        query_header_supported_partial_union_good_sets s good_sets fr
          f_fri_roots f_final as dg composition_fri_roots final"
      unfolding query_header_supported_partial_union_good_sets_def
      using idx_sample candidate query_hit by blast
    have round_hit:
      "query_rounds_any_index_set_hit s
        (query_header_supported_partial_union_good_sets s good_sets fr
          f_fri_roots f_final as dg composition_fri_roots final)
        rounds out"
      by (rule accepted_with_bound_tables_query_rounds_any_index_set_hit
          [OF bound i_bound union_hit])
    show ?thesis
      unfolding query_header_rounds_any_index_set_hit_def
      using header round_hit by blast
  qed
qed

lemma query_index_round_set_hit_imp_partial_union_or_collision:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and hit: "query_index_round_set_hit s good_sets out"
  shows
    "query_header_rounds_any_index_set_hit s
      (query_header_supported_partial_union_good_sets s good_sets) out \<or>
     hash_map_output_collision_bad s out"
proof -
  from hit obtain i where
    "query_index_round_set_hit_at s good_sets i out"
    unfolding query_index_round_set_hit_def by blast
  then show ?thesis
    by (rule query_index_round_set_hit_at_imp_partial_union_or_collision
        [OF outcome])
qed

lemma wp_query_index_round_set_hit_bound_via_partial_union_or_collision:
  fixes C H :: prob
  assumes partial_bound:
      "wp_event verify_monad
        (query_header_rounds_any_index_set_hit s
          (query_header_supported_partial_union_good_sets s good_sets)) s \<le>
        C"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (query_index_round_set_hit s good_sets) s \<le>
      C + H"
proof -
  have mono:
    "wp_event verify_monad (query_index_round_set_hit s good_sets) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          query_header_rounds_any_index_set_hit s
            (query_header_supported_partial_union_good_sets s good_sets)
            out \<or>
          hash_map_output_collision_bad s out) s"
    by (rule wp_event_mono_on_support)
      (use query_index_round_set_hit_imp_partial_union_or_collision in blast)
  also have "... \<le> C + H"
  proof -
    have "wp_event verify_monad
        (\<lambda>out.
          query_header_rounds_any_index_set_hit s
            (query_header_supported_partial_union_good_sets s good_sets)
            out \<or>
          hash_map_output_collision_bad s out) s \<le>
        wp_event verify_monad
          (query_header_rounds_any_index_set_hit s
            (query_header_supported_partial_union_good_sets s good_sets)) s +
        wp_event verify_monad (hash_map_output_collision_bad s) s"
      by (rule wp_event_union_bound)
    also have "... \<le> C + H"
      by (intro add_mono partial_bound collision_bound)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma wp_query_index_round_set_hit_bound_via_supported_partial_union_or_collision:
  fixes H :: prob
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and union_bound:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots final.
        nnreal
          (query_raw_preimage_card_envelope
            (card
              (query_header_supported_partial_union_good_sets s good_sets fr
                f_fri_roots f_final as dg composition_fri_roots final))) /
          nnreal size \<le> query_error_bound"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (query_index_round_set_hit s good_sets) s \<le>
      nnreal rounds * query_error_bound + H"
proof -
  have partial_bound:
    "wp_event verify_monad
      (query_header_rounds_any_index_set_hit s
        (query_header_supported_partial_union_good_sets s good_sets)) s \<le>
      nnreal rounds * query_error_bound"
    by (rule wp_verify_monad_query_header_rounds_any_index_set_bound
        [OF future raw_bound])
      (use query_header_supported_partial_union_good_sets_subset union_bound
        in simp_all)
  show ?thesis
    by (rule wp_query_index_round_set_hit_bound_via_partial_union_or_collision
        [OF partial_bound collision_bound])
qed

lemma wp_query_index_set_hit_bound_via_partial_union_or_collision:
  fixes C H :: prob
  assumes partial_bound:
      "wp_event verify_monad
        (query_header_rounds_any_index_set_hit s
          (query_header_supported_partial_union_good_sets s good_sets)) s \<le>
        C"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (query_index_set_hit s good_sets) s \<le> C + H"
proof -
  have "wp_event verify_monad (query_index_set_hit s good_sets) s \<le>
      wp_event verify_monad (query_index_round_set_hit s good_sets) s"
    by (rule wp_event_mono) (rule query_index_set_hit_imp_round_set_hit)
  also have "... \<le> C + H"
    by (rule wp_query_index_round_set_hit_bound_via_partial_union_or_collision
        [OF partial_bound collision_bound])
  finally show ?thesis .
qed

lemma wp_query_index_round_set_hit_bound_if_supported_partial_header_candidate_unique_or_collision:
  fixes H :: prob
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and unique:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots final.
        \<exists>trace_table composition_table.
          query_header_supported_partial_table_candidates s fr f_fri_roots
            f_final as dg composition_fri_roots final \<subseteq>
            {(trace_table, composition_table)}"
    and subset:
      "\<And>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and bounded:
      "\<And>trace_table composition_table as.
        nnreal
          (query_raw_preimage_card_envelope
            (card (good_sets trace_table composition_table as))) /
          nnreal size \<le> query_error_bound"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (query_index_round_set_hit s good_sets) s \<le>
      nnreal rounds * query_error_bound + H"
proof -
  have union_bound:
    "\<And>fr f_fri_roots f_final as dg composition_fri_roots final.
      nnreal
        (query_raw_preimage_card_envelope
          (card
            (query_header_supported_partial_union_good_sets s good_sets fr
              f_fri_roots f_final as dg composition_fri_roots final))) /
      nnreal size \<le> query_error_bound"
    by (rule
        query_header_supported_partial_union_good_sets_fraction_bound_if_unique_candidate
        [OF unique subset bounded])
  show ?thesis
    by (rule
        wp_query_index_round_set_hit_bound_via_supported_partial_union_or_collision
        [OF future raw_bound union_bound collision_bound])
qed

lemma wp_query_index_set_hit_bound_if_supported_partial_header_candidate_unique_or_collision:
  fixes H :: prob
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and unique:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots final.
        \<exists>trace_table composition_table.
          query_header_supported_partial_table_candidates s fr f_fri_roots
            f_final as dg composition_fri_roots final \<subseteq>
            {(trace_table, composition_table)}"
    and subset:
      "\<And>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and bounded:
      "\<And>trace_table composition_table as.
        nnreal
          (query_raw_preimage_card_envelope
            (card (good_sets trace_table composition_table as))) /
          nnreal size \<le> query_error_bound"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (query_index_set_hit s good_sets) s \<le>
      nnreal rounds * query_error_bound + H"
proof -
  have "wp_event verify_monad (query_index_set_hit s good_sets) s \<le>
      wp_event verify_monad (query_index_round_set_hit s good_sets) s"
    by (rule wp_event_mono) (rule query_index_set_hit_imp_round_set_hit)
  also have "... \<le> nnreal rounds * query_error_bound + H"
    by (rule
        wp_query_index_round_set_hit_bound_if_supported_partial_header_candidate_unique_or_collision
        [OF future raw_bound unique subset bounded collision_bound])
  finally show ?thesis .
qed

lemma wp_query_sampling_success_set_hit_bound_if_supported_partial_header_candidate_unique_or_collision:
  fixes H :: prob
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and unique:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots final.
        \<exists>trace_table composition_table.
          query_header_supported_partial_table_candidates s fr f_fri_roots
            f_final as dg composition_fri_roots final \<subseteq>
            {(trace_table, composition_table)}"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad
      (query_index_set_hit s query_sampling_success_space) s \<le>
      nnreal rounds * query_error_bound + H"
  by (rule
      wp_query_index_set_hit_bound_if_supported_partial_header_candidate_unique_or_collision
      [OF future raw_bound unique query_sampling_success_space_subset
        query_sampling_success_space_envelope_fraction_bound
        collision_bound])

lemma composition_fri_supported_root_composition_table_candidate_state_hash_extends:
  assumes
    "composition_fri_supported_root_composition_table_candidate_state s fr
      f_fri_roots f_final as dg composition_fri_roots composition_table
      final_state"
  shows "s \<le> final_state"
proof -
  from assms obtain result trace_table query_idxs trace_bs comp_bs final rest
    where outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    unfolding composition_fri_supported_root_composition_table_candidate_state_def
    by blast
  show ?thesis
    by (rule verify_monad_hash_extends[OF outcome])
qed

lemma composition_fri_supported_root_composition_table_candidate_states_merkle_compatible_unique_if_clean_merge:
  assumes compatible:
      "merkle_hash_maps_compatible final_state final_state'"
    and clean:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    and candidate:
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state"
    and candidate':
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table'
        final_state'"
  shows "composition_table = composition_table'"
proof -
  from candidate obtain result trace_table query_idxs trace_bs comp_bs final
      rest where
    bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and bind:
      "merkle_root_binds_table (hd composition_fri_roots) composition_table
        final_state"
    unfolding composition_fri_supported_root_composition_table_candidate_state_def
    by blast
  from candidate' obtain result' trace_table' query_idxs' trace_bs' comp_bs'
      final' rest' where
    bound':
      "accepted_with_bound_tables s (Some (result', final_state'))
        trace_table' composition_table' as query_idxs'"
    and bind':
      "merkle_root_binds_table (hd composition_fri_roots) composition_table'
        final_state'"
    unfolding composition_fri_supported_root_composition_table_candidate_state_def
    by blast
  have same_len: "length composition_table = length composition_table'"
    using accepted_with_bound_tables_shapes(2)[OF bound]
      accepted_with_bound_tables_shapes(2)[OF bound']
    by simp
  have nonempty: "composition_table \<noteq> []"
    using accepted_with_bound_tables_shapes(2)[OF bound]
      eval_domain_nontrivial by auto
  show ?thesis
    by (rule
        merkle_root_binds_same_length_tables_merkle_compatible_unique_if_clean_merge
        [OF compatible clean bind bind' same_len nonempty])
qed

lemma composition_fri_supported_root_composition_table_candidates_subset_singleton_if_common_clean_merkle_extension:
  assumes clean: "\<not> hash_map_output_collision u"
    and common_ext:
      "\<And>composition_table final_state.
        composition_fri_supported_root_composition_table_candidate_state s fr
          f_fri_roots f_final as dg composition_fri_roots composition_table
          final_state \<Longrightarrow>
        merkle_hash_extends final_state u"
  shows
    "\<exists>composition_table.
      composition_fri_supported_root_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots \<subseteq>
        {composition_table}"
proof (cases
    "composition_fri_supported_root_composition_table_candidates s fr
      f_fri_roots f_final as dg composition_fri_roots = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"]) simp
next
  case False
  then obtain composition_table0 where table0:
    "composition_table0 \<in>
      composition_fri_supported_root_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots"
    by blast
  then obtain final_state0 where state0:
    "composition_fri_supported_root_composition_table_candidate_state s fr
      f_fri_roots f_final as dg composition_fri_roots composition_table0
      final_state0"
    using composition_fri_supported_root_composition_table_candidates_iff_state
    by blast
  have subset:
    "composition_fri_supported_root_composition_table_candidates s fr
      f_fri_roots f_final as dg composition_fri_roots \<subseteq>
      {composition_table0}"
  proof
    fix composition_table
    assume table:
      "composition_table \<in>
        composition_fri_supported_root_composition_table_candidates s fr
          f_fri_roots f_final as dg composition_fri_roots"
    then obtain final_state where state:
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state"
      using composition_fri_supported_root_composition_table_candidates_iff_state
      by blast
    have ext: "merkle_hash_extends final_state u"
      by (rule common_ext[OF state])
    have ext0: "merkle_hash_extends final_state0 u"
      by (rule common_ext[OF state0])
    have clean_pair:
      "\<not> merkle_hash_value_conflict final_state final_state0 \<and>
       \<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state0)"
      by (rule common_clean_merkle_extension_imp_pairwise_merkle_clean
          [OF ext ext0 clean])
    have compatible:
      "merkle_hash_maps_compatible final_state final_state0"
      using clean_pair
      unfolding merkle_hash_maps_compatible_iff_no_value_conflict by simp
    have clean_merge:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state0)"
      using clean_pair by simp
    have "composition_table = composition_table0"
      by (rule
          composition_fri_supported_root_composition_table_candidate_states_merkle_compatible_unique_if_clean_merge
          [OF compatible clean_merge state state0])
    then show "composition_table \<in> {composition_table0}"
      by simp
  qed
  then show ?thesis
    by blast
qed

lemma composition_fri_supported_root_composition_table_candidate_states_distinct_imp_merkle_conflict_or_merge_collision:
  assumes candidate:
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state"
    and candidate':
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table'
        final_state'"
    and distinct_tables: "composition_table \<noteq> composition_table'"
  shows
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
proof (rule ccontr)
  assume no_bad:
    "\<not> (merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state'))"
  have compatible:
    "merkle_hash_maps_compatible final_state final_state'"
    using no_bad unfolding merkle_hash_maps_compatible_iff_no_value_conflict
    by simp
  have clean:
    "\<not> hash_map_output_collision
      (merkle_hash_state_merge final_state final_state')"
    using no_bad by simp
  have "composition_table = composition_table'"
    by (rule
        composition_fri_supported_root_composition_table_candidate_states_merkle_compatible_unique_if_clean_merge
        [OF compatible clean candidate candidate'])
  then show False
    using distinct_tables by contradiction
qed

lemma composition_fri_supported_root_composition_table_candidates_not_singleton_imp_pairwise_merkle_bad:
  assumes not_unique:
      "\<not> (\<exists>composition_table.
        composition_fri_supported_root_composition_table_candidates s fr
          f_fri_roots f_final as dg composition_fri_roots \<subseteq>
          {composition_table})"
  shows
    "\<exists>composition_table final_state composition_table' final_state'.
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state \<and>
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table'
        final_state' \<and>
      composition_table \<noteq> composition_table' \<and>
      (merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state'))"
proof -
  let ?C =
    "composition_fri_supported_root_composition_table_candidates s fr
      f_fri_roots f_final as dg composition_fri_roots"
  have nonempty: "?C \<noteq> {}"
    using not_unique by auto
  then obtain composition_table where table: "composition_table \<in> ?C"
    by blast
  have "\<not> ?C \<subseteq> {composition_table}"
    using not_unique by blast
  then obtain composition_table' where table':
      "composition_table' \<in> ?C"
    and distinct_tables: "composition_table \<noteq> composition_table'"
    by auto
  from table obtain final_state where candidate:
    "composition_fri_supported_root_composition_table_candidate_state s fr
      f_fri_roots f_final as dg composition_fri_roots composition_table
      final_state"
    using composition_fri_supported_root_composition_table_candidates_iff_state
    by blast
  from table' obtain final_state' where candidate':
    "composition_fri_supported_root_composition_table_candidate_state s fr
      f_fri_roots f_final as dg composition_fri_roots composition_table'
      final_state'"
    using composition_fri_supported_root_composition_table_candidates_iff_state
    by blast
  have bad:
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    by (rule
        composition_fri_supported_root_composition_table_candidate_states_distinct_imp_merkle_conflict_or_merge_collision
        [OF candidate candidate' distinct_tables])
  show ?thesis
    using candidate candidate' distinct_tables bad by blast
qed

definition composition_fri_supported_root_pairwise_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> bool"
  where
    "composition_fri_supported_root_pairwise_merkle_bad s fr f_fri_roots
      f_final as dg composition_fri_roots \<longleftrightarrow>
      (\<exists>composition_table final_state composition_table' final_state'.
        composition_fri_supported_root_composition_table_candidate_state s fr
          f_fri_roots f_final as dg composition_fri_roots composition_table
          final_state \<and>
        composition_fri_supported_root_composition_table_candidate_state s fr
          f_fri_roots f_final as dg composition_fri_roots composition_table'
          final_state' \<and>
        composition_table \<noteq> composition_table' \<and>
        (merkle_hash_value_conflict final_state final_state' \<or>
          hash_map_output_collision
            (merkle_hash_state_merge final_state final_state')))"

definition composition_fri_supported_pairwise_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "composition_fri_supported_pairwise_merkle_bad s \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final as dg composition_fri_roots.
        composition_fri_supported_root_pairwise_merkle_bad s fr f_fri_roots
          f_final as dg composition_fri_roots)"

lemma composition_fri_supported_root_pairwise_merkle_bad_extends_initial:
  assumes bad:
    "composition_fri_supported_root_pairwise_merkle_bad s fr f_fri_roots
      f_final as dg composition_fri_roots"
  obtains composition_table final_state composition_table' final_state'
  where
    "composition_fri_supported_root_composition_table_candidate_state s fr
      f_fri_roots f_final as dg composition_fri_roots composition_table
      final_state"
    "composition_fri_supported_root_composition_table_candidate_state s fr
      f_fri_roots f_final as dg composition_fri_roots composition_table'
      final_state'"
    "composition_table \<noteq> composition_table'"
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    "s \<le> final_state"
    "s \<le> final_state'"
proof -
  from bad obtain composition_table final_state composition_table' final_state'
    where candidate:
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state"
    and candidate':
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table'
        final_state'"
    and distinct: "composition_table \<noteq> composition_table'"
    and pair_bad:
      "merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
    unfolding composition_fri_supported_root_pairwise_merkle_bad_def
    by blast
  have ext: "s \<le> final_state"
    by (rule
        composition_fri_supported_root_composition_table_candidate_state_hash_extends
        [OF candidate])
  have ext': "s \<le> final_state'"
    by (rule
        composition_fri_supported_root_composition_table_candidate_state_hash_extends
        [OF candidate'])
  show ?thesis
    by (rule that[OF candidate candidate' distinct pair_bad ext ext'])
qed

definition composition_fri_supported_root_pairwise_coupling_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> bool"
  where
    "composition_fri_supported_root_pairwise_coupling_bad s fr f_fri_roots
      f_final as dg composition_fri_roots \<longleftrightarrow>
      (\<exists>composition_table final_state composition_table' final_state'.
        composition_fri_supported_root_composition_table_candidate_state s fr
          f_fri_roots f_final as dg composition_fri_roots composition_table
          final_state \<and>
        composition_fri_supported_root_composition_table_candidate_state s fr
          f_fri_roots f_final as dg composition_fri_roots composition_table'
          final_state' \<and>
        composition_table \<noteq> composition_table' \<and>
        merkle_hash_pairwise_coupling_bad final_state final_state')"

definition composition_fri_supported_pairwise_coupling_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "composition_fri_supported_pairwise_coupling_bad s \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final as dg composition_fri_roots.
        composition_fri_supported_root_pairwise_coupling_bad s fr f_fri_roots
          f_final as dg composition_fri_roots)"

lemma composition_fri_supported_root_pairwise_merkle_bad_imp_local_collision_or_coupling_bad:
  assumes bad:
    "composition_fri_supported_root_pairwise_merkle_bad s fr f_fri_roots
      f_final as dg composition_fri_roots"
  shows
    "(\<exists>composition_table final_state composition_table' final_state'.
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state \<and>
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table'
        final_state' \<and>
      composition_table \<noteq> composition_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     composition_fri_supported_root_pairwise_coupling_bad s fr f_fri_roots
      f_final as dg composition_fri_roots"
proof -
  from bad obtain composition_table final_state composition_table' final_state'
    where candidate:
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state"
    and candidate':
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table'
        final_state'"
    and distinct: "composition_table \<noteq> composition_table'"
    and pair_bad:
      "merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
    unfolding composition_fri_supported_root_pairwise_merkle_bad_def
    by blast
  have decomp:
    "hash_map_output_collision final_state \<or>
     hash_map_output_collision final_state' \<or>
     merkle_hash_pairwise_coupling_bad final_state final_state'"
    by (rule merkle_hash_pairwise_bad_imp_local_collision_or_coupling_bad
        [OF pair_bad])
  then show ?thesis
  proof
    assume "hash_map_output_collision final_state"
    then show ?thesis
      using candidate candidate' distinct by blast
  next
    assume rest:
      "hash_map_output_collision final_state' \<or>
       merkle_hash_pairwise_coupling_bad final_state final_state'"
    then show ?thesis
    proof
      assume "hash_map_output_collision final_state'"
      then show ?thesis
        using candidate candidate' distinct by blast
    next
      assume "merkle_hash_pairwise_coupling_bad final_state final_state'"
      then have
        "composition_fri_supported_root_pairwise_coupling_bad s fr f_fri_roots
          f_final as dg composition_fri_roots"
        unfolding composition_fri_supported_root_pairwise_coupling_bad_def
        using candidate candidate' distinct by blast
      then show ?thesis by simp
    qed
  qed
qed

lemma composition_fri_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad:
  assumes bad: "composition_fri_supported_pairwise_merkle_bad s"
  shows
    "(\<exists>fr f_fri_roots f_final as dg composition_fri_roots
        composition_table final_state composition_table' final_state'.
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state \<and>
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table'
        final_state' \<and>
      composition_table \<noteq> composition_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     composition_fri_supported_pairwise_coupling_bad s"
proof -
  from bad obtain fr f_fri_roots f_final as dg composition_fri_roots where
    root_bad:
      "composition_fri_supported_root_pairwise_merkle_bad s fr f_fri_roots
        f_final as dg composition_fri_roots"
    unfolding composition_fri_supported_pairwise_merkle_bad_def by blast
  from
    composition_fri_supported_root_pairwise_merkle_bad_imp_local_collision_or_coupling_bad
      [OF root_bad]
  show ?thesis
    unfolding composition_fri_supported_pairwise_coupling_bad_def by blast
qed

lemma composition_fri_supported_pairwise_merkle_bad_imp_supported_hash_collision_possible_or_coupling_bad:
  assumes bad: "composition_fri_supported_pairwise_merkle_bad s"
  shows
    "supported_hash_output_collision_possible s \<or>
     composition_fri_supported_pairwise_coupling_bad s"
proof -
  have decomp:
    "(\<exists>fr f_fri_roots f_final as dg composition_fri_roots
        composition_table final_state composition_table' final_state'.
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state \<and>
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table'
        final_state' \<and>
      composition_table \<noteq> composition_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     composition_fri_supported_pairwise_coupling_bad s"
    by (rule
        composition_fri_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad
        [OF bad])
  then show ?thesis
  proof
    assume local:
      "\<exists>fr f_fri_roots f_final as dg composition_fri_roots
        composition_table final_state composition_table' final_state'.
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state \<and>
      composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table'
        final_state' \<and>
      composition_table \<noteq> composition_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')"
    then obtain fr f_fri_roots f_final as dg composition_fri_roots
        composition_table final_state composition_table' final_state' where
      candidate:
        "composition_fri_supported_root_composition_table_candidate_state s fr
          f_fri_roots f_final as dg composition_fri_roots composition_table
          final_state"
      and candidate':
        "composition_fri_supported_root_composition_table_candidate_state s fr
          f_fri_roots f_final as dg composition_fri_roots composition_table'
          final_state'"
      and collision:
        "hash_map_output_collision final_state \<or>
         hash_map_output_collision final_state'"
      by blast
    from collision show ?thesis
    proof
      assume collision_final: "hash_map_output_collision final_state"
      from candidate obtain result trace_table query_idxs trace_bs comp_bs final
          rest where
        outcome:
          "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
        and bound:
          "accepted_with_bound_tables s (Some (result, final_state))
            trace_table composition_table as query_idxs"
        unfolding
          composition_fri_supported_root_composition_table_candidate_state_def
        by blast
      have "supported_hash_output_collision_possible s"
        by (rule
            accepted_with_bound_tables_hash_collision_imp_supported_hash_output_collision_possible
            [OF outcome bound collision_final])
      then show ?thesis by simp
    next
      assume collision_final': "hash_map_output_collision final_state'"
      from candidate' obtain result' trace_table' query_idxs' trace_bs'
          comp_bs' final' rest' where
        outcome':
          "Some (result', final_state') \<in> set_dist (execute verify_monad s)"
        and bound':
          "accepted_with_bound_tables s (Some (result', final_state'))
            trace_table' composition_table' as query_idxs'"
        unfolding
          composition_fri_supported_root_composition_table_candidate_state_def
        by blast
      have "supported_hash_output_collision_possible s"
        by (rule
            accepted_with_bound_tables_hash_collision_imp_supported_hash_output_collision_possible
            [OF outcome' bound' collision_final'])
      then show ?thesis by simp
    qed
  next
    assume "composition_fri_supported_pairwise_coupling_bad s"
    then show ?thesis by simp
  qed
qed

definition alpha_output_local_candidate_ambiguity_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "alpha_output_local_candidate_ambiguity_bad s out \<longleftrightarrow>
      (\<exists>trace_table composition_table alphas query_idxs
          trace_table' composition_table' alphas' query_idxs'.
        accepted_with_bound_tables s out trace_table composition_table
          alphas query_idxs \<and>
        accepted_with_bound_tables s out trace_table' composition_table'
          alphas' query_idxs' \<and>
        trace_table \<noteq> trace_table')"

definition query_output_local_candidate_ambiguity_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_output_local_candidate_ambiguity_bad s out \<longleftrightarrow>
      accepted_bound_table_ambiguity_bad s out"

definition trace_fri_output_local_candidate_ambiguity_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_output_local_candidate_ambiguity_bad s out \<longleftrightarrow>
      (\<exists>trace_table composition_table alphas query_idxs
          trace_table' composition_table' alphas' query_idxs'
          trace_bs dg composition_bs.
        accepted_with_bound_tables s out trace_table composition_table
          alphas query_idxs \<and>
        accepted_with_bound_tables s out trace_table' composition_table'
          alphas' query_idxs' \<and>
        accepted_fri_challenges s out trace_bs dg composition_bs \<and>
        trace_table \<noteq> trace_table')"

definition composition_fri_output_local_candidate_ambiguity_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_fri_output_local_candidate_ambiguity_bad s out \<longleftrightarrow>
      (\<exists>trace_table composition_table alphas query_idxs
          trace_table' composition_table' alphas' query_idxs'
          trace_bs dg composition_bs.
        accepted_with_bound_tables s out trace_table composition_table
          alphas query_idxs \<and>
        accepted_with_bound_tables s out trace_table' composition_table'
          alphas' query_idxs' \<and>
        accepted_fri_challenges s out trace_bs dg composition_bs \<and>
        composition_table \<noteq> composition_table')"

definition supported_output_local_candidate_ambiguity_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "supported_output_local_candidate_ambiguity_bad s out \<longleftrightarrow>
      alpha_output_local_candidate_ambiguity_bad s out \<or>
      query_output_local_candidate_ambiguity_bad s out \<or>
      trace_fri_output_local_candidate_ambiguity_bad s out \<or>
      composition_fri_output_local_candidate_ambiguity_bad s out"

lemma alpha_output_local_candidate_ambiguity_bad_imp_accepted_bound_table_ambiguity_bad:
  assumes "alpha_output_local_candidate_ambiguity_bad s out"
  shows "accepted_bound_table_ambiguity_bad s out"
  using assms
  unfolding alpha_output_local_candidate_ambiguity_bad_def
    accepted_bound_table_ambiguity_bad_def
  by blast

lemma query_output_local_candidate_ambiguity_bad_imp_accepted_bound_table_ambiguity_bad:
  assumes "query_output_local_candidate_ambiguity_bad s out"
  shows "accepted_bound_table_ambiguity_bad s out"
  using assms unfolding query_output_local_candidate_ambiguity_bad_def .

lemma trace_fri_output_local_candidate_ambiguity_bad_imp_accepted_bound_table_ambiguity_bad:
  assumes "trace_fri_output_local_candidate_ambiguity_bad s out"
  shows "accepted_bound_table_ambiguity_bad s out"
  using assms
  unfolding trace_fri_output_local_candidate_ambiguity_bad_def
    accepted_bound_table_ambiguity_bad_def
  by blast

lemma composition_fri_output_local_candidate_ambiguity_bad_imp_accepted_bound_table_ambiguity_bad:
  assumes "composition_fri_output_local_candidate_ambiguity_bad s out"
  shows "accepted_bound_table_ambiguity_bad s out"
  using assms
  unfolding composition_fri_output_local_candidate_ambiguity_bad_def
    accepted_bound_table_ambiguity_bad_def
  by blast

lemma supported_output_local_candidate_ambiguity_bad_imp_accepted_bound_table_ambiguity_bad:
  assumes "supported_output_local_candidate_ambiguity_bad s out"
  shows "accepted_bound_table_ambiguity_bad s out"
  using assms
  unfolding supported_output_local_candidate_ambiguity_bad_def
  using
    alpha_output_local_candidate_ambiguity_bad_imp_accepted_bound_table_ambiguity_bad
    query_output_local_candidate_ambiguity_bad_imp_accepted_bound_table_ambiguity_bad
    trace_fri_output_local_candidate_ambiguity_bad_imp_accepted_bound_table_ambiguity_bad
    composition_fri_output_local_candidate_ambiguity_bad_imp_accepted_bound_table_ambiguity_bad
  by blast

lemma supported_output_local_candidate_ambiguity_bad_imp_hash_map_output_collision_bad:
  assumes "supported_output_local_candidate_ambiguity_bad s out"
  shows "hash_map_output_collision_bad s out"
  by (rule
      accepted_bound_table_ambiguity_bad_imp_hash_map_output_collision_bad)
    (rule
      supported_output_local_candidate_ambiguity_bad_imp_accepted_bound_table_ambiguity_bad
      [OF assms])

lemma supported_output_local_candidate_ambiguity_bad_mono_hash_map_output_collision_bad:
  "wp_event verify_monad
      (supported_output_local_candidate_ambiguity_bad s) s \<le>
    wp_event verify_monad (hash_map_output_collision_bad s) s"
  by (rule wp_event_mono)
    (rule
      supported_output_local_candidate_ambiguity_bad_imp_hash_map_output_collision_bad)

definition supported_output_local_side_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "supported_output_local_side_bad s out \<longleftrightarrow>
      hash_map_output_collision_bad s out \<or>
      supported_output_local_candidate_ambiguity_bad s out"

lemma supported_output_local_side_bad_iff_hash_map_output_collision_bad:
  "supported_output_local_side_bad s out \<longleftrightarrow>
    hash_map_output_collision_bad s out"
  unfolding supported_output_local_side_bad_def
  using
    supported_output_local_candidate_ambiguity_bad_imp_hash_map_output_collision_bad
  by blast

lemma supported_output_local_side_bad_imp_accepted:
  assumes "supported_output_local_side_bad s out"
  shows "accepted out"
  using assms
  unfolding supported_output_local_side_bad_iff_hash_map_output_collision_bad
  by (rule hash_map_output_collision_bad_imp_accepted)

lemma supported_output_local_side_bad_mono_hash_map_output_collision_bad:
  "wp_event verify_monad (supported_output_local_side_bad s) s \<le>
    wp_event verify_monad (hash_map_output_collision_bad s) s"
  by (rule wp_event_mono)
    (simp add: supported_output_local_side_bad_iff_hash_map_output_collision_bad)

end

end
