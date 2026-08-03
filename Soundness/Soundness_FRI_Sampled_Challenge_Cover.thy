(*  Title:      Stark/Soundness_FRI_Sampled_Challenge_Cover.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Sampled_Challenge_Cover
  imports
    Soundness_FRI_Query_Challenge_Trace_Staged_Product
    Soundness_FRI_Internal_Bounds
begin

text \<open>
  Generic sampled-query FRI challenge-cover reductions.

  This layer is deliberately independent of trace/composition naming.  The
  intended later FRI low-degree proof has to show that every sampled bad
  candidate produces a challenge list in an algebraic multiround bad set.  The
  lemmas here turn exactly that fact, plus local round cardinality bounds, into
  the finite-cover/fraction interface consumed by the staged route.
\<close>

lemma nnreal_nat_mult_divide_cancel_left:
  fixes a b c :: nat
  assumes "0 < b"
  shows "nnreal (a * b) / nnreal (b * c) = nnreal a / nnreal c"
proof -
  have b_ne: "(real b) \<noteq> 0"
    using assms by simp
  have "nn2real (nnreal (a * b) / nnreal (b * c)) =
      real (a * b) / real (b * c)"
    by (simp only: nn2real_divide nn2real_nnreal)
  also have "... = (real a * real b) / (real b * real c)"
    by (simp add: of_nat_mult)
  also have "... = real a / real c"
    using b_ne by (simp add: field_simps)
  also have "... = nn2real (nnreal a / nnreal c)"
    by (simp only: nn2real_divide nn2real_nnreal)
  finally have
    "nn2real (nnreal (a * b) / nnreal (b * c)) =
      nn2real (nnreal a / nnreal c)" .
  then show ?thesis
    by (simp only: nn2real_eq_iff)
qed

context soundness
begin

definition trace_fri_sampled_query_no_full_cover_failure_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_query_no_full_cover_failure_candidate s bad out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
        trace_roots trace_bs trace_final fri_query_idxs trace_round_layers
        layers \<and>
      \<not> generic_fri_sampled_full_cover_failure trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers
        (fri_canonical_domains (length trace_bs)) layers
        (bad trace_table))"

definition composition_fri_sampled_query_no_full_cover_failure_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_query_no_full_cover_failure_candidate s bad out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat fri_dg))
        (Not \<circ> composition_table_low_degree maxDegree) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers layers \<and>
      \<not> generic_fri_sampled_full_cover_failure
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        (fri_canonical_domains (length composition_bs)) layers
        (bad fri_dg composition_table))"

definition trace_fri_sampled_query_no_full_cover_failure_pairs
  :: "('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (nat list \<times> 'f list) set"
where
  "trace_fri_sampled_query_no_full_cover_failure_pairs bad =
    ({(query_idxs, challenges).
      \<exists>candidate_table roots final_value round_layers layers.
        generic_fri_sampled_query_candidate_evidence trace_table_low_degree
          (Not \<circ> trace_table_low_degree) candidate_table (clength - 1)
          roots challenges final_value query_idxs round_layers layers \<and>
        \<not> generic_fri_sampled_full_cover_failure trace_table_low_degree
          candidate_table (clength - 1) roots challenges final_value
          query_idxs round_layers (fri_canonical_domains (length challenges))
          layers (bad candidate_table)}
     \<inter> (fri_query_index_list_space \<times> UNIV))"

definition trace_fri_sampled_query_no_full_cover_failure_query_fiber
  :: "('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      'f list \<Rightarrow> nat list set"
where
  "trace_fri_sampled_query_no_full_cover_failure_query_fiber bad
      challenges =
    fri_query_challenge_pair_query_fiber
      (trace_fri_sampled_query_no_full_cover_failure_pairs bad)
      challenges"

definition composition_fri_sampled_query_no_full_cover_failure_pairs
  :: "('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      'f \<Rightarrow> (nat list \<times> 'f list) set"
where
  "composition_fri_sampled_query_no_full_cover_failure_pairs bad dg =
    ({(query_idxs, challenges).
      \<exists>candidate_table roots final_value round_layers layers.
        generic_fri_sampled_query_candidate_evidence
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree)
          candidate_table (to_nat dg) roots challenges final_value
          query_idxs round_layers layers \<and>
        \<not> generic_fri_sampled_full_cover_failure
          (composition_table_low_degree (to_nat dg)) candidate_table
          (to_nat dg) roots challenges final_value query_idxs round_layers
          (fri_canonical_domains (length challenges)) layers
          (bad dg candidate_table)}
     \<inter> (fri_query_index_list_space \<times> UNIV))"

definition composition_fri_sampled_query_no_full_cover_failure_query_fiber
  :: "('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> nat list set"
where
  "composition_fri_sampled_query_no_full_cover_failure_query_fiber bad dg
      challenges =
    fri_query_challenge_pair_query_fiber
      (composition_fri_sampled_query_no_full_cover_failure_pairs bad dg)
      challenges"

lemma trace_fri_sampled_query_no_full_cover_failure_pairs_subset:
  "trace_fri_sampled_query_no_full_cover_failure_pairs bad
    \<subseteq> trace_fri_sampled_query_bad_pair_union \<inter>
      (fri_query_index_list_space \<times> UNIV)"
proof
  fix pair
  assume pair_in:
    "pair \<in> trace_fri_sampled_query_no_full_cover_failure_pairs bad"
  obtain query_idxs challenges where pair_eq: "pair = (query_idxs, challenges)"
    by (cases pair)
  from pair_in pair_eq obtain candidate_table roots final_value round_layers
      layers where query_space: "query_idxs \<in> fri_query_index_list_space"
      and evidence:
        "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
          (Not \<circ> trace_table_low_degree) candidate_table (clength - 1)
          roots challenges final_value query_idxs round_layers layers"
    unfolding trace_fri_sampled_query_no_full_cover_failure_pairs_def
    by blast
  have pair_set:
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set trace_table_low_degree
        (Not \<circ> trace_table_low_degree) candidate_table (clength - 1)
        roots final_value round_layers layers"
    by (rule generic_fri_sampled_query_bad_pair_setI[OF evidence])
  then have union:
    "(query_idxs, challenges) \<in> trace_fri_sampled_query_bad_pair_union"
    unfolding trace_fri_sampled_query_bad_pair_union_def
    by (rule generic_fri_sampled_query_bad_pair_unionI)
  show
    "pair \<in> trace_fri_sampled_query_bad_pair_union \<inter>
      (fri_query_index_list_space \<times> UNIV)"
    using pair_eq query_space union by simp
qed

lemma trace_fri_sampled_query_no_full_cover_failure_pairs_challenge_projection:
  "snd ` trace_fri_sampled_query_no_full_cover_failure_pairs bad
    \<subseteq> fri_challenge_space (ceil_log clength)"
  using trace_fri_sampled_query_no_full_cover_failure_pairs_subset
    trace_fri_restricted_sampled_query_bad_pair_union_challenge_projection
  by blast

lemma trace_fri_sampled_query_no_full_cover_failure_query_fiber_subset:
  "trace_fri_sampled_query_no_full_cover_failure_query_fiber bad challenges
    \<subseteq> fri_query_index_list_space"
  unfolding trace_fri_sampled_query_no_full_cover_failure_query_fiber_def
  using trace_fri_sampled_query_no_full_cover_failure_pairs_subset
  by (auto simp: fri_query_challenge_pair_query_fiber_def)

lemma composition_fri_sampled_query_no_full_cover_failure_pairs_subset:
  "composition_fri_sampled_query_no_full_cover_failure_pairs bad dg
    \<subseteq> composition_fri_sampled_query_bad_pair_union dg \<inter>
      (fri_query_index_list_space \<times> UNIV)"
proof
  fix pair
  assume pair_in:
    "pair \<in> composition_fri_sampled_query_no_full_cover_failure_pairs
      bad dg"
  obtain query_idxs challenges where pair_eq: "pair = (query_idxs, challenges)"
    by (cases pair)
  from pair_in pair_eq obtain candidate_table roots final_value round_layers
      layers where query_space: "query_idxs \<in> fri_query_index_list_space"
      and evidence:
        "generic_fri_sampled_query_candidate_evidence
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree)
          candidate_table (to_nat dg) roots challenges final_value
          query_idxs round_layers layers"
    unfolding composition_fri_sampled_query_no_full_cover_failure_pairs_def
    by blast
  have pair_set:
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree)
        candidate_table (to_nat dg) roots final_value round_layers layers"
    by (rule generic_fri_sampled_query_bad_pair_setI[OF evidence])
  then have union:
    "(query_idxs, challenges) \<in>
      composition_fri_sampled_query_bad_pair_union dg"
    unfolding composition_fri_sampled_query_bad_pair_union_def
    by (rule generic_fri_sampled_query_bad_pair_unionI)
  show
    "pair \<in> composition_fri_sampled_query_bad_pair_union dg \<inter>
      (fri_query_index_list_space \<times> UNIV)"
    using pair_eq query_space union by simp
qed

lemma composition_fri_sampled_query_no_full_cover_failure_pairs_challenge_projection:
  "snd ` composition_fri_sampled_query_no_full_cover_failure_pairs bad dg
    \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
  using composition_fri_sampled_query_no_full_cover_failure_pairs_subset
    composition_fri_restricted_sampled_query_bad_pair_union_challenge_projection
  by blast

lemma composition_fri_sampled_query_no_full_cover_failure_query_fiber_subset:
  "composition_fri_sampled_query_no_full_cover_failure_query_fiber bad dg
      challenges
    \<subseteq> fri_query_index_list_space"
  unfolding composition_fri_sampled_query_no_full_cover_failure_query_fiber_def
  using composition_fri_sampled_query_no_full_cover_failure_pairs_subset
  by (auto simp: fri_query_challenge_pair_query_fiber_def)

lemma trace_fri_sampled_query_no_full_cover_failure_candidate_imp_pair_hit:
  assumes
    "trace_fri_sampled_query_no_full_cover_failure_candidate s bad out"
  shows
    "trace_fri_query_challenge_pair_set_hit s
      (trace_fri_sampled_query_no_full_cover_failure_pairs bad) out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table layers where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and candidate:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
        trace_roots trace_bs trace_final fri_query_idxs trace_round_layers
        layers"
    and no_failure:
      "\<not> generic_fri_sampled_full_cover_failure trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers
        (fri_canonical_domains (length trace_bs)) layers
        (bad trace_table)"
    unfolding trace_fri_sampled_query_no_full_cover_failure_candidate_def
    by fastforce
  have transcript:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers"
    using evidence
    unfolding trace_fri_partial_candidate_opening_evidence_def by blast
  have query_space:
    "fri_query_idxs \<in> fri_query_index_list_space"
    by (rule accepted_fri_opening_transcript_query_index_list_space
        [OF transcript])
  have pair:
    "(fri_query_idxs, trace_bs) \<in>
      trace_fri_sampled_query_no_full_cover_failure_pairs bad"
    unfolding trace_fri_sampled_query_no_full_cover_failure_pairs_def
    using candidate no_failure query_space by blast
  show ?thesis
    unfolding trace_fri_query_challenge_pair_set_hit_def
    using transcript pair by blast
qed

lemma composition_fri_sampled_query_no_full_cover_failure_candidate_imp_pair_hit:
  assumes
    "composition_fri_sampled_query_no_full_cover_failure_candidate s bad out"
  shows
    "composition_fri_query_challenge_pair_set_hit s
      (composition_fri_sampled_query_no_full_cover_failure_pairs bad) out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table layers where
    evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table"
    and candidate:
      "generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat fri_dg))
        (Not \<circ> composition_table_low_degree maxDegree) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers layers"
    and no_failure:
      "\<not> generic_fri_sampled_full_cover_failure
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        (fri_canonical_domains (length composition_bs)) layers
        (bad fri_dg composition_table)"
    unfolding composition_fri_sampled_query_no_full_cover_failure_candidate_def
    by fastforce
  have transcript:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      fri_dg opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    using evidence
    unfolding composition_fri_partial_candidate_opening_evidence_def by blast
  have query_space:
    "fri_query_idxs \<in> fri_query_index_list_space"
    by (rule accepted_fri_opening_transcript_query_index_list_space
        [OF transcript])
  have pair:
    "(fri_query_idxs, composition_bs) \<in>
      composition_fri_sampled_query_no_full_cover_failure_pairs bad fri_dg"
    unfolding composition_fri_sampled_query_no_full_cover_failure_pairs_def
    using candidate no_failure query_space by blast
  show ?thesis
    unfolding composition_fri_query_challenge_pair_set_hit_def
    using transcript pair by blast
qed

lemma trace_fri_sampled_query_no_full_cover_failure_candidate_not_None[simp]:
  "\<not> trace_fri_sampled_query_no_full_cover_failure_candidate s bad None"
  unfolding trace_fri_sampled_query_no_full_cover_failure_candidate_def
    trace_fri_partial_candidate_opening_evidence_def
    accepted_fri_opening_transcript_def
  by simp

lemma composition_fri_sampled_query_no_full_cover_failure_candidate_not_None[simp]:
  "\<not> composition_fri_sampled_query_no_full_cover_failure_candidate s bad
    None"
  unfolding composition_fri_sampled_query_no_full_cover_failure_candidate_def
    composition_fri_partial_candidate_opening_evidence_def
    accepted_fri_opening_transcript_def
  by simp

lemma trace_fri_sampled_query_no_full_cover_failure_candidate_imp_bad_candidate:
  assumes
    "trace_fri_sampled_query_no_full_cover_failure_candidate s bad out"
  shows "trace_fri_sampled_query_bad_candidate s out"
  using assms
  unfolding trace_fri_sampled_query_no_full_cover_failure_candidate_def
    trace_fri_sampled_query_bad_candidate_def
  by force

lemma composition_fri_sampled_query_no_full_cover_failure_candidate_imp_bad_candidate:
  assumes
    "composition_fri_sampled_query_no_full_cover_failure_candidate s bad out"
  shows "composition_fri_sampled_query_bad_candidate s out"
  using assms
  unfolding
    composition_fri_sampled_query_no_full_cover_failure_candidate_def
    composition_fri_sampled_query_bad_candidate_def
  by force

lemma trace_fri_sampled_query_bad_candidate_imp_no_full_cover_or_failure:
  assumes sampled: "trace_fri_sampled_query_bad_candidate s out"
  shows
    "trace_fri_sampled_query_no_full_cover_failure_candidate s bad out \<or>
     trace_fri_sampled_full_cover_failure s bad out"
proof -
  from sampled obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and candidate:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
        trace_roots trace_bs trace_final fri_query_idxs trace_round_layers
        layers"
    unfolding trace_fri_sampled_query_bad_candidate_def by blast
  have canonical:
    "generic_fri_canonical_sampled_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers layers"
    by (rule generic_fri_sampled_query_candidate_evidenceD(1)
        [OF candidate])
  have chain:
    "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers
      (fri_canonical_domains (length trace_bs)) layers"
  proof -
    have sampled_chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers
        (fri_canonical_domains (length trace_bs)) layers"
      by (rule generic_fri_canonical_sampled_layer_chain_evidenceD
          [OF canonical])
    then show ?thesis .
  qed
  show ?thesis
  proof (cases
      "generic_fri_sampled_full_cover_failure trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers
        (fri_canonical_domains (length trace_bs)) layers
        (bad trace_table)")
    case False
    then have
      "trace_fri_sampled_query_no_full_cover_failure_candidate s bad out"
      unfolding trace_fri_sampled_query_no_full_cover_failure_candidate_def
      using evidence candidate by blast
    then show ?thesis by simp
  next
    case True
    then have "trace_fri_sampled_full_cover_failure s bad out"
      unfolding trace_fri_sampled_full_cover_failure_def
      using evidence chain by blast
    then show ?thesis by simp
  qed
qed

lemma composition_fri_sampled_query_bad_candidate_imp_no_full_cover_or_failure:
  assumes sampled: "composition_fri_sampled_query_bad_candidate s out"
  shows
    "composition_fri_sampled_query_no_full_cover_failure_candidate s bad out \<or>
     composition_fri_sampled_full_cover_failure s bad out"
proof -
  from sampled obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table"
    and candidate:
      "generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat fri_dg))
        (Not \<circ> composition_table_low_degree maxDegree) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers layers"
    unfolding composition_fri_sampled_query_bad_candidate_def by meson
  have canonical:
    "generic_fri_canonical_sampled_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers layers"
    by (rule generic_fri_sampled_query_candidate_evidenceD(1)
        [OF candidate])
  have chain:
    "generic_fri_sampled_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers
      (fri_canonical_domains (length composition_bs)) layers"
  proof -
    have sampled_chain:
      "generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        (fri_canonical_domains (length composition_bs)) layers"
      by (rule generic_fri_canonical_sampled_layer_chain_evidenceD
          [OF canonical])
    then show ?thesis .
  qed
  show ?thesis
  proof (cases
      "generic_fri_sampled_full_cover_failure
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        (fri_canonical_domains (length composition_bs)) layers
        (bad fri_dg composition_table)")
    case False
    then have
      "composition_fri_sampled_query_no_full_cover_failure_candidate s bad out"
      unfolding
        composition_fri_sampled_query_no_full_cover_failure_candidate_def
      using evidence candidate by meson
    then show ?thesis by simp
  next
    case True
    then have "composition_fri_sampled_full_cover_failure s bad out"
      unfolding composition_fri_sampled_full_cover_failure_def
      using evidence chain by meson
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_failure:
  assumes no_failure_bound:
    "wp_event verify_monad
      (trace_fri_sampled_query_no_full_cover_failure_candidate s bad) s
      \<le> N"
    and failure_bound:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_failure s bad) s \<le> F"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> N + F"
proof -
  have "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> wp_event verify_monad
        (\<lambda>out.
          trace_fri_sampled_query_no_full_cover_failure_candidate s bad out \<or>
          trace_fri_sampled_full_cover_failure s bad out) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_query_bad_candidate_imp_no_full_cover_or_failure)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_sampled_query_no_full_cover_failure_candidate s bad) s +
      wp_event verify_monad
        (trace_fri_sampled_full_cover_failure s bad) s"
    by (rule wp_event_union_bound)
  also have "... \<le> N + F"
    by (rule add_mono[OF no_failure_bound failure_bound])
  finally show ?thesis .
qed

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_failure:
  assumes no_failure_bound:
    "wp_event verify_monad
      (composition_fri_sampled_query_no_full_cover_failure_candidate s bad) s
      \<le> N"
    and failure_bound:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_failure s bad) s \<le> F"
  shows
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> N + F"
proof -
  have "wp_event verify_monad
        (composition_fri_sampled_query_bad_candidate s) s
      \<le> wp_event verify_monad
        (\<lambda>out.
          composition_fri_sampled_query_no_full_cover_failure_candidate s bad
            out \<or>
          composition_fri_sampled_full_cover_failure s bad out) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_sampled_query_bad_candidate_imp_no_full_cover_or_failure)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_sampled_query_no_full_cover_failure_candidate s bad)
        s +
      wp_event verify_monad
        (composition_fri_sampled_full_cover_failure s bad) s"
    by (rule wp_event_union_bound)
  also have "... \<le> N + F"
    by (rule add_mono[OF no_failure_bound failure_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_failure:
  assumes no_failure_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_query_no_full_cover_failure_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> N"
    and failure_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> N + F"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> trace_fri_sampled_query_bad_candidate s None"
    unfolding trace_fri_sampled_query_bad_candidate_def
      trace_fri_partial_candidate_opening_evidence_def
      accepted_fri_opening_transcript_def
    by simp
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad (trace_fri_sampled_query_bad_candidate ?s) ?s
      \<le> N + F"
    by (rule
        wp_trace_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_failure)
      (rule no_failure_bound[OF support], rule failure_bound[OF support])
qed

lemma checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_failure:
  assumes no_failure_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_query_no_full_cover_failure_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> N"
    and failure_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> N + F"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> composition_fri_sampled_query_bad_candidate s None"
    unfolding composition_fri_sampled_query_bad_candidate_def
      composition_fri_partial_candidate_opening_evidence_def
      accepted_fri_opening_transcript_def
    by simp
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (composition_fri_sampled_query_bad_candidate ?s) ?s \<le> N + F"
    by (rule
        wp_composition_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_failure)
      (rule no_failure_bound[OF support], rule failure_bound[OF support])
qed

lemma checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_staged_no_full_cover_or_failure:
  assumes no_failure_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_query_no_full_cover_failure_candidate s bad))
      adversary_initial_state \<le> N"
    and failure_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_full_cover_failure s bad))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> N + F"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s out.
            trace_fri_sampled_query_no_full_cover_failure_candidate s bad
              out \<or>
            trace_fri_sampled_full_cover_failure s bad out))
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest: trace_fri_sampled_query_bad_candidate_imp_no_full_cover_or_failure
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_sampled_query_no_full_cover_failure_candidate s
              bad) out \<or>
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_sampled_full_cover_failure s bad) out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_sampled_query_no_full_cover_failure_candidate s
            bad))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_sampled_full_cover_failure s bad))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> N + F"
    by (rule add_mono[OF no_failure_bound failure_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_staged_no_full_cover_or_failure:
  assumes no_failure_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          composition_fri_sampled_query_no_full_cover_failure_candidate s
            bad))
      adversary_initial_state \<le> N"
    and failure_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_full_cover_failure s bad))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> N + F"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s out.
            composition_fri_sampled_query_no_full_cover_failure_candidate s
              bad out \<or>
            composition_fri_sampled_full_cover_failure s bad out))
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest:
          composition_fri_sampled_query_bad_candidate_imp_no_full_cover_or_failure
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            (\<lambda>s.
              composition_fri_sampled_query_no_full_cover_failure_candidate s
                bad) out \<or>
          staged_security_with_data_state_verifier_event
            (\<lambda>s. composition_fri_sampled_full_cover_failure s bad) out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s.
            composition_fri_sampled_query_no_full_cover_failure_candidate s
              bad))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_sampled_full_cover_failure s bad))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> N + F"
    by (rule add_mono[OF no_failure_bound failure_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_sampled_query_no_full_cover_failure_candidate_bound_from_pair_fraction_challenge_weighted:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fraction:
      "generic_fri_sampled_query_pair_fraction_bound trace_table_low_degree
        (Not \<circ> trace_table_low_degree) (clength - 1) C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_query_no_full_cover_failure_candidate s bad))
      adversary_initial_state \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>challenges \<in> fri_challenge_space (ceil_log clength).
            generic_fri_sampled_query_query_fiber trace_table_low_degree
              (Not \<circ> trace_table_low_degree) (clength - 1) challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value
        (card (fri_challenge_space (ceil_log clength)) * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_query_no_full_cover_failure_candidate s bad))
      adversary_initial_state
      \<le> wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_sampled_query_bad_candidate)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          trace_fri_sampled_query_no_full_cover_failure_candidate_imp_bad_candidate
        split: option.splits prod.splits)
  also have "... \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>challenges \<in> fri_challenge_space (ceil_log clength).
            generic_fri_sampled_query_query_fiber trace_table_low_degree
              (Not \<circ> trace_table_low_degree) (clength - 1) challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value
        (card (fri_challenge_space (ceil_log clength)) * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_pair_fraction_challenge_weighted
        [OF wf controlled fraction])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_sampled_query_no_full_cover_failure_candidate_bound_from_restricted_pairs:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_query_no_full_cover_failure_candidate s bad))
      adversary_initial_state \<le>
      (\<Sum>challenges \<in> fri_challenge_space (ceil_log clength).
        (1 / nnreal (CARD('f) ^ ceil_log clength)) *
          (nnreal
            (card
              (trace_fri_sampled_query_no_full_cover_failure_query_fiber
                bad challenges)) *
            (1 / nnreal (card query_sample_space)) ^ rounds)) +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>challenges \<in> fri_challenge_space (ceil_log clength).
            trace_fri_sampled_query_no_full_cover_failure_query_fiber
              bad challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value
        (card (fri_challenge_space (ceil_log clength)) * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  let ?P = "trace_fri_sampled_query_no_full_cover_failure_pairs bad"
  let ?B = "fri_challenge_space (ceil_log clength)"
  let ?Q =
    "trace_fri_sampled_query_no_full_cover_failure_query_fiber bad"
  have event_le:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_query_no_full_cover_failure_candidate s bad))
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s ?P))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          trace_fri_sampled_query_no_full_cover_failure_candidate_imp_pair_hit
        split: option.splits prod.splits)
  have pair_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s ?P))
      adversary_initial_state \<le>
      (\<Sum>challenges \<in> ?B.
        (1 / nnreal (CARD('f) ^ ceil_log clength)) *
          (nnreal (card (?Q challenges)) *
            (1 / nnreal (card query_sample_space)) ^ rounds)) +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>challenges \<in> ?B. ?Q challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value (card ?B * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  proof (rule
      checked_staged_security_trace_fri_query_challenge_pair_set_hit_challenge_weighted_bound
      [OF wf controlled])
    show "?B \<subseteq> fri_challenge_space (ceil_log clength)"
      by simp
  next
    show "snd ` ?P \<subseteq> ?B"
      by (rule
          trace_fri_sampled_query_no_full_cover_failure_pairs_challenge_projection)
  next
    fix challenges
    assume "challenges \<in> ?B"
    show "fst ` (?P \<inter> (UNIV \<times> {challenges})) \<subseteq>
      ?Q challenges"
      unfolding trace_fri_sampled_query_no_full_cover_failure_query_fiber_def
        fri_query_challenge_pair_query_fiber_def
      by force
  next
    fix challenges
    assume "challenges \<in> ?B"
    show "?Q challenges \<subseteq> fri_query_index_list_space"
      by (rule
          trace_fri_sampled_query_no_full_cover_failure_query_fiber_subset)
  qed
  show ?thesis
    by (rule order_trans[OF event_le pair_bound])
qed

lemma checked_staged_security_composition_fri_sampled_query_no_full_cover_failure_candidate_bound_from_restricted_pairs:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          composition_fri_sampled_query_no_full_cover_failure_candidate s
            bad))
      adversary_initial_state \<le>
      (\<Sum>dg \<in> UNIV.
        \<Sum>challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
          (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
            (nnreal
              (card
                (composition_fri_sampled_query_no_full_cover_failure_query_fiber
                  bad dg challenges)) *
              (1 / nnreal (card query_sample_space)) ^ rounds)) +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>dg \<in> UNIV.
            \<Union>challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
              composition_fri_sampled_query_no_full_cover_failure_query_fiber
                bad dg challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (fri_challenge_space (ceil_log (to_nat dg + 1))) *
            ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  let ?P =
    "composition_fri_sampled_query_no_full_cover_failure_pairs bad"
  let ?B =
    "\<lambda>dg. fri_challenge_space (ceil_log (to_nat dg + 1))"
  let ?Q =
    "composition_fri_sampled_query_no_full_cover_failure_query_fiber bad"
  have event_le:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          composition_fri_sampled_query_no_full_cover_failure_candidate s
            bad))
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s ?P))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_fri_sampled_query_no_full_cover_failure_candidate_imp_pair_hit
        split: option.splits prod.splits)
  have pair_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s ?P))
      adversary_initial_state \<le>
      (\<Sum>dg \<in> UNIV.
        \<Sum>challenges \<in> ?B dg.
          (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
            (nnreal (card (?Q dg challenges)) *
              (1 / nnreal (card query_sample_space)) ^ rounds)) +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>dg \<in> UNIV. \<Union>challenges \<in> ?B dg.
            ?Q dg challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (?B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  proof (rule
      checked_staged_security_composition_fri_query_challenge_pair_set_hit_challenge_weighted_bound
      [OF wf controlled])
    fix dg
    show "?B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
      by simp
  next
    fix dg
    show "snd ` ?P dg \<subseteq> ?B dg"
      by (rule
          composition_fri_sampled_query_no_full_cover_failure_pairs_challenge_projection)
  next
    fix dg challenges
    assume "challenges \<in> ?B dg"
    show "fst ` (?P dg \<inter> (UNIV \<times> {challenges})) \<subseteq>
      ?Q dg challenges"
      unfolding
        composition_fri_sampled_query_no_full_cover_failure_query_fiber_def
        fri_query_challenge_pair_query_fiber_def
      by force
  next
    fix dg challenges
    assume "challenges \<in> ?B dg"
    show "?Q dg challenges \<subseteq> fri_query_index_list_space"
      by (rule
          composition_fri_sampled_query_no_full_cover_failure_query_fiber_subset)
  qed
  show ?thesis
    by (rule order_trans[OF event_le pair_bound])
qed

lemma checked_staged_security_composition_fri_sampled_query_no_full_cover_failure_candidate_bound_from_pair_fraction_challenge_weighted:
  fixes C :: "'f \<Rightarrow> prob"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fraction:
      "\<And>dg. generic_fri_sampled_query_pair_fraction_bound
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg) (C dg)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          composition_fri_sampled_query_no_full_cover_failure_candidate s
            bad))
      adversary_initial_state \<le>
      (\<Sum>dg \<in> UNIV. C dg) +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>dg \<in> UNIV.
            \<Union>challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
              generic_fri_sampled_query_query_fiber
                (composition_table_low_degree (to_nat dg))
                (Not \<circ> composition_table_low_degree maxDegree)
                (to_nat dg) challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (fri_challenge_space (ceil_log (to_nat dg + 1))) *
            ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          composition_fri_sampled_query_no_full_cover_failure_candidate s
            bad))
      adversary_initial_state
      \<le> wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_sampled_query_bad_candidate)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_fri_sampled_query_no_full_cover_failure_candidate_imp_bad_candidate
        split: option.splits prod.splits)
  also have "... \<le>
      (\<Sum>dg \<in> UNIV. C dg) +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>dg \<in> UNIV.
            \<Union>challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
              generic_fri_sampled_query_query_fiber
                (composition_table_low_degree (to_nat dg))
                (Not \<circ> composition_table_low_degree maxDegree)
                (to_nat dg) challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (fri_challenge_space (ceil_log (to_nat dg + 1))) *
            ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_pair_fraction_challenge_weighted
        [OF wf controlled fraction])
  finally show ?thesis .
qed

lemma finite_generic_fri_bad_challenge_lists:
  "finite (generic_fri_bad_challenge_lists n bad)"
proof (rule finite_subset)
  show "generic_fri_bad_challenge_lists n bad \<subseteq> fri_challenge_space n"
    by (rule generic_fri_bad_challenge_lists_subset)
  show "finite (fri_challenge_space n)"
    by (rule finite_fri_challenge_space)
qed

lemma generic_fri_sampled_query_finite_cover_from_bad_challenge_lists:
  assumes cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound degree_bound) bad"
  shows
    "generic_fri_sampled_query_finite_cover low_degree candidate_bad
      degree_bound
      (generic_fri_bad_challenge_lists
        (fri_round_count_for_degree_bound degree_bound) bad)"
proof (rule generic_fri_sampled_query_finite_cover_from_candidate_challenge_cover)
  show "finite
      (generic_fri_bad_challenge_lists
        (fri_round_count_for_degree_bound degree_bound) bad)"
    by (rule finite_generic_fri_bad_challenge_lists)
  fix candidate_table roots final_value round_layers layers query_idxs
    challenges
  assume query_space: "query_idxs \<in> fri_query_index_list_space"
    and evidence:
      "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers"
  show "challenges \<in>
      generic_fri_bad_challenge_lists
        (fri_round_count_for_degree_bound degree_bound) bad"
    by (rule cover[OF query_space evidence])
qed

lemma generic_fri_sampled_query_projection_fraction_bound_from_bad_challenge_round_bounds:
  assumes cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound degree_bound) bad"
    and local_bound:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound degree_bound \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad i prefix) \<le> bd i"
    and fraction_bound:
      "nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound degree_bound}.
          CARD('f) ^ i * bd i *
            CARD('f) ^
              (fri_round_count_for_degree_bound degree_bound - Suc i)) /
        nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
  shows
    "generic_fri_sampled_query_projection_fraction_bound low_degree
      candidate_bad degree_bound C"
proof -
  let ?n = "fri_round_count_for_degree_bound degree_bound"
  let ?B = "generic_fri_bad_challenge_lists ?n bad"
  let ?K =
    "(\<Sum>i \<in> {..<?n}.
      CARD('f) ^ i * bd i * CARD('f) ^ (?n - Suc i))"
  have cover_B:
    "generic_fri_sampled_query_finite_cover low_degree candidate_bad
      degree_bound ?B"
    by (rule generic_fri_sampled_query_finite_cover_from_bad_challenge_lists
        [OF cover])
  have card_bound: "card ?B \<le> ?K"
    by (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds)
      (rule local_bound)
  have ratio_bound:
    "nnreal (card ?B) / nnreal (CARD('f) ^ ?n) \<le> C"
  proof -
    have "nnreal (card ?B) / nnreal (CARD('f) ^ ?n)
        \<le> nnreal ?K / nnreal (CARD('f) ^ ?n)"
      using card_bound by (rule nnreal_nat_divide_right_mono)
    also have "... \<le> C"
      by (rule fraction_bound)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule generic_fri_sampled_query_projection_fraction_bound_from_cover
        [OF cover_B ratio_bound])
qed

lemma generic_fri_sampled_query_projection_fraction_bound_from_one_step_disagreement_subset:
  assumes cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound degree_bound) bad"
    and local_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound degree_bound \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
    and fraction_bound:
      "nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound degree_bound}.
          CARD('f) ^ i * (len i div 2) *
            CARD('f) ^
              (fri_round_count_for_degree_bound degree_bound - Suc i)) /
        nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
  shows
    "generic_fri_sampled_query_projection_fraction_bound low_degree
      candidate_bad degree_bound C"
proof (rule
    generic_fri_sampled_query_projection_fraction_bound_from_bad_challenge_round_bounds
    [OF cover _ fraction_bound])
  fix i :: nat and prefix :: "'f list"
  assume i: "i < fri_round_count_for_degree_bound degree_bound"
    and prefix: "length prefix = i"
  have "card (bad i prefix) \<le>
      card
        (fri_one_step_disagreement_challenges
          (len i) (pw i) (layer i prefix) (claimed i prefix)
          (domains i prefix))"
    by (rule card_mono) (simp_all add: local_subset[OF i prefix])
  also have "... \<le> len i div 2"
    by (rule fri_one_step_disagreement_challenges_card_bound_local)
  finally show "card (bad i prefix) \<le> len i div 2" .
qed

lemma generic_fri_sampled_query_projection_fraction_bound_from_one_step_disagreement_subset_exact:
  assumes cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound degree_bound) bad"
    and local_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound degree_bound \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
  shows
    "generic_fri_sampled_query_projection_fraction_bound low_degree
      candidate_bad degree_bound
      (fri_one_step_disagreement_round_fraction
        (fri_round_count_for_degree_bound degree_bound) len)"
proof (rule
    generic_fri_sampled_query_projection_fraction_bound_from_one_step_disagreement_subset)
  fix candidate_table roots final_value round_layers layers query_idxs challenges
  assume query_idxs: "query_idxs \<in> fri_query_index_list_space"
    and evidence:
      "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers"
  show "challenges \<in>
      generic_fri_bad_challenge_lists
        (fri_round_count_for_degree_bound degree_bound) bad"
    by (rule cover[OF query_idxs evidence])
next
  fix i :: nat and prefix :: "'f list"
  assume i: "i < fri_round_count_for_degree_bound degree_bound"
    and prefix: "length prefix = i"
  show "bad i prefix \<subseteq>
      fri_one_step_disagreement_challenges
        (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
    by (rule local_subset[OF i prefix])
next
  show "nnreal
      (\<Sum>i\<in>{..<fri_round_count_for_degree_bound degree_bound}.
        CARD('f) ^ i * (len i div 2) *
          CARD('f) ^
            (fri_round_count_for_degree_bound degree_bound - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> fri_one_step_disagreement_round_fraction
        (fri_round_count_for_degree_bound degree_bound) len"
    by (rule fri_one_step_disagreement_round_fraction_refl_bound)
qed

lemma generic_fri_sampled_query_pair_fraction_bound_from_bad_challenge_round_bounds:
  assumes cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound degree_bound) bad"
    and local_bound:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound degree_bound \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad i prefix) \<le> bd i"
    and fraction_bound:
      "nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound degree_bound}.
          CARD('f) ^ i * bd i *
            CARD('f) ^
              (fri_round_count_for_degree_bound degree_bound - Suc i)) /
        nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
  shows
    "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound C"
proof -
  let ?n = "fri_round_count_for_degree_bound degree_bound"
  let ?B = "generic_fri_bad_challenge_lists ?n bad"
  let ?K =
    "(\<Sum>i \<in> {..<?n}.
      CARD('f) ^ i * bd i * CARD('f) ^ (?n - Suc i))"
  have projection:
    "generic_fri_sampled_query_challenge_projection low_degree
      candidate_bad degree_bound \<subseteq> ?B"
  proof
    fix challenges
    assume challenges_in:
      "challenges \<in>
        generic_fri_sampled_query_challenge_projection low_degree
          candidate_bad degree_bound"
    then obtain query_idxs where pair:
      "(query_idxs, challenges) \<in>
        generic_fri_sampled_query_restricted_bad_pairs low_degree
          candidate_bad degree_bound"
      unfolding generic_fri_sampled_query_challenge_projection_def by force
    then have query_space: "query_idxs \<in> fri_query_index_list_space"
      unfolding generic_fri_sampled_query_restricted_bad_pairs_def by simp
    have pair_union:
      "(query_idxs, challenges) \<in>
        generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
          degree_bound"
      using pair
      unfolding generic_fri_sampled_query_restricted_bad_pairs_def by simp
    then obtain candidate_table roots final_value round_layers layers where
      pair_set:
        "(query_idxs, challenges) \<in>
          generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
            candidate_table degree_bound roots final_value round_layers layers"
      unfolding generic_fri_sampled_query_bad_pair_union_def by auto
    have evidence:
      "generic_fri_sampled_query_candidate_evidence low_degree
        candidate_bad candidate_table degree_bound roots challenges
        final_value query_idxs round_layers layers"
      by (rule generic_fri_sampled_query_bad_pair_setD[OF pair_set])
    show "challenges \<in> ?B"
      by (rule cover[OF query_space evidence])
  qed
  have card_bound: "card ?B \<le> ?K"
    by (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds)
      (rule local_bound)
  have ratio_bound:
    "nnreal (card ?B * card fri_query_index_list_space) /
      nnreal (card fri_query_index_list_space * CARD('f) ^ ?n)
      \<le> C"
  proof -
    have card_q_pos: "0 < card fri_query_index_list_space"
      by (simp add: card_fri_query_index_list_space
          query_sample_space_size_pos)
    then have card_q_ne: "card fri_query_index_list_space \<noteq> 0"
      by simp
    have "nnreal (card ?B * card fri_query_index_list_space) /
        nnreal (card fri_query_index_list_space * CARD('f) ^ ?n) =
        nnreal (card ?B) / nnreal (CARD('f) ^ ?n)"
      by (rule nnreal_nat_mult_divide_cancel_left[OF card_q_pos])
    also have "... \<le> nnreal ?K / nnreal (CARD('f) ^ ?n)"
      using card_bound by (rule nnreal_nat_divide_right_mono)
    also have "... \<le> C"
      by (rule fraction_bound)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule generic_fri_sampled_query_pair_fraction_bound_from_projection_and_fibers
        [OF finite_generic_fri_bad_challenge_lists projection _ ratio_bound])
      (meson card_mono finite_fri_query_index_list_space
        generic_fri_sampled_query_query_fiber_subset)
qed

lemma generic_fri_sampled_query_pair_fraction_bound_from_one_step_disagreement_subset:
  assumes cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound degree_bound) bad"
    and local_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound degree_bound \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
    and fraction_bound:
      "nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound degree_bound}.
          CARD('f) ^ i * (len i div 2) *
            CARD('f) ^
              (fri_round_count_for_degree_bound degree_bound - Suc i)) /
        nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
  shows
    "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound C"
proof (rule
    generic_fri_sampled_query_pair_fraction_bound_from_bad_challenge_round_bounds
    [OF cover _ fraction_bound])
  fix i :: nat and prefix :: "'f list"
  assume i: "i < fri_round_count_for_degree_bound degree_bound"
    and prefix: "length prefix = i"
  have "card (bad i prefix) \<le>
      card
        (fri_one_step_disagreement_challenges
          (len i) (pw i) (layer i prefix) (claimed i prefix)
          (domains i prefix))"
    by (rule card_mono) (simp_all add: local_subset[OF i prefix])
  also have "... \<le> len i div 2"
    by (rule fri_one_step_disagreement_challenges_card_bound_local)
  finally show "card (bad i prefix) \<le> len i div 2" .
qed

lemma generic_fri_sampled_query_pair_fraction_bound_from_one_step_disagreement_subset_exact:
  assumes cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound degree_bound) bad"
    and local_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound degree_bound \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
  shows
    "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound
      (fri_one_step_disagreement_round_fraction
        (fri_round_count_for_degree_bound degree_bound) len)"
proof (rule
    generic_fri_sampled_query_pair_fraction_bound_from_one_step_disagreement_subset)
  fix candidate_table roots final_value round_layers layers query_idxs challenges
  assume query_idxs: "query_idxs \<in> fri_query_index_list_space"
    and evidence:
      "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers"
  show "challenges \<in>
      generic_fri_bad_challenge_lists
        (fri_round_count_for_degree_bound degree_bound) bad"
    by (rule cover[OF query_idxs evidence])
next
  fix i :: nat and prefix :: "'f list"
  assume i: "i < fri_round_count_for_degree_bound degree_bound"
    and prefix: "length prefix = i"
  show "bad i prefix \<subseteq>
      fri_one_step_disagreement_challenges
        (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
    by (rule local_subset[OF i prefix])
next
  show "nnreal
      (\<Sum>i\<in>{..<fri_round_count_for_degree_bound degree_bound}.
        CARD('f) ^ i * (len i div 2) *
          CARD('f) ^
            (fri_round_count_for_degree_bound degree_bound - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> fri_one_step_disagreement_round_fraction
        (fri_round_count_for_degree_bound degree_bound) len"
    by (rule fri_one_step_disagreement_round_fraction_refl_bound)
qed

lemma trace_fri_sampled_query_pair_fraction_bound_from_bad_challenge_round_bounds:
  assumes cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) candidate_table (clength - 1)
        roots challenges final_value query_idxs round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound (clength - 1)) bad"
    and local_bound:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad i prefix) \<le> bd i"
    and fraction_bound:
      "nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (clength - 1)}.
          CARD('f) ^ i * bd i *
            CARD('f) ^
              (fri_round_count_for_degree_bound (clength - 1) - Suc i)) /
        nnreal (CARD('f) ^ fri_round_count_for_degree_bound (clength - 1))
      \<le> C"
  shows
    "generic_fri_sampled_query_pair_fraction_bound trace_table_low_degree
      (Not \<circ> trace_table_low_degree) (clength - 1) C"
  by (rule
      generic_fri_sampled_query_pair_fraction_bound_from_bad_challenge_round_bounds
      [OF cover local_bound fraction_bound])

lemma generic_fri_sampled_query_pair_fraction_bound_from_full_cover_round_bounds:
  assumes full_cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      \<exists>doms. generic_fri_sampled_layer_chain_full_cover low_degree
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers doms layers bad"
    and local_bound:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound degree_bound \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad i prefix) \<le> bd i"
    and fraction_bound:
      "nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound degree_bound}.
          CARD('f) ^ i * bd i *
            CARD('f) ^
              (fri_round_count_for_degree_bound degree_bound - Suc i)) /
        nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
  shows
    "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound C"
proof (rule
    generic_fri_sampled_query_pair_fraction_bound_from_bad_challenge_round_bounds
    [OF _ local_bound fraction_bound])
  fix candidate_table roots final_value round_layers layers query_idxs
    challenges
  assume query_space: "query_idxs \<in> fri_query_index_list_space"
    and evidence:
      "generic_fri_sampled_query_candidate_evidence low_degree
        candidate_bad candidate_table degree_bound roots challenges
        final_value query_idxs round_layers layers"
  obtain doms where cover:
    "generic_fri_sampled_layer_chain_full_cover low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers doms
      layers bad"
    using full_cover[OF query_space evidence] by blast
  have bad:
    "challenges \<in> generic_fri_bad_challenge_lists (length challenges) bad"
    by (rule generic_fri_sampled_layer_chain_full_cover_bad_challenge_list
        [OF cover])
  have canonical:
    "generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
    by (rule generic_fri_sampled_query_candidate_evidenceD(1)[OF evidence])
  have sampled:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
    by (rule generic_fri_canonical_sampled_layer_chain_evidenceD
        [OF canonical])
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF sampled])
  have len:
    "length challenges = fri_round_count_for_degree_bound degree_bound"
    using generic_fri_partial_evidence_shapes(1,2)[OF partial] by simp
  show "challenges \<in>
      generic_fri_bad_challenge_lists
        (fri_round_count_for_degree_bound degree_bound) bad"
    using bad by (simp add: len)
qed

lemma generic_fri_sampled_query_candidate_evidence_full_cover_if_no_failure:
  assumes evidence:
    "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
    and no_failure:
      "\<not> generic_fri_sampled_full_cover_failure low_degree candidate_table
        degree_bound roots challenges final_value query_idxs round_layers
        (fri_canonical_domains (length challenges)) layers bad"
  shows
    "\<exists>doms. generic_fri_sampled_layer_chain_full_cover low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers doms layers bad"
proof -
  have canonical:
    "generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
    by (rule generic_fri_sampled_query_candidate_evidenceD(1)[OF evidence])
  have sampled:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
    by (rule generic_fri_canonical_sampled_layer_chain_evidenceD
        [OF canonical])
  show ?thesis
    using sampled no_failure
    unfolding generic_fri_sampled_layer_chain_full_cover_def
      generic_fri_sampled_full_cover_failure_def
    by blast
qed

lemma generic_fri_sampled_query_pair_fraction_bound_from_no_full_cover_failure_round_bounds:
  assumes no_failure:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      \<not> generic_fri_sampled_full_cover_failure low_degree candidate_table
        degree_bound roots challenges final_value query_idxs round_layers
        (fri_canonical_domains (length challenges)) layers bad"
    and local_bound:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound degree_bound \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad i prefix) \<le> bd i"
    and fraction_bound:
      "nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound degree_bound}.
          CARD('f) ^ i * bd i *
            CARD('f) ^
              (fri_round_count_for_degree_bound degree_bound - Suc i)) /
        nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
  shows
    "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound C"
proof (rule
    generic_fri_sampled_query_pair_fraction_bound_from_full_cover_round_bounds
    [OF _ local_bound fraction_bound])
  fix candidate_table roots final_value round_layers layers query_idxs
    challenges
  assume query_space: "query_idxs \<in> fri_query_index_list_space"
    and evidence:
      "generic_fri_sampled_query_candidate_evidence low_degree
        candidate_bad candidate_table degree_bound roots challenges
        final_value query_idxs round_layers layers"
  show "\<exists>doms. generic_fri_sampled_layer_chain_full_cover low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers doms layers bad"
    by (rule generic_fri_sampled_query_candidate_evidence_full_cover_if_no_failure
        [OF evidence no_failure[OF query_space evidence]])
qed

lemma trace_fri_sampled_query_pair_fraction_bound_from_full_cover_round_bounds:
  assumes full_cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) candidate_table (clength - 1)
        roots challenges final_value query_idxs round_layers layers \<Longrightarrow>
      \<exists>doms. generic_fri_sampled_layer_chain_full_cover
        trace_table_low_degree candidate_table (clength - 1) roots
        challenges final_value query_idxs round_layers doms layers bad"
    and local_bound:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad i prefix) \<le> bd i"
    and fraction_bound:
      "nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (clength - 1)}.
          CARD('f) ^ i * bd i *
            CARD('f) ^
              (fri_round_count_for_degree_bound (clength - 1) - Suc i)) /
        nnreal (CARD('f) ^ fri_round_count_for_degree_bound (clength - 1))
      \<le> C"
  shows
    "generic_fri_sampled_query_pair_fraction_bound trace_table_low_degree
      (Not \<circ> trace_table_low_degree) (clength - 1) C"
  by (rule
      generic_fri_sampled_query_pair_fraction_bound_from_full_cover_round_bounds
      [OF full_cover local_bound fraction_bound])

lemma trace_fri_sampled_query_pair_fraction_bound_from_no_full_cover_failure_round_bounds:
  assumes no_failure:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) candidate_table (clength - 1)
        roots challenges final_value query_idxs round_layers layers \<Longrightarrow>
      \<not> generic_fri_sampled_full_cover_failure trace_table_low_degree
        candidate_table (clength - 1) roots challenges final_value
        query_idxs round_layers (fri_canonical_domains (length challenges))
        layers bad"
    and local_bound:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad i prefix) \<le> bd i"
    and fraction_bound:
      "nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (clength - 1)}.
          CARD('f) ^ i * bd i *
            CARD('f) ^
              (fri_round_count_for_degree_bound (clength - 1) - Suc i)) /
        nnreal (CARD('f) ^ fri_round_count_for_degree_bound (clength - 1))
      \<le> C"
  shows
    "generic_fri_sampled_query_pair_fraction_bound trace_table_low_degree
      (Not \<circ> trace_table_low_degree) (clength - 1) C"
  by (rule
      generic_fri_sampled_query_pair_fraction_bound_from_no_full_cover_failure_round_bounds
      [OF no_failure local_bound fraction_bound])

lemma composition_fri_sampled_query_pair_fraction_bound_from_bad_challenge_round_bounds:
  fixes dg :: 'f
  assumes cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) candidate_table
        (to_nat dg) roots challenges final_value query_idxs round_layers
        layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound (to_nat dg)) (bad dg)"
    and local_bound:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad dg i prefix) \<le> bd dg i"
    and fraction_bound:
      "\<And>dg.
        nnreal
          (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (to_nat dg)}.
            CARD('f) ^ i * bd dg i *
              CARD('f) ^
                (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
          nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
        \<le> C dg"
  shows
    "generic_fri_sampled_query_pair_fraction_bound
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg) (C dg)"
  proof (rule
      generic_fri_sampled_query_pair_fraction_bound_from_bad_challenge_round_bounds)
    fix candidate_table roots final_value round_layers layers query_idxs
      challenges
    assume query_space: "query_idxs \<in> fri_query_index_list_space"
      and evidence:
        "generic_fri_sampled_query_candidate_evidence
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree) candidate_table
          (to_nat dg) roots challenges final_value query_idxs round_layers
          layers"
    show "challenges \<in>
      generic_fri_bad_challenge_lists
        (fri_round_count_for_degree_bound (to_nat dg)) (bad dg)"
      by (rule cover[OF query_space evidence])
  next
    fix i and prefix :: "'f list"
    assume i: "i < fri_round_count_for_degree_bound (to_nat dg)"
      and len: "length prefix = i"
    show "card (bad dg i prefix) \<le> bd dg i"
      by (rule local_bound[OF i len])
  next
    show "nnreal
      (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (to_nat dg)}.
        CARD('f) ^ i * bd dg i *
          CARD('f) ^
            (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
      \<le> C dg"
      by (rule fraction_bound)
  qed

lemma composition_fri_sampled_query_pair_fraction_bound_from_full_cover_round_bounds:
  fixes dg :: 'f
  assumes full_cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) candidate_table
        (to_nat dg) roots challenges final_value query_idxs round_layers
        layers \<Longrightarrow>
      \<exists>doms. generic_fri_sampled_layer_chain_full_cover
        (composition_table_low_degree (to_nat dg)) candidate_table
        (to_nat dg) roots challenges final_value query_idxs round_layers doms
        layers (bad dg)"
    and local_bound:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad dg i prefix) \<le> bd dg i"
    and fraction_bound:
      "\<And>dg.
        nnreal
          (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (to_nat dg)}.
            CARD('f) ^ i * bd dg i *
              CARD('f) ^
                (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
          nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
        \<le> C dg"
  shows
    "generic_fri_sampled_query_pair_fraction_bound
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg) (C dg)"
  proof (rule
      generic_fri_sampled_query_pair_fraction_bound_from_full_cover_round_bounds)
    fix candidate_table roots final_value round_layers layers query_idxs
      challenges
    assume query_space: "query_idxs \<in> fri_query_index_list_space"
      and evidence:
        "generic_fri_sampled_query_candidate_evidence
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree) candidate_table
          (to_nat dg) roots challenges final_value query_idxs round_layers
          layers"
    show "\<exists>doms. generic_fri_sampled_layer_chain_full_cover
      (composition_table_low_degree (to_nat dg)) candidate_table
      (to_nat dg) roots challenges final_value query_idxs round_layers doms
      layers (bad dg)"
      by (rule full_cover[OF query_space evidence])
  next
    fix i and prefix :: "'f list"
    assume i: "i < fri_round_count_for_degree_bound (to_nat dg)"
      and len: "length prefix = i"
    show "card (bad dg i prefix) \<le> bd dg i"
      by (rule local_bound[OF i len])
  next
    show "nnreal
      (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (to_nat dg)}.
        CARD('f) ^ i * bd dg i *
          CARD('f) ^
            (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
      \<le> C dg"
      by (rule fraction_bound)
  qed

lemma composition_fri_sampled_query_pair_fraction_bound_from_no_full_cover_failure_round_bounds:
  fixes dg :: 'f
  assumes no_failure:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) candidate_table
        (to_nat dg) roots challenges final_value query_idxs round_layers
        layers \<Longrightarrow>
      \<not> generic_fri_sampled_full_cover_failure
        (composition_table_low_degree (to_nat dg)) candidate_table
        (to_nat dg) roots challenges final_value query_idxs round_layers
        (fri_canonical_domains (length challenges)) layers (bad dg)"
    and local_bound:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad dg i prefix) \<le> bd dg i"
    and fraction_bound:
      "\<And>dg.
        nnreal
          (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (to_nat dg)}.
            CARD('f) ^ i * bd dg i *
              CARD('f) ^
                (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
          nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
        \<le> C dg"
  shows
    "generic_fri_sampled_query_pair_fraction_bound
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg) (C dg)"
  proof (rule
      generic_fri_sampled_query_pair_fraction_bound_from_no_full_cover_failure_round_bounds)
    fix candidate_table roots final_value round_layers layers query_idxs
      challenges
    assume query_space: "query_idxs \<in> fri_query_index_list_space"
      and evidence:
        "generic_fri_sampled_query_candidate_evidence
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree) candidate_table
          (to_nat dg) roots challenges final_value query_idxs round_layers
          layers"
    show "\<not> generic_fri_sampled_full_cover_failure
      (composition_table_low_degree (to_nat dg)) candidate_table
      (to_nat dg) roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers (bad dg)"
      by (rule no_failure[OF query_space evidence])
  next
    fix i and prefix :: "'f list"
    assume i: "i < fri_round_count_for_degree_bound (to_nat dg)"
      and len: "length prefix = i"
    show "card (bad dg i prefix) \<le> bd dg i"
      by (rule local_bound[OF i len])
  next
    show "nnreal
      (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (to_nat dg)}.
        CARD('f) ^ i * bd dg i *
          CARD('f) ^
            (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
      \<le> C dg"
      by (rule fraction_bound)
  qed

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_bad_challenge_round_bounds:
  assumes future: "trace_fri_future_fresh s"
    and cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) candidate_table (clength - 1)
        roots challenges final_value query_idxs round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound (clength - 1)) bad"
    and local_bound:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad i prefix) \<le> bd i"
    and fraction_bound:
      "nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (clength - 1)}.
          CARD('f) ^ i * bd i *
            CARD('f) ^
              (fri_round_count_for_degree_bound (clength - 1) - Suc i)) /
        nnreal (CARD('f) ^ fri_round_count_for_degree_bound (clength - 1))
      \<le> C"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> C"
proof (rule
    wp_trace_fri_sampled_query_bad_candidate_bound_from_generic_projection_fraction
    [OF future])
  show
    "generic_fri_sampled_query_projection_fraction_bound
      trace_table_low_degree (Not \<circ> trace_table_low_degree)
      (clength - 1) C"
    by (rule
        generic_fri_sampled_query_projection_fraction_bound_from_bad_challenge_round_bounds
        [OF cover local_bound fraction_bound])
qed

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_one_step_disagreement_subset:
  assumes future: "trace_fri_future_fresh s"
    and cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) candidate_table (clength - 1)
        roots challenges final_value query_idxs round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound (clength - 1)) bad"
    and local_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
    and fraction_bound:
      "nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (clength - 1)}.
          CARD('f) ^ i * (len i div 2) *
            CARD('f) ^
              (fri_round_count_for_degree_bound (clength - 1) - Suc i)) /
        nnreal (CARD('f) ^ fri_round_count_for_degree_bound (clength - 1))
      \<le> C"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> C"
proof (rule
    wp_trace_fri_sampled_query_bad_candidate_bound_from_generic_projection_fraction
    [OF future])
  show
    "generic_fri_sampled_query_projection_fraction_bound
      trace_table_low_degree (Not \<circ> trace_table_low_degree)
      (clength - 1) C"
    by (rule
        generic_fri_sampled_query_projection_fraction_bound_from_one_step_disagreement_subset
        [OF cover local_subset fraction_bound])
qed

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_one_step_disagreement_subset_exact:
  assumes future: "trace_fri_future_fresh s"
    and cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) candidate_table (clength - 1)
        roots challenges final_value query_idxs round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound (clength - 1)) bad"
    and local_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le>
      fri_one_step_disagreement_round_fraction
        (fri_round_count_for_degree_bound (clength - 1)) len"
proof (rule wp_trace_fri_sampled_query_bad_candidate_bound_from_one_step_disagreement_subset)
  show "trace_fri_future_fresh s"
    by (rule future)
next
  fix candidate_table roots final_value round_layers layers query_idxs challenges
  assume query_idxs: "query_idxs \<in> fri_query_index_list_space"
    and evidence:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) candidate_table (clength - 1)
        roots challenges final_value query_idxs round_layers layers"
  show "challenges \<in>
      generic_fri_bad_challenge_lists
        (fri_round_count_for_degree_bound (clength - 1)) bad"
    by (rule cover[OF query_idxs evidence])
next
  fix i :: nat and prefix :: "'f list"
  assume i: "i < fri_round_count_for_degree_bound (clength - 1)"
    and prefix: "length prefix = i"
  show "bad i prefix \<subseteq>
      fri_one_step_disagreement_challenges
        (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
    by (rule local_subset[OF i prefix])
next
  show "nnreal
      (\<Sum>i\<in>{..<fri_round_count_for_degree_bound (clength - 1)}.
        CARD('f) ^ i * (len i div 2) *
          CARD('f) ^
            (fri_round_count_for_degree_bound (clength - 1) - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound (clength - 1))
      \<le> fri_one_step_disagreement_round_fraction
        (fri_round_count_for_degree_bound (clength - 1)) len"
    by (rule fri_one_step_disagreement_round_fraction_refl_bound)
qed

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_canonical_one_step_disagreement_subset:
  assumes future: "trace_fri_future_fresh s"
    and cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) candidate_table (clength - 1)
        roots challenges final_value query_idxs round_layers layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound (clength - 1)) bad"
    and local_subset:
      "\<And>i prefix.
        i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        bad i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (trace_fri_canonical_layer_len i) (pw i)
            (layer i prefix) (claimed i prefix) (domains i prefix)"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> concrete_trace_fri_bad_challenge_fraction"
  using
    wp_trace_fri_sampled_query_bad_candidate_bound_from_one_step_disagreement_subset_exact
      [OF future cover local_subset]
  by (simp add: concrete_trace_fri_bad_challenge_fraction_def)

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_bad_challenge_round_bounds:
  assumes future: "composition_fri_future_fresh s"
    and cover:
    "\<And>dg candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) candidate_table
        (to_nat dg) roots challenges final_value query_idxs round_layers
        layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound (to_nat dg)) (bad dg)"
    and local_bound:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        card (bad dg i prefix) \<le> bd dg i"
    and fraction_bound:
      "\<And>dg.
        nnreal
          (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (to_nat dg)}.
            CARD('f) ^ i * bd dg i *
              CARD('f) ^
                (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
          nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
        \<le> C"
  shows
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> C"
proof (rule
    wp_composition_fri_sampled_query_bad_candidate_bound_from_generic_projection_fraction
    [OF future])
  fix dg :: 'f
  show
    "generic_fri_sampled_query_projection_fraction_bound
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree)
      (to_nat dg) C"
  proof (rule
      generic_fri_sampled_query_projection_fraction_bound_from_bad_challenge_round_bounds)
    fix candidate_table roots final_value round_layers layers query_idxs
      challenges
    assume query_space: "query_idxs \<in> fri_query_index_list_space"
      and evidence:
        "generic_fri_sampled_query_candidate_evidence
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree) candidate_table
          (to_nat dg) roots challenges final_value query_idxs round_layers
          layers"
    show "challenges \<in>
      generic_fri_bad_challenge_lists
        (fri_round_count_for_degree_bound (to_nat dg)) (bad dg)"
      by (rule cover[OF query_space evidence])
  next
    fix i and prefix :: "'f list"
    assume i: "i < fri_round_count_for_degree_bound (to_nat dg)"
      and len: "length prefix = i"
    show "card (bad dg i prefix) \<le> bd dg i"
      by (rule local_bound[OF i len])
  next
    show "nnreal
      (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (to_nat dg)}.
        CARD('f) ^ i * bd dg i *
          CARD('f) ^
            (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
      \<le> C"
      by (rule fraction_bound)
  qed
qed

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_one_step_disagreement_subset:
  assumes future: "composition_fri_future_fresh s"
    and cover:
    "\<And>dg candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) candidate_table
        (to_nat dg) roots challenges final_value query_idxs round_layers
        layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound (to_nat dg)) (bad dg)"
    and local_subset:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        bad dg i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (len dg i) (pw dg i) (layer dg i prefix)
            (claimed dg i prefix) (domains dg i prefix)"
    and fraction_bound:
      "\<And>dg.
        nnreal
          (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (to_nat dg)}.
            CARD('f) ^ i * (len dg i div 2) *
              CARD('f) ^
                (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
          nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
        \<le> C"
  shows
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> C"
proof (rule
    wp_composition_fri_sampled_query_bad_candidate_bound_from_generic_projection_fraction
    [OF future])
  fix dg :: 'f
  show
    "generic_fri_sampled_query_projection_fraction_bound
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree)
      (to_nat dg) C"
  proof (rule
      generic_fri_sampled_query_projection_fraction_bound_from_one_step_disagreement_subset)
    fix candidate_table roots final_value round_layers layers query_idxs
      challenges
    assume query_space: "query_idxs \<in> fri_query_index_list_space"
      and evidence:
        "generic_fri_sampled_query_candidate_evidence
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree) candidate_table
          (to_nat dg) roots challenges final_value query_idxs round_layers
          layers"
    show "challenges \<in>
      generic_fri_bad_challenge_lists
        (fri_round_count_for_degree_bound (to_nat dg)) (bad dg)"
      by (rule cover[OF query_space evidence])
  next
    fix i and prefix :: "'f list"
    assume i: "i < fri_round_count_for_degree_bound (to_nat dg)"
      and prefix: "length prefix = i"
    show "bad dg i prefix \<subseteq>
      fri_one_step_disagreement_challenges
        (len dg i) (pw dg i) (layer dg i prefix)
        (claimed dg i prefix) (domains dg i prefix)"
      by (rule local_subset[OF i prefix])
  next
    show "nnreal
        (\<Sum>i\<in>{..<fri_round_count_for_degree_bound (to_nat dg)}.
          CARD('f) ^ i * (len dg i div 2) *
            CARD('f) ^
              (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
      \<le> C"
      by (rule fraction_bound)
  qed
qed

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_one_step_disagreement_subset_exact_bound:
  assumes future: "composition_fri_future_fresh s"
    and cover:
    "\<And>dg candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) candidate_table
        (to_nat dg) roots challenges final_value query_idxs round_layers
        layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound (to_nat dg)) (bad dg)"
    and local_subset:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        bad dg i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (len dg i) (pw dg i) (layer dg i prefix)
            (claimed dg i prefix) (domains dg i prefix)"
    and fraction_bound:
      "\<And>dg.
        fri_one_step_disagreement_round_fraction
          (fri_round_count_for_degree_bound (to_nat dg)) (len dg)
        \<le> C"
  shows
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> C"
proof (rule
    wp_composition_fri_sampled_query_bad_candidate_bound_from_one_step_disagreement_subset
    [OF future cover local_subset])
  fix dg
  show "nnreal
      (\<Sum>i\<in>{..<fri_round_count_for_degree_bound (to_nat dg)}.
        CARD('f) ^ i * (len dg i div 2) *
          CARD('f) ^
            (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
      \<le> C"
    using fraction_bound[of dg]
    by (simp add: fri_one_step_disagreement_round_fraction_def
      fri_bad_challenge_round_fraction_def
      fri_one_step_disagreement_round_mass_def
      fri_bad_challenge_round_mass_def)
qed

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_canonical_one_step_disagreement_subset:
  assumes future: "composition_fri_future_fresh s"
    and cover:
    "\<And>dg candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) candidate_table
        (to_nat dg) roots challenges final_value query_idxs round_layers
        layers \<Longrightarrow>
      challenges \<in>
        generic_fri_bad_challenge_lists
          (fri_round_count_for_degree_bound (to_nat dg)) (bad dg)"
    and local_subset:
      "\<And>dg i prefix.
        i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
        length prefix = i \<Longrightarrow>
        bad dg i prefix \<subseteq>
          fri_one_step_disagreement_challenges
            (composition_fri_canonical_layer_len dg i) (pw dg i)
            (layer dg i prefix) (claimed dg i prefix) (domains dg i prefix)"
  shows
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> concrete_composition_fri_bad_challenge_fraction"
proof (rule
    wp_composition_fri_sampled_query_bad_candidate_bound_from_one_step_disagreement_subset_exact_bound)
  show "composition_fri_future_fresh s"
    by (rule future)
next
  fix dg candidate_table roots final_value round_layers layers query_idxs
    challenges
  assume query_idxs: "query_idxs \<in> fri_query_index_list_space"
    and evidence:
      "generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) candidate_table
        (to_nat dg) roots challenges final_value query_idxs round_layers
        layers"
  show "challenges \<in>
      generic_fri_bad_challenge_lists
        (fri_round_count_for_degree_bound (to_nat dg)) (bad dg)"
    by (rule cover[OF query_idxs evidence])
next
  fix dg and i :: nat and prefix :: "'f list"
  assume i: "i < fri_round_count_for_degree_bound (to_nat dg)"
    and prefix: "length prefix = i"
  show "bad dg i prefix \<subseteq>
      fri_one_step_disagreement_challenges
        (composition_fri_canonical_layer_len dg i) (pw dg i)
        (layer dg i prefix) (claimed dg i prefix) (domains dg i prefix)"
    by (rule local_subset[OF i prefix])
next
  fix dg
  show "fri_one_step_disagreement_round_fraction
      (fri_round_count_for_degree_bound (to_nat dg))
      (composition_fri_canonical_layer_len dg)
      \<le> concrete_composition_fri_bad_challenge_fraction"
    by (rule concrete_composition_fri_bad_challenge_fraction_ge)
qed

end

end
