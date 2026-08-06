(*  Title:      Stark/Soundness_FRI_Sampled_Interface.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Sampled_Interface
  imports
    Soundness_FRI_Derived_Active_Reductions
begin

section \<open>Concrete FRI Query Bounds and Public Endpoint\<close>

text \<open>
  Sampled-query FRI interface.

  This theory names the FRI bad-candidate event that matches the verifier's
  sampled evidence: authenticated partial openings, sampled fold checks on the
  canonical domains, final consistency, and a non-low-degree candidate.  It is
  deliberately separate from the full-cover compatibility route, where sampled
  openings are temporarily strengthened to full fold-index coverage.
\<close>

context soundness
begin

definition fri_query_index_list_space :: "nat list set"
where
  "fri_query_index_list_space =
    {query_idxs. length query_idxs = rounds \<and>
      set query_idxs \<subseteq> query_sample_space}"

definition trace_fri_query_index_list_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat list set \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_query_index_list_set_hit s Q out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      fri_query_idxs \<in> Q)"

definition composition_fri_query_index_list_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat list set \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_query_index_list_set_hit s Q out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      fri_query_idxs \<in> Q)"

definition query_index_list_entries :: "nat list set \<Rightarrow> nat set"
where
  "query_index_list_entries Q = (\<Union>query_idxs \<in> Q. set query_idxs)"

lemma query_index_list_entries_subset_query_sample_space:
  assumes "Q \<subseteq> fri_query_index_list_space"
  shows "query_index_list_entries Q \<subseteq> query_sample_space"
  using assms
  unfolding query_index_list_entries_def fri_query_index_list_space_def
  by auto

lemma finite_query_index_list_entries:
  assumes "Q \<subseteq> fri_query_index_list_space"
  shows "finite (query_index_list_entries Q)"
  using query_index_list_entries_subset_query_sample_space[OF assms]
  by (rule finite_subset) (rule finite_query_sample_space)

lemma query_index_list_entries_card_le:
  assumes finite_Q: "finite Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows "card (query_index_list_entries Q) \<le> card Q * rounds"
proof -
  have
    "card (query_index_list_entries Q) \<le> (\<Sum>query_idxs \<in> Q.
      card (set query_idxs))"
    unfolding query_index_list_entries_def
    by (rule card_UN_le) (rule finite_Q)
  also have "... \<le> (\<Sum>query_idxs \<in> Q. rounds)"
  proof (rule sum_mono)
    fix query_idxs
    assume "query_idxs \<in> Q"
    then have "length query_idxs = rounds"
      using subset unfolding fri_query_index_list_space_def by auto
    then show "card (set query_idxs) \<le> rounds"
      using card_length[of query_idxs] by simp
  qed
  also have "... = card Q * rounds"
    using finite_Q by simp
  finally show ?thesis .
qed

definition generic_fri_sampled_query_candidate_evidence
  :: "('f list \<Rightarrow> bool) \<Rightarrow> ('f list \<Rightarrow> bool) \<Rightarrow>
      'f list \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers \<longleftrightarrow>
    generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers \<and>
    candidate_bad candidate_table"

lemma generic_fri_sampled_query_candidate_evidenceI:
  assumes
    "generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
    "candidate_bad candidate_table"
  shows
    "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
  using assms
  unfolding generic_fri_sampled_query_candidate_evidence_def by blast

lemma generic_fri_sampled_query_candidate_evidenceD:
  assumes
    "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
  shows
    "generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
    "candidate_bad candidate_table"
  using assms
  unfolding generic_fri_sampled_query_candidate_evidence_def by blast+

definition generic_fri_sampled_query_bad_pair_set
  :: "('f list \<Rightarrow> bool) \<Rightarrow> ('f list \<Rightarrow> bool) \<Rightarrow>
      'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list \<Rightarrow>
      (nat list \<times> 'f list) set"
where
  "generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
      candidate_table degree_bound roots final_value round_layers layers =
    {(query_idxs, challenges).
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers}"

lemma generic_fri_sampled_query_bad_pair_setI:
  assumes
    "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
  shows
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
        candidate_table degree_bound roots final_value round_layers layers"
  using assms unfolding generic_fri_sampled_query_bad_pair_set_def by simp

lemma generic_fri_sampled_query_bad_pair_setD:
  assumes
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
        candidate_table degree_bound roots final_value round_layers layers"
  shows
    "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
  using assms unfolding generic_fri_sampled_query_bad_pair_set_def by simp

lemma generic_fri_sampled_query_bad_pair_set_canonical_evidence:
  assumes pair:
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
        candidate_table degree_bound roots final_value round_layers layers"
  shows
    "generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
proof -
  have evidence:
    "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
    by (rule generic_fri_sampled_query_bad_pair_setD[OF pair])
  show ?thesis
    by (rule generic_fri_sampled_query_candidate_evidenceD(1)[OF evidence])
qed

lemma generic_fri_sampled_query_bad_pair_set_sampled_evidence:
  assumes pair:
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
        candidate_table degree_bound roots final_value round_layers layers"
  shows
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
proof -
  have canonical:
    "generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
    by (rule generic_fri_sampled_query_bad_pair_set_canonical_evidence
        [OF pair])
  show ?thesis
    by (rule generic_fri_canonical_sampled_layer_chain_evidenceD
        [OF canonical])
qed

lemma generic_fri_sampled_query_bad_pair_set_partial_evidence:
  assumes pair:
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
        candidate_table degree_bound roots final_value round_layers layers"
  shows
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
proof -
  have sampled:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
    by (rule generic_fri_sampled_query_bad_pair_set_sampled_evidence
        [OF pair])
  show ?thesis
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF sampled])
qed

lemma generic_fri_sampled_query_bad_pair_set_challenge_length:
  assumes pair:
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
        candidate_table degree_bound roots final_value round_layers layers"
  shows "length challenges = fri_round_count_for_degree_bound degree_bound"
proof -
  have evidence:
    "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
    by (rule generic_fri_sampled_query_bad_pair_setD[OF pair])
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
  show ?thesis
    using generic_fri_partial_evidence_shapes(1,2)[OF partial] by simp
qed

lemma generic_fri_sampled_query_bad_pair_set_round_layers_length:
  assumes pair:
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
        candidate_table degree_bound roots final_value round_layers layers"
  shows "length round_layers = length query_idxs"
proof -
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_query_bad_pair_set_partial_evidence
        [OF pair])
  have "fri_all_round_layer_evidence roots challenges query_idxs round_layers"
    by (rule generic_fri_partial_evidence_shapes(3)[OF partial])
  then show ?thesis
    unfolding fri_all_round_layer_evidence_def by simp
qed

lemma generic_fri_sampled_query_bad_pair_set_sample:
  assumes pair:
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
        candidate_table degree_bound roots final_value round_layers layers"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
  shows
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      length (layers ! Suc layer_idx)"
    "fri_sampled_table_fold
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (fri_canonical_domains (length challenges) ! layer_idx)
      (layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (layers ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
proof -
  have sampled:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
    by (rule generic_fri_sampled_query_bad_pair_set_sampled_evidence
        [OF pair])
  show "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      length (layers ! Suc layer_idx)"
    by (rule generic_fri_sampled_layer_chain_evidence_sample(1)
        [OF sampled round_bound layer_bound])
  show "fri_sampled_table_fold
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (fri_canonical_domains (length challenges) ! layer_idx)
      (layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (layers ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
    by (rule generic_fri_sampled_layer_chain_evidence_sample(2)
        [OF sampled round_bound layer_bound])
qed

lemma generic_fri_sampled_query_bad_pair_set_candidate_bad:
  assumes pair:
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
        candidate_table degree_bound roots final_value round_layers layers"
  shows "candidate_bad candidate_table"
proof -
  have evidence:
    "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
    by (rule generic_fri_sampled_query_bad_pair_setD[OF pair])
  show ?thesis
    by (rule generic_fri_sampled_query_candidate_evidenceD(2)[OF evidence])
qed

lemma generic_fri_sampled_query_bad_pair_set_challenge_space:
  assumes
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
        candidate_table degree_bound roots final_value round_layers layers"
  shows "challenges \<in>
    fri_challenge_space (fri_round_count_for_degree_bound degree_bound)"
  using generic_fri_sampled_query_bad_pair_set_challenge_length[OF assms]
  unfolding fri_challenge_space_def by simp

lemma generic_fri_sampled_query_bad_pair_set_subset_challenge_space:
  "generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
      candidate_table degree_bound roots final_value round_layers layers
    \<subseteq> (UNIV :: nat list set) \<times>
      fri_challenge_space (fri_round_count_for_degree_bound degree_bound)"
  by (auto intro: generic_fri_sampled_query_bad_pair_set_challenge_space)

definition fri_query_challenge_pair_query_fiber
  :: "(nat list \<times> 'f list) set \<Rightarrow> 'f list \<Rightarrow> nat list set"
where
  "fri_query_challenge_pair_query_fiber P challenges =
    {query_idxs. (query_idxs, challenges) \<in> P}"

lemma finite_fri_query_index_list_space:
  "finite fri_query_index_list_space"
proof -
  have subset:
    "fri_query_index_list_space \<subseteq>
      {query_idxs. set query_idxs \<subseteq> query_sample_space \<and>
        length query_idxs = rounds}"
    unfolding fri_query_index_list_space_def by auto
  have finite_super:
    "finite
      {query_idxs. set query_idxs \<subseteq> query_sample_space \<and>
        length query_idxs = rounds}"
    by (rule finite_lists_length_eq[OF finite_query_sample_space])
  show ?thesis
    by (rule finite_subset[OF subset finite_super])
qed

lemma fri_query_challenge_pair_query_fiber_iff[simp]:
  "query_idxs \<in> fri_query_challenge_pair_query_fiber P challenges \<longleftrightarrow>
    (query_idxs, challenges) \<in> P"
  unfolding fri_query_challenge_pair_query_fiber_def by simp

lemma fri_query_challenge_pair_query_projection_restricted:
  "fst ` (P \<inter> (fri_query_index_list_space \<times> UNIV))
    \<subseteq> fri_query_index_list_space"
proof
  fix query_idxs
  assume "query_idxs \<in>
    fst ` (P \<inter> (fri_query_index_list_space \<times> UNIV))"
  then show "query_idxs \<in> fri_query_index_list_space"
    by auto
qed

lemma finite_fri_query_challenge_pair_query_fiber_restricted:
  "finite
    (fri_query_challenge_pair_query_fiber
      (P \<inter> (fri_query_index_list_space \<times> UNIV)) challenges)"
proof -
  have
    "fri_query_challenge_pair_query_fiber
      (P \<inter> (fri_query_index_list_space \<times> UNIV)) challenges
      \<subseteq> fri_query_index_list_space"
    unfolding fri_query_challenge_pair_query_fiber_def by blast
  then show ?thesis
    by (rule finite_subset) (rule finite_fri_query_index_list_space)
qed

definition trace_fri_query_challenge_pair_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> (nat list \<times> 'f list) set \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_query_challenge_pair_set_hit s P out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      (fri_query_idxs, trace_bs) \<in> P)"

definition composition_fri_query_challenge_pair_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> (nat list \<times> 'f list) set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_query_challenge_pair_set_hit s P out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      (fri_query_idxs, composition_bs) \<in> P fri_dg)"

lemma accepted_fri_opening_transcript_query_index_list_space:
  assumes
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers"
  shows "fri_query_idxs \<in> fri_query_index_list_space"
proof -
  have len: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes[OF assms] by blast
  have subset: "set fri_query_idxs \<subseteq> query_sample_space"
  proof
    fix idx
    assume "idx \<in> set fri_query_idxs"
    then show "idx \<in> query_sample_space"
      by (rule accepted_fri_opening_transcript_query_idx_in_sample_space
          [OF assms])
  qed
  show ?thesis
    unfolding fri_query_index_list_space_def
    using len subset by simp
qed

lemma trace_fri_query_challenge_pair_set_hit_restrict_to_query_space:
  assumes "trace_fri_query_challenge_pair_set_hit s P out"
  shows
    "trace_fri_query_challenge_pair_set_hit s
      (P \<inter> (fri_query_index_list_space \<times> UNIV)) out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers where
    transcript:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and pair: "(fri_query_idxs, trace_bs) \<in> P"
    unfolding trace_fri_query_challenge_pair_set_hit_def by blast
  have query_space: "fri_query_idxs \<in> fri_query_index_list_space"
    by (rule accepted_fri_opening_transcript_query_index_list_space
        [OF transcript])
  show ?thesis
    unfolding trace_fri_query_challenge_pair_set_hit_def
    using transcript pair query_space by blast
qed

lemma composition_fri_query_challenge_pair_set_hit_restrict_to_query_space:
  assumes "composition_fri_query_challenge_pair_set_hit s P out"
  shows
    "composition_fri_query_challenge_pair_set_hit s
      (\<lambda>dg. P dg \<inter> (fri_query_index_list_space \<times> UNIV)) out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers where
    transcript:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and pair: "(fri_query_idxs, composition_bs) \<in> P fri_dg"
    unfolding composition_fri_query_challenge_pair_set_hit_def by blast
  have query_space: "fri_query_idxs \<in> fri_query_index_list_space"
    by (rule accepted_fri_opening_transcript_query_index_list_space
        [OF transcript])
  show ?thesis
    unfolding composition_fri_query_challenge_pair_set_hit_def
    using transcript pair query_space by blast
qed

lemma trace_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit:
  assumes hit: "trace_fri_query_challenge_pair_set_hit s P out"
    and projection: "fst ` P \<subseteq> Q"
  shows "trace_fri_query_index_list_set_hit s Q out"
proof -
  from hit obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers
    where openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and pair: "(fri_query_idxs, trace_bs) \<in> P"
    unfolding trace_fri_query_challenge_pair_set_hit_def by blast
  have "fri_query_idxs \<in> Q"
    using pair projection by force
  then show ?thesis
    unfolding trace_fri_query_index_list_set_hit_def
    using openings by blast
qed

lemma composition_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit:
  assumes hit: "composition_fri_query_challenge_pair_set_hit s P out"
    and projection: "\<And>dg. fst ` P dg \<subseteq> Q"
  shows "composition_fri_query_index_list_set_hit s Q out"
proof -
  from hit obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers
    where openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and pair: "(fri_query_idxs, composition_bs) \<in> P fri_dg"
    unfolding composition_fri_query_challenge_pair_set_hit_def by blast
  have "fri_query_idxs \<in> Q"
    using pair projection[of fri_dg] by force
  then show ?thesis
    unfolding composition_fri_query_index_list_set_hit_def
    using openings by blast
qed

lemma trace_fri_query_challenge_pair_set_hit_imp_challenge_list_set_hit:
  assumes hit: "trace_fri_query_challenge_pair_set_hit s P out"
    and projection: "snd ` P \<subseteq> B"
  shows "trace_fri_challenge_list_set_hit s B out"
proof -
  from hit obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers
    where openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and pair: "(fri_query_idxs, trace_bs) \<in> P"
    unfolding trace_fri_query_challenge_pair_set_hit_def by blast
  have challenges:
    "accepted_fri_challenges s out trace_bs dg composition_bs"
    by (rule accepted_fri_opening_transcript_challenges[OF openings])
  have "trace_bs \<in> B"
    using pair projection by force
  then show ?thesis
    unfolding trace_fri_challenge_list_set_hit_def
    using challenges by blast
qed

lemma composition_fri_query_challenge_pair_set_hit_imp_challenge_list_set_hit:
  assumes hit: "composition_fri_query_challenge_pair_set_hit s P out"
    and projection: "\<And>dg. snd ` P dg \<subseteq> B dg"
  shows "composition_fri_challenge_list_set_hit s B out"
proof -
  from hit obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers
    where openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and pair: "(fri_query_idxs, composition_bs) \<in> P fri_dg"
    unfolding composition_fri_query_challenge_pair_set_hit_def by blast
  have challenges:
    "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
    by (rule accepted_fri_opening_transcript_challenges[OF openings])
  have "composition_bs \<in> B fri_dg"
    using pair projection[of fri_dg] by force
  then show ?thesis
    unfolding composition_fri_challenge_list_set_hit_def
    using challenges by blast
qed

definition trace_fri_sampled_query_pair_set_hit
  :: "('f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list list list \<Rightarrow>
        'f list list \<Rightarrow> (nat list \<times> 'f list) set) \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_query_pair_set_hit R s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      (fri_query_idxs, trace_bs) \<in>
        R trace_table trace_roots trace_final trace_round_layers layers)"

definition composition_fri_sampled_query_pair_set_hit
  :: "('f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
        'f list list list \<Rightarrow> 'f list list \<Rightarrow>
        (nat list \<times> 'f list) set) \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_query_pair_set_hit R s out \<longleftrightarrow>
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
      (fri_query_idxs, composition_bs) \<in>
        R fri_dg composition_table opening_composition_roots composition_final
          composition_round_layers layers)"

lemma trace_fri_sampled_query_pair_set_hit_imp_challenge_list_set_hit:
  assumes hit: "trace_fri_sampled_query_pair_set_hit R s out"
    and projection:
      "\<And>trace_table roots final round_layers layers.
        snd `
          R trace_table roots final round_layers layers \<subseteq> B"
  shows "trace_fri_challenge_list_set_hit s B out"
proof -
  from hit obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and pair:
      "(fri_query_idxs, trace_bs) \<in>
        R trace_table trace_roots trace_final trace_round_layers layers"
    unfolding trace_fri_sampled_query_pair_set_hit_def by blast
  have challenges:
    "accepted_fri_challenges s out trace_bs dg composition_bs"
    by (rule accepted_fri_opening_transcript_challenges)
      (rule trace_fri_partial_candidate_opening_evidenceD(1)[OF evidence])
  have "trace_bs \<in> B"
    using pair projection[of trace_table trace_roots trace_final
        trace_round_layers layers] by force
  then show ?thesis
    unfolding trace_fri_challenge_list_set_hit_def
    using challenges by blast
qed

lemma composition_fri_sampled_query_pair_set_hit_imp_challenge_list_set_hit:
  assumes hit: "composition_fri_sampled_query_pair_set_hit R s out"
    and projection:
      "\<And>fri_dg composition_table roots final round_layers layers.
        snd `
          R fri_dg composition_table roots final round_layers layers
        \<subseteq> B fri_dg"
  shows "composition_fri_challenge_list_set_hit s B out"
proof -
  from hit obtain trace_roots trace_bs trace_final fri_dg
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
    and pair:
      "(fri_query_idxs, composition_bs) \<in>
        R fri_dg composition_table opening_composition_roots
          composition_final composition_round_layers layers"
    unfolding composition_fri_sampled_query_pair_set_hit_def by auto
  have challenges:
    "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
    by (rule accepted_fri_opening_transcript_challenges)
      (rule composition_fri_partial_candidate_opening_evidenceD(1)
        [OF evidence])
  have "composition_bs \<in> B fri_dg"
    using pair projection[of fri_dg composition_table
        opening_composition_roots composition_final composition_round_layers
        layers] by force
  then show ?thesis
  unfolding composition_fri_challenge_list_set_hit_def
    using challenges by blast
qed

lemma trace_fri_sampled_query_pair_set_hit_imp_query_index_list_set_hit:
  assumes hit: "trace_fri_sampled_query_pair_set_hit R s out"
    and projection:
      "\<And>trace_table roots final round_layers layers.
        fst `
          R trace_table roots final round_layers layers \<subseteq> Q"
  shows "trace_fri_query_index_list_set_hit s Q out"
proof -
  from hit obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and pair:
      "(fri_query_idxs, trace_bs) \<in>
        R trace_table trace_roots trace_final trace_round_layers layers"
    unfolding trace_fri_sampled_query_pair_set_hit_def by blast
  have openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    by (rule trace_fri_partial_candidate_opening_evidenceD(1)[OF evidence])
  have "fri_query_idxs \<in> Q"
    using pair projection[of trace_table trace_roots trace_final
        trace_round_layers layers] by force
  then show ?thesis
    unfolding trace_fri_query_index_list_set_hit_def
    using openings by blast
qed

lemma composition_fri_sampled_query_pair_set_hit_imp_query_index_list_set_hit:
  assumes hit: "composition_fri_sampled_query_pair_set_hit R s out"
    and projection:
      "\<And>fri_dg composition_table roots final round_layers layers.
        fst `
          R fri_dg composition_table roots final round_layers layers
        \<subseteq> Q"
  shows "composition_fri_query_index_list_set_hit s Q out"
proof -
  from hit obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as declared_dg composition_fri_roots final_value
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as declared_dg
        composition_fri_roots final_value trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table"
    and pair:
      "(fri_query_idxs, composition_bs) \<in>
        R fri_dg composition_table opening_composition_roots
          composition_final composition_round_layers layers"
    unfolding composition_fri_sampled_query_pair_set_hit_def by auto
  have openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    by (rule composition_fri_partial_candidate_opening_evidenceD(1)
        [OF evidence])
  have "fri_query_idxs \<in> Q"
    using pair projection[of fri_dg composition_table
        opening_composition_roots composition_final composition_round_layers
        layers] by force
  then show ?thesis
    unfolding composition_fri_query_index_list_set_hit_def
    using openings by blast
qed

lemma trace_fri_sampled_query_pair_set_hit_imp_query_challenge_pair_set_hit:
  assumes hit: "trace_fri_sampled_query_pair_set_hit R s out"
    and projection:
      "\<And>trace_table roots final round_layers layers.
        R trace_table roots final round_layers layers \<subseteq> P"
  shows "trace_fri_query_challenge_pair_set_hit s P out"
proof -
  from hit obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and pair:
      "(fri_query_idxs, trace_bs) \<in>
        R trace_table trace_roots trace_final trace_round_layers layers"
    unfolding trace_fri_sampled_query_pair_set_hit_def by blast
  have openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    by (rule trace_fri_partial_candidate_opening_evidenceD(1)[OF evidence])
  have "(fri_query_idxs, trace_bs) \<in> P"
    using pair projection[of trace_table trace_roots trace_final
        trace_round_layers layers] by blast
  then show ?thesis
    unfolding trace_fri_query_challenge_pair_set_hit_def
    using openings by blast
qed

lemma composition_fri_sampled_query_pair_set_hit_imp_query_challenge_pair_set_hit:
  assumes hit: "composition_fri_sampled_query_pair_set_hit R s out"
    and projection:
      "\<And>fri_dg composition_table roots final round_layers layers.
        R fri_dg composition_table roots final round_layers layers
          \<subseteq> P fri_dg"
  shows "composition_fri_query_challenge_pair_set_hit s P out"
proof -
  from hit obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as declared_dg composition_fri_roots final_value
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as declared_dg
        composition_fri_roots final_value trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table"
    and pair:
      "(fri_query_idxs, composition_bs) \<in>
        R fri_dg composition_table opening_composition_roots
          composition_final composition_round_layers layers"
    unfolding composition_fri_sampled_query_pair_set_hit_def by auto
  have openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    by (rule composition_fri_partial_candidate_opening_evidenceD(1)
        [OF evidence])
  have "(fri_query_idxs, composition_bs) \<in> P fri_dg"
    using pair projection[of fri_dg composition_table
        opening_composition_roots composition_final composition_round_layers
        layers] by blast
  then show ?thesis
    unfolding composition_fri_query_challenge_pair_set_hit_def
    using openings by blast
qed

lemma trace_fri_sampled_query_pair_set_hit_imp_query_index_list_space_hit:
  assumes hit: "trace_fri_sampled_query_pair_set_hit R s out"
  shows
    "trace_fri_query_index_list_set_hit s fri_query_index_list_space out"
proof -
  from hit obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    unfolding trace_fri_sampled_query_pair_set_hit_def by blast
  have openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    by (rule trace_fri_partial_candidate_opening_evidenceD(1)[OF evidence])
  have "fri_query_idxs \<in> fri_query_index_list_space"
    by (rule accepted_fri_opening_transcript_query_index_list_space
        [OF openings])
  then show ?thesis
    unfolding trace_fri_query_index_list_set_hit_def
    using openings by blast
qed

lemma composition_fri_sampled_query_pair_set_hit_imp_query_index_list_space_hit:
  assumes hit: "composition_fri_sampled_query_pair_set_hit R s out"
  shows
    "composition_fri_query_index_list_set_hit s fri_query_index_list_space out"
proof -
  from hit obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as declared_dg composition_fri_roots final_value
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as declared_dg
        composition_fri_roots final_value trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table"
    unfolding composition_fri_sampled_query_pair_set_hit_def by auto
  have openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    by (rule composition_fri_partial_candidate_opening_evidenceD(1)
        [OF evidence])
  have "fri_query_idxs \<in> fri_query_index_list_space"
    by (rule accepted_fri_opening_transcript_query_index_list_space
        [OF openings])
  then show ?thesis
    unfolding composition_fri_query_index_list_set_hit_def
    using openings by blast
qed

lemma trace_fri_sampled_query_pair_set_hit_query_indices:
  assumes hit: "trace_fri_sampled_query_pair_set_hit R s out"
  obtains query_idxs challenges candidate_table roots final round_layers layers
  where
    "length query_idxs = rounds"
    "\<forall>idx \<in> set query_idxs. idx \<in> query_sample_space"
    "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    "(query_idxs, challenges) \<in>
      R candidate_table roots final round_layers layers"
proof -
  from hit obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      candidate_table candidate_layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        candidate_table"
    and pair:
      "(fri_query_idxs, trace_bs) \<in>
        R candidate_table trace_roots trace_final trace_round_layers
          candidate_layers"
    unfolding trace_fri_sampled_query_pair_set_hit_def by blast
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    by (rule trace_fri_partial_candidate_opening_evidenceD(1)[OF evidence])
  have len: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes[OF fri_openings] by blast
  have sample_space: "\<forall>idx \<in> set fri_query_idxs. idx \<in> query_sample_space"
  proof
    fix idx
    assume "idx \<in> set fri_query_idxs"
    then show "idx \<in> query_sample_space"
      by (rule accepted_fri_opening_transcript_query_idx_in_sample_space
          [OF fri_openings])
  qed
  have bounds: "\<forall>idx \<in> set fri_query_idxs. idx < clength * scale"
    using fri_openings unfolding accepted_fri_opening_transcript_def
    by blast
  show ?thesis
    by (rule that[OF len sample_space bounds pair])
qed

lemma composition_fri_sampled_query_pair_set_hit_query_indices:
  assumes hit: "composition_fri_sampled_query_pair_set_hit R s out"
  obtains query_idxs challenges dg candidate_table roots final round_layers
      layers
  where
    "length query_idxs = rounds"
    "\<forall>idx \<in> set query_idxs. idx \<in> query_sample_space"
    "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    "(query_idxs, challenges) \<in>
      R dg candidate_table roots final round_layers layers"
proof -
  from hit obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as declared_dg composition_fri_roots final_value
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table candidate_table candidate_layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as declared_dg
        composition_fri_roots final_value trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        candidate_table"
    and pair:
      "(fri_query_idxs, composition_bs) \<in>
        R fri_dg candidate_table opening_composition_roots
          composition_final composition_round_layers candidate_layers"
    unfolding composition_fri_sampled_query_pair_set_hit_def by auto
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    by (rule composition_fri_partial_candidate_opening_evidenceD(1)
        [OF evidence])
  have len: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes[OF fri_openings] by blast
  have sample_space: "\<forall>idx \<in> set fri_query_idxs. idx \<in> query_sample_space"
  proof
    fix idx
    assume "idx \<in> set fri_query_idxs"
    then show "idx \<in> query_sample_space"
      by (rule accepted_fri_opening_transcript_query_idx_in_sample_space
          [OF fri_openings])
  qed
  have bounds: "\<forall>idx \<in> set fri_query_idxs. idx < clength * scale"
    using fri_openings unfolding accepted_fri_opening_transcript_def
    by blast
  show ?thesis
    by (rule that[OF len sample_space bounds pair])
qed

lemma wp_trace_fri_sampled_query_pair_set_hit_bound_from_projection:
  assumes future: "trace_fri_future_fresh s"
    and projection:
      "\<And>trace_table roots final round_layers layers.
        snd `
          R trace_table roots final round_layers layers \<subseteq> B"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_query_pair_set_hit R s) s \<le> C"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_query_pair_set_hit R s) s \<le>
    wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_query_pair_set_hit_imp_challenge_list_set_hit
        [OF _ projection])
  also have "... \<le> nnreal (card B) /
      nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verify_monad_trace_fri_challenge_list_set_bound
        [OF future subset])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_sampled_query_pair_set_hit_bound_from_projection:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and projection:
      "\<And>fri_dg composition_table roots final round_layers layers.
        snd `
          R fri_dg composition_table roots final round_layers layers
        \<subseteq> B fri_dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_query_pair_set_hit R s) s \<le> C"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_query_pair_set_hit R s) s \<le>
    wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_sampled_query_pair_set_hit_imp_challenge_list_set_hit
        [OF _ projection])
  also have "... \<le> C"
    by (rule wp_verify_monad_composition_fri_challenge_list_set_bound
        [OF future subset bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_query_challenge_pair_set_hit_bound_from_challenge_projection:
  assumes future: "trace_fri_future_fresh s"
    and projection: "snd ` P \<subseteq> B"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_query_challenge_pair_set_hit s P) s \<le> C"
proof -
  have "wp_event verify_monad
      (trace_fri_query_challenge_pair_set_hit s P) s \<le>
    wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule trace_fri_query_challenge_pair_set_hit_imp_challenge_list_set_hit
        [OF _ projection])
  also have "... \<le> nnreal (card B) /
      nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verify_monad_trace_fri_challenge_list_set_bound
        [OF future subset])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_query_challenge_pair_set_hit_bound_from_challenge_projection:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and projection: "\<And>dg. snd ` P dg \<subseteq> B dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s P) s \<le> C"
proof -
  have "wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s P) s \<le>
    wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_query_challenge_pair_set_hit_imp_challenge_list_set_hit
        [OF _ projection])
  also have "... \<le> C"
    by (rule wp_verify_monad_composition_fri_challenge_list_set_bound
        [OF future subset bound])
  finally show ?thesis .
qed

definition trace_fri_sampled_query_bad_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_query_bad_candidate s out \<longleftrightarrow>
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
        layers)"

definition composition_fri_sampled_query_bad_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_query_bad_candidate s out \<longleftrightarrow>
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
        composition_final fri_query_idxs composition_round_layers layers)"

definition generic_fri_sampled_query_bad_pair_union
  :: "('f list \<Rightarrow> bool) \<Rightarrow> ('f list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow>
      (nat list \<times> 'f list) set"
where
  "generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
      degree_bound =
    {pair. \<exists>candidate_table roots final round_layers layers.
      pair \<in>
        generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
          candidate_table degree_bound
          roots final round_layers layers}"

definition generic_fri_sampled_query_projection_fraction_bound
  :: "('f list \<Rightarrow> bool) \<Rightarrow> ('f list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow>
      prob \<Rightarrow> bool"
where
  "generic_fri_sampled_query_projection_fraction_bound low_degree
      candidate_bad degree_bound C \<longleftrightarrow>
    nnreal
      (card (snd `
        (generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
          degree_bound \<inter> (fri_query_index_list_space \<times> UNIV)))) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
    \<le> C"

lemma generic_fri_sampled_query_projection_fraction_boundD:
  assumes
    "generic_fri_sampled_query_projection_fraction_bound low_degree
      candidate_bad degree_bound C"
  shows
    "nnreal
      (card (snd `
        (generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
          degree_bound \<inter> (fri_query_index_list_space \<times> UNIV)))) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
    \<le> C"
  using assms
  unfolding generic_fri_sampled_query_projection_fraction_bound_def .

lemma generic_fri_sampled_query_projection_fraction_bound_mono:
  assumes
    "generic_fri_sampled_query_projection_fraction_bound low_degree
      candidate_bad degree_bound C"
    and "C \<le> D"
  shows
    "generic_fri_sampled_query_projection_fraction_bound low_degree
      candidate_bad degree_bound D"
  using assms
  unfolding generic_fri_sampled_query_projection_fraction_bound_def
  by (rule order_trans)

lemma generic_fri_sampled_query_projection_fraction_bound_from_card:
  assumes card_bound:
    "card (snd `
      (generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
        degree_bound \<inter> (fri_query_index_list_space \<times> UNIV))) \<le> K"
    and fraction_bound:
    "nnreal K /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
  shows
    "generic_fri_sampled_query_projection_fraction_bound low_degree
      candidate_bad degree_bound C"
proof -
  have "nnreal
      (card (snd `
        (generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
          degree_bound \<inter> (fri_query_index_list_space \<times> UNIV)))) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le>
      nnreal K /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)"
    using card_bound by (rule nnreal_nat_divide_right_mono)
  also have "... \<le> C"
    by (rule fraction_bound)
  finally show ?thesis
    unfolding generic_fri_sampled_query_projection_fraction_bound_def .
qed

lemma generic_fri_sampled_query_projection_fraction_bound_from_finite_cover:
  assumes cover:
    "snd `
      (generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
        degree_bound \<inter> (fri_query_index_list_space \<times> UNIV)) \<subseteq> B"
    and finite_B: "finite B"
    and fraction_bound:
    "nnreal (card B) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
  shows
    "generic_fri_sampled_query_projection_fraction_bound low_degree
      candidate_bad degree_bound C"
proof (rule generic_fri_sampled_query_projection_fraction_bound_from_card)
  show "card (snd `
      (generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
        degree_bound \<inter> (fri_query_index_list_space \<times> UNIV)))
      \<le> card B"
    by (rule card_mono[OF finite_B cover])
  show "nnreal (card B) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
    by (rule fraction_bound)
qed

definition trace_fri_sampled_query_bad_pair_union
  :: "(nat list \<times> 'f list) set"
where
  "trace_fri_sampled_query_bad_pair_union =
    generic_fri_sampled_query_bad_pair_union trace_table_low_degree
      (Not \<circ> trace_table_low_degree) (clength - 1)"

definition composition_fri_sampled_query_bad_pair_union
  :: "'f \<Rightarrow> (nat list \<times> 'f list) set"
where
  "composition_fri_sampled_query_bad_pair_union fri_dg =
    generic_fri_sampled_query_bad_pair_union
      (composition_table_low_degree (to_nat fri_dg))
      (Not \<circ> composition_table_low_degree maxDegree) (to_nat fri_dg)"

lemma generic_fri_sampled_query_bad_pair_unionI:
  assumes
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
        candidate_table degree_bound roots final round_layers layers"
  shows
    "(query_idxs, challenges) \<in>
      generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
        degree_bound"
  using assms
  unfolding generic_fri_sampled_query_bad_pair_union_def by blast

lemma generic_fri_sampled_query_bad_pair_union_subset_challenge_space:
  "generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
      degree_bound
    \<subseteq> (UNIV :: nat list set) \<times>
      fri_challenge_space (fri_round_count_for_degree_bound degree_bound)"
  unfolding generic_fri_sampled_query_bad_pair_union_def
  by (auto intro: generic_fri_sampled_query_bad_pair_set_challenge_space)

lemma generic_fri_sampled_query_bad_pair_union_challenge_projection:
  "snd `
    generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
      degree_bound
    \<subseteq> fri_challenge_space
      (fri_round_count_for_degree_bound degree_bound)"
  using generic_fri_sampled_query_bad_pair_union_subset_challenge_space
    [of low_degree candidate_bad degree_bound]
  by force

text \<open>
  Fallback sanity bound: the restricted projection is always a subset of the
  full challenge space.  This lemma is intentionally not the main FRI
  low-degree theorem; the useful symbolic bounds must come from a sharper
  sampled-query FRI argument.
\<close>

lemma generic_fri_sampled_query_projection_fraction_bound_trivial:
  "generic_fri_sampled_query_projection_fraction_bound low_degree
      candidate_bad degree_bound 1"
proof -
  let ?S =
    "snd `
      (generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
        degree_bound \<inter> (fri_query_index_list_space \<times> UNIV))"
  let ?N = "CARD('f) ^ fri_round_count_for_degree_bound degree_bound"
  have subset:
    "?S \<subseteq> fri_challenge_space
      (fri_round_count_for_degree_bound degree_bound)"
    using generic_fri_sampled_query_bad_pair_union_challenge_projection
      [of low_degree candidate_bad degree_bound]
    by blast
  have card_le: "card ?S \<le> ?N"
    using card_mono[OF finite_fri_challenge_space subset]
    by (simp add: card_fri_challenge_space)
  have "?N \<noteq> 0"
    by simp
  then have "nnreal ?N / nnreal ?N = (1::prob)"
    by (rule nnreal_nat_divide_self)
  moreover have "nnreal (card ?S) / nnreal ?N \<le> nnreal ?N / nnreal ?N"
    using card_le by (rule nnreal_nat_divide_right_mono)
  ultimately show ?thesis
    unfolding generic_fri_sampled_query_projection_fraction_bound_def
    by simp
qed

lemma trace_fri_sampled_query_bad_pair_union_challenge_projection:
  "snd ` trace_fri_sampled_query_bad_pair_union \<subseteq>
    fri_challenge_space (ceil_log clength)"
  unfolding trace_fri_sampled_query_bad_pair_union_def
  using generic_fri_sampled_query_bad_pair_union_challenge_projection
    [of trace_table_low_degree "Not \<circ> trace_table_low_degree"
      "clength - 1"]
  by (simp add: fri_round_count_for_degree_bound_def clength_pos)

lemma composition_fri_sampled_query_bad_pair_union_challenge_projection:
  "snd ` composition_fri_sampled_query_bad_pair_union fri_dg \<subseteq>
    fri_challenge_space (ceil_log (to_nat fri_dg + 1))"
  unfolding composition_fri_sampled_query_bad_pair_union_def
  using generic_fri_sampled_query_bad_pair_union_challenge_projection
    [of "composition_table_low_degree (to_nat fri_dg)"
      "Not \<circ> composition_table_low_degree maxDegree" "to_nat fri_dg"]
  by (simp add: fri_round_count_for_degree_bound_def)

lemma trace_fri_restricted_sampled_query_bad_pair_union_challenge_projection:
  "snd `
    (trace_fri_sampled_query_bad_pair_union \<inter>
      (fri_query_index_list_space \<times> UNIV))
    \<subseteq> fri_challenge_space (ceil_log clength)"
  using trace_fri_sampled_query_bad_pair_union_challenge_projection by blast

lemma composition_fri_restricted_sampled_query_bad_pair_union_challenge_projection:
  "snd `
    (composition_fri_sampled_query_bad_pair_union fri_dg \<inter>
      (fri_query_index_list_space \<times> UNIV))
    \<subseteq> fri_challenge_space (ceil_log (to_nat fri_dg + 1))"
  using composition_fri_sampled_query_bad_pair_union_challenge_projection
    [of fri_dg]
  by blast

lemma trace_fri_sampled_query_bad_candidate_iff_pair_set_hit:
  "trace_fri_sampled_query_bad_candidate s out \<longleftrightarrow>
    trace_fri_sampled_query_pair_set_hit
      (\<lambda>trace_table roots final round_layers layers.
        generic_fri_sampled_query_bad_pair_set trace_table_low_degree
          (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
          roots final round_layers layers)
      s out"
  unfolding trace_fri_sampled_query_bad_candidate_def
    trace_fri_sampled_query_pair_set_hit_def
    generic_fri_sampled_query_bad_pair_set_def
  by blast

lemma composition_fri_sampled_query_bad_candidate_iff_pair_set_hit:
  "composition_fri_sampled_query_bad_candidate s out \<longleftrightarrow>
    composition_fri_sampled_query_pair_set_hit
      (\<lambda>fri_dg composition_table roots final round_layers layers.
        generic_fri_sampled_query_bad_pair_set
          (composition_table_low_degree (to_nat fri_dg))
          (Not \<circ> composition_table_low_degree maxDegree)
          composition_table (to_nat fri_dg) roots final round_layers layers)
      s out"
  unfolding composition_fri_sampled_query_bad_candidate_def
    composition_fri_sampled_query_pair_set_hit_def
    generic_fri_sampled_query_bad_pair_set_def
  by auto

lemma trace_fri_sampled_query_bad_candidate_imp_query_challenge_pair_union_hit:
  assumes "trace_fri_sampled_query_bad_candidate s out"
  shows
    "trace_fri_query_challenge_pair_set_hit s
      trace_fri_sampled_query_bad_pair_union out"
proof -
  have hit:
    "trace_fri_sampled_query_pair_set_hit
      (\<lambda>trace_table roots final round_layers layers.
        generic_fri_sampled_query_bad_pair_set trace_table_low_degree
          (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
          roots final round_layers layers)
      s out"
    using assms trace_fri_sampled_query_bad_candidate_iff_pair_set_hit
    by blast
  show ?thesis
  proof (rule trace_fri_sampled_query_pair_set_hit_imp_query_challenge_pair_set_hit
      [OF hit])
    fix trace_table roots final round_layers layers
    show
      "generic_fri_sampled_query_bad_pair_set trace_table_low_degree
        (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
        roots final round_layers layers
      \<subseteq> trace_fri_sampled_query_bad_pair_union"
      unfolding trace_fri_sampled_query_bad_pair_union_def
      by (auto intro: generic_fri_sampled_query_bad_pair_unionI)
  qed
qed

lemma composition_fri_sampled_query_bad_candidate_imp_query_challenge_pair_union_hit:
  assumes "composition_fri_sampled_query_bad_candidate s out"
  shows
    "composition_fri_query_challenge_pair_set_hit s
      composition_fri_sampled_query_bad_pair_union out"
proof -
  have hit:
    "composition_fri_sampled_query_pair_set_hit
      (\<lambda>fri_dg composition_table roots final round_layers layers.
        generic_fri_sampled_query_bad_pair_set
          (composition_table_low_degree (to_nat fri_dg))
          (Not \<circ> composition_table_low_degree maxDegree)
          composition_table (to_nat fri_dg) roots final round_layers
          layers)
      s out"
    using assms composition_fri_sampled_query_bad_candidate_iff_pair_set_hit
    by blast
  show ?thesis
  proof (rule
      composition_fri_sampled_query_pair_set_hit_imp_query_challenge_pair_set_hit
      [OF hit])
    fix fri_dg composition_table roots final round_layers layers
    show
      "generic_fri_sampled_query_bad_pair_set
        (composition_table_low_degree (to_nat fri_dg))
        (Not \<circ> composition_table_low_degree maxDegree)
        composition_table (to_nat fri_dg) roots final round_layers layers
      \<subseteq> composition_fri_sampled_query_bad_pair_union fri_dg"
      unfolding composition_fri_sampled_query_bad_pair_union_def
      by (auto intro: generic_fri_sampled_query_bad_pair_unionI)
  qed
qed

lemma trace_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit:
  assumes "trace_fri_sampled_query_bad_candidate s out"
  shows
    "trace_fri_query_challenge_pair_set_hit s
      (trace_fri_sampled_query_bad_pair_union \<inter>
        (fri_query_index_list_space \<times> UNIV)) out"
  by (rule trace_fri_query_challenge_pair_set_hit_restrict_to_query_space)
    (rule
      trace_fri_sampled_query_bad_candidate_imp_query_challenge_pair_union_hit
      [OF assms])

lemma composition_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit:
  assumes "composition_fri_sampled_query_bad_candidate s out"
  shows
    "composition_fri_query_challenge_pair_set_hit s
      (\<lambda>dg. composition_fri_sampled_query_bad_pair_union dg \<inter>
        (fri_query_index_list_space \<times> UNIV)) out"
  by (rule composition_fri_query_challenge_pair_set_hit_restrict_to_query_space)
    (rule
      composition_fri_sampled_query_bad_candidate_imp_query_challenge_pair_union_hit
      [OF assms])

lemma wp_trace_fri_sampled_query_bad_candidate_iff_pair_set_hit:
  "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s =
    wp_event verify_monad
      (trace_fri_sampled_query_pair_set_hit
        (\<lambda>trace_table roots final round_layers layers.
          generic_fri_sampled_query_bad_pair_set trace_table_low_degree
            (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
            roots final round_layers layers)
        s) s"
proof (rule antisym)
  show "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> wp_event verify_monad
        (trace_fri_sampled_query_pair_set_hit
          (\<lambda>trace_table roots final round_layers layers.
            generic_fri_sampled_query_bad_pair_set trace_table_low_degree
              (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
              roots final round_layers layers)
          s) s"
    by (rule wp_event_mono)
      (use trace_fri_sampled_query_bad_candidate_iff_pair_set_hit in blast)
  show "wp_event verify_monad
        (trace_fri_sampled_query_pair_set_hit
          (\<lambda>trace_table roots final round_layers layers.
            generic_fri_sampled_query_bad_pair_set trace_table_low_degree
              (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
              roots final round_layers layers)
          s) s
      \<le> wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s"
    by (rule wp_event_mono)
      (use trace_fri_sampled_query_bad_candidate_iff_pair_set_hit in blast)
qed

lemma wp_composition_fri_sampled_query_bad_candidate_iff_pair_set_hit:
  "wp_event verify_monad
      (composition_fri_sampled_query_bad_candidate s) s =
    wp_event verify_monad
      (composition_fri_sampled_query_pair_set_hit
        (\<lambda>fri_dg composition_table roots final round_layers layers.
          generic_fri_sampled_query_bad_pair_set
            (composition_table_low_degree (to_nat fri_dg))
            (Not \<circ> composition_table_low_degree maxDegree)
            composition_table (to_nat fri_dg) roots final round_layers
            layers)
        s) s"
proof (rule antisym)
  show "wp_event verify_monad
        (composition_fri_sampled_query_bad_candidate s) s
      \<le> wp_event verify_monad
        (composition_fri_sampled_query_pair_set_hit
          (\<lambda>fri_dg composition_table roots final round_layers layers.
            generic_fri_sampled_query_bad_pair_set
              (composition_table_low_degree (to_nat fri_dg))
              (Not \<circ> composition_table_low_degree maxDegree)
              composition_table (to_nat fri_dg) roots final round_layers
              layers)
          s) s"
    by (rule wp_event_mono)
      (use composition_fri_sampled_query_bad_candidate_iff_pair_set_hit
        in blast)
  show "wp_event verify_monad
        (composition_fri_sampled_query_pair_set_hit
          (\<lambda>fri_dg composition_table roots final round_layers layers.
            generic_fri_sampled_query_bad_pair_set
              (composition_table_low_degree (to_nat fri_dg))
              (Not \<circ> composition_table_low_degree maxDegree)
              composition_table (to_nat fri_dg) roots final round_layers
              layers)
          s) s
      \<le> wp_event verify_monad
        (composition_fri_sampled_query_bad_candidate s) s"
    by (rule wp_event_mono)
      (use composition_fri_sampled_query_bad_candidate_iff_pair_set_hit
        in blast)
qed

lemma wp_trace_fri_sampled_query_bad_candidate_bound_by_query_challenge_union_hit:
  "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s \<le>
    wp_event verify_monad
      (trace_fri_query_challenge_pair_set_hit s
        trace_fri_sampled_query_bad_pair_union) s"
  by (rule wp_event_mono)
    (rule
      trace_fri_sampled_query_bad_candidate_imp_query_challenge_pair_union_hit)

lemma wp_composition_fri_sampled_query_bad_candidate_bound_by_query_challenge_union_hit:
  "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s \<le>
    wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s
        composition_fri_sampled_query_bad_pair_union) s"
  by (rule wp_event_mono)
    (rule
      composition_fri_sampled_query_bad_candidate_imp_query_challenge_pair_union_hit)

lemma wp_trace_fri_sampled_query_bad_candidate_bound_by_restricted_query_challenge_union_hit:
  "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s \<le>
    wp_event verify_monad
      (trace_fri_query_challenge_pair_set_hit s
        (trace_fri_sampled_query_bad_pair_union \<inter>
          (fri_query_index_list_space \<times> UNIV))) s"
  by (rule wp_event_mono)
    (rule
      trace_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit)

lemma wp_composition_fri_sampled_query_bad_candidate_bound_by_restricted_query_challenge_union_hit:
  "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s \<le>
    wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s
        (\<lambda>dg. composition_fri_sampled_query_bad_pair_union dg \<inter>
          (fri_query_index_list_space \<times> UNIV))) s"
  by (rule wp_event_mono)
    (rule
      composition_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit)

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_bad_pair_union_projection:
  assumes future: "trace_fri_future_fresh s"
    and bound:
      "nnreal (card (snd ` trace_fri_sampled_query_bad_pair_union)) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s \<le> C"
proof -
  have "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> wp_event verify_monad
        (trace_fri_query_challenge_pair_set_hit s
          trace_fri_sampled_query_bad_pair_union) s"
    by (rule
        wp_trace_fri_sampled_query_bad_candidate_bound_by_query_challenge_union_hit)
  also have "... \<le> C"
    by (rule wp_trace_fri_query_challenge_pair_set_hit_bound_from_challenge_projection
        [OF future subset_refl
          trace_fri_sampled_query_bad_pair_union_challenge_projection
          bound])
  finally show ?thesis .
qed

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_bad_pair_union_projection:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and bound:
      "\<And>dg. nnreal
          (card (snd ` composition_fri_sampled_query_bad_pair_union dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> C"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_query_bad_candidate s) s \<le>
    wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s
        composition_fri_sampled_query_bad_pair_union) s"
    by (rule
        wp_composition_fri_sampled_query_bad_candidate_bound_by_query_challenge_union_hit)
  also have "... \<le> C"
    by (rule
        wp_composition_fri_query_challenge_pair_set_hit_bound_from_challenge_projection
        [OF future subset_refl
          composition_fri_sampled_query_bad_pair_union_challenge_projection
          bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_restricted_bad_pair_union_projection:
  assumes future: "trace_fri_future_fresh s"
    and bound:
      "nnreal
        (card (snd `
          (trace_fri_sampled_query_bad_pair_union \<inter>
            (fri_query_index_list_space \<times> UNIV)))) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s \<le> C"
proof -
  have "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> wp_event verify_monad
        (trace_fri_query_challenge_pair_set_hit s
          (trace_fri_sampled_query_bad_pair_union \<inter>
            (fri_query_index_list_space \<times> UNIV))) s"
    by (rule
        wp_trace_fri_sampled_query_bad_candidate_bound_by_restricted_query_challenge_union_hit)
  also have "... \<le> C"
    by (rule wp_trace_fri_query_challenge_pair_set_hit_bound_from_challenge_projection
        [OF future subset_refl
          trace_fri_restricted_sampled_query_bad_pair_union_challenge_projection
          bound])
  finally show ?thesis .
qed

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_restricted_bad_pair_union_projection:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and bound:
      "\<And>dg. nnreal
          (card (snd `
            (composition_fri_sampled_query_bad_pair_union dg \<inter>
              (fri_query_index_list_space \<times> UNIV)))) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> C"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_query_bad_candidate s) s \<le>
    wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s
        (\<lambda>dg. composition_fri_sampled_query_bad_pair_union dg \<inter>
          (fri_query_index_list_space \<times> UNIV))) s"
    by (rule
        wp_composition_fri_sampled_query_bad_candidate_bound_by_restricted_query_challenge_union_hit)
  also have "... \<le> C"
    by (rule
        wp_composition_fri_query_challenge_pair_set_hit_bound_from_challenge_projection
        [OF future subset_refl
          composition_fri_restricted_sampled_query_bad_pair_union_challenge_projection
          bound])
  finally show ?thesis .
qed

lemma trace_fri_sampled_query_bad_pair_union_generic_projection_fraction_bound:
  assumes
    "generic_fri_sampled_query_projection_fraction_bound
      trace_table_low_degree (Not \<circ> trace_table_low_degree) (clength - 1) C"
  shows
    "nnreal
      (card (snd `
        (trace_fri_sampled_query_bad_pair_union \<inter>
          (fri_query_index_list_space \<times> UNIV)))) /
      nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  using assms
  unfolding generic_fri_sampled_query_projection_fraction_bound_def
    trace_fri_sampled_query_bad_pair_union_def
  by (simp add: fri_round_count_for_degree_bound_def clength_pos)

lemma composition_fri_sampled_query_bad_pair_union_generic_projection_fraction_bound:
  assumes
    "generic_fri_sampled_query_projection_fraction_bound
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg) C"
  shows
    "nnreal
      (card (snd `
        (composition_fri_sampled_query_bad_pair_union dg \<inter>
          (fri_query_index_list_space \<times> UNIV)))) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  using assms
  unfolding generic_fri_sampled_query_projection_fraction_bound_def
    composition_fri_sampled_query_bad_pair_union_def
  by (simp add: fri_round_count_for_degree_bound_def)

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_generic_projection_fraction:
  assumes future: "trace_fri_future_fresh s"
    and generic_bound:
      "generic_fri_sampled_query_projection_fraction_bound
        trace_table_low_degree (Not \<circ> trace_table_low_degree)
        (clength - 1) C"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s \<le> C"
  by (rule
      wp_trace_fri_sampled_query_bad_candidate_bound_from_restricted_bad_pair_union_projection
      [OF future])
    (rule
      trace_fri_sampled_query_bad_pair_union_generic_projection_fraction_bound
      [OF generic_bound])

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_generic_projection_fraction:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and generic_bound:
      "\<And>dg. generic_fri_sampled_query_projection_fraction_bound
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg) C"
  shows
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> C"
  by (rule
      wp_composition_fri_sampled_query_bad_candidate_bound_from_restricted_bad_pair_union_projection
      [OF future])
    (rule
      composition_fri_sampled_query_bad_pair_union_generic_projection_fraction_bound
      [OF generic_bound])

lemma trace_fri_sampled_query_bad_candidate_imp_query_index_list_space_hit:
  assumes "trace_fri_sampled_query_bad_candidate s out"
  shows
    "trace_fri_query_index_list_set_hit s fri_query_index_list_space out"
  using assms trace_fri_sampled_query_bad_candidate_iff_pair_set_hit
    trace_fri_sampled_query_pair_set_hit_imp_query_index_list_space_hit
  by blast

lemma composition_fri_sampled_query_bad_candidate_imp_query_index_list_space_hit:
  assumes "composition_fri_sampled_query_bad_candidate s out"
  shows
    "composition_fri_query_index_list_set_hit s fri_query_index_list_space out"
  using assms composition_fri_sampled_query_bad_candidate_iff_pair_set_hit
    composition_fri_sampled_query_pair_set_hit_imp_query_index_list_space_hit
  by blast

lemma wp_trace_fri_sampled_query_bad_candidate_bound_by_query_index_space_hit:
  "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s \<le>
    wp_event verify_monad
      (trace_fri_query_index_list_set_hit s fri_query_index_list_space) s"
  by (rule wp_event_mono)
    (rule trace_fri_sampled_query_bad_candidate_imp_query_index_list_space_hit)

lemma wp_composition_fri_sampled_query_bad_candidate_bound_by_query_index_space_hit:
  "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s \<le>
    wp_event verify_monad
      (composition_fri_query_index_list_set_hit s fri_query_index_list_space) s"
  by (rule wp_event_mono)
    (rule
      composition_fri_sampled_query_bad_candidate_imp_query_index_list_space_hit)

lemma trace_fri_sampled_query_bad_candidate_iff_canonical:
  "trace_fri_sampled_query_bad_candidate s out \<longleftrightarrow>
    trace_fri_bad_with_canonical_sampled_layer_chain s out"
proof
  assume "trace_fri_sampled_query_bad_candidate s out"
  then show "trace_fri_bad_with_canonical_sampled_layer_chain s out"
    unfolding trace_fri_sampled_query_bad_candidate_def
      trace_fri_bad_with_canonical_sampled_layer_chain_def
      generic_fri_sampled_query_candidate_evidence_def
    by blast
next
  assume canonical: "trace_fri_bad_with_canonical_sampled_layer_chain s out"
  then obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and sampled:
      "generic_fri_canonical_sampled_layer_chain_evidence
        trace_table_low_degree trace_table (clength - 1) trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers layers"
    unfolding trace_fri_bad_with_canonical_sampled_layer_chain_def by blast
  have not_low: "(Not \<circ> trace_table_low_degree) trace_table"
    using trace_fri_partial_candidate_opening_evidenceD(2)[OF evidence]
    by (simp add: o_def trace_fri_partial_candidate_evidenceD(3))
  have bad:
    "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
      (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
      trace_roots trace_bs trace_final fri_query_idxs trace_round_layers
      layers"
    using sampled not_low
    unfolding generic_fri_sampled_query_candidate_evidence_def by blast
  show "trace_fri_sampled_query_bad_candidate s out"
    unfolding trace_fri_sampled_query_bad_candidate_def
    by (intro exI conjI) (rule evidence, rule bad)
qed

lemma composition_fri_partial_candidate_opening_evidence_candidate_bad:
  assumes
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
  shows "(Not \<circ> composition_table_low_degree maxDegree) composition_table"
  using composition_fri_partial_candidate_opening_evidenceD(2)[OF assms]
  by (simp add: o_def composition_fri_partial_candidate_evidenceD(5))

lemma composition_fri_sampled_query_bad_candidate_iff_canonical:
  "composition_fri_sampled_query_bad_candidate s out \<longleftrightarrow>
    composition_fri_bad_with_canonical_sampled_layer_chain s out"
proof (rule iffI)
  assume "composition_fri_sampled_query_bad_candidate s out"
  then show "composition_fri_bad_with_canonical_sampled_layer_chain s out"
    unfolding composition_fri_sampled_query_bad_candidate_def
      composition_fri_bad_with_canonical_sampled_layer_chain_def
      generic_fri_sampled_query_candidate_evidence_def
    apply (elim exE conjE)
    apply (intro exI conjI)
     apply assumption
    apply assumption
    done
next
  assume "composition_fri_bad_with_canonical_sampled_layer_chain s out"
  then show "composition_fri_sampled_query_bad_candidate s out"
    unfolding composition_fri_sampled_query_bad_candidate_def
      composition_fri_bad_with_canonical_sampled_layer_chain_def
      generic_fri_sampled_query_candidate_evidence_def
    using composition_fri_partial_candidate_opening_evidence_candidate_bad
    apply (elim exE conjE)
    apply (intro exI conjI)
      apply assumption
     apply assumption
    apply (rule composition_fri_partial_candidate_opening_evidence_candidate_bad)
    apply assumption
    done
qed

lemma wp_trace_fri_sampled_query_bad_candidate_iff_canonical:
  "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s =
    wp_event verify_monad (trace_fri_bad_with_canonical_sampled_layer_chain s)
      s"
proof (rule antisym)
  show "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
    \<le> wp_event verify_monad
      (trace_fri_bad_with_canonical_sampled_layer_chain s) s"
    by (rule wp_event_mono)
      (use trace_fri_sampled_query_bad_candidate_iff_canonical in blast)
  show "wp_event verify_monad
      (trace_fri_bad_with_canonical_sampled_layer_chain s) s
    \<le> wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s"
    by (rule wp_event_mono)
      (use trace_fri_sampled_query_bad_candidate_iff_canonical in blast)
qed

lemma wp_composition_fri_sampled_query_bad_candidate_iff_canonical:
  "wp_event verify_monad
      (composition_fri_sampled_query_bad_candidate s) s =
    wp_event verify_monad
      (composition_fri_bad_with_canonical_sampled_layer_chain s) s"
proof (rule antisym)
  show "wp_event verify_monad
      (composition_fri_sampled_query_bad_candidate s) s
    \<le> wp_event verify_monad
      (composition_fri_bad_with_canonical_sampled_layer_chain s) s"
    by (rule wp_event_mono)
      (use composition_fri_sampled_query_bad_candidate_iff_canonical in blast)
  show "wp_event verify_monad
      (composition_fri_bad_with_canonical_sampled_layer_chain s) s
    \<le> wp_event verify_monad
      (composition_fri_sampled_query_bad_candidate s) s"
    by (rule wp_event_mono)
      (use composition_fri_sampled_query_bad_candidate_iff_canonical in blast)
qed

text \<open>
  The following bounds expose the current internal sampled-FRI interface:
  a sampled layer-chain cover plus a bad-set envelope implies a challenge-list
  hit, which is then bounded by the existing Fiat-Shamir challenge-list
  calculus.  The cover and envelope parameters are internal proof-layer
  interfaces; they are not public protocol assumptions.
\<close>

lemma trace_fri_sampled_query_bad_candidate_imp_list_hit:
  assumes sampled: "trace_fri_sampled_query_bad_candidate s out"
    and cover: "trace_fri_sampled_layer_chain_cover s bad"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
  shows "trace_fri_challenge_list_set_hit s B out"
proof -
  have canonical: "trace_fri_bad_with_canonical_sampled_layer_chain s out"
    using sampled trace_fri_sampled_query_bad_candidate_iff_canonical
    by blast
  then have sampled_chain: "trace_fri_bad_with_sampled_layer_chain s out"
    by (rule trace_fri_bad_with_canonical_sampled_layer_chain_imp_sampled)
  show ?thesis
    by (rule trace_fri_bad_with_sampled_layer_chain_imp_list_hit
        [OF sampled_chain cover envelope])
qed

lemma composition_fri_sampled_query_bad_candidate_imp_list_hit:
  assumes sampled: "composition_fri_sampled_query_bad_candidate s out"
    and cover: "composition_fri_sampled_layer_chain_cover s bad"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
  shows "composition_fri_challenge_list_set_hit s B out"
proof -
  have canonical:
    "composition_fri_bad_with_canonical_sampled_layer_chain s out"
    using sampled composition_fri_sampled_query_bad_candidate_iff_canonical
    by blast
  then have sampled_chain:
    "composition_fri_bad_with_sampled_layer_chain s out"
    by (rule composition_fri_bad_with_canonical_sampled_layer_chain_imp_sampled)
  show ?thesis
    by (rule composition_fri_bad_with_sampled_layer_chain_imp_list_hit
        [OF sampled_chain cover envelope])
qed

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_envelope:
  assumes future: "trace_fri_future_fresh s"
    and cover: "trace_fri_sampled_layer_chain_cover s bad"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s \<le> C"
proof -
  have "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_query_bad_candidate_imp_list_hit
        [OF _ cover envelope])
  also have "... \<le> nnreal (card B) /
      nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verify_monad_trace_fri_challenge_list_set_bound
        [OF future subset])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_envelope:
  assumes future: "composition_fri_future_fresh s"
    and cover: "composition_fri_sampled_layer_chain_cover s bad"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> C"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_query_bad_candidate s) s \<le>
    wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule composition_fri_sampled_query_bad_candidate_imp_list_hit
        [OF _ cover envelope])
  also have "... \<le> C"
    by (rule wp_verify_monad_composition_fri_challenge_list_set_bound
        [OF future subset bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_sampled_query_bad_candidate_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_set_hit s B))
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
      "staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate out"
    from hit obtain data attacker_state result final_state where
      out_eq: "out = Some (((data, attacker_state), result), final_state)"
      unfolding staged_security_with_data_state_verifier_event_def
      by (cases out) (auto split: option.splits prod.splits)
    have builder:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
      using checked_staged_security_experiment_with_data_state_outcomeE
        [OF support[unfolded out_eq]]
      by blast
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    have sampled:
      "trace_fri_sampled_query_bad_candidate ?s
        (Some (result, final_state))"
      using hit unfolding staged_security_with_data_state_verifier_event_def
        out_eq by simp
    have list_hit:
      "trace_fri_challenge_list_set_hit ?s B (Some (result, final_state))"
      by (rule trace_fri_sampled_query_bad_candidate_imp_list_hit
          [OF sampled cover[OF builder]])
        (rule envelope[OF builder])
    show
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_set_hit s B) out"
      unfolding staged_security_with_data_state_verifier_event_def out_eq
      using list_hit by simp
  qed
  also have "... \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule checked_staged_security_trace_fri_challenge_list_set_hit_bound
        [OF wf controlled finite_B fresh_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_sampled_query_bad_candidate_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) bad"
    and envelope:
    "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets bad dg composition_table
        \<subseteq> B dg"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_challenge_list_set_hit s B))
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
      "staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate out"
    from hit obtain data attacker_state result final_state where
      out_eq: "out = Some (((data, attacker_state), result), final_state)"
      unfolding staged_security_with_data_state_verifier_event_def
      by (cases out) (auto split: option.splits prod.splits)
    have builder:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
      using checked_staged_security_experiment_with_data_state_outcomeE
        [OF support[unfolded out_eq]]
      by blast
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    have sampled:
      "composition_fri_sampled_query_bad_candidate ?s
        (Some (result, final_state))"
      using hit unfolding staged_security_with_data_state_verifier_event_def
        out_eq by simp
    have list_hit:
      "composition_fri_challenge_list_set_hit ?s B
        (Some (result, final_state))"
      by (rule composition_fri_sampled_query_bad_candidate_imp_list_hit
          [OF sampled cover[OF builder]])
        (rule envelope[OF builder])
    show
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_set_hit s B) out"
      unfolding staged_security_with_data_state_verifier_event_def out_eq
      using list_hit by simp
  qed
  also have "... \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule checked_staged_security_composition_fri_challenge_list_set_hit_bound
        [OF wf controlled finite_B fresh_bound])
  finally show ?thesis .
qed

lemma active_fri_reductions_for_from_trace_augmented_composition_sampled_query_and_empty_conflict_zero:
  fixes TraceAug TraceMissing TraceMerkle CompSampled CompMerkle EmptySampled EmptyConflict EmptyZero ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes trace_augmented_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_augmented_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceAug data attacker_state"
    and trace_missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      TraceMissing data attacker_state"
    and trace_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceMerkle data attacker_state"
    and trace_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      TraceAug data attacker_state +
        (TraceMissing data attacker_state + TraceMerkle data attacker_state)
      \<le> trace_fri_error"
    and composition_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_query_bad_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      CompSampled data attacker_state"
    and composition_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> CompMerkle data attacker_state"
    and composition_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      CompSampled data attacker_state +
        (((CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0 + 0) +
          CompMerkle data attacker_state) + 0)
      \<le> composition_fri_error"
    and empty_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_query_bad_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptySampled data attacker_state"
    and empty_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyConflict data attacker_state"
    and empty_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyZero data attacker_state"
    and empty_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      EmptySampled data attacker_state +
        (EmptyConflict data attacker_state + EmptyZero data attacker_state)
      \<le> trace_fri_error"
  shows "active_fri_reductions_for A"
proof (rule
    active_fri_reductions_for_from_trace_augmented_composition_canonical_and_empty_conflict_zero
    [OF trace_augmented_bound trace_missing_bound trace_merkle_bound
      trace_total _ composition_merkle_bound composition_total _
      empty_conflict_bound empty_zero_bound empty_total])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (composition_fri_bad_with_canonical_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> CompSampled data attacker_state"
    using composition_sampled_bound[OF support]
    by (simp add: wp_composition_fri_sampled_query_bad_candidate_iff_canonical)
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (trace_fri_bad_with_canonical_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> EmptySampled data attacker_state"
    using empty_sampled_bound[OF support]
    by (simp add: wp_trace_fri_sampled_query_bad_candidate_iff_canonical)
qed

definition generic_fri_sampled_query_finite_cover
  :: "('f list \<Rightarrow> bool) \<Rightarrow> ('f list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow>
      'f list set \<Rightarrow> bool"
where
  "generic_fri_sampled_query_finite_cover low_degree candidate_bad
      degree_bound B \<longleftrightarrow>
    finite B \<and>
    snd `
      (generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
        degree_bound \<inter> (fri_query_index_list_space \<times> UNIV)) \<subseteq> B"

lemma generic_fri_sampled_query_finite_coverD:
  assumes
    "generic_fri_sampled_query_finite_cover low_degree candidate_bad
      degree_bound B"
  shows
    "finite B"
    "snd `
      (generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
        degree_bound \<inter> (fri_query_index_list_space \<times> UNIV)) \<subseteq> B"
  using assms
  unfolding generic_fri_sampled_query_finite_cover_def by simp_all

lemma generic_fri_sampled_query_finite_cover_from_candidate_challenge_cover:
  assumes finite_B: "finite B"
    and cover:
    "\<And>candidate_table roots final_value round_layers layers query_idxs
        challenges.
      query_idxs \<in> fri_query_index_list_space \<Longrightarrow>
      generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers \<Longrightarrow>
      challenges \<in> B"
  shows
    "generic_fri_sampled_query_finite_cover low_degree candidate_bad
      degree_bound B"
proof -
  have subset:
    "snd `
      (generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
        degree_bound \<inter> (fri_query_index_list_space \<times> UNIV)) \<subseteq> B"
  proof
    fix challenges
    assume "challenges \<in> snd `
      (generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
        degree_bound \<inter> (fri_query_index_list_space \<times> UNIV))"
    then obtain pair where pair_mem:
        "pair \<in> generic_fri_sampled_query_bad_pair_union low_degree
          candidate_bad degree_bound \<inter> (fri_query_index_list_space \<times> UNIV)"
      and challenges_eq: "challenges = snd pair"
      by blast
    obtain query_idxs challenges' where pair_eq: "pair = (query_idxs, challenges')"
      by (cases pair)
    from pair_mem pair_eq challenges_eq
    obtain candidate_table roots final_value round_layers layers
      where query_space: "query_idxs \<in> fri_query_index_list_space"
        and pair:
        "(query_idxs, challenges) \<in>
          generic_fri_sampled_query_bad_pair_set low_degree candidate_bad
            candidate_table degree_bound roots final_value round_layers layers"
      unfolding generic_fri_sampled_query_bad_pair_union_def by auto
    have evidence:
      "generic_fri_sampled_query_candidate_evidence low_degree candidate_bad
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers"
      by (rule generic_fri_sampled_query_bad_pair_setD[OF pair])
    show "challenges \<in> B"
      by (rule cover[OF query_space evidence])
  qed
  show ?thesis
    unfolding generic_fri_sampled_query_finite_cover_def
    using finite_B subset by simp
qed

lemma generic_fri_sampled_query_projection_fraction_bound_from_cover:
  assumes cover:
    "generic_fri_sampled_query_finite_cover low_degree candidate_bad
      degree_bound B"
    and fraction_bound:
    "nnreal (card B) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
  shows
    "generic_fri_sampled_query_projection_fraction_bound low_degree
      candidate_bad degree_bound C"
  by (rule generic_fri_sampled_query_projection_fraction_bound_from_finite_cover)
    (rule generic_fri_sampled_query_finite_coverD(2)[OF cover],
     rule generic_fri_sampled_query_finite_coverD(1)[OF cover],
     rule fraction_bound)

lemma trace_fri_sampled_query_bad_candidate_bound_from_generic_cover:
  assumes future: "trace_fri_future_fresh s"
    and cover:
    "generic_fri_sampled_query_finite_cover trace_table_low_degree
      (Not \<circ> trace_table_low_degree) (clength - 1) B"
    and fraction_bound:
    "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s \<le> C"
proof (rule
    wp_trace_fri_sampled_query_bad_candidate_bound_from_generic_projection_fraction
    [OF future])
  show
    "generic_fri_sampled_query_projection_fraction_bound
      trace_table_low_degree (Not \<circ> trace_table_low_degree)
      (clength - 1) C"
    by (rule generic_fri_sampled_query_projection_fraction_bound_from_cover
        [OF cover])
      (use fraction_bound in
        \<open>simp add: fri_round_count_for_degree_bound_def clength_pos\<close>)
qed

lemma composition_fri_sampled_query_bad_candidate_bound_from_generic_cover:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and cover:
    "\<And>dg. generic_fri_sampled_query_finite_cover
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg) (B dg)"
    and fraction_bound:
    "\<And>dg. nnreal (card (B dg)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> C"
proof (rule
    wp_composition_fri_sampled_query_bad_candidate_bound_from_generic_projection_fraction
    [OF future])
  fix dg
  show
    "generic_fri_sampled_query_projection_fraction_bound
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg) C"
    by (rule generic_fri_sampled_query_projection_fraction_bound_from_cover
        [OF cover[of dg]])
      (use fraction_bound[of dg] in
        \<open>simp add: fri_round_count_for_degree_bound_def\<close>)
qed

end

end
