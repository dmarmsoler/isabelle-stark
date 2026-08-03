(*  Title:      Stark/Soundness_FRI_Generic_Low_Degree.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Generic_Low_Degree
  imports Soundness_FRI_Layer_Evidence
begin

text \<open>
  Generic FRI low-degree proof interface.

  This theory factors the trace/composition-independent bad-challenge-list
  layer.  It deliberately stays at the generic FRI level: no trace-specific or
  composition-specific candidate predicate is mentioned here.
\<close>

context soundness
begin

definition generic_fri_partial_evidence
  :: "('f list \<Rightarrow> bool) \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> bool"
where
  "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers \<longleftrightarrow>
    length roots = fri_round_count_for_degree_bound degree_bound \<and>
    length challenges = length roots \<and>
    fri_all_round_layer_evidence roots challenges query_idxs round_layers"

definition generic_fri_bad_challenge_lists
  :: "nat \<Rightarrow> (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> 'f list set"
where
  "generic_fri_bad_challenge_lists n bad =
    fri_multiround_bad_challenge_lists n bad"

definition generic_fri_round_bad_challenge_lists
  :: "nat \<Rightarrow> (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> nat \<Rightarrow>
      'f list set"
where
  "generic_fri_round_bad_challenge_lists n bad i =
    {bs \<in> fri_challenge_space n. i < n \<and> bs ! i \<in> bad i (take i bs)}"

definition generic_fri_round_bad_witnesses
  :: "nat \<Rightarrow> (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> nat \<Rightarrow>
      ('f list \<times> 'f \<times> 'f list) set"
where
  "generic_fri_round_bad_witnesses n bad i =
    {(prefix, b, suffix).
      i < n \<and>
      length prefix = i \<and>
      b \<in> bad i prefix \<and>
      length suffix = n - Suc i}"

definition generic_fri_bad_candidate
  :: "('f list \<Rightarrow> bool) \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow>
      (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
where
  "generic_fri_bad_candidate low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers bad \<longleftrightarrow>
    generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers \<and>
    \<not> low_degree candidate_table \<and>
    challenges \<in> generic_fri_bad_challenge_lists (length challenges) bad"

definition generic_fri_proximity_evidence
  :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      'f list list \<Rightarrow> 'f list list \<Rightarrow> 'f list \<Rightarrow>
      (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
where
  "generic_fri_proximity_evidence n d lens pws doms layers challenges bad
    \<longleftrightarrow>
      fri_multiround_proximity_steps n d lens pws doms layers bad \<and>
      challenges \<in> fri_challenge_space n \<and>
      (\<forall>i < n.
        fri_algebraic_layer_relation (lens ! i) (pws ! i)
          (challenges ! i) (doms ! i) (layers ! i)
          (doms ! Suc i) (layers ! Suc i)) \<and>
      \<not> fri_table_low_degree_on d (doms ! 0) (layers ! 0) \<and>
      fri_table_low_degree_on (fri_degree_after n d) (doms ! n)
        (layers ! n)"

definition generic_fri_canonical_layer_chain_evidence
  :: "('f list \<Rightarrow> bool) \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow>
      (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
where
  "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad \<longleftrightarrow>
    generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers \<and>
    doms ! 0 = eval_domain \<and>
    layers ! 0 = candidate_table \<and>
    fri_final_constant_consistent (layers ! length challenges) final_value \<and>
    generic_fri_proximity_evidence (length challenges) degree_bound
      (fri_layer_lengths (length challenges) (clength * scale))
      (map (\<lambda>i. 2 ^ i) [0..<length challenges])
      doms layers challenges bad"

definition generic_fri_sampled_layer_chain_evidence
  :: "('f list \<Rightarrow> bool) \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers \<longleftrightarrow>
    generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers \<and>
    length doms = Suc (length challenges) \<and>
    length layers = Suc (length challenges) \<and>
    doms ! 0 = eval_domain \<and>
    layers ! 0 = candidate_table \<and>
    fri_final_constant_consistent (layers ! length challenges) final_value \<and>
    (\<forall>round_idx < length query_idxs.
      \<forall>layer_idx < length challenges.
        fri_evidence_next_idx roots query_idxs round_idx layer_idx <
          length (layers ! Suc layer_idx) \<and>
        fri_sampled_table_fold
          (challenges ! layer_idx)
          (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
          (2 ^ layer_idx)
          (doms ! layer_idx)
          (layers ! layer_idx)
          (round_layers ! round_idx ! layer_idx)
          (layers ! Suc layer_idx !
            fri_evidence_next_idx roots query_idxs round_idx layer_idx))"

definition fri_sampled_domains_align
  :: "'f list \<Rightarrow> nat list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "fri_sampled_domains_align roots query_idxs doms \<longleftrightarrow>
    (\<forall>round_idx < length query_idxs.
      \<forall>layer_idx < length roots.
        doms ! layer_idx !
          fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
        (h ^ fri_evidence_layer_idx roots query_idxs round_idx layer_idx *
          shift) ^ (2 ^ layer_idx))"

definition fri_sampled_next_domains_align
  :: "'f list \<Rightarrow> nat list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "fri_sampled_next_domains_align roots query_idxs doms \<longleftrightarrow>
    (\<forall>round_idx < length query_idxs.
      \<forall>layer_idx < length roots.
        doms ! layer_idx !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx =
        (h ^ fri_evidence_next_idx roots query_idxs round_idx layer_idx *
          shift) ^ (2 ^ layer_idx))"

definition fri_sampled_indices_in_fold_range
  :: "'f list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "fri_sampled_indices_in_fold_range roots query_idxs \<longleftrightarrow>
    (\<forall>round_idx < length query_idxs.
      \<forall>layer_idx < length roots.
        fri_evidence_next_idx roots query_idxs round_idx layer_idx <
          fri_evidence_layer_len roots layer_idx div 2)"

definition fri_sampled_layer_covers_fold_indices
  :: "'f list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
where
  "fri_sampled_layer_covers_fold_indices roots query_idxs layer_idx
    \<longleftrightarrow>
      (\<forall>idx < fri_evidence_layer_len roots layer_idx div 2.
        \<exists>round_idx < length query_idxs.
          fri_evidence_next_idx roots query_idxs round_idx layer_idx = idx)"

definition fri_sampled_layers_cover_fold_indices
  :: "'f list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "fri_sampled_layers_cover_fold_indices roots query_idxs \<longleftrightarrow>
    (\<forall>layer_idx < length roots.
      fri_sampled_layer_covers_fold_indices roots query_idxs layer_idx)"

definition generic_fri_sampled_layer_chain_full_cover
  :: "('f list \<Rightarrow> bool) \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow>
      (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
where
  "generic_fri_sampled_layer_chain_full_cover low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad \<longleftrightarrow>
    generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers \<and>
    fri_multiround_proximity_steps (length challenges) degree_bound
      (fri_layer_lengths (length challenges) (clength * scale))
      (map (\<lambda>i. 2 ^ i) [0..<length challenges])
      doms layers bad \<and>
    fri_sampled_layers_cover_fold_indices roots query_idxs \<and>
    (\<forall>layer_idx < length challenges.
      2 dvd fri_evidence_layer_len roots layer_idx) \<and>
    (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx * 2 ^ layer_idx =
        clength * scale) \<and>
    (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx \<le>
        length (doms ! layer_idx)) \<and>
    (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx \<le>
        length (layers ! layer_idx)) \<and>
    (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx div 2 \<le>
        length (doms ! Suc layer_idx)) \<and>
    (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx div 2 \<le>
        length (layers ! Suc layer_idx)) \<and>
    (\<forall>layer_idx < length challenges.
      \<forall>idx < fri_evidence_layer_len roots layer_idx div 2.
        doms ! Suc layer_idx ! idx =
          (doms ! layer_idx ! idx)\<^sup>2) \<and>
    (\<forall>layer_idx < length challenges.
      \<forall>idx < fri_evidence_layer_len roots layer_idx div 2.
        doms ! layer_idx ! idx = (h ^ idx * shift) ^ (2 ^ layer_idx)) \<and>
    \<not> fri_table_low_degree_on degree_bound eval_domain candidate_table \<and>
    fri_table_low_degree_on
      (fri_degree_after (length challenges) degree_bound)
      (doms ! length challenges) (layers ! length challenges)"

lemma generic_fri_partial_evidence_shapes:
  assumes "generic_fri_partial_evidence low_degree candidate_table degree_bound
    roots challenges final_value query_idxs round_layers"
  shows "length roots = fri_round_count_for_degree_bound degree_bound"
    and "length challenges = length roots"
    and "fri_all_round_layer_evidence roots challenges query_idxs round_layers"
  using assms unfolding generic_fri_partial_evidence_def by simp_all

lemma generic_fri_sampled_layer_chain_evidenceD:
  assumes
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
  shows
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    "length doms = Suc (length challenges)"
    "length layers = Suc (length challenges)"
    "doms ! 0 = eval_domain"
    "layers ! 0 = candidate_table"
    "fri_final_constant_consistent (layers ! length challenges) final_value"
  using assms
  unfolding generic_fri_sampled_layer_chain_evidence_def by simp_all

lemma generic_fri_sampled_layer_chain_evidence_sample:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
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
      (doms ! layer_idx)
      (layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (layers ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
  using chain round_bound layer_bound
  unfolding generic_fri_sampled_layer_chain_evidence_def by simp_all

lemma fri_sampled_domains_alignD:
  assumes "fri_sampled_domains_align roots query_idxs doms"
    and "round_idx < length query_idxs"
    and "layer_idx < length roots"
  shows
    "doms ! layer_idx !
        fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
      (h ^ fri_evidence_layer_idx roots query_idxs round_idx layer_idx *
        shift) ^ (2 ^ layer_idx)"
  using assms unfolding fri_sampled_domains_align_def by blast

lemma fri_sampled_next_domains_alignD:
  assumes "fri_sampled_next_domains_align roots query_idxs doms"
    and "round_idx < length query_idxs"
    and "layer_idx < length roots"
  shows
    "doms ! layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx =
      (h ^ fri_evidence_next_idx roots query_idxs round_idx layer_idx *
        shift) ^ (2 ^ layer_idx)"
  using assms unfolding fri_sampled_next_domains_align_def by blast

lemma fri_sampled_indices_in_fold_rangeD:
  assumes "fri_sampled_indices_in_fold_range roots query_idxs"
    and "round_idx < length query_idxs"
    and "layer_idx < length roots"
  shows
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      fri_evidence_layer_len roots layer_idx div 2"
  using assms unfolding fri_sampled_indices_in_fold_range_def by blast

lemma fri_sampled_layers_cover_fold_indicesD:
  assumes "fri_sampled_layers_cover_fold_indices roots query_idxs"
    and "layer_idx < length roots"
    and "idx < fri_evidence_layer_len roots layer_idx div 2"
  obtains round_idx
  where "round_idx < length query_idxs"
    and "fri_evidence_next_idx roots query_idxs round_idx layer_idx = idx"
  using assms
  unfolding fri_sampled_layers_cover_fold_indices_def
    fri_sampled_layer_covers_fold_indices_def
  by blast

lemma fri_sampled_layer_covers_fold_indices_card_le_rounds:
  assumes cover: "fri_sampled_layer_covers_fold_indices roots query_idxs layer_idx"
  shows "fri_evidence_layer_len roots layer_idx div 2 \<le> length query_idxs"
proof -
  let ?N = "fri_evidence_layer_len roots layer_idx div 2"
  have subset:
    "{..< ?N} \<subseteq>
      (\<lambda>round_idx.
        fri_evidence_next_idx roots query_idxs round_idx layer_idx) `
        {..<length query_idxs}"
  proof
    fix idx
    assume "idx \<in> {..< ?N}"
    then have idx_bound: "idx < ?N"
      by simp
    then obtain round_idx where round_bound: "round_idx < length query_idxs"
      and idx_eq:
        "fri_evidence_next_idx roots query_idxs round_idx layer_idx = idx"
      using cover
      unfolding fri_sampled_layer_covers_fold_indices_def by blast
    then show "idx \<in>
      (\<lambda>round_idx.
        fri_evidence_next_idx roots query_idxs round_idx layer_idx) `
        {..<length query_idxs}"
      by blast
  qed
  have "?N = card {..< ?N}"
    by simp
  also have "... \<le>
      card ((\<lambda>round_idx.
        fri_evidence_next_idx roots query_idxs round_idx layer_idx) `
        {..<length query_idxs})"
    by (rule card_mono) (simp_all add: subset)
  also have "... \<le> card {..<length query_idxs}"
    by (rule card_image_le) simp
  also have "... = length query_idxs"
    by simp
  finally show ?thesis .
qed

lemma fri_sampled_layers_cover_fold_indices_card_le_rounds:
  assumes cover: "fri_sampled_layers_cover_fold_indices roots query_idxs"
    and layer_bound: "layer_idx < length roots"
  shows "fri_evidence_layer_len roots layer_idx div 2 \<le> length query_idxs"
proof -
  have layer_cover:
    "fri_sampled_layer_covers_fold_indices roots query_idxs layer_idx"
    using cover layer_bound
    unfolding fri_sampled_layers_cover_fold_indices_def by blast
  show ?thesis
    by (rule fri_sampled_layer_covers_fold_indices_card_le_rounds
        [OF layer_cover])
qed

lemma fri_sampled_layers_not_cover_if_layer_exceeds_rounds:
  assumes layer_bound: "layer_idx < length roots"
    and too_few:
      "length query_idxs < fri_evidence_layer_len roots layer_idx div 2"
  shows "\<not> fri_sampled_layers_cover_fold_indices roots query_idxs"
proof
  assume cover: "fri_sampled_layers_cover_fold_indices roots query_idxs"
  have "fri_evidence_layer_len roots layer_idx div 2 \<le> length query_idxs"
    by (rule fri_sampled_layers_cover_fold_indices_card_le_rounds
        [OF cover layer_bound])
  then show False
    using too_few by simp
qed

lemma generic_fri_proximity_evidenceD:
  assumes "generic_fri_proximity_evidence n d lens pws doms layers
    challenges bad"
  shows
    "fri_multiround_proximity_steps n d lens pws doms layers bad"
    "challenges \<in> fri_challenge_space n"
    "\<not> fri_table_low_degree_on d (doms ! 0) (layers ! 0)"
    "fri_table_low_degree_on (fri_degree_after n d) (doms ! n)
      (layers ! n)"
  using assms unfolding generic_fri_proximity_evidence_def by simp_all

lemma generic_fri_proximity_evidence_relation:
  assumes proximity:
    "generic_fri_proximity_evidence n d lens pws doms layers
      challenges bad"
    and i_bound: "i < n"
  shows
    "fri_algebraic_layer_relation (lens ! i) (pws ! i)
      (challenges ! i) (doms ! i) (layers ! i)
      (doms ! Suc i) (layers ! Suc i)"
  using proximity i_bound
  unfolding generic_fri_proximity_evidence_def by blast

lemma generic_fri_canonical_layer_chain_proximity:
  assumes chain:
    "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
  shows
    "generic_fri_proximity_evidence (length challenges) degree_bound
      (fri_layer_lengths (length challenges) (clength * scale))
      (map (\<lambda>i. 2 ^ i) [0..<length challenges])
      doms layers challenges bad"
  using chain unfolding generic_fri_canonical_layer_chain_evidence_def
  by simp

lemma generic_fri_canonical_layer_chain_relation:
  assumes chain:
    "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
    and i_bound: "i < length challenges"
  shows
    "fri_algebraic_layer_relation
      (fri_layer_lengths (length challenges) (clength * scale) ! i)
      (2 ^ i)
      (challenges ! i) (doms ! i) (layers ! i)
      (doms ! Suc i) (layers ! Suc i)"
proof -
  have proximity:
    "generic_fri_proximity_evidence (length challenges) degree_bound
      (fri_layer_lengths (length challenges) (clength * scale))
      (map (\<lambda>i. 2 ^ i) [0..<length challenges])
      doms layers challenges bad"
    by (rule generic_fri_canonical_layer_chain_proximity[OF chain])
  have rel:
    "fri_algebraic_layer_relation
      (fri_layer_lengths (length challenges) (clength * scale) ! i)
      ((map (\<lambda>i. 2 ^ i) [0..<length challenges]) ! i)
      (challenges ! i) (doms ! i) (layers ! i)
      (doms ! Suc i) (layers ! Suc i)"
    by (rule generic_fri_proximity_evidence_relation
        [OF proximity i_bound])
  then show ?thesis
    using i_bound by simp
qed

lemma generic_fri_canonical_layer_chain_lengths:
  assumes chain:
    "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
  shows "length doms = Suc (length challenges)"
    and "length layers = Suc (length challenges)"
proof -
  have proximity:
    "generic_fri_proximity_evidence (length challenges) degree_bound
      (fri_layer_lengths (length challenges) (clength * scale))
      (map (\<lambda>i. 2 ^ i) [0..<length challenges])
      doms layers challenges bad"
    by (rule generic_fri_canonical_layer_chain_proximity[OF chain])
  have steps:
    "fri_multiround_proximity_steps (length challenges) degree_bound
      (fri_layer_lengths (length challenges) (clength * scale))
      (map (\<lambda>i. 2 ^ i) [0..<length challenges])
      doms layers bad"
    by (rule generic_fri_proximity_evidenceD(1)[OF proximity])
  then show "length doms = Suc (length challenges)"
    and "length layers = Suc (length challenges)"
    unfolding fri_multiround_proximity_steps_def by simp_all
qed

lemma fri_algebraic_layer_relation_next_index_bound:
  assumes relation:
    "fri_algebraic_layer_relation len pw ch fri_dom layer next_dom
      next_layer"
    and idx_bound: "idx < len div 2"
  shows "idx < length next_layer"
proof -
  have "len div 2 \<le> length next_layer"
    using relation unfolding fri_algebraic_layer_relation_def by simp
  then show ?thesis
    using idx_bound by linarith
qed

lemma fri_algebraic_layer_relation_sampled_fold_eq:
  assumes relation:
    "fri_algebraic_layer_relation len pw ch fri_dom layer next_dom
      next_layer"
    and idx_bound: "idx < len div 2"
  shows "next_layer ! idx =
    fri_table_fold_value ch layer fri_dom len pw idx"
  by (rule fri_algebraic_layer_relationD(2)[OF relation idx_bound])

lemma fri_half_dvd_len_if_even:
  fixes len :: nat
  assumes even_len: "2 dvd len"
  shows "len div 2 dvd len"
proof (cases "len = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "len = 2 * (len div 2)"
    using even_len by simp
  then have "len = (len div 2) * 2"
    by simp
  then show ?thesis
    unfolding dvd_def by blast
qed

lemma fri_sibling_index_mod_half:
  fixes len idx :: nat
  assumes even_len: "2 dvd len"
  shows "fri_sibling_index len idx mod (len div 2) =
    idx mod (len div 2)"
proof -
  have dvd_half: "len div 2 dvd len"
    by (rule fri_half_dvd_len_if_even[OF even_len])
  have "fri_sibling_index len idx mod (len div 2) =
      ((idx + len div 2) mod len) mod (len div 2)"
    unfolding fri_sibling_index_def by simp
  also have "... = (idx + len div 2) mod (len div 2)"
    using mod_mod_cancel[OF dvd_half, of "idx + len div 2"] by simp
  also have "... = idx mod (len div 2)"
    by simp
  finally show ?thesis .
qed

lemma fri_fold_value_swap_neg_denominator:
  "fri_fold_value b xp xn (- denom) =
    fri_fold_value b xn xp denom"
proof (cases "denom = 0")
  case True
  then show ?thesis
    unfolding fri_fold_value_def by (simp add: algebra_simps)
next
  case False
  then show ?thesis
    unfolding fri_fold_value_def by (simp add: field_simps)
qed

lemma soundness_h_power_mod_eval_domain:
  "h ^ (k mod (clength * scale)) = h ^ k"
proof -
  let ?N = "clength * scale"
  have order: "h ^ ?N = 1"
    using h_order .
  have k_eq: "k = (k div ?N) * ?N + k mod ?N"
    using div_mult_mod_eq[of k ?N] by (simp add: mult.commute)
  have period: "h ^ ((k div ?N) * ?N) = 1"
  proof -
    have "h ^ ((k div ?N) * ?N) = h ^ (?N * (k div ?N))"
      by (simp add: mult.commute)
    also have "... = (h ^ ?N) ^ (k div ?N)"
      by (simp only: power_mult)
    also have "... = 1"
      using order by simp
    finally show ?thesis .
  qed
  have "h ^ k = h ^ ((k div ?N) * ?N + k mod ?N)"
    using k_eq by simp
  also have "... = h ^ ((k div ?N) * ?N) * h ^ (k mod ?N)"
    by (simp add: power_add)
  also have "... = h ^ (k mod ?N)"
    using period by simp
  finally show ?thesis
    by simp
qed

lemma soundness_h_half_shift:
  "h ^ (k + (clength * scale) div 2) = -(h ^ k)"
  using h_half_order
  by (simp add: power_add algebra_simps)

lemma soundness_mod_mult_right_factor_nat:
  fixes a b c :: nat
  assumes b_pos: "0 < b"
    and c_pos: "0 < c"
  shows "((a mod b) * c) mod (b * c) = (a * c) mod (b * c)"
proof -
  have decomp: "a = a div b * b + a mod b"
    using div_mult_mod_eq[of a b] by simp
  have r_less: "(a mod b) * c < b * c"
    using b_pos c_pos mod_less_divisor[OF b_pos]
    by (simp add: mult_less_mono2)
  have r_le: "(a mod b) * c \<le> a * c"
  proof -
    have "a mod b \<le> a"
      using decomp by linarith
    then show ?thesis
      by simp
  qed
  have dvd_diff: "b * c dvd a * c - (a mod b) * c"
  proof -
    have ac_decomp: "a * c = (a div b) * (b * c) + (a mod b) * c"
    proof -
      have "a * c = (a div b * b + a mod b) * c"
        using decomp by simp
      also have "... = (a div b * b) * c + (a mod b) * c"
        by (simp only: distrib_right)
      also have "... = (a div b) * (b * c) + (a mod b) * c"
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have "a * c - (a mod b) * c = (a div b) * (b * c)"
      using ac_decomp by simp
    then show ?thesis by simp
  qed
  have "(a * c) mod (b * c) = (a mod b) * c"
    by (rule mod_nat_eqI[OF r_less r_le dvd_diff])
  then show ?thesis by simp
qed

lemma fri_layer_lengths_nth_div:
  assumes j_bound: "j < n"
  shows "fri_layer_lengths n len ! j = len div 2 ^ j"
  using j_bound
proof (induction n arbitrary: len j)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof (cases j)
    case 0
    then show ?thesis by simp
  next
    case (Suc k)
    then have k_bound: "k < n"
      using Suc.prems by simp
    have "fri_layer_lengths (Suc n) len ! j =
        fri_layer_lengths n (len div 2) ! k"
      using Suc by simp
    also have "... = (len div 2) div 2 ^ k"
      by (rule Suc.IH[OF k_bound])
    also have "... = len div 2 ^ j"
      unfolding Suc by (simp add: div_mult2_eq mult.commute)
    finally show ?thesis .
  qed
qed

lemma fri_layer_lengths_round_product_if_dvd:
  assumes j_bound: "j < n"
    and dvd: "2 ^ j dvd len"
  shows "fri_layer_lengths n len ! j * 2 ^ j = len"
proof -
  have "fri_layer_lengths n len ! j = len div 2 ^ j"
    by (rule fri_layer_lengths_nth_div[OF j_bound])
  then show ?thesis
    using dvd by (simp add: dvd_div_mult_self)
qed

lemma fri_layer_lengths_even_if_dvd:
  assumes j_bound: "j < n"
    and dvd: "2 ^ Suc j dvd len"
  shows "2 dvd fri_layer_lengths n len ! j"
proof -
  obtain k where len_eq: "len = 2 ^ Suc j * k"
    using dvd by blast
  have "fri_layer_lengths n len ! j = len div 2 ^ j"
    by (rule fri_layer_lengths_nth_div[OF j_bound])
  also have "... = 2 * k"
    using len_eq by simp
  finally show ?thesis by simp
qed

lemma fri_layer_lengths_Suc_nth:
  assumes "Suc j < n"
  shows "fri_layer_lengths n len ! Suc j =
    fri_layer_lengths n len ! j div 2"
proof -
  have j_bound: "j < n"
    using assms by simp
  have "fri_layer_lengths n len ! Suc j = len div 2 ^ Suc j"
    by (rule fri_layer_lengths_nth_div[OF assms])
  also have "... = (len div 2 ^ j) div 2"
    by (metis div_mult2_eq mult.commute power_Suc)
  also have "... = fri_layer_lengths n len ! j div 2"
    using fri_layer_lengths_nth_div[OF j_bound, of len] by simp
  finally show ?thesis .
qed

lemma generic_fri_canonical_domain_power:
  assumes chain:
    "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
    and roots_len: "length challenges = length roots"
    and layer_bound: "layer_idx < length challenges"
    and idx_bound: "idx < fri_evidence_layer_len roots layer_idx"
  shows "doms ! layer_idx ! idx = (h ^ idx * shift) ^ (2 ^ layer_idx)"
  using layer_bound idx_bound
proof (induction layer_idx arbitrary: idx)
  case 0
  note zero = 0
  have dom0: "doms ! 0 = eval_domain"
    using chain unfolding generic_fri_canonical_layer_chain_evidence_def
    by simp
  have len0: "fri_evidence_layer_len roots 0 = clength * scale"
  proof (cases roots)
    case Nil
    then show ?thesis
      using zero roots_len unfolding fri_evidence_layer_len_def by simp
  next
    case (Cons r rs)
    then show ?thesis
      unfolding fri_evidence_layer_len_def by simp
  qed
  show ?case
    using eval_domain_nth[of idx] zero len0
    unfolding dom0 by simp
next
  case (Suc j)
  have j_bound: "j < length challenges"
    using Suc.prems by simp
  have len_eq_j:
    "fri_layer_lengths (length challenges) (clength * scale) ! j =
      fri_evidence_layer_len roots j"
    using roots_len unfolding fri_evidence_layer_len_def by simp
  have len_eq_suc:
    "fri_layer_lengths (length challenges) (clength * scale) ! Suc j =
      fri_evidence_layer_len roots (Suc j)"
    using roots_len unfolding fri_evidence_layer_len_def by simp
  have suc_len:
    "fri_evidence_layer_len roots (Suc j) =
      fri_evidence_layer_len roots j div 2"
    using fri_layer_lengths_Suc_nth[OF Suc.prems(1), of "clength * scale"]
      len_eq_j len_eq_suc by simp
  have idx_half: "idx < fri_evidence_layer_len roots j div 2"
    using Suc.prems(2) suc_len by simp
  have idx_prev: "idx < fri_evidence_layer_len roots j"
    using idx_half by simp
  have rel:
    "fri_algebraic_layer_relation
      (fri_evidence_layer_len roots j)
      (2 ^ j)
      (challenges ! j) (doms ! j) (layers ! j)
      (doms ! Suc j) (layers ! Suc j)"
    using generic_fri_canonical_layer_chain_relation[OF chain j_bound]
      len_eq_j by simp
  have next_dom:
    "doms ! Suc j ! idx = (doms ! j ! idx)\<^sup>2"
    by (rule fri_algebraic_layer_relationD(1)[OF rel idx_half])
  have prev_dom:
    "doms ! j ! idx = (h ^ idx * shift) ^ (2 ^ j)"
    by (rule Suc.IH[OF j_bound idx_prev])
  let ?x = "h ^ idx * shift"
  have pow_step: "(?x ^ (2 ^ j))\<^sup>2 = ?x ^ (2 ^ Suc j)"
  proof -
    have "(?x ^ (2 ^ j))\<^sup>2 = ?x ^ ((2 ^ j) * 2)"
      by (simp add: power_mult)
    also have "... = ?x ^ (2 ^ Suc j)"
      by (simp add: mult.commute)
    finally show ?thesis .
  qed
  show ?case
    using next_dom prev_dom pow_step by simp
qed

lemma fri_sibling_domain_round:
  assumes len_pos: "0 < len"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
  shows
    "((h ^ ((i + len div 2) mod len)) * shift) ^ pw =
      - (((h ^ i) * shift) ^ pw)"
proof -
  let ?N = "clength * scale"
  have pw_pos: "0 < pw"
    using len_pos round eval_domain_size_pos by (cases pw) simp_all
  have half_round: "(len div 2) * pw = ?N div 2"
  proof -
    from even_len obtain k where len_eq: "len = 2 * k"
      by blast
    then have "?N = 2 * (k * pw)"
      using round by simp
    then show ?thesis
      using len_eq by simp
  qed
  have exp_mod:
    "(((i + len div 2) mod len) * pw) mod ?N =
      (i * pw + ?N div 2) mod ?N"
  proof -
    have "(((i + len div 2) mod len) * pw) mod ?N =
        ((i + len div 2) * pw) mod ?N"
      using soundness_mod_mult_right_factor_nat
        [OF len_pos pw_pos, of "i + len div 2"] round by simp
    also have "... = (i * pw + ?N div 2) mod ?N"
      using half_round by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have h_exp:
    "h ^ (((i + len div 2) mod len) * pw) = -(h ^ (i * pw))"
  proof -
    have "h ^ (((i + len div 2) mod len) * pw) =
        h ^ ((((i + len div 2) mod len) * pw) mod ?N)"
      using soundness_h_power_mod_eval_domain
        [of "((i + len div 2) mod len) * pw"]
      by simp
    also have "... = h ^ ((i * pw + ?N div 2) mod ?N)"
      using exp_mod by simp
    also have "... = h ^ (i * pw + ?N div 2)"
      using soundness_h_power_mod_eval_domain[of "i * pw + ?N div 2"]
      by simp
    also have "... = -(h ^ (i * pw))"
      by (rule soundness_h_half_shift)
    finally show ?thesis .
  qed
  show ?thesis
    using h_exp by (simp add: power_mult power_mult_distrib)
qed

lemma fri_sibling_fold_denominator:
  assumes len_pos: "0 < len"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
  shows
    "fri_fold_denominator ((h ^ fri_sibling_index len i * shift) ^ pw) 1 =
      - fri_fold_denominator ((h ^ i * shift) ^ pw) 1"
  using fri_sibling_domain_round[OF len_pos even_len round, of i]
  unfolding fri_sibling_index_def fri_fold_denominator_def
  by simp

lemma fri_sibling_index_first_half:
  fixes len idx :: nat
  assumes even_len: "2 dvd len"
    and idx_bound: "idx < len div 2"
  shows "fri_sibling_index len idx = idx + len div 2"
proof -
  have len_eq: "len = 2 * (len div 2)"
    using even_len by simp
  have "idx + len div 2 < len"
    using idx_bound len_eq by linarith
  then show ?thesis
    unfolding fri_sibling_index_def by simp
qed

lemma fri_sibling_index_involution_first_half:
  fixes len idx :: nat
  assumes even_len: "2 dvd len"
    and idx_bound: "idx < len div 2"
  shows "fri_sibling_index len (fri_sibling_index len idx) = idx"
proof -
  have len_eq: "len = 2 * (len div 2)"
    using even_len by simp
  have sib_eq: "fri_sibling_index len idx = idx + len div 2"
    by (rule fri_sibling_index_first_half[OF even_len idx_bound])
  have idx_len: "idx < len"
    using idx_bound len_eq by linarith
  have sum_eq: "idx + len div 2 + len div 2 = idx + len"
    using len_eq by linarith
  have "fri_sibling_index len (fri_sibling_index len idx) =
      ((idx + len div 2) mod len + len div 2) mod len"
    unfolding sib_eq fri_sibling_index_def by simp
  also have "... = (idx + len div 2 + len div 2) mod len"
    by (simp add: mod_add_left_eq)
  also have "... = (idx + len) mod len"
    by (simp only: sum_eq)
  also have "... = idx"
    using idx_len by simp
  finally show ?thesis .
qed

lemma fri_sibling_index_mod_half_second_half:
  fixes len raw :: nat
  assumes even_len: "2 dvd len"
    and raw_bound: "raw < len"
    and second_half: "\<not> raw < len div 2"
  shows "raw = fri_sibling_index len (raw mod (len div 2))"
proof -
  let ?half = "len div 2"
  have len_eq: "len = 2 * ?half"
    using even_len by simp
  have half_pos: "0 < ?half"
    using raw_bound second_half len_eq by linarith
  have half_le_raw: "?half \<le> raw"
    using second_half by simp
  define k where "k = raw - ?half"
  have raw_eq: "raw = ?half + k"
    using half_le_raw unfolding k_def by simp
  have k_bound: "k < ?half"
    using raw_bound len_eq raw_eq by linarith
  have raw_mod: "raw mod ?half = k"
    using raw_eq k_bound half_pos by simp
  have "fri_sibling_index len (raw mod ?half) =
      (k + ?half) mod len"
    unfolding raw_mod fri_sibling_index_def by simp
  also have "... = raw"
    using raw_eq raw_bound by simp
  finally show ?thesis by simp
qed

lemma fri_table_fold_value_sibling_first_half:
  assumes even_len: "2 dvd len"
    and idx_bound: "idx < len div 2"
    and round: "len * pw = clength * scale"
    and dom_idx: "fri_dom ! idx = (h ^ idx * shift) ^ pw"
    and dom_sib:
      "fri_dom ! fri_sibling_index len idx =
        (h ^ fri_sibling_index len idx * shift) ^ pw"
  shows
    "fri_table_fold_value ch layer fri_dom len pw
      (fri_sibling_index len idx) =
     fri_table_fold_value ch layer fri_dom len pw idx"
proof -
  have len_pos: "0 < len"
    using idx_bound by simp
  have sib_sib: "fri_sibling_index len (fri_sibling_index len idx) = idx"
    by (rule fri_sibling_index_involution_first_half
        [OF even_len idx_bound])
  have denom_sib:
    "fri_fold_denominator
      ((h ^ fri_sibling_index len idx * shift) ^ pw) 1 =
      - fri_fold_denominator ((h ^ idx * shift) ^ pw) 1"
    by (rule fri_sibling_fold_denominator
        [OF len_pos even_len round])
  have "fri_table_fold_value ch layer fri_dom len pw
      (fri_sibling_index len idx) =
    fri_fold_value ch
      (layer ! fri_sibling_index len idx)
      (layer ! idx)
      (- fri_fold_denominator ((h ^ idx * shift) ^ pw) 1)"
    unfolding fri_table_fold_value_def
    using sib_sib dom_sib denom_sib by simp
  also have "... =
    fri_fold_value ch
      (layer ! idx)
      (layer ! fri_sibling_index len idx)
      (fri_fold_denominator ((h ^ idx * shift) ^ pw) 1)"
    by (rule fri_fold_value_swap_neg_denominator)
  also have "... = fri_table_fold_value ch layer fri_dom len pw idx"
    unfolding fri_table_fold_value_def using dom_idx by simp
  finally show ?thesis .
qed

lemma fri_sampled_table_fold_from_algebraic_relation:
  assumes relation:
    "fri_algebraic_layer_relation len pw ch fri_dom layer next_dom
      next_layer"
    and idx_bound: "idx < len div 2"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and match: "fri_opening_matches_table len idx layer xp xn"
    and dom_idx: "fri_dom ! idx = (h ^ idx * shift) ^ pw"
  shows "idx < length next_layer"
    and "fri_sampled_table_fold ch len idx pw fri_dom layer chunk
      (next_layer ! idx)"
proof -
  show idx_len: "idx < length next_layer"
    by (rule fri_algebraic_layer_relation_next_index_bound
        [OF relation idx_bound])
  have fold_eq:
    "next_layer ! idx = fri_table_fold_value ch layer fri_dom len pw idx"
    by (rule fri_algebraic_layer_relation_sampled_fold_eq
        [OF relation idx_bound])
  show "fri_sampled_table_fold ch len idx pw fri_dom layer chunk
      (next_layer ! idx)"
    by (rule fri_sampled_table_foldI[OF chunk match dom_idx fold_eq])
qed

lemma fri_sampled_table_fold_from_algebraic_relation_sibling:
  assumes relation:
    "fri_algebraic_layer_relation len pw ch fri_dom layer next_dom
      next_layer"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
    and idx_bound: "idx < len div 2"
    and raw_eq: "raw = fri_sibling_index len idx"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and match: "fri_opening_matches_table len raw layer xp xn"
    and dom_raw: "fri_dom ! raw = (h ^ raw * shift) ^ pw"
    and dom_idx: "fri_dom ! idx = (h ^ idx * shift) ^ pw"
  shows "idx < length next_layer"
    and "fri_sampled_table_fold ch len raw pw fri_dom layer chunk
      (next_layer ! idx)"
proof -
  show idx_len: "idx < length next_layer"
    by (rule fri_algebraic_layer_relation_next_index_bound
        [OF relation idx_bound])
  have fold_idx:
    "next_layer ! idx = fri_table_fold_value ch layer fri_dom len pw idx"
    by (rule fri_algebraic_layer_relation_sampled_fold_eq
        [OF relation idx_bound])
  have fold_raw:
    "fri_table_fold_value ch layer fri_dom len pw raw =
      fri_table_fold_value ch layer fri_dom len pw idx"
    unfolding raw_eq
    by (rule fri_table_fold_value_sibling_first_half
        [OF even_len idx_bound round dom_idx])
      (use dom_raw raw_eq in simp)
  have fold_eq:
    "next_layer ! idx = fri_table_fold_value ch layer fri_dom len pw raw"
    using fold_idx fold_raw by simp
  show "fri_sampled_table_fold ch len raw pw fri_dom layer chunk
      (next_layer ! idx)"
    by (rule fri_sampled_table_foldI[OF chunk match dom_raw fold_eq])
qed

lemma fri_sampled_table_fold_from_algebraic_relation_mod_index:
  assumes relation:
    "fri_algebraic_layer_relation len pw ch fri_dom layer next_dom
      next_layer"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and match: "fri_opening_matches_table len raw layer xp xn"
    and dom_raw: "fri_dom ! raw = (h ^ raw * shift) ^ pw"
    and dom_norm:
      "fri_dom ! (raw mod (len div 2)) =
        (h ^ (raw mod (len div 2)) * shift) ^ pw"
  shows "raw mod (len div 2) < length next_layer"
    and "fri_sampled_table_fold ch len raw pw fri_dom layer chunk
      (next_layer ! (raw mod (len div 2)))"
proof -
  have raw_bound: "raw < len"
    by (rule fri_opening_matches_tableD(1)[OF match])
  show idx_len: "raw mod (len div 2) < length next_layer"
  proof (cases "raw < len div 2")
    case True
    then have raw_mod: "raw mod (len div 2) = raw"
      by simp
    show ?thesis
      using fri_sampled_table_fold_from_algebraic_relation(1)
        [OF relation True chunk match dom_raw]
      unfolding raw_mod .
  next
    case False
    let ?idx = "raw mod (len div 2)"
    have half_pos: "0 < len div 2"
      using raw_bound False even_len by (cases len) auto
    have idx_bound: "?idx < len div 2"
      using half_pos by simp
    show ?thesis
      by (rule fri_sampled_table_fold_from_algebraic_relation_sibling(1)
          [OF relation even_len round idx_bound _ chunk match dom_raw
            dom_norm])
        (rule fri_sibling_index_mod_half_second_half
          [OF even_len raw_bound False])
  qed
  show "fri_sampled_table_fold ch len raw pw fri_dom layer chunk
      (next_layer ! (raw mod (len div 2)))"
  proof (cases "raw < len div 2")
    case True
    then have raw_mod: "raw mod (len div 2) = raw"
      by simp
    show ?thesis
      using fri_sampled_table_fold_from_algebraic_relation(2)
        [OF relation True chunk match dom_raw]
      unfolding raw_mod .
  next
    case False
    let ?idx = "raw mod (len div 2)"
    have half_pos: "0 < len div 2"
      using raw_bound False even_len by (cases len) auto
    have idx_bound: "?idx < len div 2"
      using half_pos by simp
    show ?thesis
      by (rule fri_sampled_table_fold_from_algebraic_relation_sibling(2)
          [OF relation even_len round idx_bound _ chunk match dom_raw
            dom_norm])
        (rule fri_sibling_index_mod_half_second_half
          [OF even_len raw_bound False])
  qed
qed

lemma fri_sampled_table_fold_eq_at_mod_index:
  assumes fold:
    "fri_sampled_table_fold ch len raw pw fri_dom layer chunk next_value"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
    and dom_norm:
      "fri_dom ! (raw mod (len div 2)) =
        (h ^ (raw mod (len div 2)) * shift) ^ pw"
  shows "next_value =
    fri_table_fold_value ch layer fri_dom len pw (raw mod (len div 2))"
proof -
  from fold obtain xp xp_path xn xn_path where
    match: "fri_opening_matches_table len raw layer xp xn"
    and dom_raw: "fri_dom ! raw = (h ^ raw * shift) ^ pw"
    and next_eq: "next_value = fri_table_fold_value ch layer fri_dom len pw raw"
    by (elim fri_sampled_table_foldE)
  have raw_bound: "raw < len"
    by (rule fri_opening_matches_tableD(1)[OF match])
  show ?thesis
  proof (cases "raw < len div 2")
    case True
    then have "raw mod (len div 2) = raw"
      by simp
    then show ?thesis
      using next_eq by simp
  next
    case False
    let ?idx = "raw mod (len div 2)"
    have half_pos: "0 < len div 2"
      using raw_bound False even_len by (cases len) auto
    have idx_bound: "?idx < len div 2"
      using half_pos by simp
    have raw_eq: "raw = fri_sibling_index len ?idx"
      by (rule fri_sibling_index_mod_half_second_half
          [OF even_len raw_bound False])
    have dom_sib:
      "fri_dom ! fri_sibling_index len ?idx =
        (h ^ fri_sibling_index len ?idx * shift) ^ pw"
      using dom_raw raw_eq by simp
    have fold_sib:
      "fri_table_fold_value ch layer fri_dom len pw
        (fri_sibling_index len ?idx) =
        fri_table_fold_value ch layer fri_dom len pw ?idx"
      by (rule fri_table_fold_value_sibling_first_half
          [OF even_len idx_bound round dom_norm dom_sib])
    have "fri_table_fold_value ch layer fri_dom len pw raw =
        fri_table_fold_value ch layer fri_dom len pw ?idx"
      using raw_eq fold_sib by simp
    then show ?thesis
      using next_eq by simp
  qed
qed

lemma fri_algebraic_layer_relation_from_sampled_coverage:
  assumes even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
    and len_pos: "0 < len"
    and dom_len: "len \<le> length fri_dom"
    and layer_len: "len \<le> length layer"
    and next_dom_len: "len div 2 \<le> length next_dom"
    and next_layer_len: "len div 2 \<le> length next_layer"
    and next_dom:
      "\<And>idx. idx < len div 2 \<Longrightarrow>
        next_dom ! idx = (fri_dom ! idx)\<^sup>2"
    and dom_norm:
      "\<And>idx. idx < len div 2 \<Longrightarrow>
        fri_dom ! idx = (h ^ idx * shift) ^ pw"
    and sampled_cover:
      "\<And>idx. idx < len div 2 \<Longrightarrow>
        \<exists>raw chunk.
          raw mod (len div 2) = idx \<and>
          fri_sampled_table_fold ch len raw pw fri_dom layer chunk
            (next_layer ! idx)"
  shows
    "fri_algebraic_layer_relation len pw ch fri_dom layer next_dom
      next_layer"
  unfolding fri_algebraic_layer_relation_def
proof (intro conjI allI impI)
  show "0 < len"
    by (rule len_pos)
  show "len \<le> length fri_dom"
    by (rule dom_len)
  show "len \<le> length layer"
    by (rule layer_len)
  show "len div 2 \<le> length next_dom"
    by (rule next_dom_len)
  show "len div 2 \<le> length next_layer"
    by (rule next_layer_len)
  fix idx
  assume idx_bound: "idx < len div 2"
  show "next_dom ! idx = (fri_dom ! idx)\<^sup>2"
    by (rule next_dom[OF idx_bound])
  obtain raw chunk where raw_mod: "raw mod (len div 2) = idx"
    and fold:
      "fri_sampled_table_fold ch len raw pw fri_dom layer chunk
        (next_layer ! idx)"
    using sampled_cover[OF idx_bound] by blast
  have fold_eq:
    "next_layer ! idx =
      fri_table_fold_value ch layer fri_dom len pw (raw mod (len div 2))"
    by (rule fri_sampled_table_fold_eq_at_mod_index
        [OF fold even_len round])
      (use dom_norm idx_bound raw_mod in simp)
  then show "next_layer ! idx =
      fri_table_fold_value ch layer fri_dom len pw idx"
    using raw_mod by simp
qed

lemma generic_fri_sampled_layer_chain_bad_challenge_list_from_coverage:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
    and steps:
      "fri_multiround_proximity_steps (length challenges) degree_bound
        (fri_layer_lengths (length challenges) (clength * scale))
        (map (\<lambda>i. 2 ^ i) [0..<length challenges])
        doms layers bad"
    and covers: "fri_sampled_layers_cover_fold_indices roots query_idxs"
    and even_len:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        2 dvd fri_evidence_layer_len roots layer_idx"
    and round_product:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_len roots layer_idx * 2 ^ layer_idx =
          clength * scale"
    and dom_len:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_len roots layer_idx \<le> length (doms ! layer_idx)"
    and layer_len:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_len roots layer_idx \<le>
          length (layers ! layer_idx)"
    and next_dom_len:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_len roots layer_idx div 2 \<le>
          length (doms ! Suc layer_idx)"
    and next_layer_len:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_len roots layer_idx div 2 \<le>
          length (layers ! Suc layer_idx)"
    and next_dom:
      "\<And>layer_idx idx.
        layer_idx < length challenges \<Longrightarrow>
        idx < fri_evidence_layer_len roots layer_idx div 2 \<Longrightarrow>
        doms ! Suc layer_idx ! idx =
          (doms ! layer_idx ! idx)\<^sup>2"
    and dom_norm:
      "\<And>layer_idx idx.
        layer_idx < length challenges \<Longrightarrow>
        idx < fri_evidence_layer_len roots layer_idx div 2 \<Longrightarrow>
        doms ! layer_idx ! idx = (h ^ idx * shift) ^ (2 ^ layer_idx)"
    and start_not_low:
      "\<not> fri_table_low_degree_on degree_bound eval_domain candidate_table"
    and final_low:
      "fri_table_low_degree_on
        (fri_degree_after (length challenges) degree_bound)
        (doms ! length challenges) (layers ! length challenges)"
  shows "challenges \<in>
    generic_fri_bad_challenge_lists (length challenges) bad"
proof -
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have challenges_space: "challenges \<in> fri_challenge_space (length challenges)"
    unfolding fri_challenge_space_def by simp
  have dom0: "doms ! 0 = eval_domain"
    by (rule generic_fri_sampled_layer_chain_evidenceD(4)[OF chain])
  have layer0: "layers ! 0 = candidate_table"
    by (rule generic_fri_sampled_layer_chain_evidenceD(5)[OF chain])
  have relations:
    "\<And>i. i < length challenges \<Longrightarrow>
      fri_algebraic_layer_relation
        (fri_layer_lengths (length challenges) (clength * scale) ! i)
        ((map (\<lambda>i. 2 ^ i) [0..<length challenges]) ! i)
        (challenges ! i) (doms ! i) (layers ! i)
        (doms ! Suc i) (layers ! Suc i)"
  proof -
    fix i
    assume i_bound: "i < length challenges"
    have i_root_bound: "i < length roots"
      using i_bound roots_len by simp
    have len_eq:
      "fri_layer_lengths (length challenges) (clength * scale) ! i =
        fri_evidence_layer_len roots i"
      using roots_len unfolding fri_evidence_layer_len_def by simp
    have pw_eq:
      "(map (\<lambda>i. 2 ^ i) [0..<length challenges]) ! i = 2 ^ i"
      using i_bound by simp
    have sampled_cover:
      "\<And>idx. idx < fri_evidence_layer_len roots i div 2 \<Longrightarrow>
        \<exists>raw chunk.
          raw mod (fri_evidence_layer_len roots i div 2) = idx \<and>
          fri_sampled_table_fold (challenges ! i)
            (fri_evidence_layer_len roots i) raw (2 ^ i)
            (doms ! i) (layers ! i) chunk
            (layers ! Suc i ! idx)"
    proof -
      fix idx
      assume idx_bound: "idx < fri_evidence_layer_len roots i div 2"
      obtain round_idx where round_bound: "round_idx < length query_idxs"
        and idx_eq:
          "fri_evidence_next_idx roots query_idxs round_idx i = idx"
        by (rule fri_sampled_layers_cover_fold_indicesD
            [OF covers i_root_bound idx_bound])
      have sample:
        "fri_sampled_table_fold (challenges ! i)
          (fri_evidence_layer_len roots i)
          (fri_evidence_layer_idx roots query_idxs round_idx i)
          (2 ^ i) (doms ! i) (layers ! i)
          (round_layers ! round_idx ! i)
          (layers ! Suc i !
            fri_evidence_next_idx roots query_idxs round_idx i)"
        by (rule generic_fri_sampled_layer_chain_evidence_sample(2)
            [OF chain round_bound i_bound])
      show "\<exists>raw chunk.
          raw mod (fri_evidence_layer_len roots i div 2) = idx \<and>
          fri_sampled_table_fold (challenges ! i)
            (fri_evidence_layer_len roots i) raw (2 ^ i)
            (doms ! i) (layers ! i) chunk
            (layers ! Suc i ! idx)"
        using sample idx_eq
        unfolding fri_evidence_next_idx_def by blast
    qed
    have len_pos: "0 < fri_evidence_layer_len roots i"
      using round_product[OF i_bound] eval_domain_size_pos
      by (cases "fri_evidence_layer_len roots i") simp_all
    have rel:
      "fri_algebraic_layer_relation
        (fri_evidence_layer_len roots i) (2 ^ i)
        (challenges ! i) (doms ! i) (layers ! i)
        (doms ! Suc i) (layers ! Suc i)"
      by (rule fri_algebraic_layer_relation_from_sampled_coverage
          [OF even_len[OF i_bound] round_product[OF i_bound] len_pos
            dom_len[OF i_bound] layer_len[OF i_bound]
            next_dom_len[OF i_bound] next_layer_len[OF i_bound]])
        (use next_dom[OF i_bound] dom_norm[OF i_bound] sampled_cover
          in simp_all)
    then show
      "fri_algebraic_layer_relation
        (fri_layer_lengths (length challenges) (clength * scale) ! i)
        ((map (\<lambda>i. 2 ^ i) [0..<length challenges]) ! i)
        (challenges ! i) (doms ! i) (layers ! i)
        (doms ! Suc i) (layers ! Suc i)"
      using rel by (simp add: len_eq pw_eq)
  qed
  show ?thesis
    unfolding generic_fri_bad_challenge_lists_def
    by (rule fri_multiround_proximity_skeleton
        [OF steps challenges_space relations])
      (use start_not_low final_low dom0 layer0 in simp_all)
qed

lemma generic_fri_sampled_layer_chain_full_cover_bad_challenge_list:
  assumes
    "generic_fri_sampled_layer_chain_full_cover low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
  shows "challenges \<in>
    generic_fri_bad_challenge_lists (length challenges) bad"
proof -
  have chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
    and steps:
      "fri_multiround_proximity_steps (length challenges) degree_bound
        (fri_layer_lengths (length challenges) (clength * scale))
        (map (\<lambda>i. 2 ^ i) [0..<length challenges])
        doms layers bad"
    and covers: "fri_sampled_layers_cover_fold_indices roots query_idxs"
    and even_len:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        2 dvd fri_evidence_layer_len roots layer_idx"
    and round_product:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_len roots layer_idx * 2 ^ layer_idx =
          clength * scale"
    and dom_len:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_len roots layer_idx \<le>
          length (doms ! layer_idx)"
    and layer_len:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_len roots layer_idx \<le>
          length (layers ! layer_idx)"
    and next_dom_len:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_len roots layer_idx div 2 \<le>
          length (doms ! Suc layer_idx)"
    and next_layer_len:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_len roots layer_idx div 2 \<le>
          length (layers ! Suc layer_idx)"
    and next_dom:
      "\<And>layer_idx idx.
        layer_idx < length challenges \<Longrightarrow>
        idx < fri_evidence_layer_len roots layer_idx div 2 \<Longrightarrow>
        doms ! Suc layer_idx ! idx =
          (doms ! layer_idx ! idx)\<^sup>2"
    and dom_norm:
      "\<And>layer_idx idx.
        layer_idx < length challenges \<Longrightarrow>
        idx < fri_evidence_layer_len roots layer_idx div 2 \<Longrightarrow>
        doms ! layer_idx ! idx = (h ^ idx * shift) ^ (2 ^ layer_idx)"
    and start_not_low:
      "\<not> fri_table_low_degree_on degree_bound eval_domain candidate_table"
    and final_low:
      "fri_table_low_degree_on
        (fri_degree_after (length challenges) degree_bound)
        (doms ! length challenges) (layers ! length challenges)"
    using assms
    unfolding generic_fri_sampled_layer_chain_full_cover_def
    by blast+
  show ?thesis
    by (rule generic_fri_sampled_layer_chain_bad_challenge_list_from_coverage
        [OF chain steps covers even_len round_product dom_len layer_len
          next_dom_len next_layer_len next_dom dom_norm start_not_low
          final_low])
qed

lemma generic_fri_bad_candidate_from_sampled_layer_chain_full_cover:
  assumes cover:
    "generic_fri_sampled_layer_chain_full_cover low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
    and not_low: "\<not> low_degree candidate_table"
  shows
    "generic_fri_bad_candidate low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers bad"
proof -
  have sampled:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
    using cover
    unfolding generic_fri_sampled_layer_chain_full_cover_def by blast
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF sampled])
  have bad:
    "challenges \<in> generic_fri_bad_challenge_lists (length challenges) bad"
    by (rule generic_fri_sampled_layer_chain_full_cover_bad_challenge_list
        [OF cover])
  show ?thesis
    unfolding generic_fri_bad_candidate_def
    using partial not_low bad by simp
qed

lemma generic_fri_canonical_opening_match_sample:
  assumes openings:
      "fri_all_round_openings_match_tables
        (take (length challenges) layers) query_idxs round_layers"
    and layers_len: "length layers = Suc (length challenges)"
    and roots_len: "length challenges = length roots"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
  obtains xp xp_path xn xn_path
  where
    "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
      xp xp_path xn xn_path (round_layers ! round_idx ! layer_idx)"
    and "fri_opening_matches_table
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (layers ! layer_idx) xp xn"
proof -
  have layer_bound_take:
    "layer_idx < length (take (length challenges) layers)"
    using layer_bound layers_len by simp
  have openings_match:
    "fri_layer_opening_matches_bound_table (query_idxs ! round_idx)
      layer_idx (take (length challenges) layers)
      (round_layers ! round_idx)"
    by (rule fri_all_round_openings_match_tablesD
        [OF openings round_bound layer_bound_take])
  have tables_len:
    "length (take (length challenges) layers) = length roots"
    using layers_len roots_len by simp
  from fri_layer_opening_matches_bound_table_compactE
      [OF openings_match tables_len]
  obtain xp xp_path xn xn_path where
    chunk:
      "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
        xp xp_path xn xn_path (round_layers ! round_idx ! layer_idx)"
    and table_match_take:
      "fri_opening_matches_table
        (fri_evidence_layer_len roots layer_idx)
        (fri_layer_indices (length roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx)
        (take (length challenges) layers ! layer_idx) xp xn"
    by blast
  have idx_eq:
    "fri_layer_indices (length roots) (query_idxs ! round_idx)
      (clength * scale) ! layer_idx =
     fri_evidence_layer_idx roots query_idxs round_idx layer_idx"
    unfolding fri_evidence_layer_idx_def by simp
  have table_eq:
    "take (length challenges) layers ! layer_idx = layers ! layer_idx"
    using layer_bound layers_len by simp
  have table_match:
    "fri_opening_matches_table
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (layers ! layer_idx) xp xn"
    using table_match_take idx_eq table_eq by simp
  show ?thesis
    by (rule that[OF chunk table_match])
qed

lemma generic_fri_canonical_sampled_fold_at_first_half:
  assumes chain:
    "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
    and openings:
      "fri_all_round_openings_match_tables
        (take (length challenges) layers) query_idxs round_layers"
    and domains: "fri_sampled_domains_align roots query_idxs doms"
    and idx_bound:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
        fri_evidence_layer_len roots layer_idx div 2"
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
      (doms ! layer_idx)
      (layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (layers ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
proof -
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    using chain unfolding generic_fri_canonical_layer_chain_evidence_def
    by simp
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have layers_len: "length layers = Suc (length challenges)"
    by (rule generic_fri_canonical_layer_chain_lengths(2)[OF chain])
  have len_eq:
    "fri_layer_lengths (length challenges) (clength * scale) ! layer_idx =
      fri_evidence_layer_len roots layer_idx"
    using roots_len unfolding fri_evidence_layer_len_def by simp
  have relation:
    "fri_algebraic_layer_relation
      (fri_evidence_layer_len roots layer_idx)
      (2 ^ layer_idx)
      (challenges ! layer_idx) (doms ! layer_idx) (layers ! layer_idx)
      (doms ! Suc layer_idx) (layers ! Suc layer_idx)"
    using generic_fri_canonical_layer_chain_relation
      [OF chain layer_bound] len_eq by simp
  have dom_idx:
    "doms ! layer_idx !
      fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
     (h ^ fri_evidence_layer_idx roots query_idxs round_idx layer_idx *
      shift) ^ (2 ^ layer_idx)"
    by (rule fri_sampled_domains_alignD[OF domains round_bound])
      (use layer_bound roots_len in simp)
  obtain xp xp_path xn xn_path where
    chunk:
      "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
        xp xp_path xn xn_path (round_layers ! round_idx ! layer_idx)"
    and match:
      "fri_opening_matches_table
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (layers ! layer_idx) xp xn"
    by (rule generic_fri_canonical_opening_match_sample
        [OF openings layers_len roots_len round_bound layer_bound])
  have next_idx_eq:
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx =
      fri_evidence_layer_idx roots query_idxs round_idx layer_idx"
    using idx_bound unfolding fri_evidence_next_idx_def by simp
  have idx_len_orig:
    "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
      length (layers ! Suc layer_idx)"
    by (rule fri_sampled_table_fold_from_algebraic_relation(1)
        [OF relation idx_bound chunk match dom_idx])
  then show
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      length (layers ! Suc layer_idx)"
    using next_idx_eq by simp
  have fold_orig:
    "fri_sampled_table_fold
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (doms ! layer_idx)
      (layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (layers ! Suc layer_idx !
        fri_evidence_layer_idx roots query_idxs round_idx layer_idx)"
    by (rule fri_sampled_table_fold_from_algebraic_relation
        [OF relation idx_bound chunk match dom_idx])
  then show
    "fri_sampled_table_fold
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (doms ! layer_idx)
      (layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (layers ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
    using next_idx_eq by simp
qed

lemma generic_fri_canonical_sampled_fold_at_any_index:
  assumes chain:
    "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
    and openings:
      "fri_all_round_openings_match_tables
        (take (length challenges) layers) query_idxs round_layers"
    and domains: "fri_sampled_domains_align roots query_idxs doms"
    and even_len: "2 dvd fri_evidence_layer_len roots layer_idx"
    and round:
      "fri_evidence_layer_len roots layer_idx * 2 ^ layer_idx =
        clength * scale"
    and dom_norm:
      "doms ! layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx =
       (h ^ fri_evidence_next_idx roots query_idxs round_idx layer_idx *
        shift) ^ (2 ^ layer_idx)"
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
      (doms ! layer_idx)
      (layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (layers ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
proof -
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    using chain unfolding generic_fri_canonical_layer_chain_evidence_def
    by simp
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have layers_len: "length layers = Suc (length challenges)"
    by (rule generic_fri_canonical_layer_chain_lengths(2)[OF chain])
  have len_eq:
    "fri_layer_lengths (length challenges) (clength * scale) ! layer_idx =
      fri_evidence_layer_len roots layer_idx"
    using roots_len unfolding fri_evidence_layer_len_def by simp
  have relation:
    "fri_algebraic_layer_relation
      (fri_evidence_layer_len roots layer_idx)
      (2 ^ layer_idx)
      (challenges ! layer_idx) (doms ! layer_idx) (layers ! layer_idx)
      (doms ! Suc layer_idx) (layers ! Suc layer_idx)"
    using generic_fri_canonical_layer_chain_relation
      [OF chain layer_bound] len_eq by simp
  have dom_raw:
    "doms ! layer_idx !
      fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
     (h ^ fri_evidence_layer_idx roots query_idxs round_idx layer_idx *
      shift) ^ (2 ^ layer_idx)"
    by (rule fri_sampled_domains_alignD[OF domains round_bound])
      (use layer_bound roots_len in simp)
  obtain xp xp_path xn xn_path where
    chunk:
      "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
        xp xp_path xn xn_path (round_layers ! round_idx ! layer_idx)"
    and match:
      "fri_opening_matches_table
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (layers ! layer_idx) xp xn"
    by (rule generic_fri_canonical_opening_match_sample
        [OF openings layers_len roots_len round_bound layer_bound])
  show
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      length (layers ! Suc layer_idx)"
    unfolding fri_evidence_next_idx_def
    by (rule fri_sampled_table_fold_from_algebraic_relation_mod_index(1)
        [OF relation even_len round chunk match dom_raw])
      (use dom_norm fri_evidence_next_idx_def in simp)
  show
    "fri_sampled_table_fold
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (doms ! layer_idx)
      (layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (layers ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
    unfolding fri_evidence_next_idx_def
    by (rule fri_sampled_table_fold_from_algebraic_relation_mod_index(2)
        [OF relation even_len round chunk match dom_raw])
      (use dom_norm fri_evidence_next_idx_def in simp)
qed

lemma generic_fri_canonical_sampled_raw_domain_power:
  assumes chain:
    "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
    and openings:
      "fri_all_round_openings_match_tables
        (take (length challenges) layers) query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
  shows
    "doms ! layer_idx !
        fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
      (h ^ fri_evidence_layer_idx roots query_idxs round_idx layer_idx *
        shift) ^ (2 ^ layer_idx)"
proof -
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    using chain unfolding generic_fri_canonical_layer_chain_evidence_def
    by simp
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have layers_len: "length layers = Suc (length challenges)"
    by (rule generic_fri_canonical_layer_chain_lengths(2)[OF chain])
  obtain xp xp_path xn xn_path where match:
    "fri_opening_matches_table
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (layers ! layer_idx) xp xn"
    by (rule generic_fri_canonical_opening_match_sample
        [OF openings layers_len roots_len round_bound layer_bound])
  have idx_bound:
    "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
      fri_evidence_layer_len roots layer_idx"
    by (rule fri_opening_matches_tableD(1)[OF match])
  show ?thesis
    by (rule generic_fri_canonical_domain_power
        [OF chain roots_len layer_bound idx_bound])
qed

lemma generic_fri_canonical_layer_chain_as_sampled:
  assumes chain:
    "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
    and openings:
      "fri_all_round_openings_match_tables
        (take (length challenges) layers) query_idxs round_layers"
    and domains: "fri_sampled_domains_align roots query_idxs doms"
    and next_domains: "fri_sampled_next_domains_align roots query_idxs doms"
    and even_len:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        2 dvd fri_evidence_layer_len roots layer_idx"
    and round:
      "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_len roots layer_idx * 2 ^ layer_idx =
          clength * scale"
  shows
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
proof -
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    using chain unfolding generic_fri_canonical_layer_chain_evidence_def
    by simp
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have doms_len: "length doms = Suc (length challenges)"
    by (rule generic_fri_canonical_layer_chain_lengths(1)[OF chain])
  have layers_len: "length layers = Suc (length challenges)"
    by (rule generic_fri_canonical_layer_chain_lengths(2)[OF chain])
  have dom0: "doms ! 0 = eval_domain"
    using chain unfolding generic_fri_canonical_layer_chain_evidence_def
    by simp
  have layer0: "layers ! 0 = candidate_table"
    using chain unfolding generic_fri_canonical_layer_chain_evidence_def
    by simp
  have final:
    "fri_final_constant_consistent (layers ! length challenges) final_value"
    using chain unfolding generic_fri_canonical_layer_chain_evidence_def
    by simp
  have sampled:
    "\<And>round_idx layer_idx.
      round_idx < length query_idxs \<Longrightarrow>
      layer_idx < length challenges \<Longrightarrow>
      fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        length (layers ! Suc layer_idx) \<and>
      fri_sampled_table_fold
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (doms ! layer_idx)
        (layers ! layer_idx)
        (round_layers ! round_idx ! layer_idx)
        (layers ! Suc layer_idx !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
  proof -
    fix round_idx layer_idx
    assume round_bound: "round_idx < length query_idxs"
      and layer_bound: "layer_idx < length challenges"
    have layer_bound_roots: "layer_idx < length roots"
      using layer_bound roots_len by simp
    have dom_norm:
      "doms ! layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx =
       (h ^ fri_evidence_next_idx roots query_idxs round_idx layer_idx *
        shift) ^ (2 ^ layer_idx)"
      by (rule fri_sampled_next_domains_alignD
          [OF next_domains round_bound layer_bound_roots])
    show
      "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        length (layers ! Suc layer_idx) \<and>
      fri_sampled_table_fold
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (doms ! layer_idx)
        (layers ! layer_idx)
        (round_layers ! round_idx ! layer_idx)
        (layers ! Suc layer_idx !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
      by (intro conjI)
        (rule generic_fri_canonical_sampled_fold_at_any_index
          [OF chain openings domains even_len[OF layer_bound]
            round[OF layer_bound] dom_norm round_bound layer_bound])+
  qed
  show ?thesis
    unfolding generic_fri_sampled_layer_chain_evidence_def
    using partial doms_len layers_len dom0 layer0 final sampled by blast
qed

lemma generic_fri_bad_challenge_lists_subset:
  "generic_fri_bad_challenge_lists n bad \<subseteq> fri_challenge_space n"
  unfolding generic_fri_bad_challenge_lists_def
  by (rule fri_multiround_bad_challenge_lists_subset)

lemma generic_fri_bad_challenge_lists_round_union:
  "generic_fri_bad_challenge_lists n bad =
    (\<Union>i \<in> {..<n}. generic_fri_round_bad_challenge_lists n bad i)"
  unfolding generic_fri_bad_challenge_lists_def
    fri_multiround_bad_challenge_lists_def
    generic_fri_round_bad_challenge_lists_def
  by auto

lemma generic_fri_round_bad_challenge_lists_image_subset:
  "generic_fri_round_bad_challenge_lists n bad i \<subseteq>
    (\<lambda>(prefix, b, suffix). prefix @ b # suffix) `
      generic_fri_round_bad_witnesses n bad i"
proof
  fix bs
  assume bs_in: "bs \<in> generic_fri_round_bad_challenge_lists n bad i"
  then have bs_space: "bs \<in> fri_challenge_space n"
    and i_bound: "i < n"
    and hit: "bs ! i \<in> bad i (take i bs)"
    unfolding generic_fri_round_bad_challenge_lists_def by simp_all
  have len_bs: "length bs = n"
    using bs_space unfolding fri_challenge_space_def by simp
  let ?prefix = "take i bs"
  let ?b = "bs ! i"
  let ?suffix = "drop (Suc i) bs"
  have witness:
    "(?prefix, ?b, ?suffix) \<in> generic_fri_round_bad_witnesses n bad i"
    unfolding generic_fri_round_bad_witnesses_def
    using i_bound hit len_bs by simp
  have bs_eq: "bs = ?prefix @ ?b # ?suffix"
    using i_bound len_bs by (simp add: id_take_nth_drop)
  show "bs \<in> (\<lambda>(prefix, b, suffix). prefix @ b # suffix) `
      generic_fri_round_bad_witnesses n bad i"
    using witness bs_eq by force
qed

lemma generic_fri_round_bad_witnesses_subset:
  "generic_fri_round_bad_witnesses n bad i \<subseteq>
    {(prefix, b, suffix).
      length prefix = i \<and>
      b \<in> bad i prefix \<and>
      length suffix = n - Suc i}"
  unfolding generic_fri_round_bad_witnesses_def by auto

lemma generic_fri_bad_challenge_lists_card_bound_by_rounds:
  "card (generic_fri_bad_challenge_lists n bad) \<le>
    (\<Sum>i \<in> {..<n}. card (generic_fri_round_bad_challenge_lists n bad i))"
  unfolding generic_fri_bad_challenge_lists_round_union
  by (rule card_UN_le) simp

lemma generic_fri_bad_challenge_lists_bounded_byI:
  assumes card_bound: "card (generic_fri_bad_challenge_lists n bad) \<le> bd"
  shows "fri_bad_challenge_lists_bounded_by n
    (generic_fri_bad_challenge_lists n bad) bd"
  unfolding fri_bad_challenge_lists_bounded_by_def
  using generic_fri_bad_challenge_lists_subset card_bound by simp

lemma generic_fri_round_bad_witnesses_finite:
  "finite (generic_fri_round_bad_witnesses n bad i)"
proof -
  let ?P = "{prefix :: 'f list. length prefix = i}"
  let ?S = "{suffix :: 'f list. length suffix = n - Suc i}"
  have witness_eq:
    "generic_fri_round_bad_witnesses n bad i =
      (if i < n then (SIGMA prefix:?P. bad i prefix \<times> ?S) else {})"
    unfolding generic_fri_round_bad_witnesses_def by auto
  show ?thesis
  proof (cases "i < n")
    case True
    have finite_P: "finite ?P"
      by (rule finite_length_lists_UNIV)
    have finite_S: "finite ?S"
      by (rule finite_length_lists_UNIV)
    have finite_sigma: "finite (SIGMA prefix:?P. bad i prefix \<times> ?S)"
      by (rule finite_SigmaI[OF finite_P]) (use finite_S in simp)
    then show ?thesis
      using True witness_eq by simp
  next
    case False
    then show ?thesis
      using witness_eq by simp
  qed
qed

lemma generic_fri_round_bad_witnesses_card_bound:
  assumes local_bound:
    "\<And>prefix. length prefix = i \<Longrightarrow> card (bad i prefix) \<le> bd"
  shows "card (generic_fri_round_bad_witnesses n bad i) \<le>
    CARD('f) ^ i * bd * CARD('f) ^ (n - Suc i)"
proof -
  let ?P = "{prefix :: 'f list. length prefix = i}"
  let ?S = "{suffix :: 'f list. length suffix = n - Suc i}"
  have witness_eq:
    "generic_fri_round_bad_witnesses n bad i =
      (if i < n then (SIGMA prefix:?P. bad i prefix \<times> ?S) else {})"
    unfolding generic_fri_round_bad_witnesses_def by auto
  show ?thesis
  proof (cases "i < n")
    case False
    then show ?thesis
      using witness_eq by simp
  next
    case True
    have finite_P: "finite ?P"
      by (rule finite_length_lists_UNIV)
    have finite_S: "finite ?S"
      by (rule finite_length_lists_UNIV)
    have finite_products: "\<forall>prefix \<in> ?P. finite (bad i prefix \<times> ?S)"
      using finite_S by simp
    have card_witness:
      "card (generic_fri_round_bad_witnesses n bad i) =
        (\<Sum>prefix \<in> ?P. card (bad i prefix \<times> ?S))"
    proof -
      have "card (SIGMA prefix:?P. bad i prefix \<times> ?S) =
          (\<Sum>prefix \<in> ?P. card (bad i prefix \<times> ?S))"
        by (rule card_SigmaI[OF finite_P finite_products])
      then show ?thesis
        using True witness_eq by simp
    qed
    also have "... \<le> (\<Sum>prefix \<in> ?P.
        card (bad i prefix) * CARD('f) ^ (n - Suc i))"
    proof (rule sum_mono)
      fix prefix
      assume "prefix \<in> ?P"
      have "card (bad i prefix \<times> ?S) =
          card (bad i prefix) * card ?S"
        by (simp add: card_cartesian_product)
      also have "... =
          card (bad i prefix) * CARD('f) ^ (n - Suc i)"
        by (simp add: card_length_lists_UNIV)
      finally show "card (bad i prefix \<times> ?S) \<le>
        card (bad i prefix) * CARD('f) ^ (n - Suc i)"
        by simp
    qed
    also have "... \<le> (\<Sum>prefix \<in> ?P.
        bd * CARD('f) ^ (n - Suc i))"
    proof (rule sum_mono)
      fix prefix
      assume prefix_in: "prefix \<in> ?P"
      have "card (bad i prefix) \<le> bd"
        by (rule local_bound) (use prefix_in in simp)
      then show "card (bad i prefix) * CARD('f) ^ (n - Suc i)
        \<le> bd * CARD('f) ^ (n - Suc i)"
        by simp
    qed
    also have "... = card ?P * (bd * CARD('f) ^ (n - Suc i))"
      by simp
    also have "... = CARD('f) ^ i * bd * CARD('f) ^ (n - Suc i)"
      by (simp add: card_length_lists_UNIV mult.assoc)
    finally show ?thesis
      using card_witness by simp
  qed
qed

lemma generic_fri_round_bad_challenge_lists_card_bound:
  assumes local_bound:
    "\<And>prefix. length prefix = i \<Longrightarrow> card (bad i prefix) \<le> bd"
  shows "card (generic_fri_round_bad_challenge_lists n bad i) \<le>
    CARD('f) ^ i * bd * CARD('f) ^ (n - Suc i)"
proof -
  have image_subset:
    "generic_fri_round_bad_challenge_lists n bad i \<subseteq>
      (\<lambda>(prefix, b, suffix). prefix @ b # suffix) `
        generic_fri_round_bad_witnesses n bad i"
    by (rule generic_fri_round_bad_challenge_lists_image_subset)
  have finite_image:
    "finite ((\<lambda>(prefix, b, suffix). prefix @ b # suffix) `
        generic_fri_round_bad_witnesses n bad i)"
    by (rule finite_imageI)
      (rule generic_fri_round_bad_witnesses_finite)
  have "card (generic_fri_round_bad_challenge_lists n bad i) \<le>
      card ((\<lambda>(prefix, b, suffix). prefix @ b # suffix) `
        generic_fri_round_bad_witnesses n bad i)"
    by (rule card_mono[OF finite_image image_subset])
  also have "... \<le> card (generic_fri_round_bad_witnesses n bad i)"
    by (rule card_image_le)
      (rule generic_fri_round_bad_witnesses_finite)
  also have "... \<le> CARD('f) ^ i * bd * CARD('f) ^ (n - Suc i)"
    by (rule generic_fri_round_bad_witnesses_card_bound)
      (rule local_bound)
  finally show ?thesis .
qed

lemma generic_fri_bad_challenge_lists_card_bound_from_round_bounds:
  assumes local_bound:
    "\<And>i prefix. i < n \<Longrightarrow> length prefix = i \<Longrightarrow>
      card (bad i prefix) \<le> bd i"
  shows "card (generic_fri_bad_challenge_lists n bad) \<le>
    (\<Sum>i \<in> {..<n}. CARD('f) ^ i * bd i * CARD('f) ^ (n - Suc i))"
proof -
  have "card (generic_fri_bad_challenge_lists n bad) \<le>
      (\<Sum>i \<in> {..<n}. card (generic_fri_round_bad_challenge_lists n bad i))"
    by (rule generic_fri_bad_challenge_lists_card_bound_by_rounds)
  also have "... \<le>
      (\<Sum>i \<in> {..<n}. CARD('f) ^ i * bd i * CARD('f) ^ (n - Suc i))"
  proof (rule sum_mono)
    fix i
    assume i_in: "i \<in> {..<n}"
    show "card (generic_fri_round_bad_challenge_lists n bad i) \<le>
      CARD('f) ^ i * bd i * CARD('f) ^ (n - Suc i)"
      by (rule generic_fri_round_bad_challenge_lists_card_bound)
        (rule local_bound[of i], use i_in in simp_all)
  qed
  finally show ?thesis .
qed

lemma generic_fri_bad_challenge_lists_bounded_by_from_round_bounds:
  assumes local_bound:
    "\<And>i prefix. i < n \<Longrightarrow> length prefix = i \<Longrightarrow>
      card (bad i prefix) \<le> bd i"
  shows "fri_bad_challenge_lists_bounded_by n
    (generic_fri_bad_challenge_lists n bad)
    (\<Sum>i \<in> {..<n}. CARD('f) ^ i * bd i * CARD('f) ^ (n - Suc i))"
  by (rule generic_fri_bad_challenge_lists_bounded_byI)
    (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds
      [OF local_bound])

lemma generic_fri_bad_challenge_lists_card_bound:
  "card (generic_fri_bad_challenge_lists n bad) \<le> CARD('f) ^ n"
  unfolding generic_fri_bad_challenge_lists_def
  by (rule fri_multiround_bad_challenge_lists_card_bound)

lemma generic_fri_bad_challenge_lists_bounded_by:
  "fri_bad_challenge_lists_bounded_by n
    (generic_fri_bad_challenge_lists n bad) (CARD('f) ^ n)"
  unfolding generic_fri_bad_challenge_lists_def
  by (rule fri_multiround_bad_challenge_lists_bounded_by)

lemma generic_fri_low_degree_bad_challenge_listI:
  assumes steps:
      "fri_multiround_proximity_steps n d lens pws doms layers bad"
    and challenges: "bs \<in> fri_challenge_space n"
    and relations:
      "\<And>i. i < n \<Longrightarrow>
        fri_algebraic_layer_relation (lens ! i) (pws ! i) (bs ! i)
          (doms ! i) (layers ! i) (doms ! Suc i) (layers ! Suc i)"
    and start_not_low:
      "\<not> fri_table_low_degree_on d (doms ! 0) (layers ! 0)"
    and final_low:
      "fri_table_low_degree_on (fri_degree_after n d) (doms ! n)
        (layers ! n)"
  shows "bs \<in> generic_fri_bad_challenge_lists n bad"
  unfolding generic_fri_bad_challenge_lists_def
  by (rule fri_multiround_proximity_skeleton
      [OF steps challenges relations start_not_low final_low])

lemma generic_fri_proximity_evidence_bad_challenge_list:
  assumes "generic_fri_proximity_evidence n d lens pws doms layers bs bad"
  shows "bs \<in> generic_fri_bad_challenge_lists n bad"
proof -
  have steps:
      "fri_multiround_proximity_steps n d lens pws doms layers bad"
    and challenges: "bs \<in> fri_challenge_space n"
    and relations:
      "\<And>i. i < n \<Longrightarrow>
        fri_algebraic_layer_relation (lens ! i) (pws ! i) (bs ! i)
          (doms ! i) (layers ! i) (doms ! Suc i) (layers ! Suc i)"
    and start_not_low:
      "\<not> fri_table_low_degree_on d (doms ! 0) (layers ! 0)"
    and final_low:
      "fri_table_low_degree_on (fri_degree_after n d) (doms ! n)
        (layers ! n)"
    using assms unfolding generic_fri_proximity_evidence_def by blast+
  show ?thesis
    by (rule generic_fri_low_degree_bad_challenge_listI
        [OF steps challenges relations start_not_low final_low])
qed

lemma generic_fri_canonical_layer_chain_bad_challenge_list:
  assumes
    "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
  shows "challenges \<in>
    generic_fri_bad_challenge_lists (length challenges) bad"
proof -
  have "generic_fri_proximity_evidence (length challenges) degree_bound
      (fri_layer_lengths (length challenges) (clength * scale))
      (map (\<lambda>i. 2 ^ i) [0..<length challenges])
      doms layers challenges bad"
    using assms
    unfolding generic_fri_canonical_layer_chain_evidence_def by simp
  then show ?thesis
    by (rule generic_fri_proximity_evidence_bad_challenge_list)
qed

lemma generic_fri_canonical_layer_chain_evidenceD:
  assumes
    "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
  shows
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    "doms ! 0 = eval_domain"
    "layers ! 0 = candidate_table"
    "fri_final_constant_consistent (layers ! length challenges) final_value"
    "generic_fri_proximity_evidence (length challenges) degree_bound
      (fri_layer_lengths (length challenges) (clength * scale))
      (map (\<lambda>i. 2 ^ i) [0..<length challenges])
      doms layers challenges bad"
  using assms unfolding generic_fri_canonical_layer_chain_evidence_def
  by simp_all

lemma generic_fri_bad_candidate_from_canonical_layer_chain:
  assumes chain:
    "generic_fri_canonical_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
    and not_low: "\<not> low_degree candidate_table"
  shows
    "generic_fri_bad_candidate low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers bad"
proof -
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_canonical_layer_chain_evidenceD(1)[OF chain])
  have bad:
    "challenges \<in>
      generic_fri_bad_challenge_lists (length challenges) bad"
    by (rule generic_fri_canonical_layer_chain_bad_challenge_list[OF chain])
  show ?thesis
    unfolding generic_fri_bad_candidate_def
    using partial not_low bad by simp
qed

lemma generic_fri_bad_challenge_lists_mono:
  assumes mono:
    "\<And>i prefix. i < n \<Longrightarrow> length prefix = i \<Longrightarrow>
      bad i prefix \<subseteq> bad' i prefix"
  shows "generic_fri_bad_challenge_lists n bad \<subseteq>
    generic_fri_bad_challenge_lists n bad'"
proof
  fix bs
  assume bs_in: "bs \<in> generic_fri_bad_challenge_lists n bad"
  then have space: "bs \<in> fri_challenge_space n"
    unfolding generic_fri_bad_challenge_lists_def
    using fri_multiround_bad_challenge_lists_subset by blast
  from bs_in obtain i where i_bound: "i < n"
    and hit: "bs ! i \<in> bad i (take i bs)"
    unfolding generic_fri_bad_challenge_lists_def
      fri_multiround_bad_challenge_lists_def
    by blast
  have len_bs: "length bs = n"
    using space unfolding fri_challenge_space_def by simp
  have len_take: "length (take i bs) = i"
    using i_bound len_bs by simp
  have "bs ! i \<in> bad' i (take i bs)"
    using hit mono[OF i_bound len_take] by blast
  then show "bs \<in> generic_fri_bad_challenge_lists n bad'"
    using space i_bound
    unfolding generic_fri_bad_challenge_lists_def
      fri_multiround_bad_challenge_lists_def
    by blast
qed

lemma generic_fri_bad_candidateD:
  assumes "generic_fri_bad_candidate low_degree candidate_table degree_bound
    roots challenges final_value query_idxs round_layers bad"
  shows "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    and "\<not> low_degree candidate_table"
    and "challenges \<in> generic_fri_bad_challenge_lists (length challenges) bad"
  using assms unfolding generic_fri_bad_candidate_def by simp_all

lemma generic_fri_bad_candidate_challenges_in_space:
  assumes bad_candidate:
    "generic_fri_bad_candidate low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers bad"
  shows "challenges \<in> fri_challenge_space (length challenges)"
proof -
  have "challenges \<in> generic_fri_bad_challenge_lists (length challenges) bad"
    using generic_fri_bad_candidateD(3)[OF bad_candidate] .
  then show ?thesis
    using generic_fri_bad_challenge_lists_subset[of "length challenges" bad]
    by blast
qed

lemma generic_fri_bad_candidate_challenges_length:
  assumes bad_candidate:
    "generic_fri_bad_candidate low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers bad"
  shows "length challenges = fri_round_count_for_degree_bound degree_bound"
proof -
  have evidence:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    using generic_fri_bad_candidateD(1)[OF bad_candidate] .
  then show ?thesis
    using generic_fri_partial_evidence_shapes(1,2)[OF evidence] by simp
qed

lemma trace_table_low_degree_iff_fri_table_low_degree_on_eval_domain:
  "trace_table_low_degree trace_table \<longleftrightarrow>
    fri_table_low_degree_on (clength - 1) eval_domain trace_table"
proof
  assume "trace_table_low_degree trace_table"
  then obtain f where deg_f: "degree f < clength"
    and table: "trace_table = map (poly f) eval_domain"
    unfolding trace_table_low_degree_def by blast
  have "degree f \<le> clength - 1"
    using deg_f by simp
  then show "fri_table_low_degree_on (clength - 1) eval_domain trace_table"
    unfolding fri_table_low_degree_on_def
    using table by blast
next
  assume "fri_table_low_degree_on (clength - 1) eval_domain trace_table"
  then obtain p where deg_p: "degree p \<le> clength - 1"
    and table: "trace_table = map (poly p) eval_domain"
    unfolding fri_table_low_degree_on_def by blast
  have "degree p < clength"
    using deg_p clength_pos by simp
  then show "trace_table_low_degree trace_table"
    unfolding trace_table_low_degree_def
    using table by blast
qed

lemma composition_table_low_degree_iff_fri_table_low_degree_on_eval_domain:
  "composition_table_low_degree d composition_table \<longleftrightarrow>
    fri_table_low_degree_on d eval_domain composition_table"
  unfolding composition_table_low_degree_def fri_table_low_degree_on_def
  by simp

lemma composition_table_low_degree_mono:
  assumes "d \<le> d'"
    and "composition_table_low_degree d composition_table"
  shows "composition_table_low_degree d' composition_table"
proof -
  from assms(2) obtain q where deg_q: "degree q \<le> d"
    and table: "composition_table = map (poly q) eval_domain"
    unfolding composition_table_low_degree_def by blast
  have "degree q \<le> d'"
    using deg_q assms(1) by simp
  then show ?thesis
    unfolding composition_table_low_degree_def
    using table by blast
qed

lemma composition_table_not_low_degree_mono:
  assumes "d \<le> d'"
    and "\<not> composition_table_low_degree d' composition_table"
  shows "\<not> composition_table_low_degree d composition_table"
  using composition_table_low_degree_mono[OF assms(1)] assms(2) by blast

lemma trace_table_not_low_degree_iff_not_fri_table_low_degree_on_eval_domain:
  "\<not> trace_table_low_degree trace_table \<longleftrightarrow>
    \<not> fri_table_low_degree_on (clength - 1) eval_domain trace_table"
  by (simp add: trace_table_low_degree_iff_fri_table_low_degree_on_eval_domain)

lemma composition_table_not_low_degree_iff_not_fri_table_low_degree_on_eval_domain:
  "\<not> composition_table_low_degree d composition_table \<longleftrightarrow>
    \<not> fri_table_low_degree_on d eval_domain composition_table"
  by (simp add:
      composition_table_low_degree_iff_fri_table_low_degree_on_eval_domain)

lemma accepted_fri_opening_transcript_trace_generic_partial_evidence:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
  shows
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final query_idxs
      trace_round_layers"
proof -
  have count:
    "length trace_roots = fri_round_count_for_degree_bound (clength - 1)"
    using accepted_fri_opening_transcript_algebraic_round_counts(1)
      [OF fri_openings]
    by (simp add: trace_fri_algebraic_round_count_def)
  have len_bs: "length trace_bs = length trace_roots"
    using accepted_fri_opening_transcript_shapes[OF fri_openings] by blast
  have layers:
    "fri_all_round_layer_evidence trace_roots trace_bs query_idxs
      trace_round_layers"
    by (rule accepted_fri_opening_transcript_trace_all_round_layer_evidence
        [OF fri_openings])
  show ?thesis
    unfolding generic_fri_partial_evidence_def
    using count len_bs layers by simp
qed

lemma accepted_fri_opening_transcript_composition_generic_partial_evidence:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
  shows
    "generic_fri_partial_evidence (composition_table_low_degree (to_nat dg))
      composition_table (to_nat dg) composition_roots composition_bs
      composition_final query_idxs composition_round_layers"
proof -
  have count:
    "length composition_roots = fri_round_count_for_degree_bound (to_nat dg)"
    using accepted_fri_opening_transcript_algebraic_round_counts(3)
      [OF fri_openings]
    by (simp add: composition_fri_algebraic_round_count_def)
  have len_bs: "length composition_bs = length composition_roots"
    using accepted_fri_opening_transcript_shapes[OF fri_openings] by blast
  have layers:
    "fri_all_round_layer_evidence composition_roots composition_bs query_idxs
      composition_round_layers"
    by (rule
        accepted_fri_opening_transcript_composition_all_round_layer_evidence
        [OF fri_openings])
  show ?thesis
    unfolding generic_fri_partial_evidence_def
    using count len_bs layers by simp
qed

lemma trace_fri_partial_candidate_opening_evidence_generic_partial:
  assumes evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
  shows
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
proof -
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    using trace_fri_partial_candidate_opening_evidenceD(1)[OF evidence] .
  show ?thesis
    by (rule accepted_fri_opening_transcript_trace_generic_partial_evidence
        [OF fri_openings])
qed

lemma composition_fri_partial_candidate_opening_evidence_generic_partial:
  assumes evidence:
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
  shows
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat fri_dg))
      composition_table (to_nat fri_dg) opening_composition_roots
      composition_bs composition_final fri_query_idxs
      composition_round_layers"
proof -
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    using composition_fri_partial_candidate_opening_evidenceD(1)
      [OF evidence] .
  show ?thesis
    by (rule
        accepted_fri_opening_transcript_composition_generic_partial_evidence
        [OF fri_openings])
qed

lemma trace_fri_partial_candidate_opening_evidence_not_low_on_eval_domain:
  assumes evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
  shows "\<not> fri_table_low_degree_on (clength - 1) eval_domain trace_table"
proof -
  have partial:
    "trace_fri_partial_candidate_evidence s out fr candidate_query_idxs
      trace_openings trace_table"
    using trace_fri_partial_candidate_opening_evidenceD(2)[OF evidence] .
  have "\<not> trace_table_low_degree trace_table"
    using trace_fri_partial_candidate_evidenceD(3)[OF partial] .
  then show ?thesis
    using trace_table_not_low_degree_iff_not_fri_table_low_degree_on_eval_domain
    by simp
qed

lemma composition_fri_partial_candidate_opening_evidence_not_low_declared:
  assumes evidence:
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
    and degree_bound: "to_nat fri_dg \<le> maxDegree"
  shows "\<not> composition_table_low_degree (to_nat fri_dg) composition_table"
proof -
  have partial:
    "composition_fri_partial_candidate_evidence s out fr f_fri_roots
      f_final as dg composition_fri_roots final trace_query_idxs
      trace_openings composition_query_idxs composition_openings
      trace_table composition_table"
    by (rule composition_fri_partial_candidate_opening_evidenceD(2)
        [OF evidence])
  have not_low_max:
    "\<not> composition_table_low_degree maxDegree composition_table"
    by (rule composition_fri_partial_candidate_evidenceD(5)[OF partial])
  show ?thesis
    by (rule composition_table_not_low_degree_mono
        [OF degree_bound not_low_max])
qed

lemma composition_fri_partial_candidate_opening_evidence_not_low_declared_on_eval_domain:
  assumes evidence:
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
    and degree_bound: "to_nat fri_dg \<le> maxDegree"
  shows "\<not> fri_table_low_degree_on (to_nat fri_dg) eval_domain
    composition_table"
proof -
  have "\<not> composition_table_low_degree (to_nat fri_dg) composition_table"
    by (rule composition_fri_partial_candidate_opening_evidence_not_low_declared
        [OF evidence degree_bound])
  then show ?thesis
    using composition_table_not_low_degree_iff_not_fri_table_low_degree_on_eval_domain
    by simp
qed

lemma trace_fri_partial_candidate_opening_evidence_canonical_bad_candidate:
  assumes evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    and chain:
    "generic_fri_canonical_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers doms layers bad"
  shows
    "generic_fri_bad_candidate trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers bad"
proof -
  have "\<not> trace_table_low_degree trace_table"
    using trace_fri_partial_candidate_opening_evidenceD(2)[OF evidence]
      trace_fri_partial_candidate_evidenceD(3)
    by blast
  then show ?thesis
    by (rule generic_fri_bad_candidate_from_canonical_layer_chain
        [OF chain])
qed

lemma composition_fri_partial_candidate_opening_evidence_canonical_bad_candidate:
  assumes evidence:
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
    and degree_bound: "to_nat fri_dg \<le> maxDegree"
    and chain:
    "generic_fri_canonical_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers doms layers bad"
  shows
    "generic_fri_bad_candidate
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers bad"
proof -
  have "\<not> composition_table_low_degree (to_nat fri_dg) composition_table"
    by (rule composition_fri_partial_candidate_opening_evidence_not_low_declared
        [OF evidence degree_bound])
  then show ?thesis
    by (rule generic_fri_bad_candidate_from_canonical_layer_chain
        [OF chain])
qed

lemma trace_fri_multiround_bad_sets_as_generic:
  "trace_fri_multiround_bad_sets bad trace_table =
    generic_fri_bad_challenge_lists trace_fri_algebraic_round_count
      (bad trace_table)"
  unfolding trace_fri_multiround_bad_sets_def
    generic_fri_bad_challenge_lists_def
  by simp

lemma composition_fri_multiround_bad_sets_as_generic:
  "composition_fri_multiround_bad_sets bad dg composition_table =
    generic_fri_bad_challenge_lists
      (composition_fri_algebraic_round_count dg)
      (bad dg composition_table)"
  unfolding composition_fri_multiround_bad_sets_def
    generic_fri_bad_challenge_lists_def
  by simp

end

end
