(*  Title:      Stark/Soundness_FRI.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI
  imports
    Soundness_Bad_Events
begin

context soundness
begin

subsection \<open>Algebraic FRI Soundness Interface\<close>

text \<open>
  The next definitions isolate the algebraic content of the verifier's FRI fold
  equation from transcript extraction and Merkle authentication.  They are
  intentionally protocol-independent except for using the same affine fold as
  \<^term>\<open>receive_query_commits\<close>.
\<close>

definition fri_table_fold_value
  :: "'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f"
  where
    "fri_table_fold_value b layer fri_dom len pw i =
      fri_fold_value b (layer ! i) (layer ! fri_sibling_index len i)
        (fri_fold_denominator (fri_dom ! i) 1)"

definition fri_algebraic_layer_relation
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "fri_algebraic_layer_relation len pw b fri_dom layer next_dom
      next_layer \<longleftrightarrow>
      0 < len \<and>
      len \<le> length fri_dom \<and>
      len \<le> length layer \<and>
      len div 2 \<le> length next_dom \<and>
      len div 2 \<le> length next_layer \<and>
      (\<forall>i < len div 2.
        next_dom ! i = (fri_dom ! i)\<^sup>2 \<and>
        next_layer ! i = fri_table_fold_value b layer fri_dom len pw i)"

lemma fri_algebraic_layer_relationD:
  assumes "fri_algebraic_layer_relation len pw b fri_dom layer next_dom
    next_layer"
    and "i < len div 2"
  shows "next_dom ! i = (fri_dom ! i)\<^sup>2"
    and "next_layer ! i = fri_table_fold_value b layer fri_dom len pw i"
  using assms unfolding fri_algebraic_layer_relation_def by auto

definition fri_opening_matches_table
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "fri_opening_matches_table len idx layer xp xn \<longleftrightarrow>
      idx < len \<and>
      len \<le> length layer \<and>
      layer ! idx = xp \<and>
      layer ! fri_sibling_index len idx = xn"

lemma fri_opening_matches_tableD:
  assumes "fri_opening_matches_table len idx layer xp xn"
  shows "idx < len"
    and "len \<le> length layer"
    and "layer ! idx = xp"
    and "layer ! fri_sibling_index len idx = xn"
  using assms unfolding fri_opening_matches_table_def by auto

lemma fri_fold_value_eq_table_fold_value:
  assumes dom_idx: "fri_dom ! idx = (h ^ idx * shift) ^ pw"
    and match: "fri_opening_matches_table len idx layer xp xn"
  shows
    "fri_fold_value b xp xn (fri_fold_denominator (h ^ idx * shift) pw) =
      fri_table_fold_value b layer fri_dom len pw idx"
  using dom_idx fri_opening_matches_tableD(3,4)[OF match]
  unfolding fri_table_fold_value_def fri_fold_denominator_def by simp

lemma fri_layer_opening_step_outcome_fold_table_if_opening_matches:
  assumes outcome:
    "Some (out, t) \<in>
      set_dist (execute (fri_layer_opening_step (b, f) (i, x, len, pw)) s)"
    and dom_i: "fri_dom ! i = (h ^ i * shift) ^ pw"
  obtains xp xp_path xn xn_path x'
  where
    "out = (i mod (len div 2), x', len div 2, pw + pw)"
    and "xp = x"
    and "fri_layer_opening_chunk len xp xp_path xn xn_path
      ([xp] @ xp_path @ [xn] @ xn_path)"
    and "PTranscript s = ([xp] @ xp_path @ [xn] @ xn_path) @ PTranscript t"
    and "PState t = foldl concat (PState s) ([xp] @ xp_path @ [xn] @ xn_path)"
    and "s \<le> t"
    and "fri_opening_matches_table len i layer xp xn \<Longrightarrow>
      x' = fri_table_fold_value b layer fri_dom len pw i"
proof -
  from fri_layer_opening_step_outcome[OF outcome]
  obtain xp xp_path xn xn_path x' where
    out_eq: "out = (i mod (len div 2), x', len div 2, pw + pw)"
    and xp_eq: "xp = x"
    and x'_eq:
      "x' = fri_fold_value b xp xn
        (fri_fold_denominator ((h ^ i) * shift) pw)"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path
        ([xp] @ xp_path @ [xn] @ xn_path)"
    and tr:
      "PTranscript s = ([xp] @ xp_path @ [xn] @ xn_path) @ PTranscript t"
    and st:
      "PState t = foldl concat (PState s) ([xp] @ xp_path @ [xn] @ xn_path)"
    and ext: "s \<le> t"
    by blast
  have table_fold:
    "fri_opening_matches_table len i layer xp xn \<Longrightarrow>
      x' = fri_table_fold_value b layer fri_dom len pw i"
  proof -
    assume match: "fri_opening_matches_table len i layer xp xn"
    have "fri_fold_value b xp xn
        (fri_fold_denominator ((h ^ i) * shift) pw) =
      fri_table_fold_value b layer fri_dom len pw i"
      by (rule fri_fold_value_eq_table_fold_value[OF dom_i match])
    then show "x' = fri_table_fold_value b layer fri_dom len pw i"
      using x'_eq by simp
  qed
  show ?thesis
    by (rule that[OF out_eq xp_eq chunk tr st ext table_fold])
qed

definition fri_fold_coeff_pair :: "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<times> 'f"
  where
    "fri_fold_coeff_pair xp xn denom =
      ((xp + xn) div 2, (xp - xn) div denom)"

definition fri_local_hiding_challenges
  :: "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f set"
  where
    "fri_local_hiding_challenges xp xn yp yn denom =
      {b. fri_fold_value b xp xn denom = fri_fold_value b yp yn denom}"

lemma fri_affine_collision_challenges_card_le_one:
  fixes a c a' c' :: 'f
  assumes pair_diff: "(a, c) \<noteq> (a', c')"
  shows "card {b. a + b * c = a' + b * c'} \<le> (1::nat)"
proof -
  show ?thesis
  proof (cases "c = c'")
    case True
    then have a_diff: "a \<noteq> a'"
      using pair_diff by auto
    have "{b. a + b * c = a' + b * c'} = {}"
    proof (rule ccontr)
      assume "{b. a + b * c = a' + b * c'} \<noteq> {}"
      then obtain b where
        b_in: "b \<in> {b. a + b * c = a' + b * c'}"
        by blast
      then have eq: "a + b * c = a' + b * c'"
        by simp
      then have "a + b * c' = a' + b * c'"
        using True by simp
      then have "(a + b * c') - b * c' = (a' + b * c') - b * c'"
        by simp
      then have "a = a'"
        by simp
      then show False
        using a_diff by contradiction
    qed
    then show ?thesis by simp
  next
    case False
    have subset:
      "{b. a + b * c = a' + b * c'} \<subseteq>
        {(a' - a) div (c - c')}"
    proof
      fix b
      assume b_in: "b \<in> {b. a + b * c = a' + b * c'}"
      then have eq: "a + b * c = a' + b * c'"
        by simp
      have "b * (c - c') = a' - a"
        using eq by (simp add: algebra_simps)
      then have "b = (a' - a) div (c - c')"
        using False by (simp add: field_simps)
      then show "b \<in> {(a' - a) div (c - c')}"
        by simp
    qed
    have "card {b. a + b * c = a' + b * c'} \<le>
        card {(a' - a) div (c - c')}"
      by (rule card_mono) (use subset in auto)
    then show ?thesis by simp
  qed
qed

lemma fri_local_hiding_challenges_card_le_one:
  assumes pair_diff:
    "fri_fold_coeff_pair xp xn denom \<noteq> fri_fold_coeff_pair yp yn denom"
  shows "card (fri_local_hiding_challenges xp xn yp yn denom) \<le> 1"
proof -
  let ?a = "(xp + xn) div 2"
  let ?c = "(xp - xn) div denom"
  let ?a' = "(yp + yn) div 2"
  let ?c' = "(yp - yn) div denom"
  have pair_diff': "(?a, ?c) \<noteq> (?a', ?c')"
    using pair_diff unfolding fri_fold_coeff_pair_def by simp
  have "fri_local_hiding_challenges xp xn yp yn denom =
      {b. ?a + b * ?c = ?a' + b * ?c'}"
    unfolding fri_local_hiding_challenges_def fri_fold_value_def by simp
  then show ?thesis
    using fri_affine_collision_challenges_card_le_one[OF pair_diff'] by simp
qed

lemma fri_one_step_disagreement_hiding_bound:
  assumes
    "fri_fold_coeff_pair xp xn denom \<noteq> fri_fold_coeff_pair yp yn denom"
  shows "card (fri_local_hiding_challenges xp xn yp yn denom) \<le> 1"
  by (rule fri_local_hiding_challenges_card_le_one[OF assms])

lemma fri_one_step_disagreement_outside_hiding:
  assumes "b \<notin> fri_local_hiding_challenges xp xn yp yn denom"
  shows "fri_fold_value b xp xn denom \<noteq> fri_fold_value b yp yn denom"
  using assms unfolding fri_local_hiding_challenges_def by simp

definition fri_table_local_hiding_challenges
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      'f set"
  where
    "fri_table_local_hiding_challenges layer claimed fri_dom len pw i =
      fri_local_hiding_challenges
        (layer ! i) (layer ! fri_sibling_index len i)
        (claimed ! i) (claimed ! fri_sibling_index len i)
        (fri_fold_denominator (fri_dom ! i) pw)"

lemma fri_table_local_hiding_challenges_card_le_one:
  assumes
    "fri_fold_coeff_pair
      (layer ! i) (layer ! fri_sibling_index len i)
      (fri_fold_denominator (fri_dom ! i) pw) \<noteq>
      fri_fold_coeff_pair
        (claimed ! i) (claimed ! fri_sibling_index len i)
        (fri_fold_denominator (fri_dom ! i) pw)"
  shows "card (fri_table_local_hiding_challenges layer claimed fri_dom len pw i)
    \<le> 1"
  unfolding fri_table_local_hiding_challenges_def
  by (rule fri_local_hiding_challenges_card_le_one[OF assms])

definition fri_one_step_disagreement_challenges
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f set"
  where
    "fri_one_step_disagreement_challenges len pw layer claimed fri_dom =
      {b. \<exists>i < len div 2.
        fri_fold_coeff_pair
          (layer ! i) (layer ! fri_sibling_index len i)
          (fri_fold_denominator (fri_dom ! i) pw) \<noteq>
        fri_fold_coeff_pair
          (claimed ! i) (claimed ! fri_sibling_index len i)
          (fri_fold_denominator (fri_dom ! i) pw) \<and>
        b \<in> fri_table_local_hiding_challenges layer claimed fri_dom len pw i}"

lemma fri_one_step_disagreement_challenges_card_bound:
  "card (fri_one_step_disagreement_challenges len pw layer claimed fri_dom)
    \<le> CARD('f)"
proof -
  have finite_univ: "finite (UNIV :: 'f set)"
    by simp
  have "card (fri_one_step_disagreement_challenges len pw layer claimed fri_dom)
      \<le> card (UNIV :: 'f set)"
    by (rule card_mono[OF finite_univ]) auto
  then show ?thesis by simp
qed

lemma fri_one_step_disagreement_challenges_card_bound_local:
  "card (fri_one_step_disagreement_challenges len pw layer claimed fri_dom)
    \<le> len div 2"
proof -
  let ?S =
    "\<lambda>i. if
        fri_fold_coeff_pair
          (layer ! i) (layer ! fri_sibling_index len i)
          (fri_fold_denominator (fri_dom ! i) pw) \<noteq>
        fri_fold_coeff_pair
          (claimed ! i) (claimed ! fri_sibling_index len i)
          (fri_fold_denominator (fri_dom ! i) pw)
      then fri_table_local_hiding_challenges layer claimed fri_dom len pw i
      else {}"
  have set_eq:
    "fri_one_step_disagreement_challenges len pw layer claimed fri_dom =
      (\<Union>i \<in> {..<len div 2}. ?S i)"
    unfolding fri_one_step_disagreement_challenges_def by auto
  have local_bound:
    "\<And>i. i < len div 2 \<Longrightarrow> card (?S i) \<le> 1"
  proof -
    fix i
    assume "i < len div 2"
    show "card (?S i) \<le> 1"
    proof (cases
      "fri_fold_coeff_pair
        (layer ! i) (layer ! fri_sibling_index len i)
        (fri_fold_denominator (fri_dom ! i) pw) \<noteq>
      fri_fold_coeff_pair
        (claimed ! i) (claimed ! fri_sibling_index len i)
        (fri_fold_denominator (fri_dom ! i) pw)")
      case True
      then have "card
          (fri_table_local_hiding_challenges layer claimed fri_dom len pw i)
          \<le> 1"
        by (rule fri_table_local_hiding_challenges_card_le_one)
      then show ?thesis
        using True by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  have "card (fri_one_step_disagreement_challenges len pw layer claimed fri_dom) =
      card (\<Union>i \<in> {..<len div 2}. ?S i)"
    using set_eq by simp
  also have "... \<le> (\<Sum>i \<in> {..<len div 2}. card (?S i))"
    by (rule card_UN_le) simp
  also have "... \<le> (\<Sum>i \<in> {..<len div 2}. 1)"
    by (rule sum_mono) (rule local_bound, simp)
  also have "... = len div 2"
    by simp
  finally show ?thesis .
qed

definition fri_multiround_bad_challenge_lists
  :: "nat \<Rightarrow> (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> 'f list set"
  where
    "fri_multiround_bad_challenge_lists n bad =
      {bs \<in> fri_challenge_space n.
        \<exists>i < n. bs ! i \<in> bad i (take i bs)}"

definition fri_bad_challenge_lists_bounded_by
  :: "nat \<Rightarrow> 'f list set \<Rightarrow> nat \<Rightarrow> bool"
  where
    "fri_bad_challenge_lists_bounded_by n bad bd \<longleftrightarrow>
      bad \<subseteq> fri_challenge_space n \<and> card bad \<le> bd"

lemma fri_multiround_bad_challenge_lists_subset:
  "fri_multiround_bad_challenge_lists n bad \<subseteq> fri_challenge_space n"
  unfolding fri_multiround_bad_challenge_lists_def by auto

lemma fri_multiround_bad_challenge_lists_card_bound:
  "card (fri_multiround_bad_challenge_lists n bad) \<le> CARD('f) ^ n"
proof -
  have "card (fri_multiround_bad_challenge_lists n bad) \<le>
      card (fri_challenge_space n)"
    by (rule card_mono[OF finite_fri_challenge_space])
      (auto simp: fri_multiround_bad_challenge_lists_subset)
  also have "... = CARD('f) ^ n"
    by (rule card_fri_challenge_space)
  finally show ?thesis .
qed

lemma fri_multiround_bad_challenge_lists_bounded_by:
  "fri_bad_challenge_lists_bounded_by n
    (fri_multiround_bad_challenge_lists n bad) (CARD('f) ^ n)"
  unfolding fri_bad_challenge_lists_bounded_by_def
  using fri_multiround_bad_challenge_lists_subset
    fri_multiround_bad_challenge_lists_card_bound
  by simp

definition fri_final_constant_consistent :: "'f list \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "fri_final_constant_consistent layer final \<longleftrightarrow>
      (\<forall>x \<in> set layer. x = final)"

lemma fri_final_constant_consistent_nth:
  assumes "fri_final_constant_consistent layer final"
    and "i < length layer"
  shows "layer ! i = final"
  using assms unfolding fri_final_constant_consistent_def
  by (simp add: nth_mem)

lemma fri_final_constant_consistent_hd:
  assumes "fri_final_constant_consistent layer final"
    and "layer \<noteq> []"
  shows "hd layer = final"
  using assms fri_final_constant_consistent_nth[of layer final 0]
  by (cases layer) auto

definition fri_table_low_degree_on :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "fri_table_low_degree_on d fri_dom table \<longleftrightarrow>
      (\<exists>p. degree p \<le> d \<and> table = map (poly p) fri_dom)"

fun fri_degree_after :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "fri_degree_after 0 d = d"
  | "fri_degree_after (Suc n) d = fri_degree_after n d div 2"

lemma fri_degree_after_Suc[simp]:
  "fri_degree_after (Suc n) d = fri_degree_after n d div 2"
  by simp

definition fri_one_round_proximity_step
  :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f set \<Rightarrow> bool"
  where
    "fri_one_round_proximity_step d len pw fri_dom layer next_dom next_layer bad \<longleftrightarrow>
      (\<forall>b. b \<notin> bad \<longrightarrow>
        fri_algebraic_layer_relation len pw b fri_dom layer next_dom next_layer \<longrightarrow>
        fri_table_low_degree_on (d div 2) next_dom next_layer \<longrightarrow>
        fri_table_low_degree_on d fri_dom layer)"

lemma fri_one_round_proximity_step_bad_or_next_not_low:
  assumes step:
      "fri_one_round_proximity_step d len pw fri_dom layer next_dom next_layer bad"
    and relation:
      "fri_algebraic_layer_relation len pw b fri_dom layer next_dom next_layer"
    and current_not_low: "\<not> fri_table_low_degree_on d fri_dom layer"
    and challenge_not_bad: "b \<notin> bad"
  shows "\<not> fri_table_low_degree_on (d div 2) next_dom next_layer"
  using assms unfolding fri_one_round_proximity_step_def by blast

definition fri_multiround_proximity_steps
  :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      'f list list \<Rightarrow> 'f list list \<Rightarrow>
      (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
  where
    "fri_multiround_proximity_steps n d lens pws doms layers bad \<longleftrightarrow>
      length lens = n \<and>
      length pws = n \<and>
      length doms = Suc n \<and>
      length layers = Suc n \<and>
      (\<forall>bs \<in> fri_challenge_space n.
        \<forall>i < n.
          fri_one_round_proximity_step (fri_degree_after i d)
            (lens ! i) (pws ! i) (doms ! i) (layers ! i)
            (doms ! Suc i) (layers ! Suc i) (bad i (take i bs)))"

lemma fri_multiround_bad_challenge_lists_notinD:
  assumes challenges: "bs \<in> fri_challenge_space n"
    and not_bad: "bs \<notin> fri_multiround_bad_challenge_lists n bad"
    and i_bound: "i < n"
  shows "bs ! i \<notin> bad i (take i bs)"
  using assms unfolding fri_multiround_bad_challenge_lists_def by blast

lemma fri_multiround_proximity_skeleton:
  assumes steps: "fri_multiround_proximity_steps n d lens pws doms layers bad"
    and challenges: "bs \<in> fri_challenge_space n"
    and relations:
      "\<And>i. i < n \<Longrightarrow>
        fri_algebraic_layer_relation (lens ! i) (pws ! i) (bs ! i)
          (doms ! i) (layers ! i) (doms ! Suc i) (layers ! Suc i)"
    and start_not_low:
      "\<not> fri_table_low_degree_on d (doms ! 0) (layers ! 0)"
    and final_low:
      "fri_table_low_degree_on (fri_degree_after n d) (doms ! n) (layers ! n)"
  shows "bs \<in> fri_multiround_bad_challenge_lists n bad"
proof (rule ccontr)
  assume not_bad: "bs \<notin> fri_multiround_bad_challenge_lists n bad"
  have step_at:
    "\<And>i. i < n \<Longrightarrow>
      fri_one_round_proximity_step (fri_degree_after i d)
        (lens ! i) (pws ! i) (doms ! i) (layers ! i)
        (doms ! Suc i) (layers ! Suc i) (bad i (take i bs))"
    using steps challenges unfolding fri_multiround_proximity_steps_def by blast
  have not_low:
    "\<And>i. i \<le> n \<Longrightarrow>
      \<not> fri_table_low_degree_on (fri_degree_after i d) (doms ! i) (layers ! i)"
  proof -
    fix i
    assume "i \<le> n"
    then show
      "\<not> fri_table_low_degree_on (fri_degree_after i d) (doms ! i) (layers ! i)"
    proof (induction i)
      case 0
      then show ?case
        using start_not_low by simp
    next
      case (Suc i)
      have i_bound: "i < n"
        using Suc.prems by simp
      have prev_not_low:
        "\<not> fri_table_low_degree_on (fri_degree_after i d)
          (doms ! i) (layers ! i)"
        using Suc.IH Suc.prems by simp
      have challenge_not_bad: "bs ! i \<notin> bad i (take i bs)"
        by (rule fri_multiround_bad_challenge_lists_notinD
            [OF challenges not_bad i_bound])
      have next_not_low:
        "\<not> fri_table_low_degree_on (fri_degree_after i d div 2)
          (doms ! Suc i) (layers ! Suc i)"
        by (rule fri_one_round_proximity_step_bad_or_next_not_low
            [OF step_at[OF i_bound] relations[OF i_bound] prev_not_low
              challenge_not_bad])
      then show ?case
        by simp
    qed
  qed
  have "\<not> fri_table_low_degree_on (fri_degree_after n d) (doms ! n) (layers ! n)"
    by (rule not_low) simp
  then show False
    using final_low by contradiction
qed

definition fri_round_count_for_degree_bound :: "nat \<Rightarrow> nat"
  where "fri_round_count_for_degree_bound d = ceil_log (d + 1)"

definition trace_fri_algebraic_round_count :: nat
  where
    "trace_fri_algebraic_round_count =
      fri_round_count_for_degree_bound (clength - 1)"

definition composition_fri_algebraic_round_count :: "'f \<Rightarrow> nat"
  where
    "composition_fri_algebraic_round_count dg =
      fri_round_count_for_degree_bound (to_nat dg)"

lemma trace_fri_algebraic_round_count_eq:
  "trace_fri_algebraic_round_count = ceil_log clength"
  unfolding trace_fri_algebraic_round_count_def
    fri_round_count_for_degree_bound_def
  using clength_pos by simp

lemma composition_fri_algebraic_round_count_eq:
  "composition_fri_algebraic_round_count dg =
    ceil_log (to_nat dg + 1)"
  unfolding composition_fri_algebraic_round_count_def
    fri_round_count_for_degree_bound_def
  by simp

lemma trace_fri_algebraic_challenge_space:
  "fri_challenge_space trace_fri_algebraic_round_count =
    fri_challenge_space (ceil_log clength)"
  by (simp add: trace_fri_algebraic_round_count_eq)

lemma composition_fri_algebraic_challenge_space:
  "fri_challenge_space (composition_fri_algebraic_round_count dg) =
    fri_challenge_space (ceil_log (to_nat dg + 1))"
  by (simp add: composition_fri_algebraic_round_count_eq)

definition trace_fri_multiround_bad_sets
  :: "('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      'f list \<Rightarrow> 'f list set"
  where
    "trace_fri_multiround_bad_sets bad trace_table =
      fri_multiround_bad_challenge_lists trace_fri_algebraic_round_count
        (bad trace_table)"

definition composition_fri_multiround_bad_sets
  :: "('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f list set"
  where
    "composition_fri_multiround_bad_sets bad dg composition_table =
      fri_multiround_bad_challenge_lists
        (composition_fri_algebraic_round_count dg)
        (bad dg composition_table)"

lemma trace_fri_multiround_bad_sets_subset:
  "trace_fri_multiround_bad_sets bad trace_table \<subseteq>
    fri_challenge_space (ceil_log clength)"
proof -
  have "trace_fri_multiround_bad_sets bad trace_table \<subseteq>
      fri_challenge_space trace_fri_algebraic_round_count"
    unfolding trace_fri_multiround_bad_sets_def
    by (rule fri_multiround_bad_challenge_lists_subset)
  also have "... = fri_challenge_space (ceil_log clength)"
    by (rule trace_fri_algebraic_challenge_space)
  finally show ?thesis .
qed

lemma composition_fri_multiround_bad_sets_subset:
  "composition_fri_multiround_bad_sets bad dg composition_table \<subseteq>
    fri_challenge_space (ceil_log (to_nat dg + 1))"
proof -
  have "composition_fri_multiround_bad_sets bad dg composition_table \<subseteq>
      fri_challenge_space (composition_fri_algebraic_round_count dg)"
    unfolding composition_fri_multiround_bad_sets_def
    by (rule fri_multiround_bad_challenge_lists_subset)
  also have "... = fri_challenge_space (ceil_log (to_nat dg + 1))"
    by (rule composition_fri_algebraic_challenge_space)
  finally show ?thesis .
qed

lemma trace_fri_multiround_bad_sets_card_bound:
  "card (trace_fri_multiround_bad_sets bad trace_table) \<le>
    CARD('f) ^ ceil_log clength"
  unfolding trace_fri_multiround_bad_sets_def
  using fri_multiround_bad_challenge_lists_card_bound
  by (simp add: trace_fri_algebraic_round_count_eq)

lemma composition_fri_multiround_bad_sets_card_bound:
  "card (composition_fri_multiround_bad_sets bad dg composition_table) \<le>
    CARD('f) ^ ceil_log (to_nat dg + 1)"
  unfolding composition_fri_multiround_bad_sets_def
  using fri_multiround_bad_challenge_lists_card_bound
  by (simp add: composition_fri_algebraic_round_count_eq)

definition accepted_fri_challenges
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "accepted_fri_challenges s out trace_bs dg comp_bs \<longleftrightarrow>
      (\<exists>result final_state fr f_fl f_final as fl final query_state.
        out = Some (result, final_state) \<and>
        verifier_header_transcript s fr (map snd f_fl) f_final as dg
          (map snd fl) final (PTranscript query_state) \<and>
        PState query_state =
          verifier_header_state s fr (map snd f_fl) f_final as dg
            (map snd fl) final \<and>
        Some (result, final_state) \<in>
          set_dist (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state) \<and>
        PQueryCounter query_state = PQueryCounter s \<and>
        trace_bs = map fst f_fl \<and>
        comp_bs = map fst fl \<and>
        (\<forall>i < length f_fl.
          fmlookup (HashMap query_state)
            (TraceFriChallenge (PTraceFriCounter s + i) (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
            Some (fst (f_fl ! i))) \<and>
        (\<forall>i < length fl.
          fmlookup (HashMap query_state)
            (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
              (concat
                (foldl concat
                  (concat
                    (foldl concat (concat (PState s) fr) (map snd f_fl))
                    f_final)
                  as)
                dg)
              (take (Suc i) (map snd fl)))) =
            Some (fst (fl ! i))))"

lemma verify_monad_accepted_fri_challenges:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  obtains trace_bs dg comp_bs
  where "accepted_fri_challenges s (Some (result, final_state))
    trace_bs dg comp_bs"
proof -
  from verify_monad_header_random_oracle_replay[OF outcome]
  obtain fr f_fl f_final as dg fl final query_state where
    header:
      "verifier_header_transcript s fr (map snd f_fl) f_final as dg
        (map snd fl) final (PTranscript query_state)"
    and query_state_eq:
      "PState query_state =
        verifier_header_state s fr (map snd f_fl) f_final as dg
          (map snd fl) final"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
    and query_count_header:
      "PQueryCounter query_state = PQueryCounter s"
    and ext_s_query_header: "s \<le> query_state"
    and trace_lookup:
      "\<And>i. i < length f_fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (TraceFriChallenge (PTraceFriCounter s + i) (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))"
    and alpha_lookup:
      "\<And>i. i < length as \<Longrightarrow>
        fmlookup (HashMap query_state)
          (AlphaChallenge (PAlphaCounter s + i) (foldl concat
            (concat (foldl concat (concat (PState s) fr) (map snd f_fl))
              f_final)
            (take i as))) =
          Some (as ! i)"
    and comp_lookup:
      "\<And>i. i < length fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
            (concat
              (foldl concat
                (concat
                  (foldl concat (concat (PState s) fr) (map snd f_fl))
                  f_final)
                as)
              dg)
            (take (Suc i) (map snd fl)))) =
          Some (fst (fl ! i))"
    and degree_bound: "to_nat dg \<le> maxDegree"
    by blast
  have "accepted_fri_challenges s (Some (result, final_state))
      (map fst f_fl) dg (map fst fl)"
  proof -
    have trace_lookup_all:
      "\<forall>i < length f_fl.
        fmlookup (HashMap query_state)
          (TraceFriChallenge (PTraceFriCounter s + i) (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))"
      using trace_lookup by blast
    have comp_lookup_all:
      "\<forall>i < length fl.
        fmlookup (HashMap query_state)
          (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
            (concat
              (foldl concat
                (concat
                  (foldl concat (concat (PState s) fr) (map snd f_fl))
                  f_final)
                as)
              dg)
            (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i))"
      using comp_lookup by blast
    show ?thesis
      unfolding accepted_fri_challenges_def
      by (intro exI[of _ result] exI[of _ final_state] exI[of _ fr]
          exI[of _ f_fl] exI[of _ f_final] exI[of _ as] exI[of _ fl]
          exI[of _ final] exI[of _ query_state])
        (use header query_state_eq query_out query_count_header trace_lookup_all
          comp_lookup_all in simp)
  qed
  then show ?thesis
    by (rule that)
qed

lemma accepted_fri_challenges_trace_space:
  assumes "accepted_fri_challenges s out trace_bs dg comp_bs"
  shows "trace_bs \<in> fri_challenge_space (ceil_log clength)"
  using assms
  unfolding accepted_fri_challenges_def verifier_header_transcript_def
    fri_challenge_space_def
  by auto

lemma accepted_fri_challenges_composition_space:
  assumes "accepted_fri_challenges s out trace_bs dg comp_bs"
  shows "comp_bs \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
  using assms
  unfolding accepted_fri_challenges_def verifier_header_transcript_def
    fri_challenge_space_def
  by auto

lemma accepted_fri_challenges_unique:
  assumes c1:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs dg comp_bs"
    and c2:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs' dg' comp_bs'"
  shows "trace_bs' = trace_bs \<and> dg' = dg \<and> comp_bs' = comp_bs"
proof -
  from c1 obtain fr f_fl f_final as fl final query_state where
    header1:
      "verifier_header_transcript s fr (map snd f_fl) f_final as dg
        (map snd fl) final (PTranscript query_state)"
    and query_state1:
      "PState query_state =
        verifier_header_state s fr (map snd f_fl) f_final as dg
          (map snd fl) final"
    and query_out1:
      "Some (result, final_state) \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
    and trace_bs_eq: "trace_bs = map fst f_fl"
    and comp_bs_eq: "comp_bs = map fst fl"
    and trace_lookup1:
      "\<And>i. i < length f_fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (TraceFriChallenge (PTraceFriCounter s + i)
            (foldl concat (concat (PState s) fr)
              (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))"
    and comp_lookup1:
      "\<And>i. i < length fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (CompositionFriChallenge (PCompositionFriCounter s + i)
            (foldl concat
              (concat
                (foldl concat
                  (concat
                    (foldl concat (concat (PState s) fr) (map snd f_fl))
                    f_final)
                  as)
                dg)
              (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i))"
    unfolding accepted_fri_challenges_def by blast
  from c2 obtain fr' f_fl' f_final' as' fl' final' query_state' where
    header2:
      "verifier_header_transcript s fr' (map snd f_fl') f_final' as' dg'
        (map snd fl') final' (PTranscript query_state')"
    and query_state2:
      "PState query_state' =
        verifier_header_state s fr' (map snd f_fl') f_final' as' dg'
          (map snd fl') final'"
    and query_out2:
      "Some (result, final_state) \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr' f_fl' f_final' as' fl' final')
            rounds)
          query_state')"
    and trace_bs'_eq: "trace_bs' = map fst f_fl'"
    and comp_bs'_eq: "comp_bs' = map fst fl'"
    and trace_lookup2:
      "\<And>i. i < length f_fl' \<Longrightarrow>
        fmlookup (HashMap query_state')
          (TraceFriChallenge (PTraceFriCounter s + i)
            (foldl concat (concat (PState s) fr')
              (take (Suc i) (map snd f_fl')))) =
        Some (fst (f_fl' ! i))"
    and comp_lookup2:
      "\<And>i. i < length fl' \<Longrightarrow>
        fmlookup (HashMap query_state')
          (CompositionFriChallenge (PCompositionFriCounter s + i)
            (foldl concat
              (concat
                (foldl concat
                  (concat
                    (foldl concat (concat (PState s) fr') (map snd f_fl'))
                    f_final')
                  as')
                dg')
              (take (Suc i) (map snd fl')))) =
        Some (fst (fl' ! i))"
    unfolding accepted_fri_challenges_def by blast
  have header_unique:
    "fr' = fr \<and>
     map snd f_fl' = map snd f_fl \<and>
     f_final' = f_final \<and>
     as' = as \<and>
     dg' = dg \<and>
     map snd fl' = map snd fl \<and>
     final' = final \<and>
     PTranscript query_state' = PTranscript query_state"
    by (rule verifier_header_transcript_unique[OF header1 header2])
  have ext1: "query_state \<le> final_state"
    using ntimes_verifier_query_rounds_outcome[OF query_out1] by blast
  have ext2: "query_state' \<le> final_state"
    using ntimes_verifier_query_rounds_outcome[OF query_out2] by blast
  have len_f_fl': "length f_fl' = length f_fl"
    using header_unique by (metis length_map)
  have f_fl_fst_eq: "map fst f_fl' = map fst f_fl"
  proof (rule nth_equalityI)
    show "length (map fst f_fl') = length (map fst f_fl)"
      using len_f_fl' by simp
  next
    fix i
    assume i_bound: "i < length (map fst f_fl')"
    then have i_bound': "i < length f_fl'"
      by simp
    have i_bound_old: "i < length f_fl"
      using i_bound' len_f_fl' by simp
    let ?key =
      "TraceFriChallenge (PTraceFriCounter s + i)
        (foldl concat (concat (PState s) fr)
          (take (Suc i) (map snd f_fl)))"
    have lookup1_final:
      "fmlookup (HashMap final_state) ?key =
        Some (fst (f_fl ! i))"
      by (rule hash_extension_lookup[OF trace_lookup1[OF i_bound_old] ext1])
    have key_eq:
      "TraceFriChallenge (PTraceFriCounter s + i)
        (foldl concat (concat (PState s) fr')
          (take (Suc i) (map snd f_fl'))) = ?key"
      using header_unique by simp
    have lookup2_final:
      "fmlookup (HashMap final_state) ?key =
        Some (fst (f_fl' ! i))"
      using hash_extension_lookup[OF trace_lookup2[OF i_bound'] ext2]
      unfolding key_eq .
    show "map fst f_fl' ! i = map fst f_fl ! i"
      using lookup1_final lookup2_final i_bound' i_bound_old by simp
  qed
  have len_fl': "length fl' = length fl"
    using header_unique by (metis length_map)
  have fl_fst_eq: "map fst fl' = map fst fl"
  proof (rule nth_equalityI)
    show "length (map fst fl') = length (map fst fl)"
      using len_fl' by simp
  next
    fix i
    assume i_bound: "i < length (map fst fl')"
    then have i_bound': "i < length fl'"
      by simp
    have i_bound_old: "i < length fl"
      using i_bound' len_fl' by simp
    let ?key =
      "CompositionFriChallenge (PCompositionFriCounter s + i)
        (foldl concat
          (concat
            (foldl concat
              (concat
                (foldl concat (concat (PState s) fr) (map snd f_fl))
                f_final)
              as)
            dg)
          (take (Suc i) (map snd fl)))"
    have lookup1_final:
      "fmlookup (HashMap final_state) ?key =
        Some (fst (fl ! i))"
      by (rule hash_extension_lookup[OF comp_lookup1[OF i_bound_old] ext1])
    have key_eq:
      "CompositionFriChallenge (PCompositionFriCounter s + i)
        (foldl concat
          (concat
            (foldl concat
              (concat
                (foldl concat (concat (PState s) fr') (map snd f_fl'))
                f_final')
              as')
            dg')
          (take (Suc i) (map snd fl'))) = ?key"
      using header_unique by simp
    have lookup2_final:
      "fmlookup (HashMap final_state) ?key =
        Some (fst (fl' ! i))"
      using hash_extension_lookup[OF comp_lookup2[OF i_bound'] ext2]
      unfolding key_eq .
    show "map fst fl' ! i = map fst fl ! i"
      using lookup1_final lookup2_final i_bound' i_bound_old by simp
  qed
  show ?thesis
    using header_unique trace_bs_eq trace_bs'_eq comp_bs_eq comp_bs'_eq
      f_fl_fst_eq fl_fst_eq
    by simp
qed

lemma verify_monad_trace_fri_prequery_lookup:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs dg comp_bs"
    and header:
    "verifier_header_transcript s fr roots trace_final as dg
      composition_roots final rest"
    and i_len: "i < length roots"
    and lookup_s:
    "fmlookup (HashMap s)
      (TraceFriChallenge (PTraceFriCounter s + i)
        (foldl concat (concat (PState s) fr) (take (Suc i) roots))) =
      Some y"
  shows "i < length trace_bs \<and> y = trace_bs ! i"
proof (rule verify_monad_header_random_oracle_replay[OF outcome])
  fix fr' f_fl trace_final' as' dg' fl' final' query_state
  assume header_replay:
      "verifier_header_transcript s fr' (map snd f_fl) trace_final' as' dg'
        (map snd fl') final' (PTranscript query_state)"
    and query_state_eq:
      "PState query_state =
        verifier_header_state s fr' (map snd f_fl) trace_final' as' dg'
          (map snd fl') final'"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl trace_final' as' fl'
                final')
              rounds)
            query_state)"
    and query_count_header: "PQueryCounter query_state = PQueryCounter s"
    and ext_s_query: "s \<le> query_state"
    and trace_lookup:
      "\<And>j. j < length f_fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (TraceFriChallenge (PTraceFriCounter s + j)
            (foldl concat (concat (PState s) fr')
              (take (Suc j) (map snd f_fl)))) =
        Some (fst (f_fl ! j))"
    and comp_lookup:
      "\<And>j. j < length fl' \<Longrightarrow>
        fmlookup (HashMap query_state)
          (CompositionFriChallenge (PCompositionFriCounter s + j)
            (foldl concat
              (concat
                (foldl concat
                  (concat
                    (foldl concat (concat (PState s) fr') (map snd f_fl))
                    trace_final')
                  as')
                dg')
              (take (Suc j) (map snd fl')))) =
        Some (fst (fl' ! j))"
    and degree_bound: "to_nat dg' \<le> maxDegree"
  have replay_challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      (map fst f_fl) dg' (map fst fl')"
    unfolding accepted_fri_challenges_def
    by (intro exI[of _ result] exI[of _ final_state] exI[of _ fr']
        exI[of _ f_fl] exI[of _ trace_final'] exI[of _ as']
        exI[of _ fl'] exI[of _ final'] exI[of _ query_state])
      (use header_replay query_state_eq query_out query_count_header
        trace_lookup comp_lookup in auto)
  have trace_bs_eq: "trace_bs = map fst f_fl"
    using accepted_fri_challenges_unique[OF replay_challenges challenges]
    by simp
  have header_unique:
    "fr = fr' \<and>
     roots = map snd f_fl \<and>
     trace_final = trace_final' \<and>
     as = as' \<and>
     dg = dg' \<and>
     composition_roots = map snd fl' \<and>
     final = final' \<and>
     rest = PTranscript query_state"
    using verifier_header_transcript_unique[OF header header_replay]
    by simp
  have i_f_fl: "i < length f_fl"
    using i_len header_unique by simp
  have lookup_query_from_s:
    "fmlookup (HashMap query_state)
      (TraceFriChallenge (PTraceFriCounter s + i)
        (foldl concat (concat (PState s) fr) (take (Suc i) roots))) =
      Some y"
    by (rule hash_extension_lookup[OF lookup_s ext_s_query])
  have lookup_query_from_trace:
    "fmlookup (HashMap query_state)
      (TraceFriChallenge (PTraceFriCounter s + i)
        (foldl concat (concat (PState s) fr) (take (Suc i) roots))) =
      Some (trace_bs ! i)"
    using trace_lookup[OF i_f_fl] header_unique trace_bs_eq i_f_fl
    by simp
  then have y_eq: "y = trace_bs ! i"
    using lookup_query_from_s by simp
  have "i < length trace_bs"
    using i_f_fl trace_bs_eq by simp
  then show ?thesis
    using y_eq by simp
qed

lemma verify_monad_composition_fri_prequery_lookup:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs dg comp_bs"
    and header:
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots final rest"
    and i_len: "i < length composition_roots"
    and lookup_s:
    "fmlookup (HashMap s)
      (CompositionFriChallenge (PCompositionFriCounter s + i)
        (foldl concat
          (concat
            (foldl concat
              (concat
                (foldl concat (concat (PState s) fr) trace_roots)
                trace_final)
              as)
            dg)
          (take (Suc i) composition_roots))) =
      Some y"
  shows "i < length comp_bs \<and> y = comp_bs ! i"
proof (rule verify_monad_header_random_oracle_replay[OF outcome])
  fix fr' f_fl trace_final' as' dg' fl' final' query_state
  assume header_replay:
      "verifier_header_transcript s fr' (map snd f_fl) trace_final' as' dg'
        (map snd fl') final' (PTranscript query_state)"
    and query_state_eq:
      "PState query_state =
        verifier_header_state s fr' (map snd f_fl) trace_final' as' dg'
          (map snd fl') final'"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl trace_final' as' fl'
                final')
              rounds)
            query_state)"
    and query_count_header: "PQueryCounter query_state = PQueryCounter s"
    and ext_s_query: "s \<le> query_state"
    and trace_lookup:
      "\<And>j. j < length f_fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (TraceFriChallenge (PTraceFriCounter s + j)
            (foldl concat (concat (PState s) fr')
              (take (Suc j) (map snd f_fl)))) =
        Some (fst (f_fl ! j))"
    and comp_lookup:
      "\<And>j. j < length fl' \<Longrightarrow>
        fmlookup (HashMap query_state)
          (CompositionFriChallenge (PCompositionFriCounter s + j)
            (foldl concat
              (concat
                (foldl concat
                  (concat
                    (foldl concat (concat (PState s) fr') (map snd f_fl))
                    trace_final')
                  as')
                dg')
              (take (Suc j) (map snd fl')))) =
        Some (fst (fl' ! j))"
    and degree_bound: "to_nat dg' \<le> maxDegree"
  have replay_challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      (map fst f_fl) dg' (map fst fl')"
    unfolding accepted_fri_challenges_def
    by (intro exI[of _ result] exI[of _ final_state] exI[of _ fr']
        exI[of _ f_fl] exI[of _ trace_final'] exI[of _ as']
        exI[of _ fl'] exI[of _ final'] exI[of _ query_state])
      (use header_replay query_state_eq query_out query_count_header
        trace_lookup comp_lookup in auto)
  have comp_bs_eq: "comp_bs = map fst fl'"
    using accepted_fri_challenges_unique[OF replay_challenges challenges]
    by simp
  have header_unique:
    "fr = fr' \<and>
     trace_roots = map snd f_fl \<and>
     trace_final = trace_final' \<and>
     as = as' \<and>
     dg = dg' \<and>
     composition_roots = map snd fl' \<and>
     final = final' \<and>
     rest = PTranscript query_state"
    using verifier_header_transcript_unique[OF header header_replay]
    by simp
  have i_fl: "i < length fl'"
    using i_len header_unique by simp
  have lookup_query_from_s:
    "fmlookup (HashMap query_state)
      (CompositionFriChallenge (PCompositionFriCounter s + i)
        (foldl concat
          (concat
            (foldl concat
              (concat
                (foldl concat (concat (PState s) fr) trace_roots)
                trace_final)
              as)
            dg)
          (take (Suc i) composition_roots))) =
      Some y"
    by (rule hash_extension_lookup[OF lookup_s ext_s_query])
  have lookup_query_from_comp:
    "fmlookup (HashMap query_state)
      (CompositionFriChallenge (PCompositionFriCounter s + i)
        (foldl concat
          (concat
            (foldl concat
              (concat
                (foldl concat (concat (PState s) fr) trace_roots)
                trace_final)
              as)
            dg)
          (take (Suc i) composition_roots))) =
      Some (comp_bs ! i)"
    using comp_lookup[OF i_fl] header_unique comp_bs_eq i_fl
    by simp
  then have y_eq: "y = comp_bs ! i"
    using lookup_query_from_s by simp
  have "i < length comp_bs"
    using i_fl comp_bs_eq by simp
  then show ?thesis
    using y_eq by simp
qed

lemma verify_monad_accepted_fri_challenges_degree_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs dg comp_bs"
  shows "to_nat dg \<le> maxDegree"
proof -
  from verify_monad_header_random_oracle_replay[OF outcome]
  obtain fr f_fl f_final as dg' fl final query_state where
    header:
      "verifier_header_transcript s fr (map snd f_fl) f_final as dg'
        (map snd fl) final (PTranscript query_state)"
    and query_state_eq:
      "PState query_state =
        verifier_header_state s fr (map snd f_fl) f_final as dg'
          (map snd fl) final"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
    and query_count_header:
      "PQueryCounter query_state = PQueryCounter s"
    and trace_lookup:
      "\<And>i. i < length f_fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (TraceFriChallenge (PTraceFriCounter s + i) (foldl concat
            (concat (PState s) fr) (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))"
    and comp_lookup:
      "\<And>i. i < length fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
            (concat
              (foldl concat
                (concat
                  (foldl concat (concat (PState s) fr) (map snd f_fl))
                  f_final)
                as)
              dg')
            (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i))"
    and degree_bound: "to_nat dg' \<le> maxDegree"
    by metis
  have trace_lookup_all:
    "\<forall>i < length f_fl.
      fmlookup (HashMap query_state)
        (TraceFriChallenge (PTraceFriCounter s + i) (foldl concat
          (concat (PState s) fr) (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
    using trace_lookup by blast
  have comp_lookup_all:
    "\<forall>i < length fl.
      fmlookup (HashMap query_state)
        (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
          (concat
            (foldl concat
              (concat
                (foldl concat (concat (PState s) fr) (map snd f_fl))
                f_final)
              as)
            dg')
          (take (Suc i) (map snd fl)))) =
      Some (fst (fl ! i))"
    using comp_lookup by blast
  have challenges':
    "accepted_fri_challenges s (Some (result, final_state))
      (map fst f_fl) dg' (map fst fl)"
    unfolding accepted_fri_challenges_def
    by (intro exI[of _ result] exI[of _ final_state] exI[of _ fr]
        exI[of _ f_fl] exI[of _ f_final] exI[of _ as] exI[of _ fl]
        exI[of _ final] exI[of _ query_state])
      (use header query_state_eq query_out query_count_header
        trace_lookup_all comp_lookup_all in simp)
  have "dg' = dg"
    using accepted_fri_challenges_unique[OF challenges challenges'] by simp
  then show ?thesis
    using degree_bound by simp
qed

lemma verifier_after_trace_fri_accepted_fri_challenges:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((fr, f_fl), prefix_state) \<in>
      set_dist (execute verifier_trace_fri_prefix s)"
    and suffix:
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_trace_fri (fr, f_fl)) prefix_state)"
  shows "\<exists>dg comp_bs.
    accepted_fri_challenges s (Some (result, final_state))
      (map fst f_fl) dg comp_bs"
proof -
  have prefix_res:
    "length f_fl = ceil_log clength \<and>
     PTranscript s = [fr] @ map snd f_fl @ PTranscript prefix_state \<and>
     PState prefix_state =
        foldl concat (concat (PState s) fr) (map snd f_fl) \<and>
     s \<le> prefix_state \<and>
     PTraceFriCounter prefix_state = PTraceFriCounter s + ceil_log clength \<and>
     PCompositionFriCounter prefix_state = PCompositionFriCounter s \<and>
     PAlphaCounter prefix_state = PAlphaCounter s \<and>
     PQueryCounter prefix_state = PQueryCounter s \<and>
     (\<forall>i < length f_fl.
        fmlookup (HashMap prefix_state)
          (TraceFriChallenge (PTraceFriCounter s + i)
            (foldl concat (concat (PState s) fr)
              (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i)))"
    by (rule verifier_trace_fri_prefix_outcome[OF prefix])
  from suffix obtain f_final s3 as s4 dg s5 s6 fl s7 final query_state where
    read_trace_final:
      "Some (f_final, s3) \<in> set_dist (execute read prefix_state)"
    and alpha_out:
      "Some (as, s4) \<in>
        set_dist (execute (mmap (replicate (length spec) alpha_round)) s3)"
    and read_dg: "Some (dg, s5) \<in> set_dist (execute read s4)"
    and degree_assert:
      "Some ((), s6) \<in>
        set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
    and comp_fri:
      "Some (fl, s7) \<in>
        set_dist (execute
          (ntimes receive_composition_fri_commits
            (ceil_log (to_nat dg + 1))) s6)"
    and read_final: "Some (final, query_state) \<in> set_dist (execute read s7)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist (execute
          (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
    unfolding verifier_after_trace_fri_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_trace_final] obtain rest3 where
    tr_prefix: "PTranscript prefix_state = f_final # rest3"
    and st_s3: "PState s3 = concat (PState prefix_state) f_final"
    and tr_s3: "PTranscript s3 = rest3"
    and ext_prefix_s3: "prefix_state \<le> s3"
    and trace_count_s3: "PTraceFriCounter s3 = PTraceFriCounter prefix_state"
    and comp_count_s3: "PCompositionFriCounter s3 = PCompositionFriCounter prefix_state"
    and alpha_count_s3: "PAlphaCounter s3 = PAlphaCounter prefix_state"
    and query_count_s3: "PQueryCounter s3 = PQueryCounter prefix_state"
    by blast
  have alpha_res:
    "length as = length spec \<and>
     PTranscript s3 = as @ PTranscript s4 \<and>
     PState s4 = foldl concat (PState s3) as \<and>
     s3 \<le> s4 \<and>
     PTraceFriCounter s4 = PTraceFriCounter s3 \<and>
     PCompositionFriCounter s4 = PCompositionFriCounter s3 \<and>
     PAlphaCounter s4 = PAlphaCounter s3 + length spec \<and>
     PQueryCounter s4 = PQueryCounter s3"
    using mmap_alpha_round_outcome[OF alpha_out] by simp
  from read_outcome[OF read_dg] obtain rest5 where
    tr_s4: "PTranscript s4 = dg # rest5"
    and st_s5: "PState s5 = concat (PState s4) dg"
    and tr_s5: "PTranscript s5 = rest5"
    and ext_s4_s5: "s4 \<le> s5"
    and trace_count_s5: "PTraceFriCounter s5 = PTraceFriCounter s4"
    and comp_count_s5: "PCompositionFriCounter s5 = PCompositionFriCounter s4"
    and alpha_count_s5: "PAlphaCounter s5 = PAlphaCounter s4"
    and query_count_s5: "PQueryCounter s5 = PQueryCounter s4"
    by blast
  have s6_eq: "s6 = s5"
    using degree_assert unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
  have ext_s5_s6: "s5 \<le> s6"
    unfolding s6_eq by (rule hash_ext_refl)
  have comp_res:
    "length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s6 = map snd fl @ PTranscript s7 \<and>
     PState s7 = foldl concat (PState s6) (map snd fl) \<and>
     s6 \<le> s7 \<and>
     PTraceFriCounter s7 = PTraceFriCounter s6 \<and>
     PCompositionFriCounter s7 =
        PCompositionFriCounter s6 + ceil_log (to_nat dg + 1) \<and>
     PAlphaCounter s7 = PAlphaCounter s6 \<and>
     PQueryCounter s7 = PQueryCounter s6 \<and>
     (\<forall>i < ceil_log (to_nat dg + 1).
        fmlookup (HashMap s7)
          (CompositionFriChallenge (PCompositionFriCounter s6 + i)
            (foldl concat (PState s6) (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i)))"
    using ntimes_receive_composition_fri_commits_outcome[OF comp_fri]
    by simp
  from read_outcome[OF read_final] obtain rest_query where
    tr_s7: "PTranscript s7 = final # rest_query"
    and st_query: "PState query_state = concat (PState s7) final"
    and tr_query: "PTranscript query_state = rest_query"
    and ext_s7_query: "s7 \<le> query_state"
    and query_count_query: "PQueryCounter query_state = PQueryCounter s7"
    by blast
  have ext_prefix_query: "prefix_state \<le> query_state"
    using ext_prefix_s3 alpha_res ext_s4_s5 ext_s5_s6 comp_res ext_s7_query
    by (meson hash_ext_trans)
  have header:
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    using prefix_res tr_prefix tr_s3 alpha_res tr_s4 tr_s5 s6_eq comp_res
      tr_s7 tr_query
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
  have header_state:
    "PState query_state =
      verifier_header_state s fr (map snd f_fl) f_final as dg
        (map snd fl) final"
    using prefix_res st_s3 alpha_res st_s5 s6_eq comp_res st_query
    unfolding verifier_header_state_def verifier_header_messages_def
    by simp
  have query_count_header:
    "PQueryCounter query_state = PQueryCounter s"
    using prefix_res query_count_s3 alpha_res query_count_s5 s6_eq comp_res
      query_count_query
    by simp
  have trace_lookup:
    "\<And>i. i < length f_fl \<Longrightarrow>
      fmlookup (HashMap query_state)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
  proof -
    fix i
    assume i_bound: "i < length f_fl"
    have lookup_prefix:
      "fmlookup (HashMap prefix_state)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
      using prefix_res i_bound by simp
    show "fmlookup (HashMap query_state)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
      by (rule hash_extension_lookup[OF lookup_prefix ext_prefix_query])
  qed
  have comp_lookup:
    "\<And>i. i < length fl \<Longrightarrow>
      fmlookup (HashMap query_state)
        (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
              as)
            dg)
          (take (Suc i) (map snd fl)))) =
      Some (fst (fl ! i))"
  proof -
    fix i
    assume i_bound: "i < length fl"
    have lookup_s7:
      "fmlookup (HashMap s7)
        (CompositionFriChallenge (PCompositionFriCounter s6 + i)
          (foldl concat (PState s6) (take (Suc i) (map snd fl)))) =
      Some (fst (fl ! i))"
      using comp_res i_bound by simp
    show "fmlookup (HashMap query_state)
        (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
              as)
            dg)
          (take (Suc i) (map snd fl)))) =
      Some (fst (fl ! i))"
      using hash_extension_lookup[OF lookup_s7 ext_s7_query]
        prefix_res st_s3 alpha_res st_s5 s6_eq comp_count_s3 comp_count_s5
      by simp
  qed
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      (map fst f_fl) dg (map fst fl)"
    unfolding accepted_fri_challenges_def
    apply (rule exI[where x=result])
    apply (rule exI[where x=final_state])
    apply (rule exI[where x=fr])
    apply (rule exI[where x=f_fl])
    apply (rule exI[where x=f_final])
    apply (rule exI[where x=as])
    apply (rule exI[where x=fl])
    apply (rule exI[where x=final])
    apply (rule exI[where x=query_state])
    apply (intro conjI)
             apply simp
            apply (rule header)
           apply (rule header_state)
          apply (rule query_out)
         apply (rule query_count_header)
        apply simp
       apply simp
      apply (intro allI impI, rule trace_lookup, assumption)
     apply (intro allI impI, rule comp_lookup, assumption)
    done
  show ?thesis
    using challenges by blast
qed

lemma verifier_after_composition_fri_accepted_fri_challenges:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((fr, f_fl, f_final, as, dg, fl), prefix_state) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
    and suffix:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (verifier_after_composition_fri
              (fr, f_fl, f_final, as, dg, fl))
            prefix_state)"
  shows "accepted_fri_challenges s (Some (result, final_state))
    (map fst f_fl) dg (map fst fl)"
proof -
  have prefix_res:
    "length f_fl = ceil_log clength \<and>
     length as = length spec \<and>
     length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s =
       [fr] @ map snd f_fl @ [f_final] @ as @ [dg] @
       map snd fl @ PTranscript prefix_state \<and>
     PState prefix_state =
       foldl concat
        (concat
          (foldl concat
            (concat
              (foldl concat (concat (PState s) fr) (map snd f_fl))
              f_final)
            as)
          dg)
        (map snd fl) \<and>
     s \<le> prefix_state \<and>
     PQueryCounter prefix_state = PQueryCounter s \<and>
     (\<forall>i < length f_fl.
        fmlookup (HashMap prefix_state)
          (TraceFriChallenge (PTraceFriCounter s + i)
            (foldl concat (concat (PState s) fr)
              (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))) \<and>
     (\<forall>i < length fl.
        fmlookup (HashMap prefix_state)
          (CompositionFriChallenge (PCompositionFriCounter s + i)
            (foldl concat
              (concat
                (foldl concat
                  (concat
                    (foldl concat (concat (PState s) fr) (map snd f_fl))
                    f_final)
                  as)
                dg)
              (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i)))"
    by (rule verifier_composition_fri_prefix_outcome[OF prefix])
  from suffix obtain final query_state where
    read_final:
      "Some (final, query_state) \<in>
        set_dist (execute read prefix_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist (execute
          (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
    unfolding verifier_after_composition_fri_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_final] obtain rest_query where
    tr_prefix: "PTranscript prefix_state = final # rest_query"
    and st_query: "PState query_state = concat (PState prefix_state) final"
    and tr_query: "PTranscript query_state = rest_query"
    and ext_prefix_query: "prefix_state \<le> query_state"
    and query_count_query:
      "PQueryCounter query_state = PQueryCounter prefix_state"
    by blast
  have header:
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    using prefix_res tr_prefix tr_query
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
  have header_state:
    "PState query_state =
      verifier_header_state s fr (map snd f_fl) f_final as dg
        (map snd fl) final"
    using prefix_res st_query
    unfolding verifier_header_state_def verifier_header_messages_def
    by simp
  have query_count_header:
    "PQueryCounter query_state = PQueryCounter s"
    using prefix_res query_count_query by simp
  have trace_lookup:
    "\<And>i. i < length f_fl \<Longrightarrow>
      fmlookup (HashMap query_state)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
  proof -
    fix i
    assume i_bound: "i < length f_fl"
    have lookup_prefix:
      "fmlookup (HashMap prefix_state)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
      using prefix_res i_bound by simp
    show "fmlookup (HashMap query_state)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
      by (rule hash_extension_lookup[OF lookup_prefix ext_prefix_query])
  qed
  have comp_lookup:
    "\<And>i. i < length fl \<Longrightarrow>
      fmlookup (HashMap query_state)
        (CompositionFriChallenge (PCompositionFriCounter s + i)
          (foldl concat
            (concat
              (foldl concat
                (concat
                  (foldl concat (concat (PState s) fr) (map snd f_fl))
                  f_final)
                as)
              dg)
            (take (Suc i) (map snd fl)))) =
      Some (fst (fl ! i))"
  proof -
    fix i
    assume i_bound: "i < length fl"
    have lookup_prefix:
      "fmlookup (HashMap prefix_state)
        (CompositionFriChallenge (PCompositionFriCounter s + i)
          (foldl concat
            (concat
              (foldl concat
                (concat
                  (foldl concat (concat (PState s) fr) (map snd f_fl))
                  f_final)
                as)
              dg)
            (take (Suc i) (map snd fl)))) =
      Some (fst (fl ! i))"
      using prefix_res i_bound by simp
    show "fmlookup (HashMap query_state)
        (CompositionFriChallenge (PCompositionFriCounter s + i)
          (foldl concat
            (concat
              (foldl concat
                (concat
                  (foldl concat (concat (PState s) fr) (map snd f_fl))
                  f_final)
                as)
              dg)
            (take (Suc i) (map snd fl)))) =
      Some (fst (fl ! i))"
      by (rule hash_extension_lookup[OF lookup_prefix ext_prefix_query])
  qed
  show ?thesis
    unfolding accepted_fri_challenges_def
    apply (rule exI[where x=result])
    apply (rule exI[where x=final_state])
    apply (rule exI[where x=fr])
    apply (rule exI[where x=f_fl])
    apply (rule exI[where x=f_final])
    apply (rule exI[where x=as])
    apply (rule exI[where x=fl])
    apply (rule exI[where x=final])
    apply (rule exI[where x=query_state])
    apply (intro conjI)
             apply simp
            apply (rule header)
           apply (rule header_state)
          apply (rule query_out)
         apply (rule query_count_header)
        apply simp
       apply simp
      apply (intro allI impI, rule trace_lookup, assumption)
     apply (intro allI impI, rule comp_lookup, assumption)
    done
qed

definition trace_fri_challenge_list_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list set \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_challenge_list_set_hit s B out \<longleftrightarrow>
      (\<exists>trace_bs dg comp_bs.
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        trace_bs \<in> B)"

definition trace_fri_root_list_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_root_list_set_hit s B out \<longleftrightarrow>
      (\<exists>trace_bs dg comp_bs fr f_fri_roots f_final as composition_fri_roots
          final rest.
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest \<and>
        trace_bs \<in> B fr)"

definition composition_fri_challenge_list_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> ('f \<Rightarrow> 'f list set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_fri_challenge_list_set_hit s B out \<longleftrightarrow>
      (\<exists>trace_bs dg comp_bs.
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        comp_bs \<in> B dg)"

definition composition_fri_root_list_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
        'f list \<Rightarrow> 'f list set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_fri_root_list_set_hit s B out \<longleftrightarrow>
      (\<exists>trace_bs dg comp_bs fr f_fri_roots f_final as
          composition_fri_roots final rest.
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest \<and>
        comp_bs \<in> B fr f_fri_roots f_final as dg composition_fri_roots)"

lemma wp_verify_monad_trace_fri_challenge_list_set_bound:
  assumes future: "trace_fri_future_fresh s"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
  shows
    "wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s \<le>
      nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
proof -
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((_, f_fl), _) \<Rightarrow> map fst f_fl \<in> B"
  have prefix_bound:
    "wp_event verifier_trace_fri_prefix ?Head s \<le>
      nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verifier_trace_fri_prefix_challenge_space_set_bound
        [OF future subset])
  show ?thesis
    unfolding verify_monad_trace_fri_decomposition
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show "trace_fri_challenge_list_set_hit s B None \<Longrightarrow> ?Head None"
      unfolding trace_fri_challenge_list_set_hit_def
        accepted_fri_challenges_def by blast
  next
    fix header prefix_state out
    assume prefix:
      "Some (header, prefix_state) \<in>
        set_dist (execute verifier_trace_fri_prefix s)"
      and suffix:
        "out \<in>
          set_dist (execute (verifier_after_trace_fri header) prefix_state)"
      and hit: "trace_fri_challenge_list_set_hit s B out"
    obtain fr f_fl where header_eq: "header = (fr, f_fl)"
      by (cases header) auto
    from hit obtain trace_bs dg comp_bs where
      challenges_hit: "accepted_fri_challenges s out trace_bs dg comp_bs"
      and trace_bs_B: "trace_bs \<in> B"
      unfolding trace_fri_challenge_list_set_hit_def by blast
    from challenges_hit obtain result final_state where out_eq:
      "out = Some (result, final_state)"
      unfolding accepted_fri_challenges_def by blast
    have prefix':
      "Some ((fr, f_fl), prefix_state) \<in>
        set_dist (execute verifier_trace_fri_prefix s)"
      using prefix header_eq by simp
    have suffix':
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_trace_fri (fr, f_fl)) prefix_state)"
      using suffix header_eq out_eq by simp
    from verifier_after_trace_fri_accepted_fri_challenges[OF prefix' suffix']
    obtain dg' comp_bs' where
      challenges_prefix:
        "accepted_fri_challenges s (Some (result, final_state))
          (map fst f_fl) dg' comp_bs'"
      by blast
    have "trace_bs = map fst f_fl"
      using accepted_fri_challenges_unique
        [OF challenges_prefix challenges_hit[unfolded out_eq]]
      by simp
    then show "?Head (Some (header, prefix_state))"
      using trace_bs_B header_eq by simp
  qed
qed

lemma wp_verify_monad_trace_fri_root_list_set_bound:
  fixes C :: prob
  assumes future: "trace_fri_future_fresh s"
    and subset: "\<And>fr. B fr \<subseteq> fri_challenge_space (ceil_log clength)"
    and bound:
      "\<And>fr. nnreal (card (B fr)) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "wp_event verify_monad (trace_fri_root_list_set_hit s B) s \<le> C"
proof -
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl), _) \<Rightarrow> map fst f_fl \<in> B fr"
  have prefix_bound:
    "wp_event verifier_trace_fri_prefix ?Head s \<le> C"
    by (rule wp_verifier_trace_fri_prefix_dependent_challenge_space_set_bound
        [OF future subset bound])
  show ?thesis
    unfolding verify_monad_trace_fri_decomposition
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show "trace_fri_root_list_set_hit s B None \<Longrightarrow> ?Head None"
      unfolding trace_fri_root_list_set_hit_def
        accepted_fri_challenges_def by blast
  next
    fix header prefix_state out
    assume prefix:
      "Some (header, prefix_state) \<in>
        set_dist (execute verifier_trace_fri_prefix s)"
      and suffix:
        "out \<in>
          set_dist (execute (verifier_after_trace_fri header) prefix_state)"
      and hit: "trace_fri_root_list_set_hit s B out"
    obtain fr f_fl where header_eq: "header = (fr, f_fl)"
      by (cases header) auto
    from hit obtain trace_bs dg comp_bs fr' f_fri_roots' f_final' as'
        composition_fri_roots' final' rest' where
      challenges_hit: "accepted_fri_challenges s out trace_bs dg comp_bs"
      and header_hit:
        "verifier_header_transcript s fr' f_fri_roots' f_final' as' dg
          composition_fri_roots' final' rest'"
      and trace_bs_B: "trace_bs \<in> B fr'"
      unfolding trace_fri_root_list_set_hit_def by blast
    from challenges_hit obtain result final_state where out_eq:
      "out = Some (result, final_state)"
      unfolding accepted_fri_challenges_def by blast
    have prefix':
      "Some ((fr, f_fl), prefix_state) \<in>
        set_dist (execute verifier_trace_fri_prefix s)"
      using prefix header_eq by simp
    have suffix':
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_trace_fri (fr, f_fl)) prefix_state)"
      using suffix header_eq out_eq by simp
    have prefix_res:
      "PTranscript s = [fr] @ map snd f_fl @ PTranscript prefix_state"
      using verifier_trace_fri_prefix_outcome[OF prefix'] by simp
    have fr_eq: "fr' = fr"
      using prefix_res header_hit
      unfolding verifier_header_transcript_def verifier_header_messages_def
      by simp
    from verifier_after_trace_fri_accepted_fri_challenges[OF prefix' suffix']
    obtain dg' comp_bs' where
      challenges_prefix:
        "accepted_fri_challenges s (Some (result, final_state))
          (map fst f_fl) dg' comp_bs'"
      by blast
    have trace_bs_eq: "trace_bs = map fst f_fl"
      using accepted_fri_challenges_unique
        [OF challenges_prefix challenges_hit[unfolded out_eq]]
      by simp
    then show "?Head (Some (header, prefix_state))"
      using trace_bs_B fr_eq header_eq by simp
  qed
qed

lemma wp_verify_monad_composition_fri_root_list_set_bound:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and subset:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots.
        B fr f_fri_roots f_final as dg composition_fri_roots \<subseteq>
          fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots.
        nnreal
          (card
            (B fr f_fri_roots f_final as dg composition_fri_roots)) /
          nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad (composition_fri_root_list_set_hit s B) s \<le> C"
proof -
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl, f_final, as, dg, fl), _) \<Rightarrow>
          map fst fl \<in> B fr (map snd f_fl) f_final as dg (map snd fl)"
  have prefix_bound:
    "wp_event verifier_composition_fri_prefix ?Head s \<le> C"
    by (rule wp_verifier_composition_fri_prefix_root_dependent_challenge_space_set_bound
        [OF future subset bound])
  show ?thesis
    unfolding verify_monad_composition_fri_decomposition
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show "composition_fri_root_list_set_hit s B None \<Longrightarrow> ?Head None"
      unfolding composition_fri_root_list_set_hit_def
        accepted_fri_challenges_def by blast
  next
    fix header prefix_state out
    assume prefix:
      "Some (header, prefix_state) \<in>
        set_dist (execute verifier_composition_fri_prefix s)"
      and suffix:
        "out \<in>
          set_dist (execute
            (verifier_after_composition_fri header) prefix_state)"
      and hit: "composition_fri_root_list_set_hit s B out"
    obtain fr f_fl f_final as dg fl where header_eq:
      "header = (fr, f_fl, f_final, as, dg, fl)"
      by (cases header) auto
    from hit obtain trace_bs dg' comp_bs fr' f_fri_roots' f_final' as'
        composition_fri_roots' final' rest' where
      challenges_hit:
        "accepted_fri_challenges s out trace_bs dg' comp_bs"
      and header_hit:
        "verifier_header_transcript s fr' f_fri_roots' f_final' as' dg'
          composition_fri_roots' final' rest'"
      and comp_bs_B:
        "comp_bs \<in>
          B fr' f_fri_roots' f_final' as' dg' composition_fri_roots'"
      unfolding composition_fri_root_list_set_hit_def by blast
    from challenges_hit obtain result final_state where out_eq:
      "out = Some (result, final_state)"
      unfolding accepted_fri_challenges_def by blast
    have prefix':
      "Some ((fr, f_fl, f_final, as, dg, fl), prefix_state) \<in>
        set_dist (execute verifier_composition_fri_prefix s)"
      using prefix header_eq by simp
    have suffix':
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (verifier_after_composition_fri
              (fr, f_fl, f_final, as, dg, fl))
            prefix_state)"
      using suffix header_eq out_eq by simp
    from suffix'[unfolded verifier_after_composition_fri_def]
    obtain final query_state where
      read_final:
        "Some (final, query_state) \<in> set_dist (execute read prefix_state)"
      and query_out:
        "Some (result, final_state) \<in>
          set_dist
            (execute
              (ntimes
                (verifier_query_round_program fr f_fl f_final as fl final)
                rounds)
              query_state)"
      by (auto elim!: set_dist_bindE)
    have prefix_res:
      "length f_fl = ceil_log clength \<and>
       length as = length spec \<and>
       length fl = ceil_log (to_nat dg + 1) \<and>
       PTranscript s =
         [fr] @ map snd f_fl @ [f_final] @ as @ [dg] @
         map snd fl @ PTranscript prefix_state"
      using verifier_composition_fri_prefix_outcome[OF prefix'] by simp
    from read_outcome[OF read_final] obtain rest_query where
      tr_prefix: "PTranscript prefix_state = final # rest_query"
      and tr_query: "PTranscript query_state = rest_query"
      by blast
    have header_prefix:
      "verifier_header_transcript s fr (map snd f_fl) f_final as dg
        (map snd fl) final (PTranscript query_state)"
      using prefix_res tr_prefix tr_query
      unfolding verifier_header_transcript_def verifier_header_messages_def
      by simp
    have header_eqs:
      "fr' = fr \<and>
       f_fri_roots' = map snd f_fl \<and>
       f_final' = f_final \<and>
       as' = as \<and>
       dg' = dg \<and>
       composition_fri_roots' = map snd fl"
      using verifier_header_transcript_unique[OF header_prefix header_hit]
      by simp
    have challenges_prefix:
      "accepted_fri_challenges s (Some (result, final_state))
        (map fst f_fl) dg (map fst fl)"
      by (rule verifier_after_composition_fri_accepted_fri_challenges
          [OF prefix' suffix'])
    have comp_bs_eq: "comp_bs = map fst fl"
      using accepted_fri_challenges_unique
        [OF challenges_prefix challenges_hit[unfolded out_eq]]
      by simp
    show "?Head (Some (header, prefix_state))"
      using comp_bs_B comp_bs_eq header_eqs header_eq by simp
  qed
qed

lemma wp_verify_monad_composition_fri_challenge_list_set_bound:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s \<le> C"
proof -
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((_, _, _, _, dg, fl), _) \<Rightarrow> map fst fl \<in> B dg"
  have prefix_bound:
    "wp_event verifier_composition_fri_prefix ?Head s \<le> C"
    by (rule wp_verifier_composition_fri_prefix_challenge_space_set_bound
        [OF future subset bound])
  show ?thesis
    unfolding verify_monad_composition_fri_decomposition
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show "composition_fri_challenge_list_set_hit s B None \<Longrightarrow> ?Head None"
      unfolding composition_fri_challenge_list_set_hit_def
        accepted_fri_challenges_def by blast
  next
    fix header prefix_state out
    assume prefix:
      "Some (header, prefix_state) \<in>
        set_dist (execute verifier_composition_fri_prefix s)"
      and suffix:
        "out \<in>
          set_dist (execute
            (verifier_after_composition_fri header) prefix_state)"
      and hit: "composition_fri_challenge_list_set_hit s B out"
    obtain fr f_fl f_final as dg fl where header_eq:
      "header = (fr, f_fl, f_final, as, dg, fl)"
      by (cases header) auto
    from hit obtain trace_bs dg' comp_bs where
      challenges_hit: "accepted_fri_challenges s out trace_bs dg' comp_bs"
      and comp_bs_B: "comp_bs \<in> B dg'"
      unfolding composition_fri_challenge_list_set_hit_def by blast
    from challenges_hit obtain result final_state where out_eq:
      "out = Some (result, final_state)"
      unfolding accepted_fri_challenges_def by blast
    have prefix':
      "Some ((fr, f_fl, f_final, as, dg, fl), prefix_state) \<in>
        set_dist (execute verifier_composition_fri_prefix s)"
      using prefix header_eq by simp
    have suffix':
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (verifier_after_composition_fri
              (fr, f_fl, f_final, as, dg, fl))
            prefix_state)"
      using suffix header_eq out_eq by simp
    have challenges_prefix:
      "accepted_fri_challenges s (Some (result, final_state))
        (map fst f_fl) dg (map fst fl)"
      by (rule verifier_after_composition_fri_accepted_fri_challenges
          [OF prefix' suffix'])
    have eqs:
      "trace_bs = map fst f_fl \<and> dg' = dg \<and> comp_bs = map fst fl"
      using accepted_fri_challenges_unique
        [OF challenges_prefix challenges_hit[unfolded out_eq]]
      by simp
    then show "?Head (Some (header, prefix_state))"
      using comp_bs_B header_eq by simp
  qed
qed

lemma verifier_initial_alpha_list_set_error_bound:
  assumes subset: "B \<subseteq> alpha_space"
    and bounded:
      "nnreal (card B) / nnreal (card alpha_space) \<le>
        composition_error_bound"
  shows
    "wp_event verify_monad
      (alpha_list_set_hit (verifier_initial_state tr) B)
      (verifier_initial_state tr) \<le> composition_error_bound"
proof -
  have "wp_event verify_monad
      (alpha_list_set_hit (verifier_initial_state tr) B)
      (verifier_initial_state tr) \<le>
      nnreal (card B) / nnreal (card alpha_space)"
    by (rule wp_verify_monad_alpha_list_set_bound) (use subset in simp_all)
  also have "... \<le> composition_error_bound"
    by (rule bounded)
  finally show ?thesis .
qed

lemma verifier_initial_trace_fri_challenge_list_set_error_bound:
  assumes subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and bounded:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le>
        trace_fri_error"
  shows
    "wp_event verify_monad
      (trace_fri_challenge_list_set_hit (verifier_initial_state tr) B)
      (verifier_initial_state tr) \<le> trace_fri_error"
proof -
  have "wp_event verify_monad
      (trace_fri_challenge_list_set_hit (verifier_initial_state tr) B)
      (verifier_initial_state tr) \<le>
      nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verify_monad_trace_fri_challenge_list_set_bound)
      (use subset in simp_all)
  also have "... \<le> trace_fri_error"
    by (rule bounded)
  finally show ?thesis .
qed

lemma verifier_initial_composition_fri_challenge_list_set_error_bound:
  assumes subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bounded:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
        composition_fri_error"
  shows
    "wp_event verify_monad
      (composition_fri_challenge_list_set_hit (verifier_initial_state tr) B)
      (verifier_initial_state tr) \<le> composition_fri_error"
  by (rule wp_verify_monad_composition_fri_challenge_list_set_bound)
    (use subset bounded in simp_all)

definition accepted_fri_opening_transcript
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      nat list \<Rightarrow> 'f list list list \<Rightarrow> 'f list list list \<Rightarrow> bool"
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers \<longleftrightarrow>
      (\<exists>result final_state fr f_fl as fl query_state raw_idxs query_chunks.
        out = Some (result, final_state) \<and>
        trace_roots = map snd f_fl \<and>
        trace_bs = map fst f_fl \<and>
        composition_roots = map snd fl \<and>
        composition_bs = map fst fl \<and>
        accepted_fri_challenges s out trace_bs dg composition_bs \<and>
        verifier_header_transcript s fr trace_roots trace_final as dg
          composition_roots composition_final (PTranscript query_state) \<and>
        PState query_state =
          verifier_header_state s fr trace_roots trace_final as dg
            composition_roots composition_final \<and>
        PQueryCounter query_state = PQueryCounter s \<and>
        Some (result, final_state) \<in>
          set_dist (execute
            (ntimes
              (verifier_query_round_program fr f_fl trace_final as fl
                composition_final)
              rounds)
            query_state) \<and>
        verifier_query_indices_derived s out
          (verifier_header_state s fr trace_roots trace_final as dg
            composition_roots composition_final)
          (PTranscript query_state) trace_roots composition_roots query_idxs \<and>
        length trace_round_layers = rounds \<and>
        length composition_round_layers = rounds \<and>
        length raw_idxs = rounds \<and>
        query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
        length query_chunks = rounds \<and>
        PTranscript query_state =
          List.concat query_chunks @ PTranscript final_state \<and>
        (\<forall>i < rounds.
          verifier_query_round_chunk (query_idxs ! i)
            trace_roots composition_roots (query_chunks ! i)) \<and>
        (\<forall>i < rounds.
          query_round_fri_layer_transcripts (query_idxs ! i)
            trace_roots composition_roots (query_chunks ! i)
            (trace_round_layers ! i) (composition_round_layers ! i)) \<and>
        (\<forall>i < rounds.
          fmlookup (HashMap final_state)
            (QueryIndexChallenge (PQueryCounter query_state + i) (state_after_query_chunks (PState query_state) query_chunks i)) =
            Some (raw_idxs ! i)) \<and>
        (\<forall>idx \<in> set query_idxs. idx < clength * scale))"

lemma verify_monad_accepted_fri_opening_transcript:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  obtains trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final query_idxs trace_round_layers composition_round_layers
  where "accepted_fri_opening_transcript s (Some (result, final_state))
    trace_roots trace_bs trace_final dg composition_roots composition_bs
    composition_final query_idxs trace_round_layers composition_round_layers"
proof -
  from verify_monad_accepted_fri_challenges[OF outcome]
  obtain trace_bs dg composition_bs where challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs dg composition_bs"
    by blast
  then obtain result' final_state' fr f_fl trace_final as fl composition_final
      query_state where
    out_eq: "Some (result, final_state) = Some (result', final_state')"
    and trace_bs_eq: "trace_bs = map fst f_fl"
    and composition_bs_eq: "composition_bs = map fst fl"
    and header:
      "verifier_header_transcript s fr (map snd f_fl) trace_final as dg
        (map snd fl) composition_final (PTranscript query_state)"
    and query_state_eq:
      "PState query_state =
        verifier_header_state s fr (map snd f_fl) trace_final as dg
          (map snd fl) composition_final"
    and query_out:
      "Some (result', final_state') \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr f_fl trace_final as fl
              composition_final)
            rounds)
          query_state)"
    and query_count_header:
      "PQueryCounter query_state = PQueryCounter s"
    unfolding accepted_fri_challenges_def by blast
  have result'_eq: "result' = result"
    using out_eq by simp
  have final_state'_eq: "final_state' = final_state"
    using out_eq by simp
  have query_out':
    "Some (result, final_state) \<in>
      set_dist (execute
        (ntimes
          (verifier_query_round_program fr f_fl trace_final as fl
            composition_final)
          rounds)
        query_state)"
    using query_out result'_eq final_state'_eq by simp
  from ntimes_verifier_query_rounds_outcome[OF query_out']
  obtain raw_idxs query_idxs query_chunks where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_def: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and tr_query:
      "PTranscript query_state = List.concat query_chunks @ PTranscript final_state"
    and round_chunks:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and lookups:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i) (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    and idx_bounds:
      "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by auto
  have layer_exists:
    "\<forall>i < rounds.
      \<exists>trace_layers composition_layers.
        query_round_fri_layer_transcripts (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)
          trace_layers composition_layers"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < rounds"
    from verifier_query_round_chunk_fri_layer_transcriptsE
      [OF round_chunks[OF i_bound]]
    show "\<exists>trace_layers composition_layers.
        query_round_fri_layer_transcripts (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)
          trace_layers composition_layers"
      by blast
  qed
  then obtain trace_layers_of composition_layers_of where layer_of:
    "\<And>i. i < rounds \<Longrightarrow>
      query_round_fri_layer_transcripts (query_idxs ! i)
        (map snd f_fl) (map snd fl) (query_chunks ! i)
        (trace_layers_of i) (composition_layers_of i)"
    by metis
  let ?trace_round_layers = "map trace_layers_of [0..<rounds]"
  let ?composition_round_layers = "map composition_layers_of [0..<rounds]"
  have layers:
    "\<forall>i < rounds.
      query_round_fri_layer_transcripts (query_idxs ! i)
        (map snd f_fl) (map snd fl) (query_chunks ! i)
        (?trace_round_layers ! i) (?composition_round_layers ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < rounds"
    then show "query_round_fri_layer_transcripts (query_idxs ! i)
        (map snd f_fl) (map snd fl) (query_chunks ! i)
        (?trace_round_layers ! i) (?composition_round_layers ! i)"
      using layer_of[OF i_bound] by simp
  qed
  have derived:
    "verifier_query_indices_derived s (Some (result, final_state))
      (verifier_header_state s fr (map snd f_fl) trace_final as dg
        (map snd fl) composition_final)
      (PTranscript query_state) (map snd f_fl) (map snd fl) query_idxs"
  proof -
    have tr_query':
      "List.concat query_chunks @ PTranscript final_state = PTranscript query_state"
      using tr_query by simp
    have lookups':
      "\<forall>i < rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter s + i) (state_after_query_chunks
            (verifier_header_state s fr (map snd f_fl) trace_final as dg
              (map snd fl) composition_final)
            query_chunks i)) =
        Some (raw_idxs ! i)"
      using lookups query_state_eq query_count_header by simp
    show ?thesis
      unfolding verifier_query_indices_derived_def
      apply (rule exI[where x=result])
      apply (rule exI[where x=final_state])
      apply (rule exI[where x=raw_idxs])
      apply (rule exI[where x=query_chunks])
      apply (rule exI[where x="PTranscript final_state"])
      apply (intro conjI)
              apply simp
             apply (rule len_raw)
            apply (rule query_idxs_def)
           apply (rule len_chunks)
        apply (rule tr_query')
       apply (intro allI impI, rule round_chunks, assumption)
       apply (rule lookups')
      using idx_bounds by simp
  qed
  have tr_query_tail:
    "List.concat query_chunks @ PTranscript final_state = PTranscript query_state"
    using tr_query by simp
  have lookups_all:
    "\<forall>i < rounds.
      fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter query_state + i) (state_after_query_chunks (PState query_state) query_chunks i)) =
      Some (raw_idxs ! i)"
    using lookups by blast
  have lookups_all_header:
    "\<forall>i < rounds.
      fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks
            (verifier_header_state s fr (map snd f_fl) trace_final as dg
              (map snd fl) composition_final)
            query_chunks i)) =
      Some (raw_idxs ! i)"
    using lookups_all query_state_eq by simp
  have challenges_maps:
    "accepted_fri_challenges s (Some (result, final_state))
      (map fst f_fl) dg (map fst fl)"
    using challenges trace_bs_eq composition_bs_eq by simp
  have derived_maps:
    "verifier_query_indices_derived s (Some (result, final_state))
      (verifier_header_state s fr (map snd f_fl) trace_final as dg
        (map snd fl) composition_final)
      (PTranscript query_state) (map snd f_fl) (map snd fl)
      (map (\<lambda>raw. index (to_nat raw)) raw_idxs)"
    using derived query_idxs_def by simp
  have layers_maps:
    "\<forall>i < rounds.
      query_round_fri_layer_transcripts (index (to_nat (raw_idxs ! i)))
        (map snd f_fl) (map snd fl) (query_chunks ! i)
        (trace_layers_of i) (composition_layers_of i)"
    using layers query_idxs_def len_raw by auto
  have round_chunks_raw:
    "\<forall>i < rounds.
      verifier_query_round_chunk (index (to_nat (raw_idxs ! i)))
        (map snd f_fl) (map snd fl) (query_chunks ! i)"
    using round_chunks query_idxs_def len_raw by auto
  have lookups_header:
    "\<forall>i < rounds.
      fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter s + i) (state_after_query_chunks
          (verifier_header_state s fr (map snd f_fl) trace_final as dg
            (map snd fl) composition_final)
          query_chunks i)) =
      Some (raw_idxs ! i)"
    using lookups_all query_state_eq query_count_header by simp
  have accepted:
    "accepted_fri_opening_transcript s (Some (result, final_state))
      (map snd f_fl) trace_bs trace_final dg (map snd fl) composition_bs
      composition_final query_idxs ?trace_round_layers ?composition_round_layers"
    unfolding accepted_fri_opening_transcript_def
    apply (rule exI[where x=result])
    apply (rule exI[where x=final_state])
    apply (rule exI[where x=fr])
    apply (rule exI[where x=f_fl])
    apply (rule exI[where x=as])
    apply (rule exI[where x=fl])
    apply (rule exI[where x=query_state])
    apply (rule exI[where x=raw_idxs])
    apply (rule exI[where x=query_chunks])
    apply (simp add: challenges header query_state_eq query_out' derived len_raw
      query_count_header query_idxs_def len_chunks tr_query_tail layers
      lookups_all idx_bounds trace_bs_eq composition_bs_eq challenges_maps
      derived_maps layers_maps lookups_header lookups_all_header round_chunks)
    apply (rule round_chunks_raw)
    done
  then show ?thesis
    by (rule that)
qed

lemma accepted_fri_opening_transcript_challenges:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
  shows "accepted_fri_challenges s out trace_bs dg composition_bs"
  using fri_openings
  unfolding accepted_fri_opening_transcript_def
  apply (elim exE conjE)
  apply assumption
  done

lemma accepted_fri_opening_transcript_trace_challenge_list_set_hit:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and member: "trace_bs \<in> B"
  shows "trace_fri_challenge_list_set_hit s B out"
  using fri_openings
  unfolding accepted_fri_opening_transcript_def trace_fri_challenge_list_set_hit_def
  apply (elim exE conjE)
  apply (intro exI conjI)
   apply assumption
  apply (rule member)
  done

lemma accepted_fri_opening_transcript_composition_challenge_list_set_hit:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and member: "composition_bs \<in> B dg"
  shows "composition_fri_challenge_list_set_hit s B out"
  using fri_openings
  unfolding accepted_fri_opening_transcript_def
    composition_fri_challenge_list_set_hit_def
  apply (elim exE conjE)
  apply (intro exI conjI)
   apply assumption
  apply (rule member)
  done

lemma accepted_fri_opening_transcript_shapes:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
  shows "length trace_roots = ceil_log clength"
    and "length trace_bs = length trace_roots"
    and "length composition_roots = ceil_log (to_nat dg + 1)"
    and "length composition_bs = length composition_roots"
    and "length trace_round_layers = rounds"
    and "length composition_round_layers = rounds"
    and "length query_idxs = rounds"
  using fri_openings
  unfolding accepted_fri_opening_transcript_def verifier_header_transcript_def
  by auto

lemma accepted_fri_opening_transcript_algebraic_round_counts:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
  shows "length trace_roots = trace_fri_algebraic_round_count"
    and "length trace_bs = trace_fri_algebraic_round_count"
    and "length composition_roots = composition_fri_algebraic_round_count dg"
    and "length composition_bs = composition_fri_algebraic_round_count dg"
    and "length trace_round_layers = rounds"
    and "length composition_round_layers = rounds"
    and "length query_idxs = rounds"
proof -
  have shapes:
    "length trace_roots = ceil_log clength"
    "length trace_bs = length trace_roots"
    "length composition_roots = ceil_log (to_nat dg + 1)"
    "length composition_bs = length composition_roots"
    "length trace_round_layers = rounds"
    "length composition_round_layers = rounds"
    "length query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes[OF fri_openings] by blast+
  show "length trace_roots = trace_fri_algebraic_round_count"
    using shapes(1) by (simp add: trace_fri_algebraic_round_count_eq)
  show "length trace_bs = trace_fri_algebraic_round_count"
    using shapes(1,2) by (simp add: trace_fri_algebraic_round_count_eq)
  show "length composition_roots = composition_fri_algebraic_round_count dg"
    using shapes(3) by (simp add: composition_fri_algebraic_round_count_eq)
  show "length composition_bs = composition_fri_algebraic_round_count dg"
    using shapes(3,4) by (simp add: composition_fri_algebraic_round_count_eq)
  show "length trace_round_layers = rounds"
    using shapes(5) .
  show "length composition_round_layers = rounds"
    using shapes(6) .
  show "length query_idxs = rounds"
    using shapes(7) .
qed

lemma accepted_fri_opening_transcript_trace_round_layer_length:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and round_bound: "round_idx < rounds"
  shows "length (trace_round_layers ! round_idx) = length trace_roots"
proof -
  obtain result final_state fr f_fl as fl query_state raw_idxs query_chunks
    where layers:
      "\<And>i. i < rounds \<Longrightarrow>
        query_round_fri_layer_transcripts (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)
          (trace_round_layers ! i) (composition_round_layers ! i)"
    using fri_openings unfolding accepted_fri_opening_transcript_def by blast
  from layers[OF round_bound]
  obtain query_chunk trace_fri_chunk composition_fri_chunk leaves paths where
    trace_layers:
      "fri_layers_transcript (length trace_roots) (clength * scale)
        (trace_round_layers ! round_idx) trace_fri_chunk"
    unfolding query_round_fri_layer_transcripts_def by blast
  then show ?thesis
    unfolding fri_layers_transcript_def by simp
qed

lemma accepted_fri_opening_transcript_composition_round_layer_length:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and round_bound: "round_idx < rounds"
  shows "length (composition_round_layers ! round_idx) = length composition_roots"
proof -
  obtain result final_state fr f_fl as fl query_state raw_idxs query_chunks
    where layers:
      "\<And>i. i < rounds \<Longrightarrow>
        query_round_fri_layer_transcripts (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)
          (trace_round_layers ! i) (composition_round_layers ! i)"
    using fri_openings unfolding accepted_fri_opening_transcript_def by blast
  from layers[OF round_bound]
  obtain query_chunk trace_fri_chunk composition_fri_chunk leaves paths where
    composition_layers:
      "fri_layers_transcript (length composition_roots) (clength * scale)
        (composition_round_layers ! round_idx) composition_fri_chunk"
    unfolding query_round_fri_layer_transcripts_def by blast
  then show ?thesis
    unfolding fri_layers_transcript_def by simp
qed

lemma accepted_fri_opening_transcript_trace_layer_opening:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and round_bound: "round_idx < rounds"
    and layer_bound: "layer_idx < length trace_roots"
  obtains root challenge len idx sibling_idx xp xp_path xn xn_path
  where "root = trace_roots ! layer_idx"
    and "challenge = trace_bs ! layer_idx"
    and "len = fri_layer_lengths (length trace_roots) (clength * scale) ! layer_idx"
    and "idx =
      fri_layer_indices (length trace_roots) (query_idxs ! round_idx)
        (clength * scale) ! layer_idx"
    and "sibling_idx = fri_sibling_index len idx"
    and "fri_layer_opening_chunk len xp xp_path xn xn_path
      (trace_round_layers ! round_idx ! layer_idx)"
proof -
  obtain result final_state fr f_fl as fl query_state raw_idxs query_chunks
    where layers:
        "\<And>i. i < rounds \<Longrightarrow>
          query_round_fri_layer_transcripts (query_idxs ! i)
            trace_roots composition_roots (query_chunks ! i)
            (trace_round_layers ! i) (composition_round_layers ! i)"
    using fri_openings unfolding accepted_fri_opening_transcript_def by blast
  from layers[OF round_bound]
  obtain query_chunk trace_fri_chunk composition_fri_chunk leaves paths where
    trace_layers:
      "fri_layers_transcript (length trace_roots) (clength * scale)
        (trace_round_layers ! round_idx) trace_fri_chunk"
    unfolding query_round_fri_layer_transcripts_def by blast
  from fri_layers_transcript_nth_opening[OF trace_layers layer_bound]
  obtain xp xp_path xn xn_path where layer_opening:
    "fri_layer_opening_chunk
      (fri_layer_lengths (length trace_roots) (clength * scale) ! layer_idx)
      xp xp_path xn xn_path (trace_round_layers ! round_idx ! layer_idx)"
    by blast
  let ?len = "fri_layer_lengths (length trace_roots) (clength * scale) ! layer_idx"
  let ?idx =
    "fri_layer_indices (length trace_roots) (query_idxs ! round_idx)
      (clength * scale) ! layer_idx"
  let ?sidx = "fri_sibling_index ?len ?idx"
  show ?thesis
    by (rule that[of "trace_roots ! layer_idx" "trace_bs ! layer_idx"
          ?len ?idx ?sidx xp xp_path xn xn_path])
      (use layer_opening in simp_all)
qed

lemma accepted_fri_opening_transcript_composition_layer_opening:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and round_bound: "round_idx < rounds"
    and layer_bound: "layer_idx < length composition_roots"
  obtains root challenge len idx sibling_idx xp xp_path xn xn_path
  where "root = composition_roots ! layer_idx"
    and "challenge = composition_bs ! layer_idx"
    and "len =
      fri_layer_lengths (length composition_roots) (clength * scale) ! layer_idx"
    and "idx =
      fri_layer_indices (length composition_roots) (query_idxs ! round_idx)
        (clength * scale) ! layer_idx"
    and "sibling_idx = fri_sibling_index len idx"
    and "fri_layer_opening_chunk len xp xp_path xn xn_path
      (composition_round_layers ! round_idx ! layer_idx)"
proof -
  obtain result final_state fr f_fl as fl query_state raw_idxs query_chunks
    where layers:
        "\<And>i. i < rounds \<Longrightarrow>
          query_round_fri_layer_transcripts (query_idxs ! i)
            trace_roots composition_roots (query_chunks ! i)
            (trace_round_layers ! i) (composition_round_layers ! i)"
    using fri_openings unfolding accepted_fri_opening_transcript_def by blast
  from layers[OF round_bound]
  obtain query_chunk trace_fri_chunk composition_fri_chunk leaves paths where
    composition_layers:
      "fri_layers_transcript (length composition_roots) (clength * scale)
        (composition_round_layers ! round_idx) composition_fri_chunk"
    unfolding query_round_fri_layer_transcripts_def by blast
  from fri_layers_transcript_nth_opening[OF composition_layers layer_bound]
  obtain xp xp_path xn xn_path where layer_opening:
    "fri_layer_opening_chunk
      (fri_layer_lengths (length composition_roots) (clength * scale) ! layer_idx)
      xp xp_path xn xn_path
      (composition_round_layers ! round_idx ! layer_idx)"
    by blast
  let ?len =
    "fri_layer_lengths (length composition_roots) (clength * scale) ! layer_idx"
  let ?idx =
    "fri_layer_indices (length composition_roots) (query_idxs ! round_idx)
      (clength * scale) ! layer_idx"
  let ?sidx = "fri_sibling_index ?len ?idx"
  show ?thesis
    by (rule that[of "composition_roots ! layer_idx" "composition_bs ! layer_idx"
          ?len ?idx ?sidx xp xp_path xn xn_path])
      (use layer_opening in simp_all)
qed

subsection \<open>Global FRI table bindings\<close>

text \<open>
  The verifier sees authenticated local openings.  The following predicates
  describe the stronger deterministic object needed by the algebraic FRI
  argument: complete layer tables bound to the Merkle roots, with all local
  openings matching the corresponding table entries.
\<close>

definition fri_layer_tables_shape
  :: "nat \<Rightarrow> 'f list list \<Rightarrow> bool"
  where
    "fri_layer_tables_shape n tables \<longleftrightarrow>
      length tables = n \<and>
      (\<forall>j < n.
        length (tables ! j) =
          fri_layer_lengths n (clength * scale) ! j)"

definition fri_roots_bind_tables
  :: "'f list \<Rightarrow> 'f list list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "fri_roots_bind_tables roots tables final_state \<longleftrightarrow>
      length tables = length roots \<and>
      (\<forall>j < length roots.
        merkle_root_binds_table (roots ! j) (tables ! j) final_state)"

definition fri_bound_layer_tables
  :: "'f list \<Rightarrow> 'f list list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "fri_bound_layer_tables roots tables final_state \<longleftrightarrow>
      fri_layer_tables_shape (length roots) tables \<and>
      fri_roots_bind_tables roots tables final_state"

definition fri_layer_opening_matches_bound_table
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow> bool"
  where
    "fri_layer_opening_matches_bound_table query_idx layer_idx tables
      layer_chunks \<longleftrightarrow>
      layer_idx < length tables \<and>
      length layer_chunks = length tables \<and>
      (let len =
          fri_layer_lengths (length tables) (clength * scale) ! layer_idx;
          idx =
          fri_layer_indices (length tables) query_idx (clength * scale) !
            layer_idx
       in \<exists>xp xp_path xn xn_path.
          fri_layer_opening_chunk len xp xp_path xn xn_path
            (layer_chunks ! layer_idx) \<and>
          fri_opening_matches_table len idx (tables ! layer_idx) xp xn)"

definition fri_round_openings_match_tables
  :: "'f list list \<Rightarrow> nat \<Rightarrow> 'f list list \<Rightarrow> bool"
  where
    "fri_round_openings_match_tables tables query_idx layer_chunks \<longleftrightarrow>
      length layer_chunks = length tables \<and>
      (\<forall>j < length tables.
        fri_layer_opening_matches_bound_table query_idx j tables
          layer_chunks)"

definition fri_all_round_openings_match_tables
  :: "'f list list \<Rightarrow> nat list \<Rightarrow> 'f list list list \<Rightarrow> bool"
  where
    "fri_all_round_openings_match_tables tables query_idxs round_layers \<longleftrightarrow>
      length round_layers = length query_idxs \<and>
      (\<forall>i < length query_idxs.
        fri_round_openings_match_tables tables (query_idxs ! i)
          (round_layers ! i))"

definition fri_final_table_matches
  :: "'f list \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "fri_final_table_matches final_table final \<longleftrightarrow>
      final_table \<noteq> [] \<and>
      fri_final_constant_consistent final_table final"

definition trace_fri_tables_bound
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "trace_fri_tables_bound s out trace_roots trace_bs trace_final
      query_idxs trace_round_layers trace_tables trace_final_table \<longleftrightarrow>
      (\<exists>result final_state dg composition_roots composition_bs
          composition_final composition_round_layers.
        out = Some (result, final_state) \<and>
        accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final dg composition_roots composition_bs composition_final
          query_idxs trace_round_layers composition_round_layers \<and>
        fri_bound_layer_tables trace_roots trace_tables final_state \<and>
        fri_all_round_openings_match_tables trace_tables query_idxs
          trace_round_layers \<and>
        fri_final_table_matches trace_final_table trace_final)"

definition composition_fri_tables_bound
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "composition_fri_tables_bound s out dg composition_roots
      composition_bs composition_final query_idxs composition_round_layers
      composition_tables composition_final_table \<longleftrightarrow>
      (\<exists>result final_state trace_roots trace_bs trace_final
          trace_round_layers.
        out = Some (result, final_state) \<and>
        accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final dg composition_roots composition_bs composition_final
          query_idxs trace_round_layers composition_round_layers \<and>
        fri_bound_layer_tables composition_roots composition_tables
          final_state \<and>
        fri_all_round_openings_match_tables composition_tables query_idxs
          composition_round_layers \<and>
        fri_final_table_matches composition_final_table composition_final)"

definition fri_initial_table_agrees
  :: "'f list \<Rightarrow> 'f list list \<Rightarrow> bool"
  where
    "fri_initial_table_agrees initial_table tables \<longleftrightarrow>
      tables = [] \<or> hd tables = initial_table"

definition fri_merkle_binding_good
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "fri_merkle_binding_good s out \<longleftrightarrow>
      accepted out \<longrightarrow>
        (\<exists>trace_table composition_table as query_idxs
            trace_roots trace_bs trace_final dg composition_roots
            composition_bs composition_final trace_round_layers
            composition_round_layers trace_tables composition_tables
            trace_final_table composition_final_table.
          accepted_with_bound_tables s out trace_table composition_table as
            query_idxs \<and>
          accepted_fri_opening_transcript s out trace_roots trace_bs
            trace_final dg composition_roots composition_bs
            composition_final query_idxs trace_round_layers
            composition_round_layers \<and>
          trace_fri_tables_bound s out trace_roots trace_bs trace_final
            query_idxs trace_round_layers trace_tables trace_final_table \<and>
          composition_fri_tables_bound s out dg composition_roots
            composition_bs composition_final query_idxs
            composition_round_layers composition_tables
            composition_final_table \<and>
          fri_initial_table_agrees trace_table trace_tables \<and>
          fri_initial_table_agrees composition_table composition_tables)"

definition fri_merkle_binding_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "fri_merkle_binding_bad s out \<longleftrightarrow>
      accepted out \<and> \<not> fri_merkle_binding_good s out"

definition fri_merkle_binding_bound
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "fri_merkle_binding_bound s \<longleftrightarrow>
      wp_event verify_monad (fri_merkle_binding_bad s) s \<le>
        merkle_binding_error"

end

end
