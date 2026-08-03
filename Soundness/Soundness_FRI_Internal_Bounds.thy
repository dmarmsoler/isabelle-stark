(*  Title:      Stark/Soundness_FRI_Internal_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Internal_Bounds
  imports Soundness_FRI_Generic_Low_Degree
begin

text \<open>
  Internal concrete FRI challenge-list bounds.

  These lemmas deliberately avoid the symbolic parameters
  \<^term>\<open>trace_fri_error\<close> and \<^term>\<open>composition_fri_error\<close>.  They expose the
  concrete bad-set fractions obtained from the generic FRI bad challenge-list
  interface.  Later public-route work can either use these concrete terms
  directly, or relate the symbolic error parameters to these terms via an
  explicitly chosen FRI soundness interface.
\<close>

context soundness
begin

definition fri_bad_challenge_round_mass
  :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
where
  "fri_bad_challenge_round_mass n bd =
    (\<Sum>i \<in> {..<n}. CARD('f) ^ i * bd i * CARD('f) ^ (n - Suc i))"

definition fri_bad_challenge_round_fraction
  :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> prob"
where
  "fri_bad_challenge_round_fraction n bd =
    nnreal (fri_bad_challenge_round_mass n bd) / nnreal (CARD('f) ^ n)"

definition fri_one_step_disagreement_round_mass
  :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
where
  "fri_one_step_disagreement_round_mass n len =
    fri_bad_challenge_round_mass n (\<lambda>i. len i div 2)"

definition fri_one_step_disagreement_round_fraction
  :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> prob"
where
  "fri_one_step_disagreement_round_fraction n len =
    fri_bad_challenge_round_fraction n (\<lambda>i. len i div 2)"

lemma fri_one_step_disagreement_round_fraction_unfold:
  "fri_one_step_disagreement_round_fraction n len =
    nnreal
      (\<Sum>i \<in> {..<n}.
        CARD('f) ^ i * (len i div 2) * CARD('f) ^ (n - Suc i)) /
      nnreal (CARD('f) ^ n)"
  unfolding fri_one_step_disagreement_round_fraction_def
    fri_bad_challenge_round_fraction_def
    fri_bad_challenge_round_mass_def
  by simp

lemma fri_one_step_disagreement_round_fraction_refl_bound:
  "nnreal
      (\<Sum>i \<in> {..<n}.
        CARD('f) ^ i * (len i div 2) * CARD('f) ^ (n - Suc i)) /
      nnreal (CARD('f) ^ n)
    \<le> fri_one_step_disagreement_round_fraction n len"
  by (simp add: fri_one_step_disagreement_round_fraction_unfold)

definition trace_fri_canonical_layer_len :: "nat \<Rightarrow> nat"
where
  "trace_fri_canonical_layer_len i =
    fri_layer_lengths (fri_round_count_for_degree_bound (clength - 1))
      (clength * scale) ! i"

definition composition_fri_canonical_layer_len :: "'f \<Rightarrow> nat \<Rightarrow> nat"
where
  "composition_fri_canonical_layer_len dg i =
    fri_layer_lengths (fri_round_count_for_degree_bound (to_nat dg))
      (clength * scale) ! i"

definition concrete_trace_fri_bad_challenge_fraction :: prob
where
  "concrete_trace_fri_bad_challenge_fraction =
    fri_one_step_disagreement_round_fraction
      (fri_round_count_for_degree_bound (clength - 1))
      trace_fri_canonical_layer_len"

definition concrete_composition_fri_bad_challenge_fraction :: prob
where
  "concrete_composition_fri_bad_challenge_fraction =
    Max
      ((\<lambda>dg :: 'f.
        fri_one_step_disagreement_round_fraction
          (fri_round_count_for_degree_bound (to_nat dg))
          (composition_fri_canonical_layer_len dg)) ` UNIV)"

lemma concrete_trace_fri_bad_challenge_fraction_eq:
  "fri_one_step_disagreement_round_fraction
      (fri_round_count_for_degree_bound (clength - 1))
      trace_fri_canonical_layer_len
    = concrete_trace_fri_bad_challenge_fraction"
  by (simp add: concrete_trace_fri_bad_challenge_fraction_def)

lemma concrete_composition_fri_bad_challenge_fraction_ge:
  "fri_one_step_disagreement_round_fraction
      (fri_round_count_for_degree_bound (to_nat dg))
      (composition_fri_canonical_layer_len dg)
    \<le> concrete_composition_fri_bad_challenge_fraction"
  unfolding concrete_composition_fri_bad_challenge_fraction_def
  by (rule Max_ge) simp_all

lemma fri_bad_challenge_round_fraction_bound_from_round_bounds:
  assumes local_bound:
    "\<And>i prefix. i < n \<Longrightarrow> length prefix = i \<Longrightarrow>
      card (bad i prefix) \<le> bd i"
  shows "nnreal (card (generic_fri_bad_challenge_lists n bad)) /
      nnreal (CARD('f) ^ n)
    \<le> fri_bad_challenge_round_fraction n bd"
  unfolding fri_bad_challenge_round_fraction_def
    fri_bad_challenge_round_mass_def
  by (rule nnreal_nat_divide_right_mono)
    (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds
      [OF local_bound])

lemma generic_fri_bad_challenge_lists_card_bound_from_one_step_disagreement_subset:
  assumes local_subset:
    "\<And>i prefix. i < n \<Longrightarrow> length prefix = i \<Longrightarrow>
      bad i prefix \<subseteq>
        fri_one_step_disagreement_challenges
          (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
  shows "card (generic_fri_bad_challenge_lists n bad) \<le>
    (\<Sum>i \<in> {..<n}.
      CARD('f) ^ i * (len i div 2) * CARD('f) ^ (n - Suc i))"
proof (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds)
  fix i :: nat and prefix :: "'f list"
  assume i_bound: "i < n" and prefix_len: "length prefix = i"
  have "card (bad i prefix) \<le>
      card
        (fri_one_step_disagreement_challenges
          (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix))"
    by (rule card_mono) (simp_all add: local_subset[OF i_bound prefix_len])
  also have "... \<le> len i div 2"
    by (rule fri_one_step_disagreement_challenges_card_bound_local)
  finally show "card (bad i prefix) \<le> len i div 2" .
qed

lemma generic_fri_bad_challenge_lists_bounded_by_from_one_step_disagreement_subset:
  assumes local_subset:
    "\<And>i prefix. i < n \<Longrightarrow> length prefix = i \<Longrightarrow>
      bad i prefix \<subseteq>
        fri_one_step_disagreement_challenges
          (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
  shows "fri_bad_challenge_lists_bounded_by n
    (generic_fri_bad_challenge_lists n bad)
    (\<Sum>i \<in> {..<n}.
      CARD('f) ^ i * (len i div 2) * CARD('f) ^ (n - Suc i))"
  by (rule generic_fri_bad_challenge_lists_bounded_byI)
    (rule generic_fri_bad_challenge_lists_card_bound_from_one_step_disagreement_subset
      [OF local_subset])

lemma fri_bad_challenge_round_fraction_bound_from_one_step_disagreement_subset:
  assumes local_subset:
    "\<And>i prefix. i < n \<Longrightarrow> length prefix = i \<Longrightarrow>
      bad i prefix \<subseteq>
        fri_one_step_disagreement_challenges
          (len i) (pw i) (layer i prefix) (claimed i prefix) (domains i prefix)"
  shows "nnreal (card (generic_fri_bad_challenge_lists n bad)) /
      nnreal (CARD('f) ^ n)
    \<le> fri_one_step_disagreement_round_fraction n len"
  unfolding fri_one_step_disagreement_round_fraction_def
    fri_bad_challenge_round_fraction_def
    fri_one_step_disagreement_round_mass_def
    fri_bad_challenge_round_mass_def
  by (rule nnreal_nat_divide_right_mono)
    (rule generic_fri_bad_challenge_lists_card_bound_from_one_step_disagreement_subset
      [OF local_subset])

lemma wp_verify_monad_trace_generic_fri_bad_challenge_list_bound:
  assumes future: "trace_fri_future_fresh s"
  shows
    "wp_event verify_monad
      (trace_fri_challenge_list_set_hit s
        (generic_fri_bad_challenge_lists trace_fri_algebraic_round_count bad))
      s
    \<le>
      nnreal
        (card
          (generic_fri_bad_challenge_lists trace_fri_algebraic_round_count
            bad)) /
      nnreal (CARD('f) ^ ceil_log clength)"
proof (rule wp_verify_monad_trace_fri_challenge_list_set_bound[OF future])
  show "generic_fri_bad_challenge_lists trace_fri_algebraic_round_count bad
      \<subseteq> fri_challenge_space (ceil_log clength)"
    using generic_fri_bad_challenge_lists_subset
    by (simp add: trace_fri_algebraic_round_count_eq)
qed

lemma wp_verify_monad_trace_generic_fri_bad_challenge_list_bound_from_card:
  assumes future: "trace_fri_future_fresh s"
    and card_bound:
      "card (generic_fri_bad_challenge_lists trace_fri_algebraic_round_count
        bad) \<le> bd"
  shows
    "wp_event verify_monad
      (trace_fri_challenge_list_set_hit s
        (generic_fri_bad_challenge_lists trace_fri_algebraic_round_count bad))
      s
    \<le> nnreal bd / nnreal (CARD('f) ^ ceil_log clength)"
proof -
  have "wp_event verify_monad
      (trace_fri_challenge_list_set_hit s
        (generic_fri_bad_challenge_lists trace_fri_algebraic_round_count bad))
      s
    \<le>
      nnreal
        (card
          (generic_fri_bad_challenge_lists trace_fri_algebraic_round_count
            bad)) /
      nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verify_monad_trace_generic_fri_bad_challenge_list_bound
        [OF future])
  also have "... \<le> nnreal bd / nnreal (CARD('f) ^ ceil_log clength)"
    by (rule nnreal_nat_divide_right_mono[OF card_bound])
  finally show ?thesis .
qed

lemma wp_verify_monad_trace_generic_fri_bad_challenge_list_bound_from_rounds:
  assumes future: "trace_fri_future_fresh s"
    and local_bound:
      "\<And>i prefix. i < trace_fri_algebraic_round_count \<Longrightarrow>
        length prefix = i \<Longrightarrow> card (bad i prefix) \<le> bd i"
  shows
    "wp_event verify_monad
      (trace_fri_challenge_list_set_hit s
        (generic_fri_bad_challenge_lists trace_fri_algebraic_round_count bad))
      s
    \<le>
      nnreal
        (\<Sum>i \<in> {..<trace_fri_algebraic_round_count}.
          CARD('f) ^ i * bd i *
          CARD('f) ^ (trace_fri_algebraic_round_count - Suc i)) /
      nnreal (CARD('f) ^ ceil_log clength)"
  by (rule wp_verify_monad_trace_generic_fri_bad_challenge_list_bound_from_card
      [OF future])
    (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds
      [OF local_bound])

lemma wp_verify_monad_composition_generic_fri_bad_challenge_list_bound:
  assumes future: "composition_fri_future_fresh s"
    and bound:
      "\<And>dg.
        nnreal
          (card
            (generic_fri_bad_challenge_lists
              (composition_fri_algebraic_round_count dg) (bad dg))) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_challenge_list_set_hit s
        (\<lambda>dg. generic_fri_bad_challenge_lists
          (composition_fri_algebraic_round_count dg) (bad dg)))
      s \<le> C"
proof (rule wp_verify_monad_composition_fri_challenge_list_set_bound
    [OF future])
  fix dg
  show "generic_fri_bad_challenge_lists
      (composition_fri_algebraic_round_count dg) (bad dg)
      \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    using generic_fri_bad_challenge_lists_subset
    by (simp add: composition_fri_algebraic_round_count_eq)
  show "nnreal
      (card
        (generic_fri_bad_challenge_lists
          (composition_fri_algebraic_round_count dg) (bad dg))) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
    by (rule bound)
qed

lemma wp_verify_monad_composition_generic_fri_bad_challenge_list_bound_from_card:
  assumes future: "composition_fri_future_fresh s"
    and card_bound:
      "\<And>dg. card
        (generic_fri_bad_challenge_lists
          (composition_fri_algebraic_round_count dg) (bad dg)) \<le> bd dg"
    and fraction_bound:
      "\<And>dg. nnreal (bd dg) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_challenge_list_set_hit s
        (\<lambda>dg. generic_fri_bad_challenge_lists
          (composition_fri_algebraic_round_count dg) (bad dg)))
      s \<le> C"
proof (rule wp_verify_monad_composition_generic_fri_bad_challenge_list_bound
    [OF future])
  fix dg
  have "nnreal
      (card
        (generic_fri_bad_challenge_lists
          (composition_fri_algebraic_round_count dg) (bad dg))) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))
    \<le> nnreal (bd dg) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
    by (rule nnreal_nat_divide_right_mono[OF card_bound])
  also have "... \<le> C"
    by (rule fraction_bound)
  finally show "nnreal
      (card
        (generic_fri_bad_challenge_lists
          (composition_fri_algebraic_round_count dg) (bad dg))) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C" .
qed

lemma wp_verify_monad_composition_generic_fri_bad_challenge_list_bound_from_rounds:
  assumes future: "composition_fri_future_fresh s"
    and local_bound:
      "\<And>dg i prefix. i < composition_fri_algebraic_round_count dg \<Longrightarrow>
        length prefix = i \<Longrightarrow> card (bad dg i prefix) \<le> bd dg i"
    and fraction_bound:
      "\<And>dg. nnreal
        (\<Sum>i \<in> {..<composition_fri_algebraic_round_count dg}.
          CARD('f) ^ i * bd dg i *
          CARD('f) ^ (composition_fri_algebraic_round_count dg - Suc i)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_challenge_list_set_hit s
        (\<lambda>dg. generic_fri_bad_challenge_lists
          (composition_fri_algebraic_round_count dg) (bad dg)))
      s \<le> C"
proof (rule
    wp_verify_monad_composition_generic_fri_bad_challenge_list_bound_from_card
    [OF future _ fraction_bound])
  fix dg
  show "card
      (generic_fri_bad_challenge_lists
        (composition_fri_algebraic_round_count dg) (bad dg))
      \<le>
      (\<Sum>i \<in> {..<composition_fri_algebraic_round_count dg}.
        CARD('f) ^ i * bd dg i *
        CARD('f) ^ (composition_fri_algebraic_round_count dg - Suc i))"
    by (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds)
      (rule local_bound[of _ dg], simp_all)
qed

end

end
