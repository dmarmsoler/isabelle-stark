theory Soundness_FRI_Robust_Exact_Rate_Multiround
  imports Soundness_FRI_Robust_Multiround
begin

context soundness
begin

lemma fri_linear_good_radius_le_sixteenth_eight:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < m"
    and exponent_fit: "m + K \<le> N"
    and capacity: "8 * Suc m \<le> 2 ^ K"
  shows
    "fri_linear_good_radius m K i \<le>
      length (fri_canonical_domain_at i) div 16"
proof (rule less_eq_div_iff_mult_less_eq[
    OF zero_less_numeral, THEN iffD2])
  let ?u = "fri_linear_unit K (Suc i)"
  let ?c = "m - i + 1"
  have c_le: "?c \<le> Suc m"
    by simp
  have scaled_c: "8 * ?c \<le> 2 ^ K"
  proof -
    have "8 * ?c \<le> 8 * Suc m"
      using c_le by simp
    also have "... \<le> 2 ^ K"
      by (rule capacity)
    finally show ?thesis .
  qed
  have doubled_scaled_c: "2 * (8 * ?c) \<le> 2 * 2 ^ K"
    using scaled_c by simp
  have unit_step:
      "fri_linear_unit K i = 2 * ?u"
    by (rule fri_linear_unit_step[
          OF eval_power round_bound exponent_fit])
  have reconstruct:
      "2 ^ K * fri_linear_unit K i =
        length (fri_canonical_domain_at i)"
    by (rule fri_linear_unit_reconstruct[OF eval_power])
      (use round_bound exponent_fit in linarith)
  have
      "fri_linear_good_radius m K i * 16 =
        (2 * (8 * ?c)) * ?u"
    unfolding fri_linear_good_radius_def
    by (simp add: algebra_simps)
  also have "... \<le> (2 * 2 ^ K) * ?u"
    by (rule mult_right_mono[OF doubled_scaled_c]) simp
  also have "... = 2 ^ K * (2 * ?u)"
    by (simp add: algebra_simps)
  also have "... = length (fri_canonical_domain_at i)"
    using reconstruct unit_step by simp
  finally show
      "fri_linear_good_radius m K i * 16 \<le>
        length (fri_canonical_domain_at i)" .
qed


lemma fri_linear_good_radius_list_compatible_eight:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < m"
    and exponent_fit: "m + K \<le> N"
    and capacity: "8 * Suc m \<le> 2 ^ K"
  shows
    "4 * fri_linear_good_radius m K i \<le>
      length (fri_canonical_domain_at i) div 4"
proof -
  have small:
      "fri_linear_good_radius m K i \<le>
        length (fri_canonical_domain_at i) div 16"
    by (rule fri_linear_good_radius_le_sixteenth_eight[
          OF eval_power round_bound exponent_fit capacity])
  have multiplied:
      "4 * fri_linear_good_radius m K i \<le>
        4 * (length (fri_canonical_domain_at i) div 16)"
    using small by simp
  show ?thesis
    using multiplied four_sixteenth_le_quarter[
      of "length (fri_canonical_domain_at i)"] by linarith
qed

definition fri_linear_exact_list_cap_at ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "fri_linear_exact_list_cap_at d m K L i \<longleftrightarrow>
    (let n = length (fri_canonical_domain_at i);
         degree = fri_degree_after i (fri_padded_degree_bound d);
         radius = 4 * fri_linear_good_radius m K i
     in radius \<le> n \<and>
        degree \<le> n \<and>
        n * degree < (n - radius)^2 \<and>
        n * (n - degree) div ((n - radius)^2 - n * degree) \<le> L)"

definition fri_linear_exact_list_cap ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "fri_linear_exact_list_cap d m K L \<longleftrightarrow>
    (\<forall>i<m. fri_linear_exact_list_cap_at d m K L i)"

lemma fri_linear_exact_list_capD:
  assumes exact: "fri_linear_exact_list_cap d m K L"
    and active: "i < m"
  obtains
    "4 * fri_linear_good_radius m K i \<le>
      length (fri_canonical_domain_at i)"
    "fri_degree_after i (fri_padded_degree_bound d) \<le>
      length (fri_canonical_domain_at i)"
    "length (fri_canonical_domain_at i) *
        fri_degree_after i (fri_padded_degree_bound d) <
      (length (fri_canonical_domain_at i) -
        4 * fri_linear_good_radius m K i)^2"
    "length (fri_canonical_domain_at i) *
        (length (fri_canonical_domain_at i) -
          fri_degree_after i (fri_padded_degree_bound d)) div
        ((length (fri_canonical_domain_at i) -
            4 * fri_linear_good_radius m K i)^2 -
          length (fri_canonical_domain_at i) *
            fri_degree_after i (fri_padded_degree_bound d)) \<le> L"
  using exact active
  unfolding fri_linear_exact_list_cap_def
    fri_linear_exact_list_cap_at_def Let_def
  by blast


lemma fri_rs_active_layer_linear_exact_list_cap:
  assumes eval_power: "clength * scale = 2 ^ N"
    and exponent_fit: "m + K \<le> N"
    and active: "i < m"
    and exact: "fri_linear_exact_list_cap d m K L"
  shows
    "card (fri_rs_close_list
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        received
        (4 * fri_linear_good_radius m K i)) \<le> L"
proof -
  have i_le: "i \<le> N"
    using active exponent_fit by linarith
  have distinct_domain: "distinct (fri_canonical_domain_at i)"
    by (rule distinct_fri_canonical_domain_at[OF eval_power i_le])
  have radius:
      "4 * fri_linear_good_radius m K i \<le>
        length (fri_canonical_domain_at i)"
    and degree:
      "fri_degree_after i (fri_padded_degree_bound d) \<le>
        length (fri_canonical_domain_at i)"
    and johnson:
      "length (fri_canonical_domain_at i) *
          fri_degree_after i (fri_padded_degree_bound d) <
        (length (fri_canonical_domain_at i) -
          4 * fri_linear_good_radius m K i)^2"
    and envelope:
      "length (fri_canonical_domain_at i) *
          (length (fri_canonical_domain_at i) -
            fri_degree_after i (fri_padded_degree_bound d)) div
          ((length (fri_canonical_domain_at i) -
              4 * fri_linear_good_radius m K i)^2 -
            length (fri_canonical_domain_at i) *
              fri_degree_after i (fri_padded_degree_bound d)) \<le> L"
    using exact active
    unfolding fri_linear_exact_list_cap_def
      fri_linear_exact_list_cap_at_def Let_def
    by blast+
  have bound:
      "card (fri_rs_close_list
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i)
          received
          (4 * fri_linear_good_radius m K i)) \<le>
        length (fri_canonical_domain_at i) *
          (length (fri_canonical_domain_at i) -
            fri_degree_after i (fri_padded_degree_bound d)) div
          ((length (fri_canonical_domain_at i) -
              4 * fri_linear_good_radius m K i)^2 -
            length (fri_canonical_domain_at i) *
              fri_degree_after i (fri_padded_degree_bound d))"
    by (rule fri_rs_close_list_card_div_bound[
          OF distinct_domain radius degree johnson])
  show ?thesis
    using bound envelope by linarith
qed


lemma fri_canonical_one_round_decode_or_reject_at_list_cap:
  fixes d i N t L :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and active_round: "i < ceil_log (Suc d)"
    and rounds_fit: "Suc (ceil_log (Suc d)) \<le> N"
    and close_cap:
      "card (fri_rs_close_list
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i) (nth current) (4 * t)) \<le> L"
  shows
    "fri_rs_distance_to_code
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i) (nth current) \<le> 2 * t \<or>
      card (fri_fold_good_challenges
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (length (fri_canonical_domain_at i))
        (fri_canonical_domain_at i) current t) \<le>
      1 + L * Suc t"
proof -
  let ?dom = "fri_canonical_domain_at i"
  let ?next_dom = "fri_canonical_domain_at (Suc i)"
  let ?len = "length ?dom"
  let ?k = "fri_degree_after (Suc i) (fri_padded_degree_bound d)"
  let ?Good =
    "fri_fold_good_challenges ?k ?next_dom ?len ?dom current t"
  have two_rounds: "i + 2 \<le> N"
    using active_round rounds_fit by linarith
  have i_lt_N: "i < N"
    using two_rounds by linarith
  have i_le_N: "i \<le> N"
    using i_lt_N by simp
  have len_pos: "0 < ?len"
    by (rule fri_canonical_domain_at_pos[OF eval_power i_le_N])
  have even_len: "2 dvd ?len"
    by (rule fri_canonical_domain_at_even[OF eval_power i_lt_N])
  have next_length: "length ?next_dom = ?len div 2"
    by (rule fri_canonical_domain_successor_length[
          OF eval_power i_lt_N])
  have round: "?len * 2 ^ i = clength * scale"
    by (rule fri_canonical_domain_at_round_product[
          OF eval_power i_le_N])
  have successor_map:
      "?next_dom =
        map (\<lambda>j. (?dom ! j) ^ 2) [0..<?len div 2]"
    by (rule fri_canonical_domain_successor_map_square[
          OF eval_power i_lt_N])
  have successor_point:
      "\<And>j. j < ?len div 2 \<Longrightarrow>
        ?next_dom ! j = (?dom ! j) ^ 2"
    using successor_map by simp
  have sibling_point:
      "\<And>j. j < ?len div 2 \<Longrightarrow>
        ?dom ! fri_sibling_index ?len j = - (?dom ! j)"
  proof -
    fix j
    assume j_bound: "j < ?len div 2"
    have j_len: "j < ?len"
      using j_bound by simp
    have sibling_len: "fri_sibling_index ?len j < ?len"
      using len_pos unfolding fri_sibling_index_def by simp
    have dom_j:
        "?dom ! j = (h ^ j * shift) ^ (2 ^ i)"
      by (rule fri_canonical_domain_at_nth[OF j_len])
    have dom_sibling:
        "?dom ! fri_sibling_index ?len j =
          (h ^ fri_sibling_index ?len j * shift) ^ (2 ^ i)"
      by (rule fri_canonical_domain_at_nth[OF sibling_len])
    show "?dom ! fri_sibling_index ?len j = - (?dom ! j)"
      using fri_sibling_domain_round[
          OF len_pos even_len round, of j]
        dom_j dom_sibling
      unfolding fri_sibling_index_def by simp
  qed
  have point_nonzero:
      "\<And>j. j < ?len div 2 \<Longrightarrow> ?dom ! j \<noteq> 0"
  proof -
    fix j
    assume j_bound: "j < ?len div 2"
    have j_len: "j < ?len"
      using j_bound by simp
    have dom_j: "?dom ! j = (h ^ j * shift) ^ (2 ^ i)"
      by (rule fri_canonical_domain_at_nth[OF j_len])
    show "?dom ! j \<noteq> 0"
      using dom_j h_nonzero shift_nonzero by simp
  qed
  have degree_step:
      "fri_degree_after i (fri_padded_degree_bound d) =
        2 * ?k + 1"
    by (rule fri_degree_after_padded_step[OF active_round])
  have close_cap':
      "card (fri_rs_close_list
          (2 * ?k + 1) ?dom (nth current) (4 * t)) \<le> L"
    using close_cap unfolding degree_step .
  show ?thesis
  proof (cases
      "fri_rs_distance_to_code
        (fri_degree_after i (fri_padded_degree_bound d))
        ?dom (nth current) \<le> 2 * t")
    case True
    then show ?thesis by simp
  next
    case False
    have far_at_current_degree:
        "2 * t < fri_rs_distance_to_code
          (fri_degree_after i (fri_padded_degree_bound d))
          ?dom (nth current)"
      using False by simp
    have current_far:
        "2 * t < fri_rs_distance_to_code
          (2 * ?k + 1) ?dom (nth current)"
      using far_at_current_degree
      unfolding degree_step .
    show ?thesis
    proof (cases "?Good = {}")
      case True
      then show ?thesis by simp
    next
      case False
      then obtain b0 where anchor_good: "b0 \<in> ?Good"
        by blast
      have good_bound:
          "card ?Good \<le> 1 + L * Suc t"
        by (rule fri_one_round_good_challenges_card_le[
              OF anchor_good current_far close_cap' len_pos even_len
                refl next_length successor_point sibling_point
                point_nonzero])
      show ?thesis
        by (rule disjI2[OF good_bound])
    qed
  qed
qed


lemma fri_canonical_one_round_decode_or_reject_at_exact_two:
  fixes d N m K i :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and exponent_fit: "m + K \<le> N"
    and K_pos: "0 < K"
    and active: "i < m"
    and exact: "fri_linear_exact_list_cap d m K 2"
  shows
    "fri_rs_distance_to_code
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i) (nth current) \<le>
          2 * fri_linear_good_radius m K i \<or>
      card (fri_fold_good_challenges
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (length (fri_canonical_domain_at i))
        (fri_canonical_domain_at i) current
        (fri_linear_good_radius m K i)) \<le>
          2 * fri_linear_good_radius m K i + 3"
proof -
  have active_round: "i < ceil_log (Suc d)"
    using active rounds_eq by simp
  have rounds_fit: "Suc (ceil_log (Suc d)) \<le> N"
    using exponent_fit K_pos rounds_eq by linarith
  have close_cap:
      "card (fri_rs_close_list
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i) (nth current)
          (4 * fri_linear_good_radius m K i)) \<le> 2"
    by (rule fri_rs_active_layer_linear_exact_list_cap[
          OF eval_power exponent_fit active exact])
  have split:
      "fri_rs_distance_to_code
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i) (nth current) \<le>
            2 * fri_linear_good_radius m K i \<or>
        card (fri_fold_good_challenges
          (fri_degree_after (Suc i) (fri_padded_degree_bound d))
          (fri_canonical_domain_at (Suc i))
          (length (fri_canonical_domain_at i))
          (fri_canonical_domain_at i) current
          (fri_linear_good_radius m K i)) \<le>
            1 + 2 * Suc (fri_linear_good_radius m K i)"
    by (rule fri_canonical_one_round_decode_or_reject_at_list_cap[
          OF eval_power active_round rounds_fit close_cap])
  show ?thesis
    using split by (auto simp add: algebra_simps)
qed


lemma fri_canonical_multiround_linear_decode_or_reject_eight:
  fixes d N m K :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and exponent_fit: "m + K \<le> N"
    and capacity: "8 * Suc m \<le> 2 ^ K"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
    and layer_length:
      "\<And>i. i \<le> m \<Longrightarrow>
        length (layers ! i) = length (fri_canonical_domain_at i)"
    and terminal_close:
      "fri_canonical_layer_close d layers
        (fri_linear_radius m K) m"
  shows
    "fri_canonical_layer_close d layers
        (fri_linear_radius m K) 0 \<or>
      (\<exists>i<m.
        \<not> fri_canonical_layer_close d layers
            (fri_linear_radius m K) i \<and>
        fri_canonical_layer_close d layers
            (fri_linear_radius m K) (Suc i) \<and>
        ((bs ! i \<in>
            fri_canonical_layer_good_challenges
              d layers (fri_linear_good_radius m K) i \<and>
          card (fri_canonical_layer_good_challenges
              d layers (fri_linear_good_radius m K) i) \<le>
            2 * fri_linear_good_radius m K i + 3) \<or>
         card (fri_canonical_transition_agreement_indices
              bs layers i) \<le>
            length (fri_canonical_domain_at (Suc i)) -
              fri_linear_margin K i))"
proof -
  have K_pos: "0 < K"
  proof (cases K)
    case 0
    then show ?thesis
      using capacity by simp
  next
    case (Suc k)
    then show ?thesis by simp
  qed
  have rounds_fit: "Suc m \<le> N"
    using exponent_fit K_pos by linarith
  show ?thesis
  proof (rule fri_canonical_multiround_decode_or_reject[
      where N=N and m=m
        and radius="fri_linear_radius m K"
        and good_radius="fri_linear_good_radius m K"
        and margin="fri_linear_margin K"])
    show "clength * scale = 2 ^ N" by (rule eval_power)
    show "m = ceil_log (Suc d)" by (rule rounds_eq)
    show "Suc m \<le> N" by (rule rounds_fit)
    show "4 * fri_padded_degree_bound d \<le> clength * scale"
      by (rule initial_rate)
    fix i
    assume "i \<le> m"
    show "length (layers ! i) =
        length (fri_canonical_domain_at i)"
      by (rule layer_length[OF \<open>i \<le> m\<close>])
  next
    show "fri_canonical_layer_close d layers
        (fri_linear_radius m K) m"
      by (rule terminal_close)
  next
    fix i
    assume i_bound: "i < m"
    show
      "2 * fri_linear_good_radius m K i \<le>
        fri_linear_radius m K i"
      using fri_linear_current_radius_exact[
        OF eval_power i_bound exponent_fit] by simp
  next
    fix i
    assume i_bound: "i < m"
    show
      "fri_linear_radius m K (Suc i) +
          fri_linear_margin K i \<le>
        fri_linear_good_radius m K i"
      using fri_linear_transition_margin_exact[OF i_bound] by simp
  next
    fix i
    assume i_bound: "i < m"
    show
      "4 * fri_linear_good_radius m K i \<le>
        length (fri_canonical_domain_at i) div 4"
      by (rule fri_linear_good_radius_list_compatible_eight[
            OF eval_power i_bound exponent_fit capacity])
  qed
qed


lemma fri_canonical_multiround_decode_or_reject_at_list_cap_two:
  fixes d N m :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and rounds_fit: "Suc m \<le> N"
    and layer_length:
      "\<And>i. i \<le> m \<Longrightarrow>
        length (layers ! i) = length (fri_canonical_domain_at i)"
    and terminal_close:
      "fri_canonical_layer_close d layers radius m"
    and current_radius:
      "\<And>i. i < m \<Longrightarrow> 2 * good_radius i \<le> radius i"
    and transition_margin:
      "\<And>i. i < m \<Longrightarrow> radius (Suc i) + margin i \<le> good_radius i"
    and close_cap:
      "\<And>i. i < m \<Longrightarrow>
        card (fri_rs_close_list
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i) (nth (layers ! i))
          (4 * good_radius i)) \<le> 2"
  shows
    "fri_canonical_layer_close d layers radius 0 \<or>
      (\<exists>i<m.
        \<not> fri_canonical_layer_close d layers radius i \<and>
        fri_canonical_layer_close d layers radius (Suc i) \<and>
        ((bs ! i \<in>
            fri_canonical_layer_good_challenges
              d layers good_radius i \<and>
          card (fri_canonical_layer_good_challenges
              d layers good_radius i) \<le>
            2 * good_radius i + 3) \<or>
         card (fri_canonical_transition_agreement_indices
              bs layers i) \<le>
            length (fri_canonical_domain_at (Suc i)) - margin i))"
proof (cases "fri_canonical_layer_close d layers radius 0")
  case True
  then show ?thesis by simp
next
  case False
  have boundary:
      "\<exists>i<m.
        \<not> fri_canonical_layer_close d layers radius i \<and>
        fri_canonical_layer_close d layers radius (Suc i)"
    by (rule predicate_false_true_boundary[
          OF False terminal_close])
  then obtain i where i_bound: "i < m"
    and current_far:
      "\<not> fri_canonical_layer_close d layers radius i"
    and next_close:
      "fri_canonical_layer_close d layers radius (Suc i)"
    by blast
  let ?Good =
    "fri_canonical_layer_good_challenges d layers good_radius i"
  let ?Agree =
    "fri_canonical_transition_agreement_indices bs layers i"
  have active_round: "i < ceil_log (Suc d)"
    using i_bound rounds_eq by simp
  have current_far_good_radius:
      "\<not> fri_rs_distance_to_code
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i) (nth (layers ! i)) \<le>
          2 * good_radius i"
  proof
    assume close:
        "fri_rs_distance_to_code
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i) (nth (layers ! i)) \<le>
            2 * good_radius i"
    have
        "fri_rs_distance_to_code
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i) (nth (layers ! i)) \<le> radius i"
      using close current_radius[OF i_bound] by linarith
    then show False
      using current_far
      unfolding fri_canonical_layer_close_def by simp
  qed
  have good_card: "card ?Good \<le> 2 * good_radius i + 3"
  proof -
    have split:
        "fri_rs_distance_to_code
            (fri_degree_after i (fri_padded_degree_bound d))
            (fri_canonical_domain_at i) (nth (layers ! i)) \<le>
              2 * good_radius i \<or>
          card ?Good \<le> 1 + 2 * Suc (good_radius i)"
      unfolding fri_canonical_layer_good_challenges_def
      by (rule fri_canonical_one_round_decode_or_reject_at_list_cap[
            where L=2, OF eval_power active_round _
              close_cap[OF i_bound]])
        (use rounds_fit rounds_eq in simp)
    have split':
        "fri_rs_distance_to_code
            (fri_degree_after i (fri_padded_degree_bound d))
            (fri_canonical_domain_at i) (nth (layers ! i)) \<le>
              2 * good_radius i \<or>
          card ?Good \<le> 2 * good_radius i + 3"
      using split by (auto simp add: algebra_simps)
    show ?thesis
      using split' current_far_good_radius by blast
  qed
  have next_close_distance:
      "fri_rs_distance_to_code
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i)) (nth (layers ! Suc i)) \<le>
          radius (Suc i)"
    using next_close
    unfolding fri_canonical_layer_close_def .
  have next_table_length:
      "length (layers ! Suc i) =
        length (fri_canonical_domain_at (Suc i))"
    by (rule layer_length) (use i_bound in simp)
  have alternative:
      "(bs ! i \<in> ?Good \<and> card ?Good \<le> 2 * good_radius i + 3) \<or>
       card ?Agree \<le>
         length (fri_canonical_domain_at (Suc i)) - margin i"
  proof (cases "bs ! i \<in> ?Good")
    case True
    then show ?thesis
      using good_card by simp
  next
    case False
    have agreement:
        "card (fri_fold_next_agreement_indices
          (bs ! i) (length (fri_canonical_domain_at i))
          (fri_canonical_domain_at i) (layers ! i) (layers ! Suc i)) \<le>
          length (fri_canonical_domain_at (Suc i)) - margin i"
      by (rule fri_fold_next_agreement_card_bound[
            OF next_close_distance _ transition_margin[OF i_bound]
              next_table_length])
        (use False in
          \<open>simp add: fri_canonical_layer_good_challenges_def\<close>)
    then show ?thesis
      unfolding fri_canonical_transition_agreement_indices_def
      by simp
  qed
  show ?thesis
    by (rule disjI2)
      (rule exI[where x=i],
       use i_bound current_far next_close alternative in blast)
qed


lemma fri_canonical_multiround_linear_decode_or_reject_exact_two:
  fixes d N m K :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and exponent_fit: "m + K \<le> N"
    and K_pos: "0 < K"
    and exact: "fri_linear_exact_list_cap d m K 2"
    and layer_length:
      "\<And>i. i \<le> m \<Longrightarrow>
        length (layers ! i) = length (fri_canonical_domain_at i)"
    and terminal_close:
      "fri_canonical_layer_close d layers
        (fri_linear_radius m K) m"
  shows
    "fri_canonical_layer_close d layers
        (fri_linear_radius m K) 0 \<or>
      (\<exists>i<m.
        \<not> fri_canonical_layer_close d layers
            (fri_linear_radius m K) i \<and>
        fri_canonical_layer_close d layers
            (fri_linear_radius m K) (Suc i) \<and>
        ((bs ! i \<in>
            fri_canonical_layer_good_challenges
              d layers (fri_linear_good_radius m K) i \<and>
          card (fri_canonical_layer_good_challenges
              d layers (fri_linear_good_radius m K) i) \<le>
            2 * fri_linear_good_radius m K i + 3) \<or>
         card (fri_canonical_transition_agreement_indices
              bs layers i) \<le>
            length (fri_canonical_domain_at (Suc i)) -
              fri_linear_margin K i))"
proof -
  have rounds_fit: "Suc m \<le> N"
    using exponent_fit K_pos by linarith
  show ?thesis
  proof (rule fri_canonical_multiround_decode_or_reject_at_list_cap_two[
      where N=N and m=m
        and radius="fri_linear_radius m K"
        and good_radius="fri_linear_good_radius m K"
        and margin="fri_linear_margin K"])
    show "clength * scale = 2 ^ N" by (rule eval_power)
    show "m = ceil_log (Suc d)" by (rule rounds_eq)
    show "Suc m \<le> N" by (rule rounds_fit)
    fix i
    assume "i \<le> m"
    show "length (layers ! i) =
        length (fri_canonical_domain_at i)"
      by (rule layer_length[OF \<open>i \<le> m\<close>])
  next
    show "fri_canonical_layer_close d layers
        (fri_linear_radius m K) m"
      by (rule terminal_close)
  next
    fix i
    assume i_bound: "i < m"
    show
      "2 * fri_linear_good_radius m K i \<le>
        fri_linear_radius m K i"
      using fri_linear_current_radius_exact[
        OF eval_power i_bound exponent_fit] by simp
  next
    fix i
    assume i_bound: "i < m"
    show
      "fri_linear_radius m K (Suc i) +
          fri_linear_margin K i \<le>
        fri_linear_good_radius m K i"
      using fri_linear_transition_margin_exact[OF i_bound] by simp
  next
    fix i
    assume i_bound: "i < m"
    show
      "card (fri_rs_close_list
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i) (nth (layers ! i))
          (4 * fri_linear_good_radius m K i)) \<le> 2"
      by (rule fri_rs_active_layer_linear_exact_list_cap[
            OF eval_power exponent_fit i_bound exact])
  qed
qed


end
end
