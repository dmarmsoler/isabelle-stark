theory Soundness_FRI_Robust_Multiround
  imports Soundness_FRI_Robust_One_Round
begin

context soundness
begin

lemma fri_canonical_one_round_decode_or_reject_at:
  fixes d i N t :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and active_round: "i < ceil_log (Suc d)"
    and rounds_fit: "Suc (ceil_log (Suc d)) \<le> N"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
    and radius:
      "4 * t \<le> length (fri_canonical_domain_at i) div 4"
  shows
    "fri_rs_distance_to_code
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i) (nth current) \<le> 2 * t \<or>
      card (fri_fold_good_challenges
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (length (fri_canonical_domain_at i))
        (fri_canonical_domain_at i) current t) \<le> 2 * t + 3"
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
  have close_cap:
      "card (fri_rs_close_list
          (2 * ?k + 1) ?dom (nth current) (4 * t)) \<le> 2"
  proof -
    have
        "card (fri_rs_close_list
          (fri_degree_after i (fri_padded_degree_bound d))
          ?dom (nth current) (4 * t)) \<le> 2"
      by (rule fri_rs_active_layer_small_radius_list_cap[
            OF eval_power active_round rounds_fit initial_rate radius])
    then show ?thesis
      unfolding degree_step .
  qed
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
      have good_bound: "card ?Good \<le> 1 + 2 * Suc t"
        by (rule fri_one_round_good_challenges_card_le[
              OF anchor_good current_far close_cap len_pos even_len
                refl next_length successor_point sibling_point
                point_nonzero])
      show ?thesis
        by (rule disjI2) (use good_bound in simp)
    qed
  qed
qed

lemma agreement_card_bound_from_triangle:
  assumes finite_I: "finite I"
    and received_far:
      "t < card (code_disagreement_indices I received word)"
    and next_close:
      "card (code_disagreement_indices I next word) \<le> r"
    and margin: "r + s \<le> t"
  shows "card (code_agreement_indices I received next) \<le> card I - s"
proof -
  let ?A = "code_agreement_indices I received next"
  let ?D = "code_disagreement_indices I received next"
  let ?F = "code_disagreement_indices I received word"
  let ?E = "code_disagreement_indices I next word"
  have finite_D: "finite ?D"
    by (rule finite_code_disagreement_indices[OF finite_I])
  have finite_E: "finite ?E"
    by (rule finite_code_disagreement_indices[OF finite_I])
  have triangle: "?F \<subseteq> ?D \<union> ?E"
    unfolding code_disagreement_indices_def by auto
  have finite_union: "finite (?D \<union> ?E)"
    using finite_D finite_E by simp
  have F_card: "card ?F \<le> card (?D \<union> ?E)"
    by (rule card_mono[OF finite_union triangle])
  have union_card: "card (?D \<union> ?E) \<le> card ?D + card ?E"
    by (rule card_Un_le)
  have far_to_D: "t < card ?D + r"
    using received_far F_card union_card next_close by linarith
  have agreement_partition: "card ?A + card ?D = card I"
    by (rule code_agreement_disagreement_card[OF finite_I])
  show ?thesis
  proof (rule ccontr)
    assume not_bound: "\<not> card ?A \<le> card I - s"
    have I_card: "card ?A \<le> card I"
      using agreement_partition by linarith
    have D_le_I: "card ?D \<le> card I"
      using agreement_partition by linarith
    have t_lt_I_r: "t < card I + r"
      using far_to_D D_le_I by linarith
    have s_lt_I: "s < card I"
      using margin t_lt_I_r by linarith
    have s_le_I: "s \<le> card I"
      using s_lt_I by simp
    have D_small: "card ?D < s"
      using agreement_partition not_bound s_le_I by linarith
    have "card ?D + r < s + r"
      using D_small by simp
    also have "... \<le> t"
      using margin by (simp add: add.commute)
    finally have "card ?D + r < t" .
    then show False
      using far_to_D by simp
  qed
qed

definition fri_fold_next_agreement_indices ::
  "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
where
  "fri_fold_next_agreement_indices b len fri_dom current next =
    code_agreement_indices {..<length next}
      (fri_folded_received b len fri_dom current) (nth next)"

lemma finite_fri_fold_next_agreement_indices:
  "finite (fri_fold_next_agreement_indices
    b len fri_dom current next)"
  unfolding fri_fold_next_agreement_indices_def
  by (rule finite_code_agreement_indices) simp

lemma fri_fold_next_agreement_card_bound:
  assumes next_close:
      "fri_rs_distance_to_code k next_dom (nth next) \<le> r"
    and challenge_not_good:
      "b \<notin> fri_fold_good_challenges
        k next_dom len fri_dom current t"
    and margin: "r + s \<le> t"
    and next_length: "length next = length next_dom"
  shows
    "card (fri_fold_next_agreement_indices
      b len fri_dom current next) \<le> length next_dom - s"
proof -
  let ?folded = "fri_folded_received b len fri_dom current"
  let ?word = "fri_rs_canonical_decoder k next_dom (nth next)"
  have word_code: "?word \<in> fri_rs_code_functions k next_dom"
    by (rule fri_rs_canonical_decoder_code)
  have folded_distance:
      "fri_rs_distance_to_code k next_dom ?folded \<le>
        card (code_disagreement_indices
          {..<length next_dom} ?folded ?word)"
    by (rule fri_rs_distance_to_code_le[OF word_code])
  have not_good_errors:
      "t < card (fri_fold_decoder_errors
        k next_dom len fri_dom current b)"
    using challenge_not_good
    unfolding fri_fold_good_challenges_def by simp
  have folded_far:
      "t < card (code_disagreement_indices
        {..<length next_dom} ?folded ?word)"
  proof -
    have decoder_distance:
        "card (fri_fold_decoder_errors
            k next_dom len fri_dom current b) =
          fri_rs_distance_to_code k next_dom ?folded"
      unfolding fri_fold_decoder_errors_def fri_fold_decoder_def
      by (rule fri_rs_canonical_decoder_distance)
    show ?thesis
      using not_good_errors decoder_distance folded_distance by linarith
  qed
  have next_decoder_exact:
      "card (code_disagreement_indices
          {..<length next_dom} (nth next) ?word) =
        fri_rs_distance_to_code k next_dom (nth next)"
    by (rule fri_rs_canonical_decoder_distance)
  have next_decoder_close:
      "card (code_disagreement_indices
          {..<length next_dom} (nth next) ?word) \<le> r"
    using next_close next_decoder_exact by simp
  have generic:
      "card (code_agreement_indices
          {..<length next_dom} ?folded (nth next)) \<le>
        card {..<length next_dom} - s"
    by (rule agreement_card_bound_from_triangle[
          OF _ folded_far next_decoder_close margin]) simp
  show ?thesis
    using generic next_length
    unfolding fri_fold_next_agreement_indices_def by simp
qed

definition fri_canonical_layer_close ::
  "nat \<Rightarrow> 'f list list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
where
  "fri_canonical_layer_close d layers radius i \<longleftrightarrow>
    fri_rs_distance_to_code
      (fri_degree_after i (fri_padded_degree_bound d))
      (fri_canonical_domain_at i) (nth (layers ! i)) \<le> radius i"

definition fri_canonical_layer_decoder ::
  "nat \<Rightarrow> 'f list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f"
where
  "fri_canonical_layer_decoder d layers i =
    fri_rs_canonical_decoder
      (fri_degree_after i (fri_padded_degree_bound d))
      (fri_canonical_domain_at i) (nth (layers ! i))"

definition fri_canonical_table_decoder ::
  "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f"
where
  "fri_canonical_table_decoder d i table =
    fri_rs_canonical_decoder
      (fri_degree_after i (fri_padded_degree_bound d))
      (fri_canonical_domain_at i) (nth table)"

lemma fri_canonical_layer_decoder_eq_table_decoder:
  "fri_canonical_layer_decoder d layers i =
    fri_canonical_table_decoder d i (layers ! i)"
  unfolding fri_canonical_layer_decoder_def
    fri_canonical_table_decoder_def by simp

lemma fri_canonical_table_decoder_cong:
  assumes "table = table'"
  shows
    "fri_canonical_table_decoder d i table =
      fri_canonical_table_decoder d i table'"
  using assms by simp

lemma fri_canonical_layer_decoder_current_cong:
  assumes "layers ! i = layers' ! i"
  shows
    "fri_canonical_layer_decoder d layers i =
      fri_canonical_layer_decoder d layers' i"
  using assms unfolding fri_canonical_layer_decoder_def by simp

definition fri_canonical_layer_good_challenges ::
  "nat \<Rightarrow> 'f list list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'f set"
where
  "fri_canonical_layer_good_challenges d layers good_radius i =
    fri_fold_good_challenges
      (fri_degree_after (Suc i) (fri_padded_degree_bound d))
      (fri_canonical_domain_at (Suc i))
      (length (fri_canonical_domain_at i))
      (fri_canonical_domain_at i) (layers ! i) (good_radius i)"

definition fri_canonical_transition_agreement_indices ::
  "'f list \<Rightarrow> 'f list list \<Rightarrow> nat \<Rightarrow> nat set"
where
  "fri_canonical_transition_agreement_indices bs layers i =
    fri_fold_next_agreement_indices
      (bs ! i) (length (fri_canonical_domain_at i))
      (fri_canonical_domain_at i) (layers ! i) (layers ! Suc i)"

lemma predicate_false_true_boundary:
  assumes not_initial: "\<not> P 0"
    and terminal: "P m"
  shows "\<exists>i<m. \<not> P i \<and> P (Suc i)"
  using terminal not_initial
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases "P m")
    case True
    then obtain i where "i < m" "\<not> P i" "P (Suc i)"
      using Suc.IH Suc.prems(2) by blast
    show ?thesis
      by (rule exI[where x=i])
        (use \<open>i < m\<close> \<open>\<not> P i\<close> \<open>P (Suc i)\<close> in simp)
  next
    case False
    show ?thesis
      by (rule exI[where x=m])
        (use False Suc.prems(1) in simp)
  qed
qed

lemma fri_canonical_multiround_decode_or_reject:
  fixes d N m :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and rounds_fit: "Suc m \<le> N"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
    and layer_length:
      "\<And>i. i \<le> m \<Longrightarrow>
        length (layers ! i) = length (fri_canonical_domain_at i)"
    and terminal_close:
      "fri_canonical_layer_close d layers radius m"
    and current_radius:
      "\<And>i. i < m \<Longrightarrow> 2 * good_radius i \<le> radius i"
    and transition_margin:
      "\<And>i. i < m \<Longrightarrow> radius (Suc i) + margin i \<le> good_radius i"
    and list_radius:
      "\<And>i. i < m \<Longrightarrow>
        4 * good_radius i \<le>
          length (fri_canonical_domain_at i) div 4"
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
          card ?Good \<le> 2 * good_radius i + 3"
      unfolding fri_canonical_layer_good_challenges_def
      by (rule fri_canonical_one_round_decode_or_reject_at[
            OF eval_power active_round _ initial_rate list_radius[OF i_bound]])
        (use rounds_fit rounds_eq in simp)
    show ?thesis
      using split current_far_good_radius by blast
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

definition fri_linear_unit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fri_linear_unit K i =
    length (fri_canonical_domain_at i) div 2 ^ K"

definition fri_linear_radius :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fri_linear_radius m K i =
    (m - i + 1) * fri_linear_unit K i"

definition fri_linear_good_radius :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fri_linear_good_radius m K i =
    (m - i + 1) * fri_linear_unit K (Suc i)"

definition fri_linear_margin :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fri_linear_margin K i = fri_linear_unit K (Suc i)"

lemma fri_linear_unit_power:
  assumes eval_power: "clength * scale = 2 ^ N"
    and exponent_fit: "i + K \<le> N"
  shows "fri_linear_unit K i = 2 ^ (N - i - K)"
proof -
  have i_le: "i \<le> N"
    using exponent_fit by linarith
  have K_le: "K \<le> N - i"
    using exponent_fit by linarith
  show ?thesis
    unfolding fri_linear_unit_def
      fri_canonical_domain_at_length_power[OF eval_power i_le]
    by (simp add: exp_div_exp_eq K_le)
qed

lemma fri_linear_unit_pos:
  assumes eval_power: "clength * scale = 2 ^ N"
    and exponent_fit: "i + K \<le> N"
  shows "0 < fri_linear_unit K i"
  unfolding fri_linear_unit_power[OF eval_power exponent_fit]
  by simp

lemma fri_linear_unit_step:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < m"
    and exponent_fit: "m + K \<le> N"
  shows "fri_linear_unit K i = 2 * fri_linear_unit K (Suc i)"
proof -
  have current_fit: "i + K \<le> N"
    using round_bound exponent_fit by linarith
  have next_fit: "Suc i + K \<le> N"
    using round_bound exponent_fit by linarith
  have exponent_step:
      "N - i - K = Suc (N - Suc i - K)"
    using round_bound exponent_fit by linarith
  show ?thesis
    unfolding fri_linear_unit_power[OF eval_power current_fit]
      fri_linear_unit_power[OF eval_power next_fit]
      exponent_step
    by simp
qed

lemma fri_linear_current_radius_exact:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < m"
    and exponent_fit: "m + K \<le> N"
  shows
    "2 * fri_linear_good_radius m K i =
      fri_linear_radius m K i"
  unfolding fri_linear_good_radius_def fri_linear_radius_def
  using fri_linear_unit_step[OF eval_power round_bound exponent_fit]
  by (simp add: algebra_simps)

lemma fri_linear_transition_margin_exact:
  assumes round_bound: "i < m"
  shows
    "fri_linear_radius m K (Suc i) + fri_linear_margin K i =
      fri_linear_good_radius m K i"
proof -
  let ?u = "fri_linear_unit K (Suc i)"
  have coefficient:
      "m - Suc i + 1 + 1 = m - i + 1"
    using round_bound by linarith
  have
      "(m - Suc i + 1) * ?u + ?u =
        (m - Suc i + 1 + 1) * ?u"
    by (simp add: algebra_simps)
  also have "... = (m - i + 1) * ?u"
    unfolding coefficient by simp
  finally show ?thesis
    unfolding fri_linear_radius_def fri_linear_margin_def
      fri_linear_good_radius_def .
qed

lemma fri_linear_margin_pos:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < m"
    and exponent_fit: "m + K \<le> N"
  shows "0 < fri_linear_margin K i"
  unfolding fri_linear_margin_def
  by (rule fri_linear_unit_pos[OF eval_power])
    (use round_bound exponent_fit in linarith)

lemma fri_linear_unit_reconstruct:
  assumes eval_power: "clength * scale = 2 ^ N"
    and exponent_fit: "i + K \<le> N"
  shows
    "2 ^ K * fri_linear_unit K i =
      length (fri_canonical_domain_at i)"
proof -
  have i_le: "i \<le> N"
    using exponent_fit by linarith
  have exponent_split:
      "N - i = K + (N - i - K)"
    using exponent_fit by linarith
  have unit:
      "fri_linear_unit K i = 2 ^ (N - i - K)"
    by (rule fri_linear_unit_power[OF eval_power exponent_fit])
  have domain:
      "length (fri_canonical_domain_at i) = 2 ^ (N - i)"
    by (rule fri_canonical_domain_at_length_power[OF eval_power i_le])
  have "2 ^ K * fri_linear_unit K i =
      2 ^ K * 2 ^ (N - i - K)"
    unfolding unit by simp
  also have "... = 2 ^ (K + (N - i - K))"
    by (simp add: power_add)
  also have "... = 2 ^ (N - i)"
    by (rule arg_cong[OF sym[OF exponent_split]])
  also have "... = length (fri_canonical_domain_at i)"
    using domain by simp
  finally show ?thesis .
qed

lemma four_sixteenth_le_quarter:
  fixes n :: nat
  shows "4 * (n div 16) \<le> n div 4"
proof (rule less_eq_div_iff_mult_less_eq[
    OF zero_less_numeral, THEN iffD2])
  have "4 * (n div 16) * 4 = (n div 16) * 16"
    by simp
  also have "... \<le> n"
    by simp
  finally show "4 * (n div 16) * 4 \<le> n" .
qed

lemma fri_linear_good_radius_le_sixteenth:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < m"
    and exponent_fit: "m + K \<le> N"
    and capacity: "16 * Suc m \<le> 2 ^ K"
  shows
    "fri_linear_good_radius m K i \<le>
      length (fri_canonical_domain_at i) div 16"
proof (rule less_eq_div_iff_mult_less_eq[
    OF zero_less_numeral, THEN iffD2])
  let ?u = "fri_linear_unit K (Suc i)"
  let ?c = "m - i + 1"
  have c_le: "?c \<le> Suc m"
    by simp
  have scaled_c: "16 * ?c \<le> 2 ^ K"
  proof -
    have "16 * ?c \<le> 16 * Suc m"
      using c_le by simp
    also have "... \<le> 2 ^ K"
      by (rule capacity)
    finally show ?thesis .
  qed
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
        (16 * ?c) * ?u"
    unfolding fri_linear_good_radius_def
    by (simp add: algebra_simps)
  also have "... \<le> (2 ^ K) * ?u"
    by (rule mult_right_mono[OF scaled_c]) simp
  also have "... \<le> (2 ^ K) * (2 * ?u)"
    by simp
  also have "... = length (fri_canonical_domain_at i)"
    using reconstruct unit_step by simp
  finally show
      "fri_linear_good_radius m K i * 16 \<le>
        length (fri_canonical_domain_at i)" .
qed

lemma fri_linear_good_radius_list_compatible:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < m"
    and exponent_fit: "m + K \<le> N"
    and capacity: "16 * Suc m \<le> 2 ^ K"
  shows
    "4 * fri_linear_good_radius m K i \<le>
      length (fri_canonical_domain_at i) div 4"
proof -
  have small:
      "fri_linear_good_radius m K i \<le>
        length (fri_canonical_domain_at i) div 16"
    by (rule fri_linear_good_radius_le_sixteenth[
          OF eval_power round_bound exponent_fit capacity])
  have multiplied:
      "4 * fri_linear_good_radius m K i \<le>
        4 * (length (fri_canonical_domain_at i) div 16)"
    using small by simp
  show ?thesis
    using multiplied four_sixteenth_le_quarter[
      of "length (fri_canonical_domain_at i)"] by linarith
qed

lemma fri_canonical_multiround_linear_decode_or_reject:
  fixes d N m K :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and exponent_fit: "m + K \<le> N"
    and capacity: "16 * Suc m \<le> 2 ^ K"
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
      by (rule fri_linear_good_radius_list_compatible[
            OF eval_power i_bound exponent_fit capacity])
  qed
qed

end


end
