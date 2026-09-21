theory Soundness_FRI_Conditioned_Multiround
  imports
    Soundness_FRI_Conditioned_Interface
    Soundness_FRI_Full_Cover_Domains
begin

context soundness
begin

definition fri_conditioned_layer_table :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list"
where
  "fri_conditioned_layer_table i layer =
    take (length (fri_canonical_domain_at i)) layer"

lemma length_fri_conditioned_layer_table:
  assumes "length (fri_canonical_domain_at i) \<le> length layer"
  shows "length (fri_conditioned_layer_table i layer) =
    length (fri_canonical_domain_at i)"
  using assms unfolding fri_conditioned_layer_table_def by simp

lemma fri_conditioned_layer_table_nth:
  assumes idx_bound: "idx < length (fri_canonical_domain_at i)"
  shows "fri_conditioned_layer_table i layer ! idx = layer ! idx"
  using idx_bound unfolding fri_conditioned_layer_table_def by simp

lemma fri_table_fold_value_conditioned_layer:
  assumes len_pos: "0 < len"
    and len_eq: "len = length (fri_canonical_domain_at i)"
    and idx_bound: "idx < len div 2"
  shows
    "fri_table_fold_value b (fri_conditioned_layer_table i layer)
        (fri_canonical_domain_at i) len pw idx =
      fri_table_fold_value b layer (fri_canonical_domain_at i) len pw idx"
proof -
  have idx_len: "idx < length (fri_canonical_domain_at i)"
    using idx_bound len_eq by simp
  have sibling_len:
      "fri_sibling_index len idx < length (fri_canonical_domain_at i)"
    using len_pos len_eq unfolding fri_sibling_index_def by simp
  show ?thesis
    unfolding fri_table_fold_value_def
    using fri_conditioned_layer_table_nth[OF idx_len, of layer]
      fri_conditioned_layer_table_nth[OF sibling_len, of layer]
    by simp
qed

lemma fri_degree_after_closed_form:
  "fri_degree_after i d = d div 2 ^ i"
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  have "fri_degree_after (Suc i) d = (d div 2 ^ i) div 2"
    using Suc.IH by simp
  also have "... = d div (2 ^ i * 2)"
    by (rule div_mult2_eq[symmetric])
  also have "... = d div 2 ^ Suc i"
    by (simp add: mult.commute)
  finally show ?case .
qed

lemma power_minus_one_div_power:
  assumes "i \<le> n"
  shows "((2::nat) ^ n - 1) div 2 ^ i = 2 ^ (n - i) - 1"
proof -
  obtain k where n_eq: "n = i + k"
    using assms by (metis le_iff_add)
  have split:
      "(2::nat) ^ i * 2 ^ k - 1 =
        2 ^ i * (2 ^ k - 1) + (2 ^ i - 1)"
    by (simp add: algebra_simps)
  have quotient:
      "((2::nat) ^ i * (2 ^ k - 1) + (2 ^ i - 1)) div 2 ^ i =
        2 ^ k - 1"
  proof -
    have
      "((2::nat) ^ i * (2 ^ k - 1) + (2 ^ i - 1)) div 2 ^ i =
        ((2 ^ i - 1) + (2 ^ k - 1) * 2 ^ i) div 2 ^ i"
      by (simp add: add.commute mult.commute)
    also have "... = (2 ^ k - 1) + (2 ^ i - 1) div 2 ^ i"
      by (rule div_mult_self1) simp
    also have "... = 2 ^ k - 1"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
    unfolding n_eq power_add
    using split quotient by simp
qed

lemma fri_degree_after_padded:
  assumes i_bound: "i \<le> ceil_log (Suc d)"
  shows
    "fri_degree_after i (fri_padded_degree_bound d) =
      2 ^ (ceil_log (Suc d) - i) - 1"
  unfolding fri_degree_after_closed_form fri_padded_degree_bound_def
  by (rule power_minus_one_div_power[OF i_bound])

lemma fri_degree_after_padded_step:
  assumes i_bound: "i < ceil_log (Suc d)"
  shows
    "fri_degree_after i (fri_padded_degree_bound d) =
      2 * fri_degree_after (Suc i) (fri_padded_degree_bound d) + 1"
proof -
  let ?n = "ceil_log (Suc d)"
  have i_le: "i \<le> ?n" using i_bound by simp
  have suc_le: "Suc i \<le> ?n" using i_bound by simp
  have pos: "0 < ?n - i" using i_bound by simp
  have power:
      "(2::nat) ^ (?n - i) = 2 * 2 ^ (?n - Suc i)"
    using pos by (cases "?n - i") auto
  have positive: "0 < (2::nat) ^ (?n - Suc i)"
    by simp
  have minus_step:
      "2 * (2::nat) ^ (?n - Suc i) - 1 =
        2 * (2 ^ (?n - Suc i) - 1) + 1"
    using positive by linarith
  have "fri_degree_after i (fri_padded_degree_bound d) =
      2 ^ (?n - i) - 1"
    by (rule fri_degree_after_padded[OF i_le])
  also have "... = 2 * 2 ^ (?n - Suc i) - 1"
    using power by simp
  also have "... = 2 * (2 ^ (?n - Suc i) - 1) + 1"
    by (rule minus_step)
  also have
      "... = 2 * fri_degree_after (Suc i) (fri_padded_degree_bound d) + 1"
    using fri_degree_after_padded[OF suc_le] by simp
  finally show ?thesis .
qed

lemma fri_degree_after_padded_final:
  "fri_degree_after (ceil_log (Suc d)) (fri_padded_degree_bound d) = 0"
  by (simp add: fri_degree_after_padded)

definition fri_conditioned_bad_challenges
  :: "nat \<Rightarrow> (nat \<Rightarrow> 'f list \<Rightarrow> 'f list) \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
where
  "fri_conditioned_bad_challenges d committed i prefix =
    (let p = fri_table_interpolant (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i (committed i prefix));
         k = fri_degree_after (Suc i) (fri_padded_degree_bound d)
     in if degree p > 2 * k + 1 then fri_low_fold_challenges p k else {})"

definition fri_conditioned_agreement_indices
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat set"
where
  "fri_conditioned_agreement_indices i current next b =
    fri_polynomial_agreement_indices
      (fri_symbolic_fold_polynomial
        (fri_table_interpolant (fri_canonical_domain_at i)
          (fri_conditioned_layer_table i current)) b)
      (fri_table_interpolant (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i) next))
      (fri_canonical_domain_at (Suc i))"

lemma card_fri_conditioned_bad_challenges_le_one:
  "card (fri_conditioned_bad_challenges d committed i prefix) \<le> 1"
proof -
  let ?p = "fri_table_interpolant (fri_canonical_domain_at i)
    (fri_conditioned_layer_table i (committed i prefix))"
  let ?k = "fri_degree_after (Suc i) (fri_padded_degree_bound d)"
  show ?thesis
  proof (cases "degree ?p > 2 * ?k + 1")
    case True
    have bound: "card (fri_low_fold_challenges ?p ?k) \<le> 1"
      by (rule card_fri_low_fold_challenges_le_one[OF True])
    show ?thesis
      unfolding fri_conditioned_bad_challenges_def Let_def
      by (simp only: if_True True bound)
  next
    case False
    show ?thesis
      unfolding fri_conditioned_bad_challenges_def Let_def
      using False by simp
  qed
qed

lemma fri_canonical_domain_at_length_power:
  assumes eval_power: "clength * scale = 2 ^ N"
    and i_bound: "i \<le> N"
  shows "length (fri_canonical_domain_at i) = 2 ^ (N - i)"
  unfolding fri_canonical_domain_at_length eval_power
  by (simp add: exp_div_exp_eq i_bound)

lemma fri_canonical_domain_at_pos:
  assumes eval_power: "clength * scale = 2 ^ N"
    and i_bound: "i \<le> N"
  shows "0 < length (fri_canonical_domain_at i)"
  by (simp add: fri_canonical_domain_at_length_power[OF eval_power i_bound])

lemma fri_canonical_domain_at_even:
  assumes eval_power: "clength * scale = 2 ^ N"
    and i_bound: "i < N"
  shows "2 dvd length (fri_canonical_domain_at i)"
proof -
  have diff: "N - i = Suc (N - Suc i)"
    using i_bound by linarith
  have power:
      "length (fri_canonical_domain_at i) = 2 * 2 ^ (N - Suc i)"
  proof -
    have "length (fri_canonical_domain_at i) = 2 ^ (N - i)"
      by (rule fri_canonical_domain_at_length_power[OF eval_power])
        (use i_bound in simp)
    also have "... = 2 * 2 ^ (N - Suc i)"
      unfolding diff by simp
    finally show ?thesis .
  qed
  show ?thesis unfolding power by simp
qed

lemma fri_canonical_domain_at_round_product:
  assumes eval_power: "clength * scale = 2 ^ N"
    and i_bound: "i \<le> N"
  shows "length (fri_canonical_domain_at i) * 2 ^ i =
    clength * scale"
  unfolding fri_canonical_domain_at_length_power[OF eval_power i_bound]
    eval_power
  using i_bound by (simp add: power_add[symmetric])

lemma fri_canonical_domain_successor_length:
  assumes eval_power: "clength * scale = 2 ^ N"
    and i_bound: "i < N"
  shows
    "length (fri_canonical_domain_at (Suc i)) =
      length (fri_canonical_domain_at i) div 2"
proof -
  have diff: "N - i = Suc (N - Suc i)"
    using i_bound by linarith
  have current:
      "length (fri_canonical_domain_at i) = 2 * 2 ^ (N - Suc i)"
  proof -
    have "length (fri_canonical_domain_at i) = 2 ^ (N - i)"
      by (rule fri_canonical_domain_at_length_power[OF eval_power])
        (use i_bound in simp)
    also have "... = 2 * 2 ^ (N - Suc i)"
      unfolding diff by simp
    finally show ?thesis .
  qed
  have next_len:
      "length (fri_canonical_domain_at (Suc i)) = 2 ^ (N - Suc i)"
    by (rule fri_canonical_domain_at_length_power[OF eval_power])
      (use i_bound in simp)
  show ?thesis
    unfolding current next_len by simp
qed

lemma fri_canonical_domain_successor_map_square:
  assumes eval_power: "clength * scale = 2 ^ N"
    and i_bound: "i < N"
  shows
    "fri_canonical_domain_at (Suc i) =
      map (\<lambda>j. (fri_canonical_domain_at i ! j) ^ 2)
        [0..<length (fri_canonical_domain_at i) div 2]"
proof (rule nth_equalityI)
  have suc_le: "Suc i \<le> N" using i_bound by simp
  show
    "length (fri_canonical_domain_at (Suc i)) =
      length (map (\<lambda>j. (fri_canonical_domain_at i ! j) ^ 2)
        [0..<length (fri_canonical_domain_at i) div 2])"
    by (simp add: fri_canonical_domain_successor_length[OF eval_power i_bound])
next
  fix j
  assume j_bound: "j < length (fri_canonical_domain_at (Suc i))"
  have cur_bound: "j < length (fri_canonical_domain_at i)"
    using j_bound
      fri_canonical_domain_successor_length[OF eval_power i_bound]
    by simp
  show
    "fri_canonical_domain_at (Suc i) ! j =
      map (\<lambda>j. (fri_canonical_domain_at i ! j) ^ 2)
        [0..<length (fri_canonical_domain_at i) div 2] ! j"
    using fri_canonical_domain_successor_square[OF j_bound cur_bound]
      j_bound fri_canonical_domain_successor_length[OF eval_power i_bound]
    by simp
qed

lemma distinct_fri_canonical_domain_at:
  assumes eval_power: "clength * scale = 2 ^ N"
    and i_bound: "i \<le> N"
  shows "distinct (fri_canonical_domain_at i)"
proof -
  have len_pos: "0 < length (fri_canonical_domain_at i)"
    by (rule fri_canonical_domain_at_pos[OF eval_power i_bound])
  have round:
      "length (fri_canonical_domain_at i) * 2 ^ i = clength * scale"
    by (rule fri_canonical_domain_at_round_product[OF eval_power i_bound])
  have domain_eq:
      "fri_canonical_domain_at i =
        map (\<lambda>idx. (h ^ idx * shift) ^ (2 ^ i))
          [0..<length (fri_canonical_domain_at i)]"
    unfolding fri_canonical_domain_at_def fri_canonical_domain_at_length
    by simp
  have distinct:
      "distinct
        (map (\<lambda>idx. (h ^ idx * shift) ^ (2 ^ i))
          [0..<length (fri_canonical_domain_at i)])"
    by (rule distinct_fri_round_domain[OF len_pos _ round]) simp
  show ?thesis
    using domain_eq distinct by simp
qed

lemma conditioned_transition_challenge_or_agreement:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and current_cover:
      "length (fri_canonical_domain_at i) \<le> length current"
    and next_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le> length next"
    and committed: "committed i prefix = current"
    and current_not_low:
      "\<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i current)"
    and next_low:
      "fri_table_low_degree_on
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i) next)"
    and idx_bound:
      "idx < length (fri_canonical_domain_at i) div 2"
    and sampled:
      "fri_conditioned_layer_table (Suc i) next ! idx =
        fri_table_fold_value b (fri_conditioned_layer_table i current)
          (fri_canonical_domain_at i)
          (length (fri_canonical_domain_at i)) (2 ^ i) idx"
  shows
    "b \<in> fri_conditioned_bad_challenges d committed i prefix \<or>
      idx \<in> fri_conditioned_agreement_indices i current next b"
proof -
  let ?D = "fri_padded_degree_bound d"
  let ?k = "fri_degree_after (Suc i) ?D"
  let ?cur_dom = "fri_canonical_domain_at i"
  let ?next_dom = "fri_canonical_domain_at (Suc i)"
  let ?cur = "fri_conditioned_layer_table i current"
  let ?next = "fri_conditioned_layer_table (Suc i) next"
  let ?p = "fri_table_interpolant ?cur_dom ?cur"
  let ?q = "fri_table_interpolant ?next_dom ?next"
  have i_le_N: "i \<le> N"
    using round_bound rounds_le by simp
  have suc_le_N: "Suc i \<le> N"
    using round_bound rounds_le by simp
  have i_lt_N: "i < N"
    using round_bound rounds_le by simp
  have cur_len: "length ?cur = length ?cur_dom"
    by (rule length_fri_conditioned_layer_table[OF current_cover])
  have next_len: "length ?next = length ?next_dom"
    by (rule length_fri_conditioned_layer_table[OF next_cover])
  have cur_distinct: "distinct ?cur_dom"
    by (rule distinct_fri_canonical_domain_at[OF eval_power i_le_N])
  have next_distinct: "distinct ?next_dom"
    by (rule distinct_fri_canonical_domain_at[OF eval_power suc_le_N])
  have p_reproduces: "map (poly ?p) ?cur_dom = ?cur"
    by (rule fri_table_interpolant_reproduces[OF cur_distinct cur_len])
  have cur_layer: "?cur = map (poly ?p) ?cur_dom"
    using p_reproduces by simp
  have q_reproduces: "map (poly ?q) ?next_dom = ?next"
    by (rule fri_table_interpolant_reproduces[OF next_distinct next_len])
  have p_high_target:
      "degree ?p > fri_degree_after i ?D"
    using current_not_low
      fri_table_interpolant_low_degree_iff[OF cur_distinct cur_len,
        of "fri_degree_after i ?D"]
    by simp
  have target_step:
      "fri_degree_after i ?D = 2 * ?k + 1"
    by (rule fri_degree_after_padded_step[OF round_bound])
  have p_high: "degree ?p > 2 * ?k + 1"
    using p_high_target target_step by linarith
  have q_degree: "degree ?q \<le> ?k"
    using next_low
      fri_table_interpolant_low_degree_iff[OF next_distinct next_len, of ?k]
    by simp
  show ?thesis
  proof (cases "b \<in> fri_conditioned_bad_challenges d committed i prefix")
    case True
    then show ?thesis by simp
  next
    case not_cover: False
    have cover_eq:
        "fri_conditioned_bad_challenges d committed i prefix =
          fri_low_fold_challenges ?p ?k"
      unfolding fri_conditioned_bad_challenges_def Let_def committed
      using p_high by simp
    have not_low_challenge: "b \<notin> fri_low_fold_challenges ?p ?k"
      using not_cover cover_eq by simp
    have folded_high:
        "degree (fri_symbolic_fold_polynomial ?p b) > ?k"
      using not_low_challenge unfolding fri_low_fold_challenges_def by simp
    have different: "fri_symbolic_fold_polynomial ?p b \<noteq> ?q"
      using folded_high q_degree by auto
    have len_pos: "0 < length ?cur_dom"
      by (rule fri_canonical_domain_at_pos[OF eval_power i_le_N])
    have even_len: "2 dvd length ?cur_dom"
      by (rule fri_canonical_domain_at_even[OF eval_power i_lt_N])
    have product:
        "length ?cur_dom * 2 ^ i = clength * scale"
      by (rule fri_canonical_domain_at_round_product[OF eval_power i_le_N])
    have cur_dom_def:
        "?cur_dom =
          map (\<lambda>j. (h ^ j * shift) ^ (2 ^ i))
            [0..<length ?cur_dom]"
      unfolding fri_canonical_domain_at_def fri_canonical_domain_at_length
      by simp
    have next_dom_def:
        "?next_dom =
          map (\<lambda>j. (?cur_dom ! j) ^ 2)
            [0..<length ?cur_dom div 2]"
      by (rule fri_canonical_domain_successor_map_square[
          OF eval_power i_lt_N])
    have successor_length:
        "length ?next_dom = length ?cur_dom div 2"
      by (rule fri_canonical_domain_successor_length[OF eval_power i_lt_N])
    have idx_next: "idx < length ?next_dom"
      using idx_bound successor_length by simp
    have q_eval:
        "poly ?q (?next_dom ! idx) = ?next ! idx"
    proof -
      have
        "map (poly ?q) ?next_dom ! idx = ?next ! idx"
        using q_reproduces by simp
      then show ?thesis
        using idx_next by simp
    qed
    have next_value:
        "?next ! idx = poly ?q (?next_dom ! idx)"
      using q_eval by simp
    have successor_idx:
        "?next_dom ! idx = (?cur_dom ! idx) ^ 2"
      using next_dom_def idx_bound by simp
    have folded_base:
        "fri_table_fold_value b ?cur ?cur_dom
            (length ?cur_dom) (2 ^ i) idx =
          poly (fri_symbolic_fold_polynomial ?p b) ((?cur_dom ! idx) ^ 2)"
      by (rule fri_table_fold_value_polynomial[
          OF len_pos even_len product cur_dom_def cur_layer idx_bound])
    have folded_value:
        "fri_table_fold_value b ?cur ?cur_dom
            (length ?cur_dom) (2 ^ i) idx =
          poly (fri_symbolic_fold_polynomial ?p b) (?next_dom ! idx)"
      using folded_base successor_idx by simp
    have agreement:
        "poly (fri_symbolic_fold_polynomial ?p b) (?next_dom ! idx) =
          poly ?q (?next_dom ! idx)"
      using sampled folded_value next_value by simp
    have membership:
        "idx \<in> fri_polynomial_agreement_indices
          (fri_symbolic_fold_polynomial ?p b) ?q ?next_dom"
      using idx_bound successor_length agreement
      unfolding fri_polynomial_agreement_indices_def by simp
    show ?thesis
      using membership not_cover
      unfolding fri_conditioned_agreement_indices_def by simp
  qed
qed

lemma generic_canonical_chain_conditioned_sampled_fold:
  assumes chain:
      "generic_fri_canonical_sampled_layer_chain_evidence low_degree
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers"
    and eval_power: "clength * scale = 2 ^ N"
    and rounds_le: "length challenges \<le> N"
    and layer_cover:
      "\<And>j. j \<le> length challenges \<Longrightarrow>
        length (fri_canonical_domain_at j) \<le> length (layers ! j)"
    and round_idx_bound: "round_idx < length query_idxs"
    and layer_idx_bound: "layer_idx < length challenges"
  shows
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      length (fri_canonical_domain_at layer_idx) div 2"
    "fri_conditioned_layer_table (Suc layer_idx)
        (layers ! Suc layer_idx) !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx =
      fri_table_fold_value (challenges ! layer_idx)
        (fri_conditioned_layer_table layer_idx (layers ! layer_idx))
        (fri_canonical_domain_at layer_idx)
        (length (fri_canonical_domain_at layer_idx))
        (2 ^ layer_idx)
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
proof -
  let ?raw =
    "fri_evidence_layer_idx roots query_idxs round_idx layer_idx"
  let ?idx =
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx"
  let ?len = "fri_evidence_layer_len roots layer_idx"
  have sampled_chain:
      "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
        degree_bound roots challenges final_value query_idxs round_layers
        (fri_canonical_domains (length challenges)) layers"
    by (rule generic_fri_canonical_sampled_layer_chain_evidenceD[OF chain])
  have partial:
      "generic_fri_partial_evidence low_degree candidate_table degree_bound
        roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF sampled_chain])
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have len_eq:
      "?len = length (fri_canonical_domain_at layer_idx)"
    unfolding fri_evidence_layer_len_def fri_canonical_domain_at_length
    using roots_len fri_layer_lengths_nth_div[
        of layer_idx "length roots" "clength * scale"]
      layer_idx_bound
    by simp
  have current_dom:
      "fri_canonical_domains (length challenges) ! layer_idx =
        fri_canonical_domain_at layer_idx"
    by (rule fri_canonical_domains_nth) (use layer_idx_bound in simp)
  have sampled_fold:
      "fri_sampled_table_fold (challenges ! layer_idx) ?len ?raw
        (2 ^ layer_idx)
        (fri_canonical_domain_at layer_idx)
        (layers ! layer_idx)
        (round_layers ! round_idx ! layer_idx)
        (layers ! Suc layer_idx ! ?idx)"
    using generic_fri_sampled_layer_chain_evidence_sample(2)[
        OF sampled_chain round_idx_bound layer_idx_bound]
      current_dom by simp
  have opening_match_ex:
      "\<exists>xp xn. fri_opening_matches_table ?len ?raw
        (layers ! layer_idx) xp xn"
    using sampled_fold unfolding fri_sampled_table_fold_def by blast
  then obtain xp xn where opening_match:
      "fri_opening_matches_table ?len ?raw (layers ! layer_idx) xp xn"
    by blast
  have raw_bound: "?raw < ?len"
    by (rule fri_opening_matches_tableD(1)[OF opening_match])
  have i_lt_N: "layer_idx < N"
    using layer_idx_bound rounds_le by simp
  have i_le_N: "layer_idx \<le> N"
    using i_lt_N by simp
  have len_pos: "0 < ?len"
    unfolding len_eq
    by (rule fri_canonical_domain_at_pos[OF eval_power i_le_N])
  have even_len: "2 dvd ?len"
    unfolding len_eq
    by (rule fri_canonical_domain_at_even[OF eval_power i_lt_N])
  have product: "?len * 2 ^ layer_idx = clength * scale"
    unfolding len_eq
    by (rule fri_canonical_domain_at_round_product[OF eval_power i_le_N])
  have half_pos: "0 < ?len div 2"
    using len_pos even_len by (cases ?len) auto
  have idx_eq: "?idx = ?raw mod (?len div 2)"
    unfolding fri_evidence_next_idx_def by simp
  have idx_bound: "?idx < ?len div 2"
    unfolding idx_eq using half_pos by simp
  show "?idx < length (fri_canonical_domain_at layer_idx) div 2"
    using idx_bound len_eq by simp
  have canonical_idx_bound:
      "?idx < length (fri_canonical_domain_at layer_idx)"
    using idx_bound len_eq by simp
  have dom_norm:
      "fri_canonical_domain_at layer_idx ! ?idx =
        (h ^ ?idx * shift) ^ (2 ^ layer_idx)"
    by (rule fri_canonical_domain_at_nth[OF canonical_idx_bound])
  have dom_norm_mod:
      "fri_canonical_domain_at layer_idx ! (?raw mod (?len div 2)) =
        (h ^ (?raw mod (?len div 2)) * shift) ^ (2 ^ layer_idx)"
    using dom_norm idx_eq by simp
  have original_fold_mod:
      "layers ! Suc layer_idx ! ?idx =
        fri_table_fold_value (challenges ! layer_idx)
          (layers ! layer_idx) (fri_canonical_domain_at layer_idx)
          ?len (2 ^ layer_idx) (?raw mod (?len div 2))"
    by (rule fri_sampled_table_fold_eq_at_mod_index[
        OF sampled_fold even_len product dom_norm_mod])
  have original_fold:
      "layers ! Suc layer_idx ! ?idx =
        fri_table_fold_value (challenges ! layer_idx)
          (layers ! layer_idx) (fri_canonical_domain_at layer_idx)
          ?len (2 ^ layer_idx) ?idx"
    using original_fold_mod idx_eq by simp
  have successor_len:
      "length (fri_canonical_domain_at (Suc layer_idx)) = ?len div 2"
    unfolding len_eq
    by (rule fri_canonical_domain_successor_length[
        OF eval_power i_lt_N])
  have next_take:
      "fri_conditioned_layer_table (Suc layer_idx)
          (layers ! Suc layer_idx) ! ?idx =
        layers ! Suc layer_idx ! ?idx"
    by (rule fri_conditioned_layer_table_nth)
      (use idx_bound successor_len in simp)
  have conditioned_fold_len:
      "fri_table_fold_value (challenges ! layer_idx)
          (fri_conditioned_layer_table layer_idx (layers ! layer_idx))
          (fri_canonical_domain_at layer_idx)
          ?len (2 ^ layer_idx) ?idx =
        fri_table_fold_value (challenges ! layer_idx)
          (layers ! layer_idx) (fri_canonical_domain_at layer_idx)
          ?len (2 ^ layer_idx) ?idx"
    by (rule fri_table_fold_value_conditioned_layer[
        OF len_pos len_eq idx_bound])
  have conditioned_fold:
      "fri_table_fold_value (challenges ! layer_idx)
          (fri_conditioned_layer_table layer_idx (layers ! layer_idx))
          (fri_canonical_domain_at layer_idx)
          (length (fri_canonical_domain_at layer_idx))
          (2 ^ layer_idx) ?idx =
        fri_table_fold_value (challenges ! layer_idx)
          (layers ! layer_idx) (fri_canonical_domain_at layer_idx)
          ?len (2 ^ layer_idx) ?idx"
    using conditioned_fold_len len_eq by simp
  show
    "fri_conditioned_layer_table (Suc layer_idx)
        (layers ! Suc layer_idx) ! ?idx =
      fri_table_fold_value (challenges ! layer_idx)
        (fri_conditioned_layer_table layer_idx (layers ! layer_idx))
        (fri_canonical_domain_at layer_idx)
        (length (fri_canonical_domain_at layer_idx))
        (2 ^ layer_idx) ?idx"
    using original_fold next_take conditioned_fold by simp
qed

definition fri_conditioned_residual_query_lists
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow> nat \<Rightarrow> nat list set"
where
  "fri_conditioned_residual_query_lists roots challenges layers i =
    {qs. \<forall>round_idx < length qs.
      fri_evidence_next_idx roots qs round_idx i \<in>
        fri_conditioned_agreement_indices i
          (layers ! i) (layers ! Suc i) (challenges ! i)}"

lemma generic_canonical_sampled_chain_conditioned_split:
  assumes chain:
      "generic_fri_canonical_sampled_layer_chain_evidence low_degree
        candidate_table d roots challenges final_value query_idxs
        round_layers layers"
    and eval_power: "clength * scale = 2 ^ N"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and layer_cover:
      "\<And>j. j \<le> length challenges \<Longrightarrow>
        length (fri_canonical_domain_at j) \<le> length (layers ! j)"
    and committed_path:
      "\<And>j. j < length challenges \<Longrightarrow>
        committed j (take j challenges) = layers ! j"
    and start_not_low:
      "\<not> fri_table_low_degree_on (fri_padded_degree_bound d)
        (fri_canonical_domain_at 0)
        (fri_conditioned_layer_table 0 (layers ! 0))"
  shows
    "challenges \<in> generic_fri_bad_challenge_lists
        (length challenges) (fri_conditioned_bad_challenges d committed) \<or>
      (\<exists>i < length challenges.
        query_idxs \<in>
          fri_conditioned_residual_query_lists roots challenges layers i)"
proof (rule ccontr)
  assume not_conclusion:
    "\<not> (challenges \<in> generic_fri_bad_challenge_lists
          (length challenges) (fri_conditioned_bad_challenges d committed) \<or>
        (\<exists>i < length challenges.
          query_idxs \<in>
            fri_conditioned_residual_query_lists roots challenges layers i))"
  then have not_bad:
      "challenges \<notin> generic_fri_bad_challenge_lists
        (length challenges) (fri_conditioned_bad_challenges d committed)"
    by simp
  from not_conclusion have no_residual:
      "\<And>i. i < length challenges \<Longrightarrow>
        query_idxs \<notin>
          fri_conditioned_residual_query_lists roots challenges layers i"
    by blast
  have sampled_chain:
      "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
        d roots challenges final_value query_idxs round_layers
        (fri_canonical_domains (length challenges)) layers"
    by (rule generic_fri_canonical_sampled_layer_chain_evidenceD[OF chain])
  have partial:
      "generic_fri_partial_evidence low_degree candidate_table d roots
        challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF sampled_chain])
  have challenges_len:
      "length challenges = ceil_log (Suc d)"
    using generic_fri_partial_evidence_shapes(1)[OF partial]
      generic_fri_partial_evidence_shapes(2)[OF partial]
    unfolding fri_round_count_for_degree_bound_def by simp
  have challenge_space:
      "challenges \<in> fri_challenge_space (length challenges)"
    unfolding fri_challenge_space_def by simp
  have not_low:
      "\<And>i. i \<le> length challenges \<Longrightarrow>
        \<not> fri_table_low_degree_on
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i)
          (fri_conditioned_layer_table i (layers ! i))"
  proof -
    fix i
    assume i_bound: "i \<le> length challenges"
    show
      "\<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i (layers ! i))"
      using i_bound
    proof (induction i)
      case 0
      then show ?case
        using start_not_low by simp
    next
      case (Suc i)
      have i_lt: "i < length challenges"
        using Suc.prems by simp
      have current_not_low:
          "\<not> fri_table_low_degree_on
            (fri_degree_after i (fri_padded_degree_bound d))
            (fri_canonical_domain_at i)
            (fri_conditioned_layer_table i (layers ! i))"
        by (rule Suc.IH) (use Suc.prems in simp)
      show ?case
      proof
        assume next_low:
          "fri_table_low_degree_on
            (fri_degree_after (Suc i) (fri_padded_degree_bound d))
            (fri_canonical_domain_at (Suc i))
            (fri_conditioned_layer_table (Suc i) (layers ! Suc i))"
        have challenge_not_bad:
            "challenges ! i \<notin>
              fri_conditioned_bad_challenges d committed i
                (take i challenges)"
          by (rule fri_multiround_bad_challenge_lists_notinD[
              OF challenge_space _ i_lt])
            (use not_bad in
              \<open>simp add: generic_fri_bad_challenge_lists_def\<close>)
        have agreement_all:
            "\<forall>round_idx < length query_idxs.
              fri_evidence_next_idx roots query_idxs round_idx i \<in>
                fri_conditioned_agreement_indices i
                  (layers ! i) (layers ! Suc i) (challenges ! i)"
        proof (intro allI impI)
          fix round_idx
          assume round_idx_bound: "round_idx < length query_idxs"
          have idx_bound:
              "fri_evidence_next_idx roots query_idxs round_idx i <
                length (fri_canonical_domain_at i) div 2"
            by (rule generic_canonical_chain_conditioned_sampled_fold(1)[
                OF chain eval_power])
              (use rounds_le challenges_len layer_cover round_idx_bound i_lt
                in simp_all)
          have sampled:
              "fri_conditioned_layer_table (Suc i) (layers ! Suc i) !
                  fri_evidence_next_idx roots query_idxs round_idx i =
                fri_table_fold_value (challenges ! i)
                  (fri_conditioned_layer_table i (layers ! i))
                  (fri_canonical_domain_at i)
                  (length (fri_canonical_domain_at i)) (2 ^ i)
                  (fri_evidence_next_idx roots query_idxs round_idx i)"
            by (rule generic_canonical_chain_conditioned_sampled_fold(2)[
                OF chain eval_power])
              (use rounds_le challenges_len layer_cover round_idx_bound i_lt
                in simp_all)
          have i_round: "i < ceil_log (Suc d)"
            using challenges_len i_lt by simp
          have cover_i:
              "length (fri_canonical_domain_at i) \<le> length (layers ! i)"
            by (rule layer_cover) (use i_lt in simp)
          have cover_suc:
              "length (fri_canonical_domain_at (Suc i)) \<le>
                length (layers ! Suc i)"
            by (rule layer_cover) (use i_lt in simp)
          have split:
              "challenges ! i \<in>
                  fri_conditioned_bad_challenges d committed i
                    (take i challenges) \<or>
                fri_evidence_next_idx roots query_idxs round_idx i \<in>
                  fri_conditioned_agreement_indices i
                    (layers ! i) (layers ! Suc i) (challenges ! i)"
            by (rule conditioned_transition_challenge_or_agreement[
                where N=N and d=d and i=i
                  and current="layers ! i"
                  and committed=committed and prefix="take i challenges"
                  and idx="fri_evidence_next_idx roots query_idxs round_idx i"
                  and b="challenges ! i",
                OF eval_power i_round rounds_le cover_i cover_suc
                  committed_path[OF i_lt] current_not_low next_low
                  idx_bound sampled])
          show
              "fri_evidence_next_idx roots query_idxs round_idx i \<in>
                fri_conditioned_agreement_indices i
                  (layers ! i) (layers ! Suc i) (challenges ! i)"
            using split challenge_not_bad by blast
        qed
        have residual:
            "query_idxs \<in>
              fri_conditioned_residual_query_lists roots challenges layers i"
          using agreement_all
          unfolding fri_conditioned_residual_query_lists_def by simp
        show False
          using no_residual[OF i_lt] residual by contradiction
      qed
    qed
  qed
  have final_consistent:
      "fri_final_constant_consistent
        (layers ! length challenges) final_value"
    by (rule generic_fri_sampled_layer_chain_evidenceD(6)[OF sampled_chain])
  have final_conditioned_consistent:
      "fri_final_constant_consistent
        (fri_conditioned_layer_table (length challenges)
          (layers ! length challenges)) final_value"
    using final_consistent
    unfolding fri_final_constant_consistent_def
      fri_conditioned_layer_table_def
    by (meson in_set_takeD)
  have final_len:
      "length
          (fri_conditioned_layer_table (length challenges)
            (layers ! length challenges)) =
        length (fri_canonical_domain_at (length challenges))"
    by (rule length_fri_conditioned_layer_table)
      (rule layer_cover[OF order_refl])
  have final_low:
      "fri_table_low_degree_on
        (fri_degree_after (length challenges) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (length challenges))
        (fri_conditioned_layer_table (length challenges)
          (layers ! length challenges))"
    by (rule fri_final_constant_consistent_low_degree_if_lengths[
        OF final_conditioned_consistent final_len])
  have final_not_low:
      "\<not> fri_table_low_degree_on
        (fri_degree_after (length challenges) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (length challenges))
        (fri_conditioned_layer_table (length challenges)
          (layers ! length challenges))"
    by (rule not_low) simp
  show False
    using final_low final_not_low by contradiction
qed



lemma card_conditioned_bad_challenge_lists_bound:
  "card (generic_fri_bad_challenge_lists n
      (fri_conditioned_bad_challenges d committed))
    \<le> n * CARD('f) ^ (n - 1)"
proof -
  have bound:
      "card (generic_fri_bad_challenge_lists n
          (fri_conditioned_bad_challenges d committed))
        \<le> (\<Sum>i\<in>{..<n}.
          CARD('f) ^ i * 1 * CARD('f) ^ (n - Suc i))"
    by (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds)
      (use card_fri_conditioned_bad_challenges_le_one in simp)
  have local_term:
      "\<And>i. i < n \<Longrightarrow>
        CARD('f) ^ i * 1 * CARD('f) ^ (n - Suc i) =
          CARD('f) ^ (n - 1)"
  proof -
    fix i
    assume i_bound: "i < n"
    have exponent: "i + (n - Suc i) = n - 1"
      using i_bound by linarith
    show
      "CARD('f) ^ i * 1 * CARD('f) ^ (n - Suc i) =
        CARD('f) ^ (n - 1)"
      using exponent by (simp add: power_add[symmetric])
  qed
  have sum_eq:
      "(\<Sum>i\<in>{..<n}.
        CARD('f) ^ i * 1 * CARD('f) ^ (n - Suc i)) =
        n * CARD('f) ^ (n - 1)"
  proof -
    have
      "(\<Sum>i\<in>{..<n}.
        CARD('f) ^ i * 1 * CARD('f) ^ (n - Suc i)) =
        (\<Sum>i\<in>{..<n}. CARD('f) ^ (n - 1))"
      by (rule sum.cong) (use local_term in simp_all)
    also have "... = n * CARD('f) ^ (n - 1)"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
    using bound sum_eq by simp
qed

lemma card_fri_conditioned_agreement_indices_strict:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and current_cover:
      "length (fri_canonical_domain_at i) \<le> length current"
    and next_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le> length next"
    and committed: "committed i prefix = current"
    and current_not_low:
      "\<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i current)"
    and next_low:
      "fri_table_low_degree_on
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i) next)"
    and not_cover:
      "b \<notin> fri_conditioned_bad_challenges d committed i prefix"
  shows
    "card (fri_conditioned_agreement_indices i current next b) \<le>
      length (fri_canonical_domain_at (Suc i)) - 1"
proof -
  let ?D = "fri_padded_degree_bound d"
  let ?k = "fri_degree_after (Suc i) ?D"
  let ?cur_dom = "fri_canonical_domain_at i"
  let ?next_dom = "fri_canonical_domain_at (Suc i)"
  let ?cur = "fri_conditioned_layer_table i current"
  let ?next = "fri_conditioned_layer_table (Suc i) next"
  let ?p = "fri_table_interpolant ?cur_dom ?cur"
  let ?q = "fri_table_interpolant ?next_dom ?next"
  have i_le_N: "i \<le> N" using round_bound rounds_le by simp
  have suc_le_N: "Suc i \<le> N" using round_bound rounds_le by simp
  have i_lt_N: "i < N" using round_bound rounds_le by simp
  have cur_len: "length ?cur = length ?cur_dom"
    by (rule length_fri_conditioned_layer_table[OF current_cover])
  have next_len: "length ?next = length ?next_dom"
    by (rule length_fri_conditioned_layer_table[OF next_cover])
  have cur_distinct: "distinct ?cur_dom"
    by (rule distinct_fri_canonical_domain_at[OF eval_power i_le_N])
  have next_distinct: "distinct ?next_dom"
    by (rule distinct_fri_canonical_domain_at[OF eval_power suc_le_N])
  have p_high_target: "degree ?p > fri_degree_after i ?D"
    using current_not_low
      fri_table_interpolant_low_degree_iff[OF cur_distinct cur_len,
        of "fri_degree_after i ?D"]
    by simp
  have target_step: "fri_degree_after i ?D = 2 * ?k + 1"
    by (rule fri_degree_after_padded_step[OF round_bound])
  have p_high: "degree ?p > 2 * ?k + 1"
    using p_high_target target_step by linarith
  have cover_eq:
      "fri_conditioned_bad_challenges d committed i prefix =
        fri_low_fold_challenges ?p ?k"
    unfolding fri_conditioned_bad_challenges_def Let_def committed
    using p_high by simp
  have folded_high:
      "degree (fri_symbolic_fold_polynomial ?p b) > ?k"
    using not_cover cover_eq unfolding fri_low_fold_challenges_def by simp
  have q_degree_low: "degree ?q \<le> ?k"
    using next_low
      fri_table_interpolant_low_degree_iff[OF next_distinct next_len, of ?k]
    by simp
  have different: "fri_symbolic_fold_polynomial ?p b \<noteq> ?q"
    using folded_high q_degree_low by auto
  have p_degree: "degree ?p \<le> length ?cur_dom - 1"
    using degree_fri_table_interpolant_le[of ?cur_dom ?cur] cur_len
    by simp
  have folded_degree:
      "degree (fri_symbolic_fold_polynomial ?p b) \<le> degree ?p div 2"
    by (rule fri_symbolic_fold_degree_le_half)
  have cur_even: "2 dvd length ?cur_dom"
    by (rule fri_canonical_domain_at_even[OF eval_power i_lt_N])
  have cur_pos: "0 < length ?cur_dom"
    by (rule fri_canonical_domain_at_pos[OF eval_power i_le_N])
  obtain m where cur_eq: "length ?cur_dom = 2 * m"
    using cur_even by blast
  have m_pos: "0 < m"
    using cur_pos cur_eq by simp
  have half_pred:
      "(length ?cur_dom - 1) div 2 = length ?cur_dom div 2 - 1"
    using cur_eq m_pos by simp
  have successor_len:
      "length ?next_dom = length ?cur_dom div 2"
    by (rule fri_canonical_domain_successor_length[OF eval_power i_lt_N])
  have p_degree_half:
      "degree ?p div 2 \<le> (length ?cur_dom - 1) div 2"
    by (rule div_le_mono[OF p_degree])
  have folded_le:
      "degree (fri_symbolic_fold_polynomial ?p b) \<le>
        length ?next_dom - 1"
    using folded_degree p_degree_half half_pred successor_len
    by linarith
  have q_le: "degree ?q \<le> length ?next_dom - 1"
    using degree_fri_table_interpolant_le[of ?next_dom ?next] next_len
    by simp
  have max_le:
      "max (degree (fri_symbolic_fold_polynomial ?p b)) (degree ?q) \<le>
        length ?next_dom - 1"
    using folded_le q_le by simp
  have card_le:
      "card (fri_polynomial_agreement_indices
        (fri_symbolic_fold_polynomial ?p b) ?q ?next_dom) \<le>
        max (degree (fri_symbolic_fold_polynomial ?p b)) (degree ?q)"
    by (rule fri_polynomial_agreement_indices_card_bound[
        OF next_distinct different])
  show ?thesis
    unfolding fri_conditioned_agreement_indices_def
    using card_le max_le by linarith
qed

end


end
