theory Soundness_FRI_Robust_Conceptual_Split
  imports
    Soundness_FRI_Robust_Multiround
    Stark.Soundness_FRI_Conditioned_Authenticated_Bridge
    Stark.Soundness_FRI_Conditioned_Actual_Bridge
    Stark.Soundness_FRI_Conditioned_Builder_Split
    Stark.Soundness_FRI_Conditioned_Query_Fiber
begin

context soundness
begin

definition fri_robust_conditioned_layers ::
  "nat => 'f list list => 'f list list"
where
  "fri_robust_conditioned_layers n layers =
    map (\<lambda>i. fri_conditioned_layer_table i (layers ! i)) [0..<Suc n]"

lemma length_fri_robust_conditioned_layers[simp]:
  "length (fri_robust_conditioned_layers n layers) = Suc n"
  unfolding fri_robust_conditioned_layers_def by simp

lemma fri_robust_conditioned_layers_nth:
  assumes "i \<le> n"
  shows
    "fri_robust_conditioned_layers n layers ! i =
      fri_conditioned_layer_table i (layers ! i)"
proof -
  have i_bound: "i < length [0..<Suc n]"
    using assms by simp
  have range_nth_raw: "[0..<Suc n] ! i = 0 + i"
    by (rule nth_upt) (use assms in simp)
  have range_nth: "[0..<Suc n] ! i = i"
    using range_nth_raw by simp
  show ?thesis
    unfolding fri_robust_conditioned_layers_def
    by (subst nth_map[OF i_bound]) (simp only: range_nth)
qed


lemma length_fri_robust_conditioned_layers_nth:
  assumes i_bound: "i \<le> n"
    and cover:
      "\<And>j. j \<le> n \<Longrightarrow>
        length (fri_canonical_domain_at j) \<le> length (layers ! j)"
  shows
    "length (fri_robust_conditioned_layers n layers ! i) =
      length (fri_canonical_domain_at i)"
  unfolding fri_robust_conditioned_layers_nth[OF i_bound]
  by (rule length_fri_conditioned_layer_table[OF cover[OF i_bound]])

lemma fri_table_low_degree_distance_zero:
  assumes low: "fri_table_low_degree_on d fri_dom table"
  shows "fri_rs_distance_to_code d fri_dom (nth table) = 0"
proof -
  have word: "nth table \<in> fri_rs_code_functions d fri_dom"
    using low
    unfolding fri_table_low_degree_on_def
      fri_rs_code_functions_def fri_rs_code_tables_def
    by blast
  have upper:
      "fri_rs_distance_to_code d fri_dom (nth table) \<le>
        card (code_disagreement_indices
          {..<length fri_dom} (nth table) (nth table))"
    by (rule fri_rs_distance_to_code_le[OF word])
  have
      "card (code_disagreement_indices
        {..<length fri_dom} (nth table) (nth table)) = 0"
    unfolding code_disagreement_indices_def by simp
  then show ?thesis
    using upper by simp
qed

lemma fri_robust_conditioned_terminal_close:
  assumes final_low:
      "fri_table_low_degree_on
        (fri_degree_after n (fri_padded_degree_bound d))
        (fri_canonical_domain_at n)
        (fri_conditioned_layer_table n (layers ! n))"
  shows
    "fri_canonical_layer_close d
      (fri_robust_conditioned_layers n layers) radius n"
proof -
  have distance_zero:
      "fri_rs_distance_to_code
        (fri_degree_after n (fri_padded_degree_bound d))
        (fri_canonical_domain_at n)
        (nth (fri_robust_conditioned_layers n layers ! n)) = 0"
    unfolding fri_robust_conditioned_layers_nth[OF order_refl]
    by (rule fri_table_low_degree_distance_zero[OF final_low])
  show ?thesis
    using distance_zero
    unfolding fri_canonical_layer_close_def by simp
qed


definition fri_robust_conditioned_bad_challenges ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (nat \<Rightarrow> 'f list \<Rightarrow> 'f list) \<Rightarrow>
    nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
where
  "fri_robust_conditioned_bad_challenges d m K committed i prefix =
    (let current = fri_conditioned_layer_table i (committed i prefix);
         good_radius = fri_linear_good_radius m K i;
         distance = fri_rs_distance_to_code
           (fri_degree_after i (fri_padded_degree_bound d))
           (fri_canonical_domain_at i) (nth current)
     in if distance \<le> 2 * good_radius
        then {}
        else fri_fold_good_challenges
          (fri_degree_after (Suc i) (fri_padded_degree_bound d))
          (fri_canonical_domain_at (Suc i))
          (length (fri_canonical_domain_at i))
          (fri_canonical_domain_at i) current good_radius)"

definition fri_robust_conditioned_agreement_indices ::
  "'f list \<Rightarrow> 'f list list \<Rightarrow> nat \<Rightarrow> nat set"
where
  "fri_robust_conditioned_agreement_indices challenges layers i =
    fri_fold_next_agreement_indices
      (challenges ! i) (length (fri_canonical_domain_at i))
      (fri_canonical_domain_at i)
      (fri_conditioned_layer_table i (layers ! i))
      (fri_conditioned_layer_table (Suc i) (layers ! Suc i))"

definition fri_robust_conditioned_residual_query_lists ::
  "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow>
    nat \<Rightarrow> nat list set"
where
  "fri_robust_conditioned_residual_query_lists roots challenges layers i =
    {qs. \<forall>round_idx < length qs.
      fri_evidence_next_idx roots qs round_idx i \<in>
        fri_robust_conditioned_agreement_indices challenges layers i}"

lemma fri_robust_conditioned_good_eq_canonical:
  assumes i_bound: "i < m"
    and committed_path:
      "committed i (take i challenges) = layers ! i"
    and far:
      "\<not> fri_rs_distance_to_code
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (nth (fri_conditioned_layer_table i (layers ! i))) \<le>
          2 * fri_linear_good_radius m K i"
  shows
    "fri_robust_conditioned_bad_challenges d m K committed i
        (take i challenges) =
      fri_canonical_layer_good_challenges d
        (fri_robust_conditioned_layers m layers)
        (fri_linear_good_radius m K) i"
  using committed_path far
  unfolding fri_robust_conditioned_bad_challenges_def
    fri_canonical_layer_good_challenges_def
    fri_robust_conditioned_layers_nth[OF less_imp_le[OF i_bound]]
    Let_def
  by simp

lemma fri_robust_conditioned_agreement_eq_canonical:
  assumes "i < m"
  shows
    "fri_robust_conditioned_agreement_indices challenges layers i =
      fri_canonical_transition_agreement_indices challenges
        (fri_robust_conditioned_layers m layers) i"
proof -
  have i_le: "i \<le> m"
    using assms by simp
  have suc_le: "Suc i \<le> m"
    using assms by simp
  show ?thesis
    unfolding fri_robust_conditioned_agreement_indices_def
      fri_canonical_transition_agreement_indices_def
      fri_robust_conditioned_layers_nth[OF i_le]
      fri_robust_conditioned_layers_nth[OF suc_le]
    by simp
qed


lemma fri_robust_conditioned_bad_challenges_card:
  fixes d N m K i :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and exponent_fit: "m + K \<le> N"
    and capacity: "16 * Suc m \<le> 2 ^ K"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
    and i_bound: "i < m"
  shows
    "card (fri_robust_conditioned_bad_challenges
      d m K committed i prefix) \<le>
        2 * fri_linear_good_radius m K i + 3"
proof -
  let ?current = "fri_conditioned_layer_table i (committed i prefix)"
  let ?t = "fri_linear_good_radius m K i"
  have K_pos: "0 < K"
  proof (cases K)
    case 0
    then show ?thesis
      using capacity by simp
  next
    case (Suc k)
    then show ?thesis by simp
  qed
  have rounds_fit: "Suc (ceil_log (Suc d)) \<le> N"
    using exponent_fit K_pos rounds_eq by linarith
  have active_round: "i < ceil_log (Suc d)"
    using i_bound rounds_eq by simp
  have radius:
      "4 * ?t \<le> length (fri_canonical_domain_at i) div 4"
    by (rule fri_linear_good_radius_list_compatible[
          OF eval_power i_bound exponent_fit capacity])
  have split:
      "fri_rs_distance_to_code
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i) (nth ?current) \<le> 2 * ?t \<or>
        card (fri_fold_good_challenges
          (fri_degree_after (Suc i) (fri_padded_degree_bound d))
          (fri_canonical_domain_at (Suc i))
          (length (fri_canonical_domain_at i))
          (fri_canonical_domain_at i) ?current ?t) \<le> 2 * ?t + 3"
    by (rule fri_canonical_one_round_decode_or_reject_at[
          OF eval_power active_round rounds_fit initial_rate radius])
  show ?thesis
    using split
    unfolding fri_robust_conditioned_bad_challenges_def Let_def
    by (auto split: if_splits)
qed


lemma sampled_fold_imp_robust_conditioned_agreement:
  fixes i N idx pw :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and i_lt_N: "i < N"
    and successor_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        length (layers ! Suc i)"
    and idx_bound:
      "idx < length (fri_canonical_domain_at i) div 2"
    and sampled_value:
      "fri_conditioned_layer_table (Suc i) (layers ! Suc i) ! idx =
        fri_table_fold_value (challenges ! i)
          (fri_conditioned_layer_table i (layers ! i))
          (fri_canonical_domain_at i)
          (length (fri_canonical_domain_at i)) pw idx"
  shows
    "idx \<in> fri_robust_conditioned_agreement_indices
      challenges layers i"
proof -
  have successor_length:
      "length (fri_conditioned_layer_table (Suc i)
          (layers ! Suc i)) =
        length (fri_canonical_domain_at i) div 2"
    unfolding length_fri_conditioned_layer_table[OF successor_cover]
    by (rule fri_canonical_domain_successor_length[
          OF eval_power i_lt_N])
  have idx_next:
      "idx < length (fri_conditioned_layer_table (Suc i)
        (layers ! Suc i))"
    using idx_bound successor_length by simp
  have fold_eq:
      "fri_folded_received (challenges ! i)
          (length (fri_canonical_domain_at i))
          (fri_canonical_domain_at i)
          (fri_conditioned_layer_table i (layers ! i)) idx =
        nth (fri_conditioned_layer_table (Suc i)
          (layers ! Suc i)) idx"
    using sampled_value
    unfolding fri_folded_received_def fri_table_fold_value_def
    by simp
  show ?thesis
    using idx_next fold_eq
    unfolding fri_robust_conditioned_agreement_indices_def
      fri_fold_next_agreement_indices_def code_agreement_indices_def
    by simp
qed


lemma conceptual_sampled_chain_robust_decode_or_reject:
  fixes d N m K :: nat
  assumes challenge_space:
      "challenges \<in> fri_challenge_space m"
    and challenges_len: "length challenges = m"
    and rounds_eq: "m = ceil_log (Suc d)"
    and eval_power: "clength * scale = 2 ^ N"
    and exponent_fit: "m + K \<le> N"
    and capacity: "16 * Suc m \<le> 2 ^ K"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
    and layer_cover:
      "\<And>j. j \<le> m \<Longrightarrow>
        length (fri_canonical_domain_at j) \<le> length (layers ! j)"
    and committed_path:
      "\<And>j. j < m \<Longrightarrow>
        committed j (take j challenges) = layers ! j"
    and final_low:
      "fri_table_low_degree_on
        (fri_degree_after m (fri_padded_degree_bound d))
        (fri_canonical_domain_at m)
        (fri_conditioned_layer_table m (layers ! m))"
    and sampled:
      "\<And>round_idx i.
        round_idx < length query_idxs \<Longrightarrow>
        i < m \<Longrightarrow>
        fri_evidence_next_idx roots query_idxs round_idx i <
            length (fri_canonical_domain_at i) div 2 \<and>
          fri_conditioned_layer_table (Suc i) (layers ! Suc i) !
              fri_evidence_next_idx roots query_idxs round_idx i =
            fri_table_fold_value (challenges ! i)
              (fri_conditioned_layer_table i (layers ! i))
              (fri_canonical_domain_at i)
              (length (fri_canonical_domain_at i))
              (2 ^ i)
              (fri_evidence_next_idx roots query_idxs round_idx i)"
  shows
    "fri_canonical_layer_close d
        (fri_robust_conditioned_layers m layers)
        (fri_linear_radius m K) 0 \<or>
      challenges \<in> generic_fri_bad_challenge_lists m
        (fri_robust_conditioned_bad_challenges d m K committed) \<or>
      (\<exists>i<m.
        \<not> fri_canonical_layer_close d
          (fri_robust_conditioned_layers m layers)
          (fri_linear_radius m K) i \<and>
        fri_canonical_layer_close d
          (fri_robust_conditioned_layers m layers)
          (fri_linear_radius m K) (Suc i) \<and>
        query_idxs \<in>
          fri_robust_conditioned_residual_query_lists
            roots challenges layers i \<and>
        card (fri_robust_conditioned_agreement_indices
          challenges layers i) \<le>
          length (fri_canonical_domain_at (Suc i)) -
            fri_linear_margin K i)"
proof -
  let ?conditioned = "fri_robust_conditioned_layers m layers"
  have terminal_close:
      "fri_canonical_layer_close d ?conditioned
        (fri_linear_radius m K) m"
    by (rule fri_robust_conditioned_terminal_close[OF final_low])
  have layer_length:
      "\<And>i. i \<le> m \<Longrightarrow>
        length (?conditioned ! i) =
          length (fri_canonical_domain_at i)"
    by (rule length_fri_robust_conditioned_layers_nth[OF _ layer_cover])
  have split:
      "fri_canonical_layer_close d ?conditioned
          (fri_linear_radius m K) 0 \<or>
        (\<exists>i<m.
          \<not> fri_canonical_layer_close d ?conditioned
              (fri_linear_radius m K) i \<and>
          fri_canonical_layer_close d ?conditioned
              (fri_linear_radius m K) (Suc i) \<and>
          ((challenges ! i \<in>
              fri_canonical_layer_good_challenges d ?conditioned
                (fri_linear_good_radius m K) i \<and>
            card (fri_canonical_layer_good_challenges d ?conditioned
                (fri_linear_good_radius m K) i) \<le>
              2 * fri_linear_good_radius m K i + 3) \<or>
           card (fri_canonical_transition_agreement_indices
                challenges ?conditioned i) \<le>
              length (fri_canonical_domain_at (Suc i)) -
                fri_linear_margin K i))"
    by (rule fri_canonical_multiround_linear_decode_or_reject[
          OF eval_power rounds_eq exponent_fit capacity initial_rate
            layer_length terminal_close])
from split show ?thesis
  proof
    assume initial:
      "fri_canonical_layer_close d ?conditioned
        (fri_linear_radius m K) 0"
    show ?thesis
      by (rule disjI1[OF initial])
  next
    assume transitions:
      "\<exists>i<m.
        \<not> fri_canonical_layer_close d ?conditioned
            (fri_linear_radius m K) i \<and>
        fri_canonical_layer_close d ?conditioned
            (fri_linear_radius m K) (Suc i) \<and>
        ((challenges ! i \<in>
            fri_canonical_layer_good_challenges d ?conditioned
              (fri_linear_good_radius m K) i \<and>
          card (fri_canonical_layer_good_challenges d ?conditioned
              (fri_linear_good_radius m K) i) \<le>
            2 * fri_linear_good_radius m K i + 3) \<or>
         card (fri_canonical_transition_agreement_indices
              challenges ?conditioned i) \<le>
            length (fri_canonical_domain_at (Suc i)) -
              fri_linear_margin K i)"
    then obtain i where i_bound: "i < m"
      and current_far:
        "\<not> fri_canonical_layer_close d ?conditioned
          (fri_linear_radius m K) i"
      and next_close:
        "fri_canonical_layer_close d ?conditioned
          (fri_linear_radius m K) (Suc i)"
      and alternative:
        "(challenges ! i \<in>
            fri_canonical_layer_good_challenges d ?conditioned
              (fri_linear_good_radius m K) i \<and>
          card (fri_canonical_layer_good_challenges d ?conditioned
              (fri_linear_good_radius m K) i) \<le>
            2 * fri_linear_good_radius m K i + 3) \<or>
         card (fri_canonical_transition_agreement_indices
              challenges ?conditioned i) \<le>
            length (fri_canonical_domain_at (Suc i)) -
              fri_linear_margin K i"
      by blast
    from alternative show ?thesis
    proof
      assume good:
        "challenges ! i \<in>
            fri_canonical_layer_good_challenges d ?conditioned
              (fri_linear_good_radius m K) i \<and>
          card (fri_canonical_layer_good_challenges d ?conditioned
              (fri_linear_good_radius m K) i) \<le>
            2 * fri_linear_good_radius m K i + 3"
      have radius_exact:
          "2 * fri_linear_good_radius m K i =
            fri_linear_radius m K i"
        by (rule fri_linear_current_radius_exact[
              OF eval_power i_bound exponent_fit])
      have current_nth:
          "?conditioned ! i =
            fri_conditioned_layer_table i (layers ! i)"
        by (rule fri_robust_conditioned_layers_nth)
          (use i_bound in simp)
      have far_good:
          "\<not> fri_rs_distance_to_code
            (fri_degree_after i (fri_padded_degree_bound d))
            (fri_canonical_domain_at i)
            (nth (fri_conditioned_layer_table i (layers ! i))) \<le>
              2 * fri_linear_good_radius m K i"
        using current_far
        unfolding fri_canonical_layer_close_def current_nth radius_exact .
      have family_eq:
          "fri_robust_conditioned_bad_challenges d m K committed i
              (take i challenges) =
            fri_canonical_layer_good_challenges d ?conditioned
              (fri_linear_good_radius m K) i"
        by (rule fri_robust_conditioned_good_eq_canonical[
              where d=d and m=m and K=K and committed=committed
                and i=i and challenges=challenges and layers=layers,
              OF i_bound committed_path[OF i_bound] far_good])
      have challenge_bad:
          "challenges ! i \<in>
            fri_robust_conditioned_bad_challenges d m K committed i
              (take i challenges)"
        using good family_eq by blast
      have bad_list:
          "challenges \<in> generic_fri_bad_challenge_lists m
            (fri_robust_conditioned_bad_challenges d m K committed)"
        using challenge_space i_bound challenge_bad
        unfolding generic_fri_bad_challenge_lists_def
          fri_multiround_bad_challenge_lists_def
        by blast
      show ?thesis
        by (rule disjI2, rule disjI1, rule bad_list)
    next
      assume agreement:
          "card (fri_canonical_transition_agreement_indices
              challenges ?conditioned i) \<le>
            length (fri_canonical_domain_at (Suc i)) -
              fri_linear_margin K i"
      have i_lt_N: "i < N"
        using i_bound exponent_fit by linarith
      have successor_cover:
          "length (fri_canonical_domain_at (Suc i)) \<le>
            length (layers ! Suc i)"
        by (rule layer_cover) (use i_bound in simp)
      have agreement_all:
          "\<forall>round_idx < length query_idxs.
            fri_evidence_next_idx roots query_idxs round_idx i \<in>
              fri_robust_conditioned_agreement_indices
                challenges layers i"
      proof (intro allI impI)
        fix round_idx
        assume round_bound: "round_idx < length query_idxs"
        have sampled_i:
            "fri_evidence_next_idx roots query_idxs round_idx i <
                length (fri_canonical_domain_at i) div 2 \<and>
              fri_conditioned_layer_table (Suc i) (layers ! Suc i) !
                  fri_evidence_next_idx roots query_idxs round_idx i =
                fri_table_fold_value (challenges ! i)
                  (fri_conditioned_layer_table i (layers ! i))
                  (fri_canonical_domain_at i)
                  (length (fri_canonical_domain_at i))
                  (2 ^ i)
                  (fri_evidence_next_idx roots query_idxs round_idx i)"
          by (rule sampled[OF round_bound i_bound])
        have idx_bound:
            "fri_evidence_next_idx roots query_idxs round_idx i <
              length (fri_canonical_domain_at i) div 2"
          using sampled_i by blast
        have sampled_value:
            "fri_conditioned_layer_table (Suc i) (layers ! Suc i) !
                fri_evidence_next_idx roots query_idxs round_idx i =
              fri_table_fold_value (challenges ! i)
                (fri_conditioned_layer_table i (layers ! i))
                (fri_canonical_domain_at i)
                (length (fri_canonical_domain_at i))
                (2 ^ i)
                (fri_evidence_next_idx roots query_idxs round_idx i)"
          using sampled_i by blast
        show
            "fri_evidence_next_idx roots query_idxs round_idx i \<in>
              fri_robust_conditioned_agreement_indices
                challenges layers i"
          by (rule sampled_fold_imp_robust_conditioned_agreement[
                OF eval_power i_lt_N successor_cover
                  idx_bound sampled_value])
      qed
      have residual:
          "query_idxs \<in>
            fri_robust_conditioned_residual_query_lists
              roots challenges layers i"
        using agreement_all
        unfolding fri_robust_conditioned_residual_query_lists_def
        by simp
      have agreement_bound:
          "card (fri_robust_conditioned_agreement_indices
              challenges layers i) \<le>
            length (fri_canonical_domain_at (Suc i)) -
              fri_linear_margin K i"
        using agreement
          fri_robust_conditioned_agreement_eq_canonical[
            OF i_bound, of challenges layers]
        by simp
      show ?thesis
        by (rule disjI2, rule disjI2, rule exI[where x=i])
          (use i_bound current_far next_close residual agreement_bound in blast)
    qed
  qed
qed

lemma authenticated_recorded_chain_robust_decode_or_reject:
  fixes d N K :: nat
  assumes chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count:
      "length challenges = ceil_log (Suc d)"
    and exponent_fit: "length challenges + K \<le> N"
    and capacity:
      "16 * Suc (length challenges) \<le> 2 ^ K"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
    and prefix_ext:
      "\<And>j. j < length challenges \<Longrightarrow>
        prefix_state j \<le> final_state"
    and prefix_clean:
      "\<And>j. j < length challenges \<Longrightarrow>
        \<not> hash_map_output_collision (prefix_state j)"
    and no_prefix_target:
      "\<And>j. j < length challenges \<Longrightarrow>
        \<not> hash_map_new_output_hit
          (merkle_prefix_path_targets {roots ! j} (prefix_state j))
          (prefix_state j) final_state"
    and recorded_authenticated:
      "\<And>round_idx j.
        round_idx < length query_idxs \<Longrightarrow>
        j < length challenges \<Longrightarrow>
        generic_fri_recorded_layer_chunk_authenticated roots query_idxs
          round_layers final_state round_idx j"
    and layer_at:
      "\<And>j. j < length challenges \<Longrightarrow>
        layers ! j =
          conceptual_table (prefix_state j) (roots ! j)
            (length (fri_canonical_domain_at j))"
    and final_layer:
      "layers ! length challenges =
        replicate (length (fri_canonical_domain_at (length challenges)))
          final_value"
    and committed_path:
      "\<And>j. j < length challenges \<Longrightarrow>
        committed j (take j challenges) = layers ! j"
  shows
    "fri_canonical_layer_close d
        (fri_robust_conditioned_layers (length challenges) layers)
        (fri_linear_radius (length challenges) K) 0 \<or>
      challenges \<in> generic_fri_bad_challenge_lists
        (length challenges)
        (fri_robust_conditioned_bad_challenges
          d (length challenges) K committed) \<or>
      (\<exists>i<length challenges.
        \<not> fri_canonical_layer_close d
          (fri_robust_conditioned_layers (length challenges) layers)
          (fri_linear_radius (length challenges) K) i \<and>
        fri_canonical_layer_close d
          (fri_robust_conditioned_layers (length challenges) layers)
          (fri_linear_radius (length challenges) K) (Suc i) \<and>
        query_idxs \<in>
          fri_robust_conditioned_residual_query_lists
            roots challenges layers i \<and>
        card (fri_robust_conditioned_agreement_indices
          challenges layers i) \<le>
          length (fri_canonical_domain_at (Suc i)) -
            fri_linear_margin K i)"
proof -
  have challenges_len: "length challenges = length roots"
    using chain
    unfolding generic_fri_recorded_value_chain_evidence_def by simp
  have challenge_space:
      "challenges \<in> fri_challenge_space (length challenges)"
    unfolding fri_challenge_space_def by simp
  have rounds_le: "ceil_log (Suc d) \<le> N"
    using round_count exponent_fit by linarith
  have layer_cover:
      "\<And>j. j \<le> length challenges \<Longrightarrow>
        length (fri_canonical_domain_at j) \<le> length (layers ! j)"
  proof -
    fix j
    assume j_bound: "j \<le> length challenges"
    show
      "length (fri_canonical_domain_at j) \<le> length (layers ! j)"
    proof (cases "j < length challenges")
      case True
      then show ?thesis
        unfolding layer_at[OF True] by simp
    next
      case False
      then have j_eq: "j = length challenges"
        using j_bound by simp
      show ?thesis
        unfolding j_eq final_layer by simp
    qed
  qed
  have final_consistent:
      "fri_final_constant_consistent
        (fri_conditioned_layer_table (length challenges)
          (layers ! length challenges)) final_value"
    unfolding final_layer fri_conditioned_layer_table_def
      fri_final_constant_consistent_def
    by simp
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
        OF final_consistent final_len])
  have sampled:
      "\<And>round_idx i.
        round_idx < length query_idxs \<Longrightarrow>
        i < length challenges \<Longrightarrow>
        fri_evidence_next_idx roots query_idxs round_idx i <
          length (fri_canonical_domain_at i) div 2 \<and>
        fri_conditioned_layer_table (Suc i) (layers ! Suc i) !
            fri_evidence_next_idx roots query_idxs round_idx i =
          fri_table_fold_value (challenges ! i)
            (fri_conditioned_layer_table i (layers ! i))
            (fri_canonical_domain_at i)
            (length (fri_canonical_domain_at i))
            (2 ^ i)
            (fri_evidence_next_idx roots query_idxs round_idx i)"
  proof -
    fix round_idx i
    assume round_bound: "round_idx < length query_idxs"
      and i_bound: "i < length challenges"
    show
      "fri_evidence_next_idx roots query_idxs round_idx i <
          length (fri_canonical_domain_at i) div 2 \<and>
        fri_conditioned_layer_table (Suc i) (layers ! Suc i) !
            fri_evidence_next_idx roots query_idxs round_idx i =
          fri_table_fold_value (challenges ! i)
            (fri_conditioned_layer_table i (layers ! i))
            (fri_canonical_domain_at i)
            (length (fri_canonical_domain_at i))
            (2 ^ i)
            (fri_evidence_next_idx roots query_idxs round_idx i)"
      apply (rule recorded_chain_conceptual_sample[
          OF chain eval_power _ round_bound i_bound])
           apply (use round_count rounds_le in simp)
          apply (rule prefix_ext)
          apply assumption
         apply (rule prefix_clean)
         apply assumption
        apply (rule no_prefix_target)
        apply assumption
       apply (rule recorded_authenticated[OF round_bound])
       apply assumption
      apply (rule layer_at)
      apply assumption
     by (rule final_layer)
  qed
  show ?thesis
    by (rule conceptual_sampled_chain_robust_decode_or_reject[
          where N=N and d=d and m="length challenges" and K=K
            and committed=committed,
          OF challenge_space refl round_count eval_power exponent_fit capacity
            initial_rate layer_cover committed_path final_low sampled])
qed

definition fri_online_robust_bad_challenges ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    'f protocol_channel \<Rightarrow> 'f \<Rightarrow> 'f set"
where
  "fri_online_robust_bad_challenges d m K i state fri_root =
    fri_robust_conditioned_bad_challenges d m K
      (\<lambda>_ _. conceptual_table state fri_root
        (length (fri_canonical_domain_at i))) i []"

lemma card_fri_online_robust_bad_challenges:
  fixes d N m K i :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and exponent_fit: "m + K \<le> N"
    and capacity: "16 * Suc m \<le> 2 ^ K"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
    and i_bound: "i < m"
  shows
    "card (fri_online_robust_bad_challenges
      d m K i state fri_root) \<le>
        2 * fri_linear_good_radius m K i + 3"
  unfolding fri_online_robust_bad_challenges_def
  by (rule fri_robust_conditioned_bad_challenges_card[
        OF eval_power rounds_eq exponent_fit capacity initial_rate i_bound])

lemma fri_builder_robust_bad_challenge_cover_imp_online_bad:
  assumes cover:
      "challenges \<in>
        generic_fri_bad_challenge_lists (length challenges)
          (fri_robust_conditioned_bad_challenges d
            (length challenges) K
            (\<lambda>j _. fri_builder_conceptual_layers roots builder_state
              final_value ! j))"
    and lengths: "length challenges = length roots"
  shows
    "\<exists>j < length challenges.
      challenges ! j \<in>
        fri_online_robust_bad_challenges d (length challenges) K j
          builder_state (roots ! j)"
proof -
  have multiround:
      "challenges \<in>
        fri_multiround_bad_challenge_lists (length challenges)
          (fri_robust_conditioned_bad_challenges d
            (length challenges) K
            (\<lambda>j _. fri_builder_conceptual_layers roots builder_state
              final_value ! j))"
    using cover unfolding generic_fri_bad_challenge_lists_def .
  from multiround obtain j where j_bound: "j < length challenges"
    and bad:
      "challenges ! j \<in>
        fri_robust_conditioned_bad_challenges d
          (length challenges) K
          (\<lambda>j _. fri_builder_conceptual_layers roots builder_state
            final_value ! j)
          j (take j challenges)"
    unfolding fri_multiround_bad_challenge_lists_def by blast
  have root_bound: "j < length roots"
    using j_bound lengths by simp
  have layer_at:
      "fri_builder_conceptual_layers roots builder_state final_value ! j =
        conceptual_table builder_state (roots ! j)
          (length (fri_canonical_domain_at j))"
    by (rule fri_builder_conceptual_layers_at[OF root_bound])
  have online:
      "challenges ! j \<in>
        fri_online_robust_bad_challenges d (length challenges) K j
          builder_state (roots ! j)"
    using bad
    unfolding fri_online_robust_bad_challenges_def
      fri_robust_conditioned_bad_challenges_def Let_def
    by (simp only: layer_at)
  show ?thesis
    using j_bound online by blast
qed


lemma fri_builder_authenticated_chain_robust_online_or_residual:
  fixes d N K :: nat
  assumes chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and exponent_fit: "length challenges + K \<le> N"
    and capacity:
      "16 * Suc (length challenges) \<le> 2 ^ K"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
    and builder_ext: "builder_state \<le> final_state"
    and builder_clean: "\<not> hash_map_output_collision builder_state"
    and no_builder_target:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets (set roots) builder_state)
        builder_state final_state"
    and authenticated:
      "generic_fri_recorded_chunks_authenticated roots query_idxs
        round_layers final_state"
  shows
    "fri_canonical_layer_close d
        (fri_robust_conditioned_layers (length challenges)
          (fri_builder_conceptual_layers roots builder_state final_value))
        (fri_linear_radius (length challenges) K) 0 \<or>
      (\<exists>j < length challenges.
        challenges ! j \<in>
          fri_online_robust_bad_challenges d (length challenges) K j
            builder_state (roots ! j)) \<or>
      (\<exists>i < length challenges.
        \<not> fri_canonical_layer_close d
          (fri_robust_conditioned_layers (length challenges)
            (fri_builder_conceptual_layers roots builder_state final_value))
          (fri_linear_radius (length challenges) K) i \<and>
        fri_canonical_layer_close d
          (fri_robust_conditioned_layers (length challenges)
            (fri_builder_conceptual_layers roots builder_state final_value))
          (fri_linear_radius (length challenges) K) (Suc i) \<and>
        query_idxs \<in>
          fri_robust_conditioned_residual_query_lists roots challenges
            (fri_builder_conceptual_layers roots builder_state final_value) i \<and>
        card (fri_robust_conditioned_agreement_indices challenges
          (fri_builder_conceptual_layers roots builder_state final_value) i)
          \<le> length (fri_canonical_domain_at (Suc i)) -
            fri_linear_margin K i)"
proof -
  let ?layers =
    "fri_builder_conceptual_layers roots builder_state final_value"
  have lengths: "length challenges = length roots"
    using chain
    unfolding generic_fri_recorded_value_chain_evidence_def
    by simp
  have no_singleton:
      "\<And>j. j < length challenges \<Longrightarrow>
        \<not> hash_map_new_output_hit
          (merkle_prefix_path_targets {roots ! j} builder_state)
          builder_state final_state"
  proof -
    fix j
    assume j_bound: "j < length challenges"
    have root_bound: "j < length roots"
      using j_bound lengths by simp
    have root_mem: "roots ! j \<in> set roots"
      by (rule nth_mem[OF root_bound])
    have target_subset:
        "merkle_prefix_path_targets {roots ! j} builder_state \<subseteq>
          merkle_prefix_path_targets (set roots) builder_state"
      by (rule merkle_prefix_path_targets_mono) (use root_mem in auto)
    show
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {roots ! j} builder_state)
        builder_state final_state"
    proof
      assume hit:
          "hash_map_new_output_hit
            (merkle_prefix_path_targets {roots ! j} builder_state)
            builder_state final_state"
      have "hash_map_new_output_hit
          (merkle_prefix_path_targets (set roots) builder_state)
          builder_state final_state"
        by (rule hash_map_new_output_hit_subset[OF target_subset hit])
      then show False
        using no_builder_target by contradiction
    qed
  qed
  have recorded_authenticated:
      "\<And>round_idx j.
        round_idx < length query_idxs \<Longrightarrow>
        j < length challenges \<Longrightarrow>
        generic_fri_recorded_layer_chunk_authenticated roots query_idxs
          round_layers final_state round_idx j"
  proof -
    fix round_idx j
    assume round_bound: "round_idx < length query_idxs"
      and layer_bound: "j < length challenges"
    have root_bound: "j < length roots"
      using layer_bound lengths by simp
    have authenticated_chunk:
        "fri_layer_chunk_authenticated
          (roots ! j)
          (fri_evidence_layer_len roots j)
          (fri_evidence_layer_idx roots query_idxs round_idx j)
          (round_layers ! round_idx ! j) final_state"
      using authenticated round_bound root_bound
      unfolding generic_fri_recorded_chunks_authenticated_def
      by auto
    then show
        "generic_fri_recorded_layer_chunk_authenticated roots query_idxs
          round_layers final_state round_idx j"
      unfolding generic_fri_recorded_layer_chunk_authenticated_def .
  qed
  have layer_at:
      "\<And>j. j < length challenges \<Longrightarrow>
        ?layers ! j =
          conceptual_table builder_state (roots ! j)
            (length (fri_canonical_domain_at j))"
    using lengths by (simp add: fri_builder_conceptual_layers_at)
  have final_layer:
      "?layers ! length challenges =
        replicate
          (length (fri_canonical_domain_at (length challenges)))
          final_value"
    using lengths fri_builder_conceptual_layers_final[
      of roots builder_state final_value]
    by simp
  have split:
      "fri_canonical_layer_close d
          (fri_robust_conditioned_layers (length challenges) ?layers)
          (fri_linear_radius (length challenges) K) 0 \<or>
        challenges \<in> generic_fri_bad_challenge_lists
          (length challenges)
          (fri_robust_conditioned_bad_challenges d
            (length challenges) K (\<lambda>j _. ?layers ! j)) \<or>
        (\<exists>i<length challenges.
          \<not> fri_canonical_layer_close d
            (fri_robust_conditioned_layers (length challenges) ?layers)
            (fri_linear_radius (length challenges) K) i \<and>
          fri_canonical_layer_close d
            (fri_robust_conditioned_layers (length challenges) ?layers)
            (fri_linear_radius (length challenges) K) (Suc i) \<and>
          query_idxs \<in>
            fri_robust_conditioned_residual_query_lists
              roots challenges ?layers i \<and>
          card (fri_robust_conditioned_agreement_indices
            challenges ?layers i) \<le>
            length (fri_canonical_domain_at (Suc i)) -
              fri_linear_margin K i)"
    by (rule authenticated_recorded_chain_robust_decode_or_reject[
          where prefix_state="\<lambda>_. builder_state" and layers="?layers"
            and committed="\<lambda>j _. ?layers ! j",
          OF chain eval_power round_count exponent_fit capacity initial_rate])
      (use builder_ext builder_clean no_singleton recorded_authenticated
        layer_at final_layer in auto)
  from split show ?thesis
  proof
    assume initial:
        "fri_canonical_layer_close d
          (fri_robust_conditioned_layers (length challenges) ?layers)
          (fri_linear_radius (length challenges) K) 0"
    then show ?thesis by simp
  next
    assume remainder:
        "challenges \<in> generic_fri_bad_challenge_lists
            (length challenges)
            (fri_robust_conditioned_bad_challenges d
              (length challenges) K (\<lambda>j _. ?layers ! j)) \<or>
          (\<exists>i<length challenges.
            \<not> fri_canonical_layer_close d
              (fri_robust_conditioned_layers (length challenges) ?layers)
              (fri_linear_radius (length challenges) K) i \<and>
            fri_canonical_layer_close d
              (fri_robust_conditioned_layers (length challenges) ?layers)
              (fri_linear_radius (length challenges) K) (Suc i) \<and>
            query_idxs \<in>
              fri_robust_conditioned_residual_query_lists
                roots challenges ?layers i \<and>
            card (fri_robust_conditioned_agreement_indices
              challenges ?layers i) \<le>
              length (fri_canonical_domain_at (Suc i)) -
                fri_linear_margin K i)"
    from remainder show ?thesis
    proof
      assume cover:
          "challenges \<in> generic_fri_bad_challenge_lists
            (length challenges)
            (fri_robust_conditioned_bad_challenges d
              (length challenges) K (\<lambda>j _. ?layers ! j))"
      have online:
          "\<exists>j < length challenges.
            challenges ! j \<in>
              fri_online_robust_bad_challenges d (length challenges) K j
                builder_state (roots ! j)"
        by (rule fri_builder_robust_bad_challenge_cover_imp_online_bad[
              OF cover lengths])
      then show ?thesis by simp
    next
      assume residual:
          "\<exists>i<length challenges.
            \<not> fri_canonical_layer_close d
              (fri_robust_conditioned_layers (length challenges) ?layers)
              (fri_linear_radius (length challenges) K) i \<and>
            fri_canonical_layer_close d
              (fri_robust_conditioned_layers (length challenges) ?layers)
              (fri_linear_radius (length challenges) K) (Suc i) \<and>
            query_idxs \<in>
              fri_robust_conditioned_residual_query_lists
                roots challenges ?layers i \<and>
            card (fri_robust_conditioned_agreement_indices
              challenges ?layers i) \<le>
              length (fri_canonical_domain_at (Suc i)) -
                fri_linear_margin K i"
      then show ?thesis by simp
    qed
  qed
qed

lemma fri_robust_conditioned_agreement_indices_subset:
  assumes successor_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        length (layers ! Suc i)"
  shows
    "fri_robust_conditioned_agreement_indices challenges layers i
      \<subseteq> {..<length (fri_canonical_domain_at (Suc i))}"
  unfolding fri_robust_conditioned_agreement_indices_def
    fri_fold_next_agreement_indices_def code_agreement_indices_def
    length_fri_conditioned_layer_table[OF successor_cover]
  by auto

lemma fri_robust_conditioned_residual_restricted_subset:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and layer_bound: "i < length roots"
  shows
    "fri_robust_conditioned_residual_query_lists
        roots challenges layers i \<inter> fri_query_index_list_space
      \<subseteq>
      fri_conditioned_query_lists
        (fri_conditioned_query_indices roots i
          (fri_robust_conditioned_agreement_indices
            challenges layers i))"
proof
  fix qs
  assume qs:
      "qs \<in>
        fri_robust_conditioned_residual_query_lists
            roots challenges layers i \<inter>
          fri_query_index_list_space"
  then have qs_len: "length qs = rounds"
    and qs_space: "set qs \<subseteq> query_sample_space"
    unfolding fri_query_index_list_space_def by auto
  have entries:
      "set qs \<subseteq>
        fri_conditioned_query_indices roots i
          (fri_robust_conditioned_agreement_indices
            challenges layers i)"
  proof
    fix q
    assume q_in: "q \<in> set qs"
    then obtain round_idx where round_bound: "round_idx < length qs"
      and q_eq: "q = qs ! round_idx"
      by (metis in_set_conv_nth)
    have agreement:
        "fri_evidence_next_idx roots qs round_idx i \<in>
          fri_robust_conditioned_agreement_indices challenges layers i"
      using qs round_bound
      unfolding fri_robust_conditioned_residual_query_lists_def by auto
    have mod_agreement:
        "q mod length (fri_canonical_domain_at (Suc i)) \<in>
          fri_robust_conditioned_agreement_indices challenges layers i"
      using agreement
        fri_evidence_next_idx_at[
          OF eval_power roots_le layer_bound round_bound]
        q_eq
      by simp
    show
      "q \<in> fri_conditioned_query_indices roots i
        (fri_robust_conditioned_agreement_indices challenges layers i)"
      using qs_space q_in mod_agreement
      unfolding fri_conditioned_query_indices_def by auto
  qed
  show
      "qs \<in> fri_conditioned_query_lists
        (fri_conditioned_query_indices roots i
          (fri_robust_conditioned_agreement_indices
            challenges layers i))"
    unfolding fri_conditioned_query_lists_def
    using qs_len entries by simp
qed

lemma card_fri_robust_conditioned_residual_restricted:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and layer_bound: "i < length roots"
    and successor_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        length (layers ! Suc i)"
    and agreement_card:
      "card (fri_robust_conditioned_agreement_indices
        challenges layers i) \<le> A"
    and modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
  shows
    "card
      (fri_robust_conditioned_residual_query_lists
          roots challenges layers i \<inter> fri_query_index_list_space)
      \<le>
      (modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i))) A) ^ rounds"
proof -
  let ?S =
    "fri_robust_conditioned_agreement_indices challenges layers i"
  let ?I = "fri_conditioned_query_indices roots i ?S"
  have subset:
      "fri_robust_conditioned_residual_query_lists
          roots challenges layers i \<inter> fri_query_index_list_space
        \<subseteq> fri_conditioned_query_lists ?I"
    by (rule fri_robust_conditioned_residual_restricted_subset[
          OF eval_power roots_le layer_bound])
  have finite_lists: "finite (fri_conditioned_query_lists ?I)"
    unfolding fri_conditioned_query_lists_def
    by (rule finite_lists_length_eq)
      (rule finite_fri_conditioned_query_indices)
  have card_subset:
      "card
        (fri_robust_conditioned_residual_query_lists
            roots challenges layers i \<inter> fri_query_index_list_space)
        \<le> card (fri_conditioned_query_lists ?I)"
    by (rule card_mono[OF finite_lists subset])
  have indices_card:
      "card ?I \<le>
        modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i))) A"
    by (rule card_fri_conditioned_query_indices[
          OF modulus_pos
            fri_robust_conditioned_agreement_indices_subset[
              OF successor_cover]
            agreement_card])
  have lists_card:
      "card (fri_conditioned_query_lists ?I) = card ?I ^ rounds"
    by (rule card_fri_conditioned_query_lists)
      (rule finite_fri_conditioned_query_indices)
  have card_subset_power:
      "card
        (fri_robust_conditioned_residual_query_lists
            roots challenges layers i \<inter> fri_query_index_list_space)
        \<le> card ?I ^ rounds"
    using card_subset lists_card by simp
  have envelope_power:
      "card ?I ^ rounds \<le>
        (modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i))) A) ^ rounds"
    by (rule power_mono[OF indices_card]) simp
  show ?thesis
    by (rule order_trans[OF card_subset_power envelope_power])
qed

lemma card_fri_robust_linear_residual_restricted:
  fixes i N m K :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_len: "length roots = m"
    and exponent_fit: "m + K \<le> N"
    and layer_bound: "i < m"
    and successor_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        length (layers ! Suc i)"
    and agreement_card:
      "card (fri_robust_conditioned_agreement_indices
        challenges layers i) \<le>
        length (fri_canonical_domain_at (Suc i)) -
          fri_linear_margin K i"
  shows
    "card
      (fri_robust_conditioned_residual_query_lists
          roots challenges layers i \<inter> fri_query_index_list_space)
      \<le>
      (modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) -
          fri_linear_margin K i)) ^ rounds"
proof -
  have roots_le: "length roots \<le> N"
    using roots_len exponent_fit by linarith
  have layer_root: "i < length roots"
    using layer_bound roots_len by simp
  have suc_le_N: "Suc i \<le> N"
    using layer_bound exponent_fit by linarith
  have modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
    by (rule fri_canonical_domain_at_pos[OF eval_power suc_le_N])
  show ?thesis
    by (rule card_fri_robust_conditioned_residual_restricted[
          OF eval_power roots_le layer_root successor_cover
            agreement_card modulus_pos])
qed

end

end