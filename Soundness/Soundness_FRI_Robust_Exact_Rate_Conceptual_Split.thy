theory Soundness_FRI_Robust_Exact_Rate_Conceptual_Split
  imports
    Soundness_FRI_Robust_Conceptual_Split
    Soundness_FRI_Robust_Exact_Rate_Multiround
begin

context soundness
begin

lemma fri_robust_conditioned_bad_challenges_card_exact_two:
  fixes d N m K i :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and exponent_fit: "m + K \<le> N"
    and K_pos: "0 < K"
    and exact: "fri_linear_exact_list_cap d m K 2"
    and i_bound: "i < m"
  shows
    "card (fri_robust_conditioned_bad_challenges
      d m K committed i prefix) \<le>
        2 * fri_linear_good_radius m K i + 3"
proof -
  let ?current = "fri_conditioned_layer_table i (committed i prefix)"
  let ?t = "fri_linear_good_radius m K i"
  have split:
      "fri_rs_distance_to_code
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i) (nth ?current) \<le> 2 * ?t \<or>
        card (fri_fold_good_challenges
          (fri_degree_after (Suc i) (fri_padded_degree_bound d))
          (fri_canonical_domain_at (Suc i))
          (length (fri_canonical_domain_at i))
          (fri_canonical_domain_at i) ?current ?t) \<le> 2 * ?t + 3"
    by (rule fri_canonical_one_round_decode_or_reject_at_exact_two[
          OF eval_power rounds_eq exponent_fit K_pos i_bound exact])
  show ?thesis
    using split
    unfolding fri_robust_conditioned_bad_challenges_def Let_def
    by (auto split: if_splits)
qed



lemma conceptual_sampled_chain_robust_decode_or_reject_exact_two:
  fixes d N m K :: nat
  assumes challenge_space:
      "challenges \<in> fri_challenge_space m"
    and challenges_len: "length challenges = m"
    and rounds_eq: "m = ceil_log (Suc d)"
    and eval_power: "clength * scale = 2 ^ N"
    and exponent_fit: "m + K \<le> N"
    and K_pos: "0 < K"
    and exact: "fri_linear_exact_list_cap d m K 2"
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
    by (rule fri_canonical_multiround_linear_decode_or_reject_exact_two[
          OF eval_power rounds_eq exponent_fit K_pos exact
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



lemma authenticated_recorded_chain_robust_decode_or_reject_exact_two:
  fixes d N K :: nat
  assumes chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count:
      "length challenges = ceil_log (Suc d)"
    and exponent_fit: "length challenges + K \<le> N"
    and K_pos: "0 < K"
    and exact:
      "fri_linear_exact_list_cap d (length challenges) K 2"
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
    by (rule conceptual_sampled_chain_robust_decode_or_reject_exact_two[
          where N=N and d=d and m="length challenges" and K=K
            and committed=committed,
          OF challenge_space refl round_count eval_power exponent_fit K_pos
            exact layer_cover committed_path final_low sampled])
qed



lemma card_fri_online_robust_bad_challenges_exact_two:
  fixes d N m K i :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and exponent_fit: "m + K \<le> N"
    and K_pos: "0 < K"
    and exact: "fri_linear_exact_list_cap d m K 2"
    and i_bound: "i < m"
  shows
    "card (fri_online_robust_bad_challenges
      d m K i state fri_root) \<le>
        2 * fri_linear_good_radius m K i + 3"
  unfolding fri_online_robust_bad_challenges_def
  by (rule fri_robust_conditioned_bad_challenges_card_exact_two[
        OF eval_power rounds_eq exponent_fit K_pos exact i_bound])



lemma fri_builder_authenticated_chain_robust_online_or_residual_exact_two:
  fixes d N K :: nat
  assumes chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and exponent_fit: "length challenges + K \<le> N"
    and K_pos: "0 < K"
    and exact:
      "fri_linear_exact_list_cap d (length challenges) K 2"
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
    by (rule authenticated_recorded_chain_robust_decode_or_reject_exact_two[
          where prefix_state="\<lambda>_. builder_state" and layers="?layers"
            and committed="\<lambda>j _. ?layers ! j",
          OF chain eval_power round_count exponent_fit K_pos exact])
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

end
end
