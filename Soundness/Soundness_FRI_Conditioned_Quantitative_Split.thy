theory Soundness_FRI_Conditioned_Quantitative_Split
  imports
    Soundness_FRI_Conditioned_Builder_Split
    Soundness_FRI_Conditioned_Query_Fiber
begin

context soundness
begin

lemma first_true_transition:
  assumes start_false: "\<not> P 0"
    and end_true: "P n"
  shows "\<exists>i < n. \<not> P i \<and> P (Suc i)"
  using start_false end_true
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "P n")
    case True
    then obtain i where i_bound: "i < n"
      and i_false: "\<not> P i"
      and suc_true: "P (Suc i)"
      using Suc.IH Suc.prems by blast
    show ?thesis
      by (intro exI[of _ i] conjI)
        (use i_bound i_false suc_true in simp_all)
  next
    case False
    show ?thesis
      by (intro exI[of _ n] conjI)
        (use False Suc.prems in simp_all)
  qed
qed

lemma conceptual_sampled_chain_conditioned_quantitative_split:
  assumes challenge_space:
      "challenges \<in> fri_challenge_space (length challenges)"
    and round_count: "length challenges = ceil_log (Suc d)"
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
    and final_low:
      "fri_table_low_degree_on
        (fri_degree_after (length challenges) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (length challenges))
        (fri_conditioned_layer_table (length challenges)
          (layers ! length challenges))"
    and sampled:
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
  shows
    "challenges \<in> generic_fri_bad_challenge_lists
        (length challenges)
        (fri_conditioned_bad_challenges d committed) \<or>
      (\<exists>i < length challenges.
        challenges ! i \<notin>
          fri_conditioned_bad_challenges d committed i
            (take i challenges) \<and>
        \<not> fri_table_low_degree_on
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i)
          (fri_conditioned_layer_table i (layers ! i)) \<and>
        fri_table_low_degree_on
          (fri_degree_after (Suc i) (fri_padded_degree_bound d))
          (fri_canonical_domain_at (Suc i))
          (fri_conditioned_layer_table (Suc i) (layers ! Suc i)) \<and>
        query_idxs \<in>
          fri_conditioned_residual_query_lists roots challenges layers i)"
proof -
  let ?P =
    "\<lambda>i. fri_table_low_degree_on
      (fri_degree_after i (fri_padded_degree_bound d))
      (fri_canonical_domain_at i)
      (fri_conditioned_layer_table i (layers ! i))"
  have start_false: "\<not> ?P 0"
    using start_not_low by simp
  have end_true: "?P (length challenges)"
    by (rule final_low)
  have transition: "\<exists>i < length challenges. \<not> ?P i \<and> ?P (Suc i)"
    by (rule first_true_transition[OF start_false end_true])
  then obtain i where i_bound: "i < length challenges"
    and current_not_low: "\<not> ?P i"
    and next_low: "?P (Suc i)"
    by blast
  show ?thesis
  proof (cases
      "challenges ! i \<in>
        fri_conditioned_bad_challenges d committed i
          (take i challenges)")
    case True
    have bad:
        "challenges \<in> generic_fri_bad_challenge_lists
          (length challenges)
          (fri_conditioned_bad_challenges d committed)"
      using challenge_space i_bound True
      unfolding generic_fri_bad_challenge_lists_def
        fri_multiround_bad_challenge_lists_def
      by blast
    then show ?thesis by simp
  next
    case False
    have agreement_all:
        "\<forall>round_idx < length query_idxs.
          fri_evidence_next_idx roots query_idxs round_idx i \<in>
            fri_conditioned_agreement_indices i
              (layers ! i) (layers ! Suc i) (challenges ! i)"
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
      have split:
          "challenges ! i \<in>
              fri_conditioned_bad_challenges d committed i
                (take i challenges) \<or>
            fri_evidence_next_idx roots query_idxs round_idx i \<in>
              fri_conditioned_agreement_indices i
                (layers ! i) (layers ! Suc i) (challenges ! i)"
        by (rule conditioned_transition_challenge_or_agreement[
            where N=N and d=d and i=i
              and committed=committed
              and prefix="take i challenges"
              and idx="fri_evidence_next_idx roots query_idxs round_idx i"
              and b="challenges ! i",
            OF eval_power])
          (use round_count rounds_le layer_cover committed_path
            current_not_low next_low sampled_i i_bound in simp_all)
      show
          "fri_evidence_next_idx roots query_idxs round_idx i \<in>
            fri_conditioned_agreement_indices i
              (layers ! i) (layers ! Suc i) (challenges ! i)"
        using split False by blast
    qed
    have residual:
        "query_idxs \<in>
          fri_conditioned_residual_query_lists roots challenges layers i"
      using agreement_all
      unfolding fri_conditioned_residual_query_lists_def by simp
    show ?thesis
      using i_bound False current_not_low next_low residual by blast
  qed
qed


lemma authenticated_recorded_chain_conditioned_quantitative_split:
  assumes chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count:
      "length challenges = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and prefix_ext:
      "\<And>j. j < length challenges \<Longrightarrow> prefix_state j \<le> final_state"
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
    and start_not_low:
      "\<not> fri_table_low_degree_on (fri_padded_degree_bound d)
        (fri_canonical_domain_at 0)
        (fri_conditioned_layer_table 0 (layers ! 0))"
  shows
    "challenges \<in> generic_fri_bad_challenge_lists
        (length challenges)
        (fri_conditioned_bad_challenges d (\<lambda>j _. layers ! j)) \<or>
      (\<exists>i < length challenges.
        challenges ! i \<notin>
          fri_conditioned_bad_challenges d (\<lambda>j _. layers ! j) i
            (take i challenges) \<and>
        \<not> fri_table_low_degree_on
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i)
          (fri_conditioned_layer_table i (layers ! i)) \<and>
        fri_table_low_degree_on
          (fri_degree_after (Suc i) (fri_padded_degree_bound d))
          (fri_canonical_domain_at (Suc i))
          (fri_conditioned_layer_table (Suc i) (layers ! Suc i)) \<and>
        query_idxs \<in>
          fri_conditioned_residual_query_lists roots challenges layers i)"
proof -
  have challenges_len: "length challenges = length roots"
    using chain
    unfolding generic_fri_recorded_value_chain_evidence_def by simp
  have challenge_space:
      "challenges \<in> fri_challenge_space (length challenges)"
    unfolding fri_challenge_space_def by simp
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
    apply (rule conceptual_sampled_chain_conditioned_quantitative_split[
        where N=N and d=d and committed="\<lambda>j _. layers ! j",
        OF challenge_space round_count eval_power rounds_le layer_cover _
          start_not_low final_low sampled])
    by simp_all
qed


lemma fri_builder_authenticated_chain_online_or_quantitative_residual:
  assumes chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and builder_ext: "builder_state \<le> final_state"
    and builder_clean: "\<not> hash_map_output_collision builder_state"
    and no_builder_target:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets (set roots) builder_state)
        builder_state final_state"
    and authenticated:
      "generic_fri_recorded_chunks_authenticated roots query_idxs
        round_layers final_state"
    and start_not_low:
      "\<not> fri_table_low_degree_on (fri_padded_degree_bound d)
        (fri_canonical_domain_at 0)
        (fri_conditioned_layer_table 0
          (fri_builder_conceptual_layers roots builder_state final_value ! 0))"
  shows
    "(\<exists>j < length challenges.
        challenges ! j \<in>
          fri_online_bad_challenges d j builder_state (roots ! j)) \<or>
      (\<exists>i < length challenges.
        challenges ! i \<notin>
          fri_conditioned_bad_challenges d
            (\<lambda>j _. fri_builder_conceptual_layers roots builder_state
              final_value ! j)
            i (take i challenges) \<and>
        \<not> fri_table_low_degree_on
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i)
          (fri_conditioned_layer_table i
            (fri_builder_conceptual_layers roots builder_state
              final_value ! i)) \<and>
        fri_table_low_degree_on
          (fri_degree_after (Suc i) (fri_padded_degree_bound d))
          (fri_canonical_domain_at (Suc i))
          (fri_conditioned_layer_table (Suc i)
            (fri_builder_conceptual_layers roots builder_state
              final_value ! Suc i)) \<and>
        query_idxs \<in>
          fri_conditioned_residual_query_lists roots challenges
            (fri_builder_conceptual_layers roots builder_state final_value) i)"
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
      by (rule merkle_prefix_path_targets_mono)
        (use root_mem in auto)
    show
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {roots ! j} builder_state)
        builder_state final_state"
    proof
      assume hit:
          "hash_map_new_output_hit
            (merkle_prefix_path_targets {roots ! j} builder_state)
            builder_state final_state"
      have
          "hash_map_new_output_hit
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
    using lengths
      fri_builder_conceptual_layers_final[
        of roots builder_state final_value]
    by simp
  have split:
      "challenges \<in>
          generic_fri_bad_challenge_lists (length challenges)
            (fri_conditioned_bad_challenges d (\<lambda>j _. ?layers ! j)) \<or>
        (\<exists>i < length challenges.
          challenges ! i \<notin>
            fri_conditioned_bad_challenges d (\<lambda>j _. ?layers ! j) i
              (take i challenges) \<and>
          \<not> fri_table_low_degree_on
            (fri_degree_after i (fri_padded_degree_bound d))
            (fri_canonical_domain_at i)
            (fri_conditioned_layer_table i (?layers ! i)) \<and>
          fri_table_low_degree_on
            (fri_degree_after (Suc i) (fri_padded_degree_bound d))
            (fri_canonical_domain_at (Suc i))
            (fri_conditioned_layer_table (Suc i) (?layers ! Suc i)) \<and>
          query_idxs \<in>
            fri_conditioned_residual_query_lists roots challenges ?layers i)"
    by (rule authenticated_recorded_chain_conditioned_quantitative_split[
        where prefix_state="\<lambda>_. builder_state" and layers="?layers",
        OF chain eval_power round_count rounds_le])
      (use builder_ext builder_clean no_singleton recorded_authenticated
        layer_at final_layer start_not_low in auto)
  from split show ?thesis
  proof
    assume cover:
        "challenges \<in>
          generic_fri_bad_challenge_lists (length challenges)
            (fri_conditioned_bad_challenges d (\<lambda>j _. ?layers ! j))"
    have online:
        "\<exists>j < length challenges.
          challenges ! j \<in>
            fri_online_bad_challenges d j builder_state (roots ! j)"
      by (rule fri_builder_bad_challenge_cover_imp_online_bad[
        OF cover lengths])
    then show ?thesis by simp
  next
    assume residual:
        "\<exists>i < length challenges.
          challenges ! i \<notin>
            fri_conditioned_bad_challenges d (\<lambda>j _. ?layers ! j) i
              (take i challenges) \<and>
          \<not> fri_table_low_degree_on
            (fri_degree_after i (fri_padded_degree_bound d))
            (fri_canonical_domain_at i)
            (fri_conditioned_layer_table i (?layers ! i)) \<and>
          fri_table_low_degree_on
            (fri_degree_after (Suc i) (fri_padded_degree_bound d))
            (fri_canonical_domain_at (Suc i))
            (fri_conditioned_layer_table (Suc i) (?layers ! Suc i)) \<and>
          query_idxs \<in>
            fri_conditioned_residual_query_lists roots challenges ?layers i"
    then show ?thesis by simp
  qed
qed

end

end
