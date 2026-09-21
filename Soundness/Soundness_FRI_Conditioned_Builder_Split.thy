theory Soundness_FRI_Conditioned_Builder_Split
  imports Soundness_FRI_Conditioned_Security_Target_Bound
begin

context soundness
begin

definition fri_builder_conceptual_layers
  :: "'f list \<Rightarrow> 'f protocol_channel \<Rightarrow> 'f \<Rightarrow> 'f list list"
where
  "fri_builder_conceptual_layers roots builder_state final_value =
    map
      (\<lambda>j. conceptual_table builder_state (roots ! j)
        (length (fri_canonical_domain_at j)))
      [0..<length roots] @
    [replicate
      (length (fri_canonical_domain_at (length roots))) final_value]"

lemma length_fri_builder_conceptual_layers[simp]:
  "length (fri_builder_conceptual_layers roots builder_state final_value) =
    Suc (length roots)"
  unfolding fri_builder_conceptual_layers_def by simp

lemma fri_builder_conceptual_layers_at:
  assumes j_bound: "j < length roots"
  shows
    "fri_builder_conceptual_layers roots builder_state final_value ! j =
      conceptual_table builder_state (roots ! j)
        (length (fri_canonical_domain_at j))"
  unfolding fri_builder_conceptual_layers_def
  by (simp add: nth_append j_bound)

lemma fri_builder_conceptual_layers_final:
  "fri_builder_conceptual_layers roots builder_state final_value !
      length roots =
    replicate (length (fri_canonical_domain_at (length roots)))
      final_value"
  unfolding fri_builder_conceptual_layers_def
  by (simp add: nth_append)

lemma fri_builder_bad_challenge_cover_imp_online_bad:
  assumes cover:
      "challenges \<in>
        generic_fri_bad_challenge_lists (length challenges)
          (fri_conditioned_bad_challenges d
            (\<lambda>j _. fri_builder_conceptual_layers roots builder_state
              final_value ! j))"
    and lengths: "length challenges = length roots"
  shows
    "\<exists>j < length challenges.
      challenges ! j \<in>
        fri_online_bad_challenges d j builder_state (roots ! j)"
proof -
  have multiround:
      "challenges \<in>
        fri_multiround_bad_challenge_lists (length challenges)
          (fri_conditioned_bad_challenges d
            (\<lambda>j _. fri_builder_conceptual_layers roots builder_state
              final_value ! j))"
    using cover unfolding generic_fri_bad_challenge_lists_def .
  from multiround obtain j where
    j_bound: "j < length challenges"
    and bad:
      "challenges ! j \<in>
        fri_conditioned_bad_challenges d
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
  have bad':
      "challenges ! j \<in>
        fri_conditioned_bad_challenges d
          (\<lambda>_ _. conceptual_table builder_state (roots ! j)
            (length (fri_canonical_domain_at j))) j []"
    using bad
    unfolding fri_conditioned_bad_challenges_def Let_def
    by (simp only: layer_at)
  have online:
      "challenges ! j \<in>
        fri_online_bad_challenges d j builder_state (roots ! j)"
    unfolding fri_online_bad_challenges_def fri_online_conceptual_layer_def
    using bad' by simp
  show ?thesis
    using j_bound online by blast
qed

lemma fri_builder_authenticated_chain_online_or_residual:
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
        query_idxs \<in>
          fri_conditioned_residual_query_lists roots challenges
            (fri_builder_conceptual_layers roots builder_state final_value) i)"
proof -
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
        fri_builder_conceptual_layers roots builder_state final_value ! j =
          conceptual_table builder_state (roots ! j)
            (length (fri_canonical_domain_at j))"
    using lengths by (simp add: fri_builder_conceptual_layers_at)
  have final_layer:
      "fri_builder_conceptual_layers roots builder_state final_value !
          length challenges =
        replicate
          (length (fri_canonical_domain_at (length challenges)))
          final_value"
    using lengths fri_builder_conceptual_layers_final[of roots builder_state
      final_value]
    by simp
  have split:
      "challenges \<in>
          generic_fri_bad_challenge_lists (length challenges)
            (fri_conditioned_bad_challenges d
              (\<lambda>j _. fri_builder_conceptual_layers roots builder_state
                final_value ! j)) \<or>
        (\<exists>i < length challenges.
          query_idxs \<in>
            fri_conditioned_residual_query_lists roots challenges
              (fri_builder_conceptual_layers roots builder_state final_value)
              i)"
    by (rule authenticated_recorded_chain_conditioned_split[
      where prefix_state="\<lambda>_. builder_state" and
        layers="fri_builder_conceptual_layers roots builder_state final_value",
      OF chain eval_power round_count rounds_le])
      (use builder_ext builder_clean no_singleton recorded_authenticated
        layer_at final_layer start_not_low in auto)
  from split show ?thesis
  proof
    assume cover:
        "challenges \<in>
          generic_fri_bad_challenge_lists (length challenges)
            (fri_conditioned_bad_challenges d
              (\<lambda>j _. fri_builder_conceptual_layers roots builder_state
                final_value ! j))"
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
          query_idxs \<in>
            fri_conditioned_residual_query_lists roots challenges
              (fri_builder_conceptual_layers roots builder_state final_value) i"
    then show ?thesis by simp
  qed
qed

end

end
