theory Soundness_FRI_Conditioned_Authenticated_Bridge
  imports
    Soundness_FRI_Conditioned_Conceptual_Split
    Stark.Soundness_Merkle_Prefix_Target
    Stark.Soundness_FRI_RO_Actual_Query_Chain_Conflict_Collapse
begin

context soundness
begin

lemma authenticated_recorded_chunk_matches_prefix_conceptual_table:
  assumes ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and no_target:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {rt} prefix_state)
        prefix_state final_state"
    and authenticated:
      "fri_layer_chunk_authenticated rt len idx chunk final_state"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
  shows
    "fri_opening_matches_table len idx
      (conceptual_table prefix_state rt len) xp xn"
proof -
  from fri_layer_chunk_authenticated_matching_values[OF authenticated chunk]
  obtain xp_path' xn_path' where
    chunk':
      "fri_layer_opening_chunk len xp xp_path' xn xn_path' chunk"
    and base_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path'\<rparr>"
    and sibling_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path'\<rparr>"
    .
  have idx_bound: "idx < len"
    using base_auth unfolding authenticated_opening_in_def by simp
  have base:
      "conceptual_table prefix_state rt len ! idx = xp"
    using
      authenticated_opening_agrees_with_prefix_conceptual_table_or_prefix_target_hit[
        OF ext clean base_auth]
      no_target
    by simp
  have sibling:
      "conceptual_table prefix_state rt len !
        fri_sibling_index len idx = xn"
    using
      authenticated_opening_agrees_with_prefix_conceptual_table_or_prefix_target_hit[
        OF ext clean sibling_auth]
      no_target
    by simp
  show ?thesis
    unfolding fri_opening_matches_table_def
    using idx_bound base sibling by simp
qed

lemma authenticated_recorded_step_prefix_conceptual_fold:
  assumes eval_power: "clength * scale = 2 ^ N"
    and i_lt_N: "i < N"
    and len_eq: "len = length (fri_canonical_domain_at i)"
    and ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and no_target:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {rt} prefix_state)
        prefix_state final_state"
    and step:
      "fri_layer_step_evidence rt b len raw (2 ^ i)
        (fri_sibling_index len raw)
        xp xp_path xn xn_path next_idx next_value chunk"
    and authenticated:
      "fri_layer_chunk_authenticated rt len raw chunk final_state"
  shows
    "next_idx < length (fri_canonical_domain_at i) div 2"
    "next_value =
      fri_table_fold_value b
        (fri_conditioned_layer_table i
          (conceptual_table prefix_state rt len))
        (fri_canonical_domain_at i)
        (length (fri_canonical_domain_at i)) (2 ^ i) next_idx"
proof -
  have chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    by (rule fri_layer_step_evidenceD(4)[OF step])
  have match:
      "fri_opening_matches_table len raw
        (conceptual_table prefix_state rt len) xp xn"
    by (rule authenticated_recorded_chunk_matches_prefix_conceptual_table[
        OF ext clean no_target authenticated chunk])
  have raw_bound: "raw < len"
    by (rule fri_opening_matches_tableD(1)[OF match])
  have i_le_N: "i \<le> N"
    using i_lt_N by simp
  have len_pos: "0 < len"
    unfolding len_eq
    by (rule fri_canonical_domain_at_pos[OF eval_power i_le_N])
  have even_len: "2 dvd len"
    unfolding len_eq
    by (rule fri_canonical_domain_at_even[OF eval_power i_lt_N])
  have product: "len * 2 ^ i = clength * scale"
    unfolding len_eq
    by (rule fri_canonical_domain_at_round_product[OF eval_power i_le_N])
  have dom_raw:
      "fri_canonical_domain_at i ! raw =
        (h ^ raw * shift) ^ (2 ^ i)"
    by (rule fri_canonical_domain_at_nth)
      (use raw_bound len_eq in simp)
  have sampled:
      "fri_sampled_table_fold b len raw (2 ^ i)
        (fri_canonical_domain_at i)
        (conceptual_table prefix_state rt len) chunk next_value"
    by (rule fri_layer_step_evidence_sampled_table_fold_if_matching_chunk[
        OF step dom_raw chunk match])
  have half_pos: "0 < len div 2"
    using len_pos even_len by (cases len) auto
  have next_eq: "next_idx = raw mod (len div 2)"
    by (rule fri_layer_step_evidenceD(2)[OF step])
  have next_bound: "next_idx < len div 2"
    unfolding next_eq using half_pos by simp
  show
      "next_idx < length (fri_canonical_domain_at i) div 2"
    using next_bound len_eq by simp
  have dom_next:
      "fri_canonical_domain_at i ! (raw mod (len div 2)) =
        (h ^ (raw mod (len div 2)) * shift) ^ (2 ^ i)"
    by (rule fri_canonical_domain_at_nth)
      (use next_bound next_eq len_eq in simp)
  have normalized:
      "next_value =
        fri_table_fold_value b (conceptual_table prefix_state rt len)
          (fri_canonical_domain_at i) len (2 ^ i) next_idx"
    using fri_sampled_table_fold_eq_at_mod_index[
        OF sampled even_len product dom_next]
      next_eq
    by simp
  have conditioned:
      "fri_table_fold_value b
          (fri_conditioned_layer_table i
            (conceptual_table prefix_state rt len))
          (fri_canonical_domain_at i) len (2 ^ i) next_idx =
        fri_table_fold_value b (conceptual_table prefix_state rt len)
          (fri_canonical_domain_at i) len (2 ^ i) next_idx"
    by (rule fri_table_fold_value_conditioned_layer[
        OF len_pos len_eq next_bound])
  show
      "next_value =
        fri_table_fold_value b
          (fri_conditioned_layer_table i
            (conceptual_table prefix_state rt len))
          (fri_canonical_domain_at i)
          (length (fri_canonical_domain_at i)) (2 ^ i) next_idx"
    using normalized conditioned len_eq by simp
qed

lemma recorded_chain_conceptual_sample:
  assumes chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and eval_power: "clength * scale = 2 ^ N"
    and rounds_le: "length challenges \<le> N"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
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
      "\<And>j. j < length challenges \<Longrightarrow>
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
  shows
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        length (fri_canonical_domain_at layer_idx) div 2 \<and>
      fri_conditioned_layer_table (Suc layer_idx)
          (layers ! Suc layer_idx) !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx =
        fri_table_fold_value (challenges ! layer_idx)
          (fri_conditioned_layer_table layer_idx (layers ! layer_idx))
          (fri_canonical_domain_at layer_idx)
          (length (fri_canonical_domain_at layer_idx))
          (2 ^ layer_idx)
          (fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
proof -
  from generic_fri_recorded_value_chain_evidenceE[OF chain round_bound]
  obtain chain_values where
    challenges_len: "length challenges = length roots"
    and chain_values_final:
      "chain_values ! length challenges = final_value"
    and steps:
      "\<forall>j < length challenges.
        \<exists>xp_path xn xn_path.
          fri_layer_step_evidence
            (roots ! j)
            (challenges ! j)
            (fri_evidence_layer_len roots j)
            (fri_evidence_layer_idx roots query_idxs round_idx j)
            (2 ^ j)
            (fri_sibling_index
              (fri_evidence_layer_len roots j)
              (fri_evidence_layer_idx roots query_idxs round_idx j))
            (chain_values ! j) xp_path xn xn_path
            (fri_evidence_next_idx roots query_idxs round_idx j)
            (chain_values ! Suc j)
            (round_layers ! round_idx ! j)"
    by blast
  from steps[rule_format, OF layer_bound]
  obtain xp_path xn xn_path where current_step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        (chain_values ! layer_idx) xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (chain_values ! Suc layer_idx)
        (round_layers ! round_idx ! layer_idx)"
    by blast
  let ?len = "fri_evidence_layer_len roots layer_idx"
  let ?raw = "fri_evidence_layer_idx roots query_idxs round_idx layer_idx"
  let ?idx = "fri_evidence_next_idx roots query_idxs round_idx layer_idx"
  have len_eq:
      "?len = length (fri_canonical_domain_at layer_idx)"
    unfolding fri_evidence_layer_len_def fri_canonical_domain_at_length
    using challenges_len fri_layer_lengths_nth_div[
        of layer_idx "length roots" "clength * scale"]
      layer_bound
    by simp
  have i_lt_N: "layer_idx < N"
    using layer_bound rounds_le by simp
  have current_auth:
      "fri_layer_chunk_authenticated (roots ! layer_idx) ?len ?raw
        (round_layers ! round_idx ! layer_idx) final_state"
    using recorded_authenticated[OF layer_bound]
    unfolding generic_fri_recorded_layer_chunk_authenticated_def .
  from authenticated_recorded_step_prefix_conceptual_fold[
      OF eval_power i_lt_N len_eq prefix_ext[OF layer_bound]
        prefix_clean[OF layer_bound] no_prefix_target[OF layer_bound]
        current_step current_auth]
  have idx_bound:
      "?idx < length (fri_canonical_domain_at layer_idx) div 2"
    and current_fold:
      "chain_values ! Suc layer_idx =
        fri_table_fold_value (challenges ! layer_idx)
          (fri_conditioned_layer_table layer_idx
            (conceptual_table (prefix_state layer_idx)
              (roots ! layer_idx) ?len))
          (fri_canonical_domain_at layer_idx)
          (length (fri_canonical_domain_at layer_idx))
          (2 ^ layer_idx) ?idx"
    by blast+
  have current_layer:
      "layers ! layer_idx =
        conceptual_table (prefix_state layer_idx)
          (roots ! layer_idx) ?len"
    using layer_at[OF layer_bound] len_eq by simp
  have current_fold_layers:
      "chain_values ! Suc layer_idx =
        fri_table_fold_value (challenges ! layer_idx)
          (fri_conditioned_layer_table layer_idx
            (layers ! layer_idx))
          (fri_canonical_domain_at layer_idx)
          (length (fri_canonical_domain_at layer_idx))
          (2 ^ layer_idx) ?idx"
    using current_fold current_layer by simp
  have successor_len:
      "length (fri_canonical_domain_at (Suc layer_idx)) =
        length (fri_canonical_domain_at layer_idx) div 2"
    by (rule fri_canonical_domain_successor_length[OF eval_power i_lt_N])
  have idx_successor:
      "?idx < length (fri_canonical_domain_at (Suc layer_idx))"
    using idx_bound successor_len by simp
  have successor_value:
      "fri_conditioned_layer_table (Suc layer_idx)
          (layers ! Suc layer_idx) ! ?idx =
        chain_values ! Suc layer_idx"
  proof (cases "Suc layer_idx < length challenges")
    case True
    from steps[rule_format, OF True]
    obtain next_xp_path next_xn next_xn_path where successor_step:
        "fri_layer_step_evidence
          (roots ! Suc layer_idx)
          (challenges ! Suc layer_idx)
          (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx))
          (2 ^ Suc layer_idx)
          (fri_sibling_index
            (fri_evidence_layer_len roots (Suc layer_idx))
            (fri_evidence_layer_idx roots query_idxs round_idx
              (Suc layer_idx)))
          (chain_values ! Suc layer_idx) next_xp_path next_xn next_xn_path
          (fri_evidence_next_idx roots query_idxs round_idx (Suc layer_idx))
          (chain_values ! Suc (Suc layer_idx))
          (round_layers ! round_idx ! Suc layer_idx)"
      by blast
    have next_auth:
        "fri_layer_chunk_authenticated (roots ! Suc layer_idx)
          (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx))
          (round_layers ! round_idx ! Suc layer_idx) final_state"
      using recorded_authenticated[OF True]
      unfolding generic_fri_recorded_layer_chunk_authenticated_def .
    have next_chunk:
        "fri_layer_opening_chunk
          (fri_evidence_layer_len roots (Suc layer_idx))
          (chain_values ! Suc layer_idx) next_xp_path next_xn next_xn_path
          (round_layers ! round_idx ! Suc layer_idx)"
      by (rule fri_layer_step_evidenceD(4)[OF successor_step])
    have next_match:
        "fri_opening_matches_table
          (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx))
          (conceptual_table (prefix_state (Suc layer_idx))
            (roots ! Suc layer_idx)
            (fri_evidence_layer_len roots (Suc layer_idx)))
          (chain_values ! Suc layer_idx) next_xn"
      by (rule authenticated_recorded_chunk_matches_prefix_conceptual_table[
          OF prefix_ext[OF True] prefix_clean[OF True]
            no_prefix_target[OF True] next_auth next_chunk])
    have next_len_eq:
        "fri_evidence_layer_len roots (Suc layer_idx) =
          length (fri_canonical_domain_at (Suc layer_idx))"
      unfolding fri_evidence_layer_len_def fri_canonical_domain_at_length
      using challenges_len fri_layer_lengths_nth_div[
          of "Suc layer_idx" "length roots" "clength * scale"]
        True
      by simp
    have next_raw_eq:
        "fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx) =
          ?idx"
      by (rule fri_evidence_layer_idx_Suc)
        (use True challenges_len in simp)
    have conceptual_next:
        "conceptual_table (prefix_state (Suc layer_idx))
            (roots ! Suc layer_idx)
            (length (fri_canonical_domain_at (Suc layer_idx))) ! ?idx =
          chain_values ! Suc layer_idx"
      using fri_opening_matches_tableD(3)[OF next_match]
        next_len_eq next_raw_eq
      by simp
    have layer_next:
        "layers ! Suc layer_idx =
          conceptual_table (prefix_state (Suc layer_idx))
            (roots ! Suc layer_idx)
            (length (fri_canonical_domain_at (Suc layer_idx)))"
      by (rule layer_at[OF True])
    show ?thesis
      unfolding fri_conditioned_layer_table_nth[OF idx_successor]
      using conceptual_next layer_next by simp
  next
    case False
    have last: "Suc layer_idx = length challenges"
      using layer_bound False by simp
    have final_value_at:
        "chain_values ! Suc layer_idx = final_value"
      using chain_values_final last by simp
    have idx_final:
        "?idx < length (fri_canonical_domain_at (length challenges))"
      using idx_successor last by simp
    have conditioned_final:
        "fri_conditioned_layer_table (length challenges)
            (replicate
              (length (fri_canonical_domain_at (length challenges)))
              final_value) ! ?idx =
          final_value"
      unfolding fri_conditioned_layer_table_nth[OF idx_final]
      using idx_final by simp
    show ?thesis
      using last final_layer conditioned_final final_value_at by simp
  qed
  show ?thesis
    using idx_bound successor_value current_fold_layers by simp
qed

lemma authenticated_recorded_chain_conditioned_split:
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
    apply (rule conceptual_sampled_chain_conditioned_split[
        where N=N and d=d and committed="\<lambda>j _. layers ! j",
        OF challenge_space refl round_count eval_power rounds_le layer_cover
          _ start_not_low final_low sampled])
    by simp_all
qed

end

end
