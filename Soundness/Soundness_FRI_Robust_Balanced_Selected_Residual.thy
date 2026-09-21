theory Soundness_FRI_Robust_Balanced_Selected_Residual
  imports Stark.Soundness_FRI_Robust_Balanced_Actual_Query
begin

context soundness
begin

lemma fri_builder_authenticated_chain_balanced_active_residual:
  fixes d N C i :: nat
  assumes chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_fit: "Suc (length challenges) \<le> N"
    and builder_ext: "builder_state \<le> final_state"
    and builder_clean: "\<not> hash_map_output_collision builder_state"
    and no_builder_target:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets (set roots) builder_state)
        builder_state final_state"
    and authenticated:
      "generic_fri_recorded_chunks_authenticated roots query_idxs
        round_layers final_state"
    and active:
      "i \<in> fri_balanced_residual_active_layers
        d C roots challenges final_value builder_state"
  shows
    "query_idxs \<in>
      fri_robust_conditioned_residual_query_lists roots challenges
        (fri_builder_conceptual_layers roots builder_state final_value) i"
proof -
  let ?layers =
    "fri_builder_conceptual_layers roots builder_state final_value"
  have lengths: "length challenges = length roots"
    using chain
    unfolding generic_fri_recorded_value_chain_evidence_def
    by simp
  from active have i_bound: "i < length challenges"
    unfolding fri_balanced_residual_active_layers_def by auto
  have rounds_le: "ceil_log (Suc d) \<le> N"
    using round_count rounds_fit by linarith
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
      using no_builder_target
        hash_map_new_output_hit_subset[OF target_subset]
      by blast
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
  have sampled:
      "\<And>round_idx.
        round_idx < length query_idxs \<Longrightarrow>
        fri_evidence_next_idx roots query_idxs round_idx i <
            length (fri_canonical_domain_at i) div 2 \<and>
          fri_conditioned_layer_table (Suc i) (?layers ! Suc i) !
              fri_evidence_next_idx roots query_idxs round_idx i =
            fri_table_fold_value (challenges ! i)
              (fri_conditioned_layer_table i (?layers ! i))
              (fri_canonical_domain_at i)
              (length (fri_canonical_domain_at i))
              (2 ^ i)
              (fri_evidence_next_idx roots query_idxs round_idx i)"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length query_idxs"
    show
      "fri_evidence_next_idx roots query_idxs round_idx i <
          length (fri_canonical_domain_at i) div 2 \<and>
        fri_conditioned_layer_table (Suc i) (?layers ! Suc i) !
            fri_evidence_next_idx roots query_idxs round_idx i =
          fri_table_fold_value (challenges ! i)
            (fri_conditioned_layer_table i (?layers ! i))
            (fri_canonical_domain_at i)
            (length (fri_canonical_domain_at i))
            (2 ^ i)
            (fri_evidence_next_idx roots query_idxs round_idx i)"
      apply (rule recorded_chain_conceptual_sample[
          OF chain eval_power _ round_bound i_bound])
           apply (use round_count rounds_le in simp)
          apply (rule builder_ext)
         apply (rule builder_clean)
        apply (rule no_singleton)
        apply assumption
       apply (rule recorded_authenticated[OF round_bound])
       apply assumption
      apply (rule layer_at)
      apply assumption
      by (rule final_layer)
  qed
  have i_lt_N: "i < N"
    using i_bound rounds_fit by linarith
  have successor_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        length (?layers ! Suc i)"
    by (rule fri_builder_conceptual_layers_cover)
      (use i_bound lengths in simp)
  have agreement_all:
      "\<forall>round_idx < length query_idxs.
        fri_evidence_next_idx roots query_idxs round_idx i \<in>
          fri_robust_conditioned_agreement_indices
            challenges ?layers i"
  proof (intro allI impI)
    fix round_idx
    assume round_bound: "round_idx < length query_idxs"
    have sampled_i:
        "fri_evidence_next_idx roots query_idxs round_idx i <
            length (fri_canonical_domain_at i) div 2 \<and>
          fri_conditioned_layer_table (Suc i) (?layers ! Suc i) !
              fri_evidence_next_idx roots query_idxs round_idx i =
            fri_table_fold_value (challenges ! i)
              (fri_conditioned_layer_table i (?layers ! i))
              (fri_canonical_domain_at i)
              (length (fri_canonical_domain_at i))
              (2 ^ i)
              (fri_evidence_next_idx roots query_idxs round_idx i)"
      by (rule sampled[OF round_bound])
    show
        "fri_evidence_next_idx roots query_idxs round_idx i \<in>
          fri_robust_conditioned_agreement_indices challenges ?layers i"
      by (rule sampled_fold_imp_robust_conditioned_agreement[
            OF eval_power i_lt_N successor_cover])
        (use sampled_i in blast)+
  qed
  show ?thesis
    using agreement_all
    unfolding fri_robust_conditioned_residual_query_lists_def
    by simp
qed



definition fri_balanced_selected_residual_query_lists
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
    'f \<Rightarrow> 'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_balanced_selected_residual_query_lists d C roots challenges
      final_value builder_state =
    (let active =
      fri_balanced_residual_active_layers
        d C roots challenges final_value builder_state
     in if active = {} then {}
        else {qs \<in> fri_query_index_list_space.
          qs \<in> fri_robust_conditioned_residual_query_lists
            roots challenges
            (fri_builder_conceptual_layers roots builder_state final_value)
            (Min active)})"

lemma fri_builder_authenticated_chain_robust_online_or_selected_residual_balanced_exact_two:
  fixes d N C :: nat
  assumes chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_fit: "Suc (length challenges) \<le> N"
    and exact:
      "fri_balanced_exact_list_cap d (length challenges) C 2"
    and builder_ext: "builder_state \<le> final_state"
    and builder_clean: "\<not> hash_map_output_collision builder_state"
    and no_builder_target:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets (set roots) builder_state)
        builder_state final_state"
    and authenticated:
      "generic_fri_recorded_chunks_authenticated roots query_idxs
        round_layers final_state"
    and query_space: "query_idxs \<in> fri_query_index_list_space"
  shows
    "fri_canonical_layer_close d
        (fri_robust_conditioned_layers (length challenges)
          (fri_builder_conceptual_layers roots builder_state final_value))
        (fri_balanced_radius (length challenges) C) 0 \<or>
      (\<exists>j < length challenges.
        challenges ! j \<in>
          fri_online_balanced_bad_challenges d (length challenges) C j
            builder_state (roots ! j)) \<or>
      query_idxs \<in> fri_balanced_selected_residual_query_lists
        d C roots challenges final_value builder_state"
proof -
  let ?active =
    "fri_balanced_residual_active_layers
      d C roots challenges final_value builder_state"
  have split:
    "fri_canonical_layer_close d
        (fri_robust_conditioned_layers (length challenges)
          (fri_builder_conceptual_layers roots builder_state final_value))
        (fri_balanced_radius (length challenges) C) 0 \<or>
      (\<exists>j < length challenges.
        challenges ! j \<in>
          fri_online_balanced_bad_challenges d (length challenges) C j
            builder_state (roots ! j)) \<or>
      (\<exists>i < length challenges.
        \<not> fri_canonical_layer_close d
          (fri_robust_conditioned_layers (length challenges)
            (fri_builder_conceptual_layers roots builder_state final_value))
          (fri_balanced_radius (length challenges) C) i \<and>
        fri_canonical_layer_close d
          (fri_robust_conditioned_layers (length challenges)
            (fri_builder_conceptual_layers roots builder_state final_value))
          (fri_balanced_radius (length challenges) C) (Suc i) \<and>
        query_idxs \<in>
          fri_robust_conditioned_residual_query_lists roots challenges
            (fri_builder_conceptual_layers roots builder_state final_value) i \<and>
        card (fri_robust_conditioned_agreement_indices challenges
          (fri_builder_conceptual_layers roots builder_state final_value) i)
          \<le> length (fri_canonical_domain_at (Suc i)) -
            fri_balanced_margin C i)"
    by (rule
      fri_builder_authenticated_chain_robust_online_or_residual_balanced_exact_two[
        OF chain eval_power round_count rounds_fit exact builder_ext
          builder_clean no_builder_target authenticated])
  from split show ?thesis
  proof
    assume initial:
      "fri_canonical_layer_close d
        (fri_robust_conditioned_layers (length challenges)
          (fri_builder_conceptual_layers roots builder_state final_value))
        (fri_balanced_radius (length challenges) C) 0"
    then show ?thesis by simp
  next
    assume rest:
      "(\<exists>j < length challenges.
        challenges ! j \<in>
          fri_online_balanced_bad_challenges d (length challenges) C j
            builder_state (roots ! j)) \<or>
       (\<exists>i < length challenges.
        \<not> fri_canonical_layer_close d
          (fri_robust_conditioned_layers (length challenges)
            (fri_builder_conceptual_layers roots builder_state final_value))
          (fri_balanced_radius (length challenges) C) i \<and>
        fri_canonical_layer_close d
          (fri_robust_conditioned_layers (length challenges)
            (fri_builder_conceptual_layers roots builder_state final_value))
          (fri_balanced_radius (length challenges) C) (Suc i) \<and>
        query_idxs \<in>
          fri_robust_conditioned_residual_query_lists roots challenges
            (fri_builder_conceptual_layers roots builder_state final_value) i \<and>
        card (fri_robust_conditioned_agreement_indices challenges
          (fri_builder_conceptual_layers roots builder_state final_value) i)
          \<le> length (fri_canonical_domain_at (Suc i)) -
            fri_balanced_margin C i)"
    from rest show ?thesis
    proof
      assume online:
        "\<exists>j < length challenges.
          challenges ! j \<in>
            fri_online_balanced_bad_challenges d (length challenges) C j
              builder_state (roots ! j)"
      then show ?thesis by simp
    next
      assume residual:
        "\<exists>i < length challenges.
          \<not> fri_canonical_layer_close d
            (fri_robust_conditioned_layers (length challenges)
              (fri_builder_conceptual_layers roots builder_state final_value))
            (fri_balanced_radius (length challenges) C) i \<and>
          fri_canonical_layer_close d
            (fri_robust_conditioned_layers (length challenges)
              (fri_builder_conceptual_layers roots builder_state final_value))
            (fri_balanced_radius (length challenges) C) (Suc i) \<and>
          query_idxs \<in>
            fri_robust_conditioned_residual_query_lists roots challenges
              (fri_builder_conceptual_layers roots builder_state final_value) i \<and>
          card (fri_robust_conditioned_agreement_indices challenges
            (fri_builder_conceptual_layers roots builder_state final_value) i)
            \<le> length (fri_canonical_domain_at (Suc i)) -
              fri_balanced_margin C i"
      then obtain i where i_active: "i \<in> ?active"
        unfolding fri_balanced_residual_active_layers_def by auto
      have active_nonempty: "?active \<noteq> {}"
        using i_active by auto
      have min_active: "Min ?active \<in> ?active"
        by (rule Min_in[OF finite_fri_balanced_residual_active_layers
              active_nonempty])
      have min_residual:
          "query_idxs \<in>
            fri_robust_conditioned_residual_query_lists roots challenges
              (fri_builder_conceptual_layers roots builder_state final_value)
              (Min ?active)"
        by (rule fri_builder_authenticated_chain_balanced_active_residual[
          OF chain eval_power round_count rounds_fit builder_ext builder_clean
            no_builder_target authenticated min_active])
      show ?thesis
        unfolding fri_balanced_selected_residual_query_lists_def Let_def
          if_not_P[OF active_nonempty]
        using query_space min_residual by simp
    qed
  qed
qed



definition fri_balanced_selected_residual_query_indices
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
    'f \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "fri_balanced_selected_residual_query_indices d C roots challenges
      final_value builder_state =
    (let active =
      fri_balanced_residual_active_layers
        d C roots challenges final_value builder_state
     in if active = {} then {}
        else fri_balanced_residual_layer_query_indices roots challenges
          (fri_builder_conceptual_layers roots builder_state final_value)
          (Min active))"

definition fri_balanced_selected_residual_index_card_bound
  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "fri_balanced_selected_residual_index_card_bound d C =
    Max (insert 0
      ((\<lambda>i. modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) -
          fri_balanced_margin C i)) ` {..<ceil_log (Suc d)}))"

lemma fri_balanced_selected_residual_query_lists_rectangle_cover:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "fri_balanced_selected_residual_query_lists d C roots challenges
        final_value builder_state
      \<subseteq> fri_conditioned_query_lists
        (fri_balanced_selected_residual_query_indices
          d C roots challenges final_value builder_state)"
proof (cases
    "fri_balanced_residual_active_layers
      d C roots challenges final_value builder_state = {}")
  case True
  then show ?thesis
    unfolding fri_balanced_selected_residual_query_lists_def
      fri_balanced_selected_residual_query_indices_def Let_def
    by simp
next
  case False
  let ?active =
    "fri_balanced_residual_active_layers
      d C roots challenges final_value builder_state"
  let ?i = "Min ?active"
  let ?layers =
    "fri_builder_conceptual_layers roots builder_state final_value"
  have i_active: "?i \<in> ?active"
    by (rule Min_in[OF finite_fri_balanced_residual_active_layers False])
  have i_bound: "?i < length challenges"
    using i_active
    unfolding fri_balanced_residual_active_layers_def by auto
  have layer_bound: "?i < length roots"
    using i_bound lengths by simp
  have restricted:
      "fri_robust_conditioned_residual_query_lists
          roots challenges ?layers ?i \<inter> fri_query_index_list_space
        \<subseteq> fri_conditioned_query_lists
          (fri_balanced_residual_layer_query_indices
            roots challenges ?layers ?i)"
    unfolding fri_balanced_residual_layer_query_indices_def
    by (rule fri_robust_conditioned_residual_restricted_subset[
          OF eval_power roots_le layer_bound])
  show ?thesis
    unfolding fri_balanced_selected_residual_query_lists_def
      fri_balanced_selected_residual_query_indices_def Let_def
      if_not_P[OF False]
    using restricted by auto
qed

lemma fri_balanced_selected_residual_query_indices_subset:
  "fri_balanced_selected_residual_query_indices
      d C roots challenges final_value builder_state
    \<subseteq> query_sample_space"
proof (cases
    "fri_balanced_residual_active_layers
      d C roots challenges final_value builder_state = {}")
  case True
  then show ?thesis
    unfolding fri_balanced_selected_residual_query_indices_def Let_def
    by simp
next
  case False
  show ?thesis
    unfolding fri_balanced_selected_residual_query_indices_def Let_def
      if_not_P[OF False]
    by (rule fri_balanced_residual_layer_query_indices_subset)
qed

lemma card_fri_balanced_selected_residual_query_indices:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_fit: "Suc (length challenges) \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "card (fri_balanced_selected_residual_query_indices
        d C roots challenges final_value builder_state)
      \<le> fri_balanced_selected_residual_index_card_bound d C"
proof (cases
    "fri_balanced_residual_active_layers
      d C roots challenges final_value builder_state = {}")
  case True
  then show ?thesis
    unfolding fri_balanced_selected_residual_query_indices_def Let_def
    by simp
next
  case False
  let ?active =
    "fri_balanced_residual_active_layers
      d C roots challenges final_value builder_state"
  let ?i = "Min ?active"
  let ?E =
    "modulo_preimage_card_envelope query_sample_space_size
      (length (fri_canonical_domain_at (Suc ?i)))
      (length (fri_canonical_domain_at (Suc ?i)) -
        fri_balanced_margin C ?i)"
  have i_active: "?i \<in> ?active"
    by (rule Min_in[OF finite_fri_balanced_residual_active_layers False])
  have i_bound: "?i < ceil_log (Suc d)"
    using i_active round_count
    unfolding fri_balanced_residual_active_layers_def by auto
  have local:
      "card
        (fri_balanced_residual_layer_query_indices roots challenges
          (fri_builder_conceptual_layers roots builder_state final_value) ?i)
        \<le> ?E"
    by (rule card_fri_balanced_residual_layer_query_indices_active[
          OF eval_power rounds_fit lengths i_active])
  have E_mem:
      "?E \<in> insert 0
        ((\<lambda>i. modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) -
            fri_balanced_margin C i)) ` {..<ceil_log (Suc d)})"
    using i_bound by auto
  have E_le:
      "?E \<le> fri_balanced_selected_residual_index_card_bound d C"
    unfolding fri_balanced_selected_residual_index_card_bound_def
    by (rule Max_ge) (use E_mem in auto)
  show ?thesis
    unfolding fri_balanced_selected_residual_query_indices_def Let_def
      if_not_P[OF False]
    using local E_le by linarith
qed

end
end
