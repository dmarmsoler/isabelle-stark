theory Soundness_FRI_Authenticated_Global_Chain_Audit
  imports Stark.Soundness_FRI_Robust_Balanced_Selected_Residual
begin

context soundness
begin

text \<open>
  The global residual set below retains every authenticated FRI-layer
  agreement constraint.  The realizability predicate bundles evidence from an
  already recorded verifier-compatible chain; it does not assert that an
  arbitrary conceptual table family can be realized by clean Merkle roots and
  prefix-fixed random-oracle challenges.
\<close>

lemma fri_builder_authenticated_chain_residual_at_every_layer:
  fixes d N i :: nat
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
    and layer_bound: "i < length challenges"
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
      and j_bound: "j < length challenges"
    have root_bound: "j < length roots"
      using j_bound lengths by simp
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
          OF chain eval_power _ round_bound layer_bound])
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
    using layer_bound rounds_fit by linarith
  have successor_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        length (?layers ! Suc i)"
    by (rule fri_builder_conceptual_layers_cover)
      (use layer_bound lengths in simp)
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

definition fri_authenticated_global_residual_query_lists ::
  "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow> nat list set"
where
  "fri_authenticated_global_residual_query_lists roots challenges layers =
    {qs. \<forall>i<length challenges.
      qs \<in> fri_robust_conditioned_residual_query_lists
        roots challenges layers i}"

lemma fri_builder_authenticated_chain_global_residual:
  fixes d N :: nat
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
  shows
    "query_idxs \<in> fri_authenticated_global_residual_query_lists
      roots challenges
      (fri_builder_conceptual_layers roots builder_state final_value)"
  unfolding fri_authenticated_global_residual_query_lists_def
  by (intro CollectI allI impI)
    (rule fri_builder_authenticated_chain_residual_at_every_layer[
      OF chain eval_power round_count rounds_fit builder_ext builder_clean
        no_builder_target authenticated])

definition fri_authenticated_global_residual_query_indices ::
  "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow> nat set"
where
  "fri_authenticated_global_residual_query_indices roots challenges layers =
    (\<Inter>i\<in>{..<length challenges}.
      fri_conditioned_query_indices roots i
        (fri_robust_conditioned_agreement_indices challenges layers i))"

lemma fri_authenticated_global_residual_query_indices_subset_layer:
  assumes layer_bound: "i < length challenges"
  shows
    "fri_authenticated_global_residual_query_indices roots challenges layers
      \<subseteq> fri_conditioned_query_indices roots i
        (fri_robust_conditioned_agreement_indices challenges layers i)"
  using layer_bound
  unfolding fri_authenticated_global_residual_query_indices_def by auto

lemma fri_authenticated_global_residual_rectangle_cover:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "fri_authenticated_global_residual_query_lists roots challenges layers \<inter>
        fri_query_index_list_space
      \<subseteq> fri_conditioned_query_lists
        (fri_authenticated_global_residual_query_indices
          roots challenges layers)"
proof
  fix qs
  assume qs:
      "qs \<in> fri_authenticated_global_residual_query_lists
          roots challenges layers \<inter> fri_query_index_list_space"
  then have global:
      "qs \<in> fri_authenticated_global_residual_query_lists
        roots challenges layers"
    and query_space: "qs \<in> fri_query_index_list_space"
    by auto
  have entries:
      "set qs \<subseteq> fri_authenticated_global_residual_query_indices
        roots challenges layers"
  proof
    fix q
    assume q_in: "q \<in> set qs"
    show
      "q \<in> fri_authenticated_global_residual_query_indices
        roots challenges layers"
      unfolding fri_authenticated_global_residual_query_indices_def
    proof (intro INT_I)
      fix i
      assume i_in: "i \<in> {..<length challenges}"
      then have i_bound: "i < length challenges"
        by simp
      have root_bound: "i < length roots"
        using i_bound lengths by simp
      have residual:
          "qs \<in> fri_robust_conditioned_residual_query_lists
            roots challenges layers i"
        using global i_bound
        unfolding fri_authenticated_global_residual_query_lists_def
        by auto
      have local:
          "qs \<in> fri_conditioned_query_lists
            (fri_conditioned_query_indices roots i
              (fri_robust_conditioned_agreement_indices
                challenges layers i))"
        by (rule set_mp[OF
              fri_robust_conditioned_residual_restricted_subset[
                OF eval_power roots_le root_bound]])
          (use residual query_space in auto)
      show
          "q \<in> fri_conditioned_query_indices roots i
            (fri_robust_conditioned_agreement_indices challenges layers i)"
        using local q_in
        unfolding fri_conditioned_query_lists_def by auto
    qed
  qed
  have query_len: "length qs = rounds"
    using query_space
    unfolding fri_query_index_list_space_def by auto
  show
      "qs \<in> fri_conditioned_query_lists
        (fri_authenticated_global_residual_query_indices
          roots challenges layers)"
    using entries query_len
    unfolding fri_conditioned_query_lists_def by simp
qed

lemma card_fri_authenticated_global_residual_query_indices_le_layer:
  assumes layer_bound: "i < length challenges"
  shows
    "card (fri_authenticated_global_residual_query_indices
        roots challenges layers) \<le>
      card (fri_conditioned_query_indices roots i
        (fri_robust_conditioned_agreement_indices challenges layers i))"
  by (rule card_mono)
    (use fri_authenticated_global_residual_query_indices_subset_layer[
      OF layer_bound] in auto)

lemma card_fri_authenticated_global_residual_query_indices_active:
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_fit: "Suc (length challenges) \<le> N"
    and lengths: "length challenges = length roots"
    and active:
      "i \<in> fri_balanced_residual_active_layers
        d C roots challenges final_value prefix_state"
  shows
    "card (fri_authenticated_global_residual_query_indices roots challenges
        (fri_builder_conceptual_layers roots prefix_state final_value)) \<le>
      modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) -
          fri_balanced_margin C i)"
proof -
  have i_bound: "i < length challenges"
    using active
    unfolding fri_balanced_residual_active_layers_def by auto
  have global_le:
      "card (fri_authenticated_global_residual_query_indices roots challenges
          (fri_builder_conceptual_layers roots prefix_state final_value)) \<le>
        card (fri_balanced_residual_layer_query_indices roots challenges
          (fri_builder_conceptual_layers roots prefix_state final_value) i)"
    unfolding fri_balanced_residual_layer_query_indices_def
    by (rule card_fri_authenticated_global_residual_query_indices_le_layer[
          OF i_bound])
  have local_le:
      "card (fri_balanced_residual_layer_query_indices roots challenges
          (fri_builder_conceptual_layers roots prefix_state final_value) i) \<le>
        modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) -
            fri_balanced_margin C i)"
    by (rule card_fri_balanced_residual_layer_query_indices_active[
          OF eval_power rounds_fit lengths active])
  show ?thesis
    using global_le local_le by linarith
qed

definition indexed_constraint_intersection ::
  "nat \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
  "indexed_constraint_intersection m active A =
    (\<Inter>i\<in>{..<m}. if i = active then A else UNIV)"

lemma indexed_constraint_intersection_single_restriction:
  assumes active: "active < m"
  shows "indexed_constraint_intersection m active A = A"
proof
  show "indexed_constraint_intersection m active A \<subseteq> A"
  proof
    fix x
    assume x_in: "x \<in> indexed_constraint_intersection m active A"
    then show "x \<in> A"
      using active
      unfolding indexed_constraint_intersection_def by auto
  qed
  show "A \<subseteq> indexed_constraint_intersection m active A"
    unfolding indexed_constraint_intersection_def by auto
qed

theorem fri_builder_authenticated_chain_global_residual_rectangle:
  fixes d N :: nat
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
    and query_space: "query_idxs \<in> fri_query_index_list_space"
  shows
    "query_idxs \<in> fri_conditioned_query_lists
      (fri_authenticated_global_residual_query_indices roots challenges
        (fri_builder_conceptual_layers roots builder_state final_value))"
proof -
  have lengths: "length challenges = length roots"
    using chain
    unfolding generic_fri_recorded_value_chain_evidence_def by simp
  have roots_le: "length roots \<le> N"
    using lengths rounds_fit by linarith
  have global:
      "query_idxs \<in> fri_authenticated_global_residual_query_lists
        roots challenges
        (fri_builder_conceptual_layers roots builder_state final_value)"
    by (rule fri_builder_authenticated_chain_global_residual[
          OF chain eval_power round_count rounds_fit builder_ext builder_clean
            no_builder_target authenticated])
  show ?thesis
    by (rule set_mp[OF fri_authenticated_global_residual_rectangle_cover[
          OF eval_power roots_le lengths]])
      (use global query_space in auto)
qed

definition fri_authenticated_global_chain_realizable ::
  "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
    'f list list list \<Rightarrow> 'f protocol_channel \<Rightarrow> 'f protocol_channel \<Rightarrow> bool"
where
  "fri_authenticated_global_chain_realizable d N roots challenges final_value
      query_idxs round_layers builder_state final_state \<longleftrightarrow>
    generic_fri_recorded_value_chain_evidence roots challenges final_value
      query_idxs round_layers \<and>
    clength * scale = 2 ^ N \<and>
    length challenges = ceil_log (Suc d) \<and>
    Suc (length challenges) \<le> N \<and>
    builder_state \<le> final_state \<and>
    \<not> hash_map_output_collision builder_state \<and>
    \<not> hash_map_new_output_hit
      (merkle_prefix_path_targets (set roots) builder_state)
      builder_state final_state \<and>
    generic_fri_recorded_chunks_authenticated roots query_idxs
      round_layers final_state \<and>
    query_idxs \<in> fri_query_index_list_space"

lemma fri_authenticated_global_chain_realizable_imp_global_rectangle:
  assumes realizable:
    "fri_authenticated_global_chain_realizable d N roots challenges final_value
      query_idxs round_layers builder_state final_state"
  shows
    "query_idxs \<in> fri_conditioned_query_lists
      (fri_authenticated_global_residual_query_indices roots challenges
        (fri_builder_conceptual_layers roots builder_state final_value))"
  using realizable
  unfolding fri_authenticated_global_chain_realizable_def
  by (blast intro:
    fri_builder_authenticated_chain_global_residual_rectangle)

end
end
