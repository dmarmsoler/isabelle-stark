theory Soundness_FRI_Conditioned_Security_Bridge
  imports Soundness_FRI_Conditioned_Challenge_Outcome_Bridge
begin

context soundness
begin

definition fri_checked_builder_merkle_targets
  :: "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> 'f set"
where
  "fri_checked_builder_merkle_targets data attacker_state =
    merkle_prefix_path_targets
      (set (staged_trace_fri_roots data) \<union>
        set (staged_composition_fri_roots data))
      attacker_state"

definition fri_checked_builder_merkle_target_hit
  :: "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow>
      'f protocol_channel \<Rightarrow> bool"
where
  "fri_checked_builder_merkle_target_hit data attacker_state final_state \<longleftrightarrow>
    hash_map_new_output_hit
      (fri_checked_builder_merkle_targets data attacker_state)
      attacker_state final_state"

lemma fri_ro_bad_challenge_cover_imp_builder_online_bad:
  assumes cover:
      "fri_ro_prefix_challenges fri_items \<in>
        generic_fri_bad_challenge_lists (length fri_items)
          (fri_conditioned_bad_challenges d
            (\<lambda>j _. fri_ro_prefix_conceptual_layers fri_items final_value ! j))"
    and prefix_extensions:
      "\<And>j. j < length fri_items \<Longrightarrow>
        fri_ro_prefix_root_state (fri_items ! j) \<le> final_state"
    and no_prefix_target:
      "\<not> fri_ro_prefix_merkle_target_hit fri_items final_state"
    and builder_ext: "attacker_state \<le> final_state"
    and no_builder_target:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets (set (fri_ro_prefix_roots fri_items))
          attacker_state)
        attacker_state final_state"
  shows
    "\<exists>j < length fri_items.
      fri_ro_prefix_challenges fri_items ! j \<in>
        fri_online_bad_challenges d j attacker_state
          (fri_ro_prefix_roots fri_items ! j)"
proof -
  have multiround:
      "fri_ro_prefix_challenges fri_items \<in>
        fri_multiround_bad_challenge_lists (length fri_items)
          (fri_conditioned_bad_challenges d
            (\<lambda>j _. fri_ro_prefix_conceptual_layers fri_items final_value ! j))"
    using cover unfolding generic_fri_bad_challenge_lists_def .
  from multiround obtain j where
    j_bound: "j < length fri_items"
    and bad:
      "fri_ro_prefix_challenges fri_items ! j \<in>
        fri_conditioned_bad_challenges d
          (\<lambda>j _. fri_ro_prefix_conceptual_layers fri_items final_value ! j)
          j (take j (fri_ro_prefix_challenges fri_items))"
    unfolding fri_multiround_bad_challenge_lists_def by blast
  let ?root = "fri_ro_prefix_roots fri_items ! j"
  let ?prefix = "fri_ro_prefix_root_state (fri_items ! j)"
  let ?len = "length (fri_canonical_domain_at j)"
  have root_at:
      "?root = fri_ro_prefix_root (fri_items ! j)"
    unfolding fri_ro_prefix_roots_def using j_bound by simp
  have no_prefix_singleton:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {?root} ?prefix)
        ?prefix final_state"
    unfolding root_at
    by (rule fri_ro_prefix_no_targetD[OF no_prefix_target j_bound])
  have prefix_stable:
      "conceptual_table final_state ?root ?len =
        conceptual_table ?prefix ?root ?len"
    by (rule conceptual_table_prefix_stable_if_no_target[
      OF prefix_extensions[OF j_bound] no_prefix_singleton])
  have root_mem:
      "?root \<in> set (fri_ro_prefix_roots fri_items)"
    by (rule nth_mem) (simp add: fri_ro_prefix_roots_def j_bound)
  have target_subset:
      "merkle_prefix_path_targets {?root} attacker_state \<subseteq>
        merkle_prefix_path_targets (set (fri_ro_prefix_roots fri_items))
          attacker_state"
    by (rule merkle_prefix_path_targets_mono) (use root_mem in auto)
  have no_builder_singleton:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {?root} attacker_state)
        attacker_state final_state"
  proof
    assume hit:
        "hash_map_new_output_hit
          (merkle_prefix_path_targets {?root} attacker_state)
          attacker_state final_state"
    have "hash_map_new_output_hit
        (merkle_prefix_path_targets (set (fri_ro_prefix_roots fri_items))
          attacker_state)
        attacker_state final_state"
      by (rule hash_map_new_output_hit_subset[OF target_subset hit])
    then show False
      using no_builder_target by contradiction
  qed
  have builder_stable:
      "conceptual_table final_state ?root ?len =
        conceptual_table attacker_state ?root ?len"
    by (rule conceptual_table_prefix_stable_if_no_target[
      OF builder_ext no_builder_singleton])
  have table_eq:
      "conceptual_table ?prefix ?root ?len =
        conceptual_table attacker_state ?root ?len"
    using prefix_stable builder_stable by simp
  have layer_at:
      "fri_ro_prefix_conceptual_layers fri_items final_value ! j =
        conceptual_table ?prefix ?root ?len"
    using fri_ro_prefix_conceptual_layers_at[OF j_bound]
    unfolding fri_ro_prefix_roots_def
    by (simp add: j_bound)
  have layer_attacker:
      "fri_ro_prefix_conceptual_layers fri_items final_value ! j =
        conceptual_table attacker_state ?root ?len"
    using layer_at table_eq by simp
  have bad':
      "fri_ro_prefix_challenges fri_items ! j \<in>
        fri_conditioned_bad_challenges d
          (\<lambda>_ _. conceptual_table attacker_state ?root ?len) j []"
    using bad
    unfolding fri_conditioned_bad_challenges_def Let_def
    by (simp only: layer_attacker)
  have online:
      "fri_ro_prefix_challenges fri_items ! j \<in>
        fri_online_bad_challenges d j attacker_state ?root"
    unfolding fri_online_bad_challenges_def
      fri_online_conceptual_layer_def
    using bad' by simp
  show ?thesis
    using j_bound online by blast
qed

lemma fri_ro_bad_challenge_cover_imp_checked_builder_online_bad:
  assumes cover:
      "fri_ro_prefix_challenges fri_items \<in>
        generic_fri_bad_challenge_lists (length fri_items)
          (fri_conditioned_bad_challenges d
            (\<lambda>j _. fri_ro_prefix_conceptual_layers fri_items final_value ! j))"
    and prefix_extensions:
      "\<And>j. j < length fri_items \<Longrightarrow>
        fri_ro_prefix_root_state (fri_items ! j) \<le> final_state"
    and no_prefix_target:
      "\<not> fri_ro_prefix_merkle_target_hit fri_items final_state"
    and builder_ext: "attacker_state \<le> final_state"
    and roots_subset:
      "set (fri_ro_prefix_roots fri_items) \<subseteq>
        set (staged_trace_fri_roots data) \<union>
          set (staged_composition_fri_roots data)"
    and no_builder_target:
      "\<not> fri_checked_builder_merkle_target_hit data attacker_state final_state"
  shows
    "\<exists>j < length fri_items.
      fri_ro_prefix_challenges fri_items ! j \<in>
        fri_online_bad_challenges d j attacker_state
          (fri_ro_prefix_roots fri_items ! j)"
proof -
  have target_subset:
      "merkle_prefix_path_targets (set (fri_ro_prefix_roots fri_items))
          attacker_state \<subseteq>
        fri_checked_builder_merkle_targets data attacker_state"
    unfolding fri_checked_builder_merkle_targets_def
    by (rule merkle_prefix_path_targets_mono[OF roots_subset])
  have no_builder_target':
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets (set (fri_ro_prefix_roots fri_items))
          attacker_state)
        attacker_state final_state"
  proof
    assume hit:
        "hash_map_new_output_hit
          (merkle_prefix_path_targets (set (fri_ro_prefix_roots fri_items))
            attacker_state)
          attacker_state final_state"
    have "hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data attacker_state)
        attacker_state final_state"
      by (rule hash_map_new_output_hit_subset[OF target_subset hit])
    then show False
      using no_builder_target
      unfolding fri_checked_builder_merkle_target_hit_def
      by contradiction
  qed
  show ?thesis
    by (rule fri_ro_bad_challenge_cover_imp_builder_online_bad[
      OF cover prefix_extensions no_prefix_target builder_ext
        no_builder_target'])
qed

end

end
