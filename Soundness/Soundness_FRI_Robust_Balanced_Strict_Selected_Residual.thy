theory Soundness_FRI_Robust_Balanced_Strict_Selected_Residual
  imports
    Stark.Soundness_FRI_Authenticated_Residual_Realization_Audit
    Stark.Soundness_FRI_Robust_Balanced_Selected_Residual
begin

context soundness
begin

text \<open>
  The selected residual classification already charges a challenge belonging to
  any online bad-challenge target as a separate event.  On the complementary
  residual branch, the selected active layer's challenge is therefore outside
  the exact fold-good set.  Retaining that complement permits the strict
  triangle bound, and replaces the local agreement cap at margin s by the cap
  at Suc s without changing the verifier or transcript experiment.
\<close>

lemma fri_balanced_active_online_bad_eq_fold_good:
  assumes lengths: "length challenges = length roots"
    and active:
      "i \<in> fri_balanced_residual_active_layers
        d C roots challenges final_value builder_state"
  shows
    "fri_online_balanced_bad_challenges d (length challenges) C i
        builder_state (roots ! i) =
      fri_fold_good_challenges
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (length (fri_canonical_domain_at i))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i
          (conceptual_table builder_state (roots ! i)
            (length (fri_canonical_domain_at i))))
        (fri_balanced_good_radius (length challenges) C i)"
proof -
  let ?layers =
    "fri_builder_conceptual_layers roots builder_state final_value"
  from active have i_bound: "i < length challenges"
    and far:
      "\<not> fri_canonical_layer_close d
        (fri_robust_conditioned_layers (length challenges) ?layers)
        (fri_balanced_radius (length challenges) C) i"
    unfolding fri_balanced_residual_active_layers_def by auto
  have root_bound: "i < length roots"
    using i_bound lengths by simp
  have layer_at:
      "?layers ! i = conceptual_table builder_state (roots ! i)
        (length (fri_canonical_domain_at i))"
    by (rule fri_builder_conceptual_layers_at[OF root_bound])
  have distance_far:
      "\<not> fri_rs_distance_to_code
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (nth (fri_conditioned_layer_table i
          (conceptual_table builder_state (roots ! i)
            (length (fri_canonical_domain_at i))))) \<le>
          2 * fri_balanced_good_radius (length challenges) C i"
    using far fri_balanced_current_radius_exact[OF i_bound]
    unfolding fri_canonical_layer_close_def
      fri_robust_conditioned_layers_nth[OF less_imp_le[OF i_bound]]
      layer_at
    by simp
  show ?thesis
    unfolding fri_online_balanced_bad_challenges_def
      fri_balanced_conditioned_bad_challenges_def Let_def
    using distance_far by simp
qed

lemma card_fri_balanced_residual_layer_query_indices_active_strict:
  fixes i N :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_fit: "Suc (length challenges) \<le> N"
    and lengths: "length challenges = length roots"
    and active:
      "i \<in> fri_balanced_residual_active_layers
        d C roots challenges final_value builder_state"
    and challenge_not_online:
      "challenges ! i \<notin>
        fri_online_balanced_bad_challenges d (length challenges) C i
          builder_state (roots ! i)"
  shows
    "card
      (fri_balanced_residual_layer_query_indices roots challenges
        (fri_builder_conceptual_layers roots builder_state final_value) i)
      \<le> modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) -
          Suc (fri_balanced_margin C i))"
proof -
  let ?layers =
    "fri_builder_conceptual_layers roots builder_state final_value"
  from active have i_bound: "i < length challenges"
    and next_close:
      "fri_canonical_layer_close d
        (fri_robust_conditioned_layers (length challenges) ?layers)
        (fri_balanced_radius (length challenges) C) (Suc i)"
    unfolding fri_balanced_residual_active_layers_def by auto
  have root_bound: "i < length roots"
    using i_bound lengths by simp
  have current_at:
      "?layers ! i = conceptual_table builder_state (roots ! i)
        (length (fri_canonical_domain_at i))"
    by (rule fri_builder_conceptual_layers_at[OF root_bound])
  have next_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        length (?layers ! Suc i)"
    by (rule fri_builder_conceptual_layers_cover)
      (use i_bound lengths in simp)
  have next_distance:
      "fri_rs_distance_to_code
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (nth (fri_conditioned_layer_table (Suc i) (?layers ! Suc i)))
        \<le> fri_balanced_radius (length challenges) C (Suc i)"
    using next_close
    unfolding fri_canonical_layer_close_def
      fri_robust_conditioned_layers_nth[OF Suc_leI[OF i_bound]]
    by simp
  have challenge_not_good:
      "challenges ! i \<notin> fri_fold_good_challenges
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (length (fri_canonical_domain_at i))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i (?layers ! i))
        (fri_balanced_good_radius (length challenges) C i)"
  proof -
    have online_eq:
      "fri_online_balanced_bad_challenges d (length challenges) C i
          builder_state (roots ! i) =
        fri_fold_good_challenges
          (fri_degree_after (Suc i) (fri_padded_degree_bound d))
          (fri_canonical_domain_at (Suc i))
          (length (fri_canonical_domain_at i))
          (fri_canonical_domain_at i)
          (fri_conditioned_layer_table i
            (conceptual_table builder_state (roots ! i)
              (length (fri_canonical_domain_at i))))
          (fri_balanced_good_radius (length challenges) C i)"
      by (rule fri_balanced_active_online_bad_eq_fold_good[OF lengths active])
    show ?thesis
      using challenge_not_online online_eq
      unfolding current_at by simp
  qed
  have layer_fit: "Suc i \<le> N"
    using i_bound rounds_fit by linarith
  show ?thesis
    unfolding fri_balanced_residual_layer_query_indices_def
    by (rule card_fri_robust_conditioned_query_indices_strict[
          OF eval_power layer_fit next_cover next_distance
            challenge_not_good])
      (simp add: fri_balanced_transition_margin_exact)
qed
definition fri_balanced_online_bad_challenge_event
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f protocol_channel \<Rightarrow> bool"
where
  "fri_balanced_online_bad_challenge_event d C roots challenges builder_state \<longleftrightarrow>
    (\<exists>j < min (length challenges) (length roots).
      challenges ! j \<in>
        fri_online_balanced_bad_challenges d (length challenges) C j
          builder_state (roots ! j))"

definition fri_balanced_strict_selected_residual_query_lists
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
    'f \<Rightarrow> 'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_balanced_strict_selected_residual_query_lists d C roots challenges
      final_value builder_state =
    (if fri_balanced_online_bad_challenge_event
          d C roots challenges builder_state
     then {}
     else fri_balanced_selected_residual_query_lists
       d C roots challenges final_value builder_state)"

definition fri_balanced_strict_selected_residual_query_indices
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
    'f \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "fri_balanced_strict_selected_residual_query_indices d C roots challenges
      final_value builder_state =
    (if fri_balanced_online_bad_challenge_event
          d C roots challenges builder_state
     then {}
     else fri_balanced_selected_residual_query_indices
       d C roots challenges final_value builder_state)"

definition fri_balanced_strict_selected_residual_index_card_bound
  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "fri_balanced_strict_selected_residual_index_card_bound d C =
    Max (insert 0
      ((\<lambda>i. modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) -
          Suc (fri_balanced_margin C i))) ` {..<ceil_log (Suc d)}))"

lemma fri_builder_authenticated_chain_robust_online_or_strict_selected_residual_balanced_exact_two:
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
      query_idxs \<in> fri_balanced_strict_selected_residual_query_lists
        d C roots challenges final_value builder_state"
proof -
  have old:
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
    by (rule
      fri_builder_authenticated_chain_robust_online_or_selected_residual_balanced_exact_two[
        OF chain eval_power round_count rounds_fit exact builder_ext
          builder_clean no_builder_target authenticated query_space])
  from old show ?thesis
  proof (elim disjE)
    assume initial:
      "fri_canonical_layer_close d
        (fri_robust_conditioned_layers (length challenges)
          (fri_builder_conceptual_layers roots builder_state final_value))
        (fri_balanced_radius (length challenges) C) 0"
    then show ?thesis by simp
  next
    assume online:
      "\<exists>j < length challenges.
        challenges ! j \<in>
          fri_online_balanced_bad_challenges d (length challenges) C j
            builder_state (roots ! j)"
    then show ?thesis by simp
  next
    assume residual:
      "query_idxs \<in> fri_balanced_selected_residual_query_lists
        d C roots challenges final_value builder_state"
    show ?thesis
    proof (cases
        "fri_balanced_online_bad_challenge_event
          d C roots challenges builder_state")
      case True
      then have online:
        "\<exists>j < length challenges.
          challenges ! j \<in>
            fri_online_balanced_bad_challenges d (length challenges) C j
              builder_state (roots ! j)"
        unfolding fri_balanced_online_bad_challenge_event_def by auto
      then show ?thesis by simp
    next
      case False
      have residual_strict:
        "query_idxs \<in> fri_balanced_strict_selected_residual_query_lists
          d C roots challenges final_value builder_state"
        using residual
        unfolding fri_balanced_strict_selected_residual_query_lists_def
        by (simp add: False)
      then show ?thesis by simp
    qed
  qed
qed




lemma fri_balanced_strict_selected_residual_query_lists_rectangle_cover:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "fri_balanced_strict_selected_residual_query_lists
        d C roots challenges final_value builder_state
      \<subseteq> fri_conditioned_query_lists
        (fri_balanced_strict_selected_residual_query_indices
          d C roots challenges final_value builder_state)"
proof (cases
    "fri_balanced_online_bad_challenge_event
      d C roots challenges builder_state")
  case True
  then show ?thesis
    unfolding fri_balanced_strict_selected_residual_query_lists_def
      fri_balanced_strict_selected_residual_query_indices_def
    by simp
next
  case False
  show ?thesis
    unfolding fri_balanced_strict_selected_residual_query_lists_def
      fri_balanced_strict_selected_residual_query_indices_def
      if_not_P[OF False]
    by (rule fri_balanced_selected_residual_query_lists_rectangle_cover[
          OF eval_power roots_le lengths])
qed

lemma fri_balanced_strict_selected_residual_query_indices_subset:
  "fri_balanced_strict_selected_residual_query_indices
      d C roots challenges final_value builder_state
    \<subseteq> query_sample_space"
proof (cases
    "fri_balanced_online_bad_challenge_event
      d C roots challenges builder_state")
  case True
  then show ?thesis
    unfolding fri_balanced_strict_selected_residual_query_indices_def
    by simp
next
  case False
  show ?thesis
    unfolding fri_balanced_strict_selected_residual_query_indices_def
      if_not_P[OF False]
    by (rule fri_balanced_selected_residual_query_indices_subset)
qed

lemma card_fri_balanced_strict_selected_residual_query_indices:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_fit: "Suc (length challenges) \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "card (fri_balanced_strict_selected_residual_query_indices
        d C roots challenges final_value builder_state)
      \<le> fri_balanced_strict_selected_residual_index_card_bound d C"
proof (cases
    "fri_balanced_online_bad_challenge_event
      d C roots challenges builder_state")
  case online: True
  then show ?thesis
    unfolding fri_balanced_strict_selected_residual_query_indices_def
    by simp
next
  case no_online: False
  let ?active =
    "fri_balanced_residual_active_layers
      d C roots challenges final_value builder_state"
  show ?thesis
  proof (cases "?active = {}")
    case no_active: True
    show ?thesis
      unfolding fri_balanced_strict_selected_residual_query_indices_def
        fri_balanced_selected_residual_query_indices_def
        if_not_P[OF no_online] Let_def if_P[OF no_active]
      by simp
  next
    case active_nonempty: False
    let ?i = "Min ?active"
    let ?E =
      "modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc ?i)))
        (length (fri_canonical_domain_at (Suc ?i)) -
          Suc (fri_balanced_margin C ?i))"
    have i_active: "?i \<in> ?active"
      by (rule Min_in[OF finite_fri_balanced_residual_active_layers
            active_nonempty])
    have i_bound: "?i < length challenges"
      using i_active
      unfolding fri_balanced_residual_active_layers_def by auto
    have i_log_bound: "?i < ceil_log (Suc d)"
      using i_bound round_count by simp
    have i_min_bound:
        "?i < min (length challenges) (length roots)"
      using i_bound lengths by simp
    have challenge_not_online:
      "challenges ! ?i \<notin>
        fri_online_balanced_bad_challenges d (length challenges) C ?i
          builder_state (roots ! ?i)"
      using no_online i_min_bound
      unfolding fri_balanced_online_bad_challenge_event_def by blast
    have local:
      "card
        (fri_balanced_residual_layer_query_indices roots challenges
          (fri_builder_conceptual_layers roots builder_state final_value) ?i)
        \<le> ?E"
      by (rule
        card_fri_balanced_residual_layer_query_indices_active_strict[
          OF eval_power rounds_fit lengths i_active challenge_not_online])
    have E_mem:
      "?E \<in> insert 0
        ((\<lambda>i. modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) -
            Suc (fri_balanced_margin C i))) ` {..<ceil_log (Suc d)})"
      using i_log_bound by auto
    have E_le:
      "?E \<le> fri_balanced_strict_selected_residual_index_card_bound d C"
      unfolding fri_balanced_strict_selected_residual_index_card_bound_def
      by (rule Max_ge) (use E_mem in auto)
    show ?thesis
      unfolding fri_balanced_strict_selected_residual_query_indices_def
        fri_balanced_selected_residual_query_indices_def
        if_not_P[OF no_online] Let_def if_not_P[OF active_nonempty]
      using local E_le by linarith
  qed
qed

end
end
