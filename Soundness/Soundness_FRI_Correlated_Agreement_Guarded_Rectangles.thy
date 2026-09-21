theory Soundness_FRI_Correlated_Agreement_Guarded_Rectangles
 imports Stark.Soundness_FRI_Correlated_Agreement_Adaptive_Charging
   Stark.Soundness_FRI_Robust_Balanced_Decoded_Rectangle
   Stark.Soundness_FRI_Conditioned_Explicit_Residual_Complete_List_Classification
begin
section \<open>Guarded correlated-agreement query families\<close>
text \<open>
  These auxiliary sets retain the active-chain, exact degree and distance guards.
  Ineligible families are empty; no empty global intersection is used as a finite
  query set. Stability uses the already charged Merkle target complements.
  The near-code branch permits separate trace and composition distance cutoffs.
\<close>

context soundness
begin

lemma fri_mca_chain_stable:
 assumes ext: "s \<le> u"
   and no_hit: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets (set roots) s) s u"
 shows "fri_mca_chain_bad_event d ts roots challenges u =
        fri_mca_chain_bad_event d ts roots challenges s"
proof -
 have at: "\<And>i. i < min (length roots) (length challenges) \<Longrightarrow>
     fri_mca_online_bad_challenges d (ts i) i u (roots ! i) =
     fri_mca_online_bad_challenges d (ts i) i s (roots ! i)"
 proof -
   fix i assume i: "i < min (length roots) (length challenges)"
   have sub: "merkle_prefix_path_targets {roots ! i} s \<subseteq>
       merkle_prefix_path_targets (set roots) s"
     by (rule merkle_prefix_path_targets_mono) (use i in auto)
   have none: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {roots ! i} s) s u"
     using no_hit hash_map_new_output_hit_subset[OF sub] by blast
   show "fri_mca_online_bad_challenges d (ts i) i u (roots ! i) =
     fri_mca_online_bad_challenges d (ts i) i s (roots ! i)"
     by (rule fri_mca_online_bad_prefix_stable[OF ext none])
 qed
 show ?thesis unfolding fri_mca_chain_bad_event_def using at by blast
qed

lemma fri_mca_global_residual_stable:
 assumes ext: "s \<le> u"
   and no_hit: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets (set roots) s) s u"
 shows "fri_authenticated_global_residual_query_indices roots challenges
     (fri_builder_conceptual_layers roots u v) =
   fri_authenticated_global_residual_query_indices roots challenges
     (fri_builder_conceptual_layers roots s v)"
 by (simp only: fri_builder_conceptual_layers_stable_if_no_target[OF ext no_hit])

lemma fri_mca_root_distance_stable:
 assumes ext: "s \<le> u"
   and no_hit: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {rt} s) s u"
 shows "fri_rs_distance_to_code k xs (nth (conceptual_table u rt n)) =
   fri_rs_distance_to_code k xs (nth (conceptual_table s rt n))"
 by (simp only: conceptual_table_prefix_stable_if_no_target[OF ext no_hit])

lemma fri_mca_empty_chain:
 "\<not> fri_mca_chain_bad_event d ts [] challenges s"
 "\<not> fri_mca_chain_bad_event d ts roots [] s"
 by (simp_all add: fri_mca_chain_bad_event_def)

lemma fri_mca_composition_zero_distance:
 assumes empty: "staged_composition_fri_roots data = []"
 shows "fri_rs_distance_to_code (fri_padded_degree_bound d) eval_domain
   (nth (ro_actual_query_composition_candidate data s)) = 0"
proof -
 have low: "composition_table_low_degree (fri_padded_degree_bound d)
      (ro_actual_query_composition_candidate data s)"
   by (rule ro_actual_query_composition_candidate_zero_round_low_degree_any[OF empty])
 have table: "fri_table_low_degree_on (fri_padded_degree_bound d) eval_domain
      (ro_actual_query_composition_candidate data s)"
   using low unfolding composition_table_low_degree_iff_fri_table_low_degree_on_eval_domain .
 show ?thesis by (rule fri_table_low_degree_distance_zero[OF table])
qed

lemma fri_mca_near_code_semantic_bound:
 assumes original_length: "length original = length eval_domain"
   and composition_length: "length composition = length eval_domain"
   and degree: "d \<le> maxDegree"
   and trace_close: "fri_rs_distance_to_code (fri_padded_degree_bound (clength-1))
       eval_domain (nth trace) \<le> rt"
   and composition_close: "fri_rs_distance_to_code (fri_padded_degree_bound d)
       eval_domain (nth composition) \<le> rc"
   and not_all: "\<not> (composition_table_low_degree maxDegree
       (fri_canonical_decoded_table d composition) \<and>
     all_queries_consistent (fri_canonical_decoded_table (clength-1) trace)
       (fri_canonical_decoded_table d composition) alphas)"
 shows "card (trace_composition_accepted_indices original trace composition alphas)
   \<le> trace_composition_padding_query_index_bound + rt + rc"
proof -
 note split = robust_two_decodes_semantic_trichotomy[
   OF original_length composition_length trace_close composition_close,
   where as=alphas]
 have padded: "trace_composition_query_index_bound_for (fri_padded_degree_bound d)
     \<le> trace_composition_padding_query_index_bound"
   unfolding trace_composition_padding_query_index_bound_def
   by (rule trace_composition_query_index_bound_for_mono)
      (rule fri_padded_degree_bound_mono[OF degree])
 have base: "trace_composition_query_index_bound \<le> trace_composition_padding_query_index_bound"
   by (rule trace_composition_query_index_bound_le_padding)
 show ?thesis using split not_all padded base by (elim disjE conjE; linarith)
qed

definition fri_mca_guarded_indices where
 "fri_mca_guarded_indices d N ts r roots challenges v s =
 (if clength*scale=2^N \<and> length challenges=ceil_log (Suc d) \<and>
      length roots=length challenges \<and> 0<length challenges \<and> length challenges\<le>N \<and>
      \<not> fri_mca_chain_bad_event d ts roots challenges s \<and>
      r < fri_rs_distance_to_code (fri_padded_degree_bound d) (fri_canonical_domain_at 0)
        (nth (conceptual_table s (roots!0) (length (fri_canonical_domain_at 0))))
  then fri_authenticated_global_residual_query_indices roots challenges
        (fri_builder_conceptual_layers roots s v)
  else {})"

lemma fri_mca_guarded_card:
 "card (fri_mca_guarded_indices d N ts r roots challenges v s)
    \<le> fri_mca_residual_index_bound d ts r"
 unfolding fri_mca_guarded_indices_def
 by (auto intro: fri_mca_builder_global_residual_card)

lemma fri_mca_guarded_subset:
 "fri_mca_guarded_indices d N ts r roots challenges v s \<subseteq> query_sample_space"
 unfolding fri_mca_guarded_indices_def
 using fri_mca_global_subset_query_space by simp

lemma fri_mca_trace_bad_head_cong:
 "fri_mca_trace_builder_bad (ro_query_head_data data) s = fri_mca_trace_builder_bad data s"
 by (simp add: fri_mca_trace_builder_bad_def ro_query_head_data_def)

lemma fri_mca_composition_bad_head_cong:
 "fri_mca_composition_builder_bad (ro_query_head_data data) s = fri_mca_composition_builder_bad data s"
 by (simp add: fri_mca_composition_builder_bad_def ro_query_head_data_def)


lemma fri_mca_support_threshold_mono:
 assumes mn: "m \<le> n"
 shows "fri_mca_support_threshold m ts \<le> fri_mca_support_threshold n ts"
 unfolding fri_mca_support_threshold_def
 by (rule Max_mono) (use mn in auto)

lemma fri_mca_residual_degree_mono:
 assumes de: "d \<le> e"
 shows "fri_mca_residual_index_bound d ts r \<le> fri_mca_residual_index_bound e ts r"
 unfolding fri_mca_residual_index_bound_def
 by (rule max.mono[OF order_refl fri_mca_support_threshold_mono])
    (rule ceil_log_mono, use de in simp)

lemma fri_mca_guarded_stable:
 assumes ext: "s \<le> u"
   and no_hit: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets (set roots) s) s u"
 shows "fri_mca_guarded_indices d N ts r roots challenges v u =
        fri_mca_guarded_indices d N ts r roots challenges v s"
proof (cases "roots=[]")
 case True then show ?thesis
 by (force simp: fri_mca_guarded_indices_def)
next
 case False
 have root: "roots!0 \<in> set roots" using False by simp
 have sub: "merkle_prefix_path_targets {roots!0} s \<subseteq>
      merkle_prefix_path_targets (set roots) s"
   by (rule merkle_prefix_path_targets_mono) (use root in auto)
 have none: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {roots!0} s) s u"
   using no_hit hash_map_new_output_hit_subset[OF sub] by blast
 show ?thesis unfolding fri_mca_guarded_indices_def
   by (simp only: fri_mca_root_distance_stable[OF ext none]
       fri_mca_chain_stable[OF ext no_hit]
       fri_mca_global_residual_stable[OF ext no_hit])
qed


definition mca_decoded_semantic_query_index_bound :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
 "mca_decoded_semantic_query_index_bound rT rC =
  trace_composition_padding_query_index_bound + rT + rC"

definition ro_mca_decoded_semantic_query_indices where
 "ro_mca_decoded_semantic_query_indices rT rC prefix prefix_state data query_start =
  (let d = to_nat (staged_degree data);
       ft = first_trace_fri_root_prefix_first_table prefix prefix_state;
       ct = ro_actual_query_composition_candidate data query_start
   in if d \<le> maxDegree \<and>
       fri_rs_distance_to_code (fri_padded_degree_bound (clength-1)) eval_domain (nth ft) \<le> rT \<and>
       fri_rs_distance_to_code (fri_padded_degree_bound d) eval_domain (nth ct) \<le> rC \<and>
       \<not> (composition_table_low_degree maxDegree (fri_canonical_decoded_table d ct) \<and>
          all_queries_consistent (fri_canonical_decoded_table (clength-1) ft)
            (fri_canonical_decoded_table d ct) (staged_alphas data))
   then ro_actual_query_trace_composition_accepted_indices prefix prefix_state data query_start
   else {})"

definition ro_mca_decoded_semantic_query_lists where
 "ro_mca_decoded_semantic_query_lists rT rC prefix prefix_state data query_start =
  fri_conditioned_query_lists
    (ro_mca_decoded_semantic_query_indices rT rC prefix prefix_state data query_start)"

lemma ro_mca_decoded_semantic_query_indices_subset:
 "ro_mca_decoded_semantic_query_indices rT rC prefix prefix_state data query_start
    \<subseteq> query_sample_space"
 unfolding ro_mca_decoded_semantic_query_indices_def Let_def
 using ro_actual_query_trace_composition_accepted_indices_subset[
   of prefix prefix_state data query_start] by auto

lemma card_ro_mca_decoded_semantic_query_indices:
 "card (ro_mca_decoded_semantic_query_indices rT rC prefix prefix_state data query_start)
    \<le> mca_decoded_semantic_query_index_bound rT rC"
proof -
 have ol: "length (conceptual_table prefix_state (staged_trace_root data) (scale*clength))
     = length eval_domain"
   using eval_domain_length by (simp add: mult.commute)
 have cl: "length (ro_actual_query_composition_candidate data query_start) = length eval_domain"
   unfolding ro_actual_query_composition_candidate_def
   using eval_domain_length by (simp add: mult.commute)
 show ?thesis
   unfolding ro_mca_decoded_semantic_query_indices_def Let_def
     mca_decoded_semantic_query_index_bound_def
   by (auto simp: ro_actual_query_trace_composition_accepted_indices_def
       intro: fri_mca_near_code_semantic_bound[OF ol cl])
qed

definition ro_mca_rectangle_error :: "nat \<Rightarrow> staged_budgets \<Rightarrow> prob" where
 "ro_mca_rectangle_error B budgets =
  (nnreal (query_raw_preimage_card_envelope B) / nnreal size) ^
    (rounds - staged_attacker_query_budget budgets)"

lemma wp_ro_mca_decoded_semantic_rectangle:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
 shows "wp_event
    (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
    (ro_query_head_dependent_actual_query_index_list_hit (ro_mca_decoded_semantic_query_lists rT rC))
    adversary_initial_state
  \<le> ro_mca_rectangle_error (mca_decoded_semantic_query_index_bound rT rC) budgets"
 unfolding ro_mca_rectangle_error_def
 by (rule wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_bound[
      OF wf controlled, where I="ro_mca_decoded_semantic_query_indices rT rC"])
    (simp_all add: ro_mca_decoded_semantic_query_lists_def
       ro_mca_decoded_semantic_query_indices_subset card_ro_mca_decoded_semantic_query_indices)

lemma fri_mca_guarded_member:
 assumes actual: "fri_authenticated_global_chain_realizable d N roots challenges v
     qs round_layers s u"
   and active: "0 < length challenges"
   and good: "\<not> fri_mca_chain_bad_event d ts roots challenges s"
   and far: "r < fri_rs_distance_to_code (fri_padded_degree_bound d)
     (fri_canonical_domain_at 0)
     (nth (conceptual_table s (roots!0) (length (fri_canonical_domain_at 0))))"
 shows "qs \<in> fri_conditioned_query_lists (fri_mca_guarded_indices d N ts r roots challenges v s)"
proof -
 have member: "qs \<in> fri_conditioned_query_lists
     (fri_authenticated_global_residual_query_indices roots challenges
       (fri_builder_conceptual_layers roots s v))"
   by (rule fri_authenticated_global_chain_realizable_imp_global_rectangle[OF actual])
 have shape: "clength*scale=2^N \<and> length challenges=ceil_log (Suc d) \<and>
      length roots=length challenges \<and> length challenges\<le>N"
   using actual unfolding fri_authenticated_global_chain_realizable_def
     generic_fri_recorded_value_chain_evidence_def by auto
 show ?thesis unfolding fri_mca_guarded_indices_def
   using shape active good far member by simp
qed

end
end
