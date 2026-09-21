(*  Title:      Stark/Soundness_FRI_Prechallenge_Conceptual_Witness.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Prechallenge_Conceptual_Witness
  imports
    Soundness_Merkle_Prefix_Target
    Soundness_FRI_Trace_Sibling_Evidence
    Soundness_FRI_Trace_Head_Value
    Soundness_FRI_Sampled_Interface
begin

text \<open>
  Prefix-fixed conceptual witnesses for FRI commitments.  These lemmas use only
  authenticated openings and charge later disagreement to a first-fresh Merkle
  target.  They do not reconstruct a committed full table.
\<close>

context soundness
begin

lemma accepted_fri_opening_transcript_prefix_conceptual_first_layer_sibling_agreement_or_target:
  assumes roots_nonempty: "trace_roots \<noteq> []"
    and ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and fri:
      "accepted_fri_opening_transcript initial_state
        (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final query_idxs trace_round_layers
        composition_round_layers"
  shows
    "trace_table_agrees_with_recorded_first_fri_siblings
       (conceptual_table prefix_state (trace_roots ! 0) (scale * clength))
       trace_roots trace_bs query_idxs trace_round_layers \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {trace_roots ! 0} prefix_state)
       prefix_state final_state"
proof (cases
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {trace_roots ! 0} prefix_state)
      prefix_state final_state")
  case True
  then show ?thesis by simp
next
  case False
  have len0:
    "fri_evidence_layer_len trace_roots 0 = scale * clength"
    using roots_nonempty
    unfolding fri_evidence_layer_len_def
    by (cases trace_roots) (simp_all add: mult.commute)
  show ?thesis
    unfolding trace_table_agrees_with_recorded_first_fri_siblings_def
  proof (intro disjI1 allI impI)
    fix round_idx xp xp_path xn xn_path
    assume round_bound: "round_idx < length query_idxs"
      and roots_pos: "0 < length trace_roots"
      and challenges_pos: "0 < length trace_bs"
      and step:
        "fri_layer_step_evidence
          (trace_roots ! 0)
          (trace_bs ! 0)
          (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots query_idxs round_idx 0)
          1
          (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
            (fri_evidence_layer_idx trace_roots query_idxs round_idx 0))
          xp xp_path xn xn_path
          (fri_evidence_next_idx trace_roots query_idxs round_idx 0)
          (fri_evidence_next_value trace_roots trace_bs query_idxs
            round_idx 0 xp xn)
          (trace_round_layers ! round_idx ! 0)"
    have round_rounds: "round_idx < rounds"
      using round_bound accepted_fri_opening_transcript_shapes(7)[OF fri]
      by simp
    have layer_bound: "0 < length trace_roots"
      by (rule roots_pos)
    have all_layer_bounds:
      "\<And>raw k. k < length trace_roots \<Longrightarrow>
        0 < fri_layer_lengths (length trace_roots) (clength * scale) ! k \<and>
        fri_layer_indices (length trace_roots) (index (to_nat raw))
          (clength * scale) ! k <
        fri_layer_lengths (length trace_roots) (clength * scale) ! k"
      by (rule accepted_fri_opening_transcript_trace_raw_layer_bound[OF fri])
    have recorded:
      "generic_fri_recorded_layer_chunk_authenticated trace_roots query_idxs
        trace_round_layers final_state round_idx 0"
      by (rule
          accepted_fri_opening_transcript_trace_recorded_layer_chunk_authenticated_at
          [OF fri refl round_rounds layer_bound all_layer_bounds])
    have authenticated:
      "fri_layer_chunk_authenticated
        (trace_roots ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots query_idxs round_idx 0)
        (trace_round_layers ! round_idx ! 0) final_state"
      using recorded
      unfolding generic_fri_recorded_layer_chunk_authenticated_def .
    from
      fri_layer_chunk_authenticated_agrees_with_prefix_conceptual_table_or_prefix_target_hit
        [OF ext clean authenticated]
    obtain yp yp_path yn yn_path where
      recorded_chunk:
        "fri_layer_opening_chunk
          (fri_evidence_layer_len trace_roots 0)
          yp yp_path yn yn_path
          (trace_round_layers ! round_idx ! 0)"
      and recorded_sibling:
        "conceptual_table prefix_state (trace_roots ! 0)
          (fri_evidence_layer_len trace_roots 0) !
          fri_sibling_index (fri_evidence_layer_len trace_roots 0)
            (fri_evidence_layer_idx trace_roots query_idxs round_idx 0) =
          yn"
      using False by blast
    have step_chunk:
      "fri_layer_opening_chunk
        (fri_evidence_layer_len trace_roots 0)
        xp xp_path xn xn_path
        (trace_round_layers ! round_idx ! 0)"
      by (rule fri_layer_step_evidenceD(4)[OF step])
    have yn_eq: "yn = xn"
      by (rule fri_layer_opening_chunk_values_unique(2)
          [OF recorded_chunk step_chunk])
    show
      "conceptual_table prefix_state (trace_roots ! 0)
        (scale * clength) !
        fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots query_idxs round_idx 0) =
        xn"
      using recorded_sibling yn_eq len0 by simp
  qed
qed

lemma accepted_fri_opening_transcript_prefix_conceptual_first_layer_base_agreement_or_target:
  assumes roots_nonempty: "trace_roots \<noteq> []"
    and ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and fri:
      "accepted_fri_opening_transcript initial_state
        (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final query_idxs trace_round_layers
        composition_round_layers"
    and round_bound: "round_idx < length query_idxs"
  shows
    "(\<exists>xp xp_path xn xn_path.
       fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
         (trace_round_layers ! round_idx ! 0) \<and>
       conceptual_table prefix_state (trace_roots ! 0)
         (scale * clength) ! (query_idxs ! round_idx) = xp) \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {trace_roots ! 0} prefix_state)
       prefix_state final_state"
proof (cases
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {trace_roots ! 0} prefix_state)
      prefix_state final_state")
  case True
  then show ?thesis by simp
next
  case False
  have round_rounds: "round_idx < rounds"
    using round_bound accepted_fri_opening_transcript_shapes(7)[OF fri]
    by simp
  have layer_bound: "0 < length trace_roots"
    using roots_nonempty by simp
  have all_layer_bounds:
    "\<And>raw k. k < length trace_roots \<Longrightarrow>
      0 < fri_layer_lengths (length trace_roots) (clength * scale) ! k \<and>
      fri_layer_indices (length trace_roots) (index (to_nat raw))
        (clength * scale) ! k <
      fri_layer_lengths (length trace_roots) (clength * scale) ! k"
    by (rule accepted_fri_opening_transcript_trace_raw_layer_bound[OF fri])
  have recorded:
    "generic_fri_recorded_layer_chunk_authenticated trace_roots query_idxs
      trace_round_layers final_state round_idx 0"
    by (rule
        accepted_fri_opening_transcript_trace_recorded_layer_chunk_authenticated_at
        [OF fri refl round_rounds layer_bound all_layer_bounds])
  have authenticated:
    "fri_layer_chunk_authenticated
      (trace_roots ! 0)
      (fri_evidence_layer_len trace_roots 0)
      (fri_evidence_layer_idx trace_roots query_idxs round_idx 0)
      (trace_round_layers ! round_idx ! 0) final_state"
    using recorded
    unfolding generic_fri_recorded_layer_chunk_authenticated_def .
  from
    fri_layer_chunk_authenticated_agrees_with_prefix_conceptual_table_or_prefix_target_hit
      [OF ext clean authenticated]
  obtain xp xp_path xn xn_path where
    chunk:
      "fri_layer_opening_chunk
        (fri_evidence_layer_len trace_roots 0)
        xp xp_path xn xn_path
        (trace_round_layers ! round_idx ! 0)"
    and base:
      "conceptual_table prefix_state (trace_roots ! 0)
        (fri_evidence_layer_len trace_roots 0) !
        fri_evidence_layer_idx trace_roots query_idxs round_idx 0 = xp"
    using False by blast
  have len0:
    "fri_evidence_layer_len trace_roots 0 = scale * clength"
    using roots_nonempty
    unfolding fri_evidence_layer_len_def
    by (cases trace_roots) (simp_all add: mult.commute)
  have idx0:
    "fri_evidence_layer_idx trace_roots query_idxs round_idx 0 =
      query_idxs ! round_idx"
    using roots_nonempty
    unfolding fri_evidence_layer_idx_def
    by (cases trace_roots) simp_all
  have chunk':
    "fri_layer_opening_chunk (scale * clength)
      xp xp_path xn xn_path (trace_round_layers ! round_idx ! 0)"
    using chunk len0 by simp
  have base':
    "conceptual_table prefix_state (trace_roots ! 0)
      (scale * clength) ! (query_idxs ! round_idx) = xp"
    using base len0 idx0 by simp
  have
    "\<exists>xp xp_path xn xn_path.
      fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
        (trace_round_layers ! round_idx ! 0) \<and>
      conceptual_table prefix_state (trace_roots ! 0)
        (scale * clength) ! (query_idxs ! round_idx) = xp"
    using chunk' base' by blast
  then show ?thesis by simp
qed

definition trace_table_base_agreement_indices ::
  "'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
where
  "trace_table_base_agreement_indices trace_table trace_table' =
    {idx \<in> query_sample_space. trace_table ! idx = trace_table' ! idx}"

definition trace_table_base_agreement_query_lists ::
  "'f list \<Rightarrow> 'f list \<Rightarrow> nat list set"
where
  "trace_table_base_agreement_query_lists trace_table trace_table' =
    {query_idxs.
      length query_idxs = rounds \<and>
      set query_idxs \<subseteq> query_sample_space \<and>
      set query_idxs \<subseteq>
        trace_table_base_agreement_indices trace_table trace_table'}"

lemma accepted_fri_opening_transcript_prefix_conceptual_trace_head_base_agreement_or_target:
  assumes roots_nonempty: "trace_roots \<noteq> []"
    and trace_bs_nonempty: "0 < length trace_bs"
    and ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and fri:
      "accepted_fri_opening_transcript initial_state
        (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript initial_state fr trace_roots trace_final
        header_as dg composition_roots composition_final header_rest"
    and round_bound: "round_idx < length query_idxs"
  shows
    "query_idxs ! round_idx \<in>
       trace_table_base_agreement_indices
         (conceptual_table prefix_state fr (scale * clength))
         (conceptual_table prefix_state (trace_roots ! 0)
           (scale * clength)) \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {fr, trace_roots ! 0} prefix_state)
       prefix_state final_state"
proof (cases
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {fr, trace_roots ! 0} prefix_state)
      prefix_state final_state")
  case True
  then show ?thesis by simp
next
  case False
  have fr_targets_subset:
    "merkle_prefix_path_targets {fr} prefix_state \<subseteq>
      merkle_prefix_path_targets {fr, trace_roots ! 0} prefix_state"
    by (rule merkle_prefix_path_targets_mono) auto
  have no_fr:
    "\<not> hash_map_new_output_hit
      (merkle_prefix_path_targets {fr} prefix_state)
      prefix_state final_state"
  proof
    assume hit:
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {fr} prefix_state)
        prefix_state final_state"
    have
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {fr, trace_roots ! 0} prefix_state)
        prefix_state final_state"
      by (rule hash_map_new_output_hit_subset[OF fr_targets_subset hit])
    then show False
      using False by simp
  qed
  have first_targets_subset:
    "merkle_prefix_path_targets {trace_roots ! 0} prefix_state \<subseteq>
      merkle_prefix_path_targets {fr, trace_roots ! 0} prefix_state"
    by (rule merkle_prefix_path_targets_mono) auto
  have no_first:
    "\<not> hash_map_new_output_hit
      (merkle_prefix_path_targets {trace_roots ! 0} prefix_state)
      prefix_state final_state"
  proof
    assume hit:
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {trace_roots ! 0} prefix_state)
        prefix_state final_state"
    have
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {fr, trace_roots ! 0} prefix_state)
        prefix_state final_state"
      by (rule hash_map_new_output_hit_subset[OF first_targets_subset hit])
    then show False
      using False by simp
  qed
  obtain openings xp xp_path xn xn_path where
    opening_indices:
      "map opening_index openings =
        powers_scaled (query_idxs ! round_idx)"
    and partial:
      "partial_authenticated_table fr (scale * clength) openings
        final_state"
    and openings_nonempty: "openings \<noteq> []"
    and opening_value: "opening_value (hd openings) = xp"
    and fri_chunk:
      "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
        (trace_round_layers ! round_idx ! 0)"
    by (rule
        accepted_fri_opening_transcript_trace_head_layer_value_aligned_at
          [OF fri header refl round_bound trace_bs_nonempty])
  have table_agrees:
    "table_agrees_with_authenticated_openings
      (conceptual_table prefix_state fr (scale * clength))
      (scale * clength) openings"
    using
      partial_authenticated_table_agrees_with_prefix_conceptual_table_or_prefix_target_hit
        [OF ext clean partial]
      no_fr
    by blast
  have head_idx:
    "opening_index (hd openings) = query_idxs ! round_idx"
  proof -
    have "opening_index (hd openings) = hd (map opening_index openings)"
      using openings_nonempty by (cases openings) auto
    also have "... = hd (powers_scaled (query_idxs ! round_idx))"
      using opening_indices by simp
    also have "... = query_idxs ! round_idx"
      by (rule powers_scaled_hd)
    finally show ?thesis .
  qed
  have head_in: "hd openings \<in> set openings"
    using openings_nonempty by simp
  have head_agrees:
    "conceptual_table prefix_state fr (scale * clength) !
      opening_index (hd openings) = opening_value (hd openings)"
    using table_agrees head_in
    unfolding table_agrees_with_authenticated_openings_def
    by blast
  have trace_value:
    "conceptual_table prefix_state fr (scale * clength) !
       (query_idxs ! round_idx) = xp"
    using head_agrees head_idx opening_value by simp
  obtain yp yp_path yn yn_path where
    first_chunk:
      "fri_layer_opening_chunk (scale * clength) yp yp_path yn yn_path
        (trace_round_layers ! round_idx ! 0)"
    and first_value:
      "conceptual_table prefix_state (trace_roots ! 0)
        (scale * clength) ! (query_idxs ! round_idx) = yp"
    using
      accepted_fri_opening_transcript_prefix_conceptual_first_layer_base_agreement_or_target
        [OF roots_nonempty ext clean fri round_bound]
      no_first
    by blast
  have yp_eq: "yp = xp"
    by (rule fri_layer_opening_chunk_values_unique(1)
        [OF first_chunk fri_chunk])
  have query_sample:
    "query_idxs ! round_idx \<in> query_sample_space"
  proof (rule accepted_fri_opening_transcript_query_idx_in_sample_space[OF fri])
    show "query_idxs ! round_idx \<in> set query_idxs"
      by (rule nth_mem[OF round_bound])
  qed
  show ?thesis
    using query_sample trace_value first_value yp_eq
    unfolding trace_table_base_agreement_indices_def
    by simp
qed

lemma accepted_fri_opening_transcript_prefix_conceptual_trace_head_query_list_agreement_or_target:
  assumes roots_nonempty: "trace_roots \<noteq> []"
    and trace_bs_nonempty: "0 < length trace_bs"
    and ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and fri:
      "accepted_fri_opening_transcript initial_state
        (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript initial_state fr trace_roots trace_final
        header_as dg composition_roots composition_final header_rest"
  shows
    "query_idxs \<in>
       trace_table_base_agreement_query_lists
         (conceptual_table prefix_state fr (scale * clength))
         (conceptual_table prefix_state (trace_roots ! 0)
           (scale * clength)) \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {fr, trace_roots ! 0} prefix_state)
       prefix_state final_state"
proof (cases
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {fr, trace_roots ! 0} prefix_state)
      prefix_state final_state")
  case True
  then show ?thesis by simp
next
  case False
  have len: "length query_idxs = rounds"
    by (rule accepted_fri_opening_transcript_shapes(7)[OF fri])
  have sample_subset: "set query_idxs \<subseteq> query_sample_space"
  proof
    fix idx
    assume idx_in: "idx \<in> set query_idxs"
    show "idx \<in> query_sample_space"
      by (rule
          accepted_fri_opening_transcript_query_idx_in_sample_space
            [OF fri idx_in])
  qed
  have base_subset:
    "set query_idxs \<subseteq>
      trace_table_base_agreement_indices
        (conceptual_table prefix_state fr (scale * clength))
        (conceptual_table prefix_state (trace_roots ! 0)
          (scale * clength))"
  proof
    fix idx
    assume idx_in: "idx \<in> set query_idxs"
    then obtain i where i_bound: "i < length query_idxs"
      and idx_eq: "query_idxs ! i = idx"
      by (metis in_set_conv_nth)
    have
      "query_idxs ! i \<in>
         trace_table_base_agreement_indices
           (conceptual_table prefix_state fr (scale * clength))
           (conceptual_table prefix_state (trace_roots ! 0)
             (scale * clength))"
      using
        accepted_fri_opening_transcript_prefix_conceptual_trace_head_base_agreement_or_target
          [OF roots_nonempty trace_bs_nonempty ext clean fri header i_bound]
        False
      by blast
    then show
      "idx \<in>
       trace_table_base_agreement_indices
         (conceptual_table prefix_state fr (scale * clength))
         (conceptual_table prefix_state (trace_roots ! 0)
           (scale * clength))"
      using idx_eq by simp
  qed
  have
    "query_idxs \<in>
      trace_table_base_agreement_query_lists
        (conceptual_table prefix_state fr (scale * clength))
        (conceptual_table prefix_state (trace_roots ! 0)
          (scale * clength))"
    unfolding trace_table_base_agreement_query_lists_def
    using len sample_subset base_subset by simp
  then show ?thesis by simp
qed

lemma trace_table_base_agreement_indices_subset:
  "trace_table_base_agreement_indices trace_table trace_table' \<subseteq>
    query_sample_space"
  unfolding trace_table_base_agreement_indices_def by auto

lemma finite_trace_table_base_agreement_indices:
  "finite (trace_table_base_agreement_indices trace_table trace_table')"
  unfolding trace_table_base_agreement_indices_def query_sample_space_def
  by simp

lemma trace_table_base_agreement_query_lists_subset:
  "trace_table_base_agreement_query_lists trace_table trace_table'
    \<subseteq> fri_query_index_list_space"
  unfolding trace_table_base_agreement_query_lists_def
    fri_query_index_list_space_def
  by auto

lemma card_trace_table_base_agreement_query_lists:
  "card
      (trace_table_base_agreement_query_lists trace_table trace_table') =
    card (trace_table_base_agreement_indices trace_table trace_table') ^
      rounds"
proof -
  let ?A =
    "trace_table_base_agreement_indices trace_table trace_table'"
  have finite_A: "finite ?A"
    by (rule finite_trace_table_base_agreement_indices)
  have A_subset: "?A \<subseteq> query_sample_space"
    by (rule trace_table_base_agreement_indices_subset)
  have set_eq:
    "trace_table_base_agreement_query_lists trace_table trace_table' =
      {query_idxs. set query_idxs \<subseteq> ?A \<and> length query_idxs = rounds}"
    unfolding trace_table_base_agreement_query_lists_def
    using A_subset by auto
  have
    "card {query_idxs. set query_idxs \<subseteq> ?A \<and>
        length query_idxs = rounds} =
      card ?A ^ rounds"
    by (rule card_lists_length_eq[OF finite_A])
  then show ?thesis
    using set_eq by simp
qed

lemma trace_table_base_agreement_indices_card_bound:
  assumes trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows "card
      (trace_table_base_agreement_indices trace_table trace_table') <
    clength"
proof -
  from trace_low obtain f where deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    unfolding trace_table_low_degree_def by blast
  from trace'_low obtain f' where deg_f': "degree f' < clength"
    and trace_table': "trace_table' = map (poly f') eval_domain"
    unfolding trace_table_low_degree_def by blast
  let ?A =
    "trace_table_base_agreement_indices trace_table trace_table'"
  let ?R = "f - f'"
  have A_subset: "?A \<subseteq> query_sample_space"
    by (rule trace_table_base_agreement_indices_subset)
  have inj: "inj_on (\<lambda>idx. h ^ idx * shift) ?A"
  proof (intro inj_onI)
    fix i j
    assume i_in: "i \<in> ?A"
      and j_in: "j \<in> ?A"
      and eq: "h ^ i * shift = h ^ j * shift"
    have i_bound: "i < clength * scale"
      by (rule query_sample_space_less_domain[OF set_mp[OF A_subset i_in]])
    have j_bound: "j < clength * scale"
      by (rule query_sample_space_less_domain[OF set_mp[OF A_subset j_in]])
    have "h ^ i = h ^ j"
      using eq shift_nonzero by simp
    then show "i = j"
      by (rule h_power_inj_on_eval_domain[OF i_bound j_bound])
  qed
  have residual_nonzero: "?R \<noteq> 0"
  proof
    assume "?R = 0"
    then have "f = f'"
      by simp
    then show False
      using distinct trace_table trace_table' by simp
  qed
  have image_subset:
    "(\<lambda>idx. h ^ idx * shift) ` ?A \<subseteq> {x. poly ?R x = 0}"
  proof
    fix x
    assume x_in: "x \<in> (\<lambda>idx. h ^ idx * shift) ` ?A"
    then obtain idx where idx_in: "idx \<in> ?A"
      and x_eq: "x = h ^ idx * shift"
      by blast
    have idx_sample: "idx \<in> query_sample_space"
      by (rule set_mp[OF A_subset idx_in])
    have idx_bound: "idx < clength * scale"
      by (rule query_sample_space_less_domain[OF idx_sample])
    have value_eq: "trace_table ! idx = trace_table' ! idx"
      using idx_in
      unfolding trace_table_base_agreement_indices_def
      by simp
    have left:
      "trace_table ! idx = poly f (h ^ idx * shift)"
      using trace_table eval_domain_nth[OF idx_bound] idx_bound
        eval_domain_length by simp
    have right:
      "trace_table' ! idx = poly f' (h ^ idx * shift)"
      using trace_table' eval_domain_nth[OF idx_bound] idx_bound
        eval_domain_length by simp
    have "poly f (h ^ idx * shift) = poly f' (h ^ idx * shift)"
      using value_eq left right by simp
    then show "x \<in> {x. poly ?R x = 0}"
      using x_eq by simp
  qed
  have "card ?A = card ((\<lambda>idx. h ^ idx * shift) ` ?A)"
    by (simp add: card_image inj)
  also have "... \<le> card {x. poly ?R x = 0}"
    by (rule card_mono[OF poly_roots_finite[OF residual_nonzero]
          image_subset])
  also have "... \<le> degree ?R"
    by (rule card_poly_roots_bound[OF residual_nonzero])
  also have "... < clength"
    using deg_f deg_f' by (simp add: degree_diff_less)
  finally show ?thesis .
qed

lemma trace_table_base_agreement_query_lists_exact_product_bound:
  assumes trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows
    "nnreal
        (card
          (trace_table_base_agreement_query_lists trace_table trace_table')) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds \<le>
      nnreal (clength ^ rounds) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof -
  have agreement_le:
    "card
        (trace_table_base_agreement_indices trace_table trace_table') \<le>
      clength"
    using trace_table_base_agreement_indices_card_bound
        [OF trace_low trace'_low distinct]
    by simp
  have query_lists_le:
    "card
        (trace_table_base_agreement_query_lists trace_table trace_table') \<le>
      clength ^ rounds"
    unfolding card_trace_table_base_agreement_query_lists
    by (rule power_mono[OF agreement_le]; simp)
  have cast_le:
    "nnreal
        (card
          (trace_table_base_agreement_query_lists trace_table trace_table')) \<le>
      nnreal (clength ^ rounds)"
    using query_lists_le by simp
  show ?thesis
    by (rule mult_right_mono[OF cast_le]) simp
qed

lemma trace_table_base_agreement_indices_fraction_bound:
  assumes trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows "nnreal
      (card
        (trace_table_base_agreement_indices trace_table trace_table')) /
      nnreal (card query_sample_space) \<le>
    nnreal clength / nnreal (card query_sample_space)"
proof -
  have card_le:
    "card
        (trace_table_base_agreement_indices trace_table trace_table') \<le>
      clength"
    using trace_table_base_agreement_indices_card_bound
        [OF trace_low trace'_low distinct]
    by simp
  show ?thesis
    by (rule nnreal_nat_divide_right_mono[OF card_le])
qed

end

end
