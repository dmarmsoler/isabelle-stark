(*  Title:      Stark/Soundness_Partial_Initial_Aligned.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Partial_Initial_Aligned
  imports Soundness_Query_Opening_Consistency
begin

text \<open>
  Aligned partial initial-opening evidence.

  The predicate \<^term>\<open>accepted_with_partial_initial_openings\<close> records trace
  and composition openings with separate query-index lists.  For query
  soundness bounds this theory packages the stronger verifier-local fact that
  both opening families come from the same query-round execution and therefore
  use the same sampled query indices.
\<close>

context soundness
begin

definition accepted_with_partial_initial_openings_aligned
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> bool"
where
  "accepted_with_partial_initial_openings_aligned s out fr f_fri_roots
      f_final as dg composition_fri_roots final query_idxs trace_openings
      composition_openings \<longleftrightarrow>
    accepted out \<and>
    composition_fri_roots \<noteq> [] \<and>
    (\<exists>rest.
      verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest) \<and>
    accepted_with_partial_trace_openings s out fr query_idxs
      trace_openings \<and>
    accepted_with_partial_composition_openings s out
      (hd composition_fri_roots) query_idxs composition_openings"

lemma accepted_with_partial_initial_openings_aligned_imp_unaligned:
  assumes
    "accepted_with_partial_initial_openings_aligned s out fr f_fri_roots
      f_final as dg composition_fri_roots final query_idxs trace_openings
      composition_openings"
  shows
    "accepted_with_partial_initial_openings s out fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings query_idxs
      composition_openings"
  using assms
  unfolding accepted_with_partial_initial_openings_aligned_def
    accepted_with_partial_initial_openings_def
  by blast

lemma accepted_with_partial_initial_openings_aligned_shapes:
  assumes
    "accepted_with_partial_initial_openings_aligned s out fr f_fri_roots
      f_final as dg composition_fri_roots final query_idxs trace_openings
      composition_openings"
  shows "composition_fri_roots \<noteq> []"
    and "\<exists>rest. verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    and "accepted_with_partial_trace_openings s out fr query_idxs
      trace_openings"
    and "accepted_with_partial_composition_openings s out
      (hd composition_fri_roots) query_idxs composition_openings"
  using assms
  unfolding accepted_with_partial_initial_openings_aligned_def by blast+

lemma accepted_with_partial_initial_openings_aligned_candidates_if_no_partial_merkle_bad:
  assumes partial:
      "accepted_with_partial_initial_openings_aligned s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
  shows "\<exists>trace_table composition_table.
    partial_trace_table_candidate trace_table trace_openings \<and>
    partial_composition_table_candidate composition_table
      composition_openings"
proof -
  have unaligned:
    "accepted_with_partial_initial_openings s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings query_idxs
      composition_openings"
    by (rule accepted_with_partial_initial_openings_aligned_imp_unaligned
        [OF partial])
  show ?thesis
    by (rule
        accepted_with_partial_initial_openings_candidates_if_no_partial_merkle_bad
        [OF unaligned no_bad])
qed

lemma verify_monad_accepted_with_partial_initial_openings_aligned:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header0:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
  obtains query_idxs trace_openings composition_openings where
    "accepted_with_partial_initial_openings_aligned s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    "\<And>i. i < rounds \<Longrightarrow>
      partial_query_round_consistent trace_openings composition_openings as i
        (query_idxs ! i)"
proof -
  from verify_monad_header_extraction[OF outcome]
  obtain fr' f_fl f_final' as' dg' fl final' query_state where
    header:
      "verifier_header_transcript s fr' (map snd f_fl) f_final' as' dg'
        (map snd fl) final' (PTranscript query_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl f_final' as' fl
                final') rounds)
            query_state)"
    by metis
  have eqs:
    "fr' = fr \<and>
     map snd f_fl = f_fri_roots \<and>
     f_final' = f_final \<and>
     as' = as \<and>
     dg' = dg \<and>
     map snd fl = composition_fri_roots \<and>
     final' = final \<and>
     PTranscript query_state = rest"
    using verifier_header_transcript_unique[OF header header0] by simp
  have fl_nonempty: "fl \<noteq> []"
    using comp_nonempty eqs by (cases fl) simp_all
  then obtain b composition_root fl_tail where fl_eq:
    "fl = (b, composition_root) # fl_tail"
    by (cases fl) auto
  have root_eq: "composition_root = hd composition_fri_roots"
  proof -
    have "composition_root # map snd fl_tail = composition_fri_roots"
      using eqs unfolding fl_eq by simp
    then have "hd composition_fri_roots = composition_root"
      by (metis list.sel(1))
    then show ?thesis
      by simp
  qed
  obtain query_idxs trace_openings composition_openings where
    len_query_idxs: "length query_idxs = rounds"
    and len_trace: "length trace_openings = rounds"
    and len_comp: "length composition_openings = rounds"
    and trace_indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
    and trace_tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table fr' (scale * clength)
          (trace_openings ! i) final_state"
    and comp_tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table composition_root (scale * clength)
          (composition_openings ! i) final_state"
    and comp_indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (composition_openings ! i) =
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)]"
    and consistent:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_query_round_consistent trace_openings composition_openings
          as' i (query_idxs ! i)"
  proof (rule
      ntimes_verifier_query_rounds_aligned_authenticated_openings_consistent
        [OF fl_eq query_out])
    fix query_idxs trace_openings composition_openings
    assume len_query_idxs: "length query_idxs = rounds"
      and len_trace: "length trace_openings = rounds"
      and len_comp: "length composition_openings = rounds"
      and trace_indices:
        "\<And>i. i < rounds \<Longrightarrow>
          map opening_index (trace_openings ! i) =
            powers_scaled (query_idxs ! i)"
      and trace_tables:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_authenticated_table fr' (scale * clength)
            (trace_openings ! i) final_state"
      and comp_tables:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_authenticated_table composition_root (scale * clength)
            (composition_openings ! i) final_state"
      and comp_indices:
        "\<And>i. i < rounds \<Longrightarrow>
          map opening_index (composition_openings ! i) =
            [query_idxs ! i,
             fri_sibling_index (scale * clength) (query_idxs ! i)]"
      and consistent:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_query_round_consistent trace_openings composition_openings
            as' i (query_idxs ! i)"
    show ?thesis
      by (rule that[OF len_query_idxs len_trace len_comp trace_indices
            trace_tables comp_tables comp_indices consistent])
  qed
  have consistent_as:
    "\<And>i. i < rounds \<Longrightarrow>
      partial_query_round_consistent trace_openings composition_openings as i
        (query_idxs ! i)"
    using consistent eqs by simp
  have trace_partial:
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr query_idxs trace_openings"
  proof -
    have all_indices:
      "\<forall>i < rounds.
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
      using trace_indices by blast
    have all_tables:
      "\<forall>i < rounds.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) final_state"
      using trace_tables eqs by simp
    show ?thesis
      unfolding accepted_with_partial_trace_openings_def accepted_def
      by (intro conjI exI[of _ result] exI[of _ final_state])
        (use len_query_idxs len_trace all_indices all_tables in simp_all)
  qed
  have comp_partial:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots) query_idxs
      composition_openings"
  proof -
    have all_indices:
      "\<forall>i < rounds.
        map opening_index (composition_openings ! i) =
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)]"
      using comp_indices by blast
    have all_tables:
      "\<forall>i < rounds.
        partial_authenticated_table (hd composition_fri_roots)
          (scale * clength) (composition_openings ! i) final_state"
      using comp_tables root_eq by simp
    show ?thesis
      unfolding accepted_with_partial_composition_openings_def accepted_def
      by (intro conjI exI[of _ result] exI[of _ final_state])
        (use len_query_idxs len_comp all_indices all_tables in simp_all)
  qed
  have aligned:
    "accepted_with_partial_initial_openings_aligned s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
  proof -
    have accepted_out: "accepted (Some (result, final_state))"
      using trace_partial
      by (rule accepted_with_partial_trace_openings_imp_accepted)
    show ?thesis
    unfolding accepted_with_partial_initial_openings_aligned_def
    by (intro conjI exI[of _ rest])
        (use accepted_out comp_nonempty header0 trace_partial comp_partial in
          simp_all)
  qed
  show ?thesis
    by (rule that[OF aligned consistent_as])
qed

end

end
