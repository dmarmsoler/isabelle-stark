(*  Title:      Stark/Soundness_Query_Opening_Consistency.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Query_Opening_Consistency
  imports
    Soundness_Query_Opening_Extraction
    Soundness_Staged_Partial_Query
begin

text \<open>
  Verifier-local query-opening consistency facts.  These lemmas package the
  composition check enforced by a successful query round together with the
  authenticated openings extracted from that round.
\<close>

context soundness
begin

lemma verifier_query_round_after_index_authenticated_openings_consistent:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
  obtains idx trace_openings composition_openings where
    "idx = index (to_nat raw)"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    "partial_query_openings_consistent trace_openings composition_openings
      as idx"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have idx_sample: "?idx \<in> query_sample_space"
    using index_less_query_sample_space
    unfolding query_sample_space_def by simp
  from check_decommit_on_query_authenticated_openings
      [OF idx_sample query_decommit]
  obtain trace_openings where
    trace_values: "map opening_value trace_openings = fv"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled ?idx"
    and trace_table_s1:
      "partial_authenticated_table fr (scale * clength) trace_openings s1"
    by blast
  from receive_query_commits_layers_outcome[OF trace_fri]
  obtain trace_layer_chunks trace_fri_chunk where s1_s2: "s1 \<le> s2"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  have comp_steps:
    "receive_query_commits fl =
      fri_layer_opening_step (b, composition_root) #
        receive_query_commits fl_tail"
    unfolding fl_eq receive_query_commits_def fri_layer_opening_step_def
    by simp
  from comp_fri[unfolded comp_steps]
  obtain out1 s_head where
    head:
      "Some (out1, s_head) \<in>
        set_dist
          (execute
            (fri_layer_opening_step (b, composition_root)
              (?idx, cp_eval as fv (h ^ ?idx * shift),
                clength * scale, 1)) s3)"
    and tail:
      "Some (c_out, s4) \<in>
        set_dist (execute (mfold out1 (receive_query_commits fl_tail))
          s_head)"
    by (auto elim!: set_dist_bindE)
  have len_pos: "0 < clength * scale"
    using eval_domain_nontrivial by linarith
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  from query_opening_fri_layer_opening_step_partial_authenticated_table_first_value
      [OF len_pos idx_bound head]
  obtain composition_openings where
    comp_table_head:
      "partial_authenticated_table composition_root (clength * scale)
        composition_openings s_head"
    and comp_indices0:
      "map opening_index composition_openings =
        [?idx, (?idx + (clength * scale) div 2) mod (clength * scale)]"
    and comp_len: "length composition_openings = 2"
    and comp_value:
      "opening_value (composition_openings ! 0) =
        cp_eval as fv (h ^ ?idx * shift)"
    by blast
  from fri_layer_opening_step_outcome[OF head]
  have s3_s_head: "s3 \<le> s_head"
    by blast
  obtain i1 x1 len1 pw1 where out1_eq: "out1 = (i1, x1, len1, pw1)"
    by (cases out1)
  from receive_query_commits_layers_outcome[OF tail[unfolded out1_eq]]
  obtain tail_layer_chunks tail_chunk where s_head_s4: "s_head \<le> s4"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  have s1_t: "s1 \<le> t"
    using s1_s2 s3_s_head s_head_s4 unfolding s3_eq t_eq
    by (meson hash_ext_trans)
  have trace_table_t:
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    by (rule partial_authenticated_table_mono[OF trace_table_s1 s1_t])
  have comp_table_t:
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    using partial_authenticated_table_mono[OF comp_table_head s_head_s4]
    unfolding t_eq by (simp add: mult.commute)
  have comp_indices:
    "map opening_index composition_openings =
      [?idx, fri_sibling_index (scale * clength) ?idx]"
    using comp_indices0
    unfolding fri_sibling_index_def
    by (simp add: mult.commute)
  have consistent:
    "partial_query_openings_consistent trace_openings composition_openings
      as ?idx"
    by (rule partial_query_openings_consistentI
        [OF idx_sample trace_indices comp_indices])
      (use comp_value trace_values in simp)
  show ?thesis
    by (rule that[OF refl trace_indices trace_table_t comp_table_t
          comp_indices consistent])
qed

lemma verifier_query_round_after_index_empty_composition_consistent:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_empty: "fl = []"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
  obtains idx trace_openings where
    "idx = index (to_nat raw)"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "cp_eval as (map opening_value trace_openings) (h ^ idx * shift) =
      final"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have idx_sample: "?idx \<in> query_sample_space"
    using index_less_query_sample_space
    unfolding query_sample_space_def by simp
  from check_decommit_on_query_authenticated_openings
      [OF idx_sample query_decommit]
  obtain trace_openings where
    trace_values: "map opening_value trace_openings = fv"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled ?idx"
    and trace_table_s1:
      "partial_authenticated_table fr (scale * clength) trace_openings s1"
    by blast
  from receive_query_commits_layers_outcome[OF trace_fri]
  obtain trace_layer_chunks trace_fri_chunk where s1_s2: "s1 \<le> s2"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  have comp_out:
    "c_out =
      (?idx, cp_eval as fv (h ^ ?idx * shift), clength * scale, 1) \<and>
     s4 = s3"
    using comp_fri fl_empty
    unfolding receive_query_commits_def by simp
  have final_eq:
    "cp_eval as fv (h ^ ?idx * shift) = final"
  proof (rule ccontr)
    assume "\<not> cp_eval as fv (h ^ ?idx * shift) = final"
    then have "Some ((), t) \<in> set_dist (execute throw s3)"
      using assert_comp comp_out unfolding assert_def by simp
    then show False
      by (simp add: throw_no_outcome)
  qed
  have t_eq: "t = s4"
    using assert_comp comp_out final_eq unfolding assert_def by simp
  have t_s2: "t = s2"
    using s3_eq t_eq comp_out by simp
  have s1_t: "s1 \<le> t"
    using s1_s2 t_s2 by simp
  have trace_table_t:
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    by (rule partial_authenticated_table_mono[OF trace_table_s1 s1_t])
  have final_eq':
    "cp_eval as (map opening_value trace_openings) (h ^ ?idx * shift) =
      final"
    using final_eq trace_values by simp
  show ?thesis
    by (rule that[OF refl trace_indices trace_table_t final_eq'])
qed

lemma verifier_query_round_program_authenticated_openings_consistent_with_lookup:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx trace_openings composition_openings where
    "idx = index (to_nat raw)"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    "partial_query_openings_consistent trace_openings composition_openings
      as idx"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where rand:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  have lookup_s0:
    "fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF rand] by simp
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using verifier_query_round_after_index_program_preserves_query_lookup
        [OF tail, of "PQueryCounter s" "PState s"] lookup_s0
    by simp
  show ?thesis
  proof (rule verifier_query_round_after_index_authenticated_openings_consistent
      [OF fl_eq tail])
    fix idx trace_openings composition_openings
    assume idx_eq: "idx = index (to_nat raw)"
      and trace_indices:
        "map opening_index trace_openings = powers_scaled idx"
      and trace_table:
        "partial_authenticated_table fr (scale * clength) trace_openings t"
      and comp_table:
        "partial_authenticated_table composition_root (scale * clength)
          composition_openings t"
      and comp_indices:
        "map opening_index composition_openings =
          [idx, fri_sibling_index (scale * clength) idx]"
      and consistent:
        "partial_query_openings_consistent trace_openings
          composition_openings as idx"
    show ?thesis
      by (rule that[OF idx_eq trace_indices trace_table comp_table
            comp_indices consistent lookup_t])
  qed
qed

lemma verifier_query_round_program_empty_composition_consistent_with_lookup:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_empty: "fl = []"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx trace_openings where
    "idx = index (to_nat raw)"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "cp_eval as (map opening_value trace_openings) (h ^ idx * shift) =
      final"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where rand:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  have lookup_s0:
    "fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF rand] by simp
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using verifier_query_round_after_index_program_preserves_query_lookup
        [OF tail, of "PQueryCounter s" "PState s"] lookup_s0
    by simp
  show ?thesis
  proof (rule verifier_query_round_after_index_empty_composition_consistent
      [OF fl_empty tail])
    fix idx trace_openings
    assume idx_eq: "idx = index (to_nat raw)"
      and trace_indices:
        "map opening_index trace_openings = powers_scaled idx"
      and trace_table:
        "partial_authenticated_table fr (scale * clength) trace_openings t"
      and consistent:
        "cp_eval as (map opening_value trace_openings) (h ^ idx * shift) =
          final"
    show ?thesis
      by (rule that[OF idx_eq trace_indices trace_table consistent
            lookup_t])
  qed
qed

lemma ntimes_verifier_query_rounds_empty_composition_consistent:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_empty: "fl = []"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
  obtains raw_idxs query_idxs trace_openings where
    "length raw_idxs = n"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length trace_openings = n"
    "\<And>i. i < n \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    "\<And>i. i < n \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) t"
    "\<And>i. i < n \<Longrightarrow>
      cp_eval as (map opening_value (trace_openings ! i))
        (h ^ (query_idxs ! i) * shift) = final"
proof -
  have
    "\<exists>raw_idxs query_idxs trace_openings.
      length raw_idxs = n \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length trace_openings = n \<and>
      (\<forall>i < n.
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)) \<and>
      (\<forall>i < n.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) t) \<and>
      (\<forall>i < n.
        cp_eval as (map opening_value (trace_openings ! i))
          (h ^ (query_idxs ! i) * shift) = final)"
    using outcome
  proof (induction n arbitrary: s results t)
    case 0
    then show ?case
      by (intro exI[of _ "[]"]) simp
  next
    case (Suc n)
    from Suc.prems obtain u results' s1 where
      head:
        "Some (u, s1) \<in>
          set_dist
            (execute
              (verifier_query_round_program fr f_fl f_final as fl final) s)"
      and tail:
        "Some (results', t) \<in>
          set_dist
            (execute
              (ntimes
                (verifier_query_round_program fr f_fl f_final as fl final)
                n) s1)"
      by (auto elim!: set_dist_bindE)
    have u_eq: "u = ()"
      by (cases u) simp
    from verifier_query_round_program_empty_composition_consistent_with_lookup
        [OF fl_empty head[unfolded u_eq]]
    obtain raw idx openings where
      idx_eq: "idx = index (to_nat raw)"
      and idx_openings: "map opening_index openings = powers_scaled idx"
      and table_s1:
        "partial_authenticated_table fr (scale * clength) openings s1"
      and consistent_head:
        "cp_eval as (map opening_value openings) (h ^ idx * shift) =
          final"
      by blast
    from Suc.IH[OF tail] obtain raw_tail idx_tail openings_tail where
      len_raw_tail: "length raw_tail = n"
      and idx_tail_eq:
        "idx_tail = map (\<lambda>raw. index (to_nat raw)) raw_tail"
      and len_openings_tail: "length openings_tail = n"
      and tail_indices:
        "\<forall>i < n.
          map opening_index (openings_tail ! i) =
            powers_scaled (idx_tail ! i)"
      and tail_tables:
        "\<forall>i < n.
          partial_authenticated_table fr (scale * clength)
            (openings_tail ! i) t"
      and tail_consistent:
        "\<forall>i < n.
          cp_eval as (map opening_value (openings_tail ! i))
            (h ^ (idx_tail ! i) * shift) = final"
      by blast
    have s1_t: "s1 \<le> t"
      using ntimes_verifier_query_rounds_outcome[OF tail] by blast
    have table_t:
      "partial_authenticated_table fr (scale * clength) openings t"
      by (rule partial_authenticated_table_mono[OF table_s1 s1_t])
    let ?raws = "raw # raw_tail"
    let ?idxs = "idx # idx_tail"
    let ?openings = "openings # openings_tail"
    have idxs_eq:
      "?idxs = map (\<lambda>raw. index (to_nat raw)) ?raws"
      using idx_eq idx_tail_eq by simp
    have indices_all:
      "\<forall>i < Suc n.
        map opening_index (?openings ! i) =
          powers_scaled (?idxs ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < Suc n"
      show "map opening_index (?openings ! i) =
          powers_scaled (?idxs ! i)"
      proof (cases i)
        case 0
        then show ?thesis
          using idx_openings by simp
      next
        case (Suc j)
        then show ?thesis
          using i_bound tail_indices by simp
      qed
    qed
    have tables_all:
      "\<forall>i < Suc n.
        partial_authenticated_table fr (scale * clength)
          (?openings ! i) t"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < Suc n"
      show "partial_authenticated_table fr (scale * clength)
          (?openings ! i) t"
      proof (cases i)
        case 0
        then show ?thesis
          using table_t by simp
      next
        case (Suc j)
        then show ?thesis
          using i_bound tail_tables by simp
      qed
    qed
    have consistent_all:
      "\<forall>i < Suc n.
        cp_eval as (map opening_value (?openings ! i))
          (h ^ (?idxs ! i) * shift) = final"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < Suc n"
      show "cp_eval as (map opening_value (?openings ! i))
          (h ^ (?idxs ! i) * shift) = final"
      proof (cases i)
        case 0
        then show ?thesis
          using consistent_head by simp
      next
        case (Suc j)
        then show ?thesis
          using i_bound tail_consistent by simp
      qed
    qed
    show ?case
      apply (intro exI[of _ ?raws] exI[of _ ?idxs]
          exI[of _ ?openings] conjI)
          apply (simp add: len_raw_tail)
         apply (rule idxs_eq)
        apply (simp add: len_openings_tail)
       apply (rule indices_all)
      apply (rule tables_all)
      apply (rule consistent_all)
      done
  qed
  then obtain raw_idxs query_idxs trace_openings where
    len_raw: "length raw_idxs = n"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_trace: "length trace_openings = n"
    and indices:
      "\<forall>i < n.
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
    and tables:
      "\<forall>i < n.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) t"
    and consistent:
      "\<forall>i < n.
        cp_eval as (map opening_value (trace_openings ! i))
          (h ^ (query_idxs ! i) * shift) = final"
    by blast
  show ?thesis
    by (rule that[OF len_raw query_idxs_eq len_trace])
      (use indices tables consistent in auto)
qed

lemma ntimes_verifier_query_rounds_empty_composition_consistent_with_lookup:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_empty: "fl = []"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
  obtains raw_idxs query_idxs query_chunks trace_openings where
    "length raw_idxs = n"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length query_chunks = n"
    "length trace_openings = n"
    "\<And>i. i < n \<Longrightarrow>
      fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks (PState s) query_chunks i)) =
      Some (raw_idxs ! i)"
    "\<And>i. i < n \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    "\<And>i. i < n \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) t"
    "\<And>i. i < n \<Longrightarrow>
      cp_eval as (map opening_value (trace_openings ! i))
        (h ^ (query_idxs ! i) * shift) = final"
proof -
  have
    "\<exists>raw_idxs query_idxs query_chunks trace_openings.
      length raw_idxs = n \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length query_chunks = n \<and>
      length trace_openings = n \<and>
      (\<forall>i < n.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) query_chunks i)) =
        Some (raw_idxs ! i)) \<and>
      (\<forall>i < n.
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)) \<and>
      (\<forall>i < n.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) t) \<and>
      (\<forall>i < n.
        cp_eval as (map opening_value (trace_openings ! i))
          (h ^ (query_idxs ! i) * shift) = final)"
    using outcome
  proof (induction n arbitrary: s results t)
    case 0
    then show ?case
      by (intro exI[of _ "[]"]) simp
  next
    case (Suc n)
    from Suc.prems obtain u results' s1 where
      head:
        "Some (u, s1) \<in>
          set_dist
            (execute
              (verifier_query_round_program fr f_fl f_final as fl final) s)"
      and tail:
        "Some (results', t) \<in>
          set_dist
            (execute
              (ntimes
                (verifier_query_round_program fr f_fl f_final as fl final)
                n) s1)"
      by (auto elim!: set_dist_bindE)
    have u_eq: "u = ()"
      by (cases u) simp
    from verifier_query_round_program_empty_composition_consistent_with_lookup
        [OF fl_empty head[unfolded u_eq]]
    obtain raw idx openings where
      idx_eq: "idx = index (to_nat raw)"
      and idx_openings: "map opening_index openings = powers_scaled idx"
      and table_s1:
        "partial_authenticated_table fr (scale * clength) openings s1"
      and consistent_head:
        "cp_eval as (map opening_value openings) (h ^ idx * shift) =
          final"
      and lookup_s1:
        "fmlookup (HashMap s1)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
      by blast
    from verifier_query_round_program_outcome[OF head[unfolded u_eq]]
    obtain raw' idx' chunk where
      idx'_eq: "idx' = index (to_nat raw')"
      and st_s1: "PState s1 = foldl concat (PState s) chunk"
      and query_count_s1: "PQueryCounter s1 = Suc (PQueryCounter s)"
      and lookup_s1':
        "fmlookup (HashMap s1)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw'"
      by blast
    have raw'_eq: "raw' = raw"
      using lookup_s1 lookup_s1' by simp
    from Suc.IH[OF tail] obtain raw_tail idx_tail chunk_tail openings_tail
      where len_raw_tail: "length raw_tail = n"
      and idx_tail_eq:
        "idx_tail = map (\<lambda>raw. index (to_nat raw)) raw_tail"
      and len_chunk_tail: "length chunk_tail = n"
      and len_openings_tail: "length openings_tail = n"
      and lookup_tail:
        "\<forall>i < n.
          fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s1 + i)
              (state_after_query_chunks (PState s1) chunk_tail i)) =
          Some (raw_tail ! i)"
      and tail_indices:
        "\<forall>i < n.
          map opening_index (openings_tail ! i) =
            powers_scaled (idx_tail ! i)"
      and tail_tables:
        "\<forall>i < n.
          partial_authenticated_table fr (scale * clength)
            (openings_tail ! i) t"
      and tail_consistent:
        "\<forall>i < n.
          cp_eval as (map opening_value (openings_tail ! i))
            (h ^ (idx_tail ! i) * shift) = final"
      by blast
    have s1_t: "s1 \<le> t"
      using ntimes_verifier_query_rounds_outcome[OF tail] by blast
    have table_t:
      "partial_authenticated_table fr (scale * clength) openings t"
      by (rule partial_authenticated_table_mono[OF table_s1 s1_t])
    have lookup_head_t:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
      using hash_extension_lookup[OF lookup_s1 s1_t] .
    let ?raws = "raw # raw_tail"
    let ?idxs = "idx # idx_tail"
    let ?chunks = "chunk # chunk_tail"
    let ?openings = "openings # openings_tail"
    have idxs_eq:
      "?idxs = map (\<lambda>raw. index (to_nat raw)) ?raws"
      using idx_eq idx_tail_eq by simp
    have state_shift:
      "\<And>i. state_after_query_chunks (PState s) ?chunks (Suc i) =
        state_after_query_chunks (PState s1) chunk_tail i"
      using st_s1 unfolding state_after_query_chunks_def by simp
    have lookup_all:
      "\<forall>i < Suc n.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) ?chunks i)) =
        Some (?raws ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < Suc n"
      show "fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) ?chunks i)) =
        Some (?raws ! i)"
      proof (cases i)
        case 0
        then show ?thesis
          using lookup_head_t unfolding state_after_query_chunks_def by simp
      next
        case (Suc j)
        then show ?thesis
          using i_bound lookup_tail query_count_s1 state_shift[of j] by simp
      qed
    qed
    have indices_all:
      "\<forall>i < Suc n.
        map opening_index (?openings ! i) =
          powers_scaled (?idxs ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < Suc n"
      show "map opening_index (?openings ! i) =
          powers_scaled (?idxs ! i)"
      proof (cases i)
        case 0
        then show ?thesis
          using idx_openings by simp
      next
        case (Suc j)
        then show ?thesis
          using i_bound tail_indices by simp
      qed
    qed
    have tables_all:
      "\<forall>i < Suc n.
        partial_authenticated_table fr (scale * clength)
          (?openings ! i) t"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < Suc n"
      show "partial_authenticated_table fr (scale * clength)
          (?openings ! i) t"
      proof (cases i)
        case 0
        then show ?thesis
          using table_t by simp
      next
        case (Suc j)
        then show ?thesis
          using i_bound tail_tables by simp
      qed
    qed
    have consistent_all:
      "\<forall>i < Suc n.
        cp_eval as (map opening_value (?openings ! i))
          (h ^ (?idxs ! i) * shift) = final"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < Suc n"
      show "cp_eval as (map opening_value (?openings ! i))
          (h ^ (?idxs ! i) * shift) = final"
      proof (cases i)
        case 0
        then show ?thesis
          using consistent_head by simp
      next
        case (Suc j)
        then show ?thesis
          using i_bound tail_consistent by simp
      qed
    qed
    show ?case
      by (intro exI[of _ ?raws] exI[of _ ?idxs] exI[of _ ?chunks]
          exI[of _ ?openings] conjI)
        (use len_raw_tail idxs_eq len_chunk_tail len_openings_tail
          lookup_all indices_all tables_all consistent_all in simp_all)
  qed
  then obtain raw_idxs query_idxs query_chunks trace_openings where
    len_raw: "length raw_idxs = n"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = n"
    and len_trace: "length trace_openings = n"
    and lookup:
      "\<forall>i < n.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) query_chunks i)) =
        Some (raw_idxs ! i)"
    and indices:
      "\<forall>i < n.
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
    and tables:
      "\<forall>i < n.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) t"
    and consistent:
      "\<forall>i < n.
        cp_eval as (map opening_value (trace_openings ! i))
          (h ^ (query_idxs ! i) * shift) = final"
    by blast
  show ?thesis
    by (rule that[OF len_raw query_idxs_eq len_chunks len_trace])
      (use lookup indices tables consistent in auto)
qed

lemma ntimes_verifier_query_rounds_empty_composition_first_consistent:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_empty: "fl = []"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            s)"
  obtains raw trace_openings where
    "map opening_index trace_openings =
      powers_scaled (index (to_nat raw))"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "cp_eval as (map opening_value trace_openings)
      (h ^ index (to_nat raw) * shift) = final"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  from outcome obtain u results' s1 where
    head:
      "Some (u, s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and tail:
      "Some (results', t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              (rounds - Suc 0))
            s1)"
    using rounds_positive
    by (cases rounds) (auto elim!: set_dist_bindE)
  have u_eq: "u = ()"
    by (cases u) simp
  from verifier_query_round_program_empty_composition_consistent_with_lookup
      [OF fl_empty head[unfolded u_eq]]
  obtain raw idx trace_openings where idx_eq:
      "idx = index (to_nat raw)"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and trace_table_s1:
      "partial_authenticated_table fr (scale * clength) trace_openings s1"
    and consistent:
      "cp_eval as (map opening_value trace_openings) (h ^ idx * shift) =
        final"
    and lookup_s1:
      "fmlookup (HashMap s1)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by blast
  have s1_t: "s1 \<le> t"
    using ntimes_verifier_query_rounds_outcome[OF tail] by blast
  have trace_table_t:
      "partial_authenticated_table fr (scale * clength) trace_openings t"
    by (rule partial_authenticated_table_mono[OF trace_table_s1 s1_t])
  have lookup_t:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using hash_extension_lookup[OF lookup_s1 s1_t] .
  show ?thesis
    by (rule that[of trace_openings raw])
      (use idx_eq trace_indices trace_table_t consistent lookup_t in simp_all)
qed

lemma ntimes_verifier_query_rounds_authenticated_openings_consistent_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
    and i_bound: "i < n"
  obtains raw idx prefix_chunks trace_openings composition_openings where
    "idx = index (to_nat raw)"
    "length prefix_chunks = i"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    "partial_query_openings_consistent trace_openings composition_openings
      as idx"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s + i)
        (state_after_query_chunks (PState s) prefix_chunks i)) = Some raw"
proof -
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix round suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) i)
            s)"
    and round:
      "Some (round, s_suc) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              (n - Suc i))
            s_suc)"
    by blast
  have round_unit: "round = ()"
    by (cases round) simp
  show ?thesis
  proof (rule
      verifier_query_round_program_authenticated_openings_consistent_with_lookup
        [OF fl_eq round[unfolded round_unit]])
    fix raw idx trace_openings composition_openings
    assume idx_eq: "idx = index (to_nat raw)"
      and trace_indices:
        "map opening_index trace_openings = powers_scaled idx"
      and trace_table_suc:
        "partial_authenticated_table fr (scale * clength)
          trace_openings s_suc"
      and comp_table_suc:
        "partial_authenticated_table composition_root (scale * clength)
          composition_openings s_suc"
      and comp_indices:
        "map opening_index composition_openings =
          [idx, fri_sibling_index (scale * clength) idx]"
      and consistent:
        "partial_query_openings_consistent trace_openings
          composition_openings as idx"
      and lookup_suc:
        "fmlookup (HashMap s_suc)
          (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw"
    show ?thesis
    proof (rule query_opening_ntimes_prefix_state_alignment[OF prefix])
      fix prefix_chunks
      assume len_chunks: "length prefix_chunks = i"
        and state_i:
          "PState s_i =
            state_after_query_chunks (PState s) prefix_chunks i"
        and counter_i: "PQueryCounter s_i = PQueryCounter s + i"
      have suffix_ext: "s_suc \<le> t"
        by (rule query_opening_ntimes_suffix_extends[OF suffix])
      have trace_table_t:
        "partial_authenticated_table fr (scale * clength)
          trace_openings t"
        by (rule
            partial_authenticated_table_mono[OF trace_table_suc suffix_ext])
      have comp_table_t:
        "partial_authenticated_table composition_root (scale * clength)
          composition_openings t"
        by (rule
            partial_authenticated_table_mono[OF comp_table_suc suffix_ext])
      have lookup_t:
        "fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) prefix_chunks i)) =
          Some raw"
        using hash_extension_lookup[OF lookup_suc suffix_ext]
        unfolding counter_i state_i .
      show ?thesis
        by (rule that[OF idx_eq len_chunks trace_indices trace_table_t
              comp_table_t comp_indices consistent lookup_t])
    qed
  qed
qed

lemma ntimes_verifier_query_rounds_empty_composition_consistent_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_empty: "fl = []"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
    and i_bound: "i < n"
  obtains raw idx prefix_chunks trace_openings where
    "idx = index (to_nat raw)"
    "length prefix_chunks = i"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "cp_eval as (map opening_value trace_openings) (h ^ idx * shift) =
      final"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s + i)
        (state_after_query_chunks (PState s) prefix_chunks i)) = Some raw"
proof -
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix round suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) i)
            s)"
    and round:
      "Some (round, s_suc) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              (n - Suc i))
            s_suc)"
    by blast
  have round_unit: "round = ()"
    by (cases round) simp
  show ?thesis
  proof (rule
      verifier_query_round_program_empty_composition_consistent_with_lookup
        [OF fl_empty round[unfolded round_unit]])
    fix raw idx trace_openings
    assume idx_eq: "idx = index (to_nat raw)"
      and trace_indices:
        "map opening_index trace_openings = powers_scaled idx"
      and trace_table_suc:
        "partial_authenticated_table fr (scale * clength)
          trace_openings s_suc"
      and consistent:
        "cp_eval as (map opening_value trace_openings) (h ^ idx * shift) =
          final"
      and lookup_suc:
        "fmlookup (HashMap s_suc)
          (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw"
    show ?thesis
    proof (rule query_opening_ntimes_prefix_state_alignment[OF prefix])
      fix prefix_chunks
      assume len_chunks: "length prefix_chunks = i"
        and state_i:
          "PState s_i =
            state_after_query_chunks (PState s) prefix_chunks i"
        and counter_i: "PQueryCounter s_i = PQueryCounter s + i"
      have suffix_ext: "s_suc \<le> t"
        by (rule query_opening_ntimes_suffix_extends[OF suffix])
      have trace_table_t:
        "partial_authenticated_table fr (scale * clength)
          trace_openings t"
        by (rule
            partial_authenticated_table_mono[OF trace_table_suc suffix_ext])
      have lookup_t:
        "fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) prefix_chunks i)) =
          Some raw"
        using hash_extension_lookup[OF lookup_suc suffix_ext]
        unfolding counter_i state_i .
      show ?thesis
        by (rule that[OF idx_eq len_chunks trace_indices trace_table_t
              consistent lookup_t])
    qed
  qed
qed

lemma ntimes_verifier_query_rounds_selected_authenticated_chunks_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
    and i_bound: "i < n"
  obtains raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks trace_openings composition_openings where
    "idx = index (to_nat raw)"
    "length prefix_query_idxs = i"
    "length prefix_chunks = i"
    "length suffix_query_idxs = n - Suc i"
    "length suffix_chunks = n - Suc i"
    "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    "\<And>j. j < i \<Longrightarrow>
      verifier_query_round_chunk (prefix_query_idxs ! j)
        (map snd f_fl) (map snd fl) (prefix_chunks ! j)"
    "\<And>j. j < n - Suc i \<Longrightarrow>
      verifier_query_round_chunk (suffix_query_idxs ! j)
        (map snd f_fl) (map snd fl) (suffix_chunks ! j)"
    "PTranscript s =
      List.concat (prefix_chunks @ chunk # suffix_chunks) @ PTranscript t"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    "partial_query_openings_consistent trace_openings composition_openings
      as idx"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s + i)
        (state_after_query_chunks (PState s) prefix_chunks i)) = Some raw"
proof -
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix round suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) i)
            s)"
    and round:
      "Some (round, s_suc) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              (n - Suc i))
            s_suc)"
    by blast
  have round_unit: "round = ()"
    by (cases round) simp
  show ?thesis
  proof (rule query_opening_ntimes_prefix_transcript_state_alignment
      [OF prefix])
    fix prefix_query_idxs prefix_chunks
    assume len_prefix: "length prefix_query_idxs = i"
      and len_prefix_chunks: "length prefix_chunks = i"
      and transcript_prefix:
        "PTranscript s = List.concat prefix_chunks @ PTranscript s_i"
      and state_i:
        "PState s_i =
          state_after_query_chunks (PState s) prefix_chunks i"
      and counter_i: "PQueryCounter s_i = PQueryCounter s + i"
      and prefix_ext: "s \<le> s_i"
      and prefix_rounds:
        "\<And>j. j < i \<Longrightarrow>
          verifier_query_round_chunk (prefix_query_idxs ! j)
            (map snd f_fl) (map snd fl) (prefix_chunks ! j)"
    show ?thesis
    proof (rule
        query_opening_verifier_query_round_program_authenticated_with_chunk
        [OF fl_eq round[unfolded round_unit]])
      fix raw idx chunk trace_leaves trace_openings composition_openings
      assume idx_eq: "idx = index (to_nat raw)"
        and chunk_shape:
          "verifier_query_round_chunk idx (map snd f_fl) (map snd fl)
            chunk"
        and transcript_round:
          "PTranscript s_i = chunk @ PTranscript s_suc"
        and state_suc:
          "PState s_suc = foldl concat (PState s_i) chunk"
        and round_ext: "s_i \<le> s_suc"
        and counter_suc: "PQueryCounter s_suc = Suc (PQueryCounter s_i)"
        and trace_values:
          "map opening_value trace_openings = trace_leaves"
        and trace_indices:
          "map opening_index trace_openings = powers_scaled idx"
        and trace_table_suc:
          "partial_authenticated_table fr (scale * clength)
            trace_openings s_suc"
        and comp_table_suc:
          "partial_authenticated_table composition_root (scale * clength)
            composition_openings s_suc"
        and comp_indices:
          "map opening_index composition_openings =
            [idx, fri_sibling_index (scale * clength) idx]"
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
            Some raw"
      show ?thesis
      proof (rule verifier_query_round_program_authenticated_openings_consistent_with_lookup
          [OF fl_eq round[unfolded round_unit]])
        fix raw' idx' trace_openings' composition_openings'
        assume idx'_eq: "idx' = index (to_nat raw')"
          and trace_indices':
            "map opening_index trace_openings' = powers_scaled idx'"
          and trace_table_suc':
            "partial_authenticated_table fr (scale * clength)
              trace_openings' s_suc"
          and comp_table_suc':
            "partial_authenticated_table composition_root (scale * clength)
              composition_openings' s_suc"
          and comp_indices':
            "map opening_index composition_openings' =
              [idx', fri_sibling_index (scale * clength) idx']"
          and consistent':
            "partial_query_openings_consistent trace_openings'
              composition_openings' as idx'"
          and lookup_suc':
            "fmlookup (HashMap s_suc)
              (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
              Some raw'"
        have raw'_eq: "raw' = raw"
          using lookup_suc lookup_suc' by simp
        have idx'_idx: "idx' = idx"
          using idx'_eq idx_eq raw'_eq by simp
        have suffix_ext: "s_suc \<le> t"
          by (rule query_opening_ntimes_suffix_extends[OF suffix])
        have trace_table_t:
          "partial_authenticated_table fr (scale * clength)
            trace_openings' t"
          by (rule partial_authenticated_table_mono
              [OF trace_table_suc' suffix_ext])
        have comp_table_t:
          "partial_authenticated_table composition_root (scale * clength)
            composition_openings' t"
          by (rule partial_authenticated_table_mono
              [OF comp_table_suc' suffix_ext])
        have lookup_t:
          "fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s + i)
              (state_after_query_chunks (PState s) prefix_chunks i)) =
            Some raw"
          using hash_extension_lookup[OF lookup_suc suffix_ext]
          unfolding counter_i state_i .
        show ?thesis
        proof (rule query_opening_ntimes_suffix_transcript_state_alignment
            [OF suffix])
          fix suffix_query_idxs suffix_chunks
          assume len_suffix_idxs:
              "length suffix_query_idxs = n - Suc i"
            and len_suffix_chunks:
              "length suffix_chunks = n - Suc i"
            and transcript_suffix:
              "PTranscript s_suc =
                List.concat suffix_chunks @ PTranscript t"
            and suffix_state:
              "PState t =
                state_after_query_chunks (PState s_suc) suffix_chunks
                  (n - Suc i)"
            and suffix_counter:
              "PQueryCounter t = PQueryCounter s_suc + (n - Suc i)"
            and suffix_ext2: "s_suc \<le> t"
            and suffix_rounds:
              "\<And>j. j < n - Suc i \<Longrightarrow>
                verifier_query_round_chunk (suffix_query_idxs ! j)
                  (map snd f_fl) (map snd fl) (suffix_chunks ! j)"
          have transcript_all:
            "PTranscript s =
              List.concat (prefix_chunks @ chunk # suffix_chunks) @
                PTranscript t"
            using transcript_prefix transcript_round transcript_suffix
            by simp
          show ?thesis
            by (rule that[OF idx_eq len_prefix len_prefix_chunks
                  len_suffix_idxs len_suffix_chunks chunk_shape _ _
                  transcript_all _ trace_table_t comp_table_t _ _ lookup_t])
              (use trace_indices' comp_indices' consistent' idx'_idx
                prefix_rounds suffix_rounds in simp_all)
        qed
      qed
    qed
  qed
qed

lemma ntimes_verifier_query_rounds_aligned_authenticated_openings_consistent:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            s)"
  obtains query_idxs trace_openings composition_openings where
    "length query_idxs = rounds"
    "length trace_openings = rounds"
    "length composition_openings = rounds"
    "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    "\<And>i. i < rounds \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) t"
    "\<And>i. i < rounds \<Longrightarrow>
      partial_authenticated_table composition_root (scale * clength)
        (composition_openings ! i) t"
    "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (composition_openings ! i) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)]"
    "\<And>i. i < rounds \<Longrightarrow>
      partial_query_round_consistent trace_openings composition_openings as i
        (query_idxs ! i)"
proof (cases "rounds = 0")
  case True
  show ?thesis
    by (rule that[of "[]" "[]" "[]"]) (use True in simp_all)
next
  case nonzero: False
  let ?P =
    "\<lambda>i w. map opening_index (fst (snd w)) = powers_scaled (fst w) \<and>
      partial_authenticated_table fr (scale * clength) (fst (snd w)) t \<and>
      partial_authenticated_table composition_root (scale * clength)
        (snd (snd w)) t \<and>
      map opening_index (snd (snd w)) =
        [fst w, fri_sibling_index (scale * clength) (fst w)] \<and>
      partial_query_openings_consistent (fst (snd w)) (snd (snd w))
        as (fst w)"
  let ?wit = "\<lambda>i. SOME w. ?P i w"
  let ?idx = "\<lambda>i. fst (?wit i)"
  let ?trace_openings = "\<lambda>i. fst (snd (?wit i))"
  let ?composition_openings = "\<lambda>i. snd (snd (?wit i))"
  let ?query_idxs = "map ?idx [0..<rounds]"
  let ?trace_tables = "map ?trace_openings [0..<rounds]"
  let ?comp_tables = "map ?composition_openings [0..<rounds]"
  have ex_round:
    "\<And>i. i < rounds \<Longrightarrow>
      \<exists>w. ?P i w"
  proof -
    fix i
    assume i_bound: "i < rounds"
    show "\<exists>w. ?P i w"
    proof (rule ntimes_verifier_query_rounds_selected_authenticated_chunks_at
        [OF fl_eq outcome i_bound])
      fix raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
          suffix_chunks trace_openings composition_openings
      assume idx_eq: "idx = index (to_nat raw)"
        and trace_indices:
          "map opening_index trace_openings = powers_scaled idx"
        and trace_table:
          "partial_authenticated_table fr (scale * clength) trace_openings t"
        and comp_table:
          "partial_authenticated_table composition_root (scale * clength)
            composition_openings t"
        and comp_indices:
          "map opening_index composition_openings =
            [idx, fri_sibling_index (scale * clength) idx]"
        and consistent:
          "partial_query_openings_consistent trace_openings
            composition_openings as idx"
      show ?thesis
        by (intro exI[of _ "(idx, trace_openings, composition_openings)"]
            conjI)
          (use idx_eq trace_indices trace_table comp_table comp_indices
            consistent in simp_all)
    qed
  qed
  have round_props:
    "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (?trace_tables ! i) =
        powers_scaled (?query_idxs ! i) \<and>
      partial_authenticated_table fr (scale * clength)
        (?trace_tables ! i) t \<and>
      partial_authenticated_table composition_root (scale * clength)
        (?comp_tables ! i) t \<and>
      map opening_index (?comp_tables ! i) =
        [?query_idxs ! i,
         fri_sibling_index (scale * clength) (?query_idxs ! i)] \<and>
      partial_query_round_consistent ?trace_tables ?comp_tables as i
        (?query_idxs ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have chosen: "?P i (?wit i)"
      by (rule someI_ex[OF ex_round[OF i_bound]])
    have nths:
      "?query_idxs ! i = ?idx i"
      "?trace_tables ! i = ?trace_openings i"
      "?comp_tables ! i = ?composition_openings i"
      using i_bound by simp_all
    have lengths:
      "length ?trace_tables = rounds"
      "length ?comp_tables = rounds"
      by simp_all
    show
      "map opening_index (?trace_tables ! i) =
        powers_scaled (?query_idxs ! i) \<and>
      partial_authenticated_table fr (scale * clength)
        (?trace_tables ! i) t \<and>
      partial_authenticated_table composition_root (scale * clength)
        (?comp_tables ! i) t \<and>
      map opening_index (?comp_tables ! i) =
        [?query_idxs ! i,
         fri_sibling_index (scale * clength) (?query_idxs ! i)] \<and>
      partial_query_round_consistent ?trace_tables ?comp_tables as i
        (?query_idxs ! i)"
      using chosen i_bound nths lengths
      unfolding partial_query_round_consistent_def
        partial_query_openings_consistent_def
      by simp
  qed
  show ?thesis
    by (rule that[of ?query_idxs ?trace_tables ?comp_tables])
      (use round_props in simp_all)
qed

end

end
