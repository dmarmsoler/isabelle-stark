(*  Title:      Stark/Soundness_Staged_Partial_Query.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Partial_Query
  imports
    Soundness_Staged_Query_Prefix
    Soundness_Bound_Table_Partial_Openings
begin

text \<open>
  Partial-opening query events for staged soundness.

  This layer records query consistency directly from authenticated openings.
  It deliberately avoids the stronger, generally false claim that sampled
  openings determine unique complete trace and composition tables.
\<close>

context soundness
begin

lemma checked_staged_security_with_data_state_accepted_shape_query_chunks:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and shape:
      "accepted_transcript_shape
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) as query_idxs"
  shows
    "as = staged_alphas data \<and>
     (\<exists>raw_idxs.
      length raw_idxs = rounds \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      (\<forall>i < rounds.
        verifier_query_round_chunk (query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! i)) \<and>
      (\<forall>i < rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF outcome]
  have builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    by blast
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  from accepted_transcript_shape_query_chunksE[OF shape]
  obtain result' final_state' fr f_fri_roots f_final dg
      composition_fri_roots final rest raw_idxs query_chunks trailing
    where out_eq:
      "Some (result, final_state) = Some (result', final_state')"
    and header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and concat_chunks: "List.concat query_chunks @ trailing = rest"
    and chunk_shape:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          f_fri_roots composition_fri_roots (query_chunks ! i)"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter ?s + i)
            (state_after_query_chunks
              (verifier_header_state ?s fr f_fri_roots f_final as dg
                composition_fri_roots final)
              query_chunks i)) =
        Some (raw_idxs ! i)"
    and idx_bound:
      "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by blast
  have header_eq:
    "fr = staged_trace_root data \<and>
     f_fri_roots = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     composition_fri_roots = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF staged_header header]
    by simp
  have final_state_eq: "final_state' = final_state"
    using out_eq by simp
  have header_state_eq:
    "verifier_header_state ?s fr f_fri_roots f_final as dg
      composition_fri_roots final =
      staged_query_start_hash data"
    using header_eq
    unfolding verifier_header_state_def verifier_header_messages_def
      staged_query_start_hash_def staged_composition_fri_start_hash_def
      staged_trace_fri_start_hash_def
    by simp
  from checked_staged_transcript_program_query_chunks_match_verifier_lengths
      [OF builder]
  obtain staged_query_idxs where
    staged_match:
      "staged_query_chunks_match_verifier_lengths data staged_query_idxs"
    by blast
  have query_idxs_len: "length query_idxs = rounds"
    using query_idxs_eq len_raw by simp
  have staged_match_query_idxs:
    "staged_query_chunks_match_verifier_lengths data query_idxs"
    by (rule staged_query_chunks_match_verifier_lengths_transfer
        [OF staged_match query_idxs_len])
  have parser_chunk_len:
    "\<And>i. i < rounds \<Longrightarrow>
      length (query_chunks ! i) =
        verifier_query_round_transcript_length (query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    show
      "length (query_chunks ! i) =
        verifier_query_round_transcript_length (query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
      using verifier_query_round_chunk_length[OF chunk_shape[OF i_bound]]
        header_eq by simp
  qed
  have concat_staged:
    "List.concat query_chunks @ trailing =
      List.concat (staged_query_chunks data)"
    using concat_chunks header_eq by simp
  have query_chunks_eq:
    "query_chunks = staged_query_chunks data \<and> trailing = []"
    by (rule query_chunks_eq_staged_if_matching_lengths
        [OF len_chunks concat_staged parser_chunk_len
          staged_match_query_idxs])
  have chunk_shape_staged:
    "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (query_idxs ! i)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! i)"
    using chunk_shape header_eq query_chunks_eq by simp
  have lookup_staged:
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have lookup_i:
      "fmlookup (HashMap final_state')
        (QueryIndexChallenge (PQueryCounter ?s + i)
          (state_after_query_chunks
            (verifier_header_state ?s fr f_fri_roots f_final as dg
              composition_fri_roots final)
            query_chunks i)) =
        Some (raw_idxs ! i)"
      by (rule lookup[OF i_bound])
    show
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
      using lookup_i final_state_eq header_state_eq query_chunks_eq by simp
  qed
  show ?thesis
    using header_eq len_raw query_idxs_eq chunk_shape_staged lookup_staged
      idx_bound
    by blast
qed

lemma checked_staged_security_with_data_state_query_bad_round_chunkE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_query_bad_hit
        (Some (((data, attacker_state), result), final_state))"
  obtains i trace_table composition_table query_idxs raw_idxs where
    "i < rounds"
    "accepted_with_bound_tables
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state))
      trace_table composition_table (staged_alphas data) query_idxs"
    "query_idxs ! i \<in>
      query_sampling_success_space trace_table composition_table
        (staged_alphas data)"
    "length raw_idxs = rounds"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "verifier_query_round_chunk (query_idxs ! i)
      (staged_trace_fri_roots data)
      (staged_composition_fri_roots data)
      (staged_query_chunks data ! i)"
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from bad[unfolded staged_security_with_data_state_query_bad_hit_def
      Let_def]
  have query_bad: "query_bad ?s (Some (result, final_state))"
    by simp
  from query_bad_imp_query_index_round_set_hit[OF query_bad]
  obtain i trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and i_bound: "i < rounds"
    and query_hit:
      "query_idxs ! i \<in>
        query_sampling_success_space trace_table composition_table as"
    unfolding query_index_round_set_hit_def
      query_index_round_set_hit_at_def
    by blast
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state))
      as query_idxs"
    using bound
    unfolding accepted_with_bound_tables_def accepted_with_tables_def
    by simp
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled support shape]
  obtain raw_idxs where
    as_eq: "as = staged_alphas data"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and chunk_shape:
      "\<And>j. j < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)"
    and lookup:
      "\<And>j. j < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
        Some (raw_idxs ! j)"
    by blast
  have bound_staged:
    "accepted_with_bound_tables ?s (Some (result, final_state))
      trace_table composition_table (staged_alphas data) query_idxs"
    using bound as_eq by simp
  have query_hit_staged:
    "query_idxs ! i \<in>
      query_sampling_success_space trace_table composition_table
        (staged_alphas data)"
    using query_hit as_eq by simp
  show ?thesis
    by (rule that[OF i_bound bound_staged query_hit_staged len_raw
          query_idxs_eq chunk_shape[OF i_bound] lookup[OF i_bound]])
qed

lemma ntimes_outcome_decomp_at:
  assumes outcome:
      "Some (results, t) \<in> set_dist (execute (ntimes m n) s)"
    and i_bound: "i < n"
  shows
    "\<exists>prefix x suffix s_i s_suc.
      Some (prefix, s_i) \<in> set_dist (execute (ntimes m i) s) \<and>
      Some (x, s_suc) \<in> set_dist (execute m s_i) \<and>
      Some (suffix, t) \<in>
        set_dist (execute (ntimes m (n - Suc i)) s_suc) \<and>
      results = prefix @ x # suffix"
  using outcome i_bound
proof (induction n arbitrary: i s results t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain x results' s1 where
    head: "Some (x, s1) \<in> set_dist (execute m s)"
    and tail:
      "Some (results', t) \<in> set_dist (execute (ntimes m n) s1)"
    and results_eq: "results = x # results'"
    by (auto elim!: set_dist_bindE)
  show ?case
  proof (cases i)
    case 0
    have prefix0:
      "Some ([], s) \<in> set_dist (execute (ntimes m i) s)"
      using 0 by simp
    have suffix0:
      "Some (results', t) \<in>
        set_dist (execute (ntimes m (Suc n - Suc i)) s1)"
      using tail 0 by simp
    show ?thesis
      using prefix0 head suffix0 results_eq
      by (intro exI[of _ "[]"] exI[of _ x] exI[of _ results']
          exI[of _ s] exI[of _ s1]) simp
  next
    case (Suc j)
    have j_bound: "j < n"
      using Suc.prems(2) Suc by simp
    from Suc.IH[OF tail j_bound]
    obtain prefix y suffix s_j s_suc where
      prefix:
        "Some (prefix, s_j) \<in> set_dist (execute (ntimes m j) s1)"
      and round: "Some (y, s_suc) \<in> set_dist (execute m s_j)"
      and suffix:
        "Some (suffix, t) \<in>
          set_dist (execute (ntimes m (n - Suc j)) s_suc)"
      and results'_eq: "results' = prefix @ y # suffix"
      by blast
    have prefix_suc:
      "Some (x # prefix, s_j) \<in>
        set_dist (execute (ntimes m (Suc j)) s)"
      unfolding ntimes.simps
      apply (rule set_dist_bindI[OF head])
      apply (rule set_dist_bindI[OF prefix])
      apply simp
      done
    have n_minus: "Suc n - Suc (Suc j) = n - Suc j"
      by simp
    have suffix_suc:
      "Some (suffix, t) \<in>
        set_dist (execute (ntimes m (Suc n - Suc i)) s_suc)"
      using suffix n_minus Suc by simp
    show ?thesis
      using prefix_suc round suffix_suc results_eq results'_eq Suc
      by (intro exI[of _ "x # prefix"] exI[of _ y] exI[of _ suffix]
          exI[of _ s_j] exI[of _ s_suc]) simp
  qed
qed

definition partial_query_round_consistent
  :: "'f authenticated_opening list list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> bool"
where
  "partial_query_round_consistent trace_openings composition_openings as i idx
    \<longleftrightarrow>
      i < rounds \<and>
      idx \<in> query_sample_space \<and>
      length trace_openings = rounds \<and>
      length composition_openings = rounds \<and>
      map opening_index (trace_openings ! i) = powers_scaled idx \<and>
      map opening_index (composition_openings ! i) =
        [idx, fri_sibling_index (scale * clength) idx] \<and>
      composition_openings ! i \<noteq> [] \<and>
      opening_value ((composition_openings ! i) ! 0) =
        cp_eval as (map opening_value (trace_openings ! i))
          (h ^ idx * shift)"

definition partial_query_success_indices_at
  :: "'f authenticated_opening list list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      nat set"
where
  "partial_query_success_indices_at trace_openings composition_openings as i =
    {idx \<in> query_sample_space.
      partial_query_round_consistent trace_openings composition_openings as
        i idx}"

lemma partial_query_success_indices_at_subset:
  "partial_query_success_indices_at trace_openings composition_openings as i
    \<subseteq> query_sample_space"
  unfolding partial_query_success_indices_at_def by auto

lemma partial_query_success_indices_at_subset_query_sampling_success_space:
  assumes trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "partial_query_success_indices_at trace_openings composition_openings as i
      \<subseteq> query_sampling_success_space trace_table composition_table as"
proof
  fix idx
  assume idx_in:
    "idx \<in> partial_query_success_indices_at trace_openings
      composition_openings as i"
  have round:
    "partial_query_round_consistent trace_openings composition_openings as
      i idx"
    using idx_in unfolding partial_query_success_indices_at_def by simp
  have i_bound: "i < rounds"
    using round unfolding partial_query_round_consistent_def by simp
  have idx_sample: "idx \<in> query_sample_space"
    using round unfolding partial_query_round_consistent_def by simp
  have trace_indices:
    "map opening_index (trace_openings ! i) = powers_scaled idx"
    using round unfolding partial_query_round_consistent_def by simp
  have comp_indices:
    "map opening_index (composition_openings ! i) =
      [idx, fri_sibling_index (scale * clength) idx]"
    using round unfolding partial_query_round_consistent_def by simp
  have comp_value_opened:
    "opening_value ((composition_openings ! i) ! 0) =
      cp_eval as (map opening_value (trace_openings ! i))
        (h ^ idx * shift)"
    using round unfolding partial_query_round_consistent_def by simp
  have trace_len: "length trace_table = scale * clength"
    using trace_candidate unfolding partial_trace_table_candidate_def
    by simp
  have comp_len: "length composition_table = scale * clength"
    using comp_candidate unfolding partial_composition_table_candidate_def
    by simp
  have trace_values:
    "map ((!) trace_table) (powers_scaled idx) =
      map opening_value (trace_openings ! i)"
    by (rule partial_trace_table_candidate_query_values
        [OF trace_candidate i_bound trace_indices])
  have comp_value:
    "composition_table ! idx =
      opening_value ((composition_openings ! i) ! 0)"
    by (rule partial_composition_table_candidate_query_value
        [OF comp_candidate i_bound comp_indices])
  have idx_domain: "idx < clength * scale"
    by (rule query_sample_space_less_domain[OF idx_sample])
  have powers_bound:
    "\<forall>j \<in> set (powers_scaled idx). j < length trace_table"
    using query_sample_space_powers_scaled_bound[OF idx_sample] trace_len
    by (simp add: mult.commute)
  have consistent:
    "query_consistent_at trace_table composition_table as idx"
    unfolding query_consistent_at_def
    using idx_domain trace_len comp_len powers_bound trace_values comp_value
      comp_value_opened
    by (simp add: mult.commute)
  show "idx \<in> query_sampling_success_space trace_table composition_table as"
    unfolding query_sampling_success_space_def query_agreement_indices_def
    using idx_sample consistent trace_low comp_low not_all by simp
qed

lemma partial_query_round_consistent_imp_query_consistent_at:
  assumes trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and round:
      "partial_query_round_consistent trace_openings composition_openings
        as i idx"
  shows "query_consistent_at trace_table composition_table as idx"
proof -
  have i_bound: "i < rounds"
    using round unfolding partial_query_round_consistent_def by simp
  have idx_sample: "idx \<in> query_sample_space"
    using round unfolding partial_query_round_consistent_def by simp
  have trace_indices:
    "map opening_index (trace_openings ! i) = powers_scaled idx"
    using round unfolding partial_query_round_consistent_def by simp
  have comp_indices:
    "map opening_index (composition_openings ! i) =
      [idx, fri_sibling_index (scale * clength) idx]"
    using round unfolding partial_query_round_consistent_def by simp
  have comp_value_opened:
    "opening_value ((composition_openings ! i) ! 0) =
      cp_eval as (map opening_value (trace_openings ! i))
        (h ^ idx * shift)"
    using round unfolding partial_query_round_consistent_def by simp
  have trace_len: "length trace_table = scale * clength"
    using trace_candidate unfolding partial_trace_table_candidate_def
    by simp
  have comp_len: "length composition_table = scale * clength"
    using comp_candidate unfolding partial_composition_table_candidate_def
    by simp
  have trace_values:
    "map ((!) trace_table) (powers_scaled idx) =
      map opening_value (trace_openings ! i)"
    by (rule partial_trace_table_candidate_query_values
        [OF trace_candidate i_bound trace_indices])
  have comp_value:
    "composition_table ! idx =
      opening_value ((composition_openings ! i) ! 0)"
    by (rule partial_composition_table_candidate_query_value
        [OF comp_candidate i_bound comp_indices])
  have idx_domain: "idx < clength * scale"
    by (rule query_sample_space_less_domain[OF idx_sample])
  have powers_bound:
    "\<forall>j \<in> set (powers_scaled idx). j < length trace_table"
    using query_sample_space_powers_scaled_bound[OF idx_sample] trace_len
    by (simp add: mult.commute)
  show ?thesis
    unfolding query_consistent_at_def
    using idx_domain trace_len comp_len powers_bound trace_values comp_value
      comp_value_opened
    by (simp add: mult.commute)
qed

lemma partial_query_success_indices_at_fraction_bound_if_candidate_low_degree:
  assumes trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "nnreal
      (card
        (partial_query_success_indices_at trace_openings composition_openings
          as i)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof -
  have subset:
    "partial_query_success_indices_at trace_openings composition_openings as i
      \<subseteq> query_sampling_success_space trace_table composition_table as"
    by (rule partial_query_success_indices_at_subset_query_sampling_success_space
        [OF trace_candidate comp_candidate trace_low comp_low not_all])
  have finite_success:
    "finite (query_sampling_success_space trace_table composition_table as)"
    by (rule finite_subset[OF query_sampling_success_space_subset
          finite_query_sample_space])
  have card_le:
    "card
      (partial_query_success_indices_at trace_openings composition_openings
        as i) \<le>
      card (query_sampling_success_space trace_table composition_table as)"
    by (rule card_mono[OF finite_success subset])
  have "nnreal
        (card
          (partial_query_success_indices_at trace_openings
            composition_openings as i)) /
      nnreal (card query_sample_space) \<le>
      nnreal (card (query_sampling_success_space trace_table
        composition_table as)) /
        nnreal (card query_sample_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> query_error_bound"
    by (rule query_sampling_success_space_fraction_bound_query_sample_space)
  finally show ?thesis .
qed

lemma partial_query_round_consistentI:
  assumes i_bound: "i < rounds"
    and idx_sample: "idx \<in> query_sample_space"
    and trace_len: "length trace_openings = rounds"
    and comp_len: "length composition_openings = rounds"
    and trace_indices:
      "map opening_index (trace_openings ! i) = powers_scaled idx"
    and comp_indices:
      "map opening_index (composition_openings ! i) =
        [idx, fri_sibling_index (scale * clength) idx]"
    and comp_value:
      "opening_value ((composition_openings ! i) ! 0) =
        cp_eval as (map opening_value (trace_openings ! i))
          (h ^ idx * shift)"
  shows
    "partial_query_round_consistent trace_openings composition_openings as
      i idx"
proof -
  have comp_round_nonempty: "composition_openings ! i \<noteq> []"
  proof -
    have "length (map opening_index (composition_openings ! i)) =
        length [idx, fri_sibling_index (scale * clength) idx]"
      using arg_cong[OF comp_indices, of length] by simp
    then have "length (composition_openings ! i) = 2"
      by simp
    then show ?thesis by auto
  qed
  show ?thesis
    unfolding partial_query_round_consistent_def
    using i_bound idx_sample trace_len comp_len trace_indices comp_indices
      comp_round_nonempty comp_value
    by simp
qed

lemma partial_query_success_indices_atI:
  assumes "partial_query_round_consistent trace_openings composition_openings
    as i idx"
  shows
    "idx \<in> partial_query_success_indices_at trace_openings
      composition_openings as i"
  using assms unfolding partial_query_success_indices_at_def
    partial_query_round_consistent_def by simp

definition partial_query_openings_consistent
  :: "'f authenticated_opening list \<Rightarrow>
      'f authenticated_opening list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> bool"
where
  "partial_query_openings_consistent trace_openings composition_openings as idx
    \<longleftrightarrow>
      idx \<in> query_sample_space \<and>
      map opening_index trace_openings = powers_scaled idx \<and>
      map opening_index composition_openings =
        [idx, fri_sibling_index (scale * clength) idx] \<and>
      composition_openings \<noteq> [] \<and>
      opening_value (composition_openings ! 0) =
        cp_eval as (map opening_value trace_openings) (h ^ idx * shift)"

lemma partial_query_openings_consistentI:
  assumes idx_sample: "idx \<in> query_sample_space"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and comp_indices:
      "map opening_index composition_openings =
        [idx, fri_sibling_index (scale * clength) idx]"
    and comp_value:
      "opening_value (composition_openings ! 0) =
        cp_eval as (map opening_value trace_openings) (h ^ idx * shift)"
  shows
    "partial_query_openings_consistent trace_openings composition_openings
      as idx"
proof -
  have comp_nonempty: "composition_openings \<noteq> []"
  proof -
    have "length (map opening_index composition_openings) =
        length [idx, fri_sibling_index (scale * clength) idx]"
      using arg_cong[OF comp_indices, of length] by simp
    then have "length composition_openings = 2"
      by simp
    then show ?thesis by auto
  qed
  show ?thesis
    unfolding partial_query_openings_consistent_def
    using idx_sample trace_indices comp_indices comp_nonempty comp_value
    by simp
qed

lemma partial_query_round_consistent_single_roundI:
  assumes i_bound: "i < rounds"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        as idx"
  shows
    "partial_query_round_consistent
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      as i idx"
proof -
  have idx_sample: "idx \<in> query_sample_space"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have trace_indices:
    "map opening_index trace_openings = powers_scaled idx"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have comp_indices:
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have comp_value:
    "opening_value (composition_openings ! 0) =
      cp_eval as (map opening_value trace_openings) (h ^ idx * shift)"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have comp_nonempty: "composition_openings \<noteq> []"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have comp_round_value:
    "opening_value
      ((((replicate rounds []) [i := composition_openings]) ! i) ! 0) =
      cp_eval as
        (map opening_value
          (((replicate rounds []) [i := trace_openings]) ! i))
        (h ^ idx * shift)"
    using i_bound comp_value by simp
  show ?thesis
    unfolding partial_query_round_consistent_def
    using i_bound idx_sample trace_indices comp_indices comp_nonempty
      comp_round_value
    by simp
qed

lemma powers_scaled_hd:
  "hd (powers_scaled idx) = idx"
  unfolding powers_scaled_def
  using powers_pos by (simp add: upt_conv_Cons)

lemma partial_query_openings_consistent_index_unique:
  assumes left:
      "partial_query_openings_consistent trace_openings
        composition_openings as idx"
    and right:
      "partial_query_openings_consistent trace_openings
        composition_openings as idx'"
  shows "idx = idx'"
proof -
  have "powers_scaled idx = powers_scaled idx'"
    using left right
    unfolding partial_query_openings_consistent_def by simp
  then have "hd (powers_scaled idx) = hd (powers_scaled idx')"
    by simp
  then show ?thesis
    by (simp add: powers_scaled_hd)
qed

lemma partial_query_openings_consistent_indices_card_le_one:
  "card
    {idx \<in> query_sample_space.
      partial_query_openings_consistent trace_openings composition_openings
        as idx} \<le> 1"
proof -
  let ?S =
    "{idx \<in> query_sample_space.
      partial_query_openings_consistent trace_openings composition_openings
        as idx}"
  have finite_S: "finite ?S"
    by simp
  have unique: "\<And>idx idx'. idx \<in> ?S \<Longrightarrow> idx' \<in> ?S \<Longrightarrow> idx = idx'"
    by (rule partial_query_openings_consistent_index_unique) auto
  show ?thesis
  proof (cases "\<exists>idx. idx \<in> ?S")
    case False
    have empty: "?S = {}"
    proof (rule equals0I)
      fix idx
      assume "idx \<in> ?S"
      then show False
        using False by blast
    qed
    show ?thesis
      by (subst empty, simp)
  next
    case True
    then obtain idx where idx_in: "idx \<in> ?S"
      by blast
    have subset_single: "?S \<subseteq> {idx}"
      using idx_in unique by blast
    have "card ?S \<le> card {idx}"
      by (rule card_mono) (use subset_single in simp_all)
    then show ?thesis
      by simp
  qed
qed

lemma partial_query_openings_consistent_imp_round_consistent_list_update:
  assumes i_bound: "i < rounds"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        as idx"
  shows
    "partial_query_round_consistent
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      as i idx"
proof -
  have idx_sample: "idx \<in> query_sample_space"
    using consistent
    unfolding partial_query_openings_consistent_def by simp
  have trace_indices:
    "map opening_index
      (((replicate rounds []) [i := trace_openings]) ! i) =
      powers_scaled idx"
    using consistent i_bound
    unfolding partial_query_openings_consistent_def by simp
  have comp_indices:
    "map opening_index
      (((replicate rounds []) [i := composition_openings]) ! i) =
      [idx, fri_sibling_index (scale * clength) idx]"
    using consistent i_bound
    unfolding partial_query_openings_consistent_def by simp
  have comp_value:
    "opening_value
      ((((replicate rounds []) [i := composition_openings]) ! i) ! 0) =
      cp_eval as
        (map opening_value
          (((replicate rounds []) [i := trace_openings]) ! i))
        (h ^ idx * shift)"
    using consistent i_bound
    unfolding partial_query_openings_consistent_def by simp
  show ?thesis
    by (rule partial_query_round_consistentI
        [OF i_bound idx_sample])
      (use i_bound trace_indices comp_indices comp_value in simp_all)
qed

lemma partial_query_openings_consistent_indices_subset_round_success_list_update:
  assumes i_bound: "i < rounds"
  shows
    "{idx \<in> query_sample_space.
      partial_query_openings_consistent trace_openings composition_openings
        as idx}
    \<subseteq>
    partial_query_success_indices_at
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      as i"
  unfolding partial_query_success_indices_at_def
  using partial_query_openings_consistent_imp_round_consistent_list_update
    [OF i_bound]
  by blast

lemma partial_query_openings_consistent_indices_fraction_bound_if_candidate_low_degree:
  assumes i_bound: "i < rounds"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "nnreal
      (card
        {idx \<in> query_sample_space.
          partial_query_openings_consistent trace_openings
            composition_openings as idx}) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof -
  let ?trace_openings = "(replicate rounds []) [i := trace_openings]"
  let ?composition_openings =
    "(replicate rounds []) [i := composition_openings]"
  let ?flat =
    "{idx \<in> query_sample_space.
      partial_query_openings_consistent trace_openings composition_openings
        as idx}"
  let ?round =
    "partial_query_success_indices_at ?trace_openings
      ?composition_openings as i"
  have subset: "?flat \<subseteq> ?round"
    by (rule
        partial_query_openings_consistent_indices_subset_round_success_list_update
        [OF i_bound])
  have finite_round: "finite ?round"
    by (rule finite_subset[OF partial_query_success_indices_at_subset
          finite_query_sample_space])
  have card_le: "card ?flat \<le> card ?round"
    by (rule card_mono[OF finite_round subset])
  have "nnreal (card ?flat) / nnreal (card query_sample_space) \<le>
      nnreal (card ?round) / nnreal (card query_sample_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> query_error_bound"
    by (rule partial_query_success_indices_at_fraction_bound_if_candidate_low_degree
        [OF trace_candidate comp_candidate trace_low comp_low not_all])
  finally show ?thesis .
qed

lemma partial_trace_table_candidate_single_roundI:
  assumes i_bound: "i < rounds"
    and len_table: "length trace_table = scale * clength"
    and agrees:
      "table_agrees_with_authenticated_openings trace_table
        (scale * clength) trace_openings"
  shows
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [i := trace_openings])"
  unfolding partial_trace_table_candidate_def
proof (intro conjI allI impI)
  show "length trace_table = scale * clength"
    by (rule len_table)
next
  show "length ((replicate rounds []) [i := trace_openings]) = rounds"
    using i_bound by simp
next
  fix j
  assume j_bound: "j < rounds"
  show
    "table_agrees_with_authenticated_openings trace_table
      (scale * clength)
      (((replicate rounds []) [i := trace_openings]) ! j)"
  proof (cases "j = i")
    case True
    then show ?thesis
      using agrees i_bound by simp
  next
    case False
    then show ?thesis
      using j_bound len_table
      unfolding table_agrees_with_authenticated_openings_def
      by simp
  qed
qed

lemma partial_composition_table_candidate_single_roundI:
  assumes i_bound: "i < rounds"
    and len_table: "length composition_table = scale * clength"
    and agrees:
      "table_agrees_with_authenticated_openings composition_table
        (scale * clength) composition_openings"
  shows
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [i := composition_openings])"
  unfolding partial_composition_table_candidate_def
proof (intro conjI allI impI)
  show "length composition_table = scale * clength"
    by (rule len_table)
next
  show "length ((replicate rounds []) [i := composition_openings]) =
      rounds"
    using i_bound by simp
next
  fix j
  assume j_bound: "j < rounds"
  show
    "table_agrees_with_authenticated_openings composition_table
      (scale * clength)
      (((replicate rounds []) [i := composition_openings]) ! j)"
  proof (cases "j = i")
    case True
    then show ?thesis
      using agrees i_bound by simp
  next
    case False
    then show ?thesis
      using j_bound len_table
      unfolding table_agrees_with_authenticated_openings_def
      by simp
  qed
qed

lemma partial_query_openings_consistent_indices_fraction_bound_if_tables_agree_low_degree:
  assumes i_bound: "i < rounds"
    and trace_len: "length trace_table = scale * clength"
    and comp_len: "length composition_table = scale * clength"
    and trace_agrees:
      "table_agrees_with_authenticated_openings trace_table
        (scale * clength) trace_openings"
    and comp_agrees:
      "table_agrees_with_authenticated_openings composition_table
        (scale * clength) composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low: "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "nnreal
      (card
        {idx \<in> query_sample_space.
          partial_query_openings_consistent trace_openings
            composition_openings as idx}) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof -
  have trace_candidate:
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [i := trace_openings])"
    by (rule partial_trace_table_candidate_single_roundI
        [OF i_bound trace_len trace_agrees])
  have comp_candidate:
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [i := composition_openings])"
    by (rule partial_composition_table_candidate_single_roundI
        [OF i_bound comp_len comp_agrees])
  show ?thesis
    by (rule
        partial_query_openings_consistent_indices_fraction_bound_if_candidate_low_degree
        [OF i_bound trace_candidate comp_candidate trace_low comp_low
          not_all])
qed

lemma table_agrees_with_authenticated_openings_values:
  assumes agrees:
      "table_agrees_with_authenticated_openings table len openings"
    and indices: "map opening_index openings = idxs"
  shows "map ((!) table) idxs = map opening_value openings"
proof (rule nth_equalityI)
  show "length (map ((!) table) idxs) = length (map opening_value openings)"
    by (simp add: indices[symmetric])
next
  fix i
  assume i_bound: "i < length (map ((!) table) idxs)"
  have i_openings: "i < length openings"
    using i_bound by (simp add: indices[symmetric])
  have opn_in: "openings ! i \<in> set openings"
    by (rule nth_mem[OF i_openings])
  have table_value:
    "table ! opening_index (openings ! i) = opening_value (openings ! i)"
    using agrees opn_in
    unfolding table_agrees_with_authenticated_openings_def by auto
  have "idxs ! i = opening_index (openings ! i)"
    using i_bound by (simp add: indices[symmetric])
  then show "map ((!) table) idxs ! i = map opening_value openings ! i"
    using table_value i_bound i_openings by simp
qed

lemma partial_authenticated_table_agrees_with_bound_table_if_clean:
  assumes bind: "merkle_root_binds_table rt table final_state"
    and len_table: "length table = scale * clength"
    and partial:
      "partial_authenticated_table rt (scale * clength) openings final_state"
    and clean: "\<not> hash_map_output_collision final_state"
  shows
    "table_agrees_with_authenticated_openings table (scale * clength)
      openings"
proof -
  obtain n where len_pow: "clength * scale = 2 ^ n"
    using eval_domain_length_power by blast
  have table_pow: "length table = 2 ^ n"
    using len_table len_pow by (simp add: mult.commute)
  have opening_agrees:
    "\<forall>opn \<in> set openings.
      opening_index opn < scale * clength \<and>
      table ! opening_index opn = opening_value opn"
  proof
    fix opn
    assume opn_in: "opn \<in> set openings"
    have root: "opening_root opn = rt"
      using partial opn_in unfolding partial_authenticated_table_def
      by blast
    have len: "opening_length opn = length table"
      using partial opn_in len_table
      unfolding partial_authenticated_table_def by simp
    have auth: "authenticated_opening_in final_state opn"
      using partial opn_in unfolding partial_authenticated_table_def
      by blast
    have agreement:
      "opening_index opn < length table \<and>
        table ! opening_index opn = opening_value opn"
      by (rule merkle_bound_table_agrees_with_authenticated_opening_if_clean
          [OF bind table_pow auth root len clean])
    then show
      "opening_index opn < scale * clength \<and>
        table ! opening_index opn = opening_value opn"
      using len_table by simp
  qed
  show ?thesis
    unfolding table_agrees_with_authenticated_openings_def
    using len_table opening_agrees by simp
qed

lemma partial_query_openings_consistent_from_sampling_success:
  assumes trace_bind:
      "merkle_root_binds_table fr trace_table final_state"
    and comp_bind:
      "merkle_root_binds_table composition_root composition_table
        final_state"
    and trace_len: "length trace_table = scale * clength"
    and comp_len: "length composition_table = scale * clength"
    and trace_auth:
      "partial_authenticated_table fr (scale * clength) trace_openings
        final_state"
    and comp_auth:
      "partial_authenticated_table composition_root (scale * clength)
        composition_openings final_state"
    and clean: "\<not> hash_map_output_collision final_state"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and comp_indices:
      "map opening_index composition_openings =
        [idx, fri_sibling_index (scale * clength) idx]"
    and success:
      "idx \<in> query_sampling_success_space trace_table composition_table as"
  shows
    "partial_query_openings_consistent trace_openings composition_openings
      as idx"
proof -
  have idx_sample: "idx \<in> query_sample_space"
    using success
    unfolding query_sampling_success_space_def query_agreement_indices_def
    by (auto split: if_splits)
  have consistent: "query_consistent_at trace_table composition_table as idx"
    using success
    unfolding query_sampling_success_space_def query_agreement_indices_def
    by (auto split: if_splits)
  have trace_agrees:
    "table_agrees_with_authenticated_openings trace_table
      (scale * clength) trace_openings"
    by (rule partial_authenticated_table_agrees_with_bound_table_if_clean
        [OF trace_bind trace_len trace_auth clean])
  have comp_agrees:
    "table_agrees_with_authenticated_openings composition_table
      (scale * clength) composition_openings"
    by (rule partial_authenticated_table_agrees_with_bound_table_if_clean
        [OF comp_bind comp_len comp_auth clean])
  have trace_values:
    "map ((!) trace_table) (powers_scaled idx) =
      map opening_value trace_openings"
    by (rule table_agrees_with_authenticated_openings_values
        [OF trace_agrees trace_indices])
  have comp_len_openings: "length composition_openings = 2"
    using arg_cong[OF comp_indices, of length] by simp
  have first_in: "composition_openings ! 0 \<in> set composition_openings"
    by (rule nth_mem) (use comp_len_openings in simp)
  have first_index: "opening_index (composition_openings ! 0) = idx"
  proof -
    have "map opening_index composition_openings ! 0 = idx"
      using comp_indices by simp
    then show ?thesis
      using comp_len_openings by simp
  qed
  have composition_value:
    "composition_table ! idx = opening_value (composition_openings ! 0)"
    using comp_agrees first_in first_index
    unfolding table_agrees_with_authenticated_openings_def by auto
  have opened_value:
    "opening_value (composition_openings ! 0) =
      cp_eval as (map opening_value trace_openings) (h ^ idx * shift)"
    using consistent trace_values composition_value
    unfolding query_consistent_at_def by simp
  show ?thesis
    by (rule partial_query_openings_consistentI
        [OF idx_sample trace_indices comp_indices opened_value])
qed

lemma partial_query_round_consistent_from_sampling_success:
  assumes trace_partial:
      "accepted_with_partial_trace_openings s out fr query_idxs
        trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s out composition_root
        query_idxs composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and i_bound: "i < rounds"
    and success:
      "query_idxs ! i \<in>
        query_sampling_success_space trace_table composition_table as"
  shows
    "partial_query_round_consistent trace_openings composition_openings as i
      (query_idxs ! i)"
proof -
  let ?idx = "query_idxs ! i"
  have idx_sample: "?idx \<in> query_sample_space"
    using success
    unfolding query_sampling_success_space_def query_agreement_indices_def
    by (auto split: if_splits)
  have consistent: "query_consistent_at trace_table composition_table as ?idx"
    using success
    unfolding query_sampling_success_space_def query_agreement_indices_def
    by (auto split: if_splits)
  have trace_len: "length trace_openings = rounds"
    by (rule accepted_with_partial_trace_openings_shapes(2)
        [OF trace_partial])
  have comp_len: "length composition_openings = rounds"
    by (rule accepted_with_partial_composition_openings_shapes(2)
        [OF comp_partial])
  have trace_indices:
    "map opening_index (trace_openings ! i) = powers_scaled ?idx"
    by (rule accepted_with_partial_trace_openings_shapes(3)
        [OF trace_partial i_bound])
  have comp_indices:
    "map opening_index (composition_openings ! i) =
      [?idx, fri_sibling_index (scale * clength) ?idx]"
    by (rule accepted_with_partial_composition_openings_shapes(3)
        [OF comp_partial i_bound])
  have trace_values:
    "map ((!) trace_table) (powers_scaled ?idx) =
      map opening_value (trace_openings ! i)"
    by (rule partial_trace_table_candidate_query_values
        [OF trace_candidate i_bound trace_indices])
  have composition_value:
    "composition_table ! ?idx =
      opening_value ((composition_openings ! i) ! 0)"
    by (rule partial_composition_table_candidate_query_value
        [OF comp_candidate i_bound comp_indices])
  have opened_value:
    "opening_value ((composition_openings ! i) ! 0) =
      cp_eval as (map opening_value (trace_openings ! i))
        (h ^ ?idx * shift)"
    using consistent trace_values composition_value
    unfolding query_consistent_at_def by simp
  show ?thesis
    by (rule partial_query_round_consistentI
        [OF i_bound idx_sample trace_len comp_len trace_indices comp_indices
          opened_value])
qed

definition query_header_supported_partial_opening_witnesses
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow>
      ('f authenticated_opening list \<times>
        'f authenticated_opening list) set"
where
  "query_header_supported_partial_opening_witnesses s fr f_fri_roots
      f_final as dg composition_fri_roots final =
    {(trace_openings, composition_openings).
      composition_fri_roots \<noteq> [] \<and>
      (\<exists>result final_state rest.
        Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
        partial_authenticated_table fr (scale * clength) trace_openings
          final_state \<and>
        partial_authenticated_table (hd composition_fri_roots)
          (scale * clength) composition_openings final_state \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest)}"

lemma query_header_supported_partial_opening_witnessesE:
  assumes
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s fr f_fri_roots
        f_final as dg composition_fri_roots final"
  obtains result final_state rest where
    "composition_fri_roots \<noteq> []"
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    "partial_authenticated_table fr (scale * clength) trace_openings
      final_state"
    "partial_authenticated_table (hd composition_fri_roots)
      (scale * clength) composition_openings final_state"
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
  using assms
  unfolding query_header_supported_partial_opening_witnesses_def
  by blast

definition query_header_supported_partial_opening_success_indices_at
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> nat set"
where
  "query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i =
    {idx \<in> query_sample_space.
      \<exists>trace_openings composition_openings.
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses s fr
            f_fri_roots f_final as dg composition_fri_roots final \<and>
        partial_query_openings_consistent trace_openings composition_openings
          as idx}"

lemma query_header_supported_partial_opening_success_indices_at_subset:
  "query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i
    \<subseteq> query_sample_space"
  unfolding query_header_supported_partial_opening_success_indices_at_def
  by auto

lemma query_header_supported_partial_opening_success_indices_atE:
  assumes
    "idx \<in> query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i"
  obtains trace_openings composition_openings where
    "idx \<in> query_sample_space"
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s fr
        f_fri_roots f_final as dg composition_fri_roots final"
    "partial_query_openings_consistent trace_openings composition_openings
      as idx"
  using assms
  unfolding query_header_supported_partial_opening_success_indices_at_def
  by blast

lemma query_header_supported_partial_opening_success_indices_at_UN:
  "query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i =
    (\<Union>(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses s fr
          f_fri_roots f_final as dg composition_fri_roots final.
      {idx \<in> query_sample_space.
        partial_query_openings_consistent trace_openings
          composition_openings as idx})"
  unfolding query_header_supported_partial_opening_success_indices_at_def
  by auto

lemma query_header_supported_partial_opening_success_indices_at_subset_if_witnesses:
  assumes cover:
    "\<And>trace_openings composition_openings.
      (trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses s fr
          f_fri_roots f_final as dg composition_fri_roots final \<Longrightarrow>
      {idx \<in> query_sample_space.
        partial_query_openings_consistent trace_openings
          composition_openings as idx} \<subseteq> B"
  shows
    "query_header_supported_partial_opening_success_indices_at s fr
      f_fri_roots f_final as dg composition_fri_roots final i \<subseteq> B"
  unfolding query_header_supported_partial_opening_success_indices_at_UN
  using cover by auto

lemma query_header_supported_partial_opening_success_indices_atI_from_bound_tables:
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and trace_bind:
      "merkle_root_binds_table fr trace_table final_state"
    and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots) composition_table
        final_state"
    and trace_len: "length trace_table = scale * clength"
    and comp_len: "length composition_table = scale * clength"
    and trace_auth:
      "partial_authenticated_table fr (scale * clength) trace_openings
        final_state"
    and comp_auth:
      "partial_authenticated_table (hd composition_fri_roots)
        (scale * clength) composition_openings final_state"
    and clean: "\<not> hash_map_output_collision final_state"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and comp_indices:
      "map opening_index composition_openings =
        [idx, fri_sibling_index (scale * clength) idx]"
    and success:
      "idx \<in> query_sampling_success_space trace_table composition_table as"
  shows
    "idx \<in>
      query_header_supported_partial_opening_success_indices_at s fr
        f_fri_roots f_final as dg composition_fri_roots final i"
proof -
  have consistent:
    "partial_query_openings_consistent trace_openings composition_openings
      as idx"
    by (rule partial_query_openings_consistent_from_sampling_success
        [OF trace_bind comp_bind trace_len comp_len trace_auth comp_auth
          clean trace_indices comp_indices success])
  have witness:
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_opening_witnesses_def
    using comp_nonempty outcome trace_auth comp_auth header
    by (auto split: prod.splits)
  have idx_sample: "idx \<in> query_sample_space"
    using consistent
    unfolding partial_query_openings_consistent_def by simp
  show ?thesis
    unfolding query_header_supported_partial_opening_success_indices_at_def
    by (intro CollectI conjI exI[of _ trace_openings]
        exI[of _ composition_openings])
      (use idx_sample witness consistent in simp_all)
qed

lemma query_header_supported_partial_opening_success_indices_atI_from_partials:
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) composition_root query_idxs
        composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and root_eq: "composition_root = hd composition_fri_roots"
    and i_bound: "i < rounds"
    and success:
      "query_idxs ! i \<in>
        query_sampling_success_space trace_table composition_table as"
  shows
    "query_idxs ! i \<in>
      query_header_supported_partial_opening_success_indices_at s fr
        f_fri_roots f_final as dg composition_fri_roots final i"
proof -
  let ?trace_openings = "trace_openings ! i"
  let ?composition_openings = "composition_openings ! i"
  have consistent_round:
    "partial_query_round_consistent trace_openings composition_openings as
      i (query_idxs ! i)"
    by (rule partial_query_round_consistent_from_sampling_success
        [OF trace_partial comp_partial trace_candidate comp_candidate
          i_bound success])
  have consistent:
    "partial_query_openings_consistent ?trace_openings
      ?composition_openings as (query_idxs ! i)"
    unfolding partial_query_openings_consistent_def
    using consistent_round
    unfolding partial_query_round_consistent_def
    by simp
  have trace_table:
    "partial_authenticated_table fr (scale * clength) ?trace_openings
      final_state"
    using trace_partial i_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  have comp_table:
    "partial_authenticated_table (hd composition_fri_roots)
      (scale * clength) ?composition_openings final_state"
    using comp_partial i_bound root_eq
    unfolding accepted_with_partial_composition_openings_def by blast
  have witness:
    "(?trace_openings, ?composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_opening_witnesses_def
    using comp_nonempty outcome trace_table comp_table header
    by auto
  have idx_sample:
    "query_idxs ! i \<in> query_sample_space"
    using consistent unfolding partial_query_openings_consistent_def by simp
  show ?thesis
    unfolding query_header_supported_partial_opening_success_indices_at_def
    by (intro CollectI conjI exI[of _ ?trace_openings]
        exI[of _ ?composition_openings])
      (use idx_sample witness consistent in simp_all)
qed

lemma partial_query_round_consistent_from_all_queries_consistent:
  assumes trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) composition_root query_idxs
        composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and i_bound: "i < rounds"
    and idx_sample: "query_idxs ! i \<in> query_sample_space"
    and all_queries:
      "all_queries_consistent trace_table composition_table as"
  shows
    "partial_query_round_consistent trace_openings composition_openings as
      i (query_idxs ! i)"
proof -
  let ?idx = "query_idxs ! i"
  have trace_len: "length trace_openings = rounds"
    using trace_partial unfolding accepted_with_partial_trace_openings_def
    by blast
  have comp_len: "length composition_openings = rounds"
    using comp_partial
    unfolding accepted_with_partial_composition_openings_def by blast
  have trace_indices:
    "map opening_index (trace_openings ! i) = powers_scaled ?idx"
    using trace_partial i_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  have comp_indices:
    "map opening_index (composition_openings ! i) =
      [?idx, fri_sibling_index (scale * clength) ?idx]"
    using comp_partial i_bound
    unfolding accepted_with_partial_composition_openings_def by blast
  have qc:
    "query_consistent_at trace_table composition_table as ?idx"
    using all_queries idx_sample unfolding all_queries_consistent_def
    by simp
  have trace_values:
    "map ((!) trace_table) (powers_scaled ?idx) =
      map opening_value (trace_openings ! i)"
    by (rule partial_trace_table_candidate_query_values
        [OF trace_candidate i_bound trace_indices])
  have comp_value:
    "composition_table ! ?idx =
      opening_value ((composition_openings ! i) ! 0)"
    by (rule partial_composition_table_candidate_query_value
        [OF comp_candidate i_bound comp_indices])
  have opened_value:
    "opening_value ((composition_openings ! i) ! 0) =
      cp_eval as (map opening_value (trace_openings ! i))
        (h ^ ?idx * shift)"
    using qc trace_values comp_value unfolding query_consistent_at_def
    by simp
  show ?thesis
    by (rule partial_query_round_consistentI
        [OF i_bound idx_sample trace_len comp_len trace_indices
          comp_indices opened_value])
qed

lemma query_header_supported_partial_opening_success_indices_atI_from_partials_consistent:
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) composition_root query_idxs
        composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and root_eq: "composition_root = hd composition_fri_roots"
    and i_bound: "i < rounds"
    and idx_sample: "query_idxs ! i \<in> query_sample_space"
    and all_queries:
      "all_queries_consistent trace_table composition_table as"
  shows
    "query_idxs ! i \<in>
      query_header_supported_partial_opening_success_indices_at s fr
        f_fri_roots f_final as dg composition_fri_roots final i"
proof -
  let ?trace_openings = "trace_openings ! i"
  let ?composition_openings = "composition_openings ! i"
  have consistent_round:
    "partial_query_round_consistent trace_openings composition_openings as
      i (query_idxs ! i)"
    by (rule partial_query_round_consistent_from_all_queries_consistent
        [OF trace_partial comp_partial trace_candidate comp_candidate
          i_bound idx_sample all_queries])
  have consistent:
    "partial_query_openings_consistent ?trace_openings
      ?composition_openings as (query_idxs ! i)"
    unfolding partial_query_openings_consistent_def
    using consistent_round
    unfolding partial_query_round_consistent_def
    by simp
  have trace_table:
    "partial_authenticated_table fr (scale * clength) ?trace_openings
      final_state"
    using trace_partial i_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  have comp_table:
    "partial_authenticated_table (hd composition_fri_roots)
      (scale * clength) ?composition_openings final_state"
    using comp_partial i_bound root_eq
    unfolding accepted_with_partial_composition_openings_def by blast
  have witness:
    "(?trace_openings, ?composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_opening_witnesses_def
    using comp_nonempty outcome trace_table comp_table header
    by auto
  show ?thesis
    unfolding query_header_supported_partial_opening_success_indices_at_def
    by (intro CollectI conjI exI[of _ ?trace_openings]
        exI[of _ ?composition_openings])
      (use idx_sample witness consistent in simp_all)
qed

definition staged_security_with_data_state_query_partial_opening_hit_at
  :: "nat \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "staged_security_with_data_state_query_partial_opening_hit_at i out
    \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), _), final_state) \<Rightarrow>
          (let s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data);
           B =
            query_header_supported_partial_opening_success_indices_at s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              (staged_alphas data)
              (staged_degree data)
              (staged_composition_fri_roots data)
              (staged_composition_final data)
              i
           in
            (\<exists>raw.
              i < rounds \<and>
              fmlookup (HashMap final_state)
                (QueryIndexChallenge i
                  (state_after_query_chunks
                    (staged_query_start_hash data)
                    (staged_query_chunks data) i)) =
                Some raw \<and>
              index (to_nat raw) \<in> B)))"

definition staged_security_with_data_state_query_partial_opening_hit
  :: "((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "staged_security_with_data_state_query_partial_opening_hit out \<longleftrightarrow>
    (\<exists>i < rounds.
      staged_security_with_data_state_query_partial_opening_hit_at i out)"

lemma staged_security_with_data_state_query_partial_opening_hit_atD:
  assumes
    "staged_security_with_data_state_query_partial_opening_hit_at i out"
  shows "i < rounds"
  using assms
  unfolding staged_security_with_data_state_query_partial_opening_hit_at_def
  by (cases out; auto split: prod.splits)

lemma staged_security_with_data_state_query_partial_opening_hit_atE:
  assumes
    "staged_security_with_data_state_query_partial_opening_hit_at i
      (Some (((data, attacker_state), result), final_state))"
  obtains raw where
    "i < rounds"
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some raw"
    "index (to_nat raw) \<in>
      query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i"
  using assms
  unfolding staged_security_with_data_state_query_partial_opening_hit_at_def
    Let_def
  by auto

lemma staged_security_with_data_state_query_partial_opening_hitI:
  assumes "i < rounds"
    and "staged_security_with_data_state_query_partial_opening_hit_at i out"
  shows "staged_security_with_data_state_query_partial_opening_hit out"
  using assms
  unfolding staged_security_with_data_state_query_partial_opening_hit_def
  by blast

lemma staged_security_with_data_state_query_partial_opening_hit_imp_round_hit:
  assumes hit: "staged_security_with_data_state_query_partial_opening_hit out"
  shows "\<exists>i \<in> {..<rounds}.
    staged_security_with_data_state_query_partial_opening_hit_at i out"
  using assms
  unfolding staged_security_with_data_state_query_partial_opening_hit_def
  by blast

lemma checked_staged_security_with_data_state_query_partial_opening_hit_bound_from_rounds:
  assumes round_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_partial_opening_hit_at i)
        adversary_initial_state \<le> C i"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out. \<exists>i \<in> {..<rounds}.
        staged_security_with_data_state_query_partial_opening_hit_at i out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule staged_security_with_data_state_query_partial_opening_hit_imp_round_hit)
  also have "... \<le> (\<Sum>i<rounds. C i)"
    by (rule wp_event_finite_UN_bound)
      (simp_all add: round_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_partial_opening_hit_bound_from_index_set:
  assumes cover:
    "\<And>data attacker_state i.
      i < rounds \<Longrightarrow>
      query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<subseteq> B"
    and index_bound:
      "wp_event (checked_staged_security_experiment_with_data A)
        (staged_security_with_data_query_index_set_hit B)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state \<le> C"
proof -
  let ?projected =
    "\<lambda>out. case out of None \<Rightarrow>
        staged_security_with_data_query_index_set_hit B None
      | Some (((data, _), result), t) \<Rightarrow>
        staged_security_with_data_query_index_set_hit B
          (Some ((data, result), t))"
  have event_le:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?projected adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume hit:
      "staged_security_with_data_state_query_partial_opening_hit out"
    show "?projected out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding staged_security_with_data_state_query_partial_opening_hit_def
          staged_security_with_data_state_query_partial_opening_hit_at_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      let ?B =
        "\<lambda>i. query_header_supported_partial_opening_success_indices_at ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)
          i"
      from hit[unfolded out_eq
          staged_security_with_data_state_query_partial_opening_hit_def
          staged_security_with_data_state_query_partial_opening_hit_at_def
          Let_def]
      obtain i raw where i_bound: "i < rounds"
        and lookup:
          "fmlookup (HashMap final_state)
            (QueryIndexChallenge i
              (state_after_query_chunks
                (staged_query_start_hash data)
                (staged_query_chunks data) i)) =
            Some raw"
        and raw_hit: "index (to_nat raw) \<in> ?B i"
        by auto
      have raw_in_B: "index (to_nat raw) \<in> B"
      proof -
        have "?B i \<subseteq> B"
          by (rule cover[OF i_bound])
        then show ?thesis
          using raw_hit by blast
      qed
      show ?thesis
        unfolding out_eq staged_security_with_data_query_index_set_hit_def
        using i_bound lookup raw_in_B by auto
    qed
  qed
  also have
    "wp_event (checked_staged_security_experiment_with_data_state A)
      ?projected adversary_initial_state =
     wp_event (checked_staged_security_experiment_with_data A)
      (staged_security_with_data_query_index_set_hit B)
      adversary_initial_state"
    using checked_staged_security_experiment_with_data_event_from_data_state
      [of A "staged_security_with_data_query_index_set_hit B"]
    by simp
  also have "... \<le> C"
    by (rule index_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_partial_opening_hit_bound_from_index_set_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
    "\<And>data attacker_state i.
      i < rounds \<Longrightarrow>
      query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<subseteq> B"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule
    checked_staged_security_with_data_state_partial_opening_hit_bound_from_index_set)
  fix data attacker_state i
  assume i_bound: "i < rounds"
  show
    "query_header_supported_partial_opening_success_indices_at
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      i \<subseteq> B"
    by (rule cover[OF i_bound])
next
  show
    "wp_event (checked_staged_security_experiment_with_data A)
      (staged_security_with_data_query_index_set_hit B)
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule checked_staged_security_with_data_query_index_set_hit_bound
        [OF wf controlled])
qed

lemma checked_staged_security_with_data_state_partial_opening_hit_bound_from_fixed_query_error_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
    "\<And>data attacker_state i.
      i < rounds \<Longrightarrow>
      query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<subseteq> B"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (card B) / nnreal (card query_sample_space) \<le>
        query_error_bound"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
proof -
  have target:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_with_data_state_partial_opening_hit_bound_from_index_set_controlled
        [OF wf controlled cover])
  also have "... \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
    by (rule staged_phase_query_index_target_error_query_bound
        [OF raw_bound subset frac])
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_query_bad_imp_partial_opening_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_query_bad_hit
        (Some (((data, attacker_state), result), final_state))"
  shows
    "staged_security_with_data_state_query_partial_opening_hit
      (Some (((data, attacker_state), result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support]
  obtain builder where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  show ?thesis
  proof (rule checked_staged_security_with_data_state_query_bad_round_chunkE
      [OF wf controlled support bad])
    fix i trace_table composition_table query_idxs raw_idxs
    assume i_bound: "i < rounds"
      and bound:
        "accepted_with_bound_tables ?s (Some (result, final_state))
          trace_table composition_table (staged_alphas data) query_idxs"
      and success:
        "query_idxs ! i \<in>
          query_sampling_success_space trace_table composition_table
            (staged_alphas data)"
      and len_raw: "length raw_idxs = rounds"
      and query_idxs_eq:
        "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
      and query_chunk:
        "verifier_query_round_chunk (query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! i)"
      and lookup:
        "fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data) (staged_query_chunks data) i)) =
          Some (raw_idxs ! i)"
    show ?thesis
    proof (rule accepted_with_bound_tables_partial_opening_witnesses_Some
        [OF bound])
      fix fr f_fri_roots f_final dg composition_fri_roots final rest
          trace_openings composition_openings
      assume header:
        "verifier_header_transcript ?s fr f_fri_roots f_final
          (staged_alphas data) dg composition_fri_roots final rest"
        and comp_nonempty: "composition_fri_roots \<noteq> []"
        and trace_partial:
        "accepted_with_partial_trace_openings ?s
          (Some (result, final_state)) fr query_idxs trace_openings"
        and comp_partial:
        "accepted_with_partial_composition_openings ?s
          (Some (result, final_state)) (hd composition_fri_roots)
          query_idxs composition_openings"
        and trace_candidate:
        "partial_trace_table_candidate trace_table trace_openings"
        and comp_candidate:
        "partial_composition_table_candidate composition_table
          composition_openings"
        and trace_bind:
        "merkle_root_binds_table fr trace_table final_state"
        and comp_bind:
        "merkle_root_binds_table (hd composition_fri_roots)
          composition_table final_state"
      have header_eq:
        "fr = staged_trace_root data \<and>
         f_fri_roots = staged_trace_fri_roots data \<and>
         f_final = staged_trace_final data \<and>
         dg = staged_degree data \<and>
         composition_fri_roots = staged_composition_fri_roots data \<and>
         final = staged_composition_final data \<and>
         rest = List.concat (staged_query_chunks data)"
        using verifier_header_transcript_unique[OF staged_header header]
        by simp
      have idx_in_header_set:
        "query_idxs ! i \<in>
          query_header_supported_partial_opening_success_indices_at ?s fr
            f_fri_roots f_final (staged_alphas data) dg
            composition_fri_roots final i"
        by (rule
            query_header_supported_partial_opening_success_indices_atI_from_partials
            [OF verifier trace_partial comp_partial trace_candidate
              comp_candidate header comp_nonempty refl i_bound success])
      have idx_in_staged_set:
        "query_idxs ! i \<in>
          query_header_supported_partial_opening_success_indices_at ?s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)
            i"
        using idx_in_header_set header_eq by simp
      have raw_idx:
        "index (to_nat (raw_idxs ! i)) = query_idxs ! i"
        using query_idxs_eq len_raw i_bound by simp
      have hit_at:
        "staged_security_with_data_state_query_partial_opening_hit_at i
          (Some (((data, attacker_state), result), final_state))"
        unfolding
          staged_security_with_data_state_query_partial_opening_hit_at_def
        using i_bound lookup idx_in_staged_set raw_idx
        by (simp add: Let_def)
      show ?thesis
        by (rule staged_security_with_data_state_query_partial_opening_hitI
      [OF i_bound hit_at])
    qed
  qed
qed

lemma checked_staged_security_with_data_state_query_bad_bound_from_partial_opening_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
    "out \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    and bad: "staged_security_with_data_state_query_bad_hit out"
  show "staged_security_with_data_state_query_partial_opening_hit out"
  proof (cases out)
    case None
    then show ?thesis
      using bad unfolding staged_security_with_data_state_query_bad_hit_def
      by simp
  next
    case (Some packed)
    then obtain data attacker_state result final_state where out_eq:
      "out = Some (((data, attacker_state), result), final_state)"
      by (cases packed, auto split: prod.splits)
    show ?thesis
      unfolding out_eq
      by (rule
          checked_staged_security_with_data_state_query_bad_imp_partial_opening_hit_on_support
          [OF wf controlled])
        (use support bad out_eq in simp_all)
  qed
qed

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_partial_opening_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and partial_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_opening_hit
        adversary_initial_state \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le> Q"
proof -
  have query_hit_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le> Q"
    by (rule order.trans
        [OF checked_staged_security_with_data_state_query_bad_bound_from_partial_opening_hit
          [OF wf controlled] partial_bound])
  show ?thesis
    by (rule checked_staged_security_with_data_state_query_bad_verifier_event_bound
        [OF query_hit_bound])
qed

lemma checked_staged_security_with_data_state_query_bad_bound_from_partial_opening_fixed_query_error_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
    "\<And>data attacker_state i.
      i < rounds \<Longrightarrow>
      query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<subseteq> B"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (card B) / nnreal (card query_sample_space) \<le>
        query_error_bound"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_query_bad_bound_from_partial_opening_hit
        [OF wf controlled])
  also have "... \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
    by (rule
        checked_staged_security_with_data_state_partial_opening_hit_bound_from_fixed_query_error_cover
        [OF wf controlled cover raw_bound subset frac])
  finally show ?thesis .
qed

lemma verifier_query_round_program_authenticated_initial_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx trace_leaves trace_openings composition_openings where
    "idx = index (to_nat raw)"
    "map opening_value trace_openings = trace_leaves"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where tail:
    "Some ((), t) \<in>
      set_dist
        (execute
          (verifier_query_round_after_index_program
            fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  show ?thesis
  proof (rule verifier_query_round_after_index_authenticated_trace_openings
      [OF tail])
    fix idx trace_leaves trace_openings
    assume idx_eq: "idx = index (to_nat raw)"
      and trace_values:
        "map opening_value trace_openings = trace_leaves"
      and trace_indices:
        "map opening_index trace_openings = powers_scaled idx"
      and trace_table:
        "partial_authenticated_table fr (scale * clength) trace_openings t"
    show ?thesis
    proof (rule
        verifier_query_round_after_index_authenticated_composition_openings
        [OF fl_eq tail])
      fix idx' composition_openings
      assume idx'_eq: "idx' = index (to_nat raw)"
        and comp_table:
          "partial_authenticated_table composition_root (scale * clength)
            composition_openings t"
        and comp_indices:
          "map opening_index composition_openings =
            [idx', fri_sibling_index (scale * clength) idx']"
      have idx'_idx: "idx' = idx"
        using idx_eq idx'_eq by simp
      show ?thesis
        by (rule that[OF idx_eq trace_values trace_indices trace_table
              comp_table])
          (use comp_indices idx'_idx in simp)
    qed
  qed
qed

lemma verifier_query_round_program_authenticated_initial_openings_with_lookup:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx trace_leaves trace_openings composition_openings where
    "idx = index (to_nat raw)"
    "map opening_value trace_openings = trace_leaves"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
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
  proof (rule verifier_query_round_after_index_authenticated_trace_openings
      [OF tail])
    fix idx trace_leaves trace_openings
    assume idx_eq: "idx = index (to_nat raw)"
      and trace_values:
        "map opening_value trace_openings = trace_leaves"
      and trace_indices:
        "map opening_index trace_openings = powers_scaled idx"
      and trace_table:
        "partial_authenticated_table fr (scale * clength) trace_openings t"
    show ?thesis
    proof (rule
        verifier_query_round_after_index_authenticated_composition_openings
        [OF fl_eq tail])
      fix idx' composition_openings
      assume idx'_eq: "idx' = index (to_nat raw)"
        and comp_table:
          "partial_authenticated_table composition_root (scale * clength)
            composition_openings t"
        and comp_indices:
          "map opening_index composition_openings =
            [idx', fri_sibling_index (scale * clength) idx']"
      have idx'_idx: "idx' = idx"
        using idx_eq idx'_eq by simp
      show ?thesis
        by (rule that[OF idx_eq trace_values trace_indices trace_table
              comp_table _ lookup_t])
          (use comp_indices idx'_idx in simp)
    qed
  qed
qed

lemma verifier_query_round_program_authenticated_initial_openings_with_chunk:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx chunk trace_leaves trace_openings composition_openings
  where
    "idx = index (to_nat raw)"
    "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    "PTranscript s = chunk @ PTranscript t"
    "PState t = foldl concat (PState s) chunk"
    "s \<le> t"
    "PQueryCounter t = Suc (PQueryCounter s)"
    "map opening_value trace_openings = trace_leaves"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  show ?thesis
  proof (rule verifier_query_round_program_outcome[OF outcome])
    fix raw0 idx0 chunk
    assume idx0_eq: "idx0 = index (to_nat raw0)"
      and chunk_shape:
        "verifier_query_round_chunk idx0 (map snd f_fl) (map snd fl)
          chunk"
      and transcript:
        "PTranscript s = chunk @ PTranscript t"
      and state:
        "PState t = foldl concat (PState s) chunk"
      and ext: "s \<le> t"
      and counter:
        "PQueryCounter t = Suc (PQueryCounter s)"
      and lookup0:
        "fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw0"
    show ?thesis
    proof (rule
        verifier_query_round_program_authenticated_initial_openings_with_lookup
          [OF fl_eq outcome])
      fix raw idx trace_leaves trace_openings composition_openings
      assume idx_eq: "idx = index (to_nat raw)"
        and trace_values:
          "map opening_value trace_openings = trace_leaves"
        and trace_indices:
          "map opening_index trace_openings = powers_scaled idx"
        and trace_table:
          "partial_authenticated_table fr (scale * clength)
            trace_openings t"
        and comp_table:
          "partial_authenticated_table composition_root (scale * clength)
            composition_openings t"
        and comp_indices:
          "map opening_index composition_openings =
            [idx, fri_sibling_index (scale * clength) idx]"
        and lookup:
          "fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
      have raw_eq: "raw = raw0"
        using lookup lookup0 by simp
      have idx_idx0: "idx = idx0"
        using idx_eq idx0_eq raw_eq by simp
      show ?thesis
        by (rule that[OF idx_eq _ transcript state ext counter
              trace_values trace_indices trace_table comp_table comp_indices
              lookup])
          (use chunk_shape idx_idx0 in simp)
    qed
  qed
qed

lemma ntimes_verifier_query_rounds_authenticated_initial_openings_at:
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
  obtains raw idx trace_leaves trace_openings composition_openings where
    "idx = index (to_nat raw)"
    "map opening_value trace_openings = trace_leaves"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
proof -
  have
    "\<exists>raw idx trace_leaves trace_openings composition_openings.
      idx = index (to_nat raw) \<and>
      map opening_value trace_openings = trace_leaves \<and>
      map opening_index trace_openings = powers_scaled idx \<and>
      partial_authenticated_table fr (scale * clength) trace_openings t \<and>
      partial_authenticated_table composition_root (scale * clength)
        composition_openings t \<and>
      map opening_index composition_openings =
        [idx, fri_sibling_index (scale * clength) idx]"
    using outcome i_bound
  proof (induction n arbitrary: i s results t)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    from Suc.prems(1) obtain u results' s1 where
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
    show ?case
    proof (cases i)
      case 0
      show ?thesis
      proof (rule verifier_query_round_program_authenticated_initial_openings
          [OF fl_eq head[unfolded u_eq]])
        fix raw idx trace_leaves trace_openings composition_openings
        assume idx_eq: "idx = index (to_nat raw)"
          and trace_values:
            "map opening_value trace_openings = trace_leaves"
          and trace_indices:
            "map opening_index trace_openings = powers_scaled idx"
          and trace_table_s1:
            "partial_authenticated_table fr (scale * clength)
              trace_openings s1"
          and comp_table_s1:
            "partial_authenticated_table composition_root (scale * clength)
              composition_openings s1"
          and comp_indices:
            "map opening_index composition_openings =
              [idx, fri_sibling_index (scale * clength) idx]"
        from ntimes_verifier_query_rounds_outcome[OF tail]
        obtain raw_idxs query_idxs query_chunks where
          s1_t: "s1 \<le> t"
          by (elim exE conjE)
        have trace_table_t:
          "partial_authenticated_table fr (scale * clength)
            trace_openings t"
          by (rule partial_authenticated_table_mono[OF trace_table_s1 s1_t])
        have comp_table_t:
          "partial_authenticated_table composition_root (scale * clength)
            composition_openings t"
          by (rule partial_authenticated_table_mono[OF comp_table_s1 s1_t])
        show ?thesis
          apply (rule exI[where x=raw])
          apply (rule exI[where x=idx])
          apply (rule exI[where x=trace_leaves])
          apply (rule exI[where x=trace_openings])
          apply (rule exI[where x=composition_openings])
          apply (intro conjI)
               apply (rule idx_eq)
              apply (rule trace_values)
             apply (rule trace_indices)
            apply (rule trace_table_t)
          apply (rule comp_table_t)
          apply (rule comp_indices)
          done
      qed
    next
      case (Suc j)
      have j_bound: "j < n"
        using Suc.prems(2) \<open>i = Suc j\<close> by simp
      from Suc.IH[OF tail j_bound] show ?thesis .
    qed
  qed
  then obtain raw idx trace_leaves trace_openings composition_openings where
    idx_eq: "idx = index (to_nat raw)"
    and trace_values:
      "map opening_value trace_openings = trace_leaves"
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
    by (elim exE conjE)
  show ?thesis
    by (rule that[OF idx_eq trace_values trace_indices trace_table
          comp_table comp_indices])
qed

lemma accepted_with_bound_tables_partial_opening_header_witness_at:
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and i_bound: "i < rounds"
  obtains trace_openings composition_openings where
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s fr f_fri_roots
        f_final as dg composition_fri_roots final"
proof -
  show ?thesis
  proof (rule accepted_with_bound_tables_partial_opening_witnesses_Some[OF bound])
    fix fr' f_fri_roots' f_final' dg' composition_fri_roots' final'
        rest' trace_openingss composition_openingss
    assume
    header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and comp_nonempty': "composition_fri_roots' \<noteq> []"
    and trace_partial:
      "accepted_with_partial_trace_openings s (Some (result, final_state))
        fr' query_idxs trace_openingss"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots')
        query_idxs composition_openingss"
    have eqs:
      "fr' = fr \<and>
       f_fri_roots' = f_fri_roots \<and>
       f_final' = f_final \<and>
       dg' = dg \<and>
       composition_fri_roots' = composition_fri_roots \<and>
       final' = final \<and>
       rest' = rest"
      using verifier_header_transcript_unique[OF header' header] by simp
    have trace_table_i:
      "partial_authenticated_table fr (scale * clength)
        (trace_openingss ! i) final_state"
      using trace_partial i_bound eqs
      unfolding accepted_with_partial_trace_openings_def by blast
    have comp_table_i:
      "partial_authenticated_table (hd composition_fri_roots) (scale * clength)
        (composition_openingss ! i) final_state"
      using comp_partial i_bound eqs
      unfolding accepted_with_partial_composition_openings_def by simp
    have witness:
      "(trace_openingss ! i, composition_openingss ! i) \<in>
        query_header_supported_partial_opening_witnesses s fr f_fri_roots
          f_final as dg composition_fri_roots final"
      unfolding query_header_supported_partial_opening_witnesses_def
      using outcome header trace_table_i comp_table_i comp_nonempty' eqs
      by auto
    show ?thesis
      by (rule that[OF witness])
  qed
qed

lemma checked_actual_alpha_prefix_support_partial_opening_header_witness_at:
  fixes prefix prefix_state data attacker_state result final_state
  defines
    "s \<equiv>
      verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
  assumes support:
      "Some (((((prefix, prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and i_bound: "i < rounds"
  obtains trace_openings composition_openings where
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s fr f_fri_roots
        f_final as dg composition_fri_roots final"
proof -
  have verify_out:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using support
    unfolding checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
      s_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  show ?thesis
    by (rule accepted_with_bound_tables_partial_opening_header_witness_at
        [OF verify_out header bound i_bound that])
qed

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_header_witness_at:
  fixes prefix prefix_state data attacker_state result final_state
  defines
    "s \<equiv>
      verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
  assumes support:
      "Some (((((prefix, prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
        (Some (((((prefix, prefix_state), data), attacker_state),
          result), final_state))"
    and i_bound: "i < rounds"
  obtains as dg composition_fri_roots final rest trace_table composition_table
      query_idxs trace_openings composition_openings where
    "accepted_with_bound_tables s (Some (result, final_state))
      trace_table composition_table as query_idxs"
    "verifier_header_transcript s
      (staged_trace_root data) (staged_trace_fri_roots data)
      (staged_trace_final data) as dg composition_fri_roots final rest"
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s
        (staged_trace_root data) (staged_trace_fri_roots data)
        (staged_trace_final data) as dg composition_fri_roots final"
proof -
  obtain trace_table composition_table as query_idxs dg
      composition_fri_roots final rest trace_tree composition_tree where
    verify_out:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript s
        (staged_trace_root data) (staged_trace_fri_roots data)
        (staged_trace_final data) as dg composition_fri_roots final rest"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit_def
      s_def Let_def
    by auto
  obtain trace_openings composition_openings where witness:
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s
        (staged_trace_root data) (staged_trace_fri_roots data)
        (staged_trace_final data) as dg composition_fri_roots final"
    by (rule accepted_with_bound_tables_partial_opening_header_witness_at
        [OF verify_out header bound i_bound])
  show ?thesis
    by (rule that[OF bound header witness])
qed

definition
  checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (let s =
          verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)
         in \<exists>as dg composition_fri_roots final rest trace_table
              composition_table query_idxs trace_openings composition_openings.
          accepted_with_bound_tables s (Some (result, final_state))
            trace_table composition_table as query_idxs \<and>
          verifier_header_transcript s
            (staged_trace_root data) (staged_trace_fri_roots data)
            (staged_trace_final data) as dg composition_fri_roots final rest \<and>
          (trace_openings, composition_openings) \<in>
            query_header_supported_partial_opening_witnesses s
              (staged_trace_root data) (staged_trace_fri_roots data)
              (staged_trace_final data) as dg composition_fri_roots final))"

lemma checked_actual_alpha_prefix_branch_subtree_verifier_imp_partial_opening_witness_hit_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
        out"
  shows
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state result final_state where
    out_eq:
      "out = Some (((((prefix, prefix_state), data), attacker_state),
        result), final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have support_some:
    "Some (((((prefix, prefix_state), data), attacker_state),
        result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
    using support unfolding out_eq .
  have hit_some:
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
      (Some (((((prefix, prefix_state), data), attacker_state),
        result), final_state))"
    using hit unfolding out_eq .
  obtain as dg composition_fri_roots final rest trace_table composition_table
      query_idxs trace_openings composition_openings where
    bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root data) (staged_trace_fri_roots data)
        (staged_trace_final data) as dg composition_fri_roots final rest"
    and witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses ?s
          (staged_trace_root data) (staged_trace_fri_roots data)
          (staged_trace_final data) as dg composition_fri_roots final"
  proof -
    obtain trace_table composition_table as query_idxs dg
        composition_fri_roots final rest trace_tree composition_tree where
      verify_out:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
      and bound:
        "accepted_with_bound_tables ?s (Some (result, final_state))
          trace_table composition_table as query_idxs"
      and header:
        "verifier_header_transcript ?s
          (staged_trace_root data) (staged_trace_fri_roots data)
          (staged_trace_final data) as dg composition_fri_roots final rest"
      using hit_some
      unfolding
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit_def
        Let_def
      by auto
    obtain trace_openings composition_openings where witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses ?s
          (staged_trace_root data) (staged_trace_fri_roots data)
          (staged_trace_final data) as dg composition_fri_roots final"
      by (rule accepted_with_bound_tables_partial_opening_header_witness_at
          [OF verify_out header bound rounds_positive])
    show ?thesis
      by (rule that[OF bound header witness])
  qed
  show ?thesis
    unfolding out_eq
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit_def
      Let_def
    apply simp
    apply (rule exI[where x=as])
    apply (intro conjI)
     apply (rule exI[where x=trace_table])
     apply (rule exI[where x=composition_table])
     apply (rule exI[where x=query_idxs])
     apply (rule bound)
    apply (rule exI[where x=dg])
    apply (rule exI[where x=composition_fri_roots])
    apply (rule exI[where x=final])
    apply (intro conjI)
     apply (rule exI[where x=rest])
     apply (rule header)
    apply (rule exI[where x=trace_openings])
    apply (rule exI[where x=composition_openings])
    apply (rule witness)
    done
qed

end

end
