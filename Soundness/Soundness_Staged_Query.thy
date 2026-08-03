(*  Title:      Stark/Soundness_Staged_Query.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Query
  imports Soundness_Staged_Query_Prefix
begin

text \<open>Dynamic staged query target events and probability bounds.\<close>

context soundness
begin

definition checked_staged_query_prefix_dynamic_index_hit
  :: "('f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow>
        nat set) \<Rightarrow>
      ((('f staged_query_prefix_data \<times> 'f protocol_channel) \<times> 'f) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_query_prefix_dynamic_index_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((prefix, prefix_state), raw), _) \<Rightarrow>
          index (to_nat raw) \<in> B prefix prefix_state)"

definition staged_partial_query_target
  :: "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
  where
    "staged_partial_query_target data attacker_state =
      query_header_supported_partial_union_good_sets
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        query_sampling_success_space
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"

definition staged_query_prefix_matches_data
  :: "nat \<Rightarrow> 'f staged_query_prefix_data \<Rightarrow> 'f staged_proof_data \<Rightarrow>
      bool"
  where
    "staged_query_prefix_matches_data i prefix data \<longleftrightarrow>
      sqp_trace_root prefix = staged_trace_root data \<and>
      sqp_trace_fri_roots prefix = staged_trace_fri_roots data \<and>
      sqp_trace_fri_challenges prefix =
        staged_trace_fri_challenges data \<and>
      sqp_trace_final prefix = staged_trace_final data \<and>
      sqp_alphas prefix = staged_alphas data \<and>
      sqp_degree prefix = staged_degree data \<and>
      sqp_composition_fri_roots prefix =
        staged_composition_fri_roots data \<and>
      sqp_composition_fri_challenges prefix =
        staged_composition_fri_challenges data \<and>
      sqp_composition_final prefix =
        staged_composition_final data \<and>
      sqp_query_chunks prefix = take i (staged_query_chunks data)"

lemma staged_query_start_hash_of_prefix_completion:
  assumes match: "staged_query_prefix_matches_data i prefix data"
  shows "staged_query_start_hash data =
    staged_query_prefix_start_hash prefix"
  using match
  unfolding staged_query_prefix_matches_data_def
    staged_query_start_hash_def staged_composition_fri_start_hash_def
    staged_trace_fri_start_hash_def staged_query_prefix_start_hash_def
  by simp

definition staged_query_prefix_partial_query_target
  :: "nat \<Rightarrow> 'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow>
      nat set"
  where
    "staged_query_prefix_partial_query_target i prefix prefix_state =
      {idx. \<exists>data attacker_state.
        staged_query_prefix_matches_data i prefix data \<and>
        prefix_state \<le> attacker_state \<and>
        idx \<in> staged_partial_query_target data attacker_state}"

definition staged_query_prefix_committed_query_target
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
  where
    "staged_query_prefix_committed_query_target prefix prefix_state =
      query_header_committed_union_good_sets prefix_state
        query_sampling_success_space
        (sqp_trace_root prefix)
        (sqp_alphas prefix)
        (sqp_composition_fri_roots prefix)"

definition staged_query_prefix_length_committed_table_candidates
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow>
      ('f list \<times> 'f list) set"
  where
    "staged_query_prefix_length_committed_table_candidates prefix prefix_state =
      {(trace_table, composition_table).
        merkle_root_binds_table (sqp_trace_root prefix) trace_table
          prefix_state \<and>
        sqp_composition_fri_roots prefix \<noteq> [] \<and>
        merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
          composition_table prefix_state \<and>
        length trace_table = clength * scale \<and>
        length composition_table = clength * scale}"

definition staged_query_prefix_length_committed_query_target
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
  where
    "staged_query_prefix_length_committed_query_target prefix prefix_state =
      {idx \<in> query_sample_space.
        \<exists>trace_table composition_table.
          (trace_table, composition_table) \<in>
            staged_query_prefix_length_committed_table_candidates prefix
              prefix_state \<and>
          idx \<in> query_sampling_success_space trace_table
            composition_table (sqp_alphas prefix)}"

definition staged_query_prefix_clean_length_committed_query_target
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
  where
    "staged_query_prefix_clean_length_committed_query_target prefix
      prefix_state =
      (if hash_map_output_collision prefix_state then {}
       else staged_query_prefix_length_committed_query_target prefix
        prefix_state)"

definition checked_staged_query_prefix_hash_map_output_collision
  :: "((('f staged_query_prefix_data \<times> 'f protocol_channel) \<times> 'f) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_query_prefix_hash_map_output_collision out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((_, prefix_state), _), _) \<Rightarrow>
          hash_map_output_collision prefix_state)"

definition staged_query_prefix_committed_roots_clean
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> bool"
  where
    "staged_query_prefix_committed_roots_clean prefix prefix_state \<longleftrightarrow>
      \<not> merkle_root_binding_collision (sqp_trace_root prefix)
        prefix_state \<and>
      (\<forall>rt. sqp_composition_fri_roots prefix \<noteq> [] \<longrightarrow>
        rt = hd (sqp_composition_fri_roots prefix) \<longrightarrow>
        \<not> merkle_root_binding_collision rt prefix_state)"

definition staged_query_prefix_clean_committed_query_target
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
  where
    "staged_query_prefix_clean_committed_query_target prefix prefix_state =
      (if staged_query_prefix_committed_roots_clean prefix prefix_state
       then staged_query_prefix_committed_query_target prefix prefix_state
       else {})"

definition checked_staged_query_prefix_committed_root_collision
  :: "((('f staged_query_prefix_data \<times> 'f protocol_channel) \<times> 'f) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_query_prefix_committed_root_collision out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((prefix, prefix_state), _), _) \<Rightarrow>
          \<not> staged_query_prefix_committed_roots_clean prefix prefix_state)"

definition staged_security_with_data_state_query_committed_prefix_hit
  :: "'f staged_adversary \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_query_committed_prefix_hit A out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), _), _) \<Rightarrow>
          (\<exists>i prefix prefix_state raw raw_state.
            i < rounds \<and>
            Some (data, attacker_state) \<in>
              set_dist
                (execute (checked_staged_transcript_program A)
                  adversary_initial_state) \<and>
            Some (((prefix, prefix_state), raw), raw_state) \<in>
              set_dist
                (execute (checked_staged_query_prefix_receive_with_state A i)
                  adversary_initial_state) \<and>
            checked_staged_query_prefix_dynamic_index_hit
              (\<lambda>prefix prefix_state.
                staged_query_prefix_committed_query_target prefix prefix_state)
              (Some (((prefix, prefix_state), raw), raw_state))))"

definition staged_security_with_data_state_query_length_committed_prefix_hit
  :: "'f staged_adversary \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_query_length_committed_prefix_hit A out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), _), _) \<Rightarrow>
          (\<exists>i prefix prefix_state raw raw_state.
            i < rounds \<and>
            Some (data, attacker_state) \<in>
              set_dist
                (execute (checked_staged_transcript_program A)
                  adversary_initial_state) \<and>
            Some (((prefix, prefix_state), raw), raw_state) \<in>
              set_dist
                (execute (checked_staged_query_prefix_receive_with_state A i)
                  adversary_initial_state) \<and>
            checked_staged_query_prefix_dynamic_index_hit
              staged_query_prefix_length_committed_query_target
              (Some (((prefix, prefix_state), raw), raw_state))))"

definition staged_security_with_data_state_query_tree_output_hit
  :: "'f staged_adversary \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_query_tree_output_hit A out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), result), final_state) \<Rightarrow>
          (let s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in
            (\<exists>i prefix prefix_state raw raw_state trace_table
                composition_table as query_idxs trace_tree composition_tree.
              i < rounds \<and>
              Some (data, attacker_state) \<in>
                set_dist
                  (execute (checked_staged_transcript_program A)
                    adversary_initial_state) \<and>
              Some (result, final_state) \<in>
                set_dist (execute verify_monad s) \<and>
              accepted_with_bound_tables s (Some (result, final_state))
                trace_table composition_table as query_idxs \<and>
              fmlookup (HashMap final_state)
                (QueryIndexChallenge i
                  (state_after_query_chunks
                    (staged_query_start_hash data)
                    (staged_query_chunks data) i)) =
                Some raw \<and>
              index (to_nat raw) \<in>
                query_sampling_success_space trace_table composition_table
                  (staged_alphas data) \<and>
              Some (((prefix, prefix_state), raw), raw_state) \<in>
                set_dist
                  (execute (checked_staged_query_prefix_receive_with_state A i)
                    adversary_initial_state) \<and>
              sqp_composition_fri_roots prefix \<noteq> [] \<and>
              created_tree trace_table trace_tree final_state \<and>
              sqp_trace_root prefix = value trace_tree \<and>
              created_tree composition_table composition_tree final_state \<and>
              hd (sqp_composition_fri_roots prefix) = value composition_tree \<and>
              hash_map_new_output_hit
                (set_tree trace_tree \<union> set_tree composition_tree)
                prefix_state final_state)))"

lemma staged_partial_query_target_subset_prefix_completion:
  assumes match: "staged_query_prefix_matches_data i prefix data"
    and ext: "prefix_state \<le> attacker_state"
  shows
    "staged_partial_query_target data attacker_state \<subseteq>
      staged_query_prefix_partial_query_target i prefix prefix_state"
  unfolding staged_query_prefix_partial_query_target_def
  using match ext by blast

lemma staged_query_prefix_partial_query_target_subset:
  "staged_query_prefix_partial_query_target i prefix prefix_state \<subseteq>
    query_sample_space"
  unfolding staged_query_prefix_partial_query_target_def
    staged_partial_query_target_def
  using query_header_supported_partial_union_good_sets_subset by blast

lemma staged_query_prefix_committed_query_target_subset:
  "staged_query_prefix_committed_query_target prefix prefix_state \<subseteq>
    query_sample_space"
  unfolding staged_query_prefix_committed_query_target_def
  by (rule query_header_committed_union_good_sets_subset)

lemma staged_query_prefix_committed_query_targetI:
  assumes candidate:
    "(trace_table, composition_table) \<in>
      query_header_committed_table_candidates prefix_state
        (sqp_trace_root prefix) (sqp_composition_fri_roots prefix)"
    and hit:
      "idx \<in> query_sampling_success_space trace_table composition_table
        (sqp_alphas prefix)"
  shows "idx \<in> staged_query_prefix_committed_query_target prefix prefix_state"
proof -
  have idx_space: "idx \<in> query_sample_space"
    using query_sampling_success_space_subset hit by blast
  show ?thesis
    unfolding staged_query_prefix_committed_query_target_def
      query_header_committed_union_good_sets_def
    using candidate hit idx_space by blast
qed

lemma staged_query_prefix_committed_query_target_fraction_bound_if_unique_candidate:
  assumes unique:
    "\<exists>trace_table composition_table.
      query_header_committed_table_candidates prefix_state
        (sqp_trace_root prefix)
        (sqp_composition_fri_roots prefix) \<subseteq>
        {(trace_table, composition_table)}"
  shows
    "nnreal
      (card
        (staged_query_prefix_committed_query_target prefix prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
  unfolding staged_query_prefix_committed_query_target_def
  by (rule
      query_header_committed_union_good_sets_fraction_bound_if_unique_candidate
      [OF unique query_sampling_success_space_subset
        query_sampling_success_space_fraction_bound_query_sample_space])

lemma staged_query_prefix_committed_query_target_fraction_bound_if_no_root_collisions:
  assumes trace_clean:
      "\<not> merkle_root_binding_collision (sqp_trace_root prefix)
        prefix_state"
    and comp_clean:
      "\<And>rt. sqp_composition_fri_roots prefix \<noteq> [] \<Longrightarrow>
        rt = hd (sqp_composition_fri_roots prefix) \<Longrightarrow>
        \<not> merkle_root_binding_collision rt prefix_state"
  shows
    "nnreal
      (card
        (staged_query_prefix_committed_query_target prefix prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof -
  have unique:
    "\<exists>trace_table composition_table.
      query_header_committed_table_candidates prefix_state
        (sqp_trace_root prefix)
        (sqp_composition_fri_roots prefix) \<subseteq>
        {(trace_table, composition_table)}"
    by (rule
        query_header_committed_table_candidates_subset_singleton_if_no_root_collisions
        [OF trace_clean comp_clean])
  show ?thesis
    by (rule
        staged_query_prefix_committed_query_target_fraction_bound_if_unique_candidate
        [OF unique])
qed

lemma staged_query_prefix_length_committed_query_target_subset:
  "staged_query_prefix_length_committed_query_target prefix prefix_state
    \<subseteq> query_sample_space"
  unfolding staged_query_prefix_length_committed_query_target_def by auto

lemma staged_query_prefix_length_committed_query_targetI:
  assumes candidate:
    "(trace_table, composition_table) \<in>
      staged_query_prefix_length_committed_table_candidates prefix prefix_state"
    and hit:
      "idx \<in> query_sampling_success_space trace_table composition_table
        (sqp_alphas prefix)"
  shows
    "idx \<in> staged_query_prefix_length_committed_query_target prefix
      prefix_state"
proof -
  have idx_space: "idx \<in> query_sample_space"
    using query_sampling_success_space_subset hit by blast
  show ?thesis
    unfolding staged_query_prefix_length_committed_query_target_def
    using candidate hit idx_space by blast
qed

lemma staged_query_prefix_clean_length_committed_query_target_subset:
  "staged_query_prefix_clean_length_committed_query_target prefix prefix_state
    \<subseteq> query_sample_space"
  unfolding staged_query_prefix_clean_length_committed_query_target_def
  using staged_query_prefix_length_committed_query_target_subset
  by simp

lemma staged_query_prefix_length_committed_query_target_subset_committed:
  "staged_query_prefix_length_committed_query_target prefix prefix_state
    \<subseteq> staged_query_prefix_committed_query_target prefix prefix_state"
  unfolding staged_query_prefix_length_committed_query_target_def
    staged_query_prefix_length_committed_table_candidates_def
    staged_query_prefix_committed_query_target_def
    query_header_committed_union_good_sets_def
    query_header_committed_table_candidates_def
  by auto

lemma staged_query_prefix_length_committed_table_candidates_subset_singleton_if_no_hash_collision:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
  shows
    "\<exists>trace_table composition_table.
      staged_query_prefix_length_committed_table_candidates prefix
        prefix_state \<subseteq> {(trace_table, composition_table)}"
proof (cases
    "staged_query_prefix_length_committed_table_candidates prefix
      prefix_state = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"] exI[of _ "[]"]) simp
next
  case False
  then obtain pair where pair:
    "pair \<in>
      staged_query_prefix_length_committed_table_candidates prefix
        prefix_state"
    by auto
  obtain trace_table composition_table where pair_eq:
    "pair = (trace_table, composition_table)"
    by (cases pair)
  then have candidate:
    "(trace_table, composition_table) \<in>
      staged_query_prefix_length_committed_table_candidates prefix
        prefix_state"
    using pair by simp
  have trace_bind:
    "merkle_root_binds_table (sqp_trace_root prefix) trace_table
      prefix_state"
    using candidate
    unfolding staged_query_prefix_length_committed_table_candidates_def
    by simp
  have comp_nonempty: "sqp_composition_fri_roots prefix \<noteq> []"
    using candidate
    unfolding staged_query_prefix_length_committed_table_candidates_def
    by simp
  have comp_bind:
    "merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
      composition_table prefix_state"
    using candidate
    unfolding staged_query_prefix_length_committed_table_candidates_def
    by simp
  have trace_len: "length trace_table = clength * scale"
    using candidate
    unfolding staged_query_prefix_length_committed_table_candidates_def
    by simp
  have comp_len: "length composition_table = clength * scale"
    using candidate
    unfolding staged_query_prefix_length_committed_table_candidates_def
    by simp
  have trace_nonempty: "trace_table \<noteq> []"
    using trace_len eval_domain_size_pos by auto
  have comp_nonempty_table: "composition_table \<noteq> []"
    using comp_len eval_domain_size_pos by auto
  have subset:
    "staged_query_prefix_length_committed_table_candidates prefix
      prefix_state \<subseteq> {(trace_table, composition_table)}"
  proof
    fix pair
    assume pair_in:
      "pair \<in>
        staged_query_prefix_length_committed_table_candidates prefix
          prefix_state"
    obtain trace_table' composition_table' where pair_eq:
      "pair = (trace_table', composition_table')"
      by (cases pair)
    have trace_bind':
      "merkle_root_binds_table (sqp_trace_root prefix) trace_table'
        prefix_state"
      using pair_in unfolding pair_eq
        staged_query_prefix_length_committed_table_candidates_def
      by simp
    have comp_bind':
      "merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
        composition_table' prefix_state"
      using pair_in unfolding pair_eq
        staged_query_prefix_length_committed_table_candidates_def
      by simp
    have trace_len':
      "length trace_table' = clength * scale"
      using pair_in unfolding pair_eq
        staged_query_prefix_length_committed_table_candidates_def
      by simp
    have comp_len':
      "length composition_table' = clength * scale"
      using pair_in unfolding pair_eq
        staged_query_prefix_length_committed_table_candidates_def
      by simp
    have trace_eq: "trace_table' = trace_table"
      by (rule merkle_root_binds_same_length_tables_unique_if_no_hash_collision
          [OF trace_bind' trace_bind _ clean])
        (simp add: trace_len' trace_len)
    have comp_eq: "composition_table' = composition_table"
      by (rule merkle_root_binds_same_length_tables_unique_if_no_hash_collision
          [OF comp_bind' comp_bind _ clean])
        (simp add: comp_len' comp_len)
    show "pair \<in> {(trace_table, composition_table)}"
      unfolding pair_eq trace_eq comp_eq by simp
  qed
  show ?thesis
    using subset by blast
qed

lemma staged_query_prefix_length_committed_query_target_fraction_bound_if_no_hash_collision:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
  shows
    "nnreal
      (card
        (staged_query_prefix_length_committed_query_target prefix
          prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof -
  from
    staged_query_prefix_length_committed_table_candidates_subset_singleton_if_no_hash_collision
      [OF clean, of prefix]
  obtain trace_table composition_table where candidates:
    "staged_query_prefix_length_committed_table_candidates prefix
      prefix_state \<subseteq> {(trace_table, composition_table)}"
    by blast
  have union_subset:
    "staged_query_prefix_length_committed_query_target prefix prefix_state
      \<subseteq>
     query_sampling_success_space trace_table composition_table
      (sqp_alphas prefix)"
    unfolding staged_query_prefix_length_committed_query_target_def
    using candidates by auto
  have finite_good:
    "finite
      (query_sampling_success_space trace_table composition_table
        (sqp_alphas prefix))"
    by (rule finite_subset[OF query_sampling_success_space_subset
          finite_query_sample_space])
  have card_le:
    "card
      (staged_query_prefix_length_committed_query_target prefix
        prefix_state) \<le>
     card
      (query_sampling_success_space trace_table composition_table
        (sqp_alphas prefix))"
    by (rule card_mono[OF finite_good union_subset])
  have "nnreal
        (card
          (staged_query_prefix_length_committed_query_target prefix
            prefix_state)) /
      nnreal (card query_sample_space) \<le>
      nnreal
        (card
          (query_sampling_success_space trace_table composition_table
            (sqp_alphas prefix))) /
      nnreal (card query_sample_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> query_error_bound"
    by (rule query_sampling_success_space_fraction_bound_query_sample_space)
  finally show ?thesis .
qed

lemma staged_query_prefix_clean_length_committed_query_target_fraction_bound:
  shows
  "nnreal
    (card
      (staged_query_prefix_clean_length_committed_query_target prefix
        prefix_state)) /
    nnreal (card query_sample_space) \<le> query_error_bound"
proof (cases "hash_map_output_collision prefix_state")
  case True
  then show ?thesis
    unfolding staged_query_prefix_clean_length_committed_query_target_def
    by simp
next
  case False
  have bound:
    "nnreal
      (card
        (staged_query_prefix_length_committed_query_target prefix
          prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
    by (rule
        staged_query_prefix_length_committed_query_target_fraction_bound_if_no_hash_collision
        [OF False])
  then show ?thesis
    using False
    unfolding staged_query_prefix_clean_length_committed_query_target_def
    by simp
qed

lemma checked_staged_query_prefix_length_committed_hit_imp_clean_hit_or_hash_collision:
  assumes hit:
    "checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_length_committed_query_target out"
  shows
    "checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_clean_length_committed_query_target out \<or>
     checked_staged_query_prefix_hash_map_output_collision out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding checked_staged_query_prefix_dynamic_index_hit_def by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state where out_eq:
    "out = Some (((prefix, prefix_state), raw), raw_state)"
    by (cases packed, auto split: prod.splits)
  show ?thesis
  proof (cases "hash_map_output_collision prefix_state")
    case True
    then have "checked_staged_query_prefix_hash_map_output_collision out"
      unfolding out_eq checked_staged_query_prefix_hash_map_output_collision_def
      by simp
    then show ?thesis by simp
  next
    case False
    have
      "checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_length_committed_query_target out"
      using hit False
      unfolding out_eq checked_staged_query_prefix_dynamic_index_hit_def
        staged_query_prefix_clean_length_committed_query_target_def
      by simp
    then show ?thesis by simp
  qed
qed

lemma staged_query_prefix_clean_committed_query_target_subset:
  "staged_query_prefix_clean_committed_query_target prefix prefix_state
    \<subseteq> query_sample_space"
  unfolding staged_query_prefix_clean_committed_query_target_def
  using staged_query_prefix_committed_query_target_subset[of prefix prefix_state]
  by simp

lemma staged_query_prefix_clean_committed_query_target_subset_committed:
  "staged_query_prefix_clean_committed_query_target prefix prefix_state
    \<subseteq> staged_query_prefix_committed_query_target prefix prefix_state"
  unfolding staged_query_prefix_clean_committed_query_target_def by auto

lemma staged_query_prefix_clean_committed_query_target_fraction_bound:
  shows "nnreal
    (card
      (staged_query_prefix_clean_committed_query_target prefix prefix_state)) /
    nnreal (card query_sample_space) \<le> query_error_bound"
proof (cases
    "staged_query_prefix_committed_roots_clean prefix prefix_state")
  case True
  then have trace_clean:
      "\<not> merkle_root_binding_collision (sqp_trace_root prefix)
        prefix_state"
    and comp_clean:
      "\<And>rt. sqp_composition_fri_roots prefix \<noteq> [] \<Longrightarrow>
        rt = hd (sqp_composition_fri_roots prefix) \<Longrightarrow>
        \<not> merkle_root_binding_collision rt prefix_state"
    unfolding staged_query_prefix_committed_roots_clean_def by blast+
  show ?thesis
    unfolding staged_query_prefix_clean_committed_query_target_def
    using True
      staged_query_prefix_committed_query_target_fraction_bound_if_no_root_collisions
        [OF trace_clean comp_clean]
    by simp
next
  case False
  then show ?thesis
    unfolding staged_query_prefix_clean_committed_query_target_def by simp
qed

lemma checked_staged_query_prefix_committed_hit_imp_clean_hit_or_root_collision:
  assumes hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (\<lambda>prefix prefix_state.
        staged_query_prefix_committed_query_target prefix prefix_state) out"
  shows
    "checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_clean_committed_query_target out \<or>
     checked_staged_query_prefix_committed_root_collision out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding checked_staged_query_prefix_dynamic_index_hit_def by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state where out_eq:
    "out = Some (((prefix, prefix_state), raw), raw_state)"
    by (cases packed, auto split: prod.splits)
  show ?thesis
  proof (cases
      "staged_query_prefix_committed_roots_clean prefix prefix_state")
    case True
    have clean_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_committed_query_target out"
      using hit True
      unfolding out_eq checked_staged_query_prefix_dynamic_index_hit_def
        staged_query_prefix_clean_committed_query_target_def
      by simp
    then show ?thesis by simp
  next
    case False
    then have
      "checked_staged_query_prefix_committed_root_collision out"
      unfolding out_eq checked_staged_query_prefix_committed_root_collision_def
      by simp
    then show ?thesis by simp
  qed
qed

lemma staged_partial_query_target_subset:
  "staged_partial_query_target data attacker_state \<subseteq>
    query_sample_space"
  unfolding staged_partial_query_target_def
  by (rule query_header_supported_partial_union_good_sets_subset)

lemma staged_partial_query_target_fraction_bound_if_unique_candidate:
  assumes unique:
    "\<exists>trace_table composition_table.
      query_header_supported_partial_table_candidates
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data) \<subseteq>
        {(trace_table, composition_table)}"
  shows
    "nnreal (card (staged_partial_query_target data attacker_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
  unfolding staged_partial_query_target_def
  by (rule
      query_header_supported_partial_union_good_sets_fraction_bound_if_unique_candidate
      [OF unique query_sampling_success_space_subset
        query_sampling_success_space_fraction_bound_query_sample_space])

definition checked_staged_query_prefix_fixed_transcript_target_hit
  :: "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow>
      ((('f staged_query_prefix_data \<times> 'f protocol_channel) \<times> 'f) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_query_prefix_fixed_transcript_target_hit data
      attacker_state out \<longleftrightarrow>
      checked_staged_query_prefix_dynamic_index_hit
        (\<lambda>_ _. staged_partial_query_target data attacker_state) out"

lemma checked_staged_query_prefix_dynamic_index_hit_bound:
  fixes C :: prob
  assumes raw_bound: "query_index_raw_preimage_bound"
    and prefix_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<Longrightarrow>
        query_future_fresh prefix_state \<and>
        B prefix prefix_state \<subseteq> query_sample_space \<and>
        nnreal (card (B prefix prefix_state)) /
          nnreal (card query_sample_space) \<le> C"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit B) s \<le> C"
  unfolding checked_staged_query_prefix_receive_with_state_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> checked_staged_query_prefix_dynamic_index_hit B None"
    unfolding checked_staged_query_prefix_dynamic_index_hit_def by simp
next
  fix prefix_pack prefix_state
  assume prefix_support:
    "Some (prefix_pack, prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i) s)"
  obtain prefix captured_state where prefix_pack_eq:
    "prefix_pack = (prefix, captured_state)"
    by (cases prefix_pack) simp
  have captured_eq: "captured_state = prefix_state"
    using checked_staged_query_prefix_with_state_outcome_state
      [OF prefix_support[unfolded prefix_pack_eq]]
    by simp
  have support':
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i) s)"
    using checked_staged_query_prefix_with_state_outcome_canonical
      [OF prefix_support[unfolded prefix_pack_eq]]
      captured_eq
    by simp
  from prefix_bound[OF support'] have future:
      "query_future_fresh prefix_state"
    and subset:
      "B prefix prefix_state \<subseteq> query_sample_space"
    and frac:
      "nnreal (card (B prefix prefix_state)) /
        nnreal (card query_sample_space) \<le> C"
    by blast+
  have receive_bound:
    "wp_event
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))
      (checked_staged_query_prefix_dynamic_index_hit B) prefix_state \<le>
      C"
  proof -
    let ?P =
      "\<lambda>out. case out of None \<Rightarrow> False
        | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B prefix prefix_state"
    have cont_eq:
      "wp_event
        (receive_query_index_challenge \<bind> (\<lambda>raw.
          return (prefix_pack, raw)))
        (checked_staged_query_prefix_dynamic_index_hit B) prefix_state =
        wp_event receive_query_index_challenge ?P prefix_state"
      unfolding wp_event_def
      apply (subst wp_bind)
      apply (rule arg_cong[where
        f="\<lambda>Q. wp receive_query_index_challenge Q prefix_state"])
      apply (rule ext)
      apply (simp add: wp_return prefix_pack_eq captured_eq
          checked_staged_query_prefix_dynamic_index_hit_def
          split: option.splits prod.splits)
      done
    show ?thesis
      unfolding cont_eq
      by (rule order_trans
          [OF wp_receive_query_index_challenge_fresh_index_set_raw_bound
            [OF future raw_bound subset] frac])
  qed
  show "wp_event
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))
      (checked_staged_query_prefix_dynamic_index_hit B) prefix_state \<le>
      C"
    by (rule receive_bound)
qed

lemma checked_staged_query_prefix_fixed_transcript_target_hit_bound:
  fixes C :: prob
  assumes raw_bound: "query_index_raw_preimage_bound"
    and prefix_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<Longrightarrow>
        query_future_fresh prefix_state"
    and subset: "staged_partial_query_target data attacker_state \<subseteq>
        query_sample_space"
    and frac:
      "nnreal (card (staged_partial_query_target data attacker_state)) /
        nnreal (card query_sample_space) \<le> C"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_fixed_transcript_target_hit data
        attacker_state) s \<le> C"
  unfolding checked_staged_query_prefix_fixed_transcript_target_hit_def
  by (rule checked_staged_query_prefix_dynamic_index_hit_bound
      [OF raw_bound])
    (use prefix_bound subset frac in auto)

lemma checked_staged_query_prefix_committed_target_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and prefix_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<Longrightarrow>
        query_future_fresh prefix_state \<and>
        \<not> merkle_root_binding_collision (sqp_trace_root prefix)
          prefix_state \<and>
        (\<forall>rt. sqp_composition_fri_roots prefix \<noteq> [] \<longrightarrow>
          rt = hd (sqp_composition_fri_roots prefix) \<longrightarrow>
          \<not> merkle_root_binding_collision rt prefix_state)"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (\<lambda>prefix prefix_state.
          staged_query_prefix_committed_query_target prefix prefix_state))
      s \<le> query_error_bound"
proof (rule checked_staged_query_prefix_dynamic_index_hit_bound
    [OF raw_bound])
  fix prefix prefix_state
  assume support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i) s)"
  from prefix_bound[OF support]
  have future: "query_future_fresh prefix_state"
    and trace_clean:
      "\<not> merkle_root_binding_collision (sqp_trace_root prefix)
        prefix_state"
    and comp_clean:
      "\<And>rt. sqp_composition_fri_roots prefix \<noteq> [] \<Longrightarrow>
        rt = hd (sqp_composition_fri_roots prefix) \<Longrightarrow>
        \<not> merkle_root_binding_collision rt prefix_state"
    by blast+
  show
    "query_future_fresh prefix_state \<and>
     staged_query_prefix_committed_query_target prefix prefix_state
       \<subseteq> query_sample_space \<and>
     nnreal
       (card
         (staged_query_prefix_committed_query_target prefix prefix_state)) /
       nnreal (card query_sample_space) \<le> query_error_bound"
    using future
      staged_query_prefix_committed_query_target_subset[of prefix prefix_state]
      staged_query_prefix_committed_query_target_fraction_bound_if_no_root_collisions
        [OF trace_clean comp_clean]
    by blast
qed

definition checked_staged_query_prefix_dynamic_index_prehit
  :: "('f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow>
        nat set) \<Rightarrow>
      ((('f staged_query_prefix_data \<times> 'f protocol_channel) \<times> 'f) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_query_prefix_dynamic_index_prehit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((prefix, prefix_state), _), _) \<Rightarrow>
          (\<exists>raw \<in> query_index_raw_preimage (B prefix prefix_state).
            fmlookup (HashMap prefix_state)
              (QueryIndexChallenge (PQueryCounter prefix_state)
                (PState prefix_state)) = Some raw))"

definition checked_staged_query_prefix_dynamic_index_prehit_relation
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow> 'f protocol_channel \<Rightarrow>
      ('f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow>
        nat set) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "checked_staged_query_prefix_dynamic_index_prehit_relation A i s B x y
      \<longleftrightarrow>
      (\<exists>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<and>
        x = QueryIndexChallenge (PQueryCounter prefix_state)
              (PState prefix_state) \<and>
        y \<in> query_index_raw_preimage (B prefix prefix_state))"

lemma checked_staged_query_prefix_dynamic_index_prehit_imp_relation_hit:
  assumes empty: "HashMap s = fmempty"
    and prefix_support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i) s)"
    and receive_support:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i) s)"
    and prehit:
      "checked_staged_query_prefix_dynamic_index_prehit B
        (Some (((prefix, prefix_state), raw), raw_state))"
  shows
    "hash_relation_hit_event
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i s B)
      s (Some (((prefix, prefix_state), raw), raw_state))"
proof -
  from prehit obtain old_raw where old_raw_in:
      "old_raw \<in> query_index_raw_preimage (B prefix prefix_state)"
    and lookup_prefix:
      "fmlookup (HashMap prefix_state)
        (QueryIndexChallenge (PQueryCounter prefix_state)
          (PState prefix_state)) = Some old_raw"
    unfolding checked_staged_query_prefix_dynamic_index_prehit_def
    by auto
  have recv:
    "Some (raw, raw_state) \<in>
      set_dist (execute receive_query_index_challenge prefix_state)"
  proof -
    from receive_support obtain u where
      prefix_u:
        "Some ((prefix, prefix_state), u) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s)"
      and recv_u:
        "Some (raw, raw_state) \<in>
          set_dist (execute receive_query_index_challenge u)"
      unfolding checked_staged_query_prefix_receive_with_state_def
      by (auto elim!: set_dist_bindE)
    have "u = prefix_state"
      by (rule checked_staged_query_prefix_with_state_outcome_state
          [OF prefix_u])
    then show ?thesis
      using recv_u by simp
  qed
  have prefix_ext: "prefix_state \<le> raw_state"
    by (rule receive_query_index_challenge_extends[OF recv])
  have lookup_raw_state:
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge (PQueryCounter prefix_state)
        (PState prefix_state)) = Some old_raw"
    by (rule hash_extension_lookup[OF lookup_prefix prefix_ext])
  have lookup_initial:
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter prefix_state)
        (PState prefix_state)) = None"
    using empty by simp
  have rel:
    "checked_staged_query_prefix_dynamic_index_prehit_relation A i s B
      (QueryIndexChallenge (PQueryCounter prefix_state)
        (PState prefix_state)) old_raw"
    unfolding
      checked_staged_query_prefix_dynamic_index_prehit_relation_def
    using prefix_support old_raw_in by blast
  have hit:
    "hash_relation_hit
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i s B)
      s raw_state"
    unfolding hash_relation_hit_def
    by (intro exI[of _
          "QueryIndexChallenge (PQueryCounter prefix_state)
            (PState prefix_state)"]
        exI[of _ old_raw] conjI)
      (use lookup_initial lookup_raw_state rel in simp_all)
  show ?thesis
    unfolding hash_relation_hit_event_def using hit by simp
qed

lemma checked_staged_query_prefix_dynamic_index_prehit_bound_by_relation_hit:
  assumes empty: "HashMap s = fmempty"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit B) s \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (hash_relation_hit_event
        (checked_staged_query_prefix_dynamic_index_prehit_relation A i s B)
        s) s"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i) s)"
    and prehit: "checked_staged_query_prefix_dynamic_index_prehit B out"
  show
    "hash_relation_hit_event
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i s B)
      s out"
  proof (cases out)
    case None
    then show ?thesis
      using prehit
      unfolding checked_staged_query_prefix_dynamic_index_prehit_def
      by simp
  next
    case (Some packed)
    then obtain prefix prefix_state raw raw_state where out_eq:
      "out = Some (((prefix, prefix_state), raw), raw_state)"
      by (cases packed, auto split: prod.splits)
    have receive_support:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i) s)"
      using support unfolding out_eq .
    have prefix_support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i) s)"
    proof -
      from receive_support obtain u where
        prefix_u:
          "Some ((prefix, prefix_state), u) \<in>
            set_dist
              (execute (checked_staged_query_prefix_with_state A i) s)"
        unfolding checked_staged_query_prefix_receive_with_state_def
        by (auto elim!: set_dist_bindE)
      show ?thesis
        by (rule checked_staged_query_prefix_with_state_outcome_canonical
            [OF prefix_u])
    qed
    show ?thesis
      unfolding out_eq
      by (rule checked_staged_query_prefix_dynamic_index_prehit_imp_relation_hit
          [OF empty prefix_support receive_support])
        (use prehit out_eq in simp)
  qed
qed

lemma checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program:
  assumes empty: "HashMap s = fmempty"
    and relation_program:
      "hash_relation_program
        (checked_staged_query_prefix_dynamic_index_prehit_relation A i s B)
        fiber_bound query_bound
        (checked_staged_query_prefix_receive_with_state A i)"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit B) s \<le>
      staged_phase_relation_error fiber_bound query_bound"
proof -
  have prehit_le_relation:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit B) s \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (hash_relation_hit_event
        (checked_staged_query_prefix_dynamic_index_prehit_relation A i s B)
        s) s"
    by (rule
        checked_staged_query_prefix_dynamic_index_prehit_bound_by_relation_hit
        [OF empty])
  also have "... \<le> staged_phase_relation_error fiber_bound query_bound"
    using relation_program
    unfolding hash_relation_program_def hash_relation_budget_def
      staged_phase_relation_error_def
    by blast
  finally show ?thesis .
qed

lemma hash_map_preserving_get:
  "hash_map_preserving get"
  unfolding hash_map_preserving_def by simp

lemma hash_relation_program_get:
  "hash_relation_program R b 0 get"
  by (rule hash_relation_program_zero)
    (rule hash_map_preserving_get)

lemma hash_relation_program_modify_preserves_hash_map:
  assumes bump:
    "\<And>s. HashMap (bump s) = HashMap s"
  shows "hash_relation_program R b 0 (modify bump)"
  by (rule hash_relation_program_zero)
    (rule hash_map_preserving_modify[OF bump])

lemma hash_relation_program_receive_counted_tagged_random_field_element:
  assumes bump:
    "\<And>s. HashMap (bump s) = HashMap s"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b 1
      (protocol_receive_counted_tagged_random_field_element counter bump tag)"
proof -
  have modify_return:
    "hash_relation_program R b (0 + 0)
      (modify bump \<bind> (\<lambda>_. return r))"
    for r :: 'f
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_modify_preserves_hash_map[OF bump],
        rule hash_relation_program_zero[OF hash_map_preserving_return])
  have hash_tail:
    "hash_relation_program R b (1 + (0 + 0))
      (hash (tag (counter s) (PState s)) \<bind>
        (\<lambda>r. modify bump \<bind> (\<lambda>_. return r)))"
    for s
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_hash[OF fibers], rule modify_return)
  have "hash_relation_program R b (0 + (1 + (0 + 0)))
      (get \<bind>
        (\<lambda>s.
          hash (tag (counter s) (PState s)) \<bind>
            (\<lambda>r. modify bump \<bind> (\<lambda>_. return r))))"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_get, rule hash_tail)
  then show ?thesis
    unfolding protocol_receive_counted_tagged_random_field_element_def
    by simp
qed

lemma hash_relation_program_receive_query_index_challenge:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b 1
    receive_query_index_challenge"
  unfolding receive_query_index_challenge_def
  by (rule hash_relation_program_receive_counted_tagged_random_field_element
      [OF _ fibers])
    simp

lemma hash_map_preserving_get_bind_return_pair:
  "hash_map_preserving (get \<bind> (\<lambda>s. return (x, s)))"
  unfolding hash_map_preserving_def
  by (auto elim!: set_dist_bindE)

lemma hash_map_preserving_imp_hash_range_budget_zero:
  fixes m :: "('r, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes preserving: "hash_map_preserving m"
  shows "hash_range_budget 0 m"
  unfolding hash_range_budget_def
proof (intro allI impI)
  fix s y t
  assume "Some (y, t) \<in> set_dist (execute m s)"
  then have "HashMap t = HashMap s"
    using preserving unfolding hash_map_preserving_def by blast
  then show
    "card (hash_map_output_values t) \<le>
      card (hash_map_output_values s) + 0"
    by (simp add: hash_map_output_values_def)
qed

lemma hash_map_preserving_imp_hash_collision_budget_zero_scheme:
  fixes m :: "('r, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes preserving: "hash_map_preserving m"
  shows "hash_collision_budget 0 m"
  unfolding hash_collision_budget_def
proof (intro allI impI)
  fix s :: "('f, 'a) protocol_channel_scheme"
  assume clean: "\<not> hash_map_output_collision s"
  have no_event:
    "\<And>out. out \<in> set_dist (execute m s) \<Longrightarrow>
      \<not> hash_new_collision_event s out"
  proof -
    fix out
    assume support: "out \<in> set_dist (execute m s)"
    show "\<not> hash_new_collision_event s out"
    proof (cases out)
      case None
      then show ?thesis
        unfolding hash_new_collision_event_def by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) simp
      have same: "HashMap t = HashMap s"
        using preserving support Some xt
        unfolding hash_map_preserving_def by blast
      show ?thesis
        using clean same Some xt
        unfolding hash_new_collision_event_def
          hash_map_new_output_collision_def hash_map_output_collision_def
        by simp
    qed
  qed
  have no_event_dom:
    "\<And>out. out \<in> dom (dist (execute m s)) \<Longrightarrow>
      \<not> hash_new_collision_event s out"
    using no_event unfolding set_dist_def by blast
  have "wp_event m (hash_new_collision_event s) s = 0"
    unfolding wp_event_def wp_def dist_expect_def
    by (intro sum.neutral) (simp add: no_event_dom)
  then show
    "wp_event m (hash_new_collision_event s) s \<le>
      hash_collision_budget_value
        (card (hash_map_output_values s)) 0"
    unfolding hash_collision_budget_value_def by simp
qed

lemma checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound:
  assumes fibers:
    "\<And>x. card
      (\<Union>{query_index_raw_preimage (B prefix prefix_state) |
          prefix prefix_state.
            Some ((prefix, prefix_state), prefix_state) \<in>
              set_dist
                (execute (checked_staged_query_prefix_with_state A i) s) \<and>
            x = QueryIndexChallenge (PQueryCounter prefix_state)
                  (PState prefix_state)}) \<le> b"
  shows
    "card
      {y. checked_staged_query_prefix_dynamic_index_prehit_relation
        A i s B x y} \<le> b"
proof -
  let ?U =
    "\<Union>{query_index_raw_preimage (B prefix prefix_state) |
        prefix prefix_state.
          Some ((prefix, prefix_state), prefix_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_with_state A i) s) \<and>
          x = QueryIndexChallenge (PQueryCounter prefix_state)
                (PState prefix_state)}"
  have subset:
    "{y. checked_staged_query_prefix_dynamic_index_prehit_relation
        A i s B x y} \<subseteq> ?U"
    unfolding checked_staged_query_prefix_dynamic_index_prehit_relation_def
    by blast
  have finite_U: "finite ?U"
    by simp
  have "card
      {y. checked_staged_query_prefix_dynamic_index_prehit_relation
        A i s B x y} \<le> card ?U"
    by (rule card_mono[OF finite_U subset])
  also have "... \<le> b"
    by (rule fibers)
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size:
  "card
    {y. checked_staged_query_prefix_dynamic_index_prehit_relation
      A i s B x y} \<le> size"
proof -
  have subset:
    "{y. checked_staged_query_prefix_dynamic_index_prehit_relation
      A i s B x y} \<subseteq> (UNIV :: 'f set)"
    by simp
  have finite_field: "finite (UNIV :: 'f set)"
    by simp
  have "card
      {y. checked_staged_query_prefix_dynamic_index_prehit_relation
        A i s B x y} \<le> card (UNIV :: 'f set)"
    by (rule card_mono[OF finite_field subset])
  also have "... = size"
    using size_card by simp
  finally show ?thesis .
qed

lemma hash_relation_program_checked_staged_query_prefix_with_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (staged_query_search_queries budgets i)
      (checked_staged_query_prefix_with_state A i)"
  unfolding checked_staged_query_prefix_with_state_def
proof -
  have prefix:
    "hash_relation_program R b
      (staged_query_search_queries budgets i)
      (checked_staged_query_challenge_prefix_program A i)"
    by (rule hash_relation_program_checked_staged_query_challenge_prefix_program
        [OF wf controlled i_bound fibers])
  have tail:
    "\<And>prefix. hash_relation_program R b 0
      (get \<bind> (\<lambda>prefix_state. return (prefix, prefix_state)))"
    by (rule hash_relation_program_zero)
      (rule hash_map_preserving_get_bind_return_pair)
  have "hash_relation_program R b
      (staged_query_search_queries budgets i + 0)
      (checked_staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. get \<bind> (\<lambda>prefix_state.
          return (prefix, prefix_state))))"
    by (rule hash_relation_program_bind)
      (rule prefix, rule tail)
  then show "hash_relation_program R b
      (staged_query_search_queries budgets i)
      (checked_staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. get \<bind> (\<lambda>prefix_state.
          return (prefix, prefix_state))))"
    by simp
qed

lemma hash_relation_program_checked_staged_query_prefix_receive_with_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
  unfolding checked_staged_query_prefix_receive_with_state_def
proof -
  have prefix:
    "hash_relation_program R b
      (staged_query_search_queries budgets i)
      (checked_staged_query_prefix_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_with_state
        [OF wf controlled i_bound fibers])
  have receive:
    "\<And>prefix_pack. hash_relation_program R b 1
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
  proof -
    fix prefix_pack
    have "hash_relation_program R b (1 + 0)
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
      by (rule hash_relation_program_bind)
        (rule hash_relation_program_receive_query_index_challenge[OF fibers],
          rule hash_relation_program_zero[OF hash_map_preserving_return])
    then show "hash_relation_program R b 1
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
      by simp
  qed
  show "hash_relation_program R b
      (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_with_state A i \<bind>
        (\<lambda>prefix_pack. receive_query_index_challenge \<bind>
          (\<lambda>raw. return (prefix_pack, raw))))"
    by (rule hash_relation_program_bind)
      (rule prefix, rule receive)
qed

lemma hash_range_budget_checked_staged_query_prefix_with_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "hash_range_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_prefix_with_state A i)"
  unfolding checked_staged_query_prefix_with_state_def
proof -
  have prefix:
    "hash_range_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_challenge_prefix_program A i)"
    by (rule hash_range_budget_checked_staged_query_challenge_prefix_program
        [OF wf controlled i_bound])
  have tail:
    "\<And>prefix. hash_range_budget 0
      (get \<bind> (\<lambda>prefix_state. return (prefix, prefix_state)))"
    by (rule hash_map_preserving_imp_hash_range_budget_zero)
      (rule hash_map_preserving_get_bind_return_pair)
  have "hash_range_budget
      (staged_query_search_queries budgets i + 0)
      (checked_staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. get \<bind> (\<lambda>prefix_state.
          return (prefix, prefix_state))))"
    by (rule hash_range_budget_bind)
      (rule prefix, rule tail)
  then show "hash_range_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. get \<bind> (\<lambda>prefix_state.
          return (prefix, prefix_state))))"
    by simp
qed

lemma hash_collision_budget_checked_staged_query_prefix_with_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "hash_collision_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_prefix_with_state A i)"
  unfolding checked_staged_query_prefix_with_state_def
proof -
  have prefix_range:
    "hash_range_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_challenge_prefix_program A i)"
    by (rule hash_range_budget_checked_staged_query_challenge_prefix_program
        [OF wf controlled i_bound])
  have prefix_collision:
    "hash_collision_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_challenge_prefix_program A i)"
    by (rule hash_collision_budget_checked_staged_query_challenge_prefix_program
        [OF wf controlled i_bound])
  have tail_range:
    "\<And>prefix. hash_range_budget 0
      (get \<bind> (\<lambda>prefix_state. return (prefix, prefix_state)))"
    by (rule hash_map_preserving_imp_hash_range_budget_zero)
      (rule hash_map_preserving_get_bind_return_pair)
  have tail_collision:
    "\<And>prefix. hash_collision_budget 0
      (get \<bind> (\<lambda>prefix_state. return (prefix, prefix_state)))"
    by (rule hash_map_preserving_imp_hash_collision_budget_zero_scheme)
      (rule hash_map_preserving_get_bind_return_pair)
  have "hash_collision_budget
      (staged_query_search_queries budgets i + 0)
      (checked_staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. get \<bind> (\<lambda>prefix_state.
          return (prefix, prefix_state))))"
    by (rule hash_collision_budget_bind)
      (rule prefix_range, rule prefix_collision, rule tail_range,
        rule tail_collision)
  then show "hash_collision_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. get \<bind> (\<lambda>prefix_state.
          return (prefix, prefix_state))))"
    by simp
qed

lemma hash_range_budget_checked_staged_query_prefix_receive_with_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "hash_range_budget
      (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
  unfolding checked_staged_query_prefix_receive_with_state_def
proof -
  have prefix:
    "hash_range_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_prefix_with_state A i)"
    by (rule hash_range_budget_checked_staged_query_prefix_with_state
        [OF wf controlled i_bound])
  have receive:
    "\<And>prefix_pack. hash_range_budget 1
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
  proof -
    fix prefix_pack
    have "hash_range_budget (1 + 0)
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
      by (rule hash_range_budget_bind)
        (rule hash_range_budget_receive_query_index_challenge,
          rule hash_range_budget_return)
    then show "hash_range_budget 1
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
      by simp
  qed
  show "hash_range_budget
      (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_with_state A i \<bind>
        (\<lambda>prefix_pack. receive_query_index_challenge \<bind>
          (\<lambda>raw. return (prefix_pack, raw))))"
    by (rule hash_range_budget_bind)
      (rule prefix, rule receive)
qed

lemma hash_collision_budget_checked_staged_query_prefix_receive_with_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "hash_collision_budget
      (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
  unfolding checked_staged_query_prefix_receive_with_state_def
proof -
  have prefix_range:
    "hash_range_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_prefix_with_state A i)"
    by (rule hash_range_budget_checked_staged_query_prefix_with_state
        [OF wf controlled i_bound])
  have prefix_collision:
    "hash_collision_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_prefix_with_state A i)"
    by (rule hash_collision_budget_checked_staged_query_prefix_with_state
        [OF wf controlled i_bound])
  have receive_range:
    "\<And>prefix_pack. hash_range_budget 1
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
  proof -
    fix prefix_pack
    have "hash_range_budget (1 + 0)
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
      by (rule hash_range_budget_bind)
        (rule hash_range_budget_receive_query_index_challenge,
          rule hash_range_budget_return)
    then show "hash_range_budget 1
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
      by simp
  qed
  have receive_collision:
    "\<And>prefix_pack. hash_collision_budget 1
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
  proof -
    fix prefix_pack
    have "hash_collision_budget (1 + 0)
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
      by (rule hash_collision_budget_bind)
        (rule hash_range_budget_receive_query_index_challenge,
          rule hash_collision_budget_receive_query_index_challenge,
          rule hash_range_budget_return, rule hash_collision_budget_return)
    then show "hash_collision_budget 1
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))"
      by simp
  qed
  show "hash_collision_budget
      (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_with_state A i \<bind>
        (\<lambda>prefix_pack. receive_query_index_challenge \<bind>
          (\<lambda>raw. return (prefix_pack, raw))))"
    by (rule hash_collision_budget_bind)
      (rule prefix_range, rule prefix_collision, rule receive_range,
        rule receive_collision)
qed

lemma hash_map_output_collision_mono:
  assumes collision: "hash_map_output_collision s"
    and ext: "s \<le> t"
  shows "hash_map_output_collision t"
proof -
  obtain x y z where neq: "x \<noteq> y"
    and x_lookup: "fmlookup (HashMap s) x = Some z"
    and y_lookup: "fmlookup (HashMap s) y = Some z"
    using collision unfolding hash_map_output_collision_def by blast
  have x_lookup_t: "fmlookup (HashMap t) x = Some z"
    by (rule hash_extension_lookup[OF x_lookup ext])
  have y_lookup_t: "fmlookup (HashMap t) y = Some z"
    by (rule hash_extension_lookup[OF y_lookup ext])
  show ?thesis
    by (rule hash_map_output_collisionI[OF neq x_lookup_t y_lookup_t])
qed

lemma checked_staged_query_prefix_hash_map_output_collision_imp_new_collision_on_support:
  assumes support:
    "out \<in> set_dist
      (execute (checked_staged_query_prefix_receive_with_state A i)
        adversary_initial_state)"
    and collision:
      "checked_staged_query_prefix_hash_map_output_collision out"
  shows "hash_new_collision_event adversary_initial_state out"
proof (cases out)
  case None
  then show ?thesis
    using collision
    unfolding checked_staged_query_prefix_hash_map_output_collision_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state where out_eq:
    "out = Some (((prefix, prefix_state), raw), raw_state)"
    by (cases packed) auto
  have receive_support:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    using support unfolding out_eq .
  have recv:
      "Some (raw, raw_state) \<in>
        set_dist (execute receive_query_index_challenge prefix_state)"
    by (rule
        checked_staged_query_prefix_receive_with_state_receive_support
        [OF receive_support])
  have prefix_collision: "hash_map_output_collision prefix_state"
    using collision unfolding out_eq
      checked_staged_query_prefix_hash_map_output_collision_def by simp
  have raw_ext: "prefix_state \<le> raw_state"
    by (rule receive_query_index_challenge_extends[OF recv])
  have raw_collision: "hash_map_output_collision raw_state"
    by (rule hash_map_output_collision_mono[OF prefix_collision raw_ext])
  show ?thesis
    unfolding out_eq hash_new_collision_event_def
      hash_map_new_output_collision_def
    using raw_collision by simp
qed

lemma checked_staged_query_prefix_hash_map_output_collision_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      checked_staged_query_prefix_hash_map_output_collision
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
proof -
  let ?M = "checked_staged_query_prefix_receive_with_state A i"
  let ?q = "staged_query_search_queries budgets i + 1"
  have event_le:
    "wp_event ?M checked_staged_query_prefix_hash_map_output_collision
        adversary_initial_state \<le>
      wp_event ?M (hash_new_collision_event adversary_initial_state)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_query_prefix_hash_map_output_collision_imp_new_collision_on_support)
  have collision_budget:
    "hash_collision_budget ?q ?M"
    by (rule hash_collision_budget_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
  have new_collision_bound:
    "wp_event ?M (hash_new_collision_event adversary_initial_state)
        adversary_initial_state \<le>
      hash_collision_budget_value
        (card (hash_map_output_values adversary_initial_state)) ?q"
    using collision_budget adversary_initial_state_no_output_collision
    unfolding hash_collision_budget_def by blast
  have "wp_event ?M checked_staged_query_prefix_hash_map_output_collision
        adversary_initial_state \<le>
      hash_collision_budget_value
        (card (hash_map_output_values adversary_initial_state)) ?q"
    by (rule order_trans[OF event_le new_collision_bound])
  then show ?thesis
    by simp
qed

lemma checked_staged_query_prefix_partial_target_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_partial_query_target i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        (staged_query_prefix_partial_query_target i))
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_committed_target_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (\<lambda>prefix prefix_state.
          staged_query_prefix_committed_query_target prefix prefix_state))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        (\<lambda>prefix prefix_state.
          staged_query_prefix_committed_query_target prefix prefix_state))
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_clean_committed_target_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_clean_committed_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        staged_query_prefix_clean_committed_query_target)
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_clean_length_committed_target_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_clean_length_committed_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        staged_query_prefix_clean_length_committed_query_target)
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

definition checked_staged_query_prefix_dynamic_index_fresh_output_hit
  :: "('f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow>
        nat set) \<Rightarrow>
      ((('f staged_query_prefix_data \<times> 'f protocol_channel) \<times> 'f) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_query_prefix_dynamic_index_fresh_output_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((prefix, prefix_state), raw), raw_state) \<Rightarrow>
          hash_new_output_hit_event
            (query_index_raw_preimage (B prefix prefix_state))
            prefix_state (Some (raw, raw_state)))"

lemma checked_staged_query_prefix_dynamic_index_hit_imp_prehit_or_fresh:
  assumes absent:
      "\<not> checked_staged_query_prefix_dynamic_index_prehit B
        (Some (((prefix, prefix_state), raw), raw_state))"
    and prefix_support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i) s)"
    and receive_support:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i) s)"
    and hit:
      "checked_staged_query_prefix_dynamic_index_hit B
        (Some (((prefix, prefix_state), raw), raw_state))"
  shows
    "hash_new_output_hit_event
      (query_index_raw_preimage (B prefix prefix_state)) prefix_state
      (Some (raw, raw_state))"
proof -
  have raw_in:
    "raw \<in> query_index_raw_preimage (B prefix prefix_state)"
    using hit unfolding checked_staged_query_prefix_dynamic_index_hit_def
      query_index_raw_preimage_def
    by simp
  have no_lookup:
    "fmlookup (HashMap prefix_state)
      (QueryIndexChallenge (PQueryCounter prefix_state)
        (PState prefix_state)) = None"
  proof (cases
      "fmlookup (HashMap prefix_state)
        (QueryIndexChallenge (PQueryCounter prefix_state)
          (PState prefix_state))")
    case None
    then show ?thesis .
  next
    case (Some old_raw)
    have old_lookup_prefix:
      "fmlookup (HashMap prefix_state)
        (QueryIndexChallenge (PQueryCounter prefix_state)
          (PState prefix_state)) = Some old_raw"
      using Some by simp
    have old_in: "old_raw \<in> query_index_raw_preimage
        (B prefix prefix_state)"
    proof -
      have old_idx:
        "index (to_nat old_raw) \<in> B prefix prefix_state"
      proof -
        have raw_idx:
          "index (to_nat raw) \<in> B prefix prefix_state"
          using hit
          unfolding checked_staged_query_prefix_dynamic_index_hit_def
          by simp
        have recv:
          "Some (raw, raw_state) \<in>
            set_dist
              (execute receive_query_index_challenge prefix_state)"
          by (rule
              checked_staged_query_prefix_receive_with_state_receive_support
              [OF receive_support])
        have recv_lookup:
          "fmlookup (HashMap raw_state)
            (QueryIndexChallenge (PQueryCounter prefix_state)
              (PState prefix_state)) = Some raw"
          using receive_query_index_challenge_outcome[OF recv] by blast
        have ext: "prefix_state \<le> raw_state"
          using receive_query_index_challenge_extends[OF recv] .
        have old_lookup_raw_state:
          "fmlookup (HashMap raw_state)
            (QueryIndexChallenge (PQueryCounter prefix_state)
              (PState prefix_state)) = Some old_raw"
          by (rule hash_extension_lookup[OF old_lookup_prefix ext])
        have old_raw_eq: "old_raw = raw"
          using recv_lookup old_lookup_raw_state by simp
        show ?thesis
          using raw_idx unfolding old_raw_eq .
      qed
      show ?thesis
        using old_idx unfolding query_index_raw_preimage_def by simp
    qed
    have prehit:
      "checked_staged_query_prefix_dynamic_index_prehit B
        (Some (((prefix, prefix_state), raw), raw_state))"
      using old_lookup_prefix old_in
      by (auto simp: checked_staged_query_prefix_dynamic_index_prehit_def)
    then show ?thesis
      using absent by contradiction
  qed
  from receive_support have recv:
    "Some (raw, raw_state) \<in>
      set_dist (execute receive_query_index_challenge prefix_state)"
    by (rule
        checked_staged_query_prefix_receive_with_state_receive_support)
  have recv_lookup:
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge (PQueryCounter prefix_state)
        (PState prefix_state)) = Some raw"
    using receive_query_index_challenge_outcome[OF recv] by blast
  have new_hit:
    "hash_map_new_output_hit
      (query_index_raw_preimage (B prefix prefix_state))
      prefix_state raw_state"
    unfolding hash_map_new_output_hit_def
    using no_lookup recv_lookup raw_in by blast
  show ?thesis
    unfolding hash_new_output_hit_event_def using new_hit by simp
qed

lemma checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_fresh:
  "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit B) s \<le>
   wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit B) s +
   wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_fresh_output_hit B) s"
proof -
  let ?M = "checked_staged_query_prefix_receive_with_state A i"
  let ?hit = "checked_staged_query_prefix_dynamic_index_hit B"
  let ?pre = "checked_staged_query_prefix_dynamic_index_prehit B"
  let ?fresh = "checked_staged_query_prefix_dynamic_index_fresh_output_hit B"
  have "wp_event ?M ?hit s \<le> wp_event ?M (\<lambda>out. ?pre out \<or> ?fresh out) s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?M s)"
      and hit: "?hit out"
    show "?pre out \<or> ?fresh out"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding checked_staged_query_prefix_dynamic_index_hit_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state where out_eq:
        "out = Some (((prefix, prefix_state), raw), raw_state)"
        by (cases packed, auto split: prod.splits)
      show ?thesis
      proof (cases "?pre out")
        case True
        then show ?thesis by simp
      next
        case pre_absent: False
        have prefix_support:
          "Some ((prefix, prefix_state), prefix_state) \<in>
            set_dist
              (execute (checked_staged_query_prefix_with_state A i) s)"
          by (rule
              checked_staged_query_prefix_receive_with_state_prefix_support
              [OF support[unfolded out_eq]])
        have fresh:
          "hash_new_output_hit_event
            (query_index_raw_preimage (B prefix prefix_state))
            prefix_state (Some (raw, raw_state))"
          by (rule checked_staged_query_prefix_dynamic_index_hit_imp_prehit_or_fresh
              [OF _ prefix_support support[unfolded out_eq]
                hit[unfolded out_eq]])
            (use pre_absent out_eq in simp)
        then show ?thesis
          unfolding out_eq
            checked_staged_query_prefix_dynamic_index_fresh_output_hit_def
          by simp
      qed
    qed
  qed
  also have "... \<le> wp_event ?M ?pre s + wp_event ?M ?fresh s"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma wp_receive_query_index_challenge_new_output_hit_bound:
  fixes B :: "'f set"
    and s :: "('f, 'a) protocol_channel_scheme"
  shows
    "wp_event receive_query_index_challenge
      (hash_new_output_hit_event B s) s \<le> nnreal (card B) / nnreal size"
proof (cases
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s))")
  case None
  have event_le:
    "wp_event receive_query_index_challenge
      (hash_new_output_hit_event B s) s \<le>
     wp_event receive_query_index_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (raw, _) \<Rightarrow> raw \<in> B) s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute receive_query_index_challenge s)"
      and hit: "hash_new_output_hit_event B s out"
    show "(case out of None \<Rightarrow> False | Some (raw, _) \<Rightarrow> raw \<in> B)"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding hash_new_output_hit_event_def by simp
    next
      case (Some packed)
      then obtain raw t where packed_eq: "packed = (raw, t)"
        by (cases packed) simp
      have out':
        "Some (raw, t) \<in>
          set_dist (execute receive_query_index_challenge s)"
        using support unfolding Some packed_eq .
      have lookup:
        "fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
        using receive_query_index_challenge_outcome[OF out'] by blast
      have new_hit: "hash_map_new_output_hit B s t"
        using hit unfolding Some packed_eq hash_new_output_hit_event_def
        by simp
      then show ?thesis
      proof -
        from new_hit obtain x y where none_x:
            "fmlookup (HashMap s) x = None"
          and some_x: "fmlookup (HashMap t) x = Some y"
          and y_in: "y \<in> B"
          unfolding hash_map_new_output_hit_def by blast
        let ?q = "QueryIndexChallenge (PQueryCounter s) (PState s)"
        have "raw \<in> B"
        proof (cases "x = ?q")
          case True
          then have "Some y = Some raw"
            using some_x lookup by simp
          then show ?thesis
            using y_in by simp
        next
          case False
          have "fmlookup (HashMap t) x = fmlookup (HashMap s) x"
            by (rule receive_query_index_challenge_preserves_other_lookup
                [OF out' False])
          then show ?thesis
            using none_x some_x by simp
        qed
        then show ?thesis
          unfolding Some packed_eq by simp
      qed
    qed
  qed
  also have "... = nnreal (card B) / nnreal size"
    by (rule wp_receive_query_index_challenge_fresh_set[OF None])
  finally show ?thesis .
next
  case (Some old)
  have old_lookup:
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some old"
    using Some by simp
  have no_new_on_support:
    "\<And>out. out \<in> set_dist (execute receive_query_index_challenge s) \<Longrightarrow>
      \<not> hash_new_output_hit_event B s out"
  proof -
    fix out
    assume support: "out \<in> set_dist (execute receive_query_index_challenge s)"
    show "\<not> hash_new_output_hit_event B s out"
    proof (cases out)
      case None
      then show ?thesis
        unfolding hash_new_output_hit_event_def by simp
    next
      case (Some packed)
      then obtain raw t where packed_eq: "packed = (raw, t)"
        by (cases packed) simp
      have out':
        "Some (raw, t) \<in>
          set_dist (execute receive_query_index_challenge s)"
        using support unfolding Some packed_eq .
      have ext: "s \<le> t"
        by (rule receive_query_index_challenge_extends[OF out'])
      show ?thesis
      proof
        assume bad: "hash_new_output_hit_event B s out"
        have bad':
          "\<exists>x y. fmlookup (HashMap s) x = None \<and>
            fmlookup (HashMap t) x = Some y \<and> y \<in> B"
          using bad
          unfolding Some packed_eq hash_new_output_hit_event_def
            hash_map_new_output_hit_def
          by simp
        then obtain x y where none_x:
            "fmlookup (HashMap s) x = None"
          and some_x: "fmlookup (HashMap t) x = Some y"
          and y_in: "y \<in> B"
          by blast
        let ?q = "QueryIndexChallenge (PQueryCounter s) (PState s)"
        show False
        proof (cases "x = ?q")
          case True
          then show ?thesis
            using none_x old_lookup by simp
        next
          case False
          have "fmlookup (HashMap t) x = fmlookup (HashMap s) x"
            by (rule receive_query_index_challenge_preserves_other_lookup
                [OF out' False])
          then show ?thesis
            using none_x some_x by simp
        qed
      qed
    qed
  qed
  have "wp_event receive_query_index_challenge
      (hash_new_output_hit_event B s) s \<le>
    wp_event receive_query_index_challenge (\<lambda>_. False) s"
    by (rule wp_event_mono_on_support)
      (use no_new_on_support in blast)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  also have "0 \<le> nnreal (card B) / nnreal size"
    by simp
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_dynamic_index_fresh_output_hit_bound:
  fixes C :: prob
  assumes raw_bound: "query_index_raw_preimage_bound"
    and prefix_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<Longrightarrow>
        B prefix prefix_state \<subseteq> query_sample_space \<and>
        nnreal (card (B prefix prefix_state)) /
          nnreal (card query_sample_space) \<le> C"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_fresh_output_hit B) s \<le> C"
  unfolding checked_staged_query_prefix_receive_with_state_def
proof (rule wp_event_bind_bound_by_cont)
  show
    "\<not> checked_staged_query_prefix_dynamic_index_fresh_output_hit B None"
    unfolding checked_staged_query_prefix_dynamic_index_fresh_output_hit_def
    by simp
next
  fix prefix_pack prefix_state
  assume prefix_support:
    "Some (prefix_pack, prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i) s)"
  obtain prefix captured_state where prefix_pack_eq:
    "prefix_pack = (prefix, captured_state)"
    by (cases prefix_pack) simp
  have captured_eq: "captured_state = prefix_state"
    using checked_staged_query_prefix_with_state_outcome_state
      [OF prefix_support[unfolded prefix_pack_eq]]
    by simp
  have support':
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i) s)"
    using checked_staged_query_prefix_with_state_outcome_canonical
      [OF prefix_support[unfolded prefix_pack_eq]]
      captured_eq
    by simp
  from prefix_bound[OF support'] have subset:
      "B prefix prefix_state \<subseteq> query_sample_space"
    and frac:
      "nnreal (card (B prefix prefix_state)) /
        nnreal (card query_sample_space) \<le> C"
    by blast+
  have raw_frac:
    "nnreal (card (query_index_raw_preimage (B prefix prefix_state))) /
      nnreal size \<le> C"
  proof -
    have "nnreal (card (query_index_raw_preimage (B prefix prefix_state))) /
        nnreal size \<le>
      nnreal (card (B prefix prefix_state)) /
        nnreal (card query_sample_space)"
      using raw_bound subset unfolding query_index_raw_preimage_bound_def
      by blast
    also have "... \<le> C"
      by (rule frac)
    finally show ?thesis .
  qed
  have cont_eq:
    "wp_event
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))
      (checked_staged_query_prefix_dynamic_index_fresh_output_hit B)
      prefix_state =
     wp_event receive_query_index_challenge
      (hash_new_output_hit_event
        (query_index_raw_preimage (B prefix prefix_state)) prefix_state)
      prefix_state"
    unfolding wp_event_def
    apply (subst wp_bind)
    apply (rule arg_cong[where
      f="\<lambda>Q. wp receive_query_index_challenge Q prefix_state"])
	    apply (rule ext)
	    apply (simp add: wp_return prefix_pack_eq captured_eq
	        checked_staged_query_prefix_dynamic_index_fresh_output_hit_def
	        hash_new_output_hit_event_def
	        split: option.splits prod.splits)
    done
  show "wp_event
      (receive_query_index_challenge \<bind> (\<lambda>raw.
        return (prefix_pack, raw)))
      (checked_staged_query_prefix_dynamic_index_fresh_output_hit B)
      prefix_state \<le> C"
    unfolding cont_eq
    by (rule order_trans[
        OF wp_receive_query_index_challenge_new_output_hit_bound raw_frac])
qed

lemma checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error:
  fixes C :: prob
  assumes raw_bound: "query_index_raw_preimage_bound"
    and prefix_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<Longrightarrow>
        B prefix prefix_state \<subseteq> query_sample_space \<and>
        nnreal (card (B prefix prefix_state)) /
          nnreal (card query_sample_space) \<le> C"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit B) s \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit B) s + C"
proof -
  have "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit B) s \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit B) s +
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_fresh_output_hit B) s"
    by (rule checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_fresh)
  also have "... \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit B) s + C"
    by (intro add_mono order_refl
        checked_staged_query_prefix_dynamic_index_fresh_output_hit_bound
        [OF raw_bound prefix_bound])
  finally show ?thesis .
qed

lemma query_sample_space_fraction_le_one:
  assumes subset: "B \<subseteq> query_sample_space"
  shows "nnreal (card B) / nnreal (card query_sample_space) \<le> (1::prob)"
proof -
  have finite_B: "finite B"
    by (rule finite_subset[OF subset finite_query_sample_space])
  have card_le: "card B \<le> card query_sample_space"
    by (rule card_mono[OF finite_query_sample_space subset])
  have "nnreal (card B) / nnreal (card query_sample_space) \<le>
      nnreal (card query_sample_space) / nnreal (card query_sample_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... = (1::prob)"
    by (rule nnreal_nat_divide_self) (simp add: query_sample_space_size_pos)
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_partial_target_hit_bound_by_prehit_plus_one:
  assumes raw_bound: "query_index_raw_preimage_bound"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_partial_query_target i)) s \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_partial_query_target i)) s + 1"
proof (rule
    checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
    [OF raw_bound])
  fix prefix prefix_state
  assume support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist (execute (checked_staged_query_prefix_with_state A i) s)"
  have subset:
    "staged_query_prefix_partial_query_target i prefix prefix_state \<subseteq>
      query_sample_space"
    by (rule staged_query_prefix_partial_query_target_subset)
  have frac:
    "nnreal
      (card (staged_query_prefix_partial_query_target i prefix prefix_state)) /
      nnreal (card query_sample_space) \<le> (1::prob)"
    by (rule query_sample_space_fraction_le_one[OF subset])
  show "staged_query_prefix_partial_query_target i prefix prefix_state \<subseteq>
      query_sample_space \<and>
    nnreal
      (card (staged_query_prefix_partial_query_target i prefix prefix_state)) /
      nnreal (card query_sample_space) \<le> (1::prob)"
    using subset frac by blast
qed

lemma checked_staged_query_prefix_partial_target_hit_bound_by_relation_plus_one:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_partial_query_target i))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + 1"
proof -
  have "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_partial_query_target i))
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_partial_query_target i))
      adversary_initial_state + 1"
    by (rule checked_staged_query_prefix_partial_target_hit_bound_by_prehit_plus_one
        [OF raw_bound])
  also have "... \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + 1"
    by (intro add_mono order_refl
        checked_staged_query_prefix_partial_target_prehit_bound
        [OF wf controlled i_bound])
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_committed_target_hit_bound_by_relation_and_query_error:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
    and prefix_clean:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> merkle_root_binding_collision (sqp_trace_root prefix)
          prefix_state \<and>
        (\<forall>rt. sqp_composition_fri_roots prefix \<noteq> [] \<longrightarrow>
          rt = hd (sqp_composition_fri_roots prefix) \<longrightarrow>
          \<not> merkle_root_binding_collision rt prefix_state)"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (\<lambda>prefix prefix_state.
          staged_query_prefix_committed_query_target prefix prefix_state))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (\<lambda>prefix prefix_state.
          staged_query_prefix_committed_query_target prefix prefix_state))
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (\<lambda>prefix prefix_state.
          staged_query_prefix_committed_query_target prefix prefix_state))
      adversary_initial_state + query_error_bound"
  proof (rule checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    from prefix_clean[OF support]
    have trace_clean:
        "\<not> merkle_root_binding_collision (sqp_trace_root prefix)
          prefix_state"
      and comp_clean:
        "\<And>rt. sqp_composition_fri_roots prefix \<noteq> [] \<Longrightarrow>
          rt = hd (sqp_composition_fri_roots prefix) \<Longrightarrow>
          \<not> merkle_root_binding_collision rt prefix_state"
      by blast+
    show
      "(\<lambda>prefix prefix_state.
          staged_query_prefix_committed_query_target prefix prefix_state)
        prefix prefix_state \<subseteq> query_sample_space \<and>
       nnreal
        (card
          ((\<lambda>prefix prefix_state.
            staged_query_prefix_committed_query_target prefix prefix_state)
            prefix prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      using
        staged_query_prefix_committed_query_target_subset[of prefix prefix_state]
        staged_query_prefix_committed_query_target_fraction_bound_if_no_root_collisions
          [OF trace_clean comp_clean]
      by blast
  qed
  also have "... \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (intro add_mono order_refl
        checked_staged_query_prefix_committed_target_prehit_bound
        [OF wf controlled i_bound])
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_clean_committed_target_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_committed_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_committed_query_target)
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_clean_committed_query_target)
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    have subset:
      "staged_query_prefix_clean_committed_query_target prefix prefix_state
        \<subseteq> query_sample_space"
      by (rule staged_query_prefix_clean_committed_query_target_subset)
    have frac:
      "nnreal
        (card
          (staged_query_prefix_clean_committed_query_target prefix
            prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      by (rule staged_query_prefix_clean_committed_query_target_fraction_bound)
    show "staged_query_prefix_clean_committed_query_target prefix prefix_state
        \<subseteq> query_sample_space \<and>
      nnreal
        (card
          (staged_query_prefix_clean_committed_query_target prefix
            prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      using subset frac by blast
  qed
  also have "... \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (intro add_mono order_refl
        checked_staged_query_prefix_clean_committed_target_prehit_bound
        [OF wf controlled i_bound])
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_committed_target_hit_bound_by_clean_and_collision:
  "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_committed_query_target) s \<le>
   wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_committed_query_target) s +
   wp_event (checked_staged_query_prefix_receive_with_state A i)
      checked_staged_query_prefix_committed_root_collision s"
proof -
  let ?M = "checked_staged_query_prefix_receive_with_state A i"
  let ?hit =
    "checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_committed_query_target"
  let ?clean =
    "checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_clean_committed_query_target"
  let ?collision = checked_staged_query_prefix_committed_root_collision
  have "wp_event ?M ?hit s \<le> wp_event ?M (\<lambda>out. ?clean out \<or> ?collision out) s"
    by (rule wp_event_mono)
      (rule checked_staged_query_prefix_committed_hit_imp_clean_hit_or_root_collision)
  also have "... \<le> wp_event ?M ?clean s + wp_event ?M ?collision s"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_committed_target_hit_bound_by_relation_query_error_and_collision:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_committed_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      wp_event (checked_staged_query_prefix_receive_with_state A i)
        checked_staged_query_prefix_committed_root_collision
        adversary_initial_state"
proof -
  have split:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_committed_query_target)
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_committed_query_target)
      adversary_initial_state +
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      checked_staged_query_prefix_committed_root_collision
      adversary_initial_state"
    by (rule
        checked_staged_query_prefix_committed_target_hit_bound_by_clean_and_collision)
  have clean_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_committed_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule checked_staged_query_prefix_clean_committed_target_hit_bound
        [OF raw_bound wf controlled i_bound])
  have tail_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_committed_query_target)
      adversary_initial_state +
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      checked_staged_query_prefix_committed_root_collision
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      wp_event (checked_staged_query_prefix_receive_with_state A i)
        checked_staged_query_prefix_committed_root_collision
        adversary_initial_state"
    using clean_bound by (simp add: add_mono)
  show ?thesis
    by (rule order_trans[OF split tail_bound])
qed

lemma checked_staged_query_prefix_clean_length_committed_target_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_length_committed_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_length_committed_query_target)
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_clean_length_committed_query_target)
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    have subset:
      "staged_query_prefix_clean_length_committed_query_target prefix
        prefix_state \<subseteq> query_sample_space"
      by (rule staged_query_prefix_clean_length_committed_query_target_subset)
    have frac:
      "nnreal
        (card
          (staged_query_prefix_clean_length_committed_query_target prefix
            prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      by (rule staged_query_prefix_clean_length_committed_query_target_fraction_bound)
    show "staged_query_prefix_clean_length_committed_query_target prefix
        prefix_state \<subseteq> query_sample_space \<and>
      nnreal
        (card
          (staged_query_prefix_clean_length_committed_query_target prefix
            prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      using subset frac by blast
  qed
  also have "... \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (intro add_mono order_refl
        checked_staged_query_prefix_clean_length_committed_target_prehit_bound
        [OF wf controlled i_bound])
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_length_committed_target_hit_bound_by_clean_and_collision:
  "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_length_committed_query_target) s \<le>
   wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_length_committed_query_target) s +
   wp_event (checked_staged_query_prefix_receive_with_state A i)
      checked_staged_query_prefix_hash_map_output_collision s"
proof -
  let ?M = "checked_staged_query_prefix_receive_with_state A i"
  let ?hit =
    "checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_length_committed_query_target"
  let ?clean =
    "checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_clean_length_committed_query_target"
  let ?collision = checked_staged_query_prefix_hash_map_output_collision
  have "wp_event ?M ?hit s \<le> wp_event ?M (\<lambda>out. ?clean out \<or> ?collision out) s"
    by (rule wp_event_mono)
      (rule
        checked_staged_query_prefix_length_committed_hit_imp_clean_hit_or_hash_collision)
  also have "... \<le> wp_event ?M ?clean s + wp_event ?M ?collision s"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_length_committed_target_hit_bound_by_relation_query_error_and_collision:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_length_committed_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      wp_event (checked_staged_query_prefix_receive_with_state A i)
        checked_staged_query_prefix_hash_map_output_collision
        adversary_initial_state"
proof -
  have split:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_length_committed_query_target)
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_length_committed_query_target)
      adversary_initial_state +
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      checked_staged_query_prefix_hash_map_output_collision
      adversary_initial_state"
    by (rule
        checked_staged_query_prefix_length_committed_target_hit_bound_by_clean_and_collision)
  have clean_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_length_committed_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_query_prefix_clean_length_committed_target_hit_bound
        [OF raw_bound wf controlled i_bound])
  have tail_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_clean_length_committed_query_target)
      adversary_initial_state +
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      checked_staged_query_prefix_hash_map_output_collision
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      wp_event (checked_staged_query_prefix_receive_with_state A i)
        checked_staged_query_prefix_hash_map_output_collision
        adversary_initial_state"
    using clean_bound by (simp add: add_mono)
  show ?thesis
    by (rule order_trans[OF split tail_bound])
qed

lemma checked_staged_query_prefix_length_committed_target_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_length_committed_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
proof -
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_length_committed_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      wp_event (checked_staged_query_prefix_receive_with_state A i)
        checked_staged_query_prefix_hash_map_output_collision
        adversary_initial_state"
    by (rule
        checked_staged_query_prefix_length_committed_target_hit_bound_by_relation_query_error_and_collision
        [OF raw_bound wf controlled i_bound])
  have collision_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      checked_staged_query_prefix_hash_map_output_collision
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    by (rule checked_staged_query_prefix_hash_map_output_collision_bound
        [OF wf controlled i_bound])
  have tail:
    "staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      wp_event (checked_staged_query_prefix_receive_with_state A i)
        checked_staged_query_prefix_hash_map_output_collision
        adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    using collision_bound by (intro add_mono order_refl)
  show ?thesis
    by (rule order_trans[OF hit_bound tail])
qed

end

end
