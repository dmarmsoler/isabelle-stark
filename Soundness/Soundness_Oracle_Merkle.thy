(*  Title:      Stark/Soundness_Oracle_Merkle.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Oracle_Merkle
  imports Soundness_Oracle_Verifier
begin

text \<open>Merkle-binding collision covers and concrete binding interfaces.\<close>

context soundness
begin

definition hash_map_new_output_collision_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "hash_map_new_output_collision_bad s out \<longleftrightarrow>
      accepted out \<and>
      (\<exists>result final_state.
        out = Some (result, final_state) \<and>
        hash_map_new_output_collision s final_state)"

definition hash_map_new_output_collision_bound
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "hash_map_new_output_collision_bound s \<longleftrightarrow>
      wp_event verify_monad (hash_map_new_output_collision_bad s) s \<le>
        merkle_binding_error"

lemma hash_map_new_output_collision_bound_if_error_ge_one:
  assumes "1 \<le> merkle_binding_error"
  shows "hash_map_new_output_collision_bound s"
  unfolding hash_map_new_output_collision_bound_def
  using order_trans[OF wp_event_le_1 assms] .

lemma hash_map_new_output_collision_bad_imp_hash_new_collision_event:
  assumes "hash_map_new_output_collision_bad s out"
  shows "hash_new_collision_event s out"
  using assms
  unfolding hash_map_new_output_collision_bad_def hash_new_collision_event_def
  by auto

lemma hash_map_new_output_collision_event_bound_from_verify_hash_budget:
  assumes clean: "\<not> hash_map_output_collision s"
  shows
    "wp_event verify_monad (hash_map_new_output_collision_bad s) s \<le>
      hash_collision_budget_value (card (hash_map_output_values s))
        verifier_hash_query_budget"
proof -
  have "wp_event verify_monad (hash_map_new_output_collision_bad s) s \<le>
      wp_event verify_monad (hash_new_collision_event s) s"
    by (rule wp_event_mono)
      (rule hash_map_new_output_collision_bad_imp_hash_new_collision_event)
  also have "... \<le>
      hash_collision_budget_value (card (hash_map_output_values s))
        verifier_hash_query_budget"
    using hash_collision_budget_verify_monad clean
    unfolding hash_collision_budget_def by blast
  finally show ?thesis .
qed

lemma hash_map_new_output_collision_bound_from_verify_hash_budget:
  assumes clean: "\<not> hash_map_output_collision s"
    and error:
      "hash_collision_budget_value (card (hash_map_output_values s))
        verifier_hash_query_budget \<le> merkle_binding_error"
  shows "hash_map_new_output_collision_bound s"
proof -
  have "wp_event verify_monad (hash_map_new_output_collision_bad s) s \<le>
      hash_collision_budget_value (card (hash_map_output_values s))
        verifier_hash_query_budget"
    by (rule hash_map_new_output_collision_event_bound_from_verify_hash_budget
        [OF clean])
  also have "... \<le> merkle_binding_error"
    by (rule error)
  finally show ?thesis
    unfolding hash_map_new_output_collision_bound_def .
qed

lemma hash_map_new_output_collision_bound_from_verify_hash_budget_empty:
  assumes empty_hashmap: "HashMap s = fmempty"
    and error:
      "hash_collision_budget_value (card (hash_map_output_values s))
        verifier_hash_query_budget \<le> merkle_binding_error"
  shows "hash_map_new_output_collision_bound s"
proof -
  have clean: "\<not> hash_map_output_collision s"
    using empty_hashmap unfolding hash_map_output_collision_def by simp
  show ?thesis
    by (rule hash_map_new_output_collision_bound_from_verify_hash_budget
        [OF clean error])
qed

lemma verifier_initial_hash_map_new_output_collision_bound:
  assumes error:
    "hash_collision_budget_value 0 verifier_hash_query_budget \<le>
      merkle_binding_error"
  shows
    "hash_map_new_output_collision_bound (verifier_initial_state tr)"
  by (rule hash_map_new_output_collision_bound_from_verify_hash_budget_empty)
    (use error in simp_all)

lemma verifier_initial_hash_map_new_output_collision_bad_bound_concrete:
  "wp_event verify_monad
    (hash_map_new_output_collision_bad (verifier_initial_state tr))
    (verifier_initial_state tr) \<le> concrete_merkle_binding_error"
proof -
  have clean:
    "\<not> hash_map_output_collision (verifier_initial_state tr)"
    unfolding verifier_initial_state_def hash_map_output_collision_def
    by simp
  have bound:
    "wp_event verify_monad
      (hash_map_new_output_collision_bad (verifier_initial_state tr))
      (verifier_initial_state tr) \<le>
        hash_collision_budget_value
          (card (hash_map_output_values (verifier_initial_state tr)))
          verifier_hash_query_budget"
    by (rule hash_map_new_output_collision_event_bound_from_verify_hash_budget
        [OF clean])
  show ?thesis
    using bound unfolding concrete_merkle_binding_error_def by simp
qed

lemma hash_map_output_collision_bad_imp_new_collision_bad_if_initial_clean:
  assumes clean: "\<not> hash_map_output_collision s"
    and bad: "hash_map_output_collision_bad s out"
  shows "hash_map_new_output_collision_bad s out"
  using assms
  unfolding hash_map_output_collision_bad_def
    hash_map_new_output_collision_bad_def
    hash_map_new_output_collision_def
  by auto

lemma hash_map_output_collision_bound_from_new_collision_bound:
  assumes clean: "\<not> hash_map_output_collision s"
    and new_bound: "hash_map_new_output_collision_bound s"
  shows "hash_map_output_collision_bound s"
proof -
  have "wp_event verify_monad (hash_map_output_collision_bad s) s \<le>
      wp_event verify_monad (hash_map_new_output_collision_bad s) s"
    by (rule wp_event_mono)
      (rule hash_map_output_collision_bad_imp_new_collision_bad_if_initial_clean
        [OF clean])
  also have "... \<le> merkle_binding_error"
    using new_bound unfolding hash_map_new_output_collision_bound_def .
  finally show ?thesis
    unfolding hash_map_output_collision_bound_def .
qed

definition fri_merkle_binding_bad_covered_by_hash_collision
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "fri_merkle_binding_bad_covered_by_hash_collision s \<longleftrightarrow>
      (\<forall>out \<in> set_dist (execute verify_monad s).
        fri_merkle_binding_bad s out \<longrightarrow>
        hash_map_output_collision_bad s out)"

lemma fri_merkle_binding_bound_from_hash_collision_cover:
  assumes cover: "fri_merkle_binding_bad_covered_by_hash_collision s"
    and collision_bound: "hash_map_output_collision_bound s"
  shows "fri_merkle_binding_bound s"
proof -
  have "wp_event verify_monad (fri_merkle_binding_bad s) s \<le>
      wp_event verify_monad (hash_map_output_collision_bad s) s"
    by (rule wp_event_mono_on_support)
      (use cover in
        \<open>auto simp: fri_merkle_binding_bad_covered_by_hash_collision_def\<close>)
  also have "... \<le> merkle_binding_error"
    using collision_bound unfolding hash_map_output_collision_bound_def .
  finally show ?thesis
    unfolding fri_merkle_binding_bound_def .
qed

lemma fri_merkle_binding_bound_from_new_hash_collision_cover:
  assumes clean: "\<not> hash_map_output_collision s"
    and cover: "fri_merkle_binding_bad_covered_by_hash_collision s"
    and new_bound: "hash_map_new_output_collision_bound s"
  shows "fri_merkle_binding_bound s"
proof -
  have collision_bound: "hash_map_output_collision_bound s"
    by (rule hash_map_output_collision_bound_from_new_collision_bound
        [OF clean new_bound])
  show ?thesis
    by (rule fri_merkle_binding_bound_from_hash_collision_cover
        [OF cover collision_bound])
qed

lemma hash_map_output_collision_empty_hashmap[simp]:
  assumes "HashMap s = fmempty"
  shows "\<not> hash_map_output_collision s"
  using assms unfolding hash_map_output_collision_def by simp

lemma verifier_initial_no_hash_map_output_collision[simp]:
  "\<not> hash_map_output_collision (verifier_initial_state tr)"
  by simp

lemma verifier_initial_fri_merkle_binding_bound_concrete:
  assumes cover:
    "fri_merkle_binding_bad_covered_by_hash_collision
      (verifier_initial_state tr)"
  shows
    "wp_event verify_monad
      (fri_merkle_binding_bad (verifier_initial_state tr))
      (verifier_initial_state tr) \<le> concrete_merkle_binding_error"
proof -
  let ?s = "verifier_initial_state tr"
  have "wp_event verify_monad (fri_merkle_binding_bad ?s) ?s \<le>
      wp_event verify_monad (hash_map_output_collision_bad ?s) ?s"
    by (rule wp_event_mono_on_support)
      (use cover in
        \<open>auto simp: fri_merkle_binding_bad_covered_by_hash_collision_def\<close>)
  also have "... \<le>
      wp_event verify_monad (hash_map_new_output_collision_bad ?s) ?s"
    by (rule wp_event_mono)
      (rule hash_map_output_collision_bad_imp_new_collision_bad_if_initial_clean,
        simp, assumption)
  also have "... \<le> concrete_merkle_binding_error"
    by (rule verifier_initial_hash_map_new_output_collision_bad_bound_concrete)
  finally show ?thesis .
qed

lemma fri_merkle_binding_bound_from_new_hash_collision_cover_empty:
  assumes "HashMap s = fmempty"
    and cover: "fri_merkle_binding_bad_covered_by_hash_collision s"
    and new_bound: "hash_map_new_output_collision_bound s"
  shows "fri_merkle_binding_bound s"
  by (rule fri_merkle_binding_bound_from_new_hash_collision_cover
      [OF _ cover new_bound])
    (use assms(1) in simp)

lemma fri_bound_layer_tables_length:
  assumes "fri_bound_layer_tables roots tables final_state"
  shows "length tables = length roots"
  using assms
  unfolding fri_bound_layer_tables_def fri_layer_tables_shape_def by simp

lemma fri_bound_layer_tables_root:
  assumes "fri_bound_layer_tables roots tables final_state"
    and "j < length roots"
  shows "merkle_root_binds_table (roots ! j) (tables ! j) final_state"
  using assms
  unfolding fri_bound_layer_tables_def fri_roots_bind_tables_def by simp

lemma fri_bound_layer_tables_table_length:
  assumes "fri_bound_layer_tables roots tables final_state"
    and "j < length roots"
  shows
    "length (tables ! j) =
      fri_layer_lengths (length roots) (clength * scale) ! j"
  using assms
  unfolding fri_bound_layer_tables_def fri_layer_tables_shape_def
  by simp

lemma fri_bound_layer_tables_same_root_collision_imp_hash_collision_bad:
  assumes out: "out = Some (result, final_state)"
    and bound1: "fri_bound_layer_tables roots tables final_state"
    and bound2: "fri_bound_layer_tables roots tables' final_state"
    and j_bound: "j < length roots"
    and nonempty: "tables ! j \<noteq> []"
    and neq: "tables ! j \<noteq> tables' ! j"
  shows "hash_map_output_collision_bad s out"
proof -
  have bind1:
    "merkle_root_binds_table (roots ! j) (tables ! j) final_state"
    by (rule fri_bound_layer_tables_root[OF bound1 j_bound])
  have bind2:
    "merkle_root_binds_table (roots ! j) (tables' ! j) final_state"
    by (rule fri_bound_layer_tables_root[OF bound2 j_bound])
  have same_len: "length (tables ! j) = length (tables' ! j)"
    using fri_bound_layer_tables_table_length[OF bound1 j_bound]
      fri_bound_layer_tables_table_length[OF bound2 j_bound]
    by simp
  show ?thesis
    by (rule accepted_inconsistent_same_length_merkle_bindings_imp_hash_collision_bad
        [OF out bind1 bind2 same_len nonempty neq])
qed

lemma fri_layer_opening_matches_bound_tableD:
  assumes match:
    "fri_layer_opening_matches_bound_table query_idx layer_idx tables
      layer_chunks"
  obtains len idx xp xp_path xn xn_path
  where "layer_idx < length tables"
    and "length layer_chunks = length tables"
    and "len =
      fri_layer_lengths (length tables) (clength * scale) ! layer_idx"
    and "idx =
      fri_layer_indices (length tables) query_idx (clength * scale) !
        layer_idx"
    and "fri_layer_opening_chunk len xp xp_path xn xn_path
      (layer_chunks ! layer_idx)"
    and "fri_opening_matches_table len idx (tables ! layer_idx) xp xn"
  using match
  unfolding fri_layer_opening_matches_bound_table_def Let_def
  by blast

lemma fri_round_openings_match_tablesD:
  assumes "fri_round_openings_match_tables tables query_idx layer_chunks"
    and "j < length tables"
  shows
    "fri_layer_opening_matches_bound_table query_idx j tables layer_chunks"
  using assms unfolding fri_round_openings_match_tables_def by simp

lemma fri_all_round_openings_match_tablesD:
  assumes
    "fri_all_round_openings_match_tables tables query_idxs round_layers"
    and "i < length query_idxs"
  shows
    "fri_round_openings_match_tables tables (query_idxs ! i)
      (round_layers ! i)"
  using assms unfolding fri_all_round_openings_match_tables_def by simp

lemma trace_fri_tables_bound_opening_matches:
  assumes bound:
    "trace_fri_tables_bound s out trace_roots trace_bs trace_final
      query_idxs trace_round_layers trace_tables trace_final_table"
    and i_bound: "i < length query_idxs"
    and j_bound: "j < length trace_tables"
  shows
    "fri_layer_opening_matches_bound_table (query_idxs ! i) j
      trace_tables (trace_round_layers ! i)"
proof -
  have rounds:
    "fri_all_round_openings_match_tables trace_tables query_idxs
      trace_round_layers"
    using bound unfolding trace_fri_tables_bound_def by blast
  from fri_all_round_openings_match_tablesD[OF rounds i_bound]
  have "fri_round_openings_match_tables trace_tables (query_idxs ! i)
      (trace_round_layers ! i)" .
  then show ?thesis
    using j_bound by (rule fri_round_openings_match_tablesD)
qed

lemma composition_fri_tables_bound_opening_matches:
  assumes bound:
    "composition_fri_tables_bound s out dg composition_roots composition_bs
      composition_final query_idxs composition_round_layers
      composition_tables composition_final_table"
    and i_bound: "i < length query_idxs"
    and j_bound: "j < length composition_tables"
  shows
    "fri_layer_opening_matches_bound_table (query_idxs ! i) j
      composition_tables (composition_round_layers ! i)"
proof -
  have rounds:
    "fri_all_round_openings_match_tables composition_tables query_idxs
      composition_round_layers"
    using bound unfolding composition_fri_tables_bound_def by blast
  from fri_all_round_openings_match_tablesD[OF rounds i_bound]
  have "fri_round_openings_match_tables composition_tables (query_idxs ! i)
      (composition_round_layers ! i)" .
  then show ?thesis
    using j_bound by (rule fri_round_openings_match_tablesD)
qed

lemma fri_merkle_binding_bad_imp_accepted:
  assumes "fri_merkle_binding_bad s out"
  shows "accepted out"
  using assms unfolding fri_merkle_binding_bad_def by simp

lemma fri_merkle_binding_bad_mono_accepted:
  "wp_event verify_monad (fri_merkle_binding_bad s) s \<le>
    wp_event verify_monad accepted s"
  by (rule wp_event_mono)
    (simp add: fri_merkle_binding_bad_imp_accepted)

lemma accepted_good_or_fri_merkle_binding_bad:
  assumes "accepted out"
  shows "fri_merkle_binding_good s out \<or> fri_merkle_binding_bad s out"
  using assms unfolding fri_merkle_binding_bad_def by blast

lemma fri_merkle_binding_goodE:
  assumes good: "fri_merkle_binding_good s out"
    and acc: "accepted out"
  obtains trace_table composition_table as query_idxs
      trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final trace_round_layers composition_round_layers
      trace_tables composition_tables trace_final_table composition_final_table
  where
    "accepted_with_bound_tables s out trace_table composition_table as
      query_idxs"
    and "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      query_idxs trace_round_layers composition_round_layers"
    and "trace_fri_tables_bound s out trace_roots trace_bs trace_final
      query_idxs trace_round_layers trace_tables trace_final_table"
    and "composition_fri_tables_bound s out dg composition_roots
      composition_bs composition_final query_idxs composition_round_layers
      composition_tables composition_final_table"
    and "fri_initial_table_agrees trace_table trace_tables"
    and "fri_initial_table_agrees composition_table composition_tables"
  using good acc unfolding fri_merkle_binding_good_def by blast

end

end
