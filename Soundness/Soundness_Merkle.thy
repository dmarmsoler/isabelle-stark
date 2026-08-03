(*  Title:      Stark/Soundness_Merkle.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Merkle
  imports
    Soundness_Core
begin

context soundness
begin

text \<open>
  A successful verifier execution only checks the sampled authentication paths.
  Turning those local checks into full trace and composition tables bound to the
  initial committed roots is a Merkle binding/collision-resistance property.
  The current random-oracle hash-map model records enough information to replay
  checked paths, but it does not by itself imply existence or uniqueness of a
  complete maliciously committed table.  We therefore expose the missing part as
  a bad event over accepted verifier executions.  Binding for intermediate FRI
  layers is not hidden here; it is part of the FRI bad-challenge-set reductions
  introduced below.
\<close>

definition initial_merkle_binding_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "initial_merkle_binding_bad s out \<longleftrightarrow>
      (\<exists>alphas query_idxs.
        accepted_transcript_shape s out alphas query_idxs \<and>
        \<not> (\<exists>trace_table composition_table.
          accepted_with_bound_tables s out trace_table composition_table
            alphas query_idxs))"

definition initial_merkle_binding_no_bad :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "initial_merkle_binding_no_bad s \<longleftrightarrow>
      (\<forall>out \<in> set_dist (execute verify_monad s).
        \<not> initial_merkle_binding_bad s out)"

definition initial_merkle_binding_collision_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "initial_merkle_binding_collision_bad s out \<longleftrightarrow>
      accepted out \<and>
      (\<exists>result final_state rt.
        out = Some (result, final_state) \<and>
        merkle_root_binding_collision rt final_state)"

definition merkle_root_binding_collision_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "merkle_root_binding_collision_bad s out \<longleftrightarrow>
      accepted out \<and>
      (\<exists>result final_state rt.
        out = Some (result, final_state) \<and>
        merkle_root_binding_collision rt final_state)"

definition hash_map_output_collision_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "hash_map_output_collision_bad s out \<longleftrightarrow>
      accepted out \<and>
      (\<exists>result final_state.
        out = Some (result, final_state) \<and>
        hash_map_output_collision final_state)"

lemma initial_merkle_binding_collision_bad_eq_root_collision_bad:
  "initial_merkle_binding_collision_bad s out =
    merkle_root_binding_collision_bad s out"
  unfolding initial_merkle_binding_collision_bad_def
    merkle_root_binding_collision_bad_def
  by simp

lemma merkle_root_binding_collision_bad_imp_accepted:
  assumes "merkle_root_binding_collision_bad s out"
  shows "accepted out"
  using assms unfolding merkle_root_binding_collision_bad_def by simp

lemma hash_map_output_collision_bad_imp_accepted:
  assumes "hash_map_output_collision_bad s out"
  shows "accepted out"
  using assms unfolding hash_map_output_collision_bad_def by simp

lemma merkle_root_binding_collision_bad_mono_accepted:
  "wp_event verify_monad (merkle_root_binding_collision_bad s) s \<le>
    wp_event verify_monad accepted s"
  by (rule wp_event_mono)
    (simp add: merkle_root_binding_collision_bad_imp_accepted)

lemma hash_map_output_collision_bad_mono_accepted:
  "wp_event verify_monad (hash_map_output_collision_bad s) s \<le>
    wp_event verify_monad accepted s"
  by (rule wp_event_mono)
    (simp add: hash_map_output_collision_bad_imp_accepted)

lemma accepted_inconsistent_merkle_bindings_imp_collision_bad:
  assumes out: "out = Some (result, final_state)"
    and bind1: "merkle_root_binds_table rt table final_state"
    and bind2: "merkle_root_binds_table rt table' final_state"
    and neq: "table \<noteq> table'"
  shows "initial_merkle_binding_collision_bad s out"
proof -
  have collision: "merkle_root_binding_collision rt final_state"
    by (rule merkle_root_binding_collisionI[OF bind1 bind2 neq])
  show ?thesis
  proof (unfold initial_merkle_binding_collision_bad_def accepted_def, intro conjI)
    show "\<not> Option.is_none out"
      using out by simp
    show "\<exists>result final_state rt.
        out = Some (result, final_state) \<and>
        merkle_root_binding_collision rt final_state"
      using out collision by blast
  qed
qed

lemma accepted_inconsistent_merkle_bindings_imp_root_collision_bad:
  assumes out: "out = Some (result, final_state)"
    and bind1: "merkle_root_binds_table rt table final_state"
    and bind2: "merkle_root_binds_table rt table' final_state"
    and neq: "table \<noteq> table'"
  shows "merkle_root_binding_collision_bad s out"
  using accepted_inconsistent_merkle_bindings_imp_collision_bad
      [OF out bind1 bind2 neq]
  unfolding initial_merkle_binding_collision_bad_eq_root_collision_bad .

lemma hash_map_output_collision_badI:
  assumes out: "out = Some (result, final_state)"
    and neq: "x \<noteq> y"
    and x_lookup: "fmlookup (HashMap final_state) x = Some z"
    and y_lookup: "fmlookup (HashMap final_state) y = Some z"
  shows "hash_map_output_collision_bad s out"
proof -
  have collision: "hash_map_output_collision final_state"
    by (rule hash_map_output_collisionI[OF neq x_lookup y_lookup])
  show ?thesis
    unfolding hash_map_output_collision_bad_def accepted_def
    using out collision by auto
qed

lemma accepted_inconsistent_same_length_merkle_bindings_imp_hash_collision_bad:
  assumes out: "out = Some (result, final_state)"
    and bind1: "merkle_root_binds_table rt table final_state"
    and bind2: "merkle_root_binds_table rt table' final_state"
    and same_len: "length table = length table'"
    and nonempty: "table \<noteq> []"
    and neq: "table \<noteq> table'"
  shows "hash_map_output_collision_bad s out"
proof -
  have collision: "hash_map_output_collision final_state"
    by (rule merkle_root_binds_same_length_tables_collision_imp_hash_collision
        [OF bind1 bind2 same_len nonempty neq])
  show ?thesis
    unfolding hash_map_output_collision_bad_def accepted_def
    using out collision by auto
qed

lemma initial_merkle_binding_collision_bad_no_collisionD:
  assumes "\<not> initial_merkle_binding_collision_bad s (Some (result, final_state))"
  shows "\<not> merkle_root_binding_collision rt final_state"
  using assms unfolding initial_merkle_binding_collision_bad_def accepted_def
  by auto

lemma accepted_with_tables_imp_accepted:
  assumes "accepted_with_tables s out trace_table composition_table alphas query_idxs"
  shows "accepted out"
  using assms unfolding accepted_with_tables_def accepted_transcript_shape_def
    verifier_query_indices_derived_def
    accepted_def
  by auto

lemma accepted_transcript_shape_imp_accepted:
  assumes "accepted_transcript_shape s out alphas query_idxs"
  shows "accepted out"
  using assms unfolding accepted_transcript_shape_def verifier_query_indices_derived_def
    accepted_def
  by auto

lemma accepted_with_tables_imp_accepted_transcript_shape:
  assumes "accepted_with_tables s out trace_table composition_table alphas query_idxs"
  shows "accepted_transcript_shape s out alphas query_idxs"
  using assms unfolding accepted_with_tables_def by simp

lemma accepted_with_tables_shapes:
  assumes "accepted_with_tables s out trace_table composition_table alphas query_idxs"
  shows "length trace_table = clength * scale"
    and "length composition_table = clength * scale"
    and "length alphas = length spec"
    and "length query_idxs = rounds"
    and "\<And>idx. idx \<in> set query_idxs \<Longrightarrow> idx < clength * scale"
  using assms
  unfolding accepted_with_tables_def accepted_transcript_shape_def
    verifier_query_indices_derived_def
  by auto

lemma accepted_transcript_shape_query_shapes:
  assumes "accepted_transcript_shape s out alphas query_idxs"
  shows "length query_idxs = rounds"
    and "\<And>idx. idx \<in> set query_idxs \<Longrightarrow> idx < clength * scale"
  using assms
  unfolding accepted_transcript_shape_def verifier_query_indices_derived_def
  by auto

lemma verifier_query_indices_derived_query_sample_space:
  assumes "verifier_query_indices_derived s out query_start_state rest
    f_fri_roots composition_fri_roots query_idxs"
  shows "\<And>idx. idx \<in> set query_idxs \<Longrightarrow> idx \<in> query_sample_space"
  using assms index_less_query_sample_space
  unfolding verifier_query_indices_derived_def query_sample_space_def
  by auto

lemma accepted_transcript_shape_query_sample_space:
  assumes "accepted_transcript_shape s out alphas query_idxs"
  shows "\<And>idx. idx \<in> set query_idxs \<Longrightarrow> idx \<in> query_sample_space"
proof -
  fix idx
  assume idx_in: "idx \<in> set query_idxs"
  obtain result final_state fr f_fri_roots f_final dg composition_fri_roots final rest
    where derived:
      "verifier_query_indices_derived s out
        (verifier_header_state s fr f_fri_roots f_final alphas dg
          composition_fri_roots final)
        rest f_fri_roots composition_fri_roots query_idxs"
    using assms unfolding accepted_transcript_shape_def by blast
  show "idx \<in> query_sample_space"
    by (rule verifier_query_indices_derived_query_sample_space[OF derived idx_in])
qed

lemma accepted_with_tables_query_sample_space:
  assumes "accepted_with_tables s out trace_table composition_table alphas query_idxs"
  shows "\<And>idx. idx \<in> set query_idxs \<Longrightarrow> idx \<in> query_sample_space"
  using accepted_transcript_shape_query_sample_space
    [OF accepted_with_tables_imp_accepted_transcript_shape[OF assms]]
  by blast

lemma accepted_with_bound_tables_query_sample_space:
  assumes "accepted_with_bound_tables s out trace_table composition_table alphas query_idxs"
  shows "\<And>idx. idx \<in> set query_idxs \<Longrightarrow> idx \<in> query_sample_space"
proof -
  have tables: "accepted_with_tables s out trace_table composition_table alphas query_idxs"
    using assms unfolding accepted_with_bound_tables_def by simp
  show "\<And>idx. idx \<in> set query_idxs \<Longrightarrow> idx \<in> query_sample_space"
    by (rule accepted_with_tables_query_sample_space[OF tables])
qed

lemma accepted_with_tables_authenticated_roots:
  assumes "accepted_with_bound_tables s out trace_table composition_table alphas query_idxs"
  obtains result final_state fr composition_root
  where "out = Some (result, final_state)"
    and "merkle_root_binds_table fr trace_table final_state"
    and "merkle_root_binds_table composition_root composition_table final_state"
  using assms unfolding accepted_with_bound_tables_def by auto

lemma accepted_with_bound_tables_imp_accepted_with_tables:
  assumes "accepted_with_bound_tables s out trace_table composition_table alphas query_idxs"
  shows "accepted_with_tables s out trace_table composition_table alphas query_idxs"
  using assms unfolding accepted_with_bound_tables_def by simp

lemma accepted_with_bound_tables_shapes:
  assumes "accepted_with_bound_tables s out trace_table composition_table alphas query_idxs"
  shows "length trace_table = clength * scale"
    and "length composition_table = clength * scale"
    and "length alphas = length spec"
    and "length query_idxs = rounds"
    and "\<And>idx. idx \<in> set query_idxs \<Longrightarrow> idx < clength * scale"
  using accepted_with_tables_shapes
    [OF accepted_with_bound_tables_imp_accepted_with_tables[OF assms]]
  by blast+

lemma accepted_with_bound_tables_imp_accepted:
  assumes "accepted_with_bound_tables s out trace_table composition_table alphas query_idxs"
  shows "accepted out"
  using accepted_with_bound_tables_imp_accepted_with_tables[OF assms]
  by (rule accepted_with_tables_imp_accepted)

definition supported_hash_output_collision_possible
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "supported_hash_output_collision_possible s \<longleftrightarrow>
      (\<exists>out \<in> set_dist (execute verify_monad s).
        hash_map_output_collision_bad s out)"

lemma accepted_with_bound_tables_hash_collision_imp_supported_hash_output_collision_possible:
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and collision: "hash_map_output_collision final_state"
  shows "supported_hash_output_collision_possible s"
proof -
  have accepted: "accepted (Some (result, final_state))"
    by (rule accepted_with_bound_tables_imp_accepted[OF bound])
  have bad:
    "hash_map_output_collision_bad s (Some (result, final_state))"
    unfolding hash_map_output_collision_bad_def
    using accepted collision by blast
  show ?thesis
    unfolding supported_hash_output_collision_possible_def
    using outcome bad by blast
qed

definition alpha_bad_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "alpha_bad_set_hit s bad_sets out \<longleftrightarrow>
      (\<exists>trace_table composition_table as query_idxs.
        accepted_with_bound_tables s out trace_table composition_table as query_idxs \<and>
        as \<in> bad_sets trace_table)"

lemma alpha_bad_set_hit_imp_alpha_list_set_hit:
  assumes hit: "alpha_bad_set_hit s bad_sets out"
    and envelope: "\<And>trace_table. bad_sets trace_table \<subseteq> B"
  shows "alpha_list_set_hit s B out"
proof -
  from hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table as query_idxs"
    and as_bad: "as \<in> bad_sets trace_table"
    unfolding alpha_bad_set_hit_def by blast
  have shape:
    "accepted_transcript_shape s out as query_idxs"
    using bound unfolding accepted_with_bound_tables_def
      accepted_with_tables_def by simp
  have "as \<in> B"
    using as_bad envelope[of trace_table] by auto
  then show ?thesis
    unfolding alpha_list_set_hit_def using shape by blast
qed

definition alpha_header_trace_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "alpha_header_trace_table_candidates s fr f_fri_roots f_final =
      {trace_table.
        \<exists>out composition_table as query_idxs dg composition_fri_roots final rest.
          accepted_with_bound_tables s out trace_table composition_table
            as query_idxs \<and>
          verifier_header_transcript s fr f_fri_roots f_final as dg
            composition_fri_roots final rest}"

definition alpha_header_union_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "alpha_header_union_bad_sets s bad_sets fr f_fri_roots f_final =
      {as \<in> alpha_space.
        \<exists>trace_table \<in>
          alpha_header_trace_table_candidates s fr f_fri_roots f_final.
          as \<in> bad_sets trace_table}"

definition alpha_header_supported_trace_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final =
      {trace_table.
        \<exists>out composition_table as query_idxs dg composition_fri_roots final rest.
          out \<in> set_dist (execute verify_monad s) \<and>
          accepted_with_bound_tables s out trace_table composition_table
            as query_idxs \<and>
          verifier_header_transcript s fr f_fri_roots f_final as dg
            composition_fri_roots final rest}"

definition alpha_header_supported_union_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "alpha_header_supported_union_bad_sets s bad_sets fr f_fri_roots f_final =
      {as \<in> alpha_space.
        \<exists>trace_table \<in>
          alpha_header_supported_trace_table_candidates s fr f_fri_roots
            f_final.
          as \<in> bad_sets trace_table}"

lemma alpha_header_union_bad_sets_subset_alpha_space:
  "alpha_header_union_bad_sets s bad_sets fr f_fri_roots f_final \<subseteq>
    alpha_space"
  unfolding alpha_header_union_bad_sets_def by auto

lemma alpha_header_supported_union_bad_sets_subset_alpha_space:
  "alpha_header_supported_union_bad_sets s bad_sets fr f_fri_roots f_final
    \<subseteq> alpha_space"
  unfolding alpha_header_supported_union_bad_sets_def by auto

lemma alpha_header_union_bad_sets_fraction_bound_if_unique_candidate:
  fixes C :: prob
  assumes unique:
      "\<exists>trace_table.
        alpha_header_trace_table_candidates s fr f_fri_roots f_final \<subseteq>
          {trace_table}"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bound:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space) \<le> C"
  shows
    "nnreal
      (card (alpha_header_union_bad_sets s bad_sets fr f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le> C"
proof -
  from unique obtain trace_table where candidates:
    "alpha_header_trace_table_candidates s fr f_fri_roots f_final \<subseteq>
      {trace_table}"
    by blast
  have union_subset:
    "alpha_header_union_bad_sets s bad_sets fr f_fri_roots f_final \<subseteq>
      bad_sets trace_table"
    unfolding alpha_header_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets trace_table)"
    by (rule finite_subset[OF subset finite_alpha_space])
  have card_le:
    "card (alpha_header_union_bad_sets s bad_sets fr f_fri_roots f_final) \<le>
      card (bad_sets trace_table)"
    by (rule card_mono[OF finite_bad union_subset])
  have "nnreal
        (card (alpha_header_union_bad_sets s bad_sets fr f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le>
      nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma alpha_header_supported_union_bad_sets_fraction_bound_if_unique_candidate:
  fixes C :: prob
  assumes unique:
      "\<exists>trace_table.
        alpha_header_supported_trace_table_candidates s fr f_fri_roots
          f_final \<subseteq> {trace_table}"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bound:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space) \<le> C"
  shows
    "nnreal
      (card
        (alpha_header_supported_union_bad_sets s bad_sets fr f_fri_roots
          f_final)) /
      nnreal (card alpha_space) \<le> C"
proof -
  from unique obtain trace_table where candidates:
    "alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final
      \<subseteq> {trace_table}"
    by blast
  have union_subset:
    "alpha_header_supported_union_bad_sets s bad_sets fr f_fri_roots f_final
      \<subseteq> bad_sets trace_table"
    unfolding alpha_header_supported_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets trace_table)"
    by (rule finite_subset[OF subset finite_alpha_space])
  have card_le:
    "card
      (alpha_header_supported_union_bad_sets s bad_sets fr f_fri_roots
        f_final) \<le> card (bad_sets trace_table)"
    by (rule card_mono[OF finite_bad union_subset])
  have "nnreal
        (card
          (alpha_header_supported_union_bad_sets s bad_sets fr f_fri_roots
            f_final)) /
      nnreal (card alpha_space) \<le>
      nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma composition_trace_alpha_header_union_fraction_bound_if_unique_candidate:
  assumes unique:
      "\<exists>trace_table.
        alpha_header_trace_table_candidates s fr f_fri_roots f_final \<subseteq>
          {trace_table}"
  shows
    "nnreal
      (card
        (alpha_header_union_bad_sets s composition_trace_bad_alpha_space
          fr f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le> composition_error_bound"
  by (rule alpha_header_union_bad_sets_fraction_bound_if_unique_candidate
      [OF unique composition_trace_bad_alpha_space_subset_alpha_space
        composition_trace_bad_alpha_space_fraction_bound_alpha_space])

lemma composition_trace_alpha_header_supported_union_fraction_bound_if_unique_candidate:
  assumes unique:
      "\<exists>trace_table.
        alpha_header_supported_trace_table_candidates s fr f_fri_roots
          f_final \<subseteq> {trace_table}"
  shows
    "nnreal
      (card
        (alpha_header_supported_union_bad_sets s
          composition_trace_bad_alpha_space fr f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le> composition_error_bound"
  by (rule alpha_header_supported_union_bad_sets_fraction_bound_if_unique_candidate
      [OF unique composition_trace_bad_alpha_space_subset_alpha_space
        composition_trace_bad_alpha_space_fraction_bound_alpha_space])

lemma alpha_bad_set_hit_imp_alpha_header_union_bad_set_hit:
  assumes hit: "alpha_bad_set_hit s bad_sets out"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
  shows
    "alpha_header_list_set_hit s
      (alpha_header_union_bad_sets s bad_sets) out"
proof -
  from hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table
        as query_idxs"
    and as_bad: "as \<in> bad_sets trace_table"
    unfolding alpha_bad_set_hit_def by blast
  from bound obtain result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    out_eq: "out = Some (result, final_state)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding accepted_with_bound_tables_def by blast
  have shape:
    "accepted_transcript_shape s out as query_idxs"
    using accepted_with_bound_tables_imp_accepted_with_tables[OF bound]
      accepted_with_tables_imp_accepted_transcript_shape
    by blast
  have candidate:
    "trace_table \<in>
      alpha_header_trace_table_candidates s fr f_fri_roots f_final"
    unfolding alpha_header_trace_table_candidates_def
    using bound header by blast
  have as_union:
    "as \<in> alpha_header_union_bad_sets s bad_sets fr f_fri_roots f_final"
    unfolding alpha_header_union_bad_sets_def
    using as_bad candidate subset[of trace_table] by auto
  show ?thesis
    unfolding alpha_header_list_set_hit_def
    using shape out_eq header as_union by blast
qed

lemma alpha_bad_set_hit_imp_alpha_header_supported_union_bad_set_hit:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and hit: "alpha_bad_set_hit s bad_sets out"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
  shows
    "alpha_header_list_set_hit s
      (alpha_header_supported_union_bad_sets s bad_sets) out"
proof -
  from hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table
        as query_idxs"
    and as_bad: "as \<in> bad_sets trace_table"
    unfolding alpha_bad_set_hit_def by blast
  from bound obtain result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    out_eq: "out = Some (result, final_state)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding accepted_with_bound_tables_def by blast
  have shape:
    "accepted_transcript_shape s out as query_idxs"
    using accepted_with_bound_tables_imp_accepted_with_tables[OF bound]
      accepted_with_tables_imp_accepted_transcript_shape
    by blast
  have candidate:
    "trace_table \<in>
      alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final"
    unfolding alpha_header_supported_trace_table_candidates_def
    using outcome bound header by blast
  have as_union:
    "as \<in>
      alpha_header_supported_union_bad_sets s bad_sets fr f_fri_roots f_final"
    unfolding alpha_header_supported_union_bad_sets_def
    using as_bad candidate subset[of trace_table] by auto
  show ?thesis
    unfolding alpha_header_list_set_hit_def
    using shape out_eq header as_union by blast
qed

definition alpha_challenge_freshness_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "alpha_challenge_freshness_assumption s \<longleftrightarrow>
      (\<forall>bad_sets.
        (\<forall>trace_table. bad_sets trace_table \<subseteq> alpha_space) \<longrightarrow>
        (\<forall>trace_table.
          nnreal (card (bad_sets trace_table)) /
            nnreal (card alpha_space) \<le> composition_error_bound) \<longrightarrow>
        wp_event verify_monad (alpha_bad_set_hit s bad_sets) s \<le>
          composition_error_bound)"

text \<open>
  The protocol currently represents all Fiat-Shamir challenges through the same
  random-oracle hash map, without protocol-level domain-separated labels for
  alpha, query-index, and FRI challenges.  The following predicates below state
  the precise freshness obligations needed for each challenge family.  Phase 4E
  bundles them into one random-oracle model interface rather than adding labels
  to the protocol in this refactor.  Merkle hash uses are not represented as
  freshness obligations here; their binding role remains the explicit
  \<^term>\<open>initial_merkle_binding_no_bad\<close> premise.
\<close>

lemma initial_merkle_binding_no_badE:
  assumes bind: "initial_merkle_binding_no_bad s"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and shape: "accepted_transcript_shape s (Some (result, final_state)) alphas query_idxs"
  obtains trace_table composition_table
  where "accepted_with_bound_tables s (Some (result, final_state))
    trace_table composition_table alphas query_idxs"
  using assms
  unfolding initial_merkle_binding_no_bad_def initial_merkle_binding_bad_def
  by blast

lemma initial_merkle_binding_bad_bound:
  assumes bind: "initial_merkle_binding_no_bad s"
  shows "wp_event verify_monad (initial_merkle_binding_bad s) s \<le> 0"
proof -
  have "wp_event verify_monad (initial_merkle_binding_bad s) s \<le>
      wp_event verify_monad
        (\<lambda>_ :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option. False) s"
    by (rule wp_event_mono_on_support)
      (use bind in \<open>auto simp: initial_merkle_binding_no_bad_def\<close>)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis .
qed

lemma accepted_with_bound_tables_query_consistency:
  assumes bound:
    "accepted_with_bound_tables s out trace_table composition_table alphas query_idxs"
  shows "\<And>idx. idx \<in> set query_idxs \<Longrightarrow>
    query_consistent_at trace_table composition_table alphas idx"
  using bound unfolding accepted_with_bound_tables_def accepted_with_tables_def by simp

lemma accepted_with_bound_tables_bound_roots:
  assumes bound:
    "accepted_with_bound_tables s out trace_table composition_table alphas query_idxs"
  obtains result final_state fr composition_root
  where "out = Some (result, final_state)"
    and "merkle_root_binds_table fr trace_table final_state"
    and "merkle_root_binds_table composition_root composition_table final_state"
  using accepted_with_tables_authenticated_roots[OF bound] by blast

lemma verifier_header_transcript_shapes:
  assumes "verifier_header_transcript s fr f_fri_roots f_final as dg
    composition_fri_roots final rest"
  shows "PTranscript s =
      verifier_header_messages fr f_fri_roots f_final as dg
        composition_fri_roots final @ rest"
    and "length f_fri_roots = ceil_log clength"
    and "length as = length spec"
    and "length composition_fri_roots = ceil_log (to_nat dg + 1)"
  using assms unfolding verifier_header_transcript_def by simp_all

lemma verifier_header_transcript_unique:
  assumes h1:
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    and h2:
    "verifier_header_transcript s fr' f_fri_roots' f_final' as' dg'
      composition_fri_roots' final' rest'"
  shows
    "fr' = fr \<and>
     f_fri_roots' = f_fri_roots \<and>
     f_final' = f_final \<and>
     as' = as \<and>
     dg' = dg \<and>
     composition_fri_roots' = composition_fri_roots \<and>
     final' = final \<and>
     rest' = rest"
proof -
  have lengths:
    "length f_fri_roots = ceil_log clength"
    "length as = length spec"
    "length composition_fri_roots = ceil_log (to_nat dg + 1)"
    "length f_fri_roots' = ceil_log clength"
    "length as' = length spec"
    "length composition_fri_roots' = ceil_log (to_nat dg' + 1)"
    using h1 h2 unfolding verifier_header_transcript_def by simp_all
  have msg_eq:
    "verifier_header_messages fr f_fri_roots f_final as dg
        composition_fri_roots final @ rest =
      verifier_header_messages fr' f_fri_roots' f_final' as' dg'
        composition_fri_roots' final' @ rest'"
    using h1 h2 unfolding verifier_header_transcript_def by simp
  then show ?thesis
    using lengths
    unfolding verifier_header_messages_def
    by (auto simp: append_eq_append_conv_if split: if_splits)
qed

definition alpha_header_trace_table_candidate_state
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
      trace_table final_state \<longleftrightarrow>
      (\<exists>result composition_table as query_idxs dg composition_fri_roots final
          rest.
        accepted_with_bound_tables s (Some (result, final_state))
          trace_table composition_table as query_idxs \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest \<and>
        merkle_root_binds_table fr trace_table final_state)"

definition alpha_header_supported_trace_table_candidate_state
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
      f_final trace_table final_state \<longleftrightarrow>
      (\<exists>result composition_table as query_idxs dg composition_fri_roots final
          rest.
        Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
        accepted_with_bound_tables s (Some (result, final_state))
          trace_table composition_table as query_idxs \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest \<and>
        merkle_root_binds_table fr trace_table final_state)"

lemma alpha_header_trace_table_candidates_iff_state:
  "trace_table \<in>
      alpha_header_trace_table_candidates s fr f_fri_roots f_final \<longleftrightarrow>
    (\<exists>final_state.
      alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table final_state)"
proof
  assume candidate:
    "trace_table \<in>
      alpha_header_trace_table_candidates s fr f_fri_roots f_final"
  then obtain out composition_table as query_idxs dg composition_fri_roots
      final rest where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding alpha_header_trace_table_candidates_def by blast
  from bound obtain result final_state fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    out_eq: "out = Some (result, final_state)"
    and header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and bind:
      "merkle_root_binds_table fr' trace_table final_state"
    unfolding accepted_with_bound_tables_def by blast
  have fr_eq: "fr' = fr"
    using verifier_header_transcript_unique[OF header' header] by simp
  have bound_some:
    "accepted_with_bound_tables s (Some (result, final_state))
      trace_table composition_table as query_idxs"
    using bound out_eq by simp
  have state:
    "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
      trace_table final_state"
    unfolding alpha_header_trace_table_candidate_state_def
    by (intro exI[of _ result] exI[of _ composition_table] exI[of _ as]
        exI[of _ query_idxs] exI[of _ dg] exI[of _ composition_fri_roots]
        exI[of _ final] exI[of _ rest])
      (use bound_some header bind fr_eq in simp)
  then show
    "\<exists>final_state.
      alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table final_state"
    by blast
next
  assume
    "\<exists>final_state.
      alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table final_state"
  then obtain final_state result composition_table as query_idxs dg
      composition_fri_roots final rest where
    bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding alpha_header_trace_table_candidate_state_def by blast
  show
    "trace_table \<in>
      alpha_header_trace_table_candidates s fr f_fri_roots f_final"
    unfolding alpha_header_trace_table_candidates_def
    using bound header by blast
qed

lemma alpha_header_supported_trace_table_candidates_iff_state:
  "trace_table \<in>
      alpha_header_supported_trace_table_candidates s fr f_fri_roots
        f_final \<longleftrightarrow>
    (\<exists>final_state.
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state)"
proof
  assume candidate:
    "trace_table \<in>
      alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final"
  then obtain out composition_table as query_idxs dg composition_fri_roots
      final rest where
    outcome: "out \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding alpha_header_supported_trace_table_candidates_def by blast
  from bound obtain result final_state fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    out_eq: "out = Some (result, final_state)"
    and header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and bind:
      "merkle_root_binds_table fr' trace_table final_state"
    unfolding accepted_with_bound_tables_def by blast
  have fr_eq: "fr' = fr"
    using verifier_header_transcript_unique[OF header' header] by simp
  have state:
    "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
      f_final trace_table final_state"
    unfolding alpha_header_supported_trace_table_candidate_state_def
    by (intro exI[of _ result] exI[of _ composition_table] exI[of _ as]
        exI[of _ query_idxs] exI[of _ dg] exI[of _ composition_fri_roots]
        exI[of _ final] exI[of _ rest])
      (use outcome bound header bind fr_eq out_eq in simp)
  then show
    "\<exists>final_state.
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
    by blast
next
  assume
    "\<exists>final_state.
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
  then obtain final_state result composition_table as query_idxs dg
      composition_fri_roots final rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding alpha_header_supported_trace_table_candidate_state_def by blast
  show
    "trace_table \<in>
      alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final"
    unfolding alpha_header_supported_trace_table_candidates_def
    using outcome bound header by blast
qed

lemma alpha_header_supported_trace_table_candidate_state_imp_candidate_state:
  assumes
    "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
      f_final trace_table final_state"
  shows
    "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
      trace_table final_state"
  using assms
  unfolding alpha_header_supported_trace_table_candidate_state_def
    alpha_header_trace_table_candidate_state_def
  by blast

lemma alpha_header_trace_table_candidate_states_common_extension_unique_if_clean:
  assumes clean: "\<not> hash_map_output_collision u"
    and candidate1:
      "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table final_state"
    and candidate2:
      "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table' final_state'"
    and ext1: "final_state \<le> u"
    and ext2: "final_state' \<le> u"
  shows "trace_table = trace_table'"
proof -
  from candidate1 obtain result composition_table as query_idxs dg
      composition_fri_roots final rest where
    bound1:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and bind1: "merkle_root_binds_table fr trace_table final_state"
    unfolding alpha_header_trace_table_candidate_state_def by blast
  from candidate2 obtain result' composition_table' as' query_idxs' dg'
      composition_fri_roots' final' rest' where
    bound2:
      "accepted_with_bound_tables s (Some (result', final_state'))
        trace_table' composition_table' as' query_idxs'"
    and bind2: "merkle_root_binds_table fr trace_table' final_state'"
    unfolding alpha_header_trace_table_candidate_state_def by blast
  have same_len: "length trace_table = length trace_table'"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      accepted_with_bound_tables_shapes(1)[OF bound2]
    by simp
  have nonempty: "trace_table \<noteq> []"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      eval_domain_nontrivial by auto
  show ?thesis
    by (rule merkle_root_binds_same_length_tables_common_extension_unique_if_clean
        [OF clean bind1 bind2 ext1 ext2 same_len nonempty])
qed

lemma alpha_header_trace_table_candidate_states_compatible_unique_if_clean_merge:
  assumes compatible: "hash_maps_compatible final_state final_state'"
    and clean:
      "\<not> hash_map_output_collision
        (hash_state_merge final_state final_state')"
    and candidate1:
      "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table final_state"
    and candidate2:
      "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table' final_state'"
  shows "trace_table = trace_table'"
proof -
  from candidate1 obtain result composition_table as query_idxs dg
      composition_fri_roots final rest where
    bound1:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and bind1: "merkle_root_binds_table fr trace_table final_state"
    unfolding alpha_header_trace_table_candidate_state_def by blast
  from candidate2 obtain result' composition_table' as' query_idxs' dg'
      composition_fri_roots' final' rest' where
    bound2:
      "accepted_with_bound_tables s (Some (result', final_state'))
        trace_table' composition_table' as' query_idxs'"
    and bind2: "merkle_root_binds_table fr trace_table' final_state'"
    unfolding alpha_header_trace_table_candidate_state_def by blast
  have same_len: "length trace_table = length trace_table'"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      accepted_with_bound_tables_shapes(1)[OF bound2]
    by simp
  have nonempty: "trace_table \<noteq> []"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      eval_domain_nontrivial by auto
  show ?thesis
    by (rule
        merkle_root_binds_same_length_tables_compatible_states_unique_if_clean_merge
        [OF compatible clean bind1 bind2 same_len nonempty])
qed

lemma alpha_header_trace_table_candidate_states_merkle_compatible_unique_if_clean_merge:
  assumes compatible:
      "merkle_hash_maps_compatible final_state final_state'"
    and clean:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    and candidate1:
      "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table final_state"
    and candidate2:
      "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table' final_state'"
  shows "trace_table = trace_table'"
proof -
  from candidate1 obtain result composition_table as query_idxs dg
      composition_fri_roots final rest where
    bound1:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and bind1: "merkle_root_binds_table fr trace_table final_state"
    unfolding alpha_header_trace_table_candidate_state_def by blast
  from candidate2 obtain result' composition_table' as' query_idxs' dg'
      composition_fri_roots' final' rest' where
    bound2:
      "accepted_with_bound_tables s (Some (result', final_state'))
        trace_table' composition_table' as' query_idxs'"
    and bind2: "merkle_root_binds_table fr trace_table' final_state'"
    unfolding alpha_header_trace_table_candidate_state_def by blast
  have same_len: "length trace_table = length trace_table'"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      accepted_with_bound_tables_shapes(1)[OF bound2]
    by simp
  have nonempty: "trace_table \<noteq> []"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      eval_domain_nontrivial by auto
  show ?thesis
    by (rule
        merkle_root_binds_same_length_tables_merkle_compatible_unique_if_clean_merge
        [OF compatible clean bind1 bind2 same_len nonempty])
qed

lemma alpha_header_trace_table_candidates_subset_singleton_if_common_clean_extension:
  assumes clean: "\<not> hash_map_output_collision u"
    and common_ext:
      "\<And>trace_table final_state.
        alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
          trace_table final_state \<Longrightarrow>
        final_state \<le> u"
  shows
    "\<exists>trace_table.
      alpha_header_trace_table_candidates s fr f_fri_roots f_final \<subseteq>
        {trace_table}"
proof (cases
    "alpha_header_trace_table_candidates s fr f_fri_roots f_final = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"]) simp
next
  case False
  then obtain trace_table0 where table0:
    "trace_table0 \<in>
      alpha_header_trace_table_candidates s fr f_fri_roots f_final"
    by blast
  then obtain final_state0 where state0:
    "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
      trace_table0 final_state0"
    using alpha_header_trace_table_candidates_iff_state by blast
  have ext0: "final_state0 \<le> u"
    by (rule common_ext[OF state0])
  have subset:
    "alpha_header_trace_table_candidates s fr f_fri_roots f_final \<subseteq>
      {trace_table0}"
  proof
    fix trace_table
    assume table:
      "trace_table \<in>
        alpha_header_trace_table_candidates s fr f_fri_roots f_final"
    then obtain final_state where state:
      "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table final_state"
      using alpha_header_trace_table_candidates_iff_state by blast
    have ext: "final_state \<le> u"
      by (rule common_ext[OF state])
    have "trace_table = trace_table0"
      by (rule
          alpha_header_trace_table_candidate_states_common_extension_unique_if_clean
          [OF clean state state0 ext ext0])
    then show "trace_table \<in> {trace_table0}"
      by simp
  qed
  then show ?thesis
    by blast
qed

lemma alpha_header_trace_table_candidates_subset_singleton_if_pairwise_clean_merge:
  assumes pairwise:
      "\<And>trace_table final_state trace_table' final_state'.
        alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
          trace_table final_state \<Longrightarrow>
        alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
          trace_table' final_state' \<Longrightarrow>
        hash_maps_compatible final_state final_state' \<and>
        \<not> hash_map_output_collision
          (hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table.
      alpha_header_trace_table_candidates s fr f_fri_roots f_final \<subseteq>
        {trace_table}"
proof (cases
    "alpha_header_trace_table_candidates s fr f_fri_roots f_final = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"]) simp
next
  case False
  then obtain trace_table0 where table0:
    "trace_table0 \<in>
      alpha_header_trace_table_candidates s fr f_fri_roots f_final"
    by blast
  then obtain final_state0 where state0:
    "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
      trace_table0 final_state0"
    using alpha_header_trace_table_candidates_iff_state by blast
  have subset:
    "alpha_header_trace_table_candidates s fr f_fri_roots f_final \<subseteq>
      {trace_table0}"
  proof
    fix trace_table
    assume table:
      "trace_table \<in>
        alpha_header_trace_table_candidates s fr f_fri_roots f_final"
    then obtain final_state where state:
      "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table final_state"
      using alpha_header_trace_table_candidates_iff_state by blast
    have compatible:
      "hash_maps_compatible final_state final_state0"
      using pairwise[OF state state0] by simp
    have clean:
      "\<not> hash_map_output_collision
        (hash_state_merge final_state final_state0)"
      using pairwise[OF state state0] by simp
    have "trace_table = trace_table0"
      by (rule
          alpha_header_trace_table_candidate_states_compatible_unique_if_clean_merge
          [OF compatible clean state state0])
    then show "trace_table \<in> {trace_table0}"
      by simp
  qed
  then show ?thesis
    by blast
qed

lemma alpha_header_supported_trace_table_candidates_subset_singleton_if_pairwise_clean_merge:
  assumes pairwise:
      "\<And>trace_table final_state trace_table' final_state'.
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table final_state \<Longrightarrow>
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table' final_state' \<Longrightarrow>
        hash_maps_compatible final_state final_state' \<and>
        \<not> hash_map_output_collision
          (hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table.
      alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final
        \<subseteq> {trace_table}"
proof (cases
    "alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final =
      {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"]) simp
next
  case False
  then obtain trace_table0 where table0:
    "trace_table0 \<in>
      alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final"
    by blast
  then obtain final_state0 where state0:
    "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
      f_final trace_table0 final_state0"
    using alpha_header_supported_trace_table_candidates_iff_state by blast
  have state0_plain:
    "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
      trace_table0 final_state0"
    by (rule alpha_header_supported_trace_table_candidate_state_imp_candidate_state
        [OF state0])
  have subset:
    "alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final
      \<subseteq> {trace_table0}"
  proof
    fix trace_table
    assume table:
      "trace_table \<in>
        alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final"
    then obtain final_state where state:
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
      using alpha_header_supported_trace_table_candidates_iff_state by blast
    have state_plain:
      "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table final_state"
      by (rule
          alpha_header_supported_trace_table_candidate_state_imp_candidate_state
          [OF state])
    have compatible:
      "hash_maps_compatible final_state final_state0"
      using pairwise[OF state state0] by simp
    have clean:
      "\<not> hash_map_output_collision
        (hash_state_merge final_state final_state0)"
      using pairwise[OF state state0] by simp
    have "trace_table = trace_table0"
      by (rule
          alpha_header_trace_table_candidate_states_compatible_unique_if_clean_merge
          [OF compatible clean state_plain state0_plain])
    then show "trace_table \<in> {trace_table0}"
      by simp
  qed
  then show ?thesis
    by blast
qed

lemma alpha_header_supported_trace_table_candidates_subset_singleton_if_pairwise_no_value_conflict_clean_merge:
  assumes pairwise:
      "\<And>trace_table final_state trace_table' final_state'.
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table final_state \<Longrightarrow>
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table' final_state' \<Longrightarrow>
        \<not> hash_map_value_conflict final_state final_state' \<and>
        \<not> hash_map_output_collision
          (hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table.
      alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final
        \<subseteq> {trace_table}"
proof (rule
    alpha_header_supported_trace_table_candidates_subset_singleton_if_pairwise_clean_merge)
  fix trace_table final_state trace_table' final_state'
  assume candidate:
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
    and candidate':
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state'"
  have no_conflict:
    "\<not> hash_map_value_conflict final_state final_state'"
    using pairwise[OF candidate candidate'] by simp
  have compatible:
    "hash_maps_compatible final_state final_state'"
    using no_conflict
    unfolding hash_maps_compatible_iff_no_value_conflict .
  have clean:
    "\<not> hash_map_output_collision
      (hash_state_merge final_state final_state')"
    using pairwise[OF candidate candidate'] by simp
  show "hash_maps_compatible final_state final_state' \<and>
      \<not> hash_map_output_collision
        (hash_state_merge final_state final_state')"
    using compatible clean by simp
qed

lemma alpha_header_supported_trace_table_candidates_subset_singleton_if_pairwise_merkle_clean_merge:
  assumes pairwise:
      "\<And>trace_table final_state trace_table' final_state'.
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table final_state \<Longrightarrow>
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table' final_state' \<Longrightarrow>
        merkle_hash_maps_compatible final_state final_state' \<and>
        \<not> hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table.
      alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final
        \<subseteq> {trace_table}"
proof (cases
    "alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final =
      {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"]) simp
next
  case False
  then obtain trace_table0 where table0:
    "trace_table0 \<in>
      alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final"
    by blast
  then obtain final_state0 where state0:
    "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
      f_final trace_table0 final_state0"
    using alpha_header_supported_trace_table_candidates_iff_state by blast
  have state0_plain:
    "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
      trace_table0 final_state0"
    by (rule alpha_header_supported_trace_table_candidate_state_imp_candidate_state
        [OF state0])
  have subset:
    "alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final
      \<subseteq> {trace_table0}"
  proof
    fix trace_table
    assume table:
      "trace_table \<in>
        alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final"
    then obtain final_state where state:
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
      using alpha_header_supported_trace_table_candidates_iff_state by blast
    have state_plain:
      "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
        trace_table final_state"
      by (rule
          alpha_header_supported_trace_table_candidate_state_imp_candidate_state
          [OF state])
    have compatible:
      "merkle_hash_maps_compatible final_state final_state0"
      using pairwise[OF state state0] by simp
    have clean:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state0)"
      using pairwise[OF state state0] by simp
    have "trace_table = trace_table0"
      by (rule
          alpha_header_trace_table_candidate_states_merkle_compatible_unique_if_clean_merge
          [OF compatible clean state_plain state0_plain])
    then show "trace_table \<in> {trace_table0}"
      by simp
  qed
  then show ?thesis
    by blast
qed

lemma alpha_header_supported_trace_table_candidates_subset_singleton_if_pairwise_no_merkle_value_conflict_clean_merge:
  assumes pairwise:
      "\<And>trace_table final_state trace_table' final_state'.
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table final_state \<Longrightarrow>
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table' final_state' \<Longrightarrow>
        \<not> merkle_hash_value_conflict final_state final_state' \<and>
        \<not> hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table.
      alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final
        \<subseteq> {trace_table}"
proof (rule
    alpha_header_supported_trace_table_candidates_subset_singleton_if_pairwise_merkle_clean_merge)
  fix trace_table final_state trace_table' final_state'
  assume candidate:
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
    and candidate':
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state'"
  have no_conflict:
    "\<not> merkle_hash_value_conflict final_state final_state'"
    using pairwise[OF candidate candidate'] by simp
  have compatible:
    "merkle_hash_maps_compatible final_state final_state'"
    using no_conflict
    unfolding merkle_hash_maps_compatible_iff_no_value_conflict .
  have clean:
    "\<not> hash_map_output_collision
      (merkle_hash_state_merge final_state final_state')"
    using pairwise[OF candidate candidate'] by simp
  show "merkle_hash_maps_compatible final_state final_state' \<and>
      \<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    using compatible clean by simp
qed

lemma alpha_header_supported_trace_table_candidates_subset_singleton_if_common_clean_merkle_extension:
  assumes clean: "\<not> hash_map_output_collision u"
    and common_ext:
      "\<And>trace_table final_state.
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table final_state \<Longrightarrow>
        merkle_hash_extends final_state u"
  shows
    "\<exists>trace_table.
      alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final
        \<subseteq> {trace_table}"
proof (rule
    alpha_header_supported_trace_table_candidates_subset_singleton_if_pairwise_no_merkle_value_conflict_clean_merge)
  fix trace_table final_state trace_table' final_state'
  assume candidate:
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
    and candidate':
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state'"
  have ext: "merkle_hash_extends final_state u"
    by (rule common_ext[OF candidate])
  have ext': "merkle_hash_extends final_state' u"
    by (rule common_ext[OF candidate'])
  show "\<not> merkle_hash_value_conflict final_state final_state' \<and>
      \<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    by (rule common_clean_merkle_extension_imp_pairwise_merkle_clean
        [OF ext ext' clean])
qed

lemma alpha_header_supported_trace_table_candidate_states_distinct_imp_merkle_conflict_or_merge_collision:
  assumes candidate:
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
    and candidate':
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state'"
    and distinct_tables: "trace_table \<noteq> trace_table'"
  shows
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
proof (rule ccontr)
  assume no_bad:
    "\<not> (merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state'))"
  have compatible:
    "merkle_hash_maps_compatible final_state final_state'"
    using no_bad unfolding merkle_hash_maps_compatible_iff_no_value_conflict
    by simp
  have clean:
    "\<not> hash_map_output_collision
      (merkle_hash_state_merge final_state final_state')"
    using no_bad by simp
  have candidate_plain:
    "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
      trace_table final_state"
    by (rule alpha_header_supported_trace_table_candidate_state_imp_candidate_state
        [OF candidate])
  have candidate_plain':
    "alpha_header_trace_table_candidate_state s fr f_fri_roots f_final
      trace_table' final_state'"
    by (rule alpha_header_supported_trace_table_candidate_state_imp_candidate_state
        [OF candidate'])
  have "trace_table = trace_table'"
    by (rule alpha_header_trace_table_candidate_states_merkle_compatible_unique_if_clean_merge
        [OF compatible clean candidate_plain candidate_plain'])
  then show False
    using distinct_tables by contradiction
qed

lemma alpha_header_supported_trace_table_candidates_not_singleton_imp_pairwise_merkle_bad:
  assumes not_unique:
      "\<not> (\<exists>trace_table.
        alpha_header_supported_trace_table_candidates s fr f_fri_roots
          f_final \<subseteq> {trace_table})"
  shows
    "\<exists>trace_table final_state trace_table' final_state'.
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state \<and>
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state' \<and>
      trace_table \<noteq> trace_table' \<and>
      (merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state'))"
proof -
  let ?C =
    "alpha_header_supported_trace_table_candidates s fr f_fri_roots f_final"
  have nonempty: "?C \<noteq> {}"
    using not_unique by auto
  then obtain trace_table where table: "trace_table \<in> ?C"
    by blast
  have "\<not> ?C \<subseteq> {trace_table}"
    using not_unique by blast
  then obtain trace_table' where table':
      "trace_table' \<in> ?C"
    and distinct_tables: "trace_table \<noteq> trace_table'"
    by auto
  from table obtain final_state where candidate:
    "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
      f_final trace_table final_state"
    using alpha_header_supported_trace_table_candidates_iff_state by blast
  from table' obtain final_state' where candidate':
    "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
      f_final trace_table' final_state'"
    using alpha_header_supported_trace_table_candidates_iff_state by blast
  have bad:
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    by (rule
        alpha_header_supported_trace_table_candidate_states_distinct_imp_merkle_conflict_or_merge_collision
        [OF candidate candidate' distinct_tables])
  show ?thesis
    using candidate candidate' distinct_tables bad by blast
qed

definition alpha_header_supported_pairwise_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "alpha_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final
      \<longleftrightarrow>
      (\<exists>trace_table final_state trace_table' final_state'.
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table final_state \<and>
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table' final_state' \<and>
        trace_table \<noteq> trace_table' \<and>
        (merkle_hash_value_conflict final_state final_state' \<or>
          hash_map_output_collision
            (merkle_hash_state_merge final_state final_state')))"

definition alpha_supported_pairwise_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "alpha_supported_pairwise_merkle_bad s \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final.
        alpha_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final)"

lemma alpha_header_supported_candidate_unique_if_no_pairwise_merkle_bad:
  assumes no_bad:
    "\<not> alpha_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final"
  shows
    "\<exists>trace_table.
      alpha_header_supported_trace_table_candidates s fr f_fri_roots
        f_final \<subseteq> {trace_table}"
proof (rule ccontr)
  assume not_unique:
    "\<not> (\<exists>trace_table.
      alpha_header_supported_trace_table_candidates s fr f_fri_roots
        f_final \<subseteq> {trace_table})"
  have "alpha_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final"
    using
      alpha_header_supported_trace_table_candidates_not_singleton_imp_pairwise_merkle_bad
        [OF not_unique]
    unfolding alpha_header_supported_pairwise_merkle_bad_def
    by blast
  then show False
    using no_bad by contradiction
qed

lemma alpha_header_supported_candidate_unique_if_no_global_pairwise_merkle_bad:
  assumes no_bad: "\<not> alpha_supported_pairwise_merkle_bad s"
  shows
    "\<exists>trace_table.
      alpha_header_supported_trace_table_candidates s fr f_fri_roots
        f_final \<subseteq> {trace_table}"
proof (rule alpha_header_supported_candidate_unique_if_no_pairwise_merkle_bad)
  show "\<not> alpha_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final"
    using no_bad unfolding alpha_supported_pairwise_merkle_bad_def by blast
qed

lemma accepted_with_bound_tables_common_roots:
  assumes bound1:
      "accepted_with_bound_tables s out trace_table composition_table
        alphas query_idxs"
    and bound2:
      "accepted_with_bound_tables s out trace_table' composition_table'
        alphas' query_idxs'"
  obtains result final_state fr composition_root
  where "out = Some (result, final_state)"
    and "merkle_root_binds_table fr trace_table final_state"
    and "merkle_root_binds_table fr trace_table' final_state"
    and "merkle_root_binds_table composition_root composition_table final_state"
    and "merkle_root_binds_table composition_root composition_table' final_state"
proof -
  from bound1 obtain result1 final_state1 fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    out1: "out = Some (result1, final_state1)"
    and header1:
      "verifier_header_transcript s fr f_fri_roots f_final alphas dg
        composition_fri_roots final rest"
    and trace_bind1:
      "merkle_root_binds_table fr trace_table final_state1"
    and comp_bind1:
      "merkle_root_binds_table (hd composition_fri_roots)
        composition_table final_state1"
    unfolding accepted_with_bound_tables_def by blast
  from bound2 obtain result2 final_state2 fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    out2: "out = Some (result2, final_state2)"
    and header2:
      "verifier_header_transcript s fr' f_fri_roots' f_final' alphas' dg'
        composition_fri_roots' final' rest'"
    and trace_bind2:
      "merkle_root_binds_table fr' trace_table' final_state2"
    and comp_bind2:
      "merkle_root_binds_table (hd composition_fri_roots')
        composition_table' final_state2"
    unfolding accepted_with_bound_tables_def by blast
  have final_state_eq: "final_state2 = final_state1"
    using out1 out2 by simp
  have roots_eq:
    "fr' = fr \<and> composition_fri_roots' = composition_fri_roots"
    using verifier_header_transcript_unique[OF header1 header2] by simp
  have trace_bind2':
    "merkle_root_binds_table fr trace_table' final_state1"
    using trace_bind2 roots_eq final_state_eq by simp
  have comp_bind2':
    "merkle_root_binds_table (hd composition_fri_roots)
      composition_table' final_state1"
    using comp_bind2 roots_eq final_state_eq by simp
  show ?thesis
    by (rule that[OF out1 trace_bind1 trace_bind2' comp_bind1 comp_bind2'])
qed

lemma accepted_with_bound_tables_trace_table_unique_or_hash_collision_bad:
  assumes bound1:
      "accepted_with_bound_tables s out trace_table composition_table
        alphas query_idxs"
    and bound2:
      "accepted_with_bound_tables s out trace_table' composition_table'
        alphas' query_idxs'"
  shows "trace_table = trace_table' \<or> hash_map_output_collision_bad s out"
proof (cases "trace_table = trace_table'")
  case True
  then show ?thesis by simp
next
  case neq: False
  from accepted_with_bound_tables_common_roots[OF bound1 bound2]
  obtain result final_state fr composition_root where
    out: "out = Some (result, final_state)"
    and bind1: "merkle_root_binds_table fr trace_table final_state"
    and bind2: "merkle_root_binds_table fr trace_table' final_state"
    by blast
  have same_len: "length trace_table = length trace_table'"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      accepted_with_bound_tables_shapes(1)[OF bound2]
    by simp
  have nonempty: "trace_table \<noteq> []"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      eval_domain_nontrivial
    by auto
  have "hash_map_output_collision_bad s out"
    by (rule accepted_inconsistent_same_length_merkle_bindings_imp_hash_collision_bad
        [OF out bind1 bind2 same_len nonempty neq])
  then show ?thesis by simp
qed

lemma accepted_with_bound_tables_composition_table_unique_or_hash_collision_bad:
  assumes bound1:
      "accepted_with_bound_tables s out trace_table composition_table
        alphas query_idxs"
    and bound2:
      "accepted_with_bound_tables s out trace_table' composition_table'
        alphas' query_idxs'"
  shows "composition_table = composition_table' \<or>
    hash_map_output_collision_bad s out"
proof (cases "composition_table = composition_table'")
  case True
  then show ?thesis by simp
next
  case neq: False
  from accepted_with_bound_tables_common_roots[OF bound1 bound2]
  obtain result final_state fr composition_root where
    out: "out = Some (result, final_state)"
    and bind1:
      "merkle_root_binds_table composition_root composition_table final_state"
    and bind2:
      "merkle_root_binds_table composition_root composition_table' final_state"
    by blast
  have same_len: "length composition_table = length composition_table'"
    using accepted_with_bound_tables_shapes(2)[OF bound1]
      accepted_with_bound_tables_shapes(2)[OF bound2]
    by simp
  have nonempty: "composition_table \<noteq> []"
    using accepted_with_bound_tables_shapes(2)[OF bound1]
      eval_domain_nontrivial
    by auto
  have "hash_map_output_collision_bad s out"
    by (rule accepted_inconsistent_same_length_merkle_bindings_imp_hash_collision_bad
        [OF out bind1 bind2 same_len nonempty neq])
  then show ?thesis by simp
qed

lemma accepted_with_bound_tables_tables_unique_or_hash_collision_bad:
  assumes bound1:
      "accepted_with_bound_tables s out trace_table composition_table
        alphas query_idxs"
    and bound2:
      "accepted_with_bound_tables s out trace_table' composition_table'
        alphas' query_idxs'"
  shows
    "(trace_table = trace_table' \<and> composition_table = composition_table') \<or>
      hash_map_output_collision_bad s out"
proof -
  have trace_unique:
    "trace_table = trace_table' \<or> hash_map_output_collision_bad s out"
    by (rule accepted_with_bound_tables_trace_table_unique_or_hash_collision_bad
        [OF bound1 bound2])
  have comp_unique:
    "composition_table = composition_table' \<or>
      hash_map_output_collision_bad s out"
    by (rule accepted_with_bound_tables_composition_table_unique_or_hash_collision_bad
        [OF bound1 bound2])
  show ?thesis
    using trace_unique comp_unique by blast
qed

lemma accepted_with_bound_tables_trace_table_unique_if_no_hash_collision_bad:
  assumes no_collision: "\<not> hash_map_output_collision_bad s out"
    and bound1:
      "accepted_with_bound_tables s out trace_table composition_table
        alphas query_idxs"
    and bound2:
      "accepted_with_bound_tables s out trace_table' composition_table'
        alphas' query_idxs'"
  shows "trace_table = trace_table'"
  using accepted_with_bound_tables_trace_table_unique_or_hash_collision_bad
      [OF bound1 bound2] no_collision
  by blast

lemma accepted_with_bound_tables_composition_table_unique_if_no_hash_collision_bad:
  assumes no_collision: "\<not> hash_map_output_collision_bad s out"
    and bound1:
      "accepted_with_bound_tables s out trace_table composition_table
        alphas query_idxs"
    and bound2:
      "accepted_with_bound_tables s out trace_table' composition_table'
        alphas' query_idxs'"
  shows "composition_table = composition_table'"
  using accepted_with_bound_tables_composition_table_unique_or_hash_collision_bad
      [OF bound1 bound2] no_collision
  by blast

definition accepted_bound_table_ambiguity_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "accepted_bound_table_ambiguity_bad s out \<longleftrightarrow>
      (\<exists>trace_table composition_table alphas query_idxs
          trace_table' composition_table' alphas' query_idxs'.
        accepted_with_bound_tables s out trace_table composition_table
          alphas query_idxs \<and>
        accepted_with_bound_tables s out trace_table' composition_table'
          alphas' query_idxs' \<and>
        (trace_table \<noteq> trace_table' \<or>
         composition_table \<noteq> composition_table'))"

lemma accepted_bound_table_ambiguity_bad_imp_hash_map_output_collision_bad:
  assumes ambiguity: "accepted_bound_table_ambiguity_bad s out"
  shows "hash_map_output_collision_bad s out"
proof -
  from ambiguity obtain trace_table composition_table alphas query_idxs
      trace_table' composition_table' alphas' query_idxs' where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table
        alphas query_idxs"
    and bound':
      "accepted_with_bound_tables s out trace_table' composition_table'
        alphas' query_idxs'"
    and distinct:
      "trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table'"
    unfolding accepted_bound_table_ambiguity_bad_def by blast
  have
    "(trace_table = trace_table' \<and>
      composition_table = composition_table') \<or>
      hash_map_output_collision_bad s out"
    by (rule accepted_with_bound_tables_tables_unique_or_hash_collision_bad
        [OF bound bound'])
  then show ?thesis
    using distinct by blast
qed

lemma accepted_bound_table_ambiguity_bad_mono_hash_map_output_collision_bad:
  "wp_event verify_monad (accepted_bound_table_ambiguity_bad s) s \<le>
    wp_event verify_monad (hash_map_output_collision_bad s) s"
  by (rule wp_event_mono)
    (rule
      accepted_bound_table_ambiguity_bad_imp_hash_map_output_collision_bad)

end

end
