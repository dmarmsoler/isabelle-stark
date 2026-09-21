(*  Title:      Stark/Soundness_FRI_First_Root_RO_State_Relation.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_State_Relation
  imports
    Soundness_FRI_First_Root_RO_Query_Phase_Prequery
    Staged_Security_Experiment_RO_Query_Round_Replay
begin

text \<open>
  Map-indexed support for the first-root query relation.  This layer separates
  the exact query-index output fiber from later transcript/Merkle map drift.
\<close>

context soundness
begin

lemma merkle_path_bound_cong_hash_map:
  assumes map_eq: "HashMap s = HashMap t"
  shows "merkle_path_bound rt len idx v path s =
    merkle_path_bound rt len idx v path t"
  using map_eq
  by (induction path arbitrary: rt len idx v) auto

lemma authenticated_opening_in_cong_hash_map:
  assumes map_eq: "HashMap s = HashMap t"
  shows "authenticated_opening_in s opening = authenticated_opening_in t opening"
  unfolding authenticated_opening_in_def
  using merkle_path_bound_cong_hash_map[OF map_eq]
  by simp

lemma authenticated_value_at_cong_hash_map:
  assumes map_eq: "HashMap s = HashMap t"
  shows "authenticated_value_at s r len i v =
    authenticated_value_at t r len i v"
  unfolding authenticated_value_at_def
  using authenticated_opening_in_cong_hash_map[OF map_eq]
  by blast

lemma conceptual_opening_value_cong_hash_map:
  assumes map_eq: "HashMap s = HashMap t"
  shows "conceptual_opening_value s r len i =
    conceptual_opening_value t r len i"
proof -
  have "(\<lambda>v. authenticated_value_at s r len i v) =
      (\<lambda>v. authenticated_value_at t r len i v)"
    by (rule ext)
      (rule authenticated_value_at_cong_hash_map[OF map_eq])
  then show ?thesis
    unfolding conceptual_opening_value_def by simp
qed

lemma conceptual_table_cong_hash_map:
  assumes map_eq: "HashMap s = HashMap t"
  shows "conceptual_table s r len = conceptual_table t r len"
  unfolding conceptual_table_def
  using conceptual_opening_value_cong_hash_map[OF map_eq]
  by simp


definition channel_for_hash_map
  :: "('f protocol_hash_input, 'f) fmap \<Rightarrow> 'f protocol_channel"
where
  "channel_for_hash_map M = adversary_initial_state\<lparr>HashMap := M\<rparr>"

lemma ro_absorb_lookup_chain_query_index_update[simp]:
  "ro_absorb_lookup_chain
      (channel_for_hash_map (fmupd (QueryIndexChallenge c st) y M))
      start messages final =
    ro_absorb_lookup_chain (channel_for_hash_map M)
      start messages final"
  unfolding channel_for_hash_map_def
  by (induction messages arbitrary: start) auto

lemma merkle_path_bound_query_index_update[simp]:
  "merkle_path_bound rt len idx v path
      (channel_for_hash_map (fmupd (QueryIndexChallenge c st) y M)) =
    merkle_path_bound rt len idx v path (channel_for_hash_map M)"
  unfolding channel_for_hash_map_def
  by (induction path arbitrary: rt len idx v) auto

lemma authenticated_opening_in_query_index_update[simp]:
  "authenticated_opening_in
      (channel_for_hash_map (fmupd (QueryIndexChallenge c st) y M)) opening =
    authenticated_opening_in (channel_for_hash_map M) opening"
  unfolding authenticated_opening_in_def by simp

lemma authenticated_value_at_query_index_update[simp]:
  "authenticated_value_at
      (channel_for_hash_map (fmupd (QueryIndexChallenge c st) y M))
      r len i v =
    authenticated_value_at (channel_for_hash_map M) r len i v"
  unfolding authenticated_value_at_def by simp

lemma conceptual_opening_value_query_index_update[simp]:
  "conceptual_opening_value
      (channel_for_hash_map (fmupd (QueryIndexChallenge c st) y M))
      r len i =
    conceptual_opening_value (channel_for_hash_map M) r len i"
  unfolding conceptual_opening_value_def
  by (rule arg_cong[where f=The])
    (rule ext, simp)

lemma conceptual_table_query_index_update[simp]:
  "conceptual_table
      (channel_for_hash_map (fmupd (QueryIndexChallenge c st) y M))
      r len =
    conceptual_table (channel_for_hash_map M) r len"
  unfolding conceptual_table_def by simp


definition first_root_absorbed_query_relation
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
        'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "first_root_absorbed_query_relation M x y \<longleftrightarrow>
    (let s = channel_for_hash_map M in
      \<not> hash_map_output_collision s \<and>
      PState adversary_initial_state \<notin> hash_map_output_values s \<and>
      (\<exists>fr first_root rest prefix_hash final raws j.
        ro_absorb_lookup_chain s (PState adversary_initial_state)
          [fr, first_root] prefix_hash \<and>
        ro_absorb_lookup_chain s prefix_hash rest final \<and>
        trace_table_low_degree
          (first_trace_fri_root_prefix_trace_table
            (fr, [], first_root) s) \<and>
        trace_table_low_degree
          (first_trace_fri_root_prefix_first_table
            (fr, [], first_root) s) \<and>
        first_trace_fri_root_prefix_trace_table
            (fr, [], first_root) s \<noteq>
          first_trace_fri_root_prefix_first_table
            (fr, [], first_root) s \<and>
        length raws = rounds \<and>
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          first_trace_fri_root_prefix_base_agreement_query_lists
            (fr, [], first_root) s \<and>
        j < rounds \<and>
        x = QueryIndexChallenge j final \<and>
        y = raws ! j))"

lemma first_root_absorbed_query_relationD:
  assumes rel: "first_root_absorbed_query_relation M x y"
  obtains fr first_root rest prefix_hash final raws j where
    "\<not> hash_map_output_collision (channel_for_hash_map M)"
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state) [fr, first_root] prefix_hash"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      prefix_hash rest final"
    "trace_table_low_degree
      (first_trace_fri_root_prefix_trace_table
        (fr, [], first_root) (channel_for_hash_map M))"
    "trace_table_low_degree
      (first_trace_fri_root_prefix_first_table
        (fr, [], first_root) (channel_for_hash_map M))"
    "first_trace_fri_root_prefix_trace_table
        (fr, [], first_root) (channel_for_hash_map M) \<noteq>
      first_trace_fri_root_prefix_first_table
        (fr, [], first_root) (channel_for_hash_map M)"
    "length raws = rounds"
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
      first_trace_fri_root_prefix_base_agreement_query_lists
        (fr, [], first_root) (channel_for_hash_map M)"
    "j < rounds"
    "x = QueryIndexChallenge j final"
    "y = raws ! j"
  using rel
  unfolding first_root_absorbed_query_relation_def Let_def
  by blast


lemma first_root_absorbed_query_relation_direct_fiber_card_bound:
  "card {y.
      hash_state_relation_direct_activation
        first_root_absorbed_query_relation M x y}
    \<le> rounds * query_raw_preimage_card_envelope clength"
proof (cases "{y.
    hash_state_relation_direct_activation
      first_root_absorbed_query_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
    "hash_state_relation_direct_activation
      first_root_absorbed_query_relation M x y0"
    by blast
  have rel0:
    "first_root_absorbed_query_relation (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from first_root_absorbed_query_relationD[OF rel0]
  obtain fr0 first0 rest0 prefix0 final0 raws0 j0 where
    clean0:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y0 M))"
    and no_initial0:
      "PState adversary_initial_state \<notin>
        hash_map_output_values
          (channel_for_hash_map (fmupd x y0 M))"
    and prefix_chain0:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state) [fr0, first0] prefix0"
    and rest_chain0:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        prefix0 rest0 final0"
    and trace_low0:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_trace_table
          (fr0, [], first0)
          (channel_for_hash_map (fmupd x y0 M)))"
    and first_low0:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table
          (fr0, [], first0)
          (channel_for_hash_map (fmupd x y0 M)))"
    and distinct0:
      "first_trace_fri_root_prefix_trace_table
          (fr0, [], first0)
          (channel_for_hash_map (fmupd x y0 M)) \<noteq>
        first_trace_fri_root_prefix_first_table
          (fr0, [], first0)
          (channel_for_hash_map (fmupd x y0 M))"
    and raws_len0: "length raws0 = rounds"
    and raws_in0:
      "map (\<lambda>raw. index (to_nat raw)) raws0 \<in>
        first_trace_fri_root_prefix_base_agreement_query_lists
          (fr0, [], first0)
          (channel_for_hash_map (fmupd x y0 M))"
    and j0_bound: "j0 < rounds"
    and x0: "x = QueryIndexChallenge j0 final0"
    and y0_eq: "y0 = raws0 ! j0"
    .
  let ?Q0 =
    "first_trace_fri_root_prefix_base_agreement_query_lists
      (fr0, [], first0) (channel_for_hash_map (fmupd x y0 M))"
  have subset:
    "{y.
      hash_state_relation_direct_activation
        first_root_absorbed_query_relation M x y}
      \<subseteq> query_index_raw_list_position_values ?Q0 j0"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          first_root_absorbed_query_relation M x y}"
    have rely:
      "first_root_absorbed_query_relation (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from first_root_absorbed_query_relationD[OF rely]
    obtain fr first_root rest prefix_hash final raws j where
      clean_y:
        "\<not> hash_map_output_collision
          (channel_for_hash_map (fmupd x y M))"
      and no_initial_y:
        "PState adversary_initial_state \<notin>
          hash_map_output_values
            (channel_for_hash_map (fmupd x y M))"
      and prefix_chain:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y M))
          (PState adversary_initial_state) [fr, first_root] prefix_hash"
      and rest_chain:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y M))
          prefix_hash rest final"
      and trace_low_y:
        "trace_table_low_degree
          (first_trace_fri_root_prefix_trace_table
            (fr, [], first_root)
            (channel_for_hash_map (fmupd x y M)))"
      and first_low_y:
        "trace_table_low_degree
          (first_trace_fri_root_prefix_first_table
            (fr, [], first_root)
            (channel_for_hash_map (fmupd x y M)))"
      and distinct_y:
        "first_trace_fri_root_prefix_trace_table
            (fr, [], first_root)
            (channel_for_hash_map (fmupd x y M)) \<noteq>
          first_trace_fri_root_prefix_first_table
            (fr, [], first_root)
            (channel_for_hash_map (fmupd x y M))"
      and raws_len: "length raws = rounds"
      and raws_in:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          first_trace_fri_root_prefix_base_agreement_query_lists
            (fr, [], first_root)
            (channel_for_hash_map (fmupd x y M))"
      and j_bound: "j < rounds"
      and x_eq: "x = QueryIndexChallenge j final"
      and y_eq: "y = raws ! j"
      .
    have j_eq: "j = j0"
      and final_eq: "final = final0"
      using x_eq x0 by simp_all
    have full0:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state)
        ([fr0, first0] @ rest0) final0"
      by (rule ro_absorb_lookup_chain_append[OF prefix_chain0 rest_chain0])
    have prefix_chain_base:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state) [fr, first_root] prefix_hash"
      using prefix_chain
      unfolding x0
      by (simp only: ro_absorb_lookup_chain_query_index_update)
    have prefix_chain_in0:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state) [fr, first_root] prefix_hash"
      using prefix_chain_base
      unfolding x0
      by (simp only: ro_absorb_lookup_chain_query_index_update)
    have rest_chain_base:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        prefix_hash rest final0"
      using rest_chain final_eq
      unfolding x0
      by (simp only: ro_absorb_lookup_chain_query_index_update)
    have rest_chain_in0:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        prefix_hash rest final0"
      using rest_chain_base
      unfolding x0
      by (simp only: ro_absorb_lookup_chain_query_index_update)
    have full:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state)
        ([fr, first_root] @ rest) final0"
      by (rule ro_absorb_lookup_chain_append[
            OF prefix_chain_in0 rest_chain_in0])
    have messages_eq:
      "[fr, first_root] @ rest = [fr0, first0] @ rest0"
      by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
            OF clean0 no_initial0 full full0])
    have fr_eq: "fr = fr0"
      and first_eq: "first_root = first0"
      using messages_eq by simp_all
    have Q_eq:
      "first_trace_fri_root_prefix_base_agreement_query_lists
          (fr, [], first_root)
          (channel_for_hash_map (fmupd x y M)) = ?Q0"
      using fr_eq first_eq
      unfolding x0
        first_trace_fri_root_prefix_base_agreement_query_lists_def
        first_trace_fri_root_prefix_trace_table_def
        first_trace_fri_root_prefix_first_table_def
      by simp
    have raws_preimage:
      "raws \<in> query_index_raw_list_preimage ?Q0"
      unfolding query_index_raw_list_preimage_def
      using raws_len raws_in Q_eq by simp
    show "y \<in> query_index_raw_list_position_values ?Q0 j0"
      unfolding query_index_raw_list_position_values_def
      using raws_preimage y_eq j_eq j0_bound by blast
  qed
  have finite_Q0:
    "finite (query_index_raw_list_position_values ?Q0 j0)"
    by simp
  have card_le:
    "card {y.
      hash_state_relation_direct_activation
        first_root_absorbed_query_relation M x y}
      \<le> card (query_index_raw_list_position_values ?Q0 j0)"
    by (rule card_mono[OF finite_Q0 subset])
  have position_le:
    "card (query_index_raw_list_position_values ?Q0 j0)
      \<le> query_raw_preimage_card_envelope clength"
  proof -
    let ?A =
      "trace_table_base_agreement_indices
        (first_trace_fri_root_prefix_trace_table
          (fr0, [], first0)
          (channel_for_hash_map (fmupd x y0 M)))
        (first_trace_fri_root_prefix_first_table
          (fr0, [], first0)
          (channel_for_hash_map (fmupd x y0 M)))"
    have base:
      "card (query_index_raw_list_position_values ?Q0 j0)
        \<le> query_raw_preimage_card_envelope (card ?A)"
      unfolding first_trace_fri_root_prefix_base_agreement_query_lists_def
      by (rule
          card_query_index_raw_list_position_values_base_agreement_le[
            OF j0_bound])
    have agreement: "card ?A \<le> clength"
      using trace_table_base_agreement_indices_card_bound[
        OF trace_low0 first_low0 distinct0]
      by simp
    have envelope:
      "query_raw_preimage_card_envelope (card ?A) \<le>
        query_raw_preimage_card_envelope clength"
      by (rule query_raw_preimage_card_envelope_mono[OF agreement])
    show ?thesis
      by (rule order_trans[OF base envelope])
  qed
  have
    "card {y.
      hash_state_relation_direct_activation
        first_root_absorbed_query_relation M x y}
      \<le> query_raw_preimage_card_envelope clength"
    by (rule order_trans[OF card_le position_le])
  also have "... \<le> rounds * query_raw_preimage_card_envelope clength"
    using j0_bound by simp
  finally show ?thesis .
qed

definition transcript_absorb_input_values
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow> 'f set"
where
  "transcript_absorb_input_values M =
    {p. \<exists>msg out. fmlookup M (TranscriptAbsorb p msg) = Some out}"

definition transcript_absorb_message_values
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow> 'f set"
where
  "transcript_absorb_message_values M =
    {msg. \<exists>p out. fmlookup M (TranscriptAbsorb p msg) = Some out}"

definition query_index_state_values
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow> 'f set"
where
  "query_index_state_values M =
    {st. \<exists>c out. fmlookup M (QueryIndexChallenge c st) = Some out}"

definition hash_input_component_values
  :: "'f protocol_hash_input \<Rightarrow> 'f set"
where
  "hash_input_component_values x =
    (case x of
      TranscriptAbsorb p msg \<Rightarrow> {p, msg}
    | MerkleNode l r \<Rightarrow> {l, r}
    | _ \<Rightarrow> {})"

definition first_root_relation_drift_targets
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f set"
where
  "first_root_relation_drift_targets M x =
    transcript_absorb_input_values M \<union>
    transcript_absorb_message_values M \<union>
    query_index_state_values M \<union>
    hash_map_merkle_child_values (channel_for_hash_map M) \<union>
    hash_input_component_values x"

lemma transcript_absorb_input_values_subset_image:
  "transcript_absorb_input_values M \<subseteq>
    Set.image
      (\<lambda>k. case k of TranscriptAbsorb p msg \<Rightarrow> p | _ \<Rightarrow> 0)
      (fmdom' M)"
  unfolding transcript_absorb_input_values_def
proof
  fix p
  assume "p \<in> {p. \<exists>msg out.
    fmlookup M (TranscriptAbsorb p msg) = Some out}"
  then obtain msg out where
    lookup: "fmlookup M (TranscriptAbsorb p msg) = Some out"
    by blast
  have dom: "TranscriptAbsorb p msg \<in> fmdom' M"
    using lookup by (simp add: fmlookup_dom'_iff)
  show "p \<in> Set.image
    (\<lambda>k. case k of TranscriptAbsorb p msg \<Rightarrow> p | _ \<Rightarrow> 0)
    (fmdom' M)"
    by (rule image_eqI[OF _ dom]) simp
qed

lemma transcript_absorb_message_values_subset_image:
  "transcript_absorb_message_values M \<subseteq>
    Set.image
      (\<lambda>k. case k of TranscriptAbsorb p msg \<Rightarrow> msg | _ \<Rightarrow> 0)
      (fmdom' M)"
  unfolding transcript_absorb_message_values_def
proof
  fix msg
  assume "msg \<in> {msg. \<exists>p out.
    fmlookup M (TranscriptAbsorb p msg) = Some out}"
  then obtain p out where
    lookup: "fmlookup M (TranscriptAbsorb p msg) = Some out"
    by blast
  have dom: "TranscriptAbsorb p msg \<in> fmdom' M"
    using lookup by (simp add: fmlookup_dom'_iff)
  show "msg \<in> Set.image
    (\<lambda>k. case k of TranscriptAbsorb p msg \<Rightarrow> msg | _ \<Rightarrow> 0)
    (fmdom' M)"
    by (rule image_eqI[OF _ dom]) simp
qed

lemma query_index_state_values_subset_image:
  "query_index_state_values M \<subseteq>
    Set.image
      (\<lambda>k. case k of QueryIndexChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
      (fmdom' M)"
  unfolding query_index_state_values_def
proof
  fix st
  assume "st \<in> {st. \<exists>c out.
    fmlookup M (QueryIndexChallenge c st) = Some out}"
  then obtain c out where
    lookup: "fmlookup M (QueryIndexChallenge c st) = Some out"
    by blast
  have dom: "QueryIndexChallenge c st \<in> fmdom' M"
    using lookup by (simp add: fmlookup_dom'_iff)
  show "st \<in> Set.image
    (\<lambda>k. case k of QueryIndexChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
    (fmdom' M)"
    by (rule image_eqI[OF _ dom]) simp
qed

lemma finite_transcript_absorb_input_values[simp]:
  "finite (transcript_absorb_input_values M)"
  by (rule finite_subset[OF transcript_absorb_input_values_subset_image])
    simp

lemma finite_transcript_absorb_message_values[simp]:
  "finite (transcript_absorb_message_values M)"
  by (rule finite_subset[OF transcript_absorb_message_values_subset_image])
    simp

lemma finite_query_index_state_values[simp]:
  "finite (query_index_state_values M)"
  by (rule finite_subset[OF query_index_state_values_subset_image])
    simp

lemma finite_fmdom_protocol_hash_input[simp]:
  "finite (fmdom' (M :: ('f protocol_hash_input, 'f) fmap))"
  by (rule finite_fmdom')

lemma card_transcript_absorb_input_values_le:
  "card (transcript_absorb_input_values M) \<le> card (fmdom' M)"
proof -
  have "card (transcript_absorb_input_values M) \<le>
      card (Set.image
        (\<lambda>k. case k of TranscriptAbsorb p msg \<Rightarrow> p | _ \<Rightarrow> 0)
        (fmdom' M))"
    by (rule card_mono)
      (simp_all add: transcript_absorb_input_values_subset_image)
  also have "... \<le> card (fmdom' M)"
    by (rule card_image_le) simp
  finally show ?thesis .
qed

lemma card_transcript_absorb_message_values_le:
  "card (transcript_absorb_message_values M) \<le> card (fmdom' M)"
proof -
  have "card (transcript_absorb_message_values M) \<le>
      card (Set.image
        (\<lambda>k. case k of TranscriptAbsorb p msg \<Rightarrow> msg | _ \<Rightarrow> 0)
        (fmdom' M))"
    by (rule card_mono)
      (simp_all add: transcript_absorb_message_values_subset_image)
  also have "... \<le> card (fmdom' M)"
    by (rule card_image_le) simp
  finally show ?thesis .
qed

lemma card_query_index_state_values_le:
  "card (query_index_state_values M) \<le> card (fmdom' M)"
proof -
  have "card (query_index_state_values M) \<le>
      card (Set.image
        (\<lambda>k. case k of QueryIndexChallenge c st \<Rightarrow> st | _ \<Rightarrow> 0)
        (fmdom' M))"
    by (rule card_mono)
      (simp_all add: query_index_state_values_subset_image)
  also have "... \<le> card (fmdom' M)"
    by (rule card_image_le) simp
  finally show ?thesis .
qed

lemma finite_hash_input_component_values[simp]:
  "finite (hash_input_component_values x)"
  unfolding hash_input_component_values_def
  by (cases x) simp_all

lemma card_hash_input_component_values_le:
  "card (hash_input_component_values x) \<le> 2"
  unfolding hash_input_component_values_def
  by (cases x) (simp_all add: card_insert_if)

lemma finite_first_root_relation_drift_targets[simp]:
  "finite (first_root_relation_drift_targets M x)"
  unfolding first_root_relation_drift_targets_def by simp

lemma card_first_root_relation_drift_targets_le:
  "card (first_root_relation_drift_targets M x)
    \<le> 5 * card (fmdom' M) + 2"
proof -
  let ?A = "transcript_absorb_input_values M"
  let ?B = "transcript_absorb_message_values M"
  let ?C = "query_index_state_values M"
  let ?D = "hash_map_merkle_child_values (channel_for_hash_map M)"
  let ?E = "hash_input_component_values x"
  have ab: "card (?A \<union> ?B) \<le> card ?A + card ?B"
    by (rule card_Un_le)
  have abc: "card (?A \<union> ?B \<union> ?C) \<le>
      card ?A + card ?B + card ?C"
    by (rule order_trans[OF card_Un_le])
      (use ab in simp)
  have abcd: "card (?A \<union> ?B \<union> ?C \<union> ?D) \<le>
      card ?A + card ?B + card ?C + card ?D"
    by (rule order_trans[OF card_Un_le])
      (use abc in simp)
  have union_le:
    "card (first_root_relation_drift_targets M x) \<le>
      card ?A + card ?B + card ?C + card ?D + card ?E"
    unfolding first_root_relation_drift_targets_def
    by (rule order_trans[OF card_Un_le])
      (use abcd in simp)
  have child_le: "card ?D \<le> 2 * card (fmdom' M)"
    using card_hash_map_merkle_child_values_le[
      of "channel_for_hash_map M"]
    unfolding channel_for_hash_map_def by simp
  show ?thesis
    by (rule order_trans[OF union_le])
      (use card_transcript_absorb_input_values_le[of M]
        card_transcript_absorb_message_values_le[of M]
        card_query_index_state_values_le[of M]
        child_le card_hash_input_component_values_le[of x]
        in linarith)
qed


lemma transcript_absorb_lookup_input_value:
  assumes "fmlookup M (TranscriptAbsorb p msg) = Some out"
  shows "p \<in> transcript_absorb_input_values M"
  using assms unfolding transcript_absorb_input_values_def by blast

lemma transcript_absorb_lookup_message_value:
  assumes "fmlookup M (TranscriptAbsorb p msg) = Some out"
  shows "msg \<in> transcript_absorb_message_values M"
  using assms unfolding transcript_absorb_message_values_def by blast

lemma query_index_lookup_state_value:
  assumes "fmlookup M (QueryIndexChallenge c st) = Some out"
  shows "st \<in> query_index_state_values M"
  using assms unfolding query_index_state_values_def by blast

lemma channel_for_hash_map_fresh_update_extends:
  assumes fresh: "fmlookup M x = None"
  shows "channel_for_hash_map M \<le>
    channel_for_hash_map (fmupd x y M)"
  using fresh
  unfolding channel_for_hash_map_def less_eq_hash_ext_def less_eq_fmap_def
  by simp

lemma ro_absorb_lookup_chain_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and chain:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        start messages final"
    and final_target: "final \<in> query_index_state_values M"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      start messages final"
  using chain
proof (induction messages arbitrary: start)
  case Nil
  then show ?case by simp
next
  case (Cons msg messages)
  from Cons.prems obtain nxt where
    lookup:
      "fmlookup (fmupd x y M)
        (TranscriptAbsorb start msg) = Some nxt"
    and tail:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        nxt messages final"
    unfolding channel_for_hash_map_def by auto
  have key_neq: "TranscriptAbsorb start msg \<noteq> x"
  proof
    assume key_eq: "TranscriptAbsorb start msg = x"
    have nxt_eq: "nxt = y"
      using lookup key_eq by simp
    show False
    proof (cases messages)
      case Nil
      have final_eq: "final = y"
        using tail nxt_eq Nil by simp
      have "y \<in> first_root_relation_drift_targets M x"
        using final_target final_eq
        unfolding first_root_relation_drift_targets_def by blast
      then show False using no_target by contradiction
    next
      case (Cons next_msg rest)
      from tail[unfolded Cons] obtain after where
        next_lookup:
          "fmlookup (fmupd x y M)
            (TranscriptAbsorb nxt next_msg) = Some after"
        unfolding channel_for_hash_map_def by auto
      show False
      proof (cases "TranscriptAbsorb nxt next_msg = x")
        case True
        have x_eq: "x = TranscriptAbsorb nxt next_msg"
          using True by simp
        have "y \<in> hash_input_component_values x"
          using x_eq nxt_eq
          unfolding hash_input_component_values_def by simp
        then have "y \<in> first_root_relation_drift_targets M x"
          unfolding first_root_relation_drift_targets_def by blast
        then show False using no_target by contradiction
      next
        case False
        have old_lookup:
          "fmlookup M (TranscriptAbsorb nxt next_msg) = Some after"
          using next_lookup False by simp
        have "y \<in> transcript_absorb_input_values M"
          using transcript_absorb_lookup_input_value[OF old_lookup]
            nxt_eq by simp
        then have "y \<in> first_root_relation_drift_targets M x"
          unfolding first_root_relation_drift_targets_def by blast
        then show False using no_target by contradiction
      qed
    qed
  qed
  have lookup_old:
    "fmlookup M (TranscriptAbsorb start msg) = Some nxt"
    using lookup key_neq by simp
  have tail_old:
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      nxt messages final"
    by (rule Cons.IH[OF tail])
  show ?case
    using lookup_old tail_old
    unfolding channel_for_hash_map_def by auto
qed

lemma ro_absorb_lookup_chain_messages_subset:
  assumes chain:
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      start messages final"
  shows "set messages \<subseteq> transcript_absorb_message_values M"
  using chain
proof (induction messages arbitrary: start)
  case Nil
  then show ?case by simp
next
  case (Cons msg messages)
  from Cons.prems obtain nxt where
    lookup: "fmlookup M (TranscriptAbsorb start msg) = Some nxt"
    and tail:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        nxt messages final"
    unfolding channel_for_hash_map_def by auto
  have msg_in: "msg \<in> transcript_absorb_message_values M"
    by (rule transcript_absorb_lookup_message_value[OF lookup])
  have tail_in:
    "set messages \<subseteq> transcript_absorb_message_values M"
    by (rule Cons.IH[OF tail])
  show ?case using msg_in tail_in by simp
qed

lemma merkle_path_bound_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and bound:
      "merkle_path_bound rt len idx v path
        (channel_for_hash_map (fmupd x y M))"
    and root_target: "rt \<in> transcript_absorb_message_values M"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows
    "merkle_path_bound rt len idx v path
      (channel_for_hash_map M)"
proof -
  have ext:
    "channel_for_hash_map M \<le>
      channel_for_hash_map (fmupd x y M)"
    by (rule channel_for_hash_map_fresh_update_extends[OF fresh])
  from merkle_path_bound_pullback_or_prefix_target_hit[OF ext bound]
  show ?thesis
  proof
    assume old_bound:
      "merkle_path_bound rt len idx v path
        (channel_for_hash_map M)"
    then show ?thesis .
  next
    assume hit:
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {rt} (channel_for_hash_map M))
        (channel_for_hash_map M)
        (channel_for_hash_map (fmupd x y M))"
    have update_eq:
      "channel_for_hash_map (fmupd x y M) =
        (channel_for_hash_map M)\<lparr>
          HashMap := fmupd x y (HashMap (channel_for_hash_map M))\<rparr>"
      unfolding channel_for_hash_map_def by simp
    have fresh':
      "fmlookup (HashMap (channel_for_hash_map M)) x = None"
      using fresh unfolding channel_for_hash_map_def by simp
    have y_hit:
      "y \<in> merkle_prefix_path_targets {rt} (channel_for_hash_map M)"
      using hit[unfolded update_eq] fresh'
      by (simp add: hash_map_new_output_hit_after_update)
    have y_target: "y \<in> first_root_relation_drift_targets M x"
      using y_hit root_target
      unfolding merkle_prefix_path_targets_def
        first_root_relation_drift_targets_def
      by blast
    then show ?thesis using no_target by contradiction
  qed
qed


lemma authenticated_opening_in_fresh_update_iff:
  assumes fresh: "fmlookup M x = None"
    and root_target:
      "opening_root opening \<in> transcript_absorb_message_values M"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows
    "authenticated_opening_in
        (channel_for_hash_map (fmupd x y M)) opening =
      authenticated_opening_in (channel_for_hash_map M) opening"
proof
  assume auth:
    "authenticated_opening_in
      (channel_for_hash_map (fmupd x y M)) opening"
  have bound:
    "merkle_path_bound
      (opening_root opening)
      (opening_length opening)
      (opening_index opening)
      (opening_value opening)
      (opening_path opening)
      (channel_for_hash_map (fmupd x y M))"
    using auth unfolding authenticated_opening_in_def by simp
  have old_bound:
    "merkle_path_bound
      (opening_root opening)
      (opening_length opening)
      (opening_index opening)
      (opening_value opening)
      (opening_path opening)
      (channel_for_hash_map M)"
    by (rule merkle_path_bound_fresh_update_pullback[
          OF fresh bound root_target no_target])
  show "authenticated_opening_in (channel_for_hash_map M) opening"
    using auth old_bound unfolding authenticated_opening_in_def by simp
next
  assume auth: "authenticated_opening_in (channel_for_hash_map M) opening"
  have ext:
    "channel_for_hash_map M \<le>
      channel_for_hash_map (fmupd x y M)"
    by (rule channel_for_hash_map_fresh_update_extends[OF fresh])
  show "authenticated_opening_in
      (channel_for_hash_map (fmupd x y M)) opening"
    by (rule authenticated_opening_in_mono[OF auth ext])
qed

lemma authenticated_value_at_fresh_update_iff:
  assumes fresh: "fmlookup M x = None"
    and root_target: "r \<in> transcript_absorb_message_values M"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows
    "authenticated_value_at
        (channel_for_hash_map (fmupd x y M)) r len i v =
      authenticated_value_at (channel_for_hash_map M) r len i v"
  unfolding authenticated_value_at_def
  using authenticated_opening_in_fresh_update_iff[
    OF fresh _ no_target]
    root_target
  by blast

lemma conceptual_opening_value_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and root_target: "r \<in> transcript_absorb_message_values M"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows
    "conceptual_opening_value
        (channel_for_hash_map (fmupd x y M)) r len i =
      conceptual_opening_value (channel_for_hash_map M) r len i"
proof -
  have pred_eq:
    "(\<lambda>v. authenticated_value_at
        (channel_for_hash_map (fmupd x y M)) r len i v) =
      (\<lambda>v. authenticated_value_at
        (channel_for_hash_map M) r len i v)"
    by (rule ext)
      (rule authenticated_value_at_fresh_update_iff[
        OF fresh root_target no_target])
  show ?thesis
    unfolding conceptual_opening_value_def
    using pred_eq by simp
qed

lemma conceptual_table_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and root_target: "r \<in> transcript_absorb_message_values M"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows
    "conceptual_table
        (channel_for_hash_map (fmupd x y M)) r len =
      conceptual_table (channel_for_hash_map M) r len"
  unfolding conceptual_table_def
  using conceptual_opening_value_fresh_update[
    OF fresh root_target no_target]
  by simp


lemma ro_absorb_lookup_chain_append_split:
  assumes
    "ro_absorb_lookup_chain s start (xs @ ys) final"
  shows
    "\<exists>mid.
      ro_absorb_lookup_chain s start xs mid \<and>
      ro_absorb_lookup_chain s mid ys final"
  using assms
proof (induction xs arbitrary: start)
  case Nil
  then show ?case by auto
next
  case (Cons msg messages)
  from Cons.prems obtain nxt where
    lookup:
      "fmlookup (HashMap s) (TranscriptAbsorb start msg) = Some nxt"
    and tail:
      "ro_absorb_lookup_chain s nxt (messages @ ys) final"
    by auto
  from Cons.IH[OF tail] obtain mid where
    first: "ro_absorb_lookup_chain s nxt messages mid"
    and second: "ro_absorb_lookup_chain s mid ys final"
    by blast
  have head:
    "ro_absorb_lookup_chain s start (msg # messages) mid"
    using lookup first by auto
  show ?case using head second by blast
qed

lemma first_root_absorbed_query_relation_fresh_update_pullback:
  assumes fresh: "fmlookup M x = None"
    and key_neq: "k \<noteq> x"
    and active_lookup: "fmlookup (fmupd x y M) k = Some z"
    and rel:
      "first_root_absorbed_query_relation (fmupd x y M) k z"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows "first_root_absorbed_query_relation M k z"
proof -
  from first_root_absorbed_query_relationD[OF rel]
  obtain fr first_root rest prefix_hash final raws j where
    clean_new:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
    and no_initial_new:
      "PState adversary_initial_state \<notin>
        hash_map_output_values
          (channel_for_hash_map (fmupd x y M))"
    and prefix_chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        (PState adversary_initial_state) [fr, first_root] prefix_hash"
    and rest_chain_new:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y M))
        prefix_hash rest final"
    and trace_low_new:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_trace_table
          (fr, [], first_root)
          (channel_for_hash_map (fmupd x y M)))"
    and first_low_new:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table
          (fr, [], first_root)
          (channel_for_hash_map (fmupd x y M)))"
    and distinct_new:
      "first_trace_fri_root_prefix_trace_table
          (fr, [], first_root)
          (channel_for_hash_map (fmupd x y M)) \<noteq>
        first_trace_fri_root_prefix_first_table
          (fr, [], first_root)
          (channel_for_hash_map (fmupd x y M))"
    and raws_len: "length raws = rounds"
    and raws_in_new:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        first_trace_fri_root_prefix_base_agreement_query_lists
          (fr, [], first_root)
          (channel_for_hash_map (fmupd x y M))"
    and j_bound: "j < rounds"
    and k_eq: "k = QueryIndexChallenge j final"
    and z_eq: "z = raws ! j"
    .
  have old_lookup: "fmlookup M k = Some z"
    using active_lookup key_neq by simp
  have final_target: "final \<in> query_index_state_values M"
  proof -
    have
      "fmlookup M (QueryIndexChallenge j final) = Some z"
      using old_lookup k_eq by simp
    then show ?thesis by (rule query_index_lookup_state_value)
  qed
  have full_chain_new:
    "ro_absorb_lookup_chain
      (channel_for_hash_map (fmupd x y M))
      (PState adversary_initial_state)
      ([fr, first_root] @ rest) final"
    by (rule ro_absorb_lookup_chain_append[
          OF prefix_chain_new rest_chain_new])
  have full_chain_old:
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state)
      ([fr, first_root] @ rest) final"
    by (rule ro_absorb_lookup_chain_fresh_update_pullback[
          OF fresh full_chain_new final_target no_target])
  from ro_absorb_lookup_chain_append_split[OF full_chain_old]
  obtain prefix_hash_old where
    prefix_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        [fr, first_root] prefix_hash_old"
    and rest_chain_old:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        prefix_hash_old rest final"
    by blast
  have messages_target:
    "set ([fr, first_root] @ rest) \<subseteq>
      transcript_absorb_message_values M"
    by (rule ro_absorb_lookup_chain_messages_subset[OF full_chain_old])
  have fr_target: "fr \<in> transcript_absorb_message_values M"
    and first_target:
      "first_root \<in> transcript_absorb_message_values M"
    using messages_target by simp_all
  have ext:
    "channel_for_hash_map M \<le>
      channel_for_hash_map (fmupd x y M)"
    by (rule channel_for_hash_map_fresh_update_extends[OF fresh])
  have clean_old:
    "\<not> hash_map_output_collision (channel_for_hash_map M)"
  proof
    assume collision_old:
      "hash_map_output_collision (channel_for_hash_map M)"
    have
      "hash_map_output_collision
        (channel_for_hash_map (fmupd x y M))"
      by (rule hash_map_output_collision_mono[OF collision_old ext])
    then show False using clean_new by contradiction
  qed
  have no_initial_old:
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
  proof
    assume initial_old:
      "PState adversary_initial_state \<in>
        hash_map_output_values (channel_for_hash_map M)"
    from initial_old obtain q where q_lookup0:
      "fmlookup (HashMap (channel_for_hash_map M)) q =
        Some (PState adversary_initial_state)"
      unfolding hash_map_output_values_def by blast
    have q_lookup:
      "fmlookup M q = Some (PState adversary_initial_state)"
      using q_lookup0 unfolding channel_for_hash_map_def by simp
    have q_lookup_new:
      "fmlookup (fmupd x y M) q =
        Some (PState adversary_initial_state)"
      using q_lookup fresh by (cases "q = x") simp_all
    have
      "PState adversary_initial_state \<in>
        hash_map_output_values
          (channel_for_hash_map (fmupd x y M))"
    proof (rule hash_map_output_valuesI)
      show
        "fmlookup
          (HashMap (channel_for_hash_map (fmupd x y M))) q =
          Some (PState adversary_initial_state)"
        using q_lookup_new unfolding channel_for_hash_map_def by simp
    qed
    then show False using no_initial_new by contradiction
  qed
  have trace_table_eq:
    "first_trace_fri_root_prefix_trace_table
        (fr, [], first_root)
        (channel_for_hash_map (fmupd x y M)) =
      first_trace_fri_root_prefix_trace_table
        (fr, [], first_root)
        (channel_for_hash_map M)"
    using conceptual_table_fresh_update[
      OF fresh fr_target no_target]
    unfolding first_trace_fri_root_prefix_trace_table_def
    by simp
  have first_table_eq:
    "first_trace_fri_root_prefix_first_table
        (fr, [], first_root)
        (channel_for_hash_map (fmupd x y M)) =
      first_trace_fri_root_prefix_first_table
        (fr, [], first_root)
        (channel_for_hash_map M)"
    using conceptual_table_fresh_update[
      OF fresh first_target no_target]
    unfolding first_trace_fri_root_prefix_first_table_def
    by simp  have trace_low_old:
    "trace_table_low_degree
      (first_trace_fri_root_prefix_trace_table
        (fr, [], first_root) (channel_for_hash_map M))"
    using trace_low_new trace_table_eq by simp
  have first_low_old:
    "trace_table_low_degree
      (first_trace_fri_root_prefix_first_table
        (fr, [], first_root) (channel_for_hash_map M))"
    using first_low_new first_table_eq by simp
  have distinct_old:
    "first_trace_fri_root_prefix_trace_table
        (fr, [], first_root) (channel_for_hash_map M) \<noteq>
      first_trace_fri_root_prefix_first_table
        (fr, [], first_root) (channel_for_hash_map M)"
    using distinct_new trace_table_eq first_table_eq by simp
  have agreement_eq:
    "first_trace_fri_root_prefix_base_agreement_query_lists
        (fr, [], first_root)
        (channel_for_hash_map (fmupd x y M)) =
      first_trace_fri_root_prefix_base_agreement_query_lists
        (fr, [], first_root)
        (channel_for_hash_map M)"
    unfolding first_trace_fri_root_prefix_base_agreement_query_lists_def
    using trace_table_eq first_table_eq by simp
  have raws_in_old:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
      first_trace_fri_root_prefix_base_agreement_query_lists
        (fr, [], first_root) (channel_for_hash_map M)"
    using raws_in_new agreement_eq by simp
  show ?thesis
    unfolding first_root_absorbed_query_relation_def Let_def
    using clean_old no_initial_old prefix_chain_old rest_chain_old
      trace_low_old first_low_old distinct_old raws_len raws_in_old
      j_bound k_eq z_eq
    by blast
qed


lemma first_root_absorbed_query_relation_drift_activation_imp_target:
  assumes fresh: "fmlookup M x = None"
    and drift:
      "hash_state_relation_drift_activation
        first_root_absorbed_query_relation M x y"
  shows "y \<in> first_root_relation_drift_targets M x"
proof (rule ccontr)
  assume no_target: "y \<notin> first_root_relation_drift_targets M x"
  from drift obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        first_root_absorbed_query_relation (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        first_root_absorbed_query_relation M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and rel_new:
      "first_root_absorbed_query_relation (fmupd x y M) k z"
    using active_new
    unfolding hash_state_relation_active_def by blast+
  have rel_old: "first_root_absorbed_query_relation M k z"
    by (rule
      first_root_absorbed_query_relation_fresh_update_pullback[
        OF fresh key_neq lookup_new rel_new no_target])
  have lookup_old: "fmlookup M k = Some z"
    using lookup_new key_neq by simp
  have
    "hash_state_relation_active
      first_root_absorbed_query_relation M k z"
    unfolding hash_state_relation_active_def
    using lookup_old rel_old by simp
  then show False using inactive_old by contradiction
qed

lemma first_root_absorbed_query_relation_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_drift_activation
        first_root_absorbed_query_relation M x y}
      \<le> 5 * card (fmdom' M) + 2"
proof -
  have subset:
    "{y.
      hash_state_relation_drift_activation
        first_root_absorbed_query_relation M x y}
      \<subseteq> first_root_relation_drift_targets M x"
    using first_root_absorbed_query_relation_drift_activation_imp_target[
      OF fresh]
    by blast
  have
    "card {y.
      hash_state_relation_drift_activation
        first_root_absorbed_query_relation M x y}
      \<le> card (first_root_relation_drift_targets M x)"
    by (rule card_mono[OF finite_first_root_relation_drift_targets subset])
  also have "... \<le> 5 * card (fmdom' M) + 2"
    by (rule card_first_root_relation_drift_targets_le)
  finally show ?thesis .
qed

end
end
