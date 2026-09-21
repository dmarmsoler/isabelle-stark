(* Title: Stark/Soundness_FRI_Weighted_Semantic_Recovery.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Semantic_Recovery
  imports
    "Stark.Soundness_FRI_Correlated_Agreement_Guarded_Rectangles"
    "Stark.Soundness_FRI_First_Root_RO_State_Relation"
begin

section \<open>Semantic Recovery for weighted MCA soundness\<close>

text \<open>Recover decoded-semantic residual sets from authenticated serialized headers and track them under oracle-map extension. The two-draw lemmas are local ingredients; the complete all-repetition result is in @{text "Soundness_FRI_Weighted_Soundness"}.\<close>

subsection \<open>Semantic Insertion facts\<close>

context soundness
begin

definition weighted_semantic_header :: "'f staged_proof_data \<Rightarrow> 'f list" where
  "weighted_semantic_header data = verifier_header_messages
    (staged_trace_root data) (staged_trace_fri_roots data) (staged_trace_final data)
    (staged_alphas data) (staged_degree data) (staged_composition_fri_roots data)
    (staged_composition_final data)"

definition weighted_semantic_header_shape :: "'f staged_proof_data \<Rightarrow> bool" where
  "weighted_semantic_header_shape data \<longleftrightarrow>
    length (staged_trace_fri_roots data) = ceil_log clength \<and>
    length (staged_alphas data) = length spec \<and>
    length (staged_composition_fri_roots data) =
      ceil_log (to_nat (staged_degree data) + 1)"

definition weighted_semantic_indices ::
  "nat \<Rightarrow> nat \<Rightarrow> ('f protocol_hash_input, 'f) fmap \<Rightarrow> 'f staged_proof_data \<Rightarrow> nat set" where
  "weighted_semantic_indices rT rC M data =
    ro_mca_decoded_semantic_query_indices rT rC
      (staged_trace_root data, [], hd (staged_trace_fri_roots data))
      (channel_for_hash_map M) data (channel_for_hash_map M)"

lemma weighted_semantic_header_parse:
  assumes a: "weighted_semantic_header_shape a" and b: "weighted_semantic_header_shape b"
    and eq: "weighted_semantic_header a @ rest = weighted_semantic_header b @ rest'"
  shows "staged_trace_root b = staged_trace_root a \<and>
    staged_trace_fri_roots b = staged_trace_fri_roots a \<and>
    staged_trace_final b = staged_trace_final a \<and>
    staged_alphas b = staged_alphas a \<and>
    staged_degree b = staged_degree a \<and>
    staged_composition_fri_roots b = staged_composition_fri_roots a \<and>
    staged_composition_final b = staged_composition_final a \<and> rest' = rest"
proof -
  let ?s = "adversary_initial_state\<lparr>PTranscript := weighted_semantic_header a @ rest\<rparr>"
  have ha: "verifier_header_transcript ?s (staged_trace_root a)
    (staged_trace_fri_roots a) (staged_trace_final a) (staged_alphas a)
    (staged_degree a) (staged_composition_fri_roots a) (staged_composition_final a) rest"
    using a unfolding weighted_semantic_header_shape_def weighted_semantic_header_def verifier_header_transcript_def
    by simp
  have hb: "verifier_header_transcript ?s (staged_trace_root b)
    (staged_trace_fri_roots b) (staged_trace_final b) (staged_alphas b)
    (staged_degree b) (staged_composition_fri_roots b) (staged_composition_final b) rest'"
    using b eq unfolding weighted_semantic_header_shape_def weighted_semantic_header_def verifier_header_transcript_def
    by simp
  show ?thesis by (rule verifier_header_transcript_unique[OF ha hb])
qed

lemma weighted_semantic_indices_card:
  "card (weighted_semantic_indices rT rC M data) \<le> mca_decoded_semantic_query_index_bound rT rC"
  unfolding weighted_semantic_indices_def by (rule card_ro_mca_decoded_semantic_query_indices)

lemma weighted_semantic_indices_subset:
  "weighted_semantic_indices rT rC M data \<subseteq> query_sample_space"
  unfolding weighted_semantic_indices_def by (rule ro_mca_decoded_semantic_query_indices_subset)

lemma weighted_semantic_indices_header_cong:
  assumes "staged_trace_root a = staged_trace_root b"
    "staged_trace_fri_roots a = staged_trace_fri_roots b"
    "staged_alphas a = staged_alphas b"
    "staged_degree a = staged_degree b"
    "staged_composition_fri_roots a = staged_composition_fri_roots b"
    "staged_composition_final a = staged_composition_final b"
  shows "weighted_semantic_indices rT rC M a = weighted_semantic_indices rT rC M b"
  using assms
  unfolding weighted_semantic_indices_def ro_mca_decoded_semantic_query_indices_def
    ro_actual_query_trace_composition_accepted_indices_def
    first_trace_fri_root_prefix_first_table_def ro_actual_query_composition_candidate_def
  by (auto simp: Let_def)

lemma weighted_semantic_indices_query_update:
  "weighted_semantic_indices rT rC (fmupd (QueryIndexChallenge j st) y M) data =
    weighted_semantic_indices rT rC M data"
  unfolding weighted_semantic_indices_def ro_mca_decoded_semantic_query_indices_def
    ro_actual_query_trace_composition_accepted_indices_def
    first_trace_fri_root_prefix_first_table_def ro_actual_query_composition_candidate_def
  by (auto simp: Let_def)

definition weighted_semantic_ready ::
  "nat \<Rightarrow> nat \<Rightarrow> ('f protocol_hash_input, 'f) fmap \<Rightarrow> 'f \<Rightarrow> nat set \<Rightarrow> bool" where
  "weighted_semantic_ready rT rC M st I \<longleftrightarrow>
    (\<exists>data rest. weighted_semantic_header_shape data \<and> staged_trace_fri_roots data \<noteq> [] \<and>
      ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
        (weighted_semantic_header data @ rest) st \<and> I = weighted_semantic_indices rT rC M data)"

lemma weighted_semantic_ready_query_update:
  "weighted_semantic_ready rT rC (fmupd (QueryIndexChallenge j p) y M) st I =
    weighted_semantic_ready rT rC M st I"
  unfolding weighted_semantic_ready_def by (simp add: weighted_semantic_indices_query_update)

lemma weighted_semantic_ready_unique:
  assumes clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and initial: "PState adversary_initial_state \<notin> hash_map_output_values (channel_for_hash_map M)"
    and left: "weighted_semantic_ready rT rC M st I"
    and right: "weighted_semantic_ready rT rC M st J"
  shows "I = J"
proof -
  obtain a ar b br where a: "weighted_semantic_header_shape a" and b: "weighted_semantic_header_shape b"
    and ca: "ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
      (weighted_semantic_header a @ ar) st"
    and cb: "ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
      (weighted_semantic_header b @ br) st"
    and I: "I = weighted_semantic_indices rT rC M a"
    and J: "J = weighted_semantic_indices rT rC M b"
    using left right unfolding weighted_semantic_ready_def by blast
  have eq: "weighted_semantic_header a @ ar = weighted_semantic_header b @ br"
    by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[OF clean initial ca cb])
  note fields = weighted_semantic_header_parse[OF a b eq]
  have "weighted_semantic_indices rT rC M b = weighted_semantic_indices rT rC M a"
    by (rule weighted_semantic_indices_header_cong) (use fields in auto)
  then show ?thesis using I J by simp
qed

lemma weighted_semantic_indices_fresh_update:
  assumes fresh: "fmlookup M x = None"
    and active: "staged_trace_fri_roots data \<noteq> []"
    and header: "set (weighted_semantic_header data) \<subseteq> transcript_absorb_message_values M"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
  shows "weighted_semantic_indices rT rC (fmupd x y M) data =
    weighted_semantic_indices rT rC M data"
proof -
  have stable: "\<And>rt. rt \<in> set (weighted_semantic_header data) \<Longrightarrow>
    conceptual_table (channel_for_hash_map (fmupd x y M)) rt (scale*clength) =
    conceptual_table (channel_for_hash_map M) rt (scale*clength)"
    by (rule conceptual_table_fresh_update[OF fresh _ no_target]) (use header in blast)
  have original: "conceptual_table (channel_for_hash_map (fmupd x y M))
      (staged_trace_root data) (scale*clength) =
    conceptual_table (channel_for_hash_map M) (staged_trace_root data) (scale*clength)"
    by (rule stable) (simp add: weighted_semantic_header_def verifier_header_messages_def)
  have first: "conceptual_table (channel_for_hash_map (fmupd x y M))
      (hd (staged_trace_fri_roots data)) (scale*clength) =
    conceptual_table (channel_for_hash_map M) (hd (staged_trace_fri_roots data)) (scale*clength)"
    by (rule stable) (use active in \<open>auto simp: weighted_semantic_header_def verifier_header_messages_def\<close>)
  have comp: "ro_actual_query_composition_candidate data (channel_for_hash_map (fmupd x y M)) =
    ro_actual_query_composition_candidate data (channel_for_hash_map M)"
  proof (cases "staged_composition_fri_roots data = []")
    case True
    then show ?thesis by (simp add: ro_actual_query_composition_candidate_def)
  next
    case False
    have "conceptual_table (channel_for_hash_map (fmupd x y M))
        (hd (staged_composition_fri_roots data)) (scale*clength) =
      conceptual_table (channel_for_hash_map M) (hd (staged_composition_fri_roots data)) (scale*clength)"
      by (rule stable) (use False in \<open>auto simp: weighted_semantic_header_def verifier_header_messages_def\<close>)
    then show ?thesis unfolding ro_actual_query_composition_candidate_def using False by simp
  qed
  show ?thesis
    unfolding weighted_semantic_indices_def ro_mca_decoded_semantic_query_indices_def
      ro_actual_query_trace_composition_accepted_indices_def first_trace_fri_root_prefix_first_table_def
    using original first comp
    by (auto simp: Let_def)
qed

lemma weighted_semantic_ready_fresh_pullback:
  assumes fresh: "fmlookup M x = None"
    and cached: "fmlookup M (QueryIndexChallenge j st) = Some raw"
    and no_target: "y \<notin> first_root_relation_drift_targets M x"
    and ready: "weighted_semantic_ready rT rC (fmupd x y M) st I"
  shows "weighted_semantic_ready rT rC M st I"
proof -
  obtain data rest where shape: "weighted_semantic_header_shape data"
    and active: "staged_trace_fri_roots data \<noteq> []"
    and chain: "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
      (PState adversary_initial_state) (weighted_semantic_header data @ rest) st"
    and I: "I = weighted_semantic_indices rT rC (fmupd x y M) data"
    using ready unfolding weighted_semantic_ready_def by blast
  have st: "st \<in> query_index_state_values M"
    using cached unfolding query_index_state_values_def by blast
  have old_chain: "ro_absorb_lookup_chain (channel_for_hash_map M)
    (PState adversary_initial_state) (weighted_semantic_header data @ rest) st"
    by (rule ro_absorb_lookup_chain_fresh_update_pullback[OF fresh chain st no_target])
  have header: "set (weighted_semantic_header data) \<subseteq> transcript_absorb_message_values M"
    using ro_absorb_lookup_chain_messages_subset[OF old_chain] by auto
  have indices: "I = weighted_semantic_indices rT rC M data"
    using I weighted_semantic_indices_fresh_update[OF fresh active header no_target] by simp
  show ?thesis unfolding weighted_semantic_ready_def
    using shape active old_chain indices by blast
qed

lemma weighted_semantic_ready_drift_fiber:
  assumes fresh: "fmlookup M x = None"
    and cached: "fmlookup M (QueryIndexChallenge j st) = Some raw"
  shows "card {y. \<exists>I. weighted_semantic_ready rT rC (fmupd x y M) st I \<and>
    \<not> weighted_semantic_ready rT rC M st I} \<le> 5 * card (fmdom' M) + 2"
proof -
  have sub: "{y. \<exists>I. weighted_semantic_ready rT rC (fmupd x y M) st I \<and>
    \<not> weighted_semantic_ready rT rC M st I} \<subseteq> first_root_relation_drift_targets M x"
    using weighted_semantic_ready_fresh_pullback[OF fresh cached] by blast
  have "card {y. \<exists>I. weighted_semantic_ready rT rC (fmupd x y M) st I \<and>
    \<not> weighted_semantic_ready rT rC M st I} \<le> card (first_root_relation_drift_targets M x)"
    by (rule card_mono[OF finite_first_root_relation_drift_targets sub])
  also have "... \<le> 5 * card (fmdom' M) + 2" by (rule card_first_root_relation_drift_targets_le)
  finally show ?thesis .
qed

lemma weighted_semantic_transport:
  assumes prefix: "prefix = (staged_trace_root data, [], hd (staged_trace_fri_roots data))"
    and su: "s \<le> u" and tu: "t \<le> u"
    and clean: "\<not> hash_map_output_collision s"
    and no_trace: "\<not> hash_map_new_output_hit
      (first_trace_fri_root_prefix_merkle_targets prefix s) s u"
    and no_comp: "\<not> hash_map_new_output_hit
      (ro_actual_query_composition_prefix_targets data t) t u"
  shows "ro_mca_decoded_semantic_query_indices rT rC prefix s data t =
    weighted_semantic_indices rT rC (HashMap u) data"
proof -
  have no_original: "\<not> hash_map_new_output_hit
    (merkle_prefix_path_targets {staged_trace_root data} s) s u"
    and no_first: "\<not> hash_map_new_output_hit
    (merkle_prefix_path_targets {hd (staged_trace_fri_roots data)} s) s u"
    using no_trace clean unfolding prefix first_trace_fri_root_prefix_merkle_targets_def
      merkle_prefix_path_targets_def hash_map_new_output_hit_def by auto
  have same: "\<And>rt n. conceptual_table (channel_for_hash_map (HashMap u)) rt n =
    conceptual_table u rt n"
    by (rule conceptual_table_cong_hash_map) (simp add: channel_for_hash_map_def)
  have original: "conceptual_table s (staged_trace_root data) (scale*clength) =
    conceptual_table (channel_for_hash_map (HashMap u)) (staged_trace_root data) (scale*clength)"
    using conceptual_table_prefix_stable_if_no_target[OF su no_original] same by simp
  have first: "conceptual_table s (hd (staged_trace_fri_roots data)) (scale*clength) =
    conceptual_table (channel_for_hash_map (HashMap u)) (hd (staged_trace_fri_roots data)) (scale*clength)"
    using conceptual_table_prefix_stable_if_no_target[OF su no_first] same by simp
  have comp: "ro_actual_query_composition_candidate data t =
    ro_actual_query_composition_candidate data (channel_for_hash_map (HashMap u))"
  proof (cases "staged_composition_fri_roots data = []")
    case True
    then show ?thesis by (simp add: ro_actual_query_composition_candidate_def)
  next
    case False
    have nt: "\<not> hash_map_new_output_hit
      (merkle_prefix_path_targets {hd (staged_composition_fri_roots data)} t) t u"
      using no_comp False by (simp add: ro_actual_query_composition_prefix_targets_def)
    show ?thesis using conceptual_table_prefix_stable_if_no_target[OF tu nt] same False
      unfolding ro_actual_query_composition_candidate_def by simp
  qed
  show ?thesis
    unfolding weighted_semantic_indices_def ro_mca_decoded_semantic_query_indices_def prefix
      ro_actual_query_trace_composition_accepted_indices_def first_trace_fri_root_prefix_first_table_def
    using original first comp by (auto simp: Let_def)
qed

lemma weighted_semantic_indices_head_data:
  "weighted_semantic_indices rT rC M (ro_query_head_data data) =
    weighted_semantic_indices rT rC M data"
  by (rule weighted_semantic_indices_header_cong) (simp_all add: ro_query_head_data_def)

definition weighted_semantic_hit ::
  "nat \<Rightarrow> nat \<Rightarrow> ('f protocol_hash_input, 'f) fmap \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool" where
  "weighted_semantic_hit rT rC M st raw \<longleftrightarrow>
    (\<exists>I. weighted_semantic_ready rT rC M st I \<and> raw \<in> query_index_raw_preimage I)"

lemma weighted_semantic_ready_bounds:
  assumes "weighted_semantic_ready rT rC M st I"
  shows "I \<subseteq> query_sample_space" and "card I \<le> mca_decoded_semantic_query_index_bound rT rC"
  using assms weighted_semantic_indices_subset weighted_semantic_indices_card
  unfolding weighted_semantic_ready_def by blast+

lemma weighted_semantic_hit_fiber:
  assumes clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and initial: "PState adversary_initial_state \<notin> hash_map_output_values (channel_for_hash_map M)"
  shows "card {y. weighted_semantic_hit rT rC M st y} \<le>
    query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)"
proof (cases "\<exists>I. weighted_semantic_ready rT rC M st I")
  case False
  then show ?thesis unfolding weighted_semantic_hit_def by simp
next
  case True
  then obtain I where ready: "weighted_semantic_ready rT rC M st I" by blast
  have eq: "{y. weighted_semantic_hit rT rC M st y} = query_index_raw_preimage I"
    unfolding weighted_semantic_hit_def using weighted_semantic_ready_unique[OF clean initial ready] ready
    by blast
  have "card (query_index_raw_preimage I) \<le> query_raw_preimage_card_envelope (card I)"
    by (rule card_query_index_raw_preimage_le_query_envelope[OF weighted_semantic_ready_bounds(1)[OF ready]])
  also have "... \<le> query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)"
    by (rule query_raw_preimage_card_envelope_mono[OF weighted_semantic_ready_bounds(2)[OF ready]])
  finally show ?thesis unfolding eq .
qed

lemma weighted_semantic_hit_query_update:
  "weighted_semantic_hit rT rC (fmupd (QueryIndexChallenge j p) y M) st raw =
    weighted_semantic_hit rT rC M st raw"
  unfolding weighted_semantic_hit_def by (simp add: weighted_semantic_ready_query_update)

lemma wp_weighted_semantic_first_draw:
  fixes s :: "'f protocol_channel"
  assumes fresh: "fmlookup (HashMap s) (QueryIndexChallenge j st) = None"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map (HashMap s))"
    and initial: "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map (HashMap s))"
  shows "wp_event (hash (QueryIndexChallenge j st))
    (\<lambda>out. case out of None \<Rightarrow> False | Some (raw,t) \<Rightarrow>
      weighted_semantic_hit rT rC (HashMap t) st raw) s \<le>
    nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
      nnreal size"
proof -
  let ?S = "{raw. weighted_semantic_hit rT rC (HashMap s) st raw}"
  have exact: "wp_event (hash (QueryIndexChallenge j st))
    (\<lambda>out. case out of None \<Rightarrow> False | Some (raw,t) \<Rightarrow>
      weighted_semantic_hit rT rC (HashMap t) st raw) s =
    nnreal (card ?S) / nnreal size"
    unfolding wp_event_def
    using dist_expect_hash_dist_fresh_indicator[OF fresh, of "?S"]
    by (simp add: wp_hash weighted_semantic_hit_query_update)
  have bound: "card ?S \<le> query_raw_preimage_card_envelope
      (mca_decoded_semantic_query_index_bound rT rC)"
    by (rule weighted_semantic_hit_fiber[OF clean initial])
  show ?thesis unfolding exact by (rule nnreal_nat_divide_right_mono[OF bound])
qed

lemma weighted_semantic_actual_builder_semantic_ready:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome: "Some (((prefix, prefix_state), data, query_start, raws, query_states), attacker_state)
      \<in> set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
        adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and j: "j < rounds"
    and no_trace: "\<not> hash_map_new_output_hit
      (first_trace_fri_root_prefix_merkle_targets prefix prefix_state) prefix_state attacker_state"
    and no_comp: "\<not> hash_map_new_output_hit
      (ro_actual_query_composition_prefix_targets data query_start) query_start attacker_state"
  shows "weighted_semantic_ready rT rC (HashMap attacker_state) (PState (query_states ! j))
    (ro_mca_decoded_semantic_query_indices rT rC prefix prefix_state data query_start)"
proof -
  have original_out: "Some (data, attacker_state) \<in>
    set_dist (execute (ro_checked_staged_transcript_program A) adversary_initial_state)"
    by (rule ro_checked_staged_transcript_program_with_first_root_projection_outcome[OF nonempty outcome])
  have shape: "weighted_semantic_header_shape data"
    using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
    unfolding weighted_semantic_header_shape_def by blast
  have active: "staged_trace_fri_roots data \<noteq> []"
    using shape nonempty unfolding weighted_semantic_header_shape_def by auto
  note chains = ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
    OF wf controlled nonempty outcome clean j]
  have pref: "prefix = (staged_trace_root data, [], hd (staged_trace_fri_roots data))"
    using chains by blast
  have h: "ro_absorb_lookup_chain attacker_state (PState adversary_initial_state)
    (weighted_semantic_header data) (PState query_start)"
    using chains unfolding weighted_semantic_header_def by blast
  have q: "ro_absorb_lookup_chain attacker_state (PState query_start)
    (List.concat (take j (staged_query_chunks data))) (PState (query_states ! j))"
    using chains by blast
  have chain0: "ro_absorb_lookup_chain attacker_state (PState adversary_initial_state)
    (weighted_semantic_header data @ List.concat (take j (staged_query_chunks data))) (PState (query_states ! j))"
    by (rule ro_absorb_lookup_chain_append[OF h q])
  have map_eq: "HashMap (channel_for_hash_map (HashMap attacker_state)) = HashMap attacker_state"
    by (simp add: channel_for_hash_map_def)
  have chain: "ro_absorb_lookup_chain (channel_for_hash_map (HashMap attacker_state))
    (PState adversary_initial_state)
    (weighted_semantic_header data @ List.concat (take j (staged_query_chunks data))) (PState (query_states ! j))"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF map_eq]) (rule chain0)
  have su: "prefix_state \<le> attacker_state"
    using ro_checked_staged_transcript_program_with_first_root_good_fields[
      OF wf controlled nonempty outcome] by blast
  have tu: "query_start \<le> attacker_state"
    using ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
      OF wf controlled outcome] by blast
  have sc: "\<not> hash_map_output_collision prefix_state"
    using hash_map_output_collision_mono[OF _ su] clean by blast
  have eq: "ro_mca_decoded_semantic_query_indices rT rC prefix prefix_state data query_start =
    weighted_semantic_indices rT rC (HashMap attacker_state) data"
    by (rule weighted_semantic_transport[OF pref su tu sc no_trace no_comp])
  show ?thesis unfolding weighted_semantic_ready_def using shape active chain eq by blast
qed

end

subsection \<open>Semantic Interval Recovery\<close>

context soundness
begin

definition weighted_semantic_interval_targets :: "('f protocol_hash_input, 'f) fmap \<Rightarrow> 'f set" where
  "weighted_semantic_interval_targets M =
    transcript_absorb_input_values M \<union> transcript_absorb_message_values M \<union>
    query_index_state_values M \<union> hash_map_merkle_child_values (channel_for_hash_map M)"

lemma weighted_semantic_interval_targets_finite[simp]: "finite (weighted_semantic_interval_targets M)"
  unfolding weighted_semantic_interval_targets_def by simp

lemma weighted_semantic_interval_targets_card:
  "card (weighted_semantic_interval_targets M) \<le> 5 * card (fmdom' M)"
proof -
  let ?A = "transcript_absorb_input_values M"
  let ?B = "transcript_absorb_message_values M"
  let ?C = "query_index_state_values M"
  let ?D = "hash_map_merkle_child_values (channel_for_hash_map M)"
  have d: "card ?D \<le> 2 * card (fmdom' M)"
    using card_hash_map_merkle_child_values_le[of "channel_for_hash_map M"]
    by (simp add: channel_for_hash_map_def)
  show ?thesis
    using card_Un_le[of ?A ?B] card_Un_le[of "?A \<union> ?B" ?C]
      card_Un_le[of "?A \<union> ?B \<union> ?C" ?D]
      card_transcript_absorb_input_values_le[of M]
      card_transcript_absorb_message_values_le[of M]
      card_query_index_state_values_le[of M] d
    unfolding weighted_semantic_interval_targets_def by linarith
qed

lemma weighted_semantic_absorb_interval_pullback:
  fixes s u :: "'f protocol_channel"
  assumes ext: "s \<le> u"
    and inputs: "transcript_absorb_input_values (HashMap s) \<subseteq> T"
    and no_hit: "\<not> hash_map_new_output_hit T s u"
    and chain: "ro_absorb_lookup_chain u start messages final"
    and target: "final \<in> T"
  shows "ro_absorb_lookup_chain s start messages final"
  using chain target
proof (induction messages arbitrary: final rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc msg messages)
  obtain mid where prefix: "ro_absorb_lookup_chain u start messages mid"
    and last: "fmlookup (HashMap u) (TranscriptAbsorb mid msg) = Some final"
    using ro_absorb_lookup_chain_snoc[OF snoc.prems(1)] by blast
  have old: "fmlookup (HashMap s) (TranscriptAbsorb mid msg) = Some final"
  proof (cases "fmlookup (HashMap s) (TranscriptAbsorb mid msg)")
    case None
    then have "hash_map_new_output_hit T s u"
      using last snoc.prems(2) unfolding hash_map_new_output_hit_def by blast
    then show ?thesis using no_hit by contradiction
  next
    case (Some z)
    have "fmlookup (HashMap u) (TranscriptAbsorb mid msg) = Some z"
      by (rule hash_extension_lookup[OF Some ext])
    then show ?thesis using last Some by simp
  qed
  have mid: "mid \<in> T"
    using old inputs unfolding transcript_absorb_input_values_def by blast
  have prefix_old: "ro_absorb_lookup_chain s start messages mid"
    by (rule snoc.IH[OF prefix mid])
  have last_old: "ro_absorb_lookup_chain s mid [msg] final" using old by auto
  show ?case by (rule ro_absorb_lookup_chain_append[OF prefix_old last_old])
qed

lemma weighted_semantic_map_cong:
  assumes active: "staged_trace_fri_roots data \<noteq> []"
    and tables: "\<And>rt. rt \<in> set (weighted_semantic_header data) \<Longrightarrow>
      conceptual_table (channel_for_hash_map M) rt (scale*clength) =
      conceptual_table (channel_for_hash_map U) rt (scale*clength)"
  shows "weighted_semantic_indices rT rC M data = weighted_semantic_indices rT rC U data"
proof -
  have original: "conceptual_table (channel_for_hash_map M) (staged_trace_root data) (scale*clength) =
    conceptual_table (channel_for_hash_map U) (staged_trace_root data) (scale*clength)"
    by (rule tables) (simp add: weighted_semantic_header_def verifier_header_messages_def)
  have first: "conceptual_table (channel_for_hash_map M) (hd (staged_trace_fri_roots data)) (scale*clength) =
    conceptual_table (channel_for_hash_map U) (hd (staged_trace_fri_roots data)) (scale*clength)"
    by (rule tables) (use active in \<open>auto simp: weighted_semantic_header_def verifier_header_messages_def\<close>)
  have comp: "ro_actual_query_composition_candidate data (channel_for_hash_map M) =
    ro_actual_query_composition_candidate data (channel_for_hash_map U)"
  proof (cases "staged_composition_fri_roots data = []")
    case True
    then show ?thesis by (simp add: ro_actual_query_composition_candidate_def)
  next
    case False
    have "conceptual_table (channel_for_hash_map M) (hd (staged_composition_fri_roots data)) (scale*clength) =
      conceptual_table (channel_for_hash_map U) (hd (staged_composition_fri_roots data)) (scale*clength)"
      by (rule tables) (use False in \<open>auto simp: weighted_semantic_header_def verifier_header_messages_def\<close>)
    then show ?thesis using False unfolding ro_actual_query_composition_candidate_def by simp
  qed
  show ?thesis
    unfolding weighted_semantic_indices_def ro_mca_decoded_semantic_query_indices_def
      ro_actual_query_trace_composition_accepted_indices_def first_trace_fri_root_prefix_first_table_def
    using original first comp by (auto simp: Let_def)
qed

lemma weighted_semantic_ready_interval_pullback:
  assumes ext: "channel_for_hash_map M \<le> channel_for_hash_map U"
    and cached: "fmlookup M (QueryIndexChallenge j st) = Some raw"
    and no_hit: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets M)
      (channel_for_hash_map M) (channel_for_hash_map U)"
    and ready: "weighted_semantic_ready rT rC U st I"
  shows "weighted_semantic_ready rT rC M st I"
proof -
  obtain data rest where shape: "weighted_semantic_header_shape data"
    and active: "staged_trace_fri_roots data \<noteq> []"
    and chain: "ro_absorb_lookup_chain (channel_for_hash_map U)
      (PState adversary_initial_state) (weighted_semantic_header data @ rest) st"
    and I: "I = weighted_semantic_indices rT rC U data"
    using ready unfolding weighted_semantic_ready_def by blast
  have inputs: "transcript_absorb_input_values (HashMap (channel_for_hash_map M))
    \<subseteq> weighted_semantic_interval_targets M"
    unfolding weighted_semantic_interval_targets_def channel_for_hash_map_def by auto
  have target: "st \<in> weighted_semantic_interval_targets M"
    using cached unfolding weighted_semantic_interval_targets_def query_index_state_values_def by blast
  have old_chain: "ro_absorb_lookup_chain (channel_for_hash_map M)
    (PState adversary_initial_state) (weighted_semantic_header data @ rest) st"
    by (rule weighted_semantic_absorb_interval_pullback[OF ext inputs no_hit chain target])
  have header: "set (weighted_semantic_header data) \<subseteq> transcript_absorb_message_values M"
    using ro_absorb_lookup_chain_messages_subset[OF old_chain] by auto
  have tables: "\<And>rt. rt \<in> set (weighted_semantic_header data) \<Longrightarrow>
    conceptual_table (channel_for_hash_map M) rt (scale*clength) =
    conceptual_table (channel_for_hash_map U) rt (scale*clength)"
  proof -
    fix rt
    assume rt: "rt \<in> set (weighted_semantic_header data)"
    have sub: "merkle_prefix_path_targets {rt} (channel_for_hash_map M) \<subseteq> weighted_semantic_interval_targets M"
      using header rt unfolding merkle_prefix_path_targets_def weighted_semantic_interval_targets_def by blast
    have nt: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {rt} (channel_for_hash_map M))
      (channel_for_hash_map M) (channel_for_hash_map U)"
      using hash_map_new_output_hit_subset[OF sub] no_hit by blast
    show "conceptual_table (channel_for_hash_map M) rt (scale*clength) =
      conceptual_table (channel_for_hash_map U) rt (scale*clength)"
      using conceptual_table_prefix_stable_if_no_target[OF ext nt] by simp
  qed
  have indices: "I = weighted_semantic_indices rT rC M data"
    using I weighted_semantic_map_cong[OF active tables] by simp
  show ?thesis unfolding weighted_semantic_ready_def
    using shape active old_chain indices by blast
qed

lemma weighted_semantic_interval_targets_query_update:
  "weighted_semantic_interval_targets (fmupd (QueryIndexChallenge j st) raw M) =
    weighted_semantic_interval_targets M \<union> {st}"
  unfolding weighted_semantic_interval_targets_def transcript_absorb_input_values_def
    transcript_absorb_message_values_def query_index_state_values_def
    hash_map_merkle_child_values_def channel_for_hash_map_def
    merkle_node_child_output_relation_def
  by auto

lemma weighted_semantic_interval_targets_after_query_card:
  "card (weighted_semantic_interval_targets (fmupd (QueryIndexChallenge j st) raw M)) \<le>
    5 * card (fmdom' M) + 1"
  unfolding weighted_semantic_interval_targets_query_update
  using card_Un_le[of "weighted_semantic_interval_targets M" "{st}"] weighted_semantic_interval_targets_card[of M]
  by simp

lemma weighted_semantic_first_insertion_recovery:
  assumes ext: "channel_for_hash_map (fmupd (QueryIndexChallenge j st) raw M) \<le> channel_for_hash_map U"
    and no_hit: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets M \<union> {st})
      (channel_for_hash_map (fmupd (QueryIndexChallenge j st) raw M)) (channel_for_hash_map U)"
    and ready: "weighted_semantic_ready rT rC U st I"
  shows "weighted_semantic_ready rT rC M st I"
proof -
  have nt: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets (fmupd (QueryIndexChallenge j st) raw M))
      (channel_for_hash_map (fmupd (QueryIndexChallenge j st) raw M)) (channel_for_hash_map U)"
    using no_hit by (simp add: weighted_semantic_interval_targets_query_update)
  have "weighted_semantic_ready rT rC (fmupd (QueryIndexChallenge j st) raw M) st I"
    by (rule weighted_semantic_ready_interval_pullback[OF ext _ nt ready, where j=j and raw=raw]) simp
  then show ?thesis by (simp add: weighted_semantic_ready_query_update)
qed

end

subsection \<open>Semantic Draw Continuation\<close>

context soundness
begin

definition weighted_semantic_draw_then ::
  "('f \<Rightarrow> ('a, 'f protocol_channel) state_monad) \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow> ('f, 'f protocol_channel) state_monad"
where
  "weighted_semantic_draw_then K j st = do {raw \<leftarrow> hash (QueryIndexChallenge j st); K raw; return raw}"

lemma weighted_semantic_draw_then_target:
  assumes continuation: "\<And>raw. hash_target_program B q (K raw)"
  shows "hash_target_program B (Suc q) (weighted_semantic_draw_then K j st)"
proof -
  have tail: "\<And>raw. hash_target_program B q (K raw \<bind> (\<lambda>_. return raw))"
  proof -
    fix raw
    have "hash_target_program B (q + 0) (K raw \<bind> (\<lambda>_. return raw))"
      by (rule hash_target_program_bind[OF continuation])
        (rule hash_target_program_return)
    then show "hash_target_program B q (K raw \<bind> (\<lambda>_. return raw))" by simp
  qed
  have "hash_target_program B (1 + q)
      (hash (QueryIndexChallenge j st) \<bind> (\<lambda>raw. K raw \<bind> (\<lambda>_. return raw)))"
    by (rule hash_target_program_bind[OF hash_target_program_hash tail])
  then show ?thesis unfolding weighted_semantic_draw_then_def by simp
qed

lemma weighted_semantic_hash_state:
  fixes s t :: "'f protocol_channel"
  assumes outcome: "Some (raw,t) \<in> set_dist (execute (hash k) s)"
  shows "t = s\<lparr>HashMap := fmupd k raw (HashMap s)\<rparr>"
  using outcome
  unfolding hash_def apply_hash_def modify_HashMap_def modify_def
  by (auto simp: lift.rep_eq lift_dist_def set_dist_dist_map elim!: set_dist_bindE)

lemma wp_weighted_semantic_draw_then_clean:
  fixes s :: "'f protocol_channel"
  assumes extension: "\<And>raw. hash_extension_preserving (K raw)"
    and fresh: "fmlookup (HashMap s) (QueryIndexChallenge j st) = None"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map (HashMap s))"
    and initial: "PState adversary_initial_state \<notin> hash_map_output_values (channel_for_hash_map (HashMap s))"
  shows "wp_event (weighted_semantic_draw_then K j st)
    (\<lambda>out. case out of None \<Rightarrow> False | Some (raw,u) \<Rightarrow>
      weighted_semantic_hit rT rC (HashMap u) st raw \<and>
      \<not> hash_map_new_output_hit (weighted_semantic_interval_targets (HashMap s) \<union> {st}) s u) s
    \<le> nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
      nnreal size"
  unfolding weighted_semantic_draw_then_def
proof (rule wp_event_bind_bound_by_head_event[
    OF wp_weighted_semantic_first_draw[OF fresh clean initial]])
  show "(case None of None \<Rightarrow> False | Some (raw,u) \<Rightarrow>
      weighted_semantic_hit rT rC (HashMap u) st raw \<and>
      \<not> hash_map_new_output_hit (weighted_semantic_interval_targets (HashMap s) \<union> {st}) s u)
    \<Longrightarrow> (case None of None \<Rightarrow> False | Some (raw,t) \<Rightarrow> weighted_semantic_hit rT rC (HashMap t) st raw)"
    by simp
next
  fix raw t out
  assume head: "Some (raw,t) \<in> set_dist (execute (hash (QueryIndexChallenge j st)) s)"
    and tail: "out \<in> set_dist (execute (K raw \<bind> (\<lambda>_. return raw)) t)"
    and event: "case out of None \<Rightarrow> False | Some (raw,u) \<Rightarrow>
      weighted_semantic_hit rT rC (HashMap u) st raw \<and>
      \<not> hash_map_new_output_hit (weighted_semantic_interval_targets (HashMap s) \<union> {st}) s u"
  obtain v u where eq: "out = Some (raw,u)" and kout: "Some (v,u) \<in> set_dist (execute (K raw) t)"
    using tail event by (cases out) (auto elim!: set_dist_bindE)
  have tu: "t \<le> u"
    using extension kout
    unfolding hash_extension_preserving_def by blast
  have st_ext: "s \<le> t" by (rule hash_outcome(1)[OF head])
  have tm: "HashMap t = fmupd (QueryIndexChallenge j st) raw (HashMap s)"
    using weighted_semantic_hash_state[OF head] by simp
  have ext: "channel_for_hash_map (fmupd (QueryIndexChallenge j st) raw (HashMap s)) \<le>
    channel_for_hash_map (HashMap u)"
    using tu unfolding less_eq_hash_ext_def channel_for_hash_map_def tm by simp
  have nt: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets (HashMap s) \<union> {st}) t u"
    using hash_map_new_output_hit_extend_initial[OF st_ext] event eq by auto
  have nt_maps: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets (HashMap s) \<union> {st})
    (channel_for_hash_map (fmupd (QueryIndexChallenge j st) raw (HashMap s)))
    (channel_for_hash_map (HashMap u))"
    using nt unfolding hash_map_new_output_hit_def channel_for_hash_map_def tm by simp
  obtain I where ready: "weighted_semantic_ready rT rC (HashMap u) st I"
    and hit: "raw \<in> query_index_raw_preimage I"
    using event eq unfolding weighted_semantic_hit_def by auto
  have recovered: "weighted_semantic_ready rT rC (HashMap s) st I"
    by (rule weighted_semantic_first_insertion_recovery[OF ext nt_maps ready])
  have current: "weighted_semantic_hit rT rC (HashMap t) st raw"
    unfolding tm weighted_semantic_hit_def using recovered hit
    by (auto simp: weighted_semantic_ready_query_update)
  show "case Some (raw,t) of None \<Rightarrow> False | Some (raw,t) \<Rightarrow> weighted_semantic_hit rT rC (HashMap t) st raw"
    using current by simp
qed

lemma wp_weighted_semantic_draw_then_bound:
  fixes s :: "'f protocol_channel"
  assumes continuation: "\<And>raw. hash_target_program (weighted_semantic_interval_targets (HashMap s) \<union> {st}) q (K raw)"
    and fresh: "fmlookup (HashMap s) (QueryIndexChallenge j st) = None"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map (HashMap s))"
    and initial: "PState adversary_initial_state \<notin> hash_map_output_values (channel_for_hash_map (HashMap s))"
  shows "wp_event (weighted_semantic_draw_then K j st)
    (\<lambda>out. case out of None \<Rightarrow> False | Some (raw,u) \<Rightarrow>
      weighted_semantic_hit rT rC (HashMap u) st raw) s
    \<le> nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
        nnreal size
      + hash_target_budget_value (weighted_semantic_interval_targets (HashMap s) \<union> {st}) (Suc q)"
proof -
  let ?B = "weighted_semantic_interval_targets (HashMap s) \<union> {st}"
  let ?m = "weighted_semantic_draw_then K j st"
  let ?H = "\<lambda>out. case out of None \<Rightarrow> False | Some (raw,u) \<Rightarrow> weighted_semantic_hit rT rC (HashMap u) st raw"
  let ?G = "\<lambda>out. case out of None \<Rightarrow> False | Some (raw,u) \<Rightarrow>
    weighted_semantic_hit rT rC (HashMap u) st raw \<and> \<not> hash_map_new_output_hit ?B s u"
  let ?E = "hash_new_output_hit_event ?B s"
  have split: "wp_event ?m ?H s \<le> wp_event ?m (\<lambda>out. ?G out \<or> ?E out) s"
    by (rule wp_event_mono) (auto split: option.splits simp: hash_new_output_hit_event_def)
  have charged: "wp_event ?m ?E s \<le> hash_target_budget_value ?B (Suc q)"
    using weighted_semantic_draw_then_target[where K=K and q=q and B="?B" and j=j and st=st, OF continuation]
    unfolding hash_target_program_def hash_target_budget_def by blast
  have "wp_event ?m ?H s \<le> wp_event ?m ?G s + wp_event ?m ?E s"
    using split wp_event_union_bound[of ?m ?G ?E s] by order
  also have "... \<le>
      nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
        nnreal size + hash_target_budget_value ?B (Suc q)"
    by (rule add_mono[OF wp_weighted_semantic_draw_then_clean[OF hash_target_program_extension[OF continuation] fresh clean initial] charged])
  finally show ?thesis .
qed

corollary wp_weighted_semantic_controlled_draw_then_bound:
  fixes s :: "'f protocol_channel"
  assumes controlled: "\<And>raw. controlled_ro_program q (K raw)"
    and fresh: "fmlookup (HashMap s) (QueryIndexChallenge j st) = None"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map (HashMap s))"
    and initial: "PState adversary_initial_state \<notin> hash_map_output_values (channel_for_hash_map (HashMap s))"
  shows "wp_event (weighted_semantic_draw_then K j st)
    (\<lambda>out. case out of None \<Rightarrow> False | Some (raw,u) \<Rightarrow>
      weighted_semantic_hit rT rC (HashMap u) st raw) s
    \<le> nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
        nnreal size
      + hash_target_budget_value (weighted_semantic_interval_targets (HashMap s) \<union> {st}) (Suc q)"
  by (rule wp_weighted_semantic_draw_then_bound[OF _ fresh clean initial])
    (rule controlled_ro_program_target[OF controlled])

end

subsection \<open>Two Query Probability\<close>

context soundness
begin

text \<open>Proof-only logging of actual lazy hash calls. These programs are not
changes to the protocol. Freshness is tested in the recorded pre-draw map;
cached replays never count as another independent draw.\<close>

definition pair_base_ok where
  "pair_base_ok M \<longleftrightarrow>
    \<not> hash_map_output_collision (channel_for_hash_map M) \<and>
    PState adversary_initial_state \<notin> hash_map_output_values (channel_for_hash_map M)"

definition pair_insert_good where
  "pair_insert_good rT rC e \<longleftrightarrow>
    (case e of (M,k,raw) \<Rightarrow> \<exists>j st. k = QueryIndexChallenge j st \<and>
      fmlookup M k = None \<and> pair_base_ok M \<and>
      weighted_semantic_hit rT rC M st raw)"

definition pair_probe ::
  "'f protocol_hash_input \<Rightarrow>
    ((('f protocol_hash_input,'f) fmap \<times> 'f protocol_hash_input \<times> 'f),
      'f protocol_channel) state_monad"
where
  "pair_probe k = do {s \<leftarrow> get; raw \<leftarrow> hash k; return (HashMap s,k,raw)}"

lemma wp_pair_probe:
  fixes s :: "'f protocol_channel"
  shows "wp_event (pair_probe k)
    (\<lambda>out. case out of None \<Rightarrow> False | Some (e,t) \<Rightarrow> pair_insert_good rT rC e) s \<le>
    nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
      nnreal size"
proof (cases "\<exists>j st. k = QueryIndexChallenge j st \<and>
    fmlookup (HashMap s) k = None \<and> pair_base_ok (HashMap s)")
  case False
  then show ?thesis
    unfolding pair_probe_def pair_insert_good_def wp_event_def
    by (force simp: wpsimps)
next
  case True
  then obtain j st where k: "k = QueryIndexChallenge j st"
    and fresh: "fmlookup (HashMap s) k = None"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map (HashMap s))"
    and initial: "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map (HashMap s))"
    unfolding pair_base_ok_def by blast
  have exact: "wp_event (pair_probe k)
      (\<lambda>out. case out of None \<Rightarrow> False | Some (e,t) \<Rightarrow> pair_insert_good rT rC e) s =
    nnreal (card {raw. weighted_semantic_hit rT rC (HashMap s) st raw}) / nnreal size"
    unfolding pair_probe_def pair_insert_good_def pair_base_ok_def wp_event_def
    using dist_expect_hash_dist_fresh_indicator[OF fresh,
      of "{raw. weighted_semantic_hit rT rC (HashMap s) st raw}"]
    using k fresh clean initial
    by (simp add: wpsimps k)
  show ?thesis unfolding exact
    by (rule nnreal_nat_divide_right_mono[OF weighted_semantic_hit_fiber[OF clean initial]])
qed

definition pair_finish where
  "pair_finish K e1 e2 = do {K e1 e2; return (e1,e2)}"

definition pair_second where
  "pair_second C K e1 = do {w \<leftarrow> C e1; e2 \<leftarrow> pair_probe (fst w); pair_finish (\<lambda>e1 e2. K e1 (snd w) e2) e1 e2}"

definition pair_experiment where
  "pair_experiment C K k = do {e1 \<leftarrow> pair_probe k; pair_second C K e1}"

definition pair_insert_event where
  "pair_insert_event rT rC out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some ((e1,e2),t) \<Rightarrow>
      pair_insert_good rT rC e1 \<and> pair_insert_good rT rC e2)"

lemma wp_pair_second_zero:
  assumes "\<not> pair_insert_good rT rC e1"
  shows "wp_event (pair_second C K e1) (pair_insert_event rT rC) s = 0"
proof -
  have no: "\<And>out. out \<in> set_dist (execute (pair_second C K e1) s) \<Longrightarrow>
      \<not> pair_insert_event rT rC out"
  proof -
    fix out
    assume mem: "out \<in> set_dist (execute (pair_second C K e1) s)"
    show "\<not> pair_insert_event rT rC out"
      using mem assms unfolding pair_second_def pair_finish_def pair_insert_event_def
      by (cases out) (auto elim!: set_dist_bindE split: prod.splits)
  qed
  have "\<not> 0 < wp_event (pair_second C K e1) (pair_insert_event rT rC) s"
  proof
    assume pos: "0 < wp_event (pair_second C K e1) (pair_insert_event rT rC) s"
    show False
      by (rule wp_event_pos_imp_exists_support[OF pos]) (use no in blast)
  qed
  then show ?thesis by simp
qed

lemma wp_pair_second_bound:
  shows "wp_event (pair_second C K e1) (pair_insert_event rT rC) s \<le>
    nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
      nnreal size"
  unfolding pair_second_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> pair_insert_event rT rC None"
    by (simp add: pair_insert_event_def)
next
  fix w t
  assume "Some (w,t) \<in> set_dist (execute (C e1) s)"
  let ?K = "\<lambda>e1 e2. K e1 (snd w) e2"
  show "wp_event (pair_probe (fst w) \<bind> pair_finish ?K e1) (pair_insert_event rT rC) t \<le>
    nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
      nnreal size"
  proof (rule wp_event_bind_bound_by_head_event[OF wp_pair_probe])
    show "pair_insert_event rT rC None \<Longrightarrow>
      (case None of None \<Rightarrow> False | Some (e,t) \<Rightarrow> pair_insert_good rT rC e)"
      by (simp add: pair_insert_event_def)
  next
    fix e u out
    assume "Some (e,u) \<in> set_dist (execute (pair_probe (fst w)) t)"
      and tail: "out \<in> set_dist (execute (pair_finish ?K e1 e) u)"
      and ev: "pair_insert_event rT rC out"
    show "case Some (e,u) of None \<Rightarrow> False | Some (e,t) \<Rightarrow> pair_insert_good rT rC e"
      using tail ev unfolding pair_finish_def pair_insert_event_def
      by (cases out) (auto elim!: set_dist_bindE split: prod.splits)
  qed
qed

lemma wp_pair_experiment:
  shows "wp_event (pair_experiment C K k) (pair_insert_event rT rC) s \<le>
    (nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
      nnreal size)^2"
proof -
  let ?p = "nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
      nnreal size"
  let ?P = "\<lambda>out. case out of None \<Rightarrow> False | Some (e,t) \<Rightarrow> pair_insert_good rT rC e"
  have step: "wp_event (pair_experiment C K k) (pair_insert_event rT rC) s \<le>
      wp_event (pair_probe k) ?P s * ?p"
    unfolding pair_experiment_def
    apply (rule wp_event_bind_bound_by_head_and_cont)
      apply (simp add: pair_insert_event_def)
     apply (simp only: option.case prod.case)
     apply (rule wp_pair_second_zero, assumption)
    by (rule wp_pair_second_bound)
  also have "... \<le> ?p * ?p" by (rule mult_right_mono[OF wp_pair_probe]) simp
  finally show ?thesis by (simp add: power2_eq_square)
qed

definition pair_eventual_ready where
  "pair_eventual_ready rT rC U e \<longleftrightarrow>
    (case e of (M,k,raw) \<Rightarrow> \<exists>j st. k = QueryIndexChallenge j st \<and>
      fmlookup M k = None \<and> pair_base_ok M \<and>
      channel_for_hash_map (fmupd k raw M) \<le> channel_for_hash_map U \<and>
      weighted_semantic_hit rT rC U st raw)"

definition pair_late_connection where
  "pair_late_connection U e \<longleftrightarrow>
    (case e of (M,k,raw) \<Rightarrow> \<exists>j st. k = QueryIndexChallenge j st \<and>
      hash_map_new_output_hit (weighted_semantic_interval_targets M \<union> {st})
        (channel_for_hash_map (fmupd k raw M)) (channel_for_hash_map U))"

lemma pair_eventual_recovery:
  assumes ready: "pair_eventual_ready rT rC U e"
    and no_hit: "\<not> pair_late_connection U e"
  shows "pair_insert_good rT rC e"
proof -
  obtain M k raw where e: "e = (M,k,raw)" by (cases e) auto
  obtain j st I where k: "k = QueryIndexChallenge j st"
    and fresh: "fmlookup M k = None" and base: "pair_base_ok M"
    and ext: "channel_for_hash_map (fmupd k raw M) \<le> channel_for_hash_map U"
    and family: "weighted_semantic_ready rT rC U st I"
    and hit: "raw \<in> query_index_raw_preimage I"
    using ready unfolding pair_eventual_ready_def e weighted_semantic_hit_def by auto
  have nt: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets M \<union> {st})
      (channel_for_hash_map (fmupd (QueryIndexChallenge j st) raw M)) (channel_for_hash_map U)"
    using no_hit unfolding pair_late_connection_def e k by simp
  have recovered: "weighted_semantic_ready rT rC M st I"
    by (rule weighted_semantic_first_insertion_recovery[OF _ nt family]) (use ext k in simp)
  show ?thesis unfolding pair_insert_good_def e
    using k fresh base recovered hit unfolding weighted_semantic_hit_def by auto
qed

definition pair_eventual_event where
  "pair_eventual_event rT rC out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some ((e1,e2),u) \<Rightarrow>
      pair_eventual_ready rT rC (HashMap u) e1 \<and>
      pair_eventual_ready rT rC (HashMap u) e2)"

definition pair_exception_event where
  "pair_exception_event out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some ((e1,e2),u) \<Rightarrow>
      pair_late_connection (HashMap u) e1 \<or> pair_late_connection (HashMap u) e2)"

lemma pair_eventual_event_split:
  "pair_eventual_event rT rC out \<Longrightarrow>
    pair_insert_event rT rC out \<or> pair_exception_event out"
  unfolding pair_eventual_event_def pair_insert_event_def pair_exception_event_def
  using pair_eventual_recovery by (auto split: option.splits prod.splits)

lemma wp_pair_eventual:
  "wp_event (pair_experiment C K k) (pair_eventual_event rT rC) s \<le>
    (nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
      nnreal size)^2 +
    wp_event (pair_experiment C K k) pair_exception_event s"
proof -
  have "wp_event (pair_experiment C K k) (pair_eventual_event rT rC) s \<le>
      wp_event (pair_experiment C K k)
        (\<lambda>out. pair_insert_event rT rC out \<or> pair_exception_event out) s"
    by (rule wp_event_mono) (rule pair_eventual_event_split)
  also have "... \<le> wp_event (pair_experiment C K k) (pair_insert_event rT rC) s +
      wp_event (pair_experiment C K k) pair_exception_event s"
    by (rule wp_event_union_bound)
  also have "... \<le>
      (nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
        nnreal size)^2 + wp_event (pair_experiment C K k) pair_exception_event s"
    by (rule add_right_mono[OF wp_pair_experiment])
  finally show ?thesis .
qed

lemma pair_probe_outcome:
  assumes "Some (e,t) \<in> set_dist (execute (pair_probe k) s)"
  obtains raw where "e = (HashMap s,k,raw)"
    "t = s\<lparr>HashMap := fmupd k raw (HashMap s)\<rparr>"
    "Some (raw,t) \<in> set_dist (execute (hash k) s)"
  using assms weighted_semantic_hash_state
  unfolding pair_probe_def
  by (auto elim!: set_dist_bindE)

lemma pair_target_card:
  "card (weighted_semantic_interval_targets M \<union> {st}) \<le> 5 * card (fmdom' M) + 1"
  using weighted_semantic_interval_targets_after_query_card[of 0 st undefined M]
  by (simp add: weighted_semantic_interval_targets_query_update)

lemma pair_late_connection_charge:
  fixes t :: "'f protocol_channel"
  assumes budget: "hash_target_program (weighted_semantic_interval_targets M \<union> {st}) q K"
    and map: "HashMap t = fmupd (QueryIndexChallenge j st) raw M"
  shows "wp_event K
    (\<lambda>out. case out of None \<Rightarrow> False | Some (_,u) \<Rightarrow>
      pair_late_connection (HashMap u) (M,QueryIndexChallenge j st,raw)) t \<le>
    nnreal (q * (5 * card (fmdom' M) + 1)) / nnreal size"
proof -
  let ?D = "weighted_semantic_interval_targets M \<union> {st}"
  have eq: "(\<lambda>out. case out of None \<Rightarrow> False | Some (_,u) \<Rightarrow>
      pair_late_connection (HashMap u) (M,QueryIndexChallenge j st,raw)) =
      hash_new_output_hit_event ?D t"
    unfolding pair_late_connection_def hash_new_output_hit_event_def
      hash_map_new_output_hit_def channel_for_hash_map_def map
    by (rule ext) (simp split: option.splits prod.splits)
  have "wp_event K (hash_new_output_hit_event ?D t) t \<le> hash_target_budget_value ?D q"
    using budget unfolding hash_target_program_def hash_target_budget_def by blast
  also have "... \<le> nnreal (q * (5 * card (fmdom' M) + 1)) / nnreal size"
    unfolding hash_target_budget_value_def
    by (rule nnreal_nat_divide_right_mono) (rule mult_left_mono[OF pair_target_card], simp)
  finally show ?thesis unfolding eq .
qed

lemma wp_pair_eventual_clean:
  "wp_event (pair_experiment C K k)
    (\<lambda>out. pair_eventual_event rT rC out \<and> \<not> pair_exception_event out) s \<le>
    (nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
      nnreal size)^2"
proof -
  have "wp_event (pair_experiment C K k)
      (\<lambda>out. pair_eventual_event rT rC out \<and> \<not> pair_exception_event out) s \<le>
      wp_event (pair_experiment C K k) (pair_insert_event rT rC) s"
    by (rule wp_event_mono) (use pair_eventual_event_split in blast)
  also have "... \<le>
      (nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC)) /
        nnreal size)^2" by (rule wp_pair_experiment)
  finally show ?thesis .
qed

text \<open>The following projection erases only ghost logging, not hash calls.\<close>

lemma pair_probe_projection:
  "(pair_probe k \<bind> (\<lambda>e. return (snd (snd e)))) = hash k"
  unfolding pair_probe_def
  apply (rule execute_inject[THEN iffD1], rule ext)
  apply (simp add: sm_bind_assoc sm_bind.rep_eq get.rep_eq dist_get_def)
  apply (rule dist_inject[THEN iffD1])
  apply (simp only: dist_bind.rep_eq o_def dist_delta_dist)
  apply (subst map_bind_delta_left_state)
   apply (auto simp: bind_cont_map_def)
  done

end

end
