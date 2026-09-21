theory Soundness_RO_Drift_Per_Key
 imports Soundness_FRI_Conditioned_Challenge_Relation
   Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_State_Relation
begin

section \<open>Constructor-aware drift-target cardinality\<close>

text \<open>The old bounds sum separate full-domain projections. A single key
  belongs to one constructor and contributes at most two values to their union.
  No drift target is removed; current-input components still cost at most two.\<close>

definition drift_key_values :: "'a protocol_hash_input \<Rightarrow> 'a set" where
 "drift_key_values k = (case k of
    TranscriptAbsorb p m \<Rightarrow> {p,m}
  | MerkleNode l r \<Rightarrow> {l,r}
  | QueryIndexChallenge i s \<Rightarrow> {s}
  | TraceFriChallenge i s \<Rightarrow> {s}
  | CompositionFriChallenge i s \<Rightarrow> {s}
  | AlphaChallenge i s \<Rightarrow> {s}
  | _ \<Rightarrow> {})"

lemma finite_drift_key_values[simp]: "finite (drift_key_values k)"
 by (cases k) (simp_all add: drift_key_values_def)

lemma card_drift_key_values: "card (drift_key_values k) \<le> 2"
 by (cases k) (simp_all add: drift_key_values_def card_insert_if)

lemma card_drift_key_union:
 "card (\<Union>k\<in>fmdom' M. drift_key_values k) \<le> 2*card (fmdom' M)"
proof -
 have "card (\<Union>k\<in>fmdom' M. drift_key_values k) \<le>
   (\<Sum>k\<in>fmdom' M. card (drift_key_values k))"
   by (rule card_UN_le) simp
 also have "... \<le> (\<Sum>k\<in>fmdom' M. 2)"
   by (rule sum_mono) (rule card_drift_key_values)
 also have "... = 2*card (fmdom' M)" by simp
 finally show ?thesis .
qed

context soundness
begin

lemma first_root_drift_subset:
 "first_root_relation_drift_targets M x \<subseteq>
   (\<Union>k\<in>fmdom' M. drift_key_values k) \<union> hash_input_component_values x"
 unfolding first_root_relation_drift_targets_def transcript_absorb_input_values_def
   transcript_absorb_message_values_def query_index_state_values_def
   hash_map_merkle_child_values_def channel_for_hash_map_def
   merkle_node_child_output_relation_def
 by (force simp: drift_key_values_def fmlookup_dom'_iff)

lemma conditioned_drift_subset:
 "conditioned_fri_relation_drift_targets M x \<subseteq>
   (\<Union>k\<in>fmdom' M. drift_key_values k) \<union> hash_input_component_values x"
 unfolding conditioned_fri_relation_drift_targets_def
   trace_fri_challenge_state_values_def composition_fri_challenge_state_values_def
 using first_root_drift_subset[of M x]
 by (fastforce simp: drift_key_values_def fmlookup_dom'_iff)

lemma alpha_drift_subset:
 "alpha_pivot_relation_drift_targets M x \<subseteq>
   (\<Union>k\<in>fmdom' M. drift_key_values k) \<union> hash_input_component_values x"
 unfolding alpha_pivot_relation_drift_targets_def alpha_challenge_state_values_def
 using first_root_drift_subset[of M x]
 by (fastforce simp: drift_key_values_def fmlookup_dom'_iff)

lemma drift_union_cap:
 "card ((\<Union>k\<in>fmdom' M. drift_key_values k) \<union> hash_input_component_values x)
   \<le> 2*card (fmdom' M)+2"
 using card_Un_le[of "(\<Union>k\<in>fmdom' M. drift_key_values k)"
   "hash_input_component_values x"]
   card_drift_key_union[of M] card_hash_input_component_values_le[of x]
 by linarith

lemma first_root_drift_card:
 "card (first_root_relation_drift_targets M x) \<le> 2*card (fmdom' M)+2"
 by (rule order_trans[OF card_mono[OF _ first_root_drift_subset] drift_union_cap]) simp

lemma conditioned_drift_card:
 "card (conditioned_fri_relation_drift_targets M x) \<le> 2*card (fmdom' M)+2"
 by (rule order_trans[OF card_mono[OF _ conditioned_drift_subset] drift_union_cap]) simp

lemma alpha_drift_card:
 "card (alpha_pivot_relation_drift_targets M x) \<le> 2*card (fmdom' M)+2"
 by (rule order_trans[OF card_mono[OF _ alpha_drift_subset] drift_union_cap]) simp

end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then () else error "Unexpected per-key drift dependency")
    @{thms soundness.first_root_drift_card soundness.conditioned_drift_card
      soundness.alpha_drift_card};
\<close>
end
