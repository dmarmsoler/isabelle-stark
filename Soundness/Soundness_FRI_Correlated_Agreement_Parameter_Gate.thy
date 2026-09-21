theory Soundness_FRI_Correlated_Agreement_Parameter_Gate
 imports Soundness_FRI_Correlated_Agreement_Residual_Bridge
begin
section \<open>Bounded correlated-agreement parameter gate\<close>
text \<open>
  The quarter-radius binary bound applies to every active canonical layer.
  The scale-64 ceiling below excludes the new correlated-agreement event,
  not merely the earlier balanced far-to-close event. Initial distance stays
  explicit. No adaptive-oracle probability or public security bound is proved.
\<close>
context soundness
begin

definition fri_mca_quarter_radii :: "nat \<Rightarrow> nat"
where "fri_mca_quarter_radii i = length (fri_canonical_domain_at (Suc i)) div 4"

lemma fri_mca_quarter_layer_card:
 assumes ep: "clength*scale=2^N" and active: "i<ceil_log (Suc d)"
   and fit: "ceil_log (Suc d)\<le>N"
   and rate: "4*fri_padded_degree_bound d \<le> clength*scale"
 shows "card (fri_mca_online_bad_challenges d (fri_mca_quarter_radii i) i state rt)
     \<le> max 1 (2*fri_mca_quarter_radii i)"
proof -
 have iN: "i<N" using active fit by linarith
 have radius: "3*fri_mca_quarter_radii i +
   fri_degree_after (Suc i) (fri_padded_degree_bound d) <
     length (fri_canonical_domain_at (Suc i))"
   by (rule fri_mca_canonical_quarter_radius[OF ep active fit rate])
     (simp add: fri_mca_quarter_radii_def)
 show ?thesis by (rule fri_mca_online_bad_card[OF ep iN radius])
qed

lemma fri_mca_quarter_bad_strict:
 assumes ep: "clength*scale=2^N" and active: "i<ceil_log (Suc d)"
   and fit: "Suc (ceil_log (Suc d))\<le>N"
   and rate: "4*fri_padded_degree_bound d \<le> clength*scale"
 shows "card (fri_mca_online_bad_challenges d (fri_mca_quarter_radii i) i state rt)
   < card (UNIV :: 'f set)"
proof -
 let ?n = "length (fri_canonical_domain_at (Suc i))"
 have i2: "i+2\<le>N" using active fit by linarith
 have n2: "2\<le>?n"
 proof -
   have nexp: "N-Suc i = Suc (N-i-2)" using i2 by arith
   show ?thesis using fri_canonical_domain_at_length_power[OF ep, of "Suc i"] i2
     by (simp add: nexp)
 qed
 have distinct: "distinct (fri_canonical_domain_at (Suc i))"
   by (rule distinct_fri_canonical_domain_at[OF ep]) (use i2 in arith)
 have nfield: "?n \<le> card (UNIV :: 'f set)"
   using card_mono[of "UNIV :: 'f set" "set (fri_canonical_domain_at (Suc i))"] distinct
   by (simp add: distinct_card)
 have cap: "max 1 (2*(?n div 4)) < ?n"
 proof -
   have "4*(?n div 4) \<le> ?n" by simp
   then show ?thesis using n2 by arith
 qed
 have "card (fri_mca_online_bad_challenges d (fri_mca_quarter_radii i) i state rt)
     \<le> max 1 (2*fri_mca_quarter_radii i)"
   by (rule fri_mca_quarter_layer_card[OF ep active _ rate]) (use fit in arith)
 also have "... < ?n" using cap by (simp add: fri_mca_quarter_radii_def)
 also have "... \<le> card (UNIV :: 'f set)" by (rule nfield)
 finally show ?thesis .
qed

lemma fri_mca_scale64_log[simp]: "ceil_log 1024 = 10"
 by code_simp

lemma fri_mca_ten_indices: "{..<10::nat} = set [0,1,2,3,4,5,6,7,8,9]"
 by (auto simp: numeral_eq_Suc lessThan_Suc)

lemma fri_mca_scale64_support_threshold:
 assumes ep: "clength*scale=2^16" and qsize: "query_sample_space_size=65472"
 shows "fri_mca_support_threshold 10 fri_mca_quarter_radii = 49150"
 unfolding fri_mca_support_threshold_def fri_mca_ten_indices
   fri_mca_quarter_radii_def fri_canonical_domain_at_length ep qsize
   modulo_preimage_card_envelope_def
 by simp

lemma fri_mca_scale64_residual_bound:
 assumes ep: "clength*scale=2^16" and qsize: "query_sample_space_size=65472"
 shows "fri_mca_residual_index_bound 1023 fri_mca_quarter_radii 13544 = 51991"
 unfolding fri_mca_residual_index_bound_def fri_mca_scale64_log
   fri_mca_scale64_support_threshold[OF ep qsize] fri_canonical_domain_at_length ep
 by (simp add: fri_mca_scale64_support_threshold[OF ep qsize])

lemma fri_mca_scale64_query_size:
 assumes ep: "clength*scale=2^16" and scale64: "scale=64" and powers2: "powers=2"
 shows "query_sample_space_size=65472"
proof -
  have eq: "query_sample_space_size = clength*scale - Max (set [0..<powers])*scale"
    by (rule query_sample_space_size_def)
  have mx: "Max (set [0..<2::nat]) = 1" by code_simp
  show ?thesis
    apply (subst eq)
    apply (subst ep)
    apply (subst powers2)
    apply (subst mx)
    apply (subst scale64)
    by simp
qed

lemma fri_mca_scale64_challenge_envelopes:
 assumes ep: "clength*scale=2^16"
 shows "(\<Sum>i<10. max 1 (2*fri_mca_quarter_radii i)) = 32736"
 unfolding fri_mca_ten_indices fri_mca_quarter_radii_def
   fri_canonical_domain_at_length ep
 by simp

lemma fri_mca_scale64_online_card_sum:
 assumes ep: "clength*scale=2^16"
 shows "(\<Sum>i<10. card (fri_mca_online_bad_challenges 1023 (fri_mca_quarter_radii i)
   i (states i) (rts i))) \<le> 32736"
proof -
 have rate: "4*fri_padded_degree_bound 1023 \<le> clength*scale"
   by (simp add: fri_padded_degree_bound_def ep)
 have "(\<Sum>i<10. card (fri_mca_online_bad_challenges 1023 (fri_mca_quarter_radii i)
   i (states i) (rts i))) \<le> (\<Sum>i<10. max 1 (2*fri_mca_quarter_radii i))"
 proof (rule sum_mono)
   fix i :: nat assume i: "i\<in>{..<10}"
   show "card (fri_mca_online_bad_challenges 1023 (fri_mca_quarter_radii i)
       i (states i) (rts i)) \<le> max 1 (2*fri_mca_quarter_radii i)"
     by (rule fri_mca_quarter_layer_card[OF ep _ _ rate])
       (use i in \<open>simp_all\<close>)
 qed
 also have "... = 32736" by (rule fri_mca_scale64_challenge_envelopes[OF ep])
 finally show ?thesis .
qed

theorem fri_mca_scale64_authenticated_ceiling:
 assumes actual: "fri_authenticated_global_chain_realizable 1023 16 roots challenges final_value
     query_idxs round_layers builder_state final_state"
   and scale64: "scale=64" and powers2: "powers=2"
   and good: "\<not> fri_mca_chain_bad_event 1023 fri_mca_quarter_radii roots challenges builder_state"
   and far: "13544 < fri_rs_distance_to_code (fri_padded_degree_bound 1023)
     (fri_canonical_domain_at 0)
     (nth (conceptual_table builder_state (roots ! 0) (length (fri_canonical_domain_at 0))))"
 defines "survivors \<equiv> fri_authenticated_global_residual_query_indices roots challenges
     (fri_builder_conceptual_layers roots builder_state final_value)"
 shows "query_idxs \<in> fri_conditioned_query_lists survivors"
   and "card survivors \<le> 51991"
   and "card (query_index_raw_preimage survivors) \<le> query_raw_preimage_card_envelope 51991"
proof -
 have ep: "clength*scale=2^16"
   and count: "length challenges=ceil_log (Suc 1023)"
   using actual unfolding fri_authenticated_global_chain_realizable_def by auto
 have active: "0<length challenges" by (simp add: count)
 have qsize: "query_sample_space_size=65472"
   by (rule fri_mca_scale64_query_size[OF ep scale64 powers2])
 have bound: "fri_mca_residual_index_bound 1023 fri_mca_quarter_radii 13544 = 51991"
   by (rule fri_mca_scale64_residual_bound[OF ep qsize])
 show "query_idxs \<in> fri_conditioned_query_lists survivors"
   unfolding survivors_def by (rule fri_mca_authenticated_residual_bridge(1)[OF actual active good far])
 show "card survivors \<le> 51991"
   using fri_mca_authenticated_residual_bridge(3)[OF actual active good far]
   by (simp add: survivors_def bound)
 show "card (query_index_raw_preimage survivors) \<le> query_raw_preimage_card_envelope 51991"
   using fri_mca_authenticated_residual_bridge(4)[OF actual active good far]
   by (simp add: survivors_def bound)
qed

end
end
