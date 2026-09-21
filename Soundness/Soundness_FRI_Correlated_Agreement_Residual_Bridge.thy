theory Soundness_FRI_Correlated_Agreement_Residual_Bridge
 imports Soundness_FRI_Correlated_Agreement_Query_Support
begin
section \<open>Conditional authenticated residual bound with exact modulo envelopes\<close>
text \<open>
  This layer changes only the internal clean-event decomposition. It does not
  charge the new events in the adaptive random-oracle experiment and does not
  change a public soundness theorem. Initial distance is an explicit branch
  condition, not a new public premise. Old balanced-clean attainability is
  not decided by the new conditional ceiling.
\<close>
context soundness
begin

lemma fri_mca_mod_image_card_bound:
 fixes n k :: nat and Q :: "nat set"
 assumes Q: "Q \<subseteq> query_sample_space" and pos: "0<n"
   and image: "card ((\<lambda>q. q mod n) ` Q) \<le> k"
 shows "card Q \<le> modulo_preimage_card_envelope query_sample_space_size n k"
proof -
 let ?S = "(\<lambda>q. q mod n) ` Q"
 have S: "?S \<subseteq> {..<n}" using pos by auto
 have sub: "Q \<subseteq> {q. q < query_sample_space_size \<and> q mod n \<in> ?S}"
   using Q unfolding query_sample_space_def by auto
 have "card Q \<le> card {q. q < query_sample_space_size \<and> q mod n \<in> ?S}"
   by (rule card_mono) (use sub in auto)
 also have "... \<le> modulo_preimage_card_envelope query_sample_space_size n (card ?S)"
   by (rule card_modulo_set_preimage_le_envelope[OF pos S])
 also have "... \<le> modulo_preimage_card_envelope query_sample_space_size n k"
   by (rule modulo_preimage_card_envelope_mono[OF image])
 finally show ?thesis .
qed

lemma fri_mca_large_support_from_card:
 assumes ep: "clength*scale=2^N" and bound: "i\<le>N"
   and Q: "Q \<subseteq> query_sample_space"
   and high: "modulo_preimage_card_envelope query_sample_space_size
     (length (fri_canonical_domain_at i))
     (length (fri_canonical_domain_at i) - Suc t) < card Q"
 shows "length (fri_canonical_domain_at i) \<le> card (fri_mca_query_support i Q)+t"
proof (rule ccontr)
 assume "\<not> length (fri_canonical_domain_at i) \<le> card (fri_mca_query_support i Q)+t"
 then have card: "card (fri_mca_query_support i Q) \<le> length (fri_canonical_domain_at i) - Suc t"
   by arith
 have "card Q \<le> modulo_preimage_card_envelope query_sample_space_size
     (length (fri_canonical_domain_at i))
     (length (fri_canonical_domain_at i) - Suc t)"
   by (rule fri_mca_mod_image_card_bound[OF Q fri_canonical_domain_at_pos[OF ep bound]])
     (use card in \<open>simp only: fri_mca_query_support_def\<close>)
 then show False using high by simp
qed

definition fri_mca_support_threshold :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
where "fri_mca_support_threshold m ts =
 Max (insert 0 ((\<lambda>i. modulo_preimage_card_envelope query_sample_space_size
    (length (fri_canonical_domain_at (Suc i)))
    (length (fri_canonical_domain_at (Suc i)) - Suc (ts i))) ` {..<m}))"

lemma fri_mca_support_threshold_ge:
 assumes "i<m"
 shows "modulo_preimage_card_envelope query_sample_space_size
    (length (fri_canonical_domain_at (Suc i)))
    (length (fri_canonical_domain_at (Suc i)) - Suc (ts i))
   \<le> fri_mca_support_threshold m ts"
 unfolding fri_mca_support_threshold_def
 by (rule Max_ge) (use assms in auto)

definition fri_mca_residual_index_bound :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where "fri_mca_residual_index_bound d ts r =
 max (length (fri_canonical_domain_at 0) - Suc r)
   (fri_mca_support_threshold (ceil_log (Suc d)) ts)"

lemma fri_mca_global_residual_card:
 assumes ep: "clength*scale=2^N"
   and count: "length challenges = ceil_log (Suc d)"
   and active: "0 < length challenges"
   and fit: "length challenges \<le> N"
   and terminal: "layers ! length challenges =
     replicate (length (fri_canonical_domain_at (length challenges))) final_value"
   and good: "\<And>j. j < length challenges \<Longrightarrow>
     challenges ! j \<notin> fri_mca_layer_bad_challenges d (ts j) j (layers ! j)"
   and far: "r < fri_rs_distance_to_code (fri_padded_degree_bound d)
     (fri_canonical_domain_at 0) (nth (fri_conditioned_layer_table 0 (layers ! 0)))"
 shows "card (fri_authenticated_global_residual_query_indices roots challenges layers)
   \<le> fri_mca_residual_index_bound d ts r"
proof (rule ccontr)
 let ?G = "fri_authenticated_global_residual_query_indices roots challenges layers"
 assume "\<not> card ?G \<le> fri_mca_residual_index_bound d ts r"
 then have high: "fri_mca_residual_index_bound d ts r < card ?G" by simp
 have G: "?G \<subseteq> query_sample_space" by (rule fri_mca_global_subset_query_space[OF active])
 have large: "\<And>j. j < length challenges \<Longrightarrow>
   length (fri_canonical_domain_at (Suc j)) \<le> card (fri_mca_query_support (Suc j) ?G)+ts j"
 proof -
   fix j assume j: "j < length challenges"
   have jN: "Suc j\<le>N" using j fit by linarith
   have h: "modulo_preimage_card_envelope query_sample_space_size
       (length (fri_canonical_domain_at (Suc j)))
       (length (fri_canonical_domain_at (Suc j)) - Suc (ts j)) < card ?G"
     using fri_mca_support_threshold_ge[OF j, of ts] high
     unfolding fri_mca_residual_index_bound_def count by linarith
   show "length (fri_canonical_domain_at (Suc j)) \<le>
     card (fri_mca_query_support (Suc j) ?G)+ts j"
     by (rule fri_mca_large_support_from_card[OF ep jN G h])
 qed
 obtain p where dp: "degree p \<le> fri_padded_degree_bound d"
   and ap: "\<forall>j\<in>?G. fri_conditioned_layer_table 0 (layers ! 0) ! j =
     poly p (fri_canonical_domain_at 0 ! j)"
   using fri_mca_chain_support_agreement[OF ep count fit terminal good large subset_refl, of 0]
   by (fastforce simp: fri_mca_query_support_zero[OF G])
 have sub: "?G \<subseteq> {..<length (fri_canonical_domain_at 0)}"
   using fri_mca_query_support_subset[OF ep, of 0 ?G]
     fri_mca_query_support_zero[OF G] by simp
 have sum: "fri_rs_distance_to_code (fri_padded_degree_bound d)
     (fri_canonical_domain_at 0) (nth (fri_conditioned_layer_table 0 (layers ! 0))) +
     card ?G \<le> length (fri_canonical_domain_at 0)"
   by (rule fri_mca_distance_of_agreement[OF sub dp]) (use ap in simp)
 have bound: "card ?G \<le> length (fri_canonical_domain_at 0) - Suc r"
   using sum far by arith
 show False using high bound unfolding fri_mca_residual_index_bound_def by linarith
qed

lemma fri_mca_builder_global_residual_card:
 assumes ep: "clength*scale=2^N"
   and count: "length challenges = ceil_log (Suc d)"
   and lengths: "length roots = length challenges"
   and active: "0 < length challenges"
   and fit: "length challenges \<le> N"
   and good: "\<not> fri_mca_chain_bad_event d ts roots challenges state"
   and far: "r < fri_rs_distance_to_code (fri_padded_degree_bound d)
     (fri_canonical_domain_at 0)
     (nth (conceptual_table state (roots ! 0) (length (fri_canonical_domain_at 0))))"
 shows "card (fri_authenticated_global_residual_query_indices roots challenges
   (fri_builder_conceptual_layers roots state final_value)) \<le> fri_mca_residual_index_bound d ts r"
proof (rule fri_mca_global_residual_card[OF ep count active fit])
 let ?layers = "fri_builder_conceptual_layers roots state final_value"
 show "?layers ! length challenges =
   replicate (length (fri_canonical_domain_at (length challenges))) final_value"
   using lengths fri_builder_conceptual_layers_final[of roots state final_value] by simp
 show "\<And>j. j<length challenges \<Longrightarrow> challenges ! j \<notin> fri_mca_layer_bad_challenges d (ts j) j (?layers ! j)"
   by (rule fri_mca_chain_not_badD[OF good lengths])
 have initial: "fri_conditioned_layer_table 0 (?layers ! 0) =
   conceptual_table state (roots ! 0) (length (fri_canonical_domain_at 0))"
   using lengths active
   by (simp add: fri_builder_conceptual_layers_at fri_conditioned_layer_table_def conceptual_table_def)
 show "r < fri_rs_distance_to_code (fri_padded_degree_bound d) (fri_canonical_domain_at 0)
     (nth (fri_conditioned_layer_table 0 (?layers ! 0)))"
   unfolding initial by (rule far)
qed

theorem fri_mca_authenticated_residual_bridge:
 assumes actual: "fri_authenticated_global_chain_realizable d N roots challenges final_value
     query_idxs round_layers builder_state final_state"
   and active: "0 < length challenges"
   and good: "\<not> fri_mca_chain_bad_event d ts roots challenges builder_state"
   and far: "r < fri_rs_distance_to_code (fri_padded_degree_bound d)
     (fri_canonical_domain_at 0)
     (nth (conceptual_table builder_state (roots ! 0) (length (fri_canonical_domain_at 0))))"
 defines "survivors \<equiv> fri_authenticated_global_residual_query_indices roots challenges
     (fri_builder_conceptual_layers roots builder_state final_value)"
 shows "query_idxs \<in> fri_conditioned_query_lists survivors"
   and "survivors \<subseteq> query_sample_space"
   and "card survivors \<le> fri_mca_residual_index_bound d ts r"
   and "card (query_index_raw_preimage survivors) \<le>
     query_raw_preimage_card_envelope (fri_mca_residual_index_bound d ts r)"
proof -
 show "query_idxs \<in> fri_conditioned_query_lists survivors" unfolding survivors_def
   by (rule fri_authenticated_global_chain_realizable_imp_global_rectangle[OF actual])
 show survivors: "survivors \<subseteq> query_sample_space" unfolding survivors_def
   by (rule fri_mca_global_subset_query_space[OF active])
 have ep: "clength*scale=2^N" and count: "length challenges = ceil_log (Suc d)"
   and fit: "length challenges \<le> N"
   and chain: "generic_fri_recorded_value_chain_evidence roots challenges final_value query_idxs round_layers"
   using actual unfolding fri_authenticated_global_chain_realizable_def by auto
 have lengths: "length roots = length challenges"
   using chain unfolding generic_fri_recorded_value_chain_evidence_def by simp
 show card: "card survivors \<le> fri_mca_residual_index_bound d ts r" unfolding survivors_def
   by (rule fri_mca_builder_global_residual_card[OF ep count lengths active fit good far])
 have "card (query_index_raw_preimage survivors) \<le> query_raw_preimage_card_envelope (card survivors)"
   by (rule card_query_index_raw_preimage_le_query_envelope[OF survivors])
 also have "... \<le> query_raw_preimage_card_envelope (fri_mca_residual_index_bound d ts r)"
   by (rule query_raw_preimage_card_envelope_mono[OF card])
 finally show "card (query_index_raw_preimage survivors) \<le>
     query_raw_preimage_card_envelope (fri_mca_residual_index_bound d ts r)" .
qed

end
end
