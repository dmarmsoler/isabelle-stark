theory Soundness_FRI_Correlated_Agreement_Query_Support
 imports Soundness_FRI_Correlated_Agreement_Fold
begin
section \<open>Same-support agreement along actual query paths\<close>
text \<open>
  A query contributes its actual residue at every layer. The sibling-pair
  closure covers the preceding support, so codeword agreement propagates
  backwards without requiring full-domain honest folding. The folded values
  used here come from the existing authenticated global residual definition.
\<close>
context soundness
begin

lemma fri_mca_pair_indices_card:
 assumes S: "S \<subseteq> {..<n}"
 shows "card (fri_mca_pair_indices n S) = 2 * card S"
proof -
 have fin: "finite S" using S finite_subset by blast
 have disjoint: "S \<inter> ((\<lambda>i. i+n) ` S) = {}" using S by auto
 have inj: "inj_on (\<lambda>i::nat. i+n) S" by (simp add: inj_on_def)
 show ?thesis unfolding fri_mca_pair_indices_def
   using card_Un_disjoint[OF fin finite_imageI[OF fin] disjoint]
     card_image[OF inj] by simp
qed

lemma fri_mca_mod_pair_cover:
 fixes Q :: "nat set"
 assumes pos: "0<n"
 shows "(\<lambda>q. q mod (2*n)) ` Q \<subseteq>
   fri_mca_pair_indices n ((\<lambda>q. q mod n) ` Q)"
proof
 fix r assume "r \<in> (\<lambda>q. q mod (2*n)) ` Q"
 then obtain q where q: "q\<in>Q" and r: "r=q mod (2*n)" by blast
 have rlt: "r < 2*n" using r pos by simp
 have eq: "r mod n = q mod n"
   unfolding r by (rule mod_mod_cancel) simp
 show "r \<in> fri_mca_pair_indices n ((\<lambda>q. q mod n) ` Q)"
 proof (cases "r<n")
   case True
   then have "r=q mod n" using eq by simp
   then show ?thesis using q unfolding fri_mca_pair_indices_def by blast
 next
   case False
   have small: "r-n<n" using False rlt by arith
   have split: "r=(r-n)+n" using False by arith
   have "r mod n = r-n" using small by (subst split) simp
   then have "r=q mod n+n" using eq split by simp
   then show ?thesis using q unfolding fri_mca_pair_indices_def by blast
 qed
qed

definition fri_mca_query_support :: "nat \<Rightarrow> nat set \<Rightarrow> nat set"
where "fri_mca_query_support i Q =
 (\<lambda>q. q mod length (fri_canonical_domain_at i)) ` Q"

lemma fri_mca_query_support_subset:
 assumes ep: "clength*scale=2^N" and bound: "i\<le>N"
 shows "fri_mca_query_support i Q \<subseteq> {..<length (fri_canonical_domain_at i)}"
 using fri_canonical_domain_at_pos[OF ep bound]
 unfolding fri_mca_query_support_def by auto

lemma fri_mca_query_support_pair_cover:
 assumes ep: "clength*scale=2^N" and active: "i<N"
 shows "fri_mca_query_support i Q \<subseteq>
   fri_mca_pair_indices (length (fri_canonical_domain_at (Suc i)))
     (fri_mca_query_support (Suc i) Q)"
 unfolding fri_mca_query_support_def fri_mca_canonical_lengths[OF ep active]
 by (rule fri_mca_mod_pair_cover) (rule fri_canonical_domain_at_pos[OF ep Suc_leI[OF active]])

lemma fri_mca_distance_of_agreement:
 fixes xs :: "'f list"
 assumes S: "S \<subseteq> {..<length xs}" and dp: "degree p \<le> k"
   and agree: "\<And>i. i\<in>S \<Longrightarrow> received i = poly p (xs ! i)"
 shows "fri_rs_distance_to_code k xs received + card S \<le> length xs"
proof -
 let ?word = "nth (map (poly p) xs)"
 have code: "?word \<in> fri_rs_code_functions k xs"
   using dp unfolding fri_rs_code_functions_def fri_rs_code_tables_def by blast
 have subset: "code_disagreement_indices {..<length xs} received ?word \<subseteq> {..<length xs} - S"
   using S agree unfolding code_disagreement_indices_def by auto
 have fin: "finite S" using S finite_subset by blast
 have "fri_rs_distance_to_code k xs received \<le>
     card (code_disagreement_indices {..<length xs} received ?word)"
   by (rule fri_rs_distance_to_code_le[OF code])
 also have "... \<le> card ({..<length xs} - S)" by (rule card_mono) (use subset in auto)
 finally show ?thesis using S fin card_mono[OF _ S]
   by (simp add: card_Diff_subset)
qed

lemma fri_mca_global_support_folds:
 assumes Q: "Q \<subseteq> fri_authenticated_global_residual_query_indices roots challenges layers"
   and active: "i < length challenges"
   and j: "j \<in> fri_mca_query_support (Suc i) Q"
 shows "fri_conditioned_layer_table (Suc i) (layers ! Suc i) ! j =
   fri_table_fold_value (challenges ! i) (fri_conditioned_layer_table i (layers ! i))
     (fri_canonical_domain_at i) (length (fri_canonical_domain_at i)) 1 j"
proof -
 have sub: "Q \<subseteq> fri_conditioned_query_indices roots i
   (fri_robust_conditioned_agreement_indices challenges layers i)"
   using Q fri_authenticated_global_residual_query_indices_subset_layer[OF active] by blast
 have jA: "j \<in> fri_robust_conditioned_agreement_indices challenges layers i"
   using j sub unfolding fri_mca_query_support_def fri_conditioned_query_indices_def by auto
 show ?thesis using jA
   unfolding fri_robust_conditioned_agreement_indices_def
     fri_fold_next_agreement_indices_def code_agreement_indices_def fri_folded_received_def by auto
qed

lemma fri_mca_global_subset_query_space:
 assumes active: "0 < length challenges"
 shows "fri_authenticated_global_residual_query_indices roots challenges layers \<subseteq> query_sample_space"
 using fri_authenticated_global_residual_query_indices_subset_layer[OF active, of roots layers]
   fri_conditioned_query_indices_subset by blast

lemma fri_mca_query_support_zero:
 assumes Q: "Q \<subseteq> query_sample_space"
 shows "fri_mca_query_support 0 Q = Q"
proof -
 have bound: "\<And>q. q\<in>Q \<Longrightarrow> q < length (fri_canonical_domain_at 0)"
   using Q unfolding query_sample_space_def query_sample_space_size_def
     fri_canonical_domain_at_length by auto
 have eq: "\<And>q. q\<in>Q \<Longrightarrow> q mod length (fri_canonical_domain_at 0) = q"
   using bound by simp
 show ?thesis unfolding fri_mca_query_support_def using eq by auto
qed


lemma fri_mca_chain_support_agreement:
 assumes ep: "clength*scale=2^N"
   and count: "length challenges = ceil_log (Suc d)"
   and fit: "length challenges \<le> N"
   and terminal: "layers ! length challenges =
     replicate (length (fri_canonical_domain_at (length challenges))) final_value"
   and good: "\<And>j. j < length challenges \<Longrightarrow>
     challenges ! j \<notin> fri_mca_layer_bad_challenges d (ts j) j (layers ! j)"
   and large: "\<And>j. j < length challenges \<Longrightarrow>
     length (fri_canonical_domain_at (Suc j)) \<le> card (fri_mca_query_support (Suc j) Q) + ts j"
   and Q: "Q \<subseteq> fri_authenticated_global_residual_query_indices roots challenges layers"
   and bound: "i \<le> length challenges"
 shows "\<exists>p. degree p \<le> fri_degree_after i (fri_padded_degree_bound d) \<and>
   (\<forall>j\<in>fri_mca_query_support i Q.
     fri_conditioned_layer_table i (layers ! i) ! j = poly p (fri_canonical_domain_at i ! j))"
proof (rule inc_induct[OF bound])
 let ?m = "length challenges"
 show "\<exists>p. degree p \<le> fri_degree_after ?m (fri_padded_degree_bound d) \<and>
   (\<forall>j\<in>fri_mca_query_support ?m Q.
     fri_conditioned_layer_table ?m (layers ! ?m) ! j =
       poly p (fri_canonical_domain_at ?m ! j))"
 proof (intro exI[where x="[:final_value:]"] conjI)
   show "degree [:final_value:] \<le> fri_degree_after ?m (fri_padded_degree_bound d)" by simp
   show "\<forall>j\<in>fri_mca_query_support ?m Q.
     fri_conditioned_layer_table ?m (layers ! ?m) ! j = poly [:final_value:] (fri_canonical_domain_at ?m ! j)"
     using fri_mca_query_support_subset[OF ep fit, of Q]
     by (auto simp: terminal fri_conditioned_layer_table_nth)
 qed
next
 fix j assume ij: "i\<le>j" and active: "j < length challenges"
   and ih: "\<exists>p. degree p \<le> fri_degree_after (Suc j) (fri_padded_degree_bound d) \<and>
     (\<forall>a\<in>fri_mca_query_support (Suc j) Q.
       fri_conditioned_layer_table (Suc j) (layers ! Suc j) ! a =
         poly p (fri_canonical_domain_at (Suc j) ! a))"
 obtain q where dq: "degree q \<le> fri_degree_after (Suc j) (fri_padded_degree_bound d)"
   and aq: "\<forall>a\<in>fri_mca_query_support (Suc j) Q.
       fri_conditioned_layer_table (Suc j) (layers ! Suc j) ! a =
         poly q (fri_canonical_domain_at (Suc j) ! a)" using ih by blast
 have jN: "j<N" using active fit by linarith
 have jdegree: "j < ceil_log (Suc d)" using active count by simp
 have S: "fri_mca_query_support (Suc j) Q \<subseteq> {..<length (fri_canonical_domain_at (Suc j))}"
   by (rule fri_mca_query_support_subset[OF ep Suc_leI[OF jN]])
 have fold: "\<And>a. a\<in>fri_mca_query_support (Suc j) Q \<Longrightarrow>
     fri_table_fold_value (challenges ! j) (fri_conditioned_layer_table j (layers ! j))
       (fri_canonical_domain_at j) (length (fri_canonical_domain_at j)) 1 a =
     poly q (fri_canonical_domain_at (Suc j) ! a)"
   using aq fri_mca_global_support_folds[OF Q active] by simp
 obtain p where dp: "degree p \<le> fri_degree_after j (fri_padded_degree_bound d)"
   and ap: "\<forall>a\<in>fri_mca_pair_indices (length (fri_canonical_domain_at (Suc j)))
       (fri_mca_query_support (Suc j) Q).
     fri_conditioned_layer_table j (layers ! j) ! a = poly p (fri_canonical_domain_at j ! a)"
   by (rule fri_mca_layer_good_propagates[OF jdegree good[OF active] S large[OF active] dq fold])
 have sub: "fri_mca_query_support j Q \<subseteq>
   fri_mca_pair_indices (length (fri_canonical_domain_at (Suc j))) (fri_mca_query_support (Suc j) Q)"
   by (rule fri_mca_query_support_pair_cover[OF ep jN])
 show "\<exists>p. degree p \<le> fri_degree_after j (fri_padded_degree_bound d) \<and>
   (\<forall>a\<in>fri_mca_query_support j Q.
     fri_conditioned_layer_table j (layers ! j) ! a = poly p (fri_canonical_domain_at j ! a))"
   using dp ap sub by blast
qed



end
end
