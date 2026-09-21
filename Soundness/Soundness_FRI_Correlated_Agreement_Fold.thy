theory Soundness_FRI_Correlated_Agreement_Fold
  imports Soundness_FRI_Binary_Correlated_Agreement
    Soundness_FRI_Authenticated_Global_Chain_Audit
begin
section \<open>Actual folding and prefix-stable correlated-agreement events\<close>
text \<open>
  The bad event is a proof decomposition, not a new verifier check. It is
  counted for arbitrary current tables, including close ones, and for all
  field challenges. Its clean complement preserves agreement on both members
  of each queried sibling pair. Prefix stability uses the existing Merkle
  path-target exclusion; it is not an unconditional random-oracle claim.
\<close>
context soundness
begin

definition fri_mca_pair_indices :: "nat \<Rightarrow> nat set \<Rightarrow> nat set"
where "fri_mca_pair_indices n S = S \<union> ((\<lambda>i. i+n) ` S)"

definition fri_mca_even_component :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f"
where "fri_mca_even_component len xs current i =
  fst (fri_fold_coeff_pair (current ! i)
    (current ! fri_sibling_index len i) (fri_fold_denominator (xs ! i) 1))"

definition fri_mca_odd_component :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f"
where "fri_mca_odd_component len xs current i =
  snd (fri_fold_coeff_pair (current ! i)
    (current ! fri_sibling_index len i) (fri_fold_denominator (xs ! i) 1))"

lemma fri_mca_actual_fold_affine:
 "fri_table_fold_value b current xs len pw i =
  fri_mca_even_component len xs current i +
    b * fri_mca_odd_component len xs current i"
 by (simp add: fri_table_fold_value_def fri_fold_value_def
   fri_mca_even_component_def fri_mca_odd_component_def fri_fold_coeff_pair_def)

definition fri_mca_parent_polynomial :: "'f poly \<Rightarrow> 'f poly \<Rightarrow> 'f poly"
where "fri_mca_parent_polynomial A C =
 pcompose A [:0,0,1:] + [:0,1:] * pcompose C [:0,0,1:]"

lemma fri_mca_parent_eval:
 "poly (fri_mca_parent_polynomial A C) x = poly A (x^2) + x * poly C (x^2)"
 by (simp add: fri_mca_parent_polynomial_def poly_pcompose power2_eq_square)

lemma fri_mca_parent_degree:
 assumes "degree A \<le> k" "degree C \<le> k"
 shows "degree (fri_mca_parent_polynomial A C) \<le> 2*k+1"
proof -
 have e: "degree (pcompose A [:0,0,1:]) \<le> 2*k"
   using degree_pcompose_le[of A "[:0,0,1:]"] assms(1) by simp
 have o: "degree ([:0,1:] * pcompose C [:0,0,1:]) \<le> 2*k+1"
   using degree_mult_le[of "[:0,1:]" "pcompose C [:0,0,1:]"]
     degree_pcompose_le[of C "[:0,0,1:]"] assms(2) by simp
 show ?thesis unfolding fri_mca_parent_polynomial_def
   using degree_add_le_max[of "pcompose A [:0,0,1:]" "[:0,1:] * pcompose C [:0,0,1:]"]
     e o by linarith
qed

lemma fri_mca_parent_coeff_pair:
 assumes x: "x \<noteq> 0"
 shows "fri_fold_coeff_pair
   (poly (fri_mca_parent_polynomial A C) x)
   (poly (fri_mca_parent_polynomial A C) (-x)) (2*x)
   = (poly A (x^2), poly C (x^2))"
 using x two_nonzero
 by (simp add: fri_fold_coeff_pair_def fri_mca_parent_eval
   add_divide_distrib diff_divide_distrib)

lemma fri_mca_sibling_half:
 assumes "i < n"
 shows "fri_sibling_index (2*n) i = i+n"
 using assms by (simp add: fri_sibling_index_def)

lemma fri_mca_pair_indices_subset:
 assumes "S \<subseteq> {..<n}"
 shows "fri_mca_pair_indices n S \<subseteq> {..<2*n}"
 using assms by (auto simp: fri_mca_pair_indices_def)

lemma fri_mca_components_reconstruct_pairs:
 assumes lengths: "len = 2 * length next_xs"
   and sub: "S \<subseteq> {..<length next_xs}"
   and squares: "\<And>i. i \<in> S \<Longrightarrow> next_xs ! i = (xs ! i)^2"
   and siblings: "\<And>i. i \<in> S \<Longrightarrow> xs ! (i + length next_xs) = -(xs ! i)"
   and nonzero: "\<And>i. i \<in> S \<Longrightarrow> xs ! i \<noteq> 0"
   and agree: "\<And>i. i \<in> S \<Longrightarrow>
      fri_mca_even_component len xs current i = poly A (next_xs ! i) \<and>
      fri_mca_odd_component len xs current i = poly C (next_xs ! i)"
 shows "\<forall>j\<in>fri_mca_pair_indices (length next_xs) S.
    current ! j = poly (fri_mca_parent_polynomial A C) (xs ! j)"
proof -
 have pair: "\<And>i. i\<in>S \<Longrightarrow>
     current ! i = poly (fri_mca_parent_polynomial A C) (xs ! i) \<and>
     current ! (i+length next_xs) =
       poly (fri_mca_parent_polynomial A C) (xs ! (i+length next_xs))"
 proof -
   fix i assume i: "i\<in>S"
   have bound: "i < length next_xs" using i sub by auto
   have sibling: "fri_sibling_index len i = i+length next_xs"
     unfolding lengths by (rule fri_mca_sibling_half[OF bound])
   have coeff: "fri_fold_coeff_pair (current ! i)
      (current ! fri_sibling_index len i) (2*(xs ! i)) =
      (poly A ((xs ! i)^2), poly C ((xs ! i)^2))"
     using agree[OF i] squares[OF i]
     by (simp add: fri_mca_even_component_def fri_mca_odd_component_def
       fri_fold_denominator_def prod_eq_iff)
   have "current ! i = poly (fri_mca_parent_polynomial A C) (xs ! i) \<and>
       current ! fri_sibling_index len i =
         poly (fri_mca_parent_polynomial A C) (-(xs ! i))"
     using nonzero[OF i] two_nonzero coeff
       fri_mca_parent_coeff_pair[OF nonzero[OF i], of A C]
     by (metis fri_fold_coeff_pair_injective mult_eq_0_iff)
   then show "current ! i = poly (fri_mca_parent_polynomial A C) (xs ! i) \<and>
     current ! (i+length next_xs) =
       poly (fri_mca_parent_polynomial A C) (xs ! (i+length next_xs))"
     using sibling siblings[OF i] by simp
 qed
 show ?thesis using pair unfolding fri_mca_pair_indices_def by blast
qed

definition fri_mca_fold_bad_challenges ::
 "nat \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f set"
where "fri_mca_fold_bad_challenges k next_xs len xs current t =
 {b. \<exists>S. S \<subseteq> {..<length next_xs} \<and> length next_xs \<le> card S + t \<and>
   (\<exists>q. degree q \<le> k \<and>
     (\<forall>i\<in>S. fri_table_fold_value b current xs len 1 i = poly q (next_xs ! i))) \<and>
   \<not>(\<exists>p. degree p \<le> 2*k+1 \<and>
     (\<forall>i\<in>fri_mca_pair_indices (length next_xs) S.
       current ! i = poly p (xs ! i)))}"

lemma fri_mca_fold_bad_subset:
 assumes lengths: "len = 2 * length next_xs"
   and squares: "\<And>i. i < length next_xs \<Longrightarrow> next_xs ! i = (xs ! i)^2"
   and siblings: "\<And>i. i < length next_xs \<Longrightarrow> xs ! (i + length next_xs) = -(xs ! i)"
   and nonzero: "\<And>i. i < length next_xs \<Longrightarrow> xs ! i \<noteq> 0"
 shows "fri_mca_fold_bad_challenges k next_xs len xs current t \<subseteq>
   fri_binary_mca_bad_challenges next_xs k
     (fri_mca_even_component len xs current)
     (fri_mca_odd_component len xs current) t"
proof
 fix b assume b: "b \<in> fri_mca_fold_bad_challenges k next_xs len xs current t"
 then obtain S q where S: "S \<subseteq> {..<length next_xs}"
   and large: "length next_xs \<le> card S+t" and dq: "degree q \<le> k"
   and agree: "\<forall>i\<in>S. fri_table_fold_value b current xs len 1 i = poly q (next_xs ! i)"
   and no_parent: "\<not>(\<exists>p. degree p \<le> 2*k+1 \<and>
     (\<forall>i\<in>fri_mca_pair_indices (length next_xs) S. current ! i = poly p (xs ! i)))"
   unfolding fri_mca_fold_bad_challenges_def by blast
 have no_pair: "\<not>(\<exists>A C. degree A \<le> k \<and> degree C \<le> k \<and>
   (\<forall>i\<in>S. fri_mca_even_component len xs current i = poly A (next_xs ! i) \<and>
     fri_mca_odd_component len xs current i = poly C (next_xs ! i)))"
 proof
   assume "\<exists>A C. degree A \<le> k \<and> degree C \<le> k \<and>
     (\<forall>i\<in>S. fri_mca_even_component len xs current i = poly A (next_xs ! i) \<and>
       fri_mca_odd_component len xs current i = poly C (next_xs ! i))"
   then obtain A C where dA: "degree A \<le> k" and dC: "degree C \<le> k"
     and ac: "\<And>i. i\<in>S \<Longrightarrow> fri_mca_even_component len xs current i = poly A (next_xs ! i) \<and>
       fri_mca_odd_component len xs current i = poly C (next_xs ! i)" by blast
   have dP: "degree (fri_mca_parent_polynomial A C) \<le> 2*k+1"
     by (rule fri_mca_parent_degree[OF dA dC])
   have ap: "\<forall>i\<in>fri_mca_pair_indices (length next_xs) S.
       current ! i = poly (fri_mca_parent_polynomial A C) (xs ! i)"
     by (rule fri_mca_components_reconstruct_pairs[OF lengths S _ _ _ ac])
       (use S squares siblings nonzero in auto)
   show False using no_parent dP ap by blast
 qed
 show "b \<in> fri_binary_mca_bad_challenges next_xs k
     (fri_mca_even_component len xs current)
     (fri_mca_odd_component len xs current) t"
   unfolding fri_binary_mca_bad_challenges_def
   using S large dq no_pair agree[unfolded fri_mca_actual_fold_affine] by blast
qed

lemma fri_mca_fold_bad_card:
 assumes distinct: "distinct next_xs" and radius: "3*t+k < length next_xs"
   and lengths: "len = 2 * length next_xs"
   and squares: "\<And>i. i < length next_xs \<Longrightarrow> next_xs ! i = (xs ! i)^2"
   and siblings: "\<And>i. i < length next_xs \<Longrightarrow> xs ! (i + length next_xs) = -(xs ! i)"
   and nonzero: "\<And>i. i < length next_xs \<Longrightarrow> xs ! i \<noteq> 0"
 shows "card (fri_mca_fold_bad_challenges k next_xs len xs current t) \<le> max 1 (2*t)"
proof -
 have "card (fri_mca_fold_bad_challenges k next_xs len xs current t) \<le>
   card (fri_binary_mca_bad_challenges next_xs k
     (fri_mca_even_component len xs current) (fri_mca_odd_component len xs current) t)"
   by (rule card_mono) (use fri_mca_fold_bad_subset[OF lengths squares siblings nonzero] in auto)
 also have "... \<le> max 1 (2*t)"
   by (rule fri_binary_mca_bad_challenges_card[OF distinct radius])
 finally show ?thesis .
qed

lemma fri_mca_fold_good_propagates:
 assumes good: "b \<notin> fri_mca_fold_bad_challenges k next_xs len xs current t"
   and S: "S \<subseteq> {..<length next_xs}" and large: "length next_xs \<le> card S+t"
   and dq: "degree q \<le> k"
   and agree: "\<And>i. i\<in>S \<Longrightarrow> fri_table_fold_value b current xs len 1 i = poly q (next_xs ! i)"
 obtains p where "degree p \<le> 2*k+1"
   "\<forall>i\<in>fri_mca_pair_indices (length next_xs) S. current ! i = poly p (xs ! i)"
 using good S large dq agree that unfolding fri_mca_fold_bad_challenges_def by blast

lemma fri_mca_canonical_lengths:
 assumes ep: "clength * scale = 2^N" and active: "i < N"
 shows "length (fri_canonical_domain_at i) =
   2 * length (fri_canonical_domain_at (Suc i))"
 using fri_canonical_domain_successor_length[OF ep active]
   fri_canonical_domain_at_even[OF ep active] by simp

lemma fri_mca_canonical_square:
 assumes ep: "clength * scale = 2^N" and active: "i < N"
   and j: "j < length (fri_canonical_domain_at (Suc i))"
 shows "fri_canonical_domain_at (Suc i) ! j = (fri_canonical_domain_at i ! j)^2"
 using fri_canonical_domain_successor_map_square[OF ep active] j
   fri_canonical_domain_successor_length[OF ep active] by simp

lemma fri_mca_canonical_nonzero:
 assumes j: "j < length (fri_canonical_domain_at i)"
 shows "fri_canonical_domain_at i ! j \<noteq> 0"
 using fri_canonical_domain_at_nth[OF j] h_nonzero shift_nonzero by simp

lemma fri_mca_canonical_sibling:
 assumes ep: "clength * scale = 2^N" and active: "i < N"
   and j: "j < length (fri_canonical_domain_at (Suc i))"
 shows "fri_canonical_domain_at i ! (j+length (fri_canonical_domain_at (Suc i))) =
   -(fri_canonical_domain_at i ! j)"
proof -
 let ?len = "length (fri_canonical_domain_at i)"
 let ?n = "length (fri_canonical_domain_at (Suc i))"
 have len: "?len = 2*?n" by (rule fri_mca_canonical_lengths[OF ep active])
 have pos: "0 < ?len" by (rule fri_canonical_domain_at_pos[OF ep]) (use active in simp)
 have even: "2 dvd ?len" by (rule fri_canonical_domain_at_even[OF ep active])
 have round: "?len * 2^i = clength*scale"
   by (rule fri_canonical_domain_at_round_product[OF ep]) (use active in simp)
 have jl: "j < ?len" using j len by simp
 have jn: "j+?n < ?len" using j len by simp
 have sib: "fri_sibling_index ?len j = j+?n"
   unfolding len by (rule fri_mca_sibling_half[OF j])
 have domj: "fri_canonical_domain_at i ! j = (h^j * shift)^(2^i)"
   by (rule fri_canonical_domain_at_nth[OF jl])
 have domjn: "fri_canonical_domain_at i ! (j+?n) = (h^(j+?n) * shift)^(2^i)"
   by (rule fri_canonical_domain_at_nth[OF jn])
 show ?thesis
   using fri_sibling_domain_round[OF pos even round, of j] domj domjn sib
   unfolding fri_sibling_index_def by simp
qed

definition fri_mca_layer_bad_challenges :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
where "fri_mca_layer_bad_challenges d t i current =
 fri_mca_fold_bad_challenges
   (fri_degree_after (Suc i) (fri_padded_degree_bound d))
   (fri_canonical_domain_at (Suc i))
   (length (fri_canonical_domain_at i)) (fri_canonical_domain_at i)
   (fri_conditioned_layer_table i current) t"

lemma fri_mca_layer_bad_card:
 assumes ep: "clength * scale = 2^N" and active: "i < N"
   and radius: "3*t + fri_degree_after (Suc i) (fri_padded_degree_bound d)
     < length (fri_canonical_domain_at (Suc i))"
 shows "card (fri_mca_layer_bad_challenges d t i current) \<le> max 1 (2*t)"
 unfolding fri_mca_layer_bad_challenges_def
proof (rule fri_mca_fold_bad_card)
 show "distinct (fri_canonical_domain_at (Suc i))"
   by (rule distinct_fri_canonical_domain_at[OF ep]) (use active in simp)
 show "3*t + fri_degree_after (Suc i) (fri_padded_degree_bound d) <
   length (fri_canonical_domain_at (Suc i))" by (rule radius)
 show "length (fri_canonical_domain_at i) =
   2*length (fri_canonical_domain_at (Suc i))" by (rule fri_mca_canonical_lengths[OF ep active])
 show "\<And>j. j < length (fri_canonical_domain_at (Suc i)) \<Longrightarrow>
   fri_canonical_domain_at (Suc i) ! j = (fri_canonical_domain_at i ! j)^2"
   by (rule fri_mca_canonical_square[OF ep active])
 show "\<And>j. j < length (fri_canonical_domain_at (Suc i)) \<Longrightarrow>
   fri_canonical_domain_at i ! (j+length (fri_canonical_domain_at (Suc i))) =
   -(fri_canonical_domain_at i ! j)"
   by (rule fri_mca_canonical_sibling[OF ep active])
 show "\<And>j. j < length (fri_canonical_domain_at (Suc i)) \<Longrightarrow>
   fri_canonical_domain_at i ! j \<noteq> 0"
   by (rule fri_mca_canonical_nonzero)
     (use fri_mca_canonical_lengths[OF ep active] in simp)
qed

lemma fri_mca_quarter_radius_arithmetic:
 fixes k n t :: nat
 assumes rate: "4*k < n" and t: "t \<le> n div 4"
 shows "3*t+k < n"
proof -
 have "4*(n div 4) \<le> n" by simp
 then have "4*t \<le> n" using t by linarith
 then show ?thesis using rate by linarith
qed

lemma fri_mca_canonical_quarter_radius:
 assumes ep: "clength * scale = 2^N"
   and active: "i < ceil_log (Suc d)"
   and fit: "ceil_log (Suc d) \<le> N"
   and rate: "4 * fri_padded_degree_bound d \<le> clength*scale"
   and t: "t \<le> length (fri_canonical_domain_at (Suc i)) div 4"
 shows "3*t + fri_degree_after (Suc i) (fri_padded_degree_bound d)
     < length (fri_canonical_domain_at (Suc i))"
proof (rule fri_mca_quarter_radius_arithmetic[OF _ t])
 have a: "i < N" using active fit by linarith
 have r: "4*fri_degree_after i (fri_padded_degree_bound d) \<le>
   length (fri_canonical_domain_at i)"
   by (rule fri_degree_after_rate_preserved[OF rate])
 show "4*fri_degree_after (Suc i) (fri_padded_degree_bound d) <
     length (fri_canonical_domain_at (Suc i))"
   using r fri_mca_canonical_lengths[OF ep a]
     fri_degree_after_padded_step[OF active] by linarith
qed

lemma fri_mca_layer_good_propagates:
 assumes active: "i < ceil_log (Suc d)"
   and good: "b \<notin> fri_mca_layer_bad_challenges d t i current"
   and S: "S \<subseteq> {..<length (fri_canonical_domain_at (Suc i))}"
   and large: "length (fri_canonical_domain_at (Suc i)) \<le> card S+t"
   and dq: "degree q \<le> fri_degree_after (Suc i) (fri_padded_degree_bound d)"
   and agree: "\<And>j. j\<in>S \<Longrightarrow>
     fri_table_fold_value b (fri_conditioned_layer_table i current)
       (fri_canonical_domain_at i) (length (fri_canonical_domain_at i)) 1 j =
     poly q (fri_canonical_domain_at (Suc i) ! j)"
 obtains p where "degree p \<le> fri_degree_after i (fri_padded_degree_bound d)"
   "\<forall>j\<in>fri_mca_pair_indices (length (fri_canonical_domain_at (Suc i))) S.
     fri_conditioned_layer_table i current ! j = poly p (fri_canonical_domain_at i ! j)"
 proof -
 obtain p where dp: "degree p \<le> 2 * fri_degree_after (Suc i) (fri_padded_degree_bound d) + 1"
   and ap: "\<forall>j\<in>fri_mca_pair_indices (length (fri_canonical_domain_at (Suc i))) S.
     fri_conditioned_layer_table i current ! j = poly p (fri_canonical_domain_at i ! j)"
   by (rule fri_mca_fold_good_propagates[OF good[unfolded fri_mca_layer_bad_challenges_def] S large dq agree])
 have dp': "degree p \<le> fri_degree_after i (fri_padded_degree_bound d)"
   unfolding fri_degree_after_padded_step[OF active] by (rule dp)
 show thesis by (rule that[OF dp' ap])
qed

definition fri_mca_online_bad_challenges ::
 "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f protocol_channel \<Rightarrow> 'f \<Rightarrow> 'f set"
where "fri_mca_online_bad_challenges d t i state rt =
 fri_mca_layer_bad_challenges d t i
   (conceptual_table state rt (length (fri_canonical_domain_at i)))"

lemma fri_mca_online_bad_prefix_stable:
 assumes ext: "s \<le> u"
   and no_hit: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {rt} s) s u"
 shows "fri_mca_online_bad_challenges d t i u rt =
   fri_mca_online_bad_challenges d t i s rt"
 unfolding fri_mca_online_bad_challenges_def
 by (simp only: conceptual_table_prefix_stable_if_no_target[OF ext no_hit])

lemma fri_mca_online_bad_card:
 assumes ep: "clength*scale = 2^N" and active: "i < N"
   and radius: "3*t + fri_degree_after (Suc i) (fri_padded_degree_bound d)
     < length (fri_canonical_domain_at (Suc i))"
 shows "card (fri_mca_online_bad_challenges d t i state rt) \<le> max 1 (2*t)"
 unfolding fri_mca_online_bad_challenges_def
 by (rule fri_mca_layer_bad_card[OF ep active radius])

definition fri_mca_chain_bad_event ::
 "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f protocol_channel \<Rightarrow> bool"
where "fri_mca_chain_bad_event d ts roots challenges state \<longleftrightarrow>
 (\<exists>i<min (length roots) (length challenges).
   challenges ! i \<in> fri_mca_online_bad_challenges d (ts i) i state (roots ! i))"

lemma fri_mca_chain_not_badD:
 assumes good: "\<not> fri_mca_chain_bad_event d ts roots challenges state"
   and lengths: "length roots = length challenges"
   and active: "i < length challenges"
 shows "challenges ! i \<notin> fri_mca_layer_bad_challenges d (ts i) i
   (fri_builder_conceptual_layers roots state final_value ! i)"
 using good lengths active
 unfolding fri_mca_chain_bad_event_def fri_mca_online_bad_challenges_def
 by (simp add: fri_builder_conceptual_layers_at)

end
end
