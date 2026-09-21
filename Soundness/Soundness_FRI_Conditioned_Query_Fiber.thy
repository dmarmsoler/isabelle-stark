theory Soundness_FRI_Conditioned_Query_Fiber
  imports
    Soundness_FRI_Conditioned_Authenticated_Bridge
    Soundness_Query_Index_Modulo_Bounds
    Soundness_FRI_Query_List_Exact_Product
begin

context soundness
begin

lemma fri_evidence_layer_len_canonical:
  assumes layer_bound: "i < length roots"
  shows
    "fri_evidence_layer_len roots i =
      length (fri_canonical_domain_at i)"
  unfolding fri_evidence_layer_len_def fri_canonical_domain_at_length
  using fri_layer_lengths_nth_div[
      OF layer_bound, of "clength * scale"]
  by simp

lemma fri_evidence_next_idx_singleton_mod_canonical:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and layer_bound: "i < length roots"
  shows
    "fri_evidence_next_idx roots [q] 0 i =
      q mod length (fri_canonical_domain_at (Suc i))"
  using layer_bound
proof (induction i)
  case 0
  have zero_lt_N: "0 < N"
    using 0 roots_le by linarith
  have idx0:
      "fri_layer_indices (length roots) q (clength * scale) ! 0 = q"
    using fri_layer_indices_prefix_nth[OF 0, of q "clength * scale"]
    by simp
  show ?case
    unfolding fri_evidence_next_idx_def fri_evidence_layer_idx_def
      fri_evidence_layer_len_canonical[OF 0]
    using fri_canonical_domain_successor_length[OF eval_power zero_lt_N]
      idx0
    by simp
next
  case (Suc i)
  have i_bound: "i < length roots"
    using Suc.prems by simp
  have suc_lt_N: "Suc i < N"
    using Suc.prems roots_le by linarith
  have ih:
      "fri_evidence_next_idx roots [q] 0 i =
        q mod length (fri_canonical_domain_at (Suc i))"
    by (rule Suc.IH[OF i_bound])
  have layer_idx:
      "fri_evidence_layer_idx roots [q] 0 (Suc i) =
        fri_evidence_next_idx roots [q] 0 i"
    by (rule fri_evidence_layer_idx_Suc)
      (rule Suc.prems)
  have len_current:
      "fri_evidence_layer_len roots (Suc i) =
        length (fri_canonical_domain_at (Suc i))"
    by (rule fri_evidence_layer_len_canonical[OF Suc.prems])
  have len_next:
      "length (fri_canonical_domain_at (Suc (Suc i))) =
        length (fri_canonical_domain_at (Suc i)) div 2"
    by (rule fri_canonical_domain_successor_length[
        OF eval_power suc_lt_N])
  have divisor:
      "length (fri_canonical_domain_at (Suc (Suc i))) dvd
        length (fri_canonical_domain_at (Suc i))"
    unfolding len_next
    using fri_canonical_domain_at_even[OF eval_power suc_lt_N]
    by auto
  have next_unfold:
      "fri_evidence_next_idx roots [q] 0 (Suc i) =
        fri_evidence_next_idx roots [q] 0 i mod
          length (fri_canonical_domain_at (Suc (Suc i)))"
    unfolding fri_evidence_next_idx_def layer_idx len_current len_next
    by simp
  show ?case
    unfolding next_unfold ih
    by (rule mod_mod_cancel[OF divisor])
qed

lemma fri_evidence_next_idx_at:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and layer_bound: "i < length roots"
    and round_bound: "round_idx < length query_idxs"
  shows
    "fri_evidence_next_idx roots query_idxs round_idx i =
      query_idxs ! round_idx mod
        length (fri_canonical_domain_at (Suc i))"
proof -
  have same:
      "fri_evidence_next_idx roots query_idxs round_idx i =
        fri_evidence_next_idx roots [query_idxs ! round_idx] 0 i"
    unfolding fri_evidence_next_idx_def fri_evidence_layer_idx_def
      fri_evidence_layer_len_def
    by simp
  show ?thesis
    unfolding same
    by (rule fri_evidence_next_idx_singleton_mod_canonical[
        OF eval_power roots_le layer_bound])
qed

definition fri_conditioned_query_indices
  :: "'f list \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set"
where
  "fri_conditioned_query_indices roots i A =
    {q \<in> query_sample_space.
      q mod length (fri_canonical_domain_at (Suc i)) \<in> A}"

lemma fri_conditioned_query_indices_subset:
  "fri_conditioned_query_indices roots i A \<subseteq> query_sample_space"
  unfolding fri_conditioned_query_indices_def by simp

lemma finite_fri_conditioned_query_indices[simp]:
  "finite (fri_conditioned_query_indices roots i A)"
  by (rule finite_subset[OF fri_conditioned_query_indices_subset])
    (rule finite_query_sample_space)

definition fri_conditioned_query_lists :: "nat set \<Rightarrow> nat list set"
where
  "fri_conditioned_query_lists indices =
    {query_idxs. set query_idxs \<subseteq> indices \<and> length query_idxs = rounds}"

lemma finite_fri_conditioned_query_lists:
  assumes "finite indices"
  shows "finite (fri_conditioned_query_lists indices)"
  unfolding fri_conditioned_query_lists_def
  by (rule finite_lists_length_eq[OF assms])

lemma card_fri_conditioned_query_lists:
  assumes "finite indices"
  shows
    "card (fri_conditioned_query_lists indices) = card indices ^ rounds"
  unfolding fri_conditioned_query_lists_def
  using card_lists_length_eq[OF assms, of rounds]
  by (simp add: conj_commute)

lemma fri_conditioned_residual_query_lists_restricted_subset:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and layer_bound: "i < length roots"
  shows
    "fri_conditioned_residual_query_lists roots challenges layers i \<inter>
        fri_query_index_list_space \<subseteq>
      fri_conditioned_query_lists
        (fri_conditioned_query_indices roots i
          (fri_conditioned_agreement_indices i
            (layers ! i) (layers ! Suc i) (challenges ! i)))"
proof
  fix qs
  assume qs:
      "qs \<in>
        fri_conditioned_residual_query_lists roots challenges layers i \<inter>
          fri_query_index_list_space"
  then have qs_len: "length qs = rounds"
    and qs_space: "set qs \<subseteq> query_sample_space"
    unfolding fri_query_index_list_space_def by auto
  have entries:
      "set qs \<subseteq>
        fri_conditioned_query_indices roots i
          (fri_conditioned_agreement_indices i
            (layers ! i) (layers ! Suc i) (challenges ! i))"
  proof
    fix q
    assume q_in: "q \<in> set qs"
    then obtain round_idx where round_bound: "round_idx < length qs"
      and q_eq: "q = qs ! round_idx"
      by (metis in_set_conv_nth)
    have agreement:
        "fri_evidence_next_idx roots qs round_idx i \<in>
          fri_conditioned_agreement_indices i
            (layers ! i) (layers ! Suc i) (challenges ! i)"
      using qs round_bound
      unfolding fri_conditioned_residual_query_lists_def by auto
    have mod_agreement:
        "q mod length (fri_canonical_domain_at (Suc i)) \<in>
          fri_conditioned_agreement_indices i
            (layers ! i) (layers ! Suc i) (challenges ! i)"
      using agreement
        fri_evidence_next_idx_at[
          OF eval_power roots_le layer_bound round_bound]
        q_eq
      by simp
    show
      "q \<in> fri_conditioned_query_indices roots i
        (fri_conditioned_agreement_indices i
          (layers ! i) (layers ! Suc i) (challenges ! i))"
      using qs_space q_in mod_agreement
      unfolding fri_conditioned_query_indices_def by auto
  qed
  show
      "qs \<in> fri_conditioned_query_lists
        (fri_conditioned_query_indices roots i
          (fri_conditioned_agreement_indices i
            (layers ! i) (layers ! Suc i) (challenges ! i)))"
    unfolding fri_conditioned_query_lists_def
    using qs_len entries by simp
qed

lemma modulo_preimage_card_envelope_mono:
  assumes "k \<le> l"
  shows
    "modulo_preimage_card_envelope N q k \<le>
      modulo_preimage_card_envelope N q l"
  using assms
  unfolding modulo_preimage_card_envelope_def
  by (intro add_mono mult_le_mono1 min.mono) simp_all

lemma card_fri_conditioned_query_indices:
  assumes modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
    and agreement_subset:
      "A \<subseteq> {..<length (fri_canonical_domain_at (Suc i))}"
    and agreement_card: "card A \<le> K"
  shows
    "card (fri_conditioned_query_indices roots i A) \<le>
      modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i))) K"
proof -
  let ?m = "length (fri_canonical_domain_at (Suc i))"
  have set_eq:
      "fri_conditioned_query_indices roots i A =
        {q. q < query_sample_space_size \<and> q mod ?m \<in> A}"
    unfolding fri_conditioned_query_indices_def query_sample_space_def
    by auto
  have base:
      "card {q. q < query_sample_space_size \<and> q mod ?m \<in> A} \<le>
        modulo_preimage_card_envelope query_sample_space_size ?m (card A)"
    by (rule card_modulo_set_preimage_le_envelope[
        OF modulus_pos agreement_subset])
  have mono:
      "modulo_preimage_card_envelope query_sample_space_size ?m (card A) \<le>
        modulo_preimage_card_envelope query_sample_space_size ?m K"
    by (rule modulo_preimage_card_envelope_mono[OF agreement_card])
  show ?thesis
    unfolding set_eq
    by (rule order_trans[OF base mono])
qed

lemma fri_conditioned_agreement_indices_subset:
  "fri_conditioned_agreement_indices i current next b \<subseteq>
    {..<length (fri_canonical_domain_at (Suc i))}"
  unfolding fri_conditioned_agreement_indices_def
    fri_polynomial_agreement_indices_def
  by auto

lemma card_fri_conditioned_residual_restricted:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and layer_bound: "i < length roots"
    and agreement_card:
      "card (fri_conditioned_agreement_indices i
        (layers ! i) (layers ! Suc i) (challenges ! i)) \<le> K"
    and modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
  shows
    "card
      (fri_conditioned_residual_query_lists roots challenges layers i \<inter>
        fri_query_index_list_space) \<le>
      (modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i))) K) ^ rounds"
proof -
  let ?A =
    "fri_conditioned_agreement_indices i
      (layers ! i) (layers ! Suc i) (challenges ! i)"
  let ?I = "fri_conditioned_query_indices roots i ?A"
  have subset:
      "fri_conditioned_residual_query_lists roots challenges layers i \<inter>
          fri_query_index_list_space \<subseteq> fri_conditioned_query_lists ?I"
    by (rule fri_conditioned_residual_query_lists_restricted_subset[
        OF eval_power roots_le layer_bound])
  have finite_lists: "finite (fri_conditioned_query_lists ?I)"
    unfolding fri_conditioned_query_lists_def
    by (rule finite_lists_length_eq)
      (rule finite_fri_conditioned_query_indices)
  have card_subset:
      "card
        (fri_conditioned_residual_query_lists roots challenges layers i \<inter>
          fri_query_index_list_space) \<le>
        card (fri_conditioned_query_lists ?I)"
    by (rule card_mono[OF finite_lists subset])
  have indices_card:
      "card ?I \<le>
        modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i))) K"
    by (rule card_fri_conditioned_query_indices[
        OF modulus_pos fri_conditioned_agreement_indices_subset
          agreement_card])
  have lists_card:
      "card (fri_conditioned_query_lists ?I) = card ?I ^ rounds"
    by (rule card_fri_conditioned_query_lists)
      (rule finite_fri_conditioned_query_indices)
  have card_subset_power:
      "card
        (fri_conditioned_residual_query_lists roots challenges layers i \<inter>
          fri_query_index_list_space) \<le> card ?I ^ rounds"
    using card_subset lists_card by simp
  have envelope_power:
      "card ?I ^ rounds \<le>
        (modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i))) K) ^ rounds"
    by (rule power_mono[OF indices_card]) simp
  show ?thesis
    by (rule order_trans[OF card_subset_power envelope_power])
qed

lemma modulo_preimage_card_envelope_strict:
  assumes q_pos: "0 < q"
    and q_le_N: "q \<le> N"
    and k_lt: "k < q"
  shows "modulo_preimage_card_envelope N q k < N"
proof -
  have quotient_pos: "0 < N div q"
    using q_pos q_le_N
    by (simp add: div_greater_zero_iff)
  have block_strict: "(N div q) * k < (N div q) * q"
    using quotient_pos k_lt by simp
  have remainder_le: "min k (N mod q) \<le> N mod q"
    by simp
  have strict_sum:
      "(N div q) * k + min k (N mod q) <
        (N div q) * q + N mod q"
    using block_strict remainder_le by linarith
  have N_eq: "(N div q) * q + N mod q = N"
    using div_mult_mod_eq[of N q] by simp
  show ?thesis
    unfolding modulo_preimage_card_envelope_def
    using strict_sum N_eq by simp
qed

lemma card_fri_conditioned_residual_restricted_strict:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and layer_bound: "i < length roots"
    and agreement_card:
      "card (fri_conditioned_agreement_indices i
        (layers ! i) (layers ! Suc i) (challenges ! i)) \<le>
        length (fri_canonical_domain_at (Suc i)) - 1"
    and modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
    and modulus_le_sample_space:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        query_sample_space_size"
    and rounds_pos: "0 < rounds"
  shows
    "card
      (fri_conditioned_residual_query_lists roots challenges layers i \<inter>
        fri_query_index_list_space) < query_sample_space_size ^ rounds"
proof -
  let ?q = "length (fri_canonical_domain_at (Suc i))"
  let ?E =
    "modulo_preimage_card_envelope query_sample_space_size ?q (?q - 1)"
  have card_le:
      "card
        (fri_conditioned_residual_query_lists roots challenges layers i \<inter>
          fri_query_index_list_space) \<le> ?E ^ rounds"
    by (rule card_fri_conditioned_residual_restricted[
        OF eval_power roots_le layer_bound agreement_card modulus_pos])
  have predecessor_lt: "?q - 1 < ?q"
    using modulus_pos by simp
  have envelope_lt: "?E < query_sample_space_size"
    by (rule modulo_preimage_card_envelope_strict[
        OF modulus_pos modulus_le_sample_space predecessor_lt])
  have power_lt: "?E ^ rounds < query_sample_space_size ^ rounds"
    by (rule power_strict_mono[OF envelope_lt _ rounds_pos]) simp
  show ?thesis
    by (rule le_less_trans[OF card_le power_lt])
qed

lemma fri_conditioned_residual_restricted_not_full:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and layer_bound: "i < length roots"
    and agreement_card:
      "card (fri_conditioned_agreement_indices i
        (layers ! i) (layers ! Suc i) (challenges ! i)) \<le>
        length (fri_canonical_domain_at (Suc i)) - 1"
    and modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
    and modulus_le_sample_space:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        query_sample_space_size"
    and rounds_pos: "0 < rounds"
  shows
    "fri_conditioned_residual_query_lists roots challenges layers i \<inter>
        fri_query_index_list_space \<noteq> fri_query_index_list_space"
proof
  assume equality:
      "fri_conditioned_residual_query_lists roots challenges layers i \<inter>
          fri_query_index_list_space = fri_query_index_list_space"
  have strict:
      "card
        (fri_conditioned_residual_query_lists roots challenges layers i \<inter>
          fri_query_index_list_space) < query_sample_space_size ^ rounds"
    by (rule card_fri_conditioned_residual_restricted_strict[
        OF eval_power roots_le layer_bound agreement_card modulus_pos
          modulus_le_sample_space rounds_pos])
  have full_card:
      "card fri_query_index_list_space = query_sample_space_size ^ rounds"
    using card_fri_query_index_list_space
    unfolding card_query_sample_space by simp
  show False
    using strict equality full_card by simp
qed

end

end