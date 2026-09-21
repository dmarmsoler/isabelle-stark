theory Soundness_FRI_Authenticated_Residual_Realization_Audit
  imports
    Stark.Soundness_FRI_Authenticated_Global_Chain_Audit
    Stark.Soundness_FRI_Robust_Schedule_Optimality
begin

context soundness
begin

text \<open>
  This bounded audit separates two questions that the non-strict schedule
  envelope does not distinguish.  First, an actual residual transition uses a
  challenge outside the corresponding good-challenge set.  Its folded distance
  is therefore strictly greater than the good radius, so the triangle argument
  loses at least one more successor-domain position than the non-strict
  envelope records.  Second, attaining the resulting conceptual envelope still
  does not by itself construct a verifier execution: the committed tables,
  prefix-derived challenges, authenticated openings, terminal constant, and
  collision-free random-oracle state must coexist.

  The strict lemmas below formalize the first point.  The final Merkle lemma
  shows that a single arbitrary power-of-two table is not obstructed merely by
  authentication.  It deliberately does not claim a converse to the existing
  execution-to-evidence theorems for an entire FRI chain.
\<close>

lemma agreement_card_bound_from_triangle_strict:
  assumes finite_I: "finite I"
    and received_far:
      "t < card (code_disagreement_indices I received word)"
    and next_close:
      "card (code_disagreement_indices I next word) \<le> r"
    and margin: "r + s \<le> t"
  shows
    "card (code_agreement_indices I received next) \<le>
      card I - Suc s"
proof -
  let ?A = "code_agreement_indices I received next"
  let ?D = "code_disagreement_indices I received next"
  let ?F = "code_disagreement_indices I received word"
  let ?E = "code_disagreement_indices I next word"
  have finite_D: "finite ?D"
    by (rule finite_code_disagreement_indices[OF finite_I])
  have finite_E: "finite ?E"
    by (rule finite_code_disagreement_indices[OF finite_I])
  have triangle: "?F \<subseteq> ?D \<union> ?E"
    unfolding code_disagreement_indices_def by auto
  have finite_union: "finite (?D \<union> ?E)"
    using finite_D finite_E by simp
  have F_card: "card ?F \<le> card (?D \<union> ?E)"
    by (rule card_mono[OF finite_union triangle])
  have union_card: "card (?D \<union> ?E) \<le> card ?D + card ?E"
    by (rule card_Un_le)
  have far_to_D: "t < card ?D + r"
    using received_far F_card union_card next_close by linarith
  have D_strict: "s < card ?D"
    using margin far_to_D by linarith
  have agreement_partition: "card ?A + card ?D = card I"
    by (rule code_agreement_disagreement_card[OF finite_I])
  show ?thesis
    using D_strict agreement_partition by linarith
qed

lemma fri_fold_next_agreement_card_bound_strict:
  assumes next_close:
      "fri_rs_distance_to_code k next_dom (nth next) \<le> r"
    and challenge_not_good:
      "b \<notin> fri_fold_good_challenges
        k next_dom len fri_dom current t"
    and margin: "r + s \<le> t"
    and next_length: "length next = length next_dom"
  shows
    "card (fri_fold_next_agreement_indices
      b len fri_dom current next) \<le> length next_dom - Suc s"
proof -
  let ?folded = "fri_folded_received b len fri_dom current"
  let ?word = "fri_rs_canonical_decoder k next_dom (nth next)"
  have word_code: "?word \<in> fri_rs_code_functions k next_dom"
    by (rule fri_rs_canonical_decoder_code)
  have folded_distance:
      "fri_rs_distance_to_code k next_dom ?folded \<le>
        card (code_disagreement_indices
          {..<length next_dom} ?folded ?word)"
    by (rule fri_rs_distance_to_code_le[OF word_code])
  have not_good_errors:
      "t < card (fri_fold_decoder_errors
        k next_dom len fri_dom current b)"
    using challenge_not_good
    unfolding fri_fold_good_challenges_def by simp
  have folded_far:
      "t < card (code_disagreement_indices
        {..<length next_dom} ?folded ?word)"
  proof -
    have decoder_distance:
        "card (fri_fold_decoder_errors
            k next_dom len fri_dom current b) =
          fri_rs_distance_to_code k next_dom ?folded"
      unfolding fri_fold_decoder_errors_def fri_fold_decoder_def
      by (rule fri_rs_canonical_decoder_distance)
    show ?thesis
      using not_good_errors decoder_distance folded_distance by linarith
  qed
  have next_decoder_exact:
      "card (code_disagreement_indices
          {..<length next_dom} (nth next) ?word) =
        fri_rs_distance_to_code k next_dom (nth next)"
    by (rule fri_rs_canonical_decoder_distance)
  have next_decoder_close:
      "card (code_disagreement_indices
          {..<length next_dom} (nth next) ?word) \<le> r"
    using next_close next_decoder_exact by simp
  have generic:
      "card (code_agreement_indices
          {..<length next_dom} ?folded (nth next)) \<le>
        card {..<length next_dom} - Suc s"
    by (rule agreement_card_bound_from_triangle_strict[
          OF _ folded_far next_decoder_close margin]) simp
  show ?thesis
    using generic next_length
    unfolding fri_fold_next_agreement_indices_def by simp
qed

lemma card_fri_robust_conditioned_query_indices_strict:
  fixes i N k r s t :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and layer_fit: "Suc i \<le> N"
    and next_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        length (layers ! Suc i)"
    and next_close:
      "fri_rs_distance_to_code k
        (fri_canonical_domain_at (Suc i))
        (nth (fri_conditioned_layer_table (Suc i) (layers ! Suc i)))
        \<le> r"
    and challenge_not_good:
      "challenges ! i \<notin> fri_fold_good_challenges k
        (fri_canonical_domain_at (Suc i))
        (length (fri_canonical_domain_at i))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i (layers ! i)) t"
    and margin: "r + s \<le> t"
  shows
    "card (fri_conditioned_query_indices roots i
      (fri_robust_conditioned_agreement_indices challenges layers i))
      \<le> modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) - Suc s)"
proof -
  let ?next =
    "fri_conditioned_layer_table (Suc i) (layers ! Suc i)"
  have next_length:
      "length ?next = length (fri_canonical_domain_at (Suc i))"
    by (rule length_fri_conditioned_layer_table[OF next_cover])
  have agreement:
      "card (fri_robust_conditioned_agreement_indices challenges layers i)
        \<le> length (fri_canonical_domain_at (Suc i)) - Suc s"
    unfolding fri_robust_conditioned_agreement_indices_def
    by (rule fri_fold_next_agreement_card_bound_strict[
          OF next_close challenge_not_good margin next_length])
  have modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
    by (rule fri_canonical_domain_at_pos[OF eval_power layer_fit])
  show ?thesis
    by (rule card_fri_conditioned_query_indices[
          OF modulus_pos
            fri_robust_conditioned_agreement_indices_subset[
              OF next_cover]
            agreement])
qed


lemma scale64_first_layer_strict_residual_envelope:
  "modulo_preimage_card_envelope 65472 32768
      (32768 - Suc 620) = 64294"
  unfolding modulo_preimage_card_envelope_def by simp

lemma fri_scale64_optimal_strict_residual_envelope:
  assumes "i < 10"
  shows
    "modulo_preimage_card_envelope 65472
       (fri_scale64_successor_size i)
       (fri_scale64_successor_size i -
         Suc (fri_scale64_optimal_margin i)) \<le> 64294"
proof -
  have cases:
      "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or>
       i = 5 \<or> i = 6 \<or> i = 7 \<or> i = 8 \<or> i = 9"
    using assms by arith
  from cases show ?thesis
    unfolding fri_scale64_successor_size_def
      fri_scale64_optimal_margin_def
      modulo_preimage_card_envelope_def
    by (elim disjE; simp)
qed

lemma fri_scale64_optimal_strict_residual_envelope_exact:
  "modulo_preimage_card_envelope 65472
     (fri_scale64_successor_size 0)
     (fri_scale64_successor_size 0 -
       Suc (fri_scale64_optimal_margin 0)) = 64294"
  unfolding fri_scale64_successor_size_def
    fri_scale64_optimal_margin_def
    modulo_preimage_card_envelope_def
  by simp

lemma conceptual_table_eq_of_created_tree:
  assumes created: "created_tree table tree s"
    and length_power: "length table = 2 ^ n"
    and clean: "\<not> hash_map_output_collision s"
  shows
    "conceptual_table s (value tree) (length table) = table"
proof (rule nth_equalityI)
  show
    "length (conceptual_table s (value tree) (length table)) =
      length table"
    by simp
next
  fix i
  assume i_bound:
    "i < length (conceptual_table s (value tree) (length table))"
  then have i_table: "i < length table"
    by simp
  let ?path = "get_authentication_path (length table) i tree"
  let ?opening =
    "\<lparr>opening_root = value tree,
      opening_length = length table,
      opening_index = i,
      opening_value = table ! i,
      opening_path = ?path\<rparr>"
  have root_in_map:
      "merkle_path_root_in_map s (length table) i
        (table ! i) ?path = Some (value tree)"
    by (rule protocol_created_tree_path_root_in_map[
          OF created[unfolded created_tree_def] length_power i_table])
  have path_bound:
      "merkle_path_bound (value tree) (length table) i
        (table ! i) ?path s"
    by (rule merkle_path_root_in_map_some_imp_bound[OF root_in_map])
  have table_nonempty: "table \<noteq> []"
    using length_power by auto
  have path_length:
      "length ?path = floor_log (length table)"
    by (rule created_tree_get_authentication_path_len[
          OF created table_nonempty])
  have authenticated: "authenticated_opening_in s ?opening"
    unfolding authenticated_opening_in_def
    using i_table path_length path_bound by simp
  have value_at:
      "authenticated_value_at s (value tree) (length table) i (table ! i)"
    unfolding authenticated_value_at_def
    by (rule exI[where x="?opening"]) (use authenticated in simp)
  have conceptual_value:
      "conceptual_opening_value s (value tree) (length table) i = table ! i"
    by (rule conceptual_opening_value_eq_if_authenticated[
          OF clean value_at])
  show
      "conceptual_table s (value tree) (length table) ! i = table ! i"
    unfolding conceptual_table_nth[OF i_table]
    by (rule conceptual_value)
qed

text \<open>
  At scale 64, the old 64296 numeral corresponds at layer zero to allowing
  32768 - 620 = 32148 successor-domain agreements.  In the residual branch,
  however, the selected challenge is outside the good-challenge set.  With
  successor radius 6152 and good radius 6772, strictness forces at least 621
  disagreements, hence at most 32147 agreements and the exact modulo envelope
  64294.  Thus 64296 is not realizable by an execution satisfying the residual
  branch premises.

  This audit provides the converse direction only locally:
  The predicate \<^const>\<open>created_tree\<close> can authenticate an arbitrary
  power-of-two table, as proved above.  It does not construct, from a prescribed
  family of conceptual tables and challenges, one collision-free protocol state
  whose Merkle roots, prefix-derived challenges, authenticated openings, full
  folding chain, terminal value, and verifier outcome all agree.  The existing
  global chain results instead start from recorded authenticated evidence and
  extract the conceptual constraints.  Consequently this audit does not
  construct a near-saturating authenticated verifier execution at 64294; the
  separate algebraic realization layer tests only the fold-chain part of that
  question.
\<close>

end
end
