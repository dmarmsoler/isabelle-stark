(*  Title:      Stark/Soundness_FRI_Composition_Replay_Gaps.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Composition_Replay_Gaps
  imports
    Soundness_FRI_Composition_Support
    Soundness_FRI_Generic_Low_Degree
begin

text \<open>
  Narrow downstream layer for the remaining composition verifier-tied replay
  gaps.  This avoids growing the composition residuals theory, which is
  already above the advisory size threshold.
\<close>

context soundness
begin

lemma fri_same_mod_half_index_cases:
  fixes len i j :: nat
  assumes even_len: "2 dvd len"
    and i_bound: "i < len"
    and j_bound: "j < len"
    and same_mod: "i mod (len div 2) = j mod (len div 2)"
  shows
    "i = j \<or>
     i = fri_sibling_index len j \<or>
     fri_sibling_index len i = j \<or>
     fri_sibling_index len i = fri_sibling_index len j"
proof -
  let ?half = "len div 2"
  have len_eq: "len = 2 * ?half"
    using even_len by simp
  have half_pos: "0 < ?half"
    using i_bound len_eq by linarith
  consider
    (ff) "i < ?half" "j < ?half"
  | (fs) "i < ?half" "\<not> j < ?half"
  | (sf) "\<not> i < ?half" "j < ?half"
  | (ss) "\<not> i < ?half" "\<not> j < ?half"
    by blast
  then show ?thesis
  proof cases
    case ff
    then have "i = j"
      using same_mod half_pos by simp
    then show ?thesis by simp
  next
    case fs
    have j_eq: "j = fri_sibling_index len (j mod ?half)"
      by (rule fri_sibling_index_mod_half_second_half
          [OF even_len j_bound fs(2)])
    have i_eq: "j mod ?half = i"
      using same_mod fs(1) by simp
    have "fri_sibling_index len i = j"
      using j_eq i_eq by simp
    then show ?thesis by simp
  next
    case sf
    have i_eq: "i = fri_sibling_index len (i mod ?half)"
      by (rule fri_sibling_index_mod_half_second_half
          [OF even_len i_bound sf(1)])
    have j_eq: "i mod ?half = j"
      using same_mod sf(2) by simp
    have "i = fri_sibling_index len j"
      using i_eq j_eq by simp
    then show ?thesis by simp
  next
    case ss
    have i_eq: "i = fri_sibling_index len (i mod ?half)"
      by (rule fri_sibling_index_mod_half_second_half
          [OF even_len i_bound ss(1)])
    have j_eq: "j = fri_sibling_index len (j mod ?half)"
      by (rule fri_sibling_index_mod_half_second_half
          [OF even_len j_bound ss(2)])
    have "i = j"
      using i_eq j_eq same_mod by simp
    then show ?thesis by simp
  qed
qed

lemma fri_same_mod_half_index_cases3:
  fixes len i j :: nat
  assumes even_len: "2 dvd len"
    and i_bound: "i < len"
    and j_bound: "j < len"
    and same_mod: "i mod (len div 2) = j mod (len div 2)"
  shows
    "i = j \<or>
     i = fri_sibling_index len j \<or>
     fri_sibling_index len i = j"
proof -
  let ?half = "len div 2"
  have len_eq: "len = 2 * ?half"
    using even_len by simp
  have half_pos: "0 < ?half"
    using i_bound len_eq by linarith
  consider
    (ff) "i < ?half" "j < ?half"
  | (fs) "i < ?half" "\<not> j < ?half"
  | (sf) "\<not> i < ?half" "j < ?half"
  | (ss) "\<not> i < ?half" "\<not> j < ?half"
    by blast
  then show ?thesis
  proof cases
    case ff
    then have "i = j"
      using same_mod half_pos by simp
    then show ?thesis by simp
  next
    case fs
    have j_eq: "j = fri_sibling_index len (j mod ?half)"
      by (rule fri_sibling_index_mod_half_second_half
          [OF even_len j_bound fs(2)])
    have i_eq: "j mod ?half = i"
      using same_mod fs(1) by simp
    have "fri_sibling_index len i = j"
      using j_eq i_eq by simp
    then show ?thesis by simp
  next
    case sf
    have i_eq: "i = fri_sibling_index len (i mod ?half)"
      by (rule fri_sibling_index_mod_half_second_half
          [OF even_len i_bound sf(1)])
    have j_eq: "i mod ?half = j"
      using same_mod sf(2) by simp
    have "i = fri_sibling_index len j"
      using i_eq j_eq by simp
    then show ?thesis by simp
  next
    case ss
    have i_eq: "i = fri_sibling_index len (i mod ?half)"
      by (rule fri_sibling_index_mod_half_second_half
          [OF even_len i_bound ss(1)])
    have j_eq: "j = fri_sibling_index len (j mod ?half)"
      by (rule fri_sibling_index_mod_half_second_half
          [OF even_len j_bound ss(2)])
    have "i = j"
      using i_eq j_eq same_mod by simp
    then show ?thesis by simp
  qed
qed

lemma fri_sibling_index_involution:
  fixes len idx :: nat
  assumes even_len: "2 dvd len"
    and idx_bound: "idx < len"
  shows "fri_sibling_index len (fri_sibling_index len idx) = idx"
proof -
  let ?half = "len div 2"
  have len_eq: "len = 2 * ?half"
    using even_len by simp
  have half_pos: "0 < ?half"
    using idx_bound len_eq by linarith
  show ?thesis
  proof (cases "idx < ?half")
    case True
    then show ?thesis
      by (rule fri_sibling_index_involution_first_half[OF even_len])
  next
    case False
    define k where "k = idx - ?half"
    have idx_eq: "idx = ?half + k"
      using False unfolding k_def by simp
    have k_bound: "k < ?half"
      using idx_bound len_eq idx_eq by linarith
    have sib_eq: "fri_sibling_index len idx = k"
    proof -
      have sum_eq: "(?half + k + ?half) = k + len"
        using len_eq by linarith
      have k_len: "k < len"
        using k_bound len_eq by linarith
      have "(?half + k + ?half) mod len = (k + len) mod len"
        by (simp only: sum_eq)
      also have "... = k"
        using k_len by simp
      finally have mod_eq: "(?half + k + ?half) mod len = k" .
      then show ?thesis
        unfolding fri_sibling_index_def idx_eq
        using mod_eq by simp
    qed
    have "fri_sibling_index len (fri_sibling_index len idx) =
        fri_sibling_index len k"
      using sib_eq by simp
    also have "... = idx"
      using fri_sibling_index_first_half[OF even_len k_bound]
      unfolding idx_eq by simp
    finally show ?thesis .
  qed
qed

lemma fri_sibling_fold_denominator_verifier:
  assumes len_pos: "0 < len"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
  shows
    "fri_fold_denominator ((h ^ fri_sibling_index len i) * shift) pw =
      - fri_fold_denominator ((h ^ i) * shift) pw"
  using fri_sibling_domain_round[OF len_pos even_len round, of i]
  unfolding fri_sibling_index_def fri_fold_denominator_def
  by simp

lemma fri_fold_value_sibling_verifier:
  assumes len_pos: "0 < len"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
  shows
    "fri_fold_value b xn xp
      (fri_fold_denominator ((h ^ fri_sibling_index len i) * shift) pw) =
     fri_fold_value b xp xn
      (fri_fold_denominator ((h ^ i) * shift) pw)"
proof -
  have denom:
    "fri_fold_denominator ((h ^ fri_sibling_index len i) * shift) pw =
      - fri_fold_denominator ((h ^ i) * shift) pw"
    by (rule fri_sibling_fold_denominator_verifier
        [OF len_pos even_len round])
  show ?thesis
    unfolding denom
    by (rule fri_fold_value_swap_neg_denominator)
qed

lemma generic_fri_forced_next_value_eq_if_no_same_layer_conflict:
  assumes no_same:
    "\<not> generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and even_len: "2 dvd fri_evidence_layer_len roots layer_idx"
    and raw_bound:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
        fri_evidence_layer_len roots layer_idx"
    and raw_bound':
      "fri_evidence_layer_idx roots query_idxs round_idx' layer_idx <
        fri_evidence_layer_len roots layer_idx"
    and round_product:
      "fri_evidence_layer_len roots layer_idx * 2 ^ layer_idx =
        clength * scale"
    and same_next:
      "fri_evidence_next_idx roots query_idxs round_idx layer_idx =
       fri_evidence_next_idx roots query_idxs round_idx' layer_idx"
    and forced:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx layer_idx v"
    and forced':
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx' layer_idx v'"
  shows "v = v'"
proof -
  let ?len = "fri_evidence_layer_len roots layer_idx"
  let ?raw = "fri_evidence_layer_idx roots query_idxs round_idx layer_idx"
  let ?raw' =
    "fri_evidence_layer_idx roots query_idxs round_idx' layer_idx"
  let ?ch = "challenges ! layer_idx"
  let ?pw = "2 ^ layer_idx"
  have len_pos: "0 < ?len"
    using raw_bound by simp
  from forced obtain xp xp_path xn xn_path where step:
    "fri_layer_step_evidence
      (roots ! layer_idx)
      ?ch
      ?len
      ?raw
      ?pw
      (fri_sibling_index ?len ?raw)
      xp xp_path xn xn_path
      (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
      v
      (round_layers ! round_idx ! layer_idx)"
    unfolding generic_fri_round_forced_next_value_def by blast
  have v_eq:
    "v = fri_evidence_next_value roots challenges query_idxs round_idx
      layer_idx xp xn"
    using fri_layer_step_evidenceD(3)[OF step]
    unfolding fri_evidence_next_value_def by simp
  have step_norm:
    "fri_layer_step_evidence
      (roots ! layer_idx)
      ?ch
      ?len
      ?raw
      ?pw
      (fri_sibling_index ?len ?raw)
      xp xp_path xn xn_path
      (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
      (fri_evidence_next_value roots challenges query_idxs round_idx
        layer_idx xp xn)
      (round_layers ! round_idx ! layer_idx)"
    using step v_eq by simp
  from forced' obtain yp yp_path yn yn_path where step':
    "fri_layer_step_evidence
      (roots ! layer_idx)
      ?ch
      ?len
      ?raw'
      ?pw
      (fri_sibling_index ?len ?raw')
      yp yp_path yn yn_path
      (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
      v'
      (round_layers ! round_idx' ! layer_idx)"
    unfolding generic_fri_round_forced_next_value_def by blast
  have v'_eq:
    "v' = fri_evidence_next_value roots challenges query_idxs round_idx'
      layer_idx yp yn"
    using fri_layer_step_evidenceD(3)[OF step']
    unfolding fri_evidence_next_value_def by simp
  have step'_norm:
    "fri_layer_step_evidence
      (roots ! layer_idx)
      ?ch
      ?len
      ?raw'
      ?pw
      (fri_sibling_index ?len ?raw')
      yp yp_path yn yn_path
      (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
      (fri_evidence_next_value roots challenges query_idxs round_idx'
        layer_idx yp yn)
      (round_layers ! round_idx' ! layer_idx)"
    using step' v'_eq by simp
  have same_mod: "?raw mod (?len div 2) = ?raw' mod (?len div 2)"
    using same_next unfolding fri_evidence_next_idx_def by simp
  have idx_cases:
    "?raw = ?raw' \<or>
     ?raw = fri_sibling_index ?len ?raw' \<or>
     fri_sibling_index ?len ?raw = ?raw'"
    by (rule fri_same_mod_half_index_cases3
        [OF even_len raw_bound raw_bound' same_mod])
  from idx_cases show ?thesis
  proof
    assume raw_eq: "?raw = ?raw'"
    have xp_eq: "xp = yp"
      by (rule generic_fri_no_same_layer_opening_conflict_left_left
          [OF no_same round_bound round_bound' layer_bound step_norm
            step'_norm])
        (rule raw_eq)
    have xn_eq: "xn = yn"
      by (rule generic_fri_no_same_layer_opening_conflict_right_right
          [OF no_same round_bound round_bound' layer_bound step_norm
            step'_norm])
        (use raw_eq in simp)
    show ?thesis
      using v_eq v'_eq raw_eq xp_eq xn_eq
      unfolding fri_evidence_next_value_def
      by simp
  next
    assume raw_or_sib:
      "?raw = fri_sibling_index ?len ?raw' \<or>
       fri_sibling_index ?len ?raw = ?raw'"
    then show ?thesis
    proof
      assume raw_sib: "?raw = fri_sibling_index ?len ?raw'"
      have sib_raw: "fri_sibling_index ?len ?raw = ?raw'"
        using raw_sib
          fri_sibling_index_involution[OF even_len raw_bound']
        by simp
      have xp_eq: "xp = yn"
        by (rule generic_fri_no_same_layer_opening_conflict_left_right
            [OF no_same round_bound round_bound' layer_bound step_norm
              step'_norm])
          (rule raw_sib)
      have xn_eq: "xn = yp"
        by (rule generic_fri_no_same_layer_opening_conflict_right_left
            [OF no_same round_bound round_bound' layer_bound step_norm
              step'_norm])
          (rule sib_raw)
      have fold_eq:
        "fri_fold_value ?ch xp xn
          (fri_fold_denominator ((h ^ ?raw) * shift) ?pw) =
         fri_fold_value ?ch yp yn
          (fri_fold_denominator ((h ^ ?raw') * shift) ?pw)"
        using fri_fold_value_sibling_verifier
          [OF len_pos even_len round_product,
            where i="?raw'" and b="?ch" and xn="yn" and xp="yp"]
          raw_sib xp_eq xn_eq
        by simp
      show ?thesis
        using v_eq v'_eq fold_eq
        unfolding fri_evidence_next_value_def
        by simp
    next
      assume sib_raw: "fri_sibling_index ?len ?raw = ?raw'"
      have raw_sib: "?raw = fri_sibling_index ?len ?raw'"
        using sib_raw fri_sibling_index_involution[OF even_len raw_bound]
        by simp
      have xn_eq: "xn = yp"
        by (rule generic_fri_no_same_layer_opening_conflict_right_left
            [OF no_same round_bound round_bound' layer_bound step_norm
              step'_norm])
          (rule sib_raw)
      have xp_eq: "xp = yn"
        by (rule generic_fri_no_same_layer_opening_conflict_left_right
            [OF no_same round_bound round_bound' layer_bound step_norm
              step'_norm])
          (rule raw_sib)
      have fold_eq:
        "fri_fold_value ?ch yp yn
          (fri_fold_denominator ((h ^ ?raw') * shift) ?pw) =
         fri_fold_value ?ch xp xn
          (fri_fold_denominator ((h ^ ?raw) * shift) ?pw)"
        using fri_fold_value_sibling_verifier
          [OF len_pos even_len round_product,
            where i="?raw" and b="?ch" and xn="xn" and xp="xp"]
          sib_raw xp_eq xn_eq
        by simp
      show ?thesis
        using v_eq v'_eq fold_eq
        unfolding fri_evidence_next_value_def
        by simp
    qed
  qed
qed

lemma accepted_fri_opening_transcript_composition_layer_arithmetic:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and layer_bound: "layer_idx < length composition_bs"
  shows "2 dvd fri_evidence_layer_len composition_roots layer_idx"
    and "fri_evidence_layer_len composition_roots layer_idx * 2 ^ layer_idx =
      clength * scale"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have bs_len: "length composition_bs = length composition_roots"
    using accepted_fri_opening_transcript_shapes(4)[OF fri_openings] .
  have roots_bound: "layer_idx < length composition_roots"
    using layer_bound bs_len by simp
  have roots_le: "length composition_roots \<le> N"
  proof -
    have len: "length composition_roots = ceil_log (to_nat dg + 1)"
      using accepted_fri_opening_transcript_shapes(3)[OF fri_openings] .
    have "to_nat dg + 1 \<le> clength * scale"
      using degree_bound maxDegree_less_eval_domain by linarith
    also have "... = 2 ^ N"
      by (rule eval_power)
    finally have "ceil_log (to_nat dg + 1) \<le> N"
      by (rule ceil_log_le_power)
    then show ?thesis
      using len by simp
  qed
  have suc_le: "Suc layer_idx \<le> N"
    using roots_bound roots_le by simp
  have dvd_eval_suc: "(2::nat) ^ Suc layer_idx dvd clength * scale"
    using le_imp_power_dvd[OF suc_le] eval_power by simp
  show "2 dvd fri_evidence_layer_len composition_roots layer_idx"
    unfolding fri_evidence_layer_len_def
    by (rule fri_layer_lengths_even_if_dvd[OF roots_bound dvd_eval_suc])
  have le_N: "layer_idx \<le> N"
    using roots_bound roots_le by simp
  have dvd_eval: "(2::nat) ^ layer_idx dvd clength * scale"
    using le_imp_power_dvd[OF le_N] eval_power by simp
  show "fri_evidence_layer_len composition_roots layer_idx *
      2 ^ layer_idx = clength * scale"
    unfolding fri_evidence_layer_len_def
    by (rule fri_layer_lengths_round_product_if_dvd
      [OF roots_bound dvd_eval])
qed

lemma accepted_fri_opening_transcript_composition_evidence_layer_idx_bound:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length composition_roots"
  shows
    "fri_evidence_layer_idx composition_roots query_idxs round_idx layer_idx <
      fri_evidence_layer_len composition_roots layer_idx"
proof -
  obtain raw_idxs query_chunks query_state where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    using fri_openings
    by (auto simp: accepted_fri_opening_transcript_def)
  have len_query: "length query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes(7)[OF fri_openings] .
  have round_raw_bound: "round_idx < length raw_idxs"
    using round_bound len_query len_raw by simp
  have query_idx_eq:
    "query_idxs ! round_idx = index (to_nat (raw_idxs ! round_idx))"
    using query_idxs_eq round_raw_bound by simp
  have raw_layer:
    "0 < fri_layer_lengths (length composition_roots)
        (clength * scale) ! layer_idx \<and>
     fri_layer_indices (length composition_roots)
        (index (to_nat (raw_idxs ! round_idx))) (clength * scale) !
        layer_idx <
     fri_layer_lengths (length composition_roots)
        (clength * scale) ! layer_idx"
    by (rule accepted_fri_opening_transcript_composition_raw_layer_bound
        [OF fri_openings degree_bound layer_bound])
  show ?thesis
    using raw_layer query_idx_eq
    unfolding fri_evidence_layer_idx_def fri_evidence_layer_len_def
    by simp
qed

lemma generic_fri_forced_next_value_eq_from_recorded_step:
  assumes forced:
    "generic_fri_round_forced_next_value roots challenges query_idxs
      round_layers round_idx layer_idx v"
    and step:
    "fri_layer_step_evidence
      (roots ! layer_idx)
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
      xp xp_path xn xn_path
      (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
      v'
      (round_layers ! round_idx ! layer_idx)"
  shows "v = v'"
proof -
  from forced obtain yp yp_path yn yn_path where forced_step:
    "fri_layer_step_evidence
      (roots ! layer_idx)
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
      yp yp_path yn yn_path
      (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
      v
      (round_layers ! round_idx ! layer_idx)"
    unfolding generic_fri_round_forced_next_value_def by blast
  have yp_eq: "yp = xp"
    by (rule fri_layer_opening_chunk_values_unique(1))
      (rule fri_layer_step_evidenceD(4)[OF forced_step],
       rule fri_layer_step_evidenceD(4)[OF step])
  have yn_eq: "yn = xn"
    by (rule fri_layer_opening_chunk_values_unique(2))
      (rule fri_layer_step_evidenceD(4)[OF forced_step],
       rule fri_layer_step_evidenceD(4)[OF step])
  show ?thesis
    using fri_layer_step_evidenceD(3)[OF forced_step]
      fri_layer_step_evidenceD(3)[OF step]
      yp_eq yn_eq
    by simp
qed

lemma fri_layer_indices_tail_nth:
  "fri_layer_indices (Suc j) (q mod (len div 2)) (len div 2) ! j =
    fri_layer_indices (Suc j) q len ! j mod
      (fri_layer_lengths (Suc j) len ! j div 2)"
  by (induction j arbitrary: q len) simp_all

lemma fri_layer_indices_Suc_nth:
  assumes layer_bound: "Suc j < n"
  shows
    "fri_layer_indices n q len ! Suc j =
      fri_layer_indices n q len ! j mod
        (fri_layer_lengths n len ! j div 2)"
proof -
  have idx_Suc:
    "fri_layer_indices n q len ! Suc j =
      fri_layer_indices (Suc (Suc j)) q len ! Suc j"
    using fri_layer_indices_prefix_nth[OF layer_bound, of q len] by simp
  have idx_j:
    "fri_layer_indices n q len ! j =
      fri_layer_indices (Suc j) q len ! j"
    using fri_layer_indices_prefix_nth[of j n q len] layer_bound by simp
  have len_j:
    "fri_layer_lengths n len ! j =
      fri_layer_lengths (Suc j) len ! j"
    using fri_layer_lengths_prefix_nth[of j n len] layer_bound by simp
  show ?thesis
    unfolding idx_Suc idx_j len_j
    using fri_layer_indices_tail_nth[of j q len]
    by simp
qed

lemma fri_evidence_layer_idx_Suc:
  assumes layer_bound: "Suc layer_idx < length roots"
  shows
    "fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx) =
      fri_evidence_next_idx roots query_idxs round_idx layer_idx"
  using fri_layer_indices_Suc_nth[OF layer_bound,
      of "query_idxs ! round_idx" "clength * scale"]
  unfolding fri_evidence_layer_idx_def fri_evidence_next_idx_def
    fri_evidence_layer_len_def
  by simp

lemma mfold_fri_layer_openings_successor_prefix_step:
  fixes s s_suc :: "('f, 'a) protocol_channel_scheme"
  assumes prefix_suc:
    "Some ((idx_suc, x_suc, len_suc, pw_suc), s_suc) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take (Suc j) (map fri_layer_opening_step bfs))) s)"
    and j_bound: "j < length bfs"
  obtains idx_j x_j len_j pw_j b rt xp xp_path xn xn_path s_j where
    "bfs ! j = (b, rt)"
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    "Some ((idx_suc, x_suc, len_suc, pw_suc), s_suc) \<in>
      set_dist
        (execute
          (fri_layer_opening_step (b, rt) (idx_j, x_j, len_j, pw_j))
          s_j)"
    "fri_layer_step_evidence rt b len_j idx_j pw_j
      (fri_sibling_index len_j idx_j) xp xp_path xn xn_path
      idx_suc x_suc ([xp] @ xp_path @ [xn] @ xn_path)"
proof -
  let ?bfs = "take (Suc j) bfs"
  have j_bound_take: "j < length ?bfs"
    using j_bound by simp
  have take_map:
    "take (Suc j) (map fri_layer_opening_step bfs) =
      map fri_layer_opening_step ?bfs"
    by (simp add: take_map)
  show ?thesis
  proof (rule mfold_fri_layer_openings_decomp_at
      [OF prefix_suc[unfolded take_map] j_bound_take])
    fix idx_j x_j len_j pw_j out_j s_j s_j_suc
    assume prefix:
      "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (take j (map fri_layer_opening_step ?bfs))) s)"
      and selected:
      "Some (out_j, s_j_suc) \<in>
        set_dist
          (execute
            (fri_layer_opening_step (?bfs ! j)
              (idx_j, x_j, len_j, pw_j)) s_j)"
      and suffix:
      "Some ((idx_suc, x_suc, len_suc, pw_suc), s_suc) \<in>
        set_dist
          (execute
            (mfold out_j
              (drop (Suc j) (map fri_layer_opening_step ?bfs))) s_j_suc)"
    have drop_empty:
      "drop (Suc j) (map fri_layer_opening_step ?bfs) = []"
      by simp
    have out_j_eq: "out_j = (idx_suc, x_suc, len_suc, pw_suc)"
      and s_suc_eq: "s_suc = s_j_suc"
      using suffix unfolding drop_empty by simp_all
    have take_prefix_list: "take j ?bfs = take j bfs"
      by (simp add: take_take)
    have take_prefix:
      "take j (map fri_layer_opening_step ?bfs) =
        take j (map fri_layer_opening_step bfs)"
    proof (rule nth_equalityI)
      show "length (take j (map fri_layer_opening_step ?bfs)) =
        length (take j (map fri_layer_opening_step bfs))"
        by simp
    next
      fix i
      assume i_bound: "i < length (take j (map fri_layer_opening_step ?bfs))"
      then have "i < j"
        by simp
      then show "take j (map fri_layer_opening_step ?bfs) ! i =
        take j (map fri_layer_opening_step bfs) ! i"
        using j_bound by simp
    qed
    have bfs_j: "?bfs ! j = bfs ! j"
      using j_bound by simp
    obtain b rt where bf_eq: "bfs ! j = (b, rt)"
      by (cases "bfs ! j")
    show ?thesis
    proof (rule fri_layer_opening_step_outcome_evidence
        [OF selected[unfolded bfs_j bf_eq out_j_eq]])
      fix xp xp_path xn xn_path
      assume xp_eq: "xp = x_j"
        and next_idx_eq: "idx_suc = idx_j mod (len_j div 2)"
        and next_len_eq: "len_suc = len_j div 2"
        and next_pow_eq: "pw_suc = pw_j + pw_j"
        and step:
        "fri_layer_step_evidence rt b len_j idx_j pw_j
          (fri_sibling_index len_j idx_j) xp xp_path xn xn_path
          idx_suc x_suc ([xp] @ xp_path @ [xn] @ xn_path)"
      have selected_suc:
        "Some ((idx_suc, x_suc, len_suc, pw_suc), s_suc) \<in>
          set_dist
            (execute
              (fri_layer_opening_step (b, rt)
                (idx_j, x_j, len_j, pw_j)) s_j)"
        using selected[unfolded bfs_j bf_eq out_j_eq] s_suc_eq by simp
      show ?thesis
        by (rule that[OF bf_eq prefix[unfolded take_prefix]
              selected_suc step])
    qed
  qed
qed

lemma mfold_fri_layer_opening_selected_recorded_step_evidence_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (map fri_layer_opening_step bfs)) s)"
    and layers:
      "fri_layers_transcript (length bfs) len layer_chunks total_chunk"
    and transcript:
      "PTranscript s = total_chunk @ PTranscript t"
    and initial_idx_bound: "idx < len"
    and all_layer_bounds:
      "\<And>k. k < length bfs \<Longrightarrow>
        0 < fri_layer_lengths (length bfs) len ! k \<and>
        fri_layer_indices (length bfs) idx len ! k <
          fri_layer_lengths (length bfs) len ! k"
    and j_bound: "j < length bfs"
  shows
    "\<exists>xp xp_path xn xn_path next_value.
      fri_layer_step_evidence (snd (bfs ! j)) (fst (bfs ! j))
      (fri_layer_lengths (length bfs) len ! j)
      (fri_layer_indices (length bfs) idx len ! j)
      (pw * 2 ^ j)
      (fri_sibling_index (fri_layer_lengths (length bfs) len ! j)
        (fri_layer_indices (length bfs) idx len ! j))
      xp xp_path xn xn_path
      (fri_layer_indices (length bfs) idx len ! j mod
        (fri_layer_lengths (length bfs) len ! j div 2))
      next_value
      (layer_chunks ! j)"
proof -
  show ?thesis
    using outcome layers transcript initial_idx_bound all_layer_bounds
      j_bound
  proof (induction bfs arbitrary: idx x len pw s out t j layer_chunks total_chunk)
    case Nil
    then show ?case by simp
  next
    case (Cons bf bfs)
    obtain b rt where bf_eq: "bf = (b, rt)"
      by (cases bf)
    from Cons.prems(1)[unfolded bf_eq]
    obtain out1 s1 where
      head:
        "Some (out1, s1) \<in>
          set_dist
            (execute (fri_layer_opening_step (b, rt)
              (idx, x, len, pw)) s)"
      and tail:
        "Some (out, t) \<in>
          set_dist
            (execute (mfold out1 (map fri_layer_opening_step bfs)) s1)"
      by (auto elim!: set_dist_bindE)
    obtain first rest where chunks_eq: "layer_chunks = first # rest"
      using Cons.prems(6) Cons.prems(2)
      unfolding fri_layers_transcript_def by (cases layer_chunks) auto
    have total_eq: "total_chunk = first @ List.concat rest"
      using Cons.prems(2) unfolding fri_layers_transcript_def chunks_eq
      by simp
    have first_open:
      "\<exists>yp yp_path yn yn_path.
        fri_layer_opening_chunk len yp yp_path yn yn_path first"
      using Cons.prems(2) unfolding fri_layers_transcript_def chunks_eq
      by auto
    have rest_layers:
      "fri_layers_transcript (length bfs) (len div 2) rest
        (List.concat rest)"
      using Cons.prems(2) unfolding fri_layers_transcript_def chunks_eq
      by auto
    obtain x1 xp xp_path xn xn_path head_chunk where out1_eq:
        "out1 = (idx mod (len div 2), x1, len div 2, pw + pw)"
      and head_chunk_def: "head_chunk = [xp] @ xp_path @ [xn] @ xn_path"
      and head_open:
        "fri_layer_opening_chunk len xp xp_path xn xn_path head_chunk"
      and head_transcript:
        "PTranscript s = head_chunk @ PTranscript s1"
      and head_step:
        "fri_layer_step_evidence rt b len idx pw
          (fri_sibling_index len idx) xp xp_path xn xn_path
          (idx mod (len div 2)) x1 head_chunk"
    proof -
      have len_pos: "0 < len"
        using Cons.prems(5)[of 0] by simp
      have idx_bound: "idx < len"
        by (rule Cons.prems(4))
      show ?thesis
      proof (rule fri_layer_opening_step_outcome_authenticated
          [OF len_pos idx_bound head])
        fix xp' xp_path' xn' xn_path' x' chunk
        assume out_eq:
            "out1 = (idx mod (len div 2), x', len div 2, pw + pw)"
          and xp_eq: "xp' = x"
          and x'_eq:
            "x' = fri_fold_value b xp' xn'
              (fri_fold_denominator ((h ^ idx) * shift) pw)"
          and chunk_eq: "chunk = [xp'] @ xp_path' @ [xn'] @ xn_path'"
          and chunk_open:
            "fri_layer_opening_chunk len xp' xp_path' xn' xn_path'
              chunk"
          and tr: "PTranscript s = chunk @ PTranscript s1"
          assume
            "s \<le> s1"
            "PState s1 = foldl concat (PState s) chunk"
            "PQueryCounter s1 = PQueryCounter s"
            "authenticated_opening_in s1
              \<lparr>opening_root = rt, opening_length = len,
               opening_index = idx, opening_value = xp',
               opening_path = xp_path'\<rparr>"
            "authenticated_opening_in s1
              \<lparr>opening_root = rt, opening_length = len,
               opening_index = fri_sibling_index len idx,
               opening_value = xn', opening_path = xn_path'\<rparr>"
        have step:
          "fri_layer_step_evidence rt b len idx pw
            (fri_sibling_index len idx) xp' xp_path' xn' xn_path'
            (idx mod (len div 2)) x' chunk"
          by (rule fri_layer_step_evidenceI)
            (use x'_eq chunk_open in simp_all)
        show ?thesis
          by (rule that[OF out_eq chunk_eq chunk_open tr step])
      qed
    qed
    from mfold_fri_layer_openings_outcome[OF tail[unfolded out1_eq]]
    obtain tail_layers tail_chunk where
      tail_transcript:
        "PTranscript s1 = tail_chunk @ PTranscript t"
      by blast
    have head_len:
      "length head_chunk = length first"
    proof -
      obtain yp yp_path yn yn_path where first_open':
        "fri_layer_opening_chunk len yp yp_path yn yn_path first"
        using first_open by blast
      show ?thesis
        using fri_layer_opening_chunk_length[OF head_open]
          fri_layer_opening_chunk_length[OF first_open']
        by simp
    qed
    have chunks_total_eq:
      "head_chunk @ tail_chunk = first @ List.concat rest"
      using head_transcript tail_transcript Cons.prems(3) total_eq by simp
    have head_eq: "head_chunk = first"
      using arg_cong[OF chunks_total_eq,
        of "take (length head_chunk)"]
        head_len
      by simp
    have tail_chunk_eq: "tail_chunk = List.concat rest"
      using chunks_total_eq head_eq by simp
    have tail_transcript_rest:
      "PTranscript s1 = List.concat rest @ PTranscript t"
      using tail_transcript tail_chunk_eq by simp
    show ?case
    proof (cases j)
      case 0
      have step:
        "fri_layer_step_evidence (snd ((bf # bfs) ! j))
          (fst ((bf # bfs) ! j))
          (fri_layer_lengths (length (bf # bfs)) len ! j)
          (fri_layer_indices (length (bf # bfs)) idx len ! j)
          (pw * 2 ^ j)
          (fri_sibling_index
            (fri_layer_lengths (length (bf # bfs)) len ! j)
            (fri_layer_indices (length (bf # bfs)) idx len ! j))
          xp xp_path xn xn_path
          (fri_layer_indices (length (bf # bfs)) idx len ! j mod
            (fri_layer_lengths (length (bf # bfs)) len ! j div 2))
          x1 (layer_chunks ! j)"
        using head_step 0 bf_eq head_eq chunks_eq by simp
      show ?thesis
        using step by blast
    next
      case (Suc k)
      have k_bound: "k < length bfs"
        using Cons.prems(6) Suc by simp
      have tail_all_layer_bounds:
        "\<And>m. m < length bfs \<Longrightarrow>
          0 < fri_layer_lengths (length bfs) (len div 2) ! m \<and>
          fri_layer_indices (length bfs) (idx mod (len div 2))
            (len div 2) ! m <
          fri_layer_lengths (length bfs) (len div 2) ! m"
        using Cons.prems(5)[of "Suc m" for m] by simp
      have tail_initial_idx_bound:
        "idx mod (len div 2) < len div 2"
        using tail_all_layer_bounds[of 0] k_bound by (cases bfs) simp_all
      from Cons.IH[OF tail[unfolded out1_eq] rest_layers
          tail_transcript_rest tail_initial_idx_bound tail_all_layer_bounds
          k_bound]
      obtain txp txp_path txn txn_path tnext where tail_step:
        "fri_layer_step_evidence (snd (bfs ! k)) (fst (bfs ! k))
          (fri_layer_lengths (length bfs) (len div 2) ! k)
          (fri_layer_indices (length bfs) (idx mod (len div 2))
            (len div 2) ! k)
          ((pw + pw) * 2 ^ k)
          (fri_sibling_index
            (fri_layer_lengths (length bfs) (len div 2) ! k)
            (fri_layer_indices (length bfs) (idx mod (len div 2))
              (len div 2) ! k))
          txp txp_path txn txn_path
          (fri_layer_indices (length bfs) (idx mod (len div 2))
            (len div 2) ! k mod
            (fri_layer_lengths (length bfs) (len div 2) ! k div 2))
          tnext (rest ! k)"
        by blast
      have pow_eq: "(pw + pw) * 2 ^ k = pw * 2 ^ Suc k"
        by (simp add: algebra_simps)
      have step:
        "fri_layer_step_evidence (snd ((bf # bfs) ! j))
          (fst ((bf # bfs) ! j))
          (fri_layer_lengths (length (bf # bfs)) len ! j)
          (fri_layer_indices (length (bf # bfs)) idx len ! j)
          (pw * 2 ^ j)
          (fri_sibling_index
            (fri_layer_lengths (length (bf # bfs)) len ! j)
            (fri_layer_indices (length (bf # bfs)) idx len ! j))
          txp txp_path txn txn_path
          (fri_layer_indices (length (bf # bfs)) idx len ! j mod
            (fri_layer_lengths (length (bf # bfs)) len ! j div 2))
          tnext (layer_chunks ! j)"
        using tail_step Suc chunks_eq pow_eq by simp
      show ?thesis
        using step by blast
    qed
  qed
qed

lemma mfold_fri_layer_opening_first_recorded_step_evidence:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (map fri_layer_opening_step bfs)) s)"
    and layers:
      "fri_layers_transcript (length bfs) len layer_chunks total_chunk"
    and transcript:
      "PTranscript s = total_chunk @ PTranscript t"
    and nonempty: "0 < length bfs"
  shows
    "\<exists>xp_path xn xn_path next_value.
      fri_layer_step_evidence (snd (bfs ! 0)) (fst (bfs ! 0))
      (fri_layer_lengths (length bfs) len ! 0)
      (fri_layer_indices (length bfs) idx len ! 0)
      pw
      (fri_sibling_index (fri_layer_lengths (length bfs) len ! 0)
        (fri_layer_indices (length bfs) idx len ! 0))
      x xp_path xn xn_path
      (fri_layer_indices (length bfs) idx len ! 0 mod
        (fri_layer_lengths (length bfs) len ! 0 div 2))
      next_value
      (layer_chunks ! 0)"
proof -
  obtain bf bfs' where bfs_eq: "bfs = bf # bfs'"
    using nonempty by (cases bfs) auto
  obtain b rt where bf_eq: "bf = (b, rt)"
    by (cases bf)
  from outcome[unfolded bfs_eq bf_eq]
  obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt)
            (idx, x, len, pw)) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist
          (execute (mfold out1 (map fri_layer_opening_step bfs')) s1)"
    by (auto elim!: set_dist_bindE)
  obtain first rest where chunks_eq: "layer_chunks = first # rest"
    using layers nonempty unfolding bfs_eq fri_layers_transcript_def
    by (cases layer_chunks) auto
  have total_eq: "total_chunk = first @ List.concat rest"
    using layers unfolding bfs_eq fri_layers_transcript_def chunks_eq
    by simp
  have first_open:
    "\<exists>yp yp_path yn yn_path.
      fri_layer_opening_chunk len yp yp_path yn yn_path first"
    using layers unfolding bfs_eq fri_layers_transcript_def chunks_eq
    by auto
  obtain x1 xp xp_path xn xn_path head_chunk where out1_eq:
      "out1 = (idx mod (len div 2), x1, len div 2, pw + pw)"
    and head_chunk_def: "head_chunk = [xp] @ xp_path @ [xn] @ xn_path"
    and xp_eq: "xp = x"
    and head_open:
      "fri_layer_opening_chunk len xp xp_path xn xn_path head_chunk"
    and head_transcript:
      "PTranscript s = head_chunk @ PTranscript s1"
    and head_step:
      "fri_layer_step_evidence rt b len idx pw
        (fri_sibling_index len idx) xp xp_path xn xn_path
        (idx mod (len div 2)) x1 head_chunk"
  proof -
    from fri_layer_opening_step_outcome[OF head]
    obtain xp' xp_path' xn' xn_path' x' where out1_eq':
        "out1 = (idx mod (len div 2), x', len div 2, pw + pw)"
      and xp'_eq: "xp' = x"
      and x'_eq:
        "x' = fri_fold_value b xp' xn'
          (fri_fold_denominator ((h ^ idx) * shift) pw)"
      and chunk_open:
        "fri_layer_opening_chunk len xp' xp_path' xn' xn_path'
          ([xp'] @ xp_path' @ [xn'] @ xn_path')"
      and tr:
        "PTranscript s =
          ([xp'] @ xp_path' @ [xn'] @ xn_path') @ PTranscript s1"
      by blast
    have step:
      "fri_layer_step_evidence rt b len idx pw
        (fri_sibling_index len idx) xp' xp_path' xn' xn_path'
        (idx mod (len div 2)) x'
        ([xp'] @ xp_path' @ [xn'] @ xn_path')"
      by (rule fri_layer_step_evidenceI)
        (use x'_eq chunk_open in simp_all)
    show ?thesis
      by (rule that[OF out1_eq' refl xp'_eq chunk_open tr step])
  qed
  from mfold_fri_layer_openings_outcome[OF tail[unfolded out1_eq]]
  obtain tail_layers tail_chunk where
    tail_transcript:
      "PTranscript s1 = tail_chunk @ PTranscript t"
    by blast
  have head_len:
    "length head_chunk = length first"
  proof -
    obtain yp yp_path yn yn_path where first_open':
      "fri_layer_opening_chunk len yp yp_path yn yn_path first"
      using first_open by blast
    show ?thesis
      using fri_layer_opening_chunk_length[OF head_open]
        fri_layer_opening_chunk_length[OF first_open']
      by simp
  qed
  have chunks_total_eq:
    "head_chunk @ tail_chunk = first @ List.concat rest"
    using head_transcript tail_transcript transcript total_eq by simp
  have head_eq: "head_chunk = first"
    using arg_cong[OF chunks_total_eq,
      of "take (length head_chunk)"]
      head_len
    by simp
  have step:
    "fri_layer_step_evidence (snd (bfs ! 0)) (fst (bfs ! 0))
      (fri_layer_lengths (length bfs) len ! 0)
      (fri_layer_indices (length bfs) idx len ! 0)
      pw
      (fri_sibling_index (fri_layer_lengths (length bfs) len ! 0)
        (fri_layer_indices (length bfs) idx len ! 0))
      x xp_path xn xn_path
      (fri_layer_indices (length bfs) idx len ! 0 mod
        (fri_layer_lengths (length bfs) len ! 0 div 2))
      x1
      (layer_chunks ! 0)"
    using head_step bfs_eq bf_eq chunks_eq head_eq xp_eq by simp
  show ?thesis
    using step by blast
qed

lemma mfold_fri_layer_opening_successor_recorded_step_from_previous:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (map fri_layer_opening_step bfs)) s)"
    and layers:
      "fri_layers_transcript (length bfs) len layer_chunks total_chunk"
    and transcript:
      "PTranscript s = total_chunk @ PTranscript t"
    and initial_idx_bound: "idx < len"
    and all_layer_bounds:
      "\<And>k. k < length bfs \<Longrightarrow>
        0 < fri_layer_lengths (length bfs) len ! k \<and>
        fri_layer_indices (length bfs) idx len ! k <
          fri_layer_lengths (length bfs) len ! k"
    and j_bound: "Suc j < length bfs"
    and previous_step:
      "fri_layer_step_evidence (snd (bfs ! j)) (fst (bfs ! j))
        (fri_layer_lengths (length bfs) len ! j)
        (fri_layer_indices (length bfs) idx len ! j)
        (pw * 2 ^ j)
        (fri_sibling_index
          (fri_layer_lengths (length bfs) len ! j)
          (fri_layer_indices (length bfs) idx len ! j))
        xp xp_path xn xn_path
        (fri_layer_indices (length bfs) idx len ! j mod
          (fri_layer_lengths (length bfs) len ! j div 2))
        v
        (layer_chunks ! j)"
  shows
    "\<exists>xp_path' xn' xn_path' next_value.
      fri_layer_step_evidence (snd (bfs ! Suc j)) (fst (bfs ! Suc j))
        (fri_layer_lengths (length bfs) len ! Suc j)
        (fri_layer_indices (length bfs) idx len ! Suc j)
        (pw * 2 ^ Suc j)
        (fri_sibling_index
          (fri_layer_lengths (length bfs) len ! Suc j)
          (fri_layer_indices (length bfs) idx len ! Suc j))
        v xp_path' xn' xn_path'
        (fri_layer_indices (length bfs) idx len ! Suc j mod
          (fri_layer_lengths (length bfs) len ! Suc j div 2))
        next_value
        (layer_chunks ! Suc j)"
  using outcome layers transcript initial_idx_bound all_layer_bounds j_bound
    previous_step
proof (induction bfs arbitrary: idx x len pw s out t j layer_chunks total_chunk
    xp xp_path xn xn_path v)
  case Nil
  then show ?case by simp
next
  case (Cons bf bfs)
  obtain b rt where bf_eq: "bf = (b, rt)"
    by (cases bf)
  from Cons.prems(1)[unfolded bf_eq]
  obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt)
            (idx, x, len, pw)) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist
          (execute (mfold out1 (map fri_layer_opening_step bfs)) s1)"
    by (auto elim!: set_dist_bindE)
  obtain first rest where chunks_eq: "layer_chunks = first # rest"
    using Cons.prems(2) Cons.prems(6)
    unfolding fri_layers_transcript_def by (cases layer_chunks) auto
  have total_eq: "total_chunk = first @ List.concat rest"
    using Cons.prems(2) unfolding fri_layers_transcript_def chunks_eq
    by simp
  have first_open:
    "\<exists>yp yp_path yn yn_path.
      fri_layer_opening_chunk len yp yp_path yn yn_path first"
    using Cons.prems(2) unfolding fri_layers_transcript_def chunks_eq
    by auto
  have rest_layers:
    "fri_layers_transcript (length bfs) (len div 2) rest
      (List.concat rest)"
    using Cons.prems(2) unfolding fri_layers_transcript_def chunks_eq
    by auto
  obtain x1 hxp hxp_path hxn hxn_path head_chunk where out1_eq:
      "out1 = (idx mod (len div 2), x1, len div 2, pw + pw)"
    and hxp_eq: "hxp = x"
    and head_open:
      "fri_layer_opening_chunk len hxp hxp_path hxn hxn_path head_chunk"
    and head_transcript:
      "PTranscript s = head_chunk @ PTranscript s1"
    and head_step:
      "fri_layer_step_evidence rt b len idx pw
        (fri_sibling_index len idx) hxp hxp_path hxn hxn_path
        (idx mod (len div 2)) x1 head_chunk"
  proof -
    from fri_layer_opening_step_outcome[OF head]
    obtain xp' xp_path' xn' xn_path' x' where out1_eq':
        "out1 = (idx mod (len div 2), x', len div 2, pw + pw)"
      and xp'_eq: "xp' = x"
      and x'_eq:
        "x' = fri_fold_value b xp' xn'
          (fri_fold_denominator ((h ^ idx) * shift) pw)"
      and chunk_open:
        "fri_layer_opening_chunk len xp' xp_path' xn' xn_path'
          ([xp'] @ xp_path' @ [xn'] @ xn_path')"
      and tr:
        "PTranscript s =
          ([xp'] @ xp_path' @ [xn'] @ xn_path') @ PTranscript s1"
      by blast
    have step:
      "fri_layer_step_evidence rt b len idx pw
        (fri_sibling_index len idx) xp' xp_path' xn' xn_path'
        (idx mod (len div 2)) x'
        ([xp'] @ xp_path' @ [xn'] @ xn_path')"
      by (rule fri_layer_step_evidenceI)
        (use x'_eq chunk_open in simp_all)
    show ?thesis
      by (rule that[OF out1_eq' xp'_eq chunk_open tr step])
  qed
  from mfold_fri_layer_openings_outcome[OF tail[unfolded out1_eq]]
  obtain tail_layers tail_chunk where
    tail_transcript:
      "PTranscript s1 = tail_chunk @ PTranscript t"
    by blast
  have head_len:
    "length head_chunk = length first"
  proof -
    obtain yp yp_path yn yn_path where first_open':
      "fri_layer_opening_chunk len yp yp_path yn yn_path first"
      using first_open by blast
    show ?thesis
      using fri_layer_opening_chunk_length[OF head_open]
        fri_layer_opening_chunk_length[OF first_open']
      by simp
  qed
  have chunks_total_eq:
    "head_chunk @ tail_chunk = first @ List.concat rest"
    using head_transcript tail_transcript Cons.prems(3) total_eq by simp
  have head_eq: "head_chunk = first"
    using arg_cong[OF chunks_total_eq,
      of "take (length head_chunk)"]
      head_len
    by simp
  have tail_chunk_eq: "tail_chunk = List.concat rest"
    using chunks_total_eq head_eq by simp
  have tail_transcript_rest:
    "PTranscript s1 = List.concat rest @ PTranscript t"
    using tail_transcript tail_chunk_eq by simp
  show ?case
  proof (cases j)
    case 0
    have prev_head:
      "fri_layer_step_evidence rt b len idx pw
        (fri_sibling_index len idx) xp xp_path xn xn_path
        (idx mod (len div 2)) v first"
      using Cons.prems(7) 0 bf_eq chunks_eq by simp
    have v_eq_x1: "v = x1"
    proof -
      have xp_eq: "xp = hxp"
        by (rule fri_layer_opening_chunk_values_unique(1))
          (rule fri_layer_step_evidenceD(4)[OF prev_head],
           rule fri_layer_step_evidenceD(4)[OF head_step[unfolded head_eq]])
      have xn_eq: "xn = hxn"
        by (rule fri_layer_opening_chunk_values_unique(2))
          (rule fri_layer_step_evidenceD(4)[OF prev_head],
           rule fri_layer_step_evidenceD(4)[OF head_step[unfolded head_eq]])
      show ?thesis
        using fri_layer_step_evidenceD(3)[OF prev_head]
          fri_layer_step_evidenceD(3)[OF head_step[unfolded head_eq]]
          xp_eq xn_eq
        by simp
    qed
    have bfs_nonempty: "0 < length bfs"
      using Cons.prems(6) 0 by simp
    from mfold_fri_layer_opening_first_recorded_step_evidence
        [OF tail[unfolded out1_eq] rest_layers tail_transcript_rest
          bfs_nonempty]
    obtain sxp_path sxn sxn_path snext where succ_step_tail:
      "fri_layer_step_evidence (snd (bfs ! 0)) (fst (bfs ! 0))
        (fri_layer_lengths (length bfs) (len div 2) ! 0)
        (fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! 0)
        (pw + pw)
        (fri_sibling_index
          (fri_layer_lengths (length bfs) (len div 2) ! 0)
          (fri_layer_indices (length bfs) (idx mod (len div 2))
            (len div 2) ! 0))
        x1 sxp_path sxn sxn_path
        (fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! 0 mod
          (fri_layer_lengths (length bfs) (len div 2) ! 0 div 2))
        snext
        (rest ! 0)"
      by blast
    have pow_eq: "pw + pw = pw * 2 ^ Suc 0"
      by (simp add: algebra_simps)
    have succ_step:
      "fri_layer_step_evidence (snd ((bf # bfs) ! Suc j))
        (fst ((bf # bfs) ! Suc j))
        (fri_layer_lengths (length (bf # bfs)) len ! Suc j)
        (fri_layer_indices (length (bf # bfs)) idx len ! Suc j)
        (pw * 2 ^ Suc j)
        (fri_sibling_index
          (fri_layer_lengths (length (bf # bfs)) len ! Suc j)
          (fri_layer_indices (length (bf # bfs)) idx len ! Suc j))
        v sxp_path sxn sxn_path
        (fri_layer_indices (length (bf # bfs)) idx len ! Suc j mod
          (fri_layer_lengths (length (bf # bfs)) len ! Suc j div 2))
        snext
        (layer_chunks ! Suc j)"
      using succ_step_tail 0 chunks_eq v_eq_x1 pow_eq by simp
    show ?thesis
      using succ_step by blast
  next
    case (Suc k)
    have k_bound: "Suc k < length bfs"
      using Cons.prems(6) Suc by simp
    have tail_all_layer_bounds:
      "\<And>m. m < length bfs \<Longrightarrow>
        0 < fri_layer_lengths (length bfs) (len div 2) ! m \<and>
        fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! m <
        fri_layer_lengths (length bfs) (len div 2) ! m"
      using Cons.prems(5)[of "Suc m" for m] by simp
    have tail_initial_idx_bound:
      "idx mod (len div 2) < len div 2"
      using tail_all_layer_bounds[of 0] k_bound by (cases bfs) simp_all
    have prev_tail:
      "fri_layer_step_evidence (snd (bfs ! k)) (fst (bfs ! k))
        (fri_layer_lengths (length bfs) (len div 2) ! k)
        (fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! k)
        ((pw + pw) * 2 ^ k)
        (fri_sibling_index
          (fri_layer_lengths (length bfs) (len div 2) ! k)
          (fri_layer_indices (length bfs) (idx mod (len div 2))
            (len div 2) ! k))
        xp xp_path xn xn_path
        (fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! k mod
          (fri_layer_lengths (length bfs) (len div 2) ! k div 2))
        v (rest ! k)"
    proof -
      have pow_eq: "(pw + pw) * 2 ^ k = pw * (2 * 2 ^ k)"
        by (simp add: algebra_simps)
      have raw:
        "fri_layer_step_evidence (snd (bfs ! k)) (fst (bfs ! k))
          (fri_layer_lengths (length bfs) (len div 2) ! k)
          (fri_layer_indices (length bfs) (idx mod (len div 2))
            (len div 2) ! k)
          (pw * (2 * 2 ^ k))
          (fri_sibling_index
            (fri_layer_lengths (length bfs) (len div 2) ! k)
            (fri_layer_indices (length bfs) (idx mod (len div 2))
              (len div 2) ! k))
          xp xp_path xn xn_path
          (fri_layer_indices (length bfs) (idx mod (len div 2))
            (len div 2) ! k mod
            (fri_layer_lengths (length bfs) (len div 2) ! k div 2))
          v (rest ! k)"
        using Cons.prems(7) Suc chunks_eq pow_eq by simp
      show ?thesis
        unfolding pow_eq by (rule raw)
    qed
    from Cons.IH[OF tail[unfolded out1_eq] rest_layers
        tail_transcript_rest tail_initial_idx_bound tail_all_layer_bounds
        k_bound prev_tail]
    obtain sxp_path sxn sxn_path snext where succ_tail:
      "fri_layer_step_evidence (snd (bfs ! Suc k))
        (fst (bfs ! Suc k))
        (fri_layer_lengths (length bfs) (len div 2) ! Suc k)
        (fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! Suc k)
        ((pw + pw) * 2 ^ Suc k)
        (fri_sibling_index
          (fri_layer_lengths (length bfs) (len div 2) ! Suc k)
          (fri_layer_indices (length bfs) (idx mod (len div 2))
            (len div 2) ! Suc k))
        v sxp_path sxn sxn_path
        (fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! Suc k mod
          (fri_layer_lengths (length bfs) (len div 2) ! Suc k div 2))
        snext (rest ! Suc k)"
      by blast
    have pow_eq: "(pw + pw) * (2 * 2 ^ k) = pw * (4 * 2 ^ k)"
      by (simp add: algebra_simps)
    have succ_tail_raw:
      "fri_layer_step_evidence (snd (bfs ! Suc k))
        (fst (bfs ! Suc k))
        (fri_layer_lengths (length bfs) (len div 2) ! Suc k)
        (fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! Suc k)
        ((pw + pw) * (2 * 2 ^ k))
        (fri_sibling_index
          (fri_layer_lengths (length bfs) (len div 2) ! Suc k)
          (fri_layer_indices (length bfs) (idx mod (len div 2))
            (len div 2) ! Suc k))
        v sxp_path sxn sxn_path
        (fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! Suc k mod
          (fri_layer_lengths (length bfs) (len div 2) ! Suc k div 2))
        snext (rest ! Suc k)"
      using succ_tail by simp
    have succ_step:
      "fri_layer_step_evidence (snd ((bf # bfs) ! Suc j))
        (fst ((bf # bfs) ! Suc j))
        (fri_layer_lengths (length (bf # bfs)) len ! Suc j)
        (fri_layer_indices (length (bf # bfs)) idx len ! Suc j)
        (pw * 2 ^ Suc j)
        (fri_sibling_index
          (fri_layer_lengths (length (bf # bfs)) len ! Suc j)
          (fri_layer_indices (length (bf # bfs)) idx len ! Suc j))
        v sxp_path sxn sxn_path
        (fri_layer_indices (length (bf # bfs)) idx len ! Suc j mod
          (fri_layer_lengths (length (bf # bfs)) len ! Suc j div 2))
        snext
        (layer_chunks ! Suc j)"
      using succ_tail_raw Suc chunks_eq pow_eq
      by (simp add: algebra_simps)
    show ?thesis
      using succ_step by blast
  qed
qed

lemma verifier_query_round_after_index_composition_recorded_layer_step_evidence:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
    and recorded:
      "query_round_fri_layer_transcripts (index (to_nat raw))
        (map snd f_fl) (map snd fl) round_chunk trace_layers
        composition_layers"
    and transcript: "PTranscript s = round_chunk @ PTranscript t"
    and j_bound: "j < length fl"
    and all_layer_bounds:
      "\<And>k. k < length fl \<Longrightarrow>
        0 < fri_layer_lengths (length fl) (clength * scale) ! k \<and>
        fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! k <
        fri_layer_lengths (length fl) (clength * scale) ! k"
  shows
    "\<exists>xp xp_path xn xn_path next_value.
      fri_layer_step_evidence (snd (fl ! j)) (fst (fl ! j))
        (fri_layer_lengths (length fl) (clength * scale) ! j)
        (fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! j)
        (2 ^ j)
        (fri_sibling_index
          (fri_layer_lengths (length fl) (clength * scale) ! j)
          (fri_layer_indices (length fl) (index (to_nat raw))
            (clength * scale) ! j))
        xp xp_path xn xn_path
        (fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! j mod
          (fri_layer_lengths (length fl) (clength * scale) ! j div 2))
        next_value
        (composition_layers ! j)"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold
            (?idx, cp_eval as fv (h ^ ?idx * shift), clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  from check_decommit_on_query_outcome[OF query_decommit]
  obtain query_paths query_chunk where
    query_chunk_shape:
      "query_decommitment_transcript ?idx fv query_paths query_chunk"
    and tr_s: "PTranscript s = query_chunk @ PTranscript s1"
    by blast
  from receive_query_commits_layers_outcome[OF trace_fri]
  obtain trace_layer_chunks trace_fri_chunk where
    trace_layers_actual:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layer_chunks trace_fri_chunk"
    and tr_s1: "PTranscript s1 = trace_fri_chunk @ PTranscript s2"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  from receive_query_commits_layers_outcome[OF comp_fri]
  obtain comp_layer_chunks comp_fri_chunk where
    comp_layers_actual:
      "fri_layers_transcript (length fl) (clength * scale)
        comp_layer_chunks comp_fri_chunk"
    and tr_s3: "PTranscript s3 = comp_fri_chunk @ PTranscript s4"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  let ?actual_chunk = "query_chunk @ trace_fri_chunk @ comp_fri_chunk"
  have actual_recorded:
    "query_round_fri_layer_transcripts ?idx (map snd f_fl) (map snd fl)
      ?actual_chunk trace_layer_chunks comp_layer_chunks"
    unfolding query_round_fri_layer_transcripts_def
    by (intro exI[of _ query_chunk] exI[of _ trace_fri_chunk]
        exI[of _ comp_fri_chunk] exI[of _ fv] exI[of _ query_paths] conjI)
      (use query_chunk_shape trace_layers_actual comp_layers_actual in
        \<open>simp_all add: mult.commute\<close>)
  have actual_transcript:
    "PTranscript s = ?actual_chunk @ PTranscript t"
    using tr_s tr_s1 tr_s3 s3_eq t_eq by simp
  have actual_chunk_eq: "?actual_chunk = round_chunk"
    using actual_transcript transcript by simp
  have comp_layer_chunks_eq:
    "comp_layer_chunks = composition_layers"
    by (rule query_round_fri_layer_transcripts_unique(2)
        [OF actual_recorded[unfolded actual_chunk_eq] recorded])
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  have map_eq:
    "receive_query_commits fl = map fri_layer_opening_step fl"
    unfolding receive_query_commits_def fri_layer_opening_step_def
    by (simp add: fun_eq_iff split: prod.splits)
  from mfold_fri_layer_opening_selected_recorded_step_evidence_at
      [OF comp_fri[unfolded map_eq] comp_layers_actual tr_s3 idx_bound
        all_layer_bounds j_bound]
  obtain xp xp_path xn xn_path next_value where step_actual:
    "fri_layer_step_evidence (snd (fl ! j)) (fst (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) ?idx (clength * scale) ! j)
      (1 * 2 ^ j)
      (fri_sibling_index
        (fri_layer_lengths (length fl) (clength * scale) ! j)
        (fri_layer_indices (length fl) ?idx (clength * scale) ! j))
      xp xp_path xn xn_path
      (fri_layer_indices (length fl) ?idx (clength * scale) ! j mod
        (fri_layer_lengths (length fl) (clength * scale) ! j div 2))
      next_value
      (comp_layer_chunks ! j)"
    by blast
  have step:
    "fri_layer_step_evidence (snd (fl ! j)) (fst (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) ?idx (clength * scale) ! j)
      (2 ^ j)
      (fri_sibling_index
        (fri_layer_lengths (length fl) (clength * scale) ! j)
        (fri_layer_indices (length fl) ?idx (clength * scale) ! j))
      xp xp_path xn xn_path
      (fri_layer_indices (length fl) ?idx (clength * scale) ! j mod
        (fri_layer_lengths (length fl) (clength * scale) ! j div 2))
      next_value
      (composition_layers ! j)"
    using step_actual comp_layer_chunks_eq by simp
  show ?thesis
    using step by blast
qed

lemma verifier_query_round_after_index_composition_successor_recorded_step_from_previous:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
    and recorded:
      "query_round_fri_layer_transcripts (index (to_nat raw))
        (map snd f_fl) (map snd fl) round_chunk trace_layers
        composition_layers"
    and transcript: "PTranscript s = round_chunk @ PTranscript t"
    and j_bound: "Suc j < length fl"
    and all_layer_bounds:
      "\<And>k. k < length fl \<Longrightarrow>
        0 < fri_layer_lengths (length fl) (clength * scale) ! k \<and>
        fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! k <
        fri_layer_lengths (length fl) (clength * scale) ! k"
    and previous_step:
      "fri_layer_step_evidence (snd (fl ! j)) (fst (fl ! j))
        (fri_layer_lengths (length fl) (clength * scale) ! j)
        (fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! j)
        (2 ^ j)
        (fri_sibling_index
          (fri_layer_lengths (length fl) (clength * scale) ! j)
          (fri_layer_indices (length fl) (index (to_nat raw))
            (clength * scale) ! j))
        xp xp_path xn xn_path
        (fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! j mod
          (fri_layer_lengths (length fl) (clength * scale) ! j div 2))
        v
        (composition_layers ! j)"
  shows
    "\<exists>xp_path' xn' xn_path' next_value.
      fri_layer_step_evidence (snd (fl ! Suc j)) (fst (fl ! Suc j))
        (fri_layer_lengths (length fl) (clength * scale) ! Suc j)
        (fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! Suc j)
        (2 ^ Suc j)
        (fri_sibling_index
          (fri_layer_lengths (length fl) (clength * scale) ! Suc j)
          (fri_layer_indices (length fl) (index (to_nat raw))
            (clength * scale) ! Suc j))
        v xp_path' xn' xn_path'
        (fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! Suc j mod
          (fri_layer_lengths (length fl) (clength * scale) ! Suc j div 2))
        next_value
        (composition_layers ! Suc j)"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold
            (?idx, cp_eval as fv (h ^ ?idx * shift), clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  from check_decommit_on_query_outcome[OF query_decommit]
  obtain query_paths query_chunk where
    query_chunk_shape:
      "query_decommitment_transcript ?idx fv query_paths query_chunk"
    and tr_s: "PTranscript s = query_chunk @ PTranscript s1"
    by blast
  from receive_query_commits_layers_outcome[OF trace_fri]
  obtain trace_layer_chunks trace_fri_chunk where
    trace_layers_actual:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layer_chunks trace_fri_chunk"
    and tr_s1: "PTranscript s1 = trace_fri_chunk @ PTranscript s2"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  from receive_query_commits_layers_outcome[OF comp_fri]
  obtain comp_layer_chunks comp_fri_chunk where
    comp_layers_actual:
      "fri_layers_transcript (length fl) (clength * scale)
        comp_layer_chunks comp_fri_chunk"
    and tr_s3: "PTranscript s3 = comp_fri_chunk @ PTranscript s4"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  let ?actual_chunk = "query_chunk @ trace_fri_chunk @ comp_fri_chunk"
  have actual_recorded:
    "query_round_fri_layer_transcripts ?idx (map snd f_fl) (map snd fl)
      ?actual_chunk trace_layer_chunks comp_layer_chunks"
    unfolding query_round_fri_layer_transcripts_def
    by (intro exI[of _ query_chunk] exI[of _ trace_fri_chunk]
        exI[of _ comp_fri_chunk] exI[of _ fv] exI[of _ query_paths] conjI)
      (use query_chunk_shape trace_layers_actual comp_layers_actual in
        \<open>simp_all add: mult.commute\<close>)
  have actual_transcript:
    "PTranscript s = ?actual_chunk @ PTranscript t"
    using tr_s tr_s1 tr_s3 s3_eq t_eq by simp
  have actual_chunk_eq: "?actual_chunk = round_chunk"
    using actual_transcript transcript by simp
  have comp_layer_chunks_eq:
    "comp_layer_chunks = composition_layers"
    by (rule query_round_fri_layer_transcripts_unique(2)
        [OF actual_recorded[unfolded actual_chunk_eq] recorded])
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  have map_eq:
    "receive_query_commits fl = map fri_layer_opening_step fl"
    unfolding receive_query_commits_def fri_layer_opening_step_def
    by (simp add: fun_eq_iff split: prod.splits)
  have previous_step_actual:
    "fri_layer_step_evidence (snd (fl ! j)) (fst (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) ?idx (clength * scale) ! j)
      (1 * 2 ^ j)
      (fri_sibling_index
        (fri_layer_lengths (length fl) (clength * scale) ! j)
        (fri_layer_indices (length fl) ?idx (clength * scale) ! j))
      xp xp_path xn xn_path
      (fri_layer_indices (length fl) ?idx (clength * scale) ! j mod
        (fri_layer_lengths (length fl) (clength * scale) ! j div 2))
      v
      (comp_layer_chunks ! j)"
    using previous_step comp_layer_chunks_eq by simp
  from mfold_fri_layer_opening_successor_recorded_step_from_previous
      [OF comp_fri[unfolded map_eq] comp_layers_actual tr_s3 idx_bound
        all_layer_bounds j_bound previous_step_actual]
  obtain sxp_path sxn sxn_path snext where succ_actual:
    "fri_layer_step_evidence (snd (fl ! Suc j)) (fst (fl ! Suc j))
      (fri_layer_lengths (length fl) (clength * scale) ! Suc j)
      (fri_layer_indices (length fl) ?idx (clength * scale) ! Suc j)
      (1 * 2 ^ Suc j)
      (fri_sibling_index
        (fri_layer_lengths (length fl) (clength * scale) ! Suc j)
        (fri_layer_indices (length fl) ?idx (clength * scale) ! Suc j))
      v sxp_path sxn sxn_path
      (fri_layer_indices (length fl) ?idx (clength * scale) ! Suc j mod
        (fri_layer_lengths (length fl) (clength * scale) ! Suc j div 2))
      snext
      (comp_layer_chunks ! Suc j)"
    by blast
  have succ:
    "fri_layer_step_evidence (snd (fl ! Suc j)) (fst (fl ! Suc j))
      (fri_layer_lengths (length fl) (clength * scale) ! Suc j)
      (fri_layer_indices (length fl) ?idx (clength * scale) ! Suc j)
      (2 ^ Suc j)
      (fri_sibling_index
        (fri_layer_lengths (length fl) (clength * scale) ! Suc j)
        (fri_layer_indices (length fl) ?idx (clength * scale) ! Suc j))
      v sxp_path sxn sxn_path
      (fri_layer_indices (length fl) ?idx (clength * scale) ! Suc j mod
        (fri_layer_lengths (length fl) (clength * scale) ! Suc j div 2))
      snext
      (composition_layers ! Suc j)"
    using succ_actual comp_layer_chunks_eq by simp
  show ?thesis
    using succ by blast
qed

lemma accepted_fri_opening_transcript_composition_successor_recorded_step_from_previous_at:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "i < rounds"
    and layer_bound: "Suc j < length composition_roots"
    and all_layer_bounds:
      "\<And>raw k. k < length composition_roots \<Longrightarrow>
        0 < fri_layer_lengths (length composition_roots)
          (clength * scale) ! k \<and>
        fri_layer_indices (length composition_roots) (index (to_nat raw))
          (clength * scale) ! k <
        fri_layer_lengths (length composition_roots) (clength * scale) ! k"
    and previous_step:
      "fri_layer_step_evidence (composition_roots ! j)
        (composition_bs ! j)
        (fri_evidence_layer_len composition_roots j)
        (fri_evidence_layer_idx composition_roots query_idxs i j)
        (2 ^ j)
        (fri_sibling_index (fri_evidence_layer_len composition_roots j)
          (fri_evidence_layer_idx composition_roots query_idxs i j))
        xp xp_path xn xn_path
        (fri_evidence_next_idx composition_roots query_idxs i j)
        v
        (composition_round_layers ! i ! j)"
  shows
    "\<exists>xp_path' xn' xn_path' next_value.
      fri_layer_step_evidence (composition_roots ! Suc j)
        (composition_bs ! Suc j)
        (fri_evidence_layer_len composition_roots (Suc j))
        (fri_evidence_layer_idx composition_roots query_idxs i (Suc j))
        (2 ^ Suc j)
        (fri_sibling_index
          (fri_evidence_layer_len composition_roots (Suc j))
          (fri_evidence_layer_idx composition_roots query_idxs i
            (Suc j)))
        v xp_path' xn' xn_path'
        (fri_evidence_next_idx composition_roots query_idxs i (Suc j))
        next_value
        (composition_round_layers ! i ! Suc j)"
proof -
  from fri_openings obtain result' final_state' fr f_fl as fl query_state
      raw_idxs query_chunks where
    out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and composition_bs_eq: "composition_bs = map fst fl"
    and outcome:
      "Some (result', final_state') \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr f_fl trace_final as fl
              composition_final)
            rounds)
          query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state'"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    and recorded:
      "\<And>i. i < rounds \<Longrightarrow>
        query_round_fri_layer_transcripts (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)
          (trace_round_layers ! i) (composition_round_layers ! i)"
    unfolding accepted_fri_opening_transcript_def by blast
  have result_eq: "result' = result"
    using out_def out_eq by simp
  have final_state_eq: "final_state' = final_state"
    using out_def out_eq by simp
  have outcome':
    "Some (result, final_state) \<in>
      set_dist (execute
        (ntimes
          (verifier_query_round_program fr f_fl trace_final as fl
            composition_final)
          rounds)
        query_state)"
    using outcome result_eq final_state_eq by simp
  let ?round =
    "verifier_query_round_program fr f_fl trace_final as fl composition_final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome' round_bound]
  obtain prefix x suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in>
        set_dist (execute (ntimes ?round i) query_state)"
    and round:
      "Some (x, s_suc) \<in> set_dist (execute ?round s_i)"
    and suffix:
      "Some (suffix, final_state) \<in>
        set_dist (execute (ntimes ?round (rounds - Suc i)) s_suc)"
    by blast
  have x_eq: "x = ()"
    by (cases x) simp
  show ?thesis
  proof (rule query_opening_ntimes_prefix_transcript_state_alignment
      [OF prefix])
    fix prefix_query_idxs prefix_chunks
    assume len_prefix_idxs: "length prefix_query_idxs = i"
      and len_prefix_chunks: "length prefix_chunks = i"
      and transcript_prefix:
        "PTranscript query_state =
          List.concat prefix_chunks @ PTranscript s_i"
      and state_i:
        "PState s_i =
          state_after_query_chunks (PState query_state) prefix_chunks i"
      and counter_i: "PQueryCounter s_i = PQueryCounter query_state + i"
      and prefix_ext: "query_state \<le> s_i"
      and prefix_rounds:
        "\<And>k. k < i \<Longrightarrow>
          verifier_query_round_chunk (prefix_query_idxs ! k)
            (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    from round[unfolded x_eq verifier_query_round_program_alt_def]
    obtain raw s0 where
      raw_out:
        "Some (raw, s0) \<in>
          set_dist (execute receive_query_index_challenge s_i)"
      and after:
        "Some ((), s_suc) \<in>
          set_dist (execute
            (verifier_query_round_after_index_program fr f_fl trace_final as
              fl composition_final raw) s0)"
      by (auto elim!: set_dist_bindE)
    have tr_s0: "PTranscript s0 = PTranscript s_i"
      using receive_query_index_challenge_outcome[OF raw_out] by simp
    show ?thesis
    proof (rule verifier_query_round_program_outcome[OF round[unfolded x_eq]])
      fix raw' idx chunk
      assume idx_eq: "idx = index (to_nat raw')"
        and chunk_shape:
          "verifier_query_round_chunk idx (map snd f_fl) (map snd fl)
            chunk"
        and transcript_round:
          "PTranscript s_i = chunk @ PTranscript s_suc"
        and state_suc:
          "PState s_suc = foldl concat (PState s_i) chunk"
        and round_ext: "s_i \<le> s_suc"
        and counter_suc:
          "PQueryCounter s_suc = Suc (PQueryCounter s_i)"
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw'"
      have raw_eq': "raw = raw'"
      proof -
        have lookup_s0:
          "fmlookup (HashMap s0)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw"
          using receive_query_index_challenge_outcome[OF raw_out] by simp
        have s0_suc: "s0 \<le> s_suc"
          using verifier_query_round_after_index_program_outcome[OF after]
          by simp
        have lookup_suc_raw:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw"
          using hash_extension_lookup[OF lookup_s0 s0_suc] .
        show ?thesis
          using lookup_suc lookup_suc_raw by simp
      qed
      show ?thesis
      proof (rule query_opening_ntimes_suffix_transcript_state_alignment
          [OF suffix])
        fix suffix_query_idxs suffix_chunks
        assume len_suffix_idxs:
            "length suffix_query_idxs = rounds - Suc i"
          and len_suffix_chunks:
            "length suffix_chunks = rounds - Suc i"
          and transcript_suffix:
            "PTranscript s_suc =
              List.concat suffix_chunks @ PTranscript final_state"
          and suffix_state:
            "PState final_state =
              state_after_query_chunks (PState s_suc) suffix_chunks
                (rounds - Suc i)"
          and suffix_counter:
            "PQueryCounter final_state =
              PQueryCounter s_suc + (rounds - Suc i)"
          and suffix_ext: "s_suc \<le> final_state"
          and suffix_rounds:
            "\<And>k. k < rounds - Suc i \<Longrightarrow>
              verifier_query_round_chunk (suffix_query_idxs ! k)
                (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
        let ?selected_chunks = "prefix_chunks @ chunk # suffix_chunks"
        have len_selected_chunks: "length ?selected_chunks = rounds"
          using len_prefix_chunks len_suffix_chunks round_bound by simp
        have selected_chunk_lens:
          "\<And>k. k < rounds \<Longrightarrow>
            length (?selected_chunks ! k) =
              verifier_query_round_transcript_length (query_idxs ! k)
                (map snd f_fl) (map snd fl)"
        proof -
          fix k
          assume k_bound: "k < rounds"
          show
            "length (?selected_chunks ! k) =
              verifier_query_round_transcript_length (query_idxs ! k)
                (map snd f_fl) (map snd fl)"
          proof (cases "k < i")
            case True
            have nth_eq: "?selected_chunks ! k = prefix_chunks ! k"
              using True len_prefix_chunks by (simp add: nth_append)
            have
              "length (prefix_chunks ! k) =
                verifier_query_round_transcript_length
                  (prefix_query_idxs ! k) (map snd f_fl) (map snd fl)"
              by (rule verifier_query_round_chunk_length
                  [OF prefix_rounds[OF True]])
            then show ?thesis
              using nth_eq
              by (simp add:
                  verifier_query_round_transcript_length_index_irrelevant)
          next
            case False
            show ?thesis
            proof (cases "k = i")
              case True
              have nth_eq: "?selected_chunks ! k = chunk"
                using True len_prefix_chunks by (simp add: nth_append)
              have
                "length chunk =
                  verifier_query_round_transcript_length idx
                    (map snd f_fl) (map snd fl)"
                by (rule verifier_query_round_chunk_length[OF chunk_shape])
              then show ?thesis
                using nth_eq
                by (simp add:
                    verifier_query_round_transcript_length_index_irrelevant)
            next
              case False
              let ?k = "k - Suc i"
              have ge: "Suc i \<le> k"
                using \<open>\<not> k < i\<close> False by linarith
              have k_bound': "?k < rounds - Suc i"
                using ge k_bound by linarith
              have nth_eq: "?selected_chunks ! k = suffix_chunks ! ?k"
                using ge len_prefix_chunks by (simp add: nth_append)
              have
                "length (suffix_chunks ! ?k) =
                  verifier_query_round_transcript_length
                    (suffix_query_idxs ! ?k) (map snd f_fl) (map snd fl)"
                by (rule verifier_query_round_chunk_length
                    [OF suffix_rounds[OF k_bound']])
              then show ?thesis
                using nth_eq
                by (simp add:
                    verifier_query_round_transcript_length_index_irrelevant)
            qed
          qed
        qed
        have query_chunk_f:
          "\<And>k. k < rounds \<Longrightarrow>
            verifier_query_round_chunk (query_idxs ! k)
              (map snd f_fl) (map snd fl) (query_chunks ! k)"
          using query_chunk trace_roots_eq composition_roots_eq by simp
        have query_chunk_lens:
          "\<And>k. k < rounds \<Longrightarrow>
            length (query_chunks ! k) =
              verifier_query_round_transcript_length (query_idxs ! k)
                (map snd f_fl) (map snd fl)"
          using query_chunk_f verifier_query_round_chunk_length by blast
        have selected_transcript:
          "PTranscript query_state =
            List.concat ?selected_chunks @ PTranscript final_state"
          using transcript_prefix transcript_round transcript_suffix by simp
        have concat_eq: "List.concat ?selected_chunks = List.concat query_chunks"
          using selected_transcript transcript_query final_state_eq by simp
        have chunks_eq: "?selected_chunks = query_chunks"
        proof -
          have same_lens:
            "\<And>k. k < length ?selected_chunks \<Longrightarrow>
              length (?selected_chunks ! k) = length (query_chunks ! k)"
            using selected_chunk_lens query_chunk_lens len_selected_chunks
            by simp
          have concat_eq_empty:
            "List.concat ?selected_chunks @ [] = List.concat query_chunks"
            using concat_eq by simp
          have len_eq: "length ?selected_chunks = length query_chunks"
            using len_selected_chunks len_query_chunks by simp
          have "?selected_chunks = query_chunks \<and> ([] :: 'f list) = []"
            by (rule concat_append_eq_concat_same_chunk_lengths
                [OF len_eq same_lens concat_eq_empty])
          then show ?thesis
            by simp
        qed
        have prefix_state_eq:
          "state_after_query_chunks (PState query_state) prefix_chunks i =
            state_after_query_chunks (PState query_state) query_chunks i"
        proof -
          have
            "state_after_query_chunks (PState query_state) ?selected_chunks i =
              state_after_query_chunks (PState query_state) prefix_chunks i"
            by (rule state_after_query_chunks_append_prefix
                [OF len_prefix_chunks])
          then show ?thesis
            using chunks_eq by simp
        qed
        have lookup_final:
          "fmlookup (HashMap final_state)
            (QueryIndexChallenge (PQueryCounter query_state + i)
              (state_after_query_chunks (PState query_state) query_chunks i)) =
          Some raw'"
        proof -
          have lookup_suc':
            "fmlookup (HashMap s_suc)
              (QueryIndexChallenge (PQueryCounter query_state + i)
                (state_after_query_chunks (PState query_state)
                  prefix_chunks i)) =
            Some raw'"
            using lookup_suc state_i counter_i by simp
          have lookup_final_prefix:
            "fmlookup (HashMap final_state)
              (QueryIndexChallenge (PQueryCounter query_state + i)
                (state_after_query_chunks (PState query_state)
                  prefix_chunks i)) =
            Some raw'"
            using hash_extension_lookup[OF lookup_suc' suffix_ext] .
          show ?thesis
            using lookup_final_prefix prefix_state_eq by simp
        qed
        have raw_idx_eq: "raw' = raw_idxs ! i"
          using lookup_final replay_lookup[OF round_bound] final_state_eq
          by simp
        have idx_eq_query: "idx = query_idxs ! i"
          using idx_eq raw_idx_eq query_idxs_eq len_raw round_bound by simp
        have selected_i: "?selected_chunks ! i = chunk"
          using len_prefix_chunks by (simp add: nth_append)
        have chunk_i_eq: "chunk = query_chunks ! i"
          using chunks_eq selected_i by simp
        have recorded_i:
          "query_round_fri_layer_transcripts (index (to_nat raw))
            (map snd f_fl) (map snd fl) chunk (trace_round_layers ! i)
            (composition_round_layers ! i)"
          using recorded[OF round_bound] idx_eq idx_eq_query raw_eq'
            chunk_i_eq trace_roots_eq composition_roots_eq
          by simp
        have tr_s0_suc:
          "PTranscript s0 = chunk @ PTranscript s_suc"
          using tr_s0 transcript_round by simp
        have suc_j_bound_fl: "Suc j < length fl"
          using layer_bound composition_roots_eq by simp
        have all_layer_bounds_fl:
          "\<And>k. k < length fl \<Longrightarrow>
            0 < fri_layer_lengths (length fl) (clength * scale) ! k \<and>
            fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! k <
            fri_layer_lengths (length fl) (clength * scale) ! k"
          using all_layer_bounds composition_roots_eq by simp
        have raw_idx_query: "index (to_nat raw) = query_idxs ! i"
          using idx_eq idx_eq_query raw_eq' by simp
        have previous_step_fl:
          "fri_layer_step_evidence (snd (fl ! j)) (fst (fl ! j))
            (fri_layer_lengths (length fl) (clength * scale) ! j)
            (fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! j)
            (2 ^ j)
            (fri_sibling_index
              (fri_layer_lengths (length fl) (clength * scale) ! j)
              (fri_layer_indices (length fl) (index (to_nat raw))
                (clength * scale) ! j))
            xp xp_path xn xn_path
            (fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! j mod
              (fri_layer_lengths (length fl) (clength * scale) ! j div 2))
            v
            (composition_round_layers ! i ! j)"
          using previous_step composition_roots_eq composition_bs_eq
            raw_idx_query layer_bound
          unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
            fri_evidence_next_idx_def
          by simp
        from verifier_query_round_after_index_composition_successor_recorded_step_from_previous
            [OF after recorded_i tr_s0_suc suc_j_bound_fl
              all_layer_bounds_fl previous_step_fl]
        obtain sxp_path sxn sxn_path snext where succ_fl:
          "fri_layer_step_evidence (snd (fl ! Suc j))
            (fst (fl ! Suc j))
            (fri_layer_lengths (length fl) (clength * scale) ! Suc j)
            (fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! Suc j)
            (2 ^ Suc j)
            (fri_sibling_index
              (fri_layer_lengths (length fl) (clength * scale) ! Suc j)
              (fri_layer_indices (length fl) (index (to_nat raw))
                (clength * scale) ! Suc j))
            v sxp_path sxn sxn_path
            (fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! Suc j mod
              (fri_layer_lengths (length fl) (clength * scale) ! Suc j
                div 2))
            snext
            (composition_round_layers ! i ! Suc j)"
          by blast
        have succ:
          "fri_layer_step_evidence (composition_roots ! Suc j)
            (composition_bs ! Suc j)
            (fri_evidence_layer_len composition_roots (Suc j))
            (fri_evidence_layer_idx composition_roots query_idxs i
              (Suc j))
            (2 ^ Suc j)
            (fri_sibling_index
              (fri_evidence_layer_len composition_roots (Suc j))
              (fri_evidence_layer_idx composition_roots query_idxs i
                (Suc j)))
            v sxp_path sxn sxn_path
            (fri_evidence_next_idx composition_roots query_idxs i (Suc j))
            snext
            (composition_round_layers ! i ! Suc j)"
          using succ_fl composition_roots_eq composition_bs_eq
            raw_idx_query layer_bound
          unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
            fri_evidence_next_idx_def
          by simp
        show ?thesis
          using succ by blast
      qed
    qed
  qed
qed

lemma generic_fri_sampled_successor_conflict_imp_same_layer_with_source_steps:
  assumes successor:
    "generic_fri_sampled_successor_opening_conflict roots challenges
      query_idxs round_layers"
    and len_challenges: "length challenges = length roots"
    and source_step:
      "\<And>source_round layer_idx v.
        source_round < length query_idxs \<Longrightarrow>
        Suc layer_idx < length challenges \<Longrightarrow>
        generic_fri_round_forced_next_value roots challenges query_idxs
          round_layers source_round layer_idx v \<Longrightarrow>
        \<exists>xp_path xn xn_path.
          fri_layer_step_evidence
            (roots ! Suc layer_idx)
            (challenges ! Suc layer_idx)
            (fri_evidence_layer_len roots (Suc layer_idx))
            (fri_evidence_layer_idx roots query_idxs source_round
              (Suc layer_idx))
            (2 ^ Suc layer_idx)
            (fri_sibling_index
              (fri_evidence_layer_len roots (Suc layer_idx))
              (fri_evidence_layer_idx roots query_idxs source_round
                (Suc layer_idx)))
            v xp_path xn xn_path
            (fri_evidence_next_idx roots query_idxs source_round
              (Suc layer_idx))
            (fri_evidence_next_value roots challenges query_idxs
              source_round (Suc layer_idx) v xn)
            (round_layers ! source_round ! Suc layer_idx)"
  shows
    "generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
proof -
  from generic_fri_sampled_successor_opening_conflictE[OF successor]
  obtain source_round target_round layer_idx v xp xp_path xn xn_path
    where source_bound: "source_round < length query_idxs"
      and target_bound: "target_round < length query_idxs"
      and layer_bound: "Suc layer_idx < length challenges"
      and forced:
        "generic_fri_round_forced_next_value roots challenges query_idxs
          round_layers source_round layer_idx v"
      and target_step:
        "fri_layer_step_evidence
          (roots ! Suc layer_idx)
          (challenges ! Suc layer_idx)
          (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs target_round
            (Suc layer_idx))
          (2 ^ Suc layer_idx)
          (fri_sibling_index
            (fri_evidence_layer_len roots (Suc layer_idx))
            (fri_evidence_layer_idx roots query_idxs target_round
              (Suc layer_idx)))
          xp xp_path xn xn_path
          (fri_evidence_next_idx roots query_idxs target_round
            (Suc layer_idx))
          (fri_evidence_next_value roots challenges query_idxs target_round
            (Suc layer_idx) xp xn)
          (round_layers ! target_round ! Suc layer_idx)"
      and conflict:
        "(fri_evidence_next_idx roots query_idxs source_round layer_idx =
          fri_evidence_layer_idx roots query_idxs target_round
            (Suc layer_idx) \<and>
          v \<noteq> xp) \<or>
         (fri_evidence_next_idx roots query_idxs source_round layer_idx =
          fri_sibling_index
            (fri_evidence_layer_len roots (Suc layer_idx))
            (fri_evidence_layer_idx roots query_idxs target_round
              (Suc layer_idx)) \<and>
          v \<noteq> xn)"
    by blast
  from source_step[OF source_bound layer_bound forced]
  obtain vp_path vn vn_path where source_suc_step:
    "fri_layer_step_evidence
      (roots ! Suc layer_idx)
      (challenges ! Suc layer_idx)
      (fri_evidence_layer_len roots (Suc layer_idx))
      (fri_evidence_layer_idx roots query_idxs source_round
        (Suc layer_idx))
      (2 ^ Suc layer_idx)
      (fri_sibling_index
        (fri_evidence_layer_len roots (Suc layer_idx))
        (fri_evidence_layer_idx roots query_idxs source_round
          (Suc layer_idx)))
      v vp_path vn vn_path
      (fri_evidence_next_idx roots query_idxs source_round
        (Suc layer_idx))
      (fri_evidence_next_value roots challenges query_idxs source_round
        (Suc layer_idx) v vn)
      (round_layers ! source_round ! Suc layer_idx)"
    by blast
  have source_idx_suc:
    "fri_evidence_layer_idx roots query_idxs source_round (Suc layer_idx) =
      fri_evidence_next_idx roots query_idxs source_round layer_idx"
    by (rule fri_evidence_layer_idx_Suc)
      (use layer_bound len_challenges in simp)
  have layer_suc_bound: "Suc layer_idx < length challenges"
    using layer_bound .
  have same_conflict:
    "(fri_evidence_layer_idx roots query_idxs source_round (Suc layer_idx) =
        fri_evidence_layer_idx roots query_idxs target_round
          (Suc layer_idx) \<and>
      v \<noteq> xp) \<or>
     (fri_evidence_layer_idx roots query_idxs source_round (Suc layer_idx) =
        fri_sibling_index
          (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs target_round
            (Suc layer_idx)) \<and>
      v \<noteq> xn)"
  proof -
    from conflict show ?thesis
    proof
      assume c:
        "fri_evidence_next_idx roots query_idxs source_round layer_idx =
          fri_evidence_layer_idx roots query_idxs target_round
            (Suc layer_idx) \<and>
          v \<noteq> xp"
      then show ?thesis
        using source_idx_suc by simp
    next
      assume c:
        "fri_evidence_next_idx roots query_idxs source_round layer_idx =
          fri_sibling_index
            (fri_evidence_layer_len roots (Suc layer_idx))
            (fri_evidence_layer_idx roots query_idxs target_round
              (Suc layer_idx)) \<and>
          v \<noteq> xn"
      then show ?thesis
        using source_idx_suc by simp
    qed
  qed
  show ?thesis
    unfolding generic_fri_sampled_same_layer_opening_conflict_def
    apply (rule exI[where x=source_round])
    apply (rule exI[where x=target_round])
    apply (rule exI[where x="Suc layer_idx"])
    apply (rule exI[where x=v])
    apply (rule exI[where x=vp_path])
    apply (rule exI[where x=vn])
    apply (rule exI[where x=vn_path])
    apply (rule exI[where x=xp])
    apply (rule exI[where x=xp_path])
    apply (rule exI[where x=xn])
    apply (rule exI[where x=xn_path])
    apply (intro conjI)
    using source_bound target_bound layer_suc_bound source_suc_step
      target_step same_conflict
    by blast+
qed

lemma generic_fri_sampled_same_layer_conflict_imp_merkle_or_slot_gap:
  assumes conflict:
    "generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
    and len_challenges: "length challenges = length roots"
    and auth_step:
      "\<And>round_idx layer_idx.
        round_idx < length query_idxs \<Longrightarrow>
        layer_idx < length challenges \<Longrightarrow>
        generic_fri_transcript_step_with_authenticated_chunk roots
          challenges query_idxs round_layers final_state round_idx layer_idx"
  shows
    "partial_merkle_inconsistency_bad s (Some (result, final_state)) \<or>
     generic_fri_authenticated_slot_recorded_chunk_gap roots query_idxs
      round_layers final_state"
proof -
  from generic_fri_sampled_same_layer_imp_authenticated_or_recorded_auth_gap
    [OF conflict, of final_state]
  consider
    "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state"
  | "generic_fri_sampled_same_layer_recorded_auth_gap roots challenges
      query_idxs round_layers final_state"
    by blast
  then show ?thesis
  proof cases
    case 1
    then have "partial_merkle_inconsistency_bad s (Some (result, final_state))"
      by (rule
          generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_imp_partial_merkle)
        (rule len_challenges)
    then show ?thesis by simp
  next
    case 2
    then have auth_gap:
      "generic_fri_sampled_same_layer_authenticated_recorded_auth_gap roots
        challenges query_idxs round_layers final_state"
      by (rule generic_fri_recorded_auth_gap_imp_authenticated_recorded_auth_gap)
        (rule auth_step)
    have "generic_fri_authenticated_slot_recorded_chunk_gap roots query_idxs
      round_layers final_state"
      by (rule generic_fri_authenticated_recorded_auth_gap_imp_slot_recorded_chunk_gap
          [OF auth_gap])
    then show ?thesis by simp
  qed
qed

lemma composition_fri_verifier_tied_next_value_replay_gap_imp_merkle_or_slot_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and gap:
      "composition_fri_verifier_tied_next_value_replay_gap s out"
  shows
    "partial_merkle_inconsistency_bad s out \<or>
     composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
      s out"
proof -
  from gap have sampled:
    "composition_fri_verifier_tied_sampled_next_value_conflict s out"
    unfolding composition_fri_verifier_tied_next_value_replay_gap_def
    by simp
  from composition_fri_verifier_tied_sampled_next_value_conflictE[OF sampled]
  obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table round_idx round_idx' layer_idx v v'
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_cand: "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and round_bound: "round_idx < length fri_query_idxs"
    and round_bound': "round_idx' < length fri_query_idxs"
    and layer_bound: "layer_idx < length composition_bs"
    and same_idx:
      "fri_evidence_next_idx composition_roots fri_query_idxs round_idx
        layer_idx =
       fri_evidence_next_idx composition_roots fri_query_idxs round_idx'
        layer_idx"
    and forced:
      "generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx layer_idx v"
    and forced':
      "generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx' layer_idx v'"
    and neq: "v \<noteq> v'"
    using sampled
    by (elim composition_fri_verifier_tied_sampled_next_value_conflictE)
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  have support_some:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using support out_eq by simp
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs fri_dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF fri_openings]
      out_eq by simp
  have degree_bound: "to_nat fri_dg \<le> maxDegree"
    by (rule verify_monad_accepted_fri_challenges_degree_bound
        [OF support_some challenges])
  have len_bs_roots: "length composition_bs = length composition_roots"
    using accepted_fri_opening_transcript_shapes(4)[OF fri_openings] .
  have layer_bound_roots: "layer_idx < length composition_roots"
    using layer_bound len_bs_roots by simp
  have len_query: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes(7)[OF fri_openings] .
  have round_bound_rounds: "round_idx < rounds"
    using round_bound len_query by simp
  have round_bound_rounds': "round_idx' < rounds"
    using round_bound' len_query by simp
  have raw_bound:
    "fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
      layer_idx <
     fri_evidence_layer_len composition_roots layer_idx"
    by (rule
        accepted_fri_opening_transcript_composition_evidence_layer_idx_bound
        [OF fri_openings degree_bound round_bound layer_bound_roots])
  have raw_bound':
    "fri_evidence_layer_idx composition_roots fri_query_idxs round_idx'
      layer_idx <
     fri_evidence_layer_len composition_roots layer_idx"
    by (rule
        accepted_fri_opening_transcript_composition_evidence_layer_idx_bound
        [OF fri_openings degree_bound round_bound' layer_bound_roots])
  have even_len:
    "2 dvd fri_evidence_layer_len composition_roots layer_idx"
    by (rule accepted_fri_opening_transcript_composition_layer_arithmetic(1)
        [OF fri_openings degree_bound layer_bound])
  have round_product:
    "fri_evidence_layer_len composition_roots layer_idx * 2 ^ layer_idx =
      clength * scale"
    by (rule accepted_fri_opening_transcript_composition_layer_arithmetic(2)
        [OF fri_openings degree_bound layer_bound])
  have auth_step:
    "\<And>i j.
      i < length fri_query_idxs \<Longrightarrow>
      j < length composition_bs \<Longrightarrow>
      generic_fri_transcript_step_with_authenticated_chunk composition_roots
        composition_bs fri_query_idxs composition_round_layers final_state i j"
  proof -
    fix i j
    assume i_bound: "i < length fri_query_idxs"
      and j_bound: "j < length composition_bs"
    have i_rounds: "i < rounds"
      using i_bound len_query by simp
    have j_roots: "j < length composition_roots"
      using j_bound len_bs_roots by simp
    show
      "generic_fri_transcript_step_with_authenticated_chunk
        composition_roots composition_bs fri_query_idxs
        composition_round_layers final_state i j"
      by (rule
          accepted_fri_opening_transcript_composition_step_with_authenticated_chunk_at_raw
          [OF fri_openings out_eq degree_bound i_rounds j_roots])
  qed
  show ?thesis
  proof (cases
      "generic_fri_sampled_same_layer_opening_conflict composition_roots
        composition_bs fri_query_idxs composition_round_layers")
    case True
    have conflict_route:
      "partial_merkle_inconsistency_bad s (Some (result, final_state)) \<or>
       generic_fri_authenticated_slot_recorded_chunk_gap composition_roots
        fri_query_idxs composition_round_layers final_state"
      by (rule generic_fri_sampled_same_layer_conflict_imp_merkle_or_slot_gap
          [OF True len_bs_roots auth_step])
    then show ?thesis
    proof
      assume "partial_merkle_inconsistency_bad s (Some (result, final_state))"
      then show ?thesis
        using out_eq by simp
    next
      assume slot_gap:
        "generic_fri_authenticated_slot_recorded_chunk_gap composition_roots
          fri_query_idxs composition_round_layers final_state"
      have route_slot_gap:
        "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          s out"
        unfolding
          composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_def
        by (intro exI conjI)
          (rule out_eq, rule fri_openings, rule aligned, rule trace_cand,
            rule comp_cand, rule trace_low, rule comp_not_low, rule slot_gap)
      then show ?thesis by simp
    qed
  next
    case False
    then have no_same:
      "\<not> generic_fri_sampled_same_layer_opening_conflict
        composition_roots composition_bs fri_query_idxs
        composition_round_layers"
      by simp
    have "v = v'"
      by (rule generic_fri_forced_next_value_eq_if_no_same_layer_conflict
          [OF no_same round_bound round_bound' layer_bound even_len
            raw_bound raw_bound' round_product same_idx forced forced'])
    then show ?thesis
      using neq by simp
  qed
qed

lemma composition_fri_verifier_tied_successor_replay_gap_imp_merkle_or_slot_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and gap:
      "composition_fri_verifier_tied_successor_replay_gap s out"
  shows
    "partial_merkle_inconsistency_bad s out \<or>
     composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
      s out"
proof -
  from gap have sampled:
    "composition_fri_verifier_tied_sampled_successor_opening_conflict s out"
    unfolding composition_fri_verifier_tied_successor_replay_gap_def
    by simp
  obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table source_round target_round layer_idx v
      xp xp_path xn xn_path
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_cand: "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and source_bound: "source_round < length fri_query_idxs"
    and target_bound: "target_round < length fri_query_idxs"
    and layer_bound: "Suc layer_idx < length composition_bs"
    and forced:
      "generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers source_round layer_idx v"
    and target_step:
      "fri_layer_step_evidence
        (composition_roots ! Suc layer_idx)
        (composition_bs ! Suc layer_idx)
        (fri_evidence_layer_len composition_roots (Suc layer_idx))
        (fri_evidence_layer_idx composition_roots fri_query_idxs
          target_round (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len composition_roots (Suc layer_idx))
          (fri_evidence_layer_idx composition_roots fri_query_idxs
            target_round (Suc layer_idx)))
        xp xp_path xn xn_path
        (fri_evidence_next_idx composition_roots fri_query_idxs
          target_round (Suc layer_idx))
        (fri_evidence_next_value composition_roots composition_bs
          fri_query_idxs target_round (Suc layer_idx) xp xn)
        (composition_round_layers ! target_round ! Suc layer_idx)"
    and conflict:
      "(fri_evidence_next_idx composition_roots fri_query_idxs source_round
          layer_idx =
        fri_evidence_layer_idx composition_roots fri_query_idxs target_round
          (Suc layer_idx) \<and>
        v \<noteq> xp) \<or>
       (fri_evidence_next_idx composition_roots fri_query_idxs source_round
          layer_idx =
        fri_sibling_index
          (fri_evidence_layer_len composition_roots (Suc layer_idx))
          (fri_evidence_layer_idx composition_roots fri_query_idxs
            target_round (Suc layer_idx)) \<and>
        v \<noteq> xn)"
    using sampled
    by (elim composition_fri_verifier_tied_sampled_successor_opening_conflictE)
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  have support_some:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using support out_eq by simp
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs fri_dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF fri_openings]
      out_eq by simp
  have degree_bound: "to_nat fri_dg \<le> maxDegree"
    by (rule verify_monad_accepted_fri_challenges_degree_bound
        [OF support_some challenges])
  have len_bs_roots: "length composition_bs = length composition_roots"
    using accepted_fri_opening_transcript_shapes(4)[OF fri_openings] .
  have len_query: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes(7)[OF fri_openings] .
  have sampled_generic:
    "generic_fri_sampled_successor_opening_conflict composition_roots
      composition_bs fri_query_idxs composition_round_layers"
    unfolding generic_fri_sampled_successor_opening_conflict_def
    by (intro exI conjI)
      (rule source_bound, rule target_bound, rule layer_bound,
       rule forced, rule target_step, rule conflict)
  have all_layer_bounds:
    "\<And>raw k. k < length composition_roots \<Longrightarrow>
      0 < fri_layer_lengths (length composition_roots)
        (clength * scale) ! k \<and>
      fri_layer_indices (length composition_roots) (index (to_nat raw))
        (clength * scale) ! k <
      fri_layer_lengths (length composition_roots) (clength * scale) ! k"
    by (rule accepted_fri_opening_transcript_composition_raw_layer_bound
        [OF fri_openings degree_bound])
  have source_step:
    "\<And>source_round layer_idx v.
      source_round < length fri_query_idxs \<Longrightarrow>
      Suc layer_idx < length composition_bs \<Longrightarrow>
      generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers source_round layer_idx v \<Longrightarrow>
      \<exists>xp_path xn xn_path.
        fri_layer_step_evidence
          (composition_roots ! Suc layer_idx)
          (composition_bs ! Suc layer_idx)
          (fri_evidence_layer_len composition_roots (Suc layer_idx))
          (fri_evidence_layer_idx composition_roots fri_query_idxs
            source_round (Suc layer_idx))
          (2 ^ Suc layer_idx)
          (fri_sibling_index
            (fri_evidence_layer_len composition_roots (Suc layer_idx))
            (fri_evidence_layer_idx composition_roots fri_query_idxs
              source_round (Suc layer_idx)))
          v xp_path xn xn_path
          (fri_evidence_next_idx composition_roots fri_query_idxs
            source_round (Suc layer_idx))
          (fri_evidence_next_value composition_roots composition_bs
            fri_query_idxs source_round (Suc layer_idx) v xn)
          (composition_round_layers ! source_round ! Suc layer_idx)"
  proof -
    fix source_round layer_idx v
    assume source_round_bound: "source_round < length fri_query_idxs"
      and layer_bound': "Suc layer_idx < length composition_bs"
      and forced':
        "generic_fri_round_forced_next_value composition_roots composition_bs
          fri_query_idxs composition_round_layers source_round layer_idx v"
    have source_round_rounds: "source_round < rounds"
      using source_round_bound len_query by simp
    have layer_bound_roots: "Suc layer_idx < length composition_roots"
      using layer_bound' len_bs_roots by simp
    from forced' obtain fxp fxp_path fxn fxn_path where previous_step:
      "fri_layer_step_evidence (composition_roots ! layer_idx)
        (composition_bs ! layer_idx)
        (fri_evidence_layer_len composition_roots layer_idx)
        (fri_evidence_layer_idx composition_roots fri_query_idxs
          source_round layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len composition_roots layer_idx)
          (fri_evidence_layer_idx composition_roots fri_query_idxs
            source_round layer_idx))
        fxp fxp_path fxn fxn_path
        (fri_evidence_next_idx composition_roots fri_query_idxs
          source_round layer_idx)
        v
        (composition_round_layers ! source_round ! layer_idx)"
      unfolding generic_fri_round_forced_next_value_def by blast
    from accepted_fri_opening_transcript_composition_successor_recorded_step_from_previous_at
        [OF fri_openings out_eq source_round_rounds layer_bound_roots
          all_layer_bounds previous_step]
    obtain sxp_path sxn sxn_path snext where succ:
      "fri_layer_step_evidence (composition_roots ! Suc layer_idx)
        (composition_bs ! Suc layer_idx)
        (fri_evidence_layer_len composition_roots (Suc layer_idx))
        (fri_evidence_layer_idx composition_roots fri_query_idxs
          source_round (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len composition_roots (Suc layer_idx))
          (fri_evidence_layer_idx composition_roots fri_query_idxs
            source_round (Suc layer_idx)))
        v sxp_path sxn sxn_path
        (fri_evidence_next_idx composition_roots fri_query_idxs
          source_round (Suc layer_idx))
        snext
        (composition_round_layers ! source_round ! Suc layer_idx)"
      by blast
    have snext_eq:
      "snext =
        fri_evidence_next_value composition_roots composition_bs
          fri_query_idxs source_round (Suc layer_idx) v sxn"
      using fri_layer_step_evidenceD(3)[OF succ]
      unfolding fri_evidence_next_value_def by simp
    show
      "\<exists>xp_path xn xn_path.
        fri_layer_step_evidence
          (composition_roots ! Suc layer_idx)
          (composition_bs ! Suc layer_idx)
          (fri_evidence_layer_len composition_roots (Suc layer_idx))
          (fri_evidence_layer_idx composition_roots fri_query_idxs
            source_round (Suc layer_idx))
          (2 ^ Suc layer_idx)
          (fri_sibling_index
            (fri_evidence_layer_len composition_roots (Suc layer_idx))
            (fri_evidence_layer_idx composition_roots fri_query_idxs
              source_round (Suc layer_idx)))
          v xp_path xn xn_path
          (fri_evidence_next_idx composition_roots fri_query_idxs
            source_round (Suc layer_idx))
          (fri_evidence_next_value composition_roots composition_bs
            fri_query_idxs source_round (Suc layer_idx) v xn)
          (composition_round_layers ! source_round ! Suc layer_idx)"
      using succ snext_eq by blast
  qed
  have same_layer:
    "generic_fri_sampled_same_layer_opening_conflict composition_roots
      composition_bs fri_query_idxs composition_round_layers"
    by (rule generic_fri_sampled_successor_conflict_imp_same_layer_with_source_steps
        [OF sampled_generic len_bs_roots source_step])
  have auth_step:
    "\<And>i j.
      i < length fri_query_idxs \<Longrightarrow>
      j < length composition_bs \<Longrightarrow>
      generic_fri_transcript_step_with_authenticated_chunk composition_roots
        composition_bs fri_query_idxs composition_round_layers final_state i j"
  proof -
    fix i j
    assume i_bound: "i < length fri_query_idxs"
      and j_bound: "j < length composition_bs"
    have i_rounds: "i < rounds"
      using i_bound len_query by simp
    have j_roots: "j < length composition_roots"
      using j_bound len_bs_roots by simp
    show
      "generic_fri_transcript_step_with_authenticated_chunk
        composition_roots composition_bs fri_query_idxs
        composition_round_layers final_state i j"
      by (rule
          accepted_fri_opening_transcript_composition_step_with_authenticated_chunk_at_raw
          [OF fri_openings out_eq degree_bound i_rounds j_roots])
  qed
  have route:
    "partial_merkle_inconsistency_bad s (Some (result, final_state)) \<or>
     generic_fri_authenticated_slot_recorded_chunk_gap composition_roots
      fri_query_idxs composition_round_layers final_state"
    by (rule generic_fri_sampled_same_layer_conflict_imp_merkle_or_slot_gap
        [OF same_layer len_bs_roots auth_step])
  then show ?thesis
  proof
    assume "partial_merkle_inconsistency_bad s (Some (result, final_state))"
    then show ?thesis
      using out_eq by simp
  next
    assume slot_gap:
      "generic_fri_authenticated_slot_recorded_chunk_gap composition_roots
        fri_query_idxs composition_round_layers final_state"
    have route_slot_gap:
      "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
        s out"
      unfolding
        composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_def
      by (intro exI conjI)
        (rule out_eq, rule fri_openings, rule aligned, rule trace_cand,
          rule comp_cand, rule trace_low, rule comp_not_low, rule slot_gap)
    then show ?thesis by simp
  qed
qed

lemma wp_composition_fri_verifier_tied_successor_replay_gap_bound_from_merkle_and_slot:
  fixes M A :: prob
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and slot_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> A"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap s) s
      \<le> M + A"
proof -
  let ?P = "partial_merkle_inconsistency_bad s"
  let ?Q = "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s"
  have event_le:
    "wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap s) s \<le>
     wp_event verify_monad (\<lambda>out. ?P out \<or> ?Q out) s"
    by (rule wp_event_mono_on_support)
      (rule
        composition_fri_verifier_tied_successor_replay_gap_imp_merkle_or_slot_on_support)
  also have "... \<le> wp_event verify_monad ?P s +
      wp_event verify_monad ?Q s"
    by (rule wp_event_union_bound)
  also have "... \<le> M + A"
    by (intro add_mono merkle_bound slot_bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_verifier_tied_next_value_replay_gap_bound_from_merkle_and_slot:
  fixes M A :: prob
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and slot_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> A"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap s) s
      \<le> M + A"
proof -
  let ?P = "partial_merkle_inconsistency_bad s"
  let ?Q = "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s"
  have event_le:
    "wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap s) s \<le>
     wp_event verify_monad (\<lambda>out. ?P out \<or> ?Q out) s"
    by (rule wp_event_mono_on_support)
      (rule
        composition_fri_verifier_tied_next_value_replay_gap_imp_merkle_or_slot_on_support)
  also have "... \<le> wp_event verify_monad ?P s +
      wp_event verify_monad ?Q s"
    by (rule wp_event_union_bound)
  also have "... \<le> M + A"
    by (intro add_mono merkle_bound slot_bound)
  finally show ?thesis .
qed

end

end
