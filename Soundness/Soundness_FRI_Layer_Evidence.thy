(*  Title:      Stark/Soundness_FRI_Layer_Evidence.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Layer_Evidence
  imports Soundness_FRI_Partial_Evidence
begin

text \<open>
  Partial FRI layer evidence extracted from the verifier transcript.

  This theory only packages facts already exposed by the trace and composition
  layer-opening lemmas for @{term accepted_fri_opening_transcript}.  It does not
  reconstruct complete FRI tables from sampled openings.
\<close>

context soundness
begin

definition fri_layer_step_evidence
  :: "'f \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      nat \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> bool"
where
  "fri_layer_step_evidence rt ch len idx pw sibling_idx
      xp xp_path xn xn_path next_idx next_value chunk \<longleftrightarrow>
    sibling_idx = fri_sibling_index len idx \<and>
    next_idx = idx mod (len div 2) \<and>
    next_value =
      fri_fold_value ch xp xn
        (fri_fold_denominator ((h ^ idx) * shift) pw) \<and>
    fri_layer_opening_chunk len xp xp_path xn xn_path chunk"

definition fri_round_layer_evidence
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> 'f list list list \<Rightarrow> bool"
where
  "fri_round_layer_evidence roots challenges query_idxs round_idx
      layer_idx round_layers \<longleftrightarrow>
    round_idx < length query_idxs \<and>
    layer_idx < length roots \<and>
    length challenges = length roots \<and>
    length round_layers = length query_idxs \<and>
    (\<exists>xp xp_path xn xn_path.
      fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
        (fri_layer_indices (length roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index
          (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
          (fri_layer_indices (length roots) (query_idxs ! round_idx)
            (clength * scale) ! layer_idx))
        xp xp_path xn xn_path
        ((fri_layer_indices (length roots) (query_idxs ! round_idx)
            (clength * scale) ! layer_idx) mod
          ((fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
            div 2))
        (fri_fold_value (challenges ! layer_idx) xp xn
          (fri_fold_denominator
            ((h ^
              (fri_layer_indices (length roots) (query_idxs ! round_idx)
                (clength * scale) ! layer_idx)) * shift)
            (2 ^ layer_idx)))
        (round_layers ! round_idx ! layer_idx))"

definition fri_all_round_layer_evidence
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> bool"
where
  "fri_all_round_layer_evidence roots challenges query_idxs round_layers
    \<longleftrightarrow>
      length challenges = length roots \<and>
      length round_layers = length query_idxs \<and>
      (\<forall>round_idx < length query_idxs.
        \<forall>layer_idx < length roots.
          fri_round_layer_evidence roots challenges query_idxs round_idx
            layer_idx round_layers)"

definition fri_evidence_layer_len :: "'f list \<Rightarrow> nat \<Rightarrow> nat"
where
  "fri_evidence_layer_len roots layer_idx =
    fri_layer_lengths (length roots) (clength * scale) ! layer_idx"

definition fri_evidence_layer_idx
  :: "'f list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
    fri_layer_indices (length roots) (query_idxs ! round_idx)
      (clength * scale) ! layer_idx"

definition fri_evidence_next_idx
  :: "'f list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "fri_evidence_next_idx roots query_idxs round_idx layer_idx =
    fri_evidence_layer_idx roots query_idxs round_idx layer_idx mod
      (fri_evidence_layer_len roots layer_idx div 2)"

definition fri_evidence_next_value
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      'f \<Rightarrow> 'f \<Rightarrow> 'f"
where
  "fri_evidence_next_value roots challenges query_idxs round_idx layer_idx
      xp xn =
    fri_fold_value (challenges ! layer_idx) xp xn
      (fri_fold_denominator
        ((h ^ fri_evidence_layer_idx roots query_idxs round_idx layer_idx) *
          shift)
        (2 ^ layer_idx))"

definition fri_sampled_table_fold
  :: "'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> bool"
where
  "fri_sampled_table_fold ch len idx pw fri_dom layer chunk next_value
    \<longleftrightarrow>
      (\<exists>xp xp_path xn xn_path.
        fri_layer_opening_chunk len xp xp_path xn xn_path chunk \<and>
        fri_opening_matches_table len idx layer xp xn \<and>
        fri_dom ! idx = (h ^ idx * shift) ^ pw \<and>
        next_value = fri_table_fold_value ch layer fri_dom len pw idx)"

definition generic_fri_round_forced_next_value
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow> bool"
where
  "generic_fri_round_forced_next_value roots challenges query_idxs
      round_layers round_idx layer_idx v \<longleftrightarrow>
    (\<exists>xp xp_path xn xn_path.
      fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        v
        (round_layers ! round_idx ! layer_idx))"

lemma fri_layer_step_evidenceI:
  assumes "sibling_idx = fri_sibling_index len idx"
    and "next_idx = idx mod (len div 2)"
    and "next_value =
      fri_fold_value ch xp xn
        (fri_fold_denominator ((h ^ idx) * shift) pw)"
    and "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
  shows "fri_layer_step_evidence rt ch len idx pw sibling_idx
    xp xp_path xn xn_path next_idx next_value chunk"
  using assms unfolding fri_layer_step_evidence_def by simp

lemma fri_layer_step_evidenceD:
  assumes "fri_layer_step_evidence rt ch len idx pw sibling_idx
    xp xp_path xn xn_path next_idx next_value chunk"
  shows "sibling_idx = fri_sibling_index len idx"
    and "next_idx = idx mod (len div 2)"
    and "next_value =
      fri_fold_value ch xp xn
        (fri_fold_denominator ((h ^ idx) * shift) pw)"
    and "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
  using assms unfolding fri_layer_step_evidence_def by simp_all

lemma fri_layer_opening_chunk_values_unique:
  assumes first:
    "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and second:
    "fri_layer_opening_chunk len yp yp_path yn yn_path chunk"
  shows "xp = yp"
    and "xn = yn"
proof -
  have chunk_eq:
    "[xp] @ xp_path @ [xn] @ xn_path =
      [yp] @ yp_path @ [yn] @ yn_path"
    using first second unfolding fri_layer_opening_chunk_def by simp
  then show "xp = yp"
    by simp
  have len_eq: "length xp_path = length yp_path"
    using first second unfolding fri_layer_opening_chunk_def by simp
  have left:
    "([xp] @ xp_path @ [xn] @ xn_path) ! Suc (length xp_path) = xn"
    by simp
  have right:
    "([yp] @ yp_path @ [yn] @ yn_path) ! Suc (length xp_path) = yn"
    using len_eq by simp
  show "xn = yn"
    using chunk_eq left right by metis
qed

lemma fri_round_layer_evidenceE:
  assumes evidence:
    "fri_round_layer_evidence roots challenges query_idxs round_idx
      layer_idx round_layers"
  obtains xp xp_path xn xn_path
  where "round_idx < length query_idxs"
    and "layer_idx < length roots"
    and "length challenges = length roots"
    and "length round_layers = length query_idxs"
    and "fri_layer_step_evidence
      (roots ! layer_idx)
      (challenges ! layer_idx)
      (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
      (fri_layer_indices (length roots) (query_idxs ! round_idx)
        (clength * scale) ! layer_idx)
      (2 ^ layer_idx)
      (fri_sibling_index
        (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
        (fri_layer_indices (length roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx))
      xp xp_path xn xn_path
      ((fri_layer_indices (length roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx) mod
        ((fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
          div 2))
      (fri_fold_value (challenges ! layer_idx) xp xn
        (fri_fold_denominator
          ((h ^
            (fri_layer_indices (length roots) (query_idxs ! round_idx)
              (clength * scale) ! layer_idx)) * shift)
          (2 ^ layer_idx)))
      (round_layers ! round_idx ! layer_idx)"
  using evidence unfolding fri_round_layer_evidence_def by blast

lemma fri_round_layer_evidence_compactE:
  assumes evidence:
    "fri_round_layer_evidence roots challenges query_idxs round_idx
      layer_idx round_layers"
  obtains xp xp_path xn xn_path
  where "round_idx < length query_idxs"
    and "layer_idx < length roots"
    and "length challenges = length roots"
    and "length round_layers = length query_idxs"
    and "fri_layer_step_evidence
      (roots ! layer_idx)
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
      xp xp_path xn xn_path
      (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
      (fri_evidence_next_value roots challenges query_idxs round_idx
        layer_idx xp xn)
      (round_layers ! round_idx ! layer_idx)"
proof -
  from fri_round_layer_evidenceE[OF evidence]
  obtain xp xp_path xn xn_path where
    round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length roots"
    and challenges_len: "length challenges = length roots"
    and layers_len: "length round_layers = length query_idxs"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
        (fri_layer_indices (length roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index
          (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
          (fri_layer_indices (length roots) (query_idxs ! round_idx)
            (clength * scale) ! layer_idx))
        xp xp_path xn xn_path
        ((fri_layer_indices (length roots) (query_idxs ! round_idx)
            (clength * scale) ! layer_idx) mod
          ((fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
            div 2))
        (fri_fold_value (challenges ! layer_idx) xp xn
          (fri_fold_denominator
            ((h ^
              (fri_layer_indices (length roots) (query_idxs ! round_idx)
                (clength * scale) ! layer_idx)) * shift)
            (2 ^ layer_idx)))
        (round_layers ! round_idx ! layer_idx)"
    by blast
  have compact_step:
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
      (fri_evidence_next_value roots challenges query_idxs round_idx
        layer_idx xp xn)
      (round_layers ! round_idx ! layer_idx)"
    using step
    unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
      fri_evidence_next_idx_def fri_evidence_next_value_def
    by simp
  show ?thesis
    by (rule that[OF round_bound layer_bound challenges_len layers_len
          compact_step])
qed

lemma fri_all_round_layer_evidenceD:
  assumes evidence:
    "fri_all_round_layer_evidence roots challenges query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length roots"
  shows "fri_round_layer_evidence roots challenges query_idxs round_idx
    layer_idx round_layers"
  using assms unfolding fri_all_round_layer_evidence_def by blast

lemma fri_layer_step_evidence_from_outcome:
  assumes outcome:
    "Some ((next_idx, next_value, next_len, next_pw), t) \<in>
      set_dist (execute (fri_layer_opening_step (ch, rt)
        (idx, x, len, pw)) s)"
  obtains xp xp_path xn xn_path chunk
  where "fri_layer_step_evidence rt ch len idx pw
      (fri_sibling_index len idx) xp xp_path xn xn_path
      next_idx next_value chunk"
    and "chunk = [xp] @ xp_path @ [xn] @ xn_path"
    and "x = xp"
    and "next_len = len div 2"
    and "next_pw = pw + pw"
proof -
  from fri_layer_opening_step_outcome[OF outcome]
  obtain xp xp_path xn xn_path x' where
    out_eq:
      "(next_idx, next_value, next_len, next_pw) =
        (idx mod (len div 2), x', len div 2, pw + pw)"
    and xp_eq: "xp = x"
    and x'_eq:
      "x' = fri_fold_value ch xp xn
        (fri_fold_denominator ((h ^ idx) * shift) pw)"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path
        ([xp] @ xp_path @ [xn] @ xn_path)"
    by blast
  let ?chunk = "[xp] @ xp_path @ [xn] @ xn_path"
  have step:
    "fri_layer_step_evidence rt ch len idx pw
      (fri_sibling_index len idx) xp xp_path xn xn_path next_idx
      next_value ?chunk"
    using out_eq x'_eq chunk unfolding fri_layer_step_evidence_def by simp
  show ?thesis
    by (rule that[OF step refl])
      (use out_eq xp_eq in simp_all)
qed

lemma fri_layer_step_evidence_fold_table_if_opening_matches:
  assumes evidence:
    "fri_layer_step_evidence rt ch len idx pw sibling_idx
      xp xp_path xn xn_path next_idx next_value chunk"
    and dom_i: "fri_dom ! idx = (h ^ idx * shift) ^ pw"
    and match: "fri_opening_matches_table len idx layer xp xn"
  shows "next_value = fri_table_fold_value ch layer fri_dom len pw idx"
proof -
  have next_value_eq:
    "next_value =
      fri_fold_value ch xp xn
        (fri_fold_denominator ((h ^ idx) * shift) pw)"
    using fri_layer_step_evidenceD(3)[OF evidence] .
  also have "... = fri_table_fold_value ch layer fri_dom len pw idx"
    by (rule fri_fold_value_eq_table_fold_value[OF dom_i match])
  finally show ?thesis .
qed

lemma fri_layer_step_evidence_fold_table_if_matching_chunk:
  assumes evidence:
    "fri_layer_step_evidence rt ch len idx pw sibling_idx
      xp xp_path xn xn_path next_idx next_value chunk"
    and dom_i: "fri_dom ! idx = (h ^ idx * shift) ^ pw"
    and chunk_match:
      "fri_layer_opening_chunk len yp yp_path yn yn_path chunk"
    and table_match: "fri_opening_matches_table len idx layer yp yn"
  shows "next_value = fri_table_fold_value ch layer fri_dom len pw idx"
proof -
  have step_chunk: "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    by (rule fri_layer_step_evidenceD(4)[OF evidence])
  have xp_eq: "xp = yp"
    by (rule fri_layer_opening_chunk_values_unique(1)
        [OF step_chunk chunk_match])
  have xn_eq: "xn = yn"
    by (rule fri_layer_opening_chunk_values_unique(2)
        [OF step_chunk chunk_match])
  have table_match':
    "fri_opening_matches_table len idx layer xp xn"
    using table_match xp_eq xn_eq by simp
  show ?thesis
    by (rule fri_layer_step_evidence_fold_table_if_opening_matches
        [OF evidence dom_i table_match'])
qed

lemma fri_sampled_table_foldI:
  assumes
    "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and "fri_opening_matches_table len idx layer xp xn"
    and "fri_dom ! idx = (h ^ idx * shift) ^ pw"
    and "next_value = fri_table_fold_value ch layer fri_dom len pw idx"
  shows "fri_sampled_table_fold ch len idx pw fri_dom layer chunk
    next_value"
  using assms unfolding fri_sampled_table_fold_def by blast

lemma fri_sampled_table_foldE:
  assumes "fri_sampled_table_fold ch len idx pw fri_dom layer chunk
    next_value"
  obtains xp xp_path xn xn_path
  where "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and "fri_opening_matches_table len idx layer xp xn"
    and "fri_dom ! idx = (h ^ idx * shift) ^ pw"
    and "next_value = fri_table_fold_value ch layer fri_dom len pw idx"
  using assms unfolding fri_sampled_table_fold_def by blast

lemma fri_layer_step_evidence_sampled_table_fold_if_matching_chunk:
  assumes evidence:
    "fri_layer_step_evidence rt ch len idx pw sibling_idx
      xp xp_path xn xn_path next_idx next_value chunk"
    and dom_i: "fri_dom ! idx = (h ^ idx * shift) ^ pw"
    and chunk_match:
      "fri_layer_opening_chunk len yp yp_path yn yn_path chunk"
    and table_match: "fri_opening_matches_table len idx layer yp yn"
  shows "fri_sampled_table_fold ch len idx pw fri_dom layer chunk
    next_value"
proof -
  have fold_eq:
    "next_value = fri_table_fold_value ch layer fri_dom len pw idx"
    by (rule fri_layer_step_evidence_fold_table_if_matching_chunk
        [OF evidence dom_i chunk_match table_match])
  show ?thesis
    by (rule fri_sampled_table_foldI
        [OF chunk_match table_match dom_i fold_eq])
qed

lemma fri_layer_opening_matches_bound_table_compactE:
  assumes match:
    "fri_layer_opening_matches_bound_table query_idx layer_idx tables
      layer_chunks"
    and tables_len: "length tables = length roots"
  obtains xp xp_path xn xn_path
  where
    "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
      xp xp_path xn xn_path (layer_chunks ! layer_idx)"
    and "fri_opening_matches_table
      (fri_evidence_layer_len roots layer_idx)
      (fri_layer_indices (length roots) query_idx (clength * scale) !
        layer_idx)
      (tables ! layer_idx) xp xn"
proof -
  let ?len = "fri_evidence_layer_len roots layer_idx"
  let ?idx =
    "fri_layer_indices (length roots) query_idx (clength * scale) !
      layer_idx"
  from match obtain xp xp_path xn xn_path where
    chunk:
      "fri_layer_opening_chunk ?len xp xp_path xn xn_path
        (layer_chunks ! layer_idx)"
    and table_match:
      "fri_opening_matches_table ?len ?idx (tables ! layer_idx) xp xn"
    unfolding fri_layer_opening_matches_bound_table_def
    by (auto simp: Let_def tables_len fri_evidence_layer_len_def)
  show ?thesis
    by (rule that[OF chunk table_match])
qed

lemma fri_all_round_openings_match_tablesD:
  assumes all:
    "fri_all_round_openings_match_tables tables query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length tables"
  shows "fri_layer_opening_matches_bound_table
    (query_idxs ! round_idx) layer_idx tables
    (round_layers ! round_idx)"
  using assms
  unfolding fri_all_round_openings_match_tables_def
    fri_round_openings_match_tables_def
  by blast

lemma accepted_fri_opening_transcript_trace_round_layer_evidence:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and round_bound: "round_idx < rounds"
    and layer_bound: "layer_idx < length trace_roots"
  shows "fri_round_layer_evidence trace_roots trace_bs query_idxs
    round_idx layer_idx trace_round_layers"
proof -
  have shapes:
    "length trace_bs = length trace_roots"
    "length trace_round_layers = rounds"
    "length query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes[OF fri_openings] by blast+
  from accepted_fri_opening_transcript_trace_layer_opening
    [OF fri_openings round_bound layer_bound]
  obtain root challenge len idx sibling_idx xp xp_path xn xn_path where
    root_eq: "root = trace_roots ! layer_idx"
    and challenge_eq: "challenge = trace_bs ! layer_idx"
    and len_eq:
      "len =
        fri_layer_lengths (length trace_roots) (clength * scale) ! layer_idx"
    and idx_eq:
      "idx =
        fri_layer_indices (length trace_roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx"
    and sibling_eq: "sibling_idx = fri_sibling_index len idx"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path
        (trace_round_layers ! round_idx ! layer_idx)"
    by blast
  have step:
    "fri_layer_step_evidence (trace_roots ! layer_idx)
      (trace_bs ! layer_idx)
      (fri_layer_lengths (length trace_roots) (clength * scale) ! layer_idx)
      (fri_layer_indices (length trace_roots) (query_idxs ! round_idx)
        (clength * scale) ! layer_idx)
      (2 ^ layer_idx)
      (fri_sibling_index
        (fri_layer_lengths (length trace_roots) (clength * scale) ! layer_idx)
        (fri_layer_indices (length trace_roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx))
      xp xp_path xn xn_path
      ((fri_layer_indices (length trace_roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx) mod
        ((fri_layer_lengths (length trace_roots) (clength * scale) ! layer_idx)
          div 2))
      (fri_fold_value (trace_bs ! layer_idx) xp xn
        (fri_fold_denominator
          ((h ^
            (fri_layer_indices (length trace_roots) (query_idxs ! round_idx)
              (clength * scale) ! layer_idx)) * shift)
          (2 ^ layer_idx)))
      (trace_round_layers ! round_idx ! layer_idx)"
    using sibling_eq chunk unfolding fri_layer_step_evidence_def
    by (simp add: len_eq idx_eq)
  show ?thesis
    unfolding fri_round_layer_evidence_def
    using round_bound layer_bound shapes step
    by auto
qed

lemma accepted_fri_opening_transcript_composition_round_layer_evidence:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
    and round_bound: "round_idx < rounds"
    and layer_bound: "layer_idx < length composition_roots"
  shows "fri_round_layer_evidence composition_roots composition_bs query_idxs
    round_idx layer_idx composition_round_layers"
proof -
  have shapes:
    "length composition_bs = length composition_roots"
    "length composition_round_layers = rounds"
    "length query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes[OF fri_openings] by blast+
  from accepted_fri_opening_transcript_composition_layer_opening
    [OF fri_openings round_bound layer_bound]
  obtain root challenge len idx sibling_idx xp xp_path xn xn_path where
    root_eq: "root = composition_roots ! layer_idx"
    and challenge_eq: "challenge = composition_bs ! layer_idx"
    and len_eq:
      "len =
        fri_layer_lengths (length composition_roots) (clength * scale) !
          layer_idx"
    and idx_eq:
      "idx =
        fri_layer_indices (length composition_roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx"
    and sibling_eq: "sibling_idx = fri_sibling_index len idx"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path
        (composition_round_layers ! round_idx ! layer_idx)"
    by blast
  have step:
    "fri_layer_step_evidence (composition_roots ! layer_idx)
      (composition_bs ! layer_idx)
      (fri_layer_lengths (length composition_roots) (clength * scale) !
        layer_idx)
      (fri_layer_indices (length composition_roots) (query_idxs ! round_idx)
        (clength * scale) ! layer_idx)
      (2 ^ layer_idx)
      (fri_sibling_index
        (fri_layer_lengths (length composition_roots) (clength * scale) !
          layer_idx)
        (fri_layer_indices (length composition_roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx))
      xp xp_path xn xn_path
      ((fri_layer_indices (length composition_roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx) mod
        ((fri_layer_lengths (length composition_roots) (clength * scale) !
          layer_idx) div 2))
      (fri_fold_value (composition_bs ! layer_idx) xp xn
        (fri_fold_denominator
          ((h ^
            (fri_layer_indices (length composition_roots)
              (query_idxs ! round_idx) (clength * scale) ! layer_idx)) *
            shift)
          (2 ^ layer_idx)))
      (composition_round_layers ! round_idx ! layer_idx)"
    using sibling_eq chunk unfolding fri_layer_step_evidence_def
    by (simp add: len_eq idx_eq)
  show ?thesis
    unfolding fri_round_layer_evidence_def
    using round_bound layer_bound shapes step
    by auto
qed

lemma accepted_fri_opening_transcript_trace_all_round_layer_evidence:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
  shows "fri_all_round_layer_evidence trace_roots trace_bs query_idxs
    trace_round_layers"
proof -
  have shapes:
    "length trace_bs = length trace_roots"
    "length trace_round_layers = rounds"
    "length query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes[OF fri_openings] by blast+
  show ?thesis
    unfolding fri_all_round_layer_evidence_def
    using shapes
    by (intro conjI allI impI)
      (auto intro:
        accepted_fri_opening_transcript_trace_round_layer_evidence
          [OF fri_openings])
qed

lemma accepted_fri_opening_transcript_composition_all_round_layer_evidence:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
  shows "fri_all_round_layer_evidence composition_roots composition_bs
    query_idxs composition_round_layers"
proof -
  have shapes:
    "length composition_bs = length composition_roots"
    "length composition_round_layers = rounds"
    "length query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes[OF fri_openings] by blast+
  show ?thesis
    unfolding fri_all_round_layer_evidence_def
    using shapes
    by (intro conjI allI impI)
      (auto intro:
        accepted_fri_opening_transcript_composition_round_layer_evidence
          [OF fri_openings])
qed

lemma ntimes_verifier_query_round_program_final_checks_at:
  assumes outcome:
    "Some (results, t) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final) n)
          s)"
    and i_bound: "i < n"
  obtains prefix suffix s_i s_suc raw idx fv s0 s1
      f_i f_len f_pow s2 c_i c_len c_pow s4
  where
    "Some (prefix, s_i) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final) i)
          s)"
    "Some ((), s_suc) \<in>
      set_dist
        (execute
          (verifier_query_round_program fr f_fl f_final as fl final) s_i)"
    "Some (suffix, t) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            (n - Suc i))
          s_suc)"
    "results = prefix @ () # suffix"
    "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s_i)"
    "idx = index (to_nat raw)"
    "Some (fv, s1) \<in>
      set_dist (execute (mmap (check_decommit_on_query fr idx)) s0)"
    "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
      set_dist
        (execute
          (mfold (idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    "Some ((c_i, final, c_len, c_pow), s4) \<in>
      set_dist
        (execute
          (mfold (idx, cp_eval as fv (h ^ idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s2)"
    "s_suc = s4"
proof -
  let ?round = "verifier_query_round_program fr f_fl f_final as fl final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix x suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in> set_dist (execute (ntimes ?round i) s)"
    and round:
      "Some (x, s_suc) \<in> set_dist (execute ?round s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist (execute (ntimes ?round (n - Suc i)) s_suc)"
    and results_eq: "results = prefix @ x # suffix"
    by blast
  have x_eq: "x = ()"
    by (cases x) simp
  have round_unit:
    "Some ((), s_suc) \<in> set_dist (execute ?round s_i)"
    using round x_eq by simp
  show ?thesis
  proof (rule verifier_query_round_program_final_checks[OF round_unit])
    fix raw idx fv s0 s1 f_i f_len f_pow s2 c_i c_len c_pow s4
    assume raw:
        "Some (raw, s0) \<in>
          set_dist (execute receive_query_index_challenge s_i)"
      and idx_eq: "idx = index (to_nat raw)"
      and query_decommit:
        "Some (fv, s1) \<in>
          set_dist (execute (mmap (check_decommit_on_query fr idx)) s0)"
      and trace_final:
        "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
          set_dist
            (execute
              (mfold (idx, hd fv, clength * scale, 1)
                (receive_query_commits f_fl)) s1)"
      and composition_final:
        "Some ((c_i, final, c_len, c_pow), s4) \<in>
          set_dist
            (execute
              (mfold (idx, cp_eval as fv (h ^ idx * shift),
                  clength * scale, 1)
                (receive_query_commits fl)) s2)"
      and s_suc_eq: "s_suc = s4"
    have results_unit: "results = prefix @ () # suffix"
      using results_eq x_eq by simp
    show ?thesis
      by (rule that[OF prefix round_unit suffix results_unit raw idx_eq
            query_decommit trace_final composition_final s_suc_eq])
  qed
qed

end

end
