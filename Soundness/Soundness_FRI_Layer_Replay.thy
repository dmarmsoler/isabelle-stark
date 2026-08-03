(*  Title:      Stark/Soundness_FRI_Layer_Replay.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Layer_Replay
  imports Soundness_FRI_Layer_Authenticated
begin

text \<open>
  Narrow replay facts for selected FRI layer openings.

  The first lemma is a generic selected-position decomposition for
  @{term mfold}.  It avoids adding another proof by induction over the full
  FRI verifier layer in the already-large Merkle theory.
\<close>

context soundness
begin

lemma fri_layer_lengths_prefix_nth:
  assumes "j < n"
  shows "fri_layer_lengths n len ! j = fri_layer_lengths (Suc j) len ! j"
  using assms
proof (induction j arbitrary: n len)
  case 0
  then show ?case
    by (cases n) simp_all
next
  case (Suc j)
  then obtain n' where n_eq: "n = Suc n'"
    by (cases n) auto
  have j_bound: "j < n'"
    using Suc.prems unfolding n_eq by simp
  show ?case
    using Suc.IH[OF j_bound, of "len div 2"]
    unfolding n_eq by simp
qed

lemma fri_layer_indices_prefix_nth:
  assumes "j < n"
  shows
    "fri_layer_indices n idx len ! j =
      fri_layer_indices (Suc j) idx len ! j"
  using assms
proof (induction j arbitrary: n idx len)
  case 0
  then show ?case
    by (cases n) simp_all
next
  case (Suc j)
  then obtain n' where n_eq: "n = Suc n'"
    by (cases n) auto
  have j_bound: "j < n'"
    using Suc.prems unfolding n_eq by simp
  show ?case
    using Suc.IH[OF j_bound, of "idx mod (len div 2)" "len div 2"]
    unfolding n_eq by simp
qed

lemma fri_layer_lengths_prefix_same:
  assumes k_bound: "k < j"
  shows "fri_layer_lengths (Suc j) len ! k = fri_layer_lengths j len ! k"
  using fri_layer_lengths_prefix_nth[OF less_trans[OF k_bound lessI], of len]
    fri_layer_lengths_prefix_nth[OF k_bound, of len]
  by simp

lemma fri_layers_transcript_snoc:
  assumes prefix:
    "fri_layers_transcript j len prefix_chunks prefix_chunk"
    and last:
    "fri_layer_opening_chunk (fri_layer_lengths (Suc j) len ! j)
      xp xp_path xn xn_path last_chunk"
  shows
    "fri_layers_transcript (Suc j) len (prefix_chunks @ [last_chunk])
      (prefix_chunk @ last_chunk)"
  using prefix last
proof (induction j arbitrary: len prefix_chunks prefix_chunk)
  case 0
  then have chunks_eq: "prefix_chunks = []"
    and prefix_chunk_eq: "prefix_chunk = []"
    unfolding fri_layers_transcript_def by simp_all
  have last_fact:
    "fri_layer_opening_chunk len xp xp_path xn xn_path last_chunk"
    using "0.prems"(2) by simp
  have last_open:
    "\<exists>yp yp_path yn yn_path.
      fri_layer_opening_chunk len yp yp_path yn yn_path last_chunk"
    apply (rule exI[where x=xp])
    apply (rule exI[where x=xp_path])
    apply (rule exI[where x=xn])
    apply (rule exI[where x=xn_path])
    apply (rule last_fact)
    done
  show ?case
    unfolding chunks_eq prefix_chunk_eq fri_layers_transcript_def
    using last_open by simp
next
  case (Suc j)
  obtain first rest where chunks_eq: "prefix_chunks = first # rest"
    using Suc.prems(1) unfolding fri_layers_transcript_def
    by (cases prefix_chunks) auto
  have first_open:
    "\<exists>yp yp_path yn yn_path.
      fri_layer_opening_chunk len yp yp_path yn yn_path first"
    using Suc.prems(1) unfolding fri_layers_transcript_def chunks_eq
    by auto
  have rest_layers:
    "fri_layers_transcript j (len div 2) rest (List.concat rest)"
    using Suc.prems(1) unfolding fri_layers_transcript_def chunks_eq
    by auto
  have last_tail:
    "fri_layer_opening_chunk
      (fri_layer_lengths (Suc j) (len div 2) ! j)
      xp xp_path xn xn_path last_chunk"
    using Suc.prems(2) by simp
  have tail:
    "fri_layers_transcript (Suc j) (len div 2) (rest @ [last_chunk])
      (List.concat rest @ last_chunk)"
    by (rule Suc.IH[OF rest_layers last_tail])
  have prefix_chunk_eq: "prefix_chunk = first @ List.concat rest"
    using Suc.prems(1) unfolding fri_layers_transcript_def chunks_eq by simp
  show ?case
    unfolding chunks_eq prefix_chunk_eq fri_layers_transcript_def
    using first_open tail unfolding fri_layers_transcript_def by auto
qed

lemma fri_layers_transcript_last_chunk_eq:
  assumes layers:
    "fri_layers_transcript (Suc j) len layer_chunks chunk"
    and prefix:
    "fri_layers_transcript j len prefix_chunks prefix_chunk"
    and last:
    "fri_layer_opening_chunk (fri_layer_lengths (Suc j) len ! j)
      xp xp_path xn xn_path last_chunk"
    and chunk_eq: "chunk = prefix_chunk @ last_chunk"
  shows "layer_chunks ! j = last_chunk"
proof -
  have combined:
    "fri_layers_transcript (Suc j) len (prefix_chunks @ [last_chunk])
      (prefix_chunk @ last_chunk)"
    by (rule fri_layers_transcript_snoc[OF prefix last])
  have layers_eq: "layer_chunks = prefix_chunks @ [last_chunk]"
    by (rule fri_layers_transcript_unique
        [OF layers combined[unfolded chunk_eq[symmetric]]])
  have len_prefix: "length prefix_chunks = j"
    using prefix unfolding fri_layers_transcript_def by simp
  show ?thesis
    using layers_eq len_prefix by (simp add: nth_append)
qed

lemma generic_fri_round_forced_next_value_from_step_evidence:
  assumes step:
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
      v
      (round_layers ! round_idx ! layer_idx)"
  shows
    "generic_fri_round_forced_next_value roots challenges query_idxs
      round_layers round_idx layer_idx v"
  using step
  unfolding generic_fri_round_forced_next_value_def by blast

lemma mfold_outcome_decomp_at:
  assumes outcome:
    "Some (out, t) \<in> set_dist (execute (mfold a ms) s)"
    and j_bound: "j < length ms"
  shows
    "\<exists>a_j s_j out_j s_suc.
      Some (a_j, s_j) \<in> set_dist (execute (mfold a (take j ms)) s) \<and>
      Some (out_j, s_suc) \<in> set_dist (execute ((ms ! j) a_j) s_j) \<and>
      Some (out, t) \<in>
        set_dist (execute (mfold out_j (drop (Suc j) ms)) s_suc)"
  using outcome j_bound
proof (induction j arbitrary: a ms s)
  case 0
  then obtain m ms' where ms_eq: "ms = m # ms'"
    by (cases ms) auto
  from "0.prems"(1)[unfolded ms_eq]
  obtain out_j s_suc where
    head: "Some (out_j, s_suc) \<in> set_dist (execute (m a) s)"
    and tail:
      "Some (out, t) \<in> set_dist (execute (mfold out_j ms') s_suc)"
    by (auto elim!: set_dist_bindE)
  have prefix: "Some (a, s) \<in> set_dist (execute (mfold a (take 0 ms)) s)"
    by simp
  have selected_orig:
    "Some (out_j, s_suc) \<in> set_dist (execute ((ms ! 0) a) s)"
    using head unfolding ms_eq by simp
  have suffix_orig:
    "Some (out, t) \<in>
      set_dist (execute (mfold out_j (drop (Suc 0) ms)) s_suc)"
    using tail unfolding ms_eq by simp
  show ?case
    by (intro exI[of _ a] exI[of _ s] exI[of _ out_j]
        exI[of _ s_suc] conjI)
      (use prefix selected_orig suffix_orig in simp_all)
next
  case (Suc j)
  then obtain m ms' where ms_eq: "ms = m # ms'"
    by (cases ms) auto
  from Suc.prems(1)[unfolded ms_eq]
  obtain out1 s1 where
    head: "Some (out1, s1) \<in> set_dist (execute (m a) s)"
    and tail:
      "Some (out, t) \<in> set_dist (execute (mfold out1 ms') s1)"
    by (auto elim!: set_dist_bindE)
  have j_bound': "j < length ms'"
    using Suc.prems(2) unfolding ms_eq by simp
  from Suc.IH[OF tail j_bound']
  obtain a_j s_j out_j s_suc where
    prefix_tail:
      "Some (a_j, s_j) \<in>
        set_dist (execute (mfold out1 (take j ms')) s1)"
    and selected:
      "Some (out_j, s_suc) \<in>
        set_dist (execute ((ms' ! j) a_j) s_j)"
    and suffix:
      "Some (out, t) \<in>
        set_dist (execute (mfold out_j (drop (Suc j) ms')) s_suc)"
    by blast
  have prefix_unfolded:
    "Some (a_j, s_j) \<in>
      set_dist (execute ((m a) \<bind> (\<lambda>x. mfold x (take j ms'))) s)"
    by (rule_tac x=out1 and t=s1 in set_dist_bindI)
      (use head prefix_tail in simp_all)
  have prefix_mfold:
    "Some (a_j, s_j) \<in>
      set_dist (execute (mfold a (m # take j ms')) s)"
    using prefix_unfolded by simp
  have prefix:
    "Some (a_j, s_j) \<in>
      set_dist (execute (mfold a (take (Suc j) ms)) s)"
    using prefix_mfold unfolding ms_eq by simp
  have selected_orig:
    "Some (out_j, s_suc) \<in>
      set_dist (execute ((ms ! Suc j) a_j) s_j)"
    using selected unfolding ms_eq by simp
  have suffix_orig:
    "Some (out, t) \<in>
      set_dist (execute (mfold out_j (drop (Suc (Suc j)) ms)) s_suc)"
    using suffix unfolding ms_eq by simp
  show ?case
    by (intro exI[of _ a_j] exI[of _ s_j] exI[of _ out_j]
        exI[of _ s_suc] conjI)
      (use prefix selected_orig suffix_orig in simp_all)
qed

lemma mfold_fri_layer_openings_decomp_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (out, t) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw) (map fri_layer_opening_step bfs)) s)"
    and j_bound: "j < length bfs"
  obtains idx_j x_j len_j pw_j out_j s_j s_suc where
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    "Some (out_j, s_suc) \<in>
      set_dist
        (execute
          (fri_layer_opening_step (bfs ! j)
            (idx_j, x_j, len_j, pw_j)) s_j)"
    "Some (out, t) \<in>
      set_dist
        (execute
          (mfold out_j (drop (Suc j) (map fri_layer_opening_step bfs)))
          s_suc)"
proof -
  have mapped_bound: "j < length (map fri_layer_opening_step bfs)"
    using j_bound by simp
  from mfold_outcome_decomp_at[OF outcome mapped_bound]
  obtain a_j s_j out_j s_suc where
    prefix:
      "Some (a_j, s_j) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (take j (map fri_layer_opening_step bfs))) s)"
    and selected:
      "Some (out_j, s_suc) \<in>
        set_dist
          (execute
            ((map fri_layer_opening_step bfs ! j) a_j) s_j)"
    and suffix:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold out_j (drop (Suc j) (map fri_layer_opening_step bfs)))
            s_suc)"
    by blast
  obtain idx_j x_j len_j pw_j where a_j_eq:
    "a_j = (idx_j, x_j, len_j, pw_j)"
    by (cases a_j)
  have selected':
    "Some (out_j, s_suc) \<in>
      set_dist
        (execute
          (fri_layer_opening_step (bfs ! j)
            (idx_j, x_j, len_j, pw_j)) s_j)"
    using selected j_bound unfolding a_j_eq by simp
  show ?thesis
    by (rule that[OF prefix[unfolded a_j_eq] selected' suffix])
qed

lemma mfold_fri_layer_openings_prefix_idx_len:
  fixes s s_j :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    and j_bound: "j \<le> length bfs"
  shows
    "idx_j = fri_layer_indices (Suc j) idx len ! j \<and>
     len_j = fri_layer_lengths (Suc j) len ! j"
  using prefix j_bound
proof (induction j arbitrary: idx x len pw bfs s idx_j x_j len_j pw_j s_j)
  case 0
  then show ?case
    by simp
next
  case (Suc j)
  then obtain bf bfs' where bfs_eq: "bfs = bf # bfs'"
    by (cases bfs) auto
  obtain b rt where bf_eq: "bf = (b, rt)"
    by (cases bf)
  from Suc.prems(1)[unfolded bfs_eq]
  obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist
          (execute (fri_layer_opening_step bf (idx, x, len, pw)) s)"
    and tail:
      "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
        set_dist
          (execute
            (mfold out1 (take j (map fri_layer_opening_step bfs'))) s1)"
    by (auto elim!: set_dist_bindE)
  from fri_layer_opening_step_outcome[OF head[unfolded bf_eq]]
  obtain x' xp xp_path xn xn_path where out1_eq:
    "out1 = (idx mod (len div 2), x', len div 2, pw + pw)"
    by blast
  have j_bound': "j \<le> length bfs'"
    using Suc.prems(2) unfolding bfs_eq by simp
  have tail_shape:
    "idx_j =
      fri_layer_indices (Suc j) (idx mod (len div 2)) (len div 2) ! j \<and>
     len_j = fri_layer_lengths (Suc j) (len div 2) ! j"
    by (rule Suc.IH[OF tail[unfolded out1_eq] j_bound'])
  show ?case
    using tail_shape by simp
qed

lemma mfold_fri_layer_openings_prefix_pow:
  fixes s s_j :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    and j_bound: "j \<le> length bfs"
  shows "pw_j = pw * 2 ^ j"
  using prefix j_bound
proof (induction j arbitrary: idx x len pw bfs s idx_j x_j len_j pw_j s_j)
  case 0
  then show ?case
    by simp
next
  case (Suc j)
  then obtain bf bfs' where bfs_eq: "bfs = bf # bfs'"
    by (cases bfs) auto
  obtain b rt where bf_eq: "bf = (b, rt)"
    by (cases bf)
  from Suc.prems(1)[unfolded bfs_eq]
  obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist
          (execute (fri_layer_opening_step bf (idx, x, len, pw)) s)"
    and tail:
      "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
        set_dist
          (execute
            (mfold out1 (take j (map fri_layer_opening_step bfs'))) s1)"
    by (auto elim!: set_dist_bindE)
  from fri_layer_opening_step_outcome[OF head[unfolded bf_eq]]
  obtain x' xp xp_path xn xn_path where out1_eq:
    "out1 = (idx mod (len div 2), x', len div 2, pw + pw)"
    by blast
  have j_bound': "j \<le> length bfs'"
    using Suc.prems(2) unfolding bfs_eq by simp
  have tail_pow: "pw_j = (pw + pw) * 2 ^ j"
    by (rule Suc.IH[OF tail[unfolded out1_eq] j_bound'])
  then show ?case
    by simp
qed

lemma mfold_fri_layer_openings_prefix_pow_full:
  fixes s s_j :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    and j_bound: "j < length bfs"
  shows "pw_j = pw * 2 ^ j"
  by (rule mfold_fri_layer_openings_prefix_pow[OF prefix])
    (use j_bound in simp)

lemma mfold_fri_layer_openings_prefix_idx_len_full:
  fixes s s_j :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    and j_bound: "j < length bfs"
  shows
    "idx_j = fri_layer_indices (length bfs) idx len ! j \<and>
     len_j = fri_layer_lengths (length bfs) len ! j"
proof -
  have shape:
    "idx_j = fri_layer_indices (Suc j) idx len ! j \<and>
     len_j = fri_layer_lengths (Suc j) len ! j"
    by (rule mfold_fri_layer_openings_prefix_idx_len[OF prefix])
      (use j_bound in simp)
  show ?thesis
    using shape fri_layer_indices_prefix_nth[OF j_bound, of idx len]
      fri_layer_lengths_prefix_nth[OF j_bound, of len]
    by simp
qed

lemma fri_layer_opening_selected_step_authenticated_full:
  fixes s s_j s_suc :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    and selected:
      "Some (out_j, s_suc) \<in>
        set_dist
          (execute
            (fri_layer_opening_step (bfs ! j)
              (idx_j, x_j, len_j, pw_j)) s_j)"
    and j_bound: "j < length bfs"
    and layer_len_pos:
      "0 < fri_layer_lengths (length bfs) len ! j"
    and layer_idx_bound:
      "fri_layer_indices (length bfs) idx len ! j <
        fri_layer_lengths (length bfs) len ! j"
  obtains chunk where
    "fri_layer_chunk_authenticated (snd (bfs ! j))
      (fri_layer_lengths (length bfs) len ! j)
      (fri_layer_indices (length bfs) idx len ! j)
      chunk s_suc"
proof -
  have shape:
    "idx_j = fri_layer_indices (length bfs) idx len ! j \<and>
     len_j = fri_layer_lengths (length bfs) len ! j"
    by (rule mfold_fri_layer_openings_prefix_idx_len_full
        [OF prefix j_bound])
  obtain b rt where bf_eq: "bfs ! j = (b, rt)"
    by (cases "bfs ! j")
  from fri_layer_opening_step_authenticated_chunk_pred
      [OF _ _ selected[unfolded bf_eq]]
  obtain chunk where auth:
    "fri_layer_chunk_authenticated rt len_j idx_j chunk s_suc"
    using layer_len_pos layer_idx_bound shape
    by blast
  show ?thesis
    by (rule that[of chunk])
      (use auth shape bf_eq in simp)
qed

lemma receive_query_commits_decomp_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (out, t) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw) (receive_query_commits bfs)) s)"
    and j_bound: "j < length bfs"
  obtains idx_j x_j len_j pw_j out_j s_j s_suc where
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    "Some (out_j, s_suc) \<in>
      set_dist
        (execute
          (fri_layer_opening_step (bfs ! j)
            (idx_j, x_j, len_j, pw_j)) s_j)"
    "Some (out, t) \<in>
      set_dist
        (execute
          (mfold out_j (drop (Suc j) (map fri_layer_opening_step bfs)))
          s_suc)"
proof -
  have map_eq: "receive_query_commits bfs = map fri_layer_opening_step bfs"
    unfolding receive_query_commits_def fri_layer_opening_step_def
    by (simp add: fun_eq_iff split: prod.splits)
  show ?thesis
    by (rule mfold_fri_layer_openings_decomp_at
        [OF outcome[unfolded map_eq] j_bound that])
qed

lemma receive_query_commits_prefix_idx_len:
  fixes s s_j :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    and j_bound: "j \<le> length bfs"
  shows
    "idx_j = fri_layer_indices (Suc j) idx len ! j \<and>
     len_j = fri_layer_lengths (Suc j) len ! j"
  by (rule mfold_fri_layer_openings_prefix_idx_len[OF prefix j_bound])

lemma receive_query_commits_prefix_pow:
  fixes s s_j :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    and j_bound: "j \<le> length bfs"
  shows "pw_j = pw * 2 ^ j"
  by (rule mfold_fri_layer_openings_prefix_pow[OF prefix j_bound])

lemma receive_query_commits_prefix_pow_full:
  fixes s s_j :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    and j_bound: "j < length bfs"
  shows "pw_j = pw * 2 ^ j"
  by (rule mfold_fri_layer_openings_prefix_pow_full[OF prefix j_bound])

lemma receive_query_commits_prefix_idx_len_full:
  fixes s s_j :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    and j_bound: "j < length bfs"
  shows
    "idx_j = fri_layer_indices (length bfs) idx len ! j \<and>
     len_j = fri_layer_lengths (length bfs) len ! j"
  by (rule mfold_fri_layer_openings_prefix_idx_len_full[OF prefix j_bound])

lemma fri_layer_opening_step_outcome_evidence:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some ((next_idx, next_value, next_len, next_pow), t) \<in>
      set_dist (execute (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
  obtains xp xp_path xn xn_path where
    "xp = x"
    "next_idx = idx mod (len div 2)"
    "next_len = len div 2"
    "next_pow = pw + pw"
    "fri_layer_step_evidence rt b len idx pw
      (fri_sibling_index len idx) xp xp_path xn xn_path
      next_idx next_value ([xp] @ xp_path @ [xn] @ xn_path)"
proof -
  from fri_layer_opening_step_outcome[OF outcome]
  obtain xp xp_path xn xn_path x' where out_eq:
      "(next_idx, next_value, next_len, next_pow) =
        (idx mod (len div 2), x', len div 2, pw + pw)"
    and xp_eq: "xp = x"
    and x'_eq:
      "x' = fri_fold_value b xp xn
        (fri_fold_denominator ((h ^ idx) * shift) pw)"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path
        ([xp] @ xp_path @ [xn] @ xn_path)"
    by blast
  have next_idx_eq: "next_idx = idx mod (len div 2)"
    using out_eq by simp
  have next_value_eq: "next_value = x'"
    using out_eq by simp
  have next_len_eq: "next_len = len div 2"
    using out_eq by simp
  have next_pow_eq: "next_pow = pw + pw"
    using out_eq by simp
  have evidence:
    "fri_layer_step_evidence rt b len idx pw
      (fri_sibling_index len idx) xp xp_path xn xn_path
      next_idx next_value ([xp] @ xp_path @ [xn] @ xn_path)"
    by (rule fri_layer_step_evidenceI)
      (use next_idx_eq next_value_eq x'_eq chunk in simp_all)
  show ?thesis
    by (rule that[OF xp_eq next_idx_eq next_len_eq next_pow_eq evidence])
qed

lemma receive_query_commits_last_step_evidence:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some ((out_idx, out_value, out_len, out_pow), t) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw) (receive_query_commits bfs)) s)"
    and nonempty: "0 < length bfs"
  obtains j idx_j x_j len_j pw_j b rt xp xp_path xn xn_path s_j
      s_suc where
    "j = length bfs - 1"
    "j < length bfs"
    "bfs ! j = (b, rt)"
    "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (take j (map fri_layer_opening_step bfs))) s)"
    "Some ((out_idx, out_value, out_len, out_pow), s_suc) \<in>
      set_dist
        (execute
          (fri_layer_opening_step (b, rt)
            (idx_j, x_j, len_j, pw_j)) s_j)"
    "t = s_suc"
    "idx_j = fri_layer_indices (length bfs) idx len ! j"
    "len_j = fri_layer_lengths (length bfs) len ! j"
    "pw_j = pw * 2 ^ j"
    "fri_layer_step_evidence rt b len_j idx_j pw_j
      (fri_sibling_index len_j idx_j) xp xp_path xn xn_path
      out_idx out_value ([xp] @ xp_path @ [xn] @ xn_path)"
proof -
  let ?j = "length bfs - 1"
  have j_bound: "?j < length bfs"
    using nonempty by simp
  show ?thesis
  proof (rule receive_query_commits_decomp_at[OF outcome j_bound])
    fix idx_j x_j len_j pw_j out_j s_j s_suc
    assume prefix:
        "Some ((idx_j, x_j, len_j, pw_j), s_j) \<in>
          set_dist
            (execute
              (mfold (idx, x, len, pw)
                (take ?j (map fri_layer_opening_step bfs))) s)"
      and selected:
        "Some (out_j, s_suc) \<in>
          set_dist
            (execute
              (fri_layer_opening_step (bfs ! ?j)
                (idx_j, x_j, len_j, pw_j)) s_j)"
      and suffix:
        "Some ((out_idx, out_value, out_len, out_pow), t) \<in>
          set_dist
            (execute
              (mfold out_j
                (drop (Suc ?j) (map fri_layer_opening_step bfs))) s_suc)"
    have drop_empty:
      "drop (Suc ?j) (map fri_layer_opening_step bfs) = []"
      using nonempty by simp
    have out_j_eq: "out_j = (out_idx, out_value, out_len, out_pow)"
      and t_eq: "t = s_suc"
      using suffix unfolding drop_empty by simp_all
    obtain b rt where bf_eq: "bfs ! ?j = (b, rt)"
      by (cases "bfs ! ?j")
    have shape:
      "idx_j = fri_layer_indices (length bfs) idx len ! ?j \<and>
       len_j = fri_layer_lengths (length bfs) len ! ?j"
      by (rule receive_query_commits_prefix_idx_len_full
          [OF prefix j_bound])
    have pow: "pw_j = pw * 2 ^ ?j"
      by (rule receive_query_commits_prefix_pow_full[OF prefix j_bound])
    show ?thesis
    proof (rule fri_layer_opening_step_outcome_evidence
        [OF selected[unfolded bf_eq out_j_eq]])
      fix xp xp_path xn xn_path
      assume
        "xp = x_j"
        "out_idx = idx_j mod (len_j div 2)"
        "out_len = len_j div 2"
        "out_pow = pw_j + pw_j"
        and step:
        "fri_layer_step_evidence rt b len_j idx_j pw_j
          (fri_sibling_index len_j idx_j) xp xp_path xn xn_path
          out_idx out_value ([xp] @ xp_path @ [xn] @ xn_path)"
      show ?thesis
        by (rule that[OF refl j_bound bf_eq prefix
              selected[unfolded bf_eq out_j_eq] t_eq conjunct1[OF shape]
              conjunct2[OF shape] pow step])
    qed
  qed
qed

lemma verifier_query_round_after_index_trace_fri_last_step_evidence:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some ((), t) \<in>
      set_dist
        (execute
          (verifier_query_round_after_index_program
            fr f_fl f_final as fl final raw) s)"
    and nonempty: "0 < length f_fl"
    and raw_layer:
      "\<And>raw'.
        0 < fri_layer_lengths (length f_fl) (clength * scale) !
          (length f_fl - 1) \<and>
        fri_layer_indices (length f_fl) (index (to_nat raw'))
          (clength * scale) ! (length f_fl - 1) <
        fri_layer_lengths (length f_fl) (clength * scale) !
          (length f_fl - 1)"
  obtains actual_chunk axp axp_path axn axn_path where
    "fri_layer_chunk_authenticated
      (snd (f_fl ! (length f_fl - 1)))
      (fri_layer_lengths (length f_fl) (clength * scale) !
        (length f_fl - 1))
      (fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! (length f_fl - 1))
      actual_chunk t"
    "fri_layer_step_evidence
      (snd (f_fl ! (length f_fl - 1)))
      (fst (f_fl ! (length f_fl - 1)))
      (fri_layer_lengths (length f_fl) (clength * scale) !
        (length f_fl - 1))
      (fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! (length f_fl - 1))
      (2 ^ (length f_fl - 1))
      (fri_sibling_index
        (fri_layer_lengths (length f_fl) (clength * scale) !
          (length f_fl - 1))
        (fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! (length f_fl - 1)))
      axp axp_path axn axn_path
      ((fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! (length f_fl - 1)) mod
        ((fri_layer_lengths (length f_fl) (clength * scale) !
          (length f_fl - 1)) div 2))
      f_final actual_chunk"
proof -
  show ?thesis
  proof (rule verifier_query_round_after_index_final_checks[OF outcome])
    fix idx fv s1 f_i f_len f_pow s2 c_i c_len c_pow s4
    assume idx_eq: "idx = index (to_nat raw)"
      and trace_fri:
        "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
          set_dist
            (execute
              (mfold (idx, hd fv, clength * scale, 1)
                (receive_query_commits f_fl)) s1)"
      and comp_fri:
        "Some ((c_i, final, c_len, c_pow), s4) \<in>
          set_dist
            (execute
              (mfold (idx, cp_eval as fv (h ^ idx * shift),
                  clength * scale, 1)
                (receive_query_commits fl)) s2)"
      and t_eq: "t = s4"
    let ?j = "length f_fl - 1"
    let ?len = "fri_layer_lengths (length f_fl) (clength * scale) ! ?j"
    let ?idx =
      "fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! ?j"
    have len_pos: "0 < ?len"
      using raw_layer[of raw] by simp
    have idx_bound: "?idx < ?len"
      using raw_layer[of raw] by simp
    show ?thesis
    proof (rule receive_query_commits_last_step_evidence
        [OF trace_fri[unfolded idx_eq] nonempty])
      fix j idx_j x_j len_j pw_j b rt xp xp_path xn xn_path s_j s_suc
      assume j_eq: "j = ?j"
        and bf_eq: "f_fl ! j = (b, rt)"
        and selected:
          "Some ((f_i, f_final, f_len, f_pow), s_suc) \<in>
            set_dist
              (execute
                (fri_layer_opening_step (b, rt)
                  (idx_j, x_j, len_j, pw_j)) s_j)"
        and s2_eq: "s2 = s_suc"
        and idx_j_eq:
          "idx_j =
            fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! j"
        and len_j_eq:
          "len_j =
            fri_layer_lengths (length f_fl) (clength * scale) ! j"
        and pw_j_eq: "pw_j = 1 * 2 ^ j"
      have len_pos_j: "0 < len_j"
        using len_pos len_j_eq j_eq by simp
      have idx_bound_j: "idx_j < len_j"
        using idx_bound idx_j_eq len_j_eq j_eq by simp
      show ?thesis
      proof (rule fri_layer_opening_step_outcome_authenticated
          [OF len_pos_j idx_bound_j selected])
        fix axp axp_path axn axn_path next_value actual_chunk
        assume selected_out:
            "(f_i, f_final, f_len, f_pow) =
              (idx_j mod (len_j div 2), next_value, len_j div 2,
                pw_j + pw_j)"
          and next_value_eq:
            "next_value =
              fri_fold_value b axp axn
                (fri_fold_denominator ((h ^ idx_j) * shift) pw_j)"
          and chunk:
            "fri_layer_opening_chunk len_j axp axp_path axn axn_path
              actual_chunk"
          and axp_auth:
            "authenticated_opening_in s_suc
              \<lparr>opening_root = rt, opening_length = len_j,
               opening_index = idx_j, opening_value = axp,
               opening_path = axp_path\<rparr>"
          and axn_auth:
            "authenticated_opening_in s_suc
              \<lparr>opening_root = rt, opening_length = len_j,
               opening_index = fri_sibling_index len_j idx_j,
               opening_value = axn, opening_path = axn_path\<rparr>"
        have f_final_eq: "f_final = next_value"
          using selected_out by simp
        have auth_s2:
          "fri_layer_chunk_authenticated rt len_j idx_j actual_chunk s2"
          unfolding s2_eq
          by (rule fri_layer_chunk_authenticatedI[OF chunk axp_auth axn_auth])
        have s2_t: "s2 \<le> t"
          using receive_query_commits_mfold_hash_extends[OF comp_fri] t_eq
          by simp
        have auth_t:
          "fri_layer_chunk_authenticated rt len_j idx_j actual_chunk t"
          by (rule fri_layer_chunk_authenticated_mono[OF auth_s2 s2_t])
        have step:
          "fri_layer_step_evidence rt b len_j idx_j pw_j
            (fri_sibling_index len_j idx_j) axp axp_path axn axn_path
            (idx_j mod (len_j div 2)) f_final actual_chunk"
          by (rule fri_layer_step_evidenceI)
            (use next_value_eq f_final_eq chunk in simp_all)
        have step':
          "fri_layer_step_evidence
            (snd (f_fl ! ?j)) (fst (f_fl ! ?j)) ?len ?idx (2 ^ ?j)
            (fri_sibling_index ?len ?idx) axp axp_path axn axn_path
            (?idx mod (?len div 2)) f_final actual_chunk"
          using step bf_eq idx_j_eq len_j_eq pw_j_eq j_eq by simp
        show ?thesis
          by (rule that[OF _ step'])
            (use auth_t bf_eq idx_j_eq len_j_eq j_eq in simp)
      qed
    qed
  qed
qed

lemma verifier_query_round_after_index_composition_fri_last_step_evidence:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some ((), t) \<in>
      set_dist
        (execute
          (verifier_query_round_after_index_program
            fr f_fl f_final as fl final raw) s)"
    and nonempty: "0 < length fl"
    and raw_layer:
      "\<And>raw'.
        0 < fri_layer_lengths (length fl) (clength * scale) !
          (length fl - 1) \<and>
        fri_layer_indices (length fl) (index (to_nat raw'))
          (clength * scale) ! (length fl - 1) <
        fri_layer_lengths (length fl) (clength * scale) !
          (length fl - 1)"
  obtains actual_chunk axp axp_path axn axn_path where
    "fri_layer_chunk_authenticated
      (snd (fl ! (length fl - 1)))
      (fri_layer_lengths (length fl) (clength * scale) !
        (length fl - 1))
      (fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! (length fl - 1))
      actual_chunk t"
    "fri_layer_step_evidence
      (snd (fl ! (length fl - 1)))
      (fst (fl ! (length fl - 1)))
      (fri_layer_lengths (length fl) (clength * scale) !
        (length fl - 1))
      (fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! (length fl - 1))
      (2 ^ (length fl - 1))
      (fri_sibling_index
        (fri_layer_lengths (length fl) (clength * scale) !
          (length fl - 1))
        (fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! (length fl - 1)))
      axp axp_path axn axn_path
      ((fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! (length fl - 1)) mod
        ((fri_layer_lengths (length fl) (clength * scale) !
          (length fl - 1)) div 2))
      final actual_chunk"
proof -
  show ?thesis
  proof (rule verifier_query_round_after_index_final_checks[OF outcome])
    fix idx fv s1 f_i f_len f_pow s2 c_i c_len c_pow s4
    assume idx_eq: "idx = index (to_nat raw)"
      and comp_fri:
        "Some ((c_i, final, c_len, c_pow), s4) \<in>
          set_dist
            (execute
              (mfold (idx, cp_eval as fv (h ^ idx * shift),
                  clength * scale, 1)
                (receive_query_commits fl)) s2)"
      and t_eq: "t = s4"
    let ?j = "length fl - 1"
    let ?len = "fri_layer_lengths (length fl) (clength * scale) ! ?j"
    let ?idx =
      "fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! ?j"
    have len_pos: "0 < ?len"
      using raw_layer[of raw] by simp
    have idx_bound: "?idx < ?len"
      using raw_layer[of raw] by simp
    show ?thesis
    proof (rule receive_query_commits_last_step_evidence
        [OF comp_fri[unfolded idx_eq] nonempty])
      fix j idx_j x_j len_j pw_j b rt xp xp_path xn xn_path s_j s_suc
      assume j_eq: "j = ?j"
        and bf_eq: "fl ! j = (b, rt)"
        and selected:
          "Some ((c_i, final, c_len, c_pow), s_suc) \<in>
            set_dist
              (execute
                (fri_layer_opening_step (b, rt)
                  (idx_j, x_j, len_j, pw_j)) s_j)"
        and s4_eq: "s4 = s_suc"
        and idx_j_eq:
          "idx_j =
            fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! j"
        and len_j_eq:
          "len_j =
            fri_layer_lengths (length fl) (clength * scale) ! j"
        and pw_j_eq: "pw_j = 1 * 2 ^ j"
      have len_pos_j: "0 < len_j"
        using len_pos len_j_eq j_eq by simp
      have idx_bound_j: "idx_j < len_j"
        using idx_bound idx_j_eq len_j_eq j_eq by simp
      show ?thesis
      proof (rule fri_layer_opening_step_outcome_authenticated
          [OF len_pos_j idx_bound_j selected])
        fix axp axp_path axn axn_path next_value actual_chunk
        assume selected_out:
            "(c_i, final, c_len, c_pow) =
              (idx_j mod (len_j div 2), next_value, len_j div 2,
                pw_j + pw_j)"
          and next_value_eq:
            "next_value =
              fri_fold_value b axp axn
                (fri_fold_denominator ((h ^ idx_j) * shift) pw_j)"
          and chunk:
            "fri_layer_opening_chunk len_j axp axp_path axn axn_path
              actual_chunk"
          and axp_auth:
            "authenticated_opening_in s_suc
              \<lparr>opening_root = rt, opening_length = len_j,
               opening_index = idx_j, opening_value = axp,
               opening_path = axp_path\<rparr>"
          and axn_auth:
            "authenticated_opening_in s_suc
              \<lparr>opening_root = rt, opening_length = len_j,
               opening_index = fri_sibling_index len_j idx_j,
               opening_value = axn, opening_path = axn_path\<rparr>"
        have final_eq: "final = next_value"
          using selected_out by simp
        have auth_t:
          "fri_layer_chunk_authenticated rt len_j idx_j actual_chunk t"
          unfolding t_eq s4_eq
          by (rule fri_layer_chunk_authenticatedI[OF chunk axp_auth axn_auth])
        have step:
          "fri_layer_step_evidence rt b len_j idx_j pw_j
            (fri_sibling_index len_j idx_j) axp axp_path axn axn_path
            (idx_j mod (len_j div 2)) final actual_chunk"
          by (rule fri_layer_step_evidenceI)
            (use next_value_eq final_eq chunk in simp_all)
        have step':
          "fri_layer_step_evidence
            (snd (fl ! ?j)) (fst (fl ! ?j)) ?len ?idx (2 ^ ?j)
            (fri_sibling_index ?len ?idx) axp axp_path axn axn_path
            (?idx mod (?len div 2)) final actual_chunk"
          using step bf_eq idx_j_eq len_j_eq pw_j_eq j_eq by simp
        show ?thesis
          by (rule that[OF _ step'])
            (use auth_t bf_eq idx_j_eq len_j_eq j_eq in simp)
      qed
    qed
  qed
qed

lemma ntimes_verifier_query_rounds_selected_trace_fri_last_step_with_prefix_at:
  fixes query_state final_state :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    and i_bound: "i < rounds"
    and nonempty: "0 < length f_fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length f_fl) (clength * scale) !
          (length f_fl - 1) \<and>
        fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! (length f_fl - 1) <
        fri_layer_lengths (length f_fl) (clength * scale) !
          (length f_fl - 1)"
  obtains raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks actual_chunk axp axp_path axn axn_path where
    "idx = index (to_nat raw)"
    "length prefix_query_idxs = i"
    "length prefix_chunks = i"
    "length suffix_query_idxs = rounds - Suc i"
    "length suffix_chunks = rounds - Suc i"
    "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    "\<And>k. k < i \<Longrightarrow>
      verifier_query_round_chunk (prefix_query_idxs ! k)
        (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    "\<And>k. k < rounds - Suc i \<Longrightarrow>
      verifier_query_round_chunk (suffix_query_idxs ! k)
        (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
    "PTranscript query_state =
      List.concat (prefix_chunks @ chunk # suffix_chunks) @
        PTranscript final_state"
    "fri_layer_chunk_authenticated
      (snd (f_fl ! (length f_fl - 1)))
      (fri_layer_lengths (length f_fl) (clength * scale) !
        (length f_fl - 1))
      (fri_layer_indices (length f_fl) idx (clength * scale) !
        (length f_fl - 1))
      actual_chunk final_state"
    "fri_layer_step_evidence
      (snd (f_fl ! (length f_fl - 1)))
      (fst (f_fl ! (length f_fl - 1)))
      (fri_layer_lengths (length f_fl) (clength * scale) !
        (length f_fl - 1))
      (fri_layer_indices (length f_fl) idx (clength * scale) !
        (length f_fl - 1))
      (2 ^ (length f_fl - 1))
      (fri_sibling_index
        (fri_layer_lengths (length f_fl) (clength * scale) !
          (length f_fl - 1))
        (fri_layer_indices (length f_fl) idx (clength * scale) !
          (length f_fl - 1)))
      axp axp_path axn axn_path
      ((fri_layer_indices (length f_fl) idx (clength * scale) !
          (length f_fl - 1)) mod
        ((fri_layer_lengths (length f_fl) (clength * scale) !
          (length f_fl - 1)) div 2))
      f_final actual_chunk"
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge (PQueryCounter query_state + i)
        (state_after_query_chunks (PState query_state) prefix_chunks i)) =
      Some raw"
proof -
  let ?round = "verifier_query_round_program fr f_fl f_final as fl final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
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
          set_dist
            (execute
              (verifier_query_round_after_index_program fr f_fl f_final as
                fl final raw) s0)"
      by (auto elim!: set_dist_bindE)
    have lookup_s0:
      "fmlookup (HashMap s0)
        (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
      Some raw"
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
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw'"
      have s0_suc: "s0 \<le> s_suc"
        using verifier_query_round_after_index_program_outcome[OF after]
        by simp
      have lookup_suc_raw:
        "fmlookup (HashMap s_suc)
          (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
        Some raw"
        by (rule hash_extension_lookup[OF lookup_s0 s0_suc])
      have raw_eq': "raw = raw'"
        using lookup_suc lookup_suc_raw by simp
      from verifier_query_round_after_index_trace_fri_last_step_evidence
          [OF after nonempty raw_layer]
      obtain actual_chunk axp axp_path axn axn_path where
        auth_suc:
          "fri_layer_chunk_authenticated
            (snd (f_fl ! (length f_fl - 1)))
            (fri_layer_lengths (length f_fl) (clength * scale) !
              (length f_fl - 1))
            (fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! (length f_fl - 1))
            actual_chunk s_suc"
        and step_raw:
          "fri_layer_step_evidence
            (snd (f_fl ! (length f_fl - 1)))
            (fst (f_fl ! (length f_fl - 1)))
            (fri_layer_lengths (length f_fl) (clength * scale) !
              (length f_fl - 1))
            (fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! (length f_fl - 1))
            (2 ^ (length f_fl - 1))
            (fri_sibling_index
              (fri_layer_lengths (length f_fl) (clength * scale) !
                (length f_fl - 1))
              (fri_layer_indices (length f_fl) (index (to_nat raw))
                (clength * scale) ! (length f_fl - 1)))
            axp axp_path axn axn_path
            ((fri_layer_indices (length f_fl) (index (to_nat raw))
                (clength * scale) ! (length f_fl - 1)) mod
              ((fri_layer_lengths (length f_fl) (clength * scale) !
                (length f_fl - 1)) div 2))
            f_final actual_chunk"
        by blast
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
          and suffix_ext: "s_suc \<le> final_state"
          and suffix_rounds:
            "\<And>k. k < rounds - Suc i \<Longrightarrow>
              verifier_query_round_chunk (suffix_query_idxs ! k)
                (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
        have transcript_all:
          "PTranscript query_state =
            List.concat (prefix_chunks @ chunk # suffix_chunks) @
              PTranscript final_state"
          using transcript_prefix transcript_round transcript_suffix by simp
        have auth_final_raw:
          "fri_layer_chunk_authenticated
            (snd (f_fl ! (length f_fl - 1)))
            (fri_layer_lengths (length f_fl) (clength * scale) !
              (length f_fl - 1))
            (fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) !
              (length f_fl - 1))
            actual_chunk final_state"
          by (rule fri_layer_chunk_authenticated_mono[OF auth_suc suffix_ext])
        have auth_final:
          "fri_layer_chunk_authenticated
            (snd (f_fl ! (length f_fl - 1)))
            (fri_layer_lengths (length f_fl) (clength * scale) !
              (length f_fl - 1))
            (fri_layer_indices (length f_fl) idx (clength * scale) !
              (length f_fl - 1))
            actual_chunk final_state"
          using auth_final_raw raw_eq' idx_eq by simp
        have step_idx:
          "fri_layer_step_evidence
            (snd (f_fl ! (length f_fl - 1)))
            (fst (f_fl ! (length f_fl - 1)))
            (fri_layer_lengths (length f_fl) (clength * scale) !
              (length f_fl - 1))
            (fri_layer_indices (length f_fl) idx (clength * scale) !
              (length f_fl - 1))
            (2 ^ (length f_fl - 1))
            (fri_sibling_index
              (fri_layer_lengths (length f_fl) (clength * scale) !
                (length f_fl - 1))
              (fri_layer_indices (length f_fl) idx (clength * scale) !
                (length f_fl - 1)))
            axp axp_path axn axn_path
            ((fri_layer_indices (length f_fl) idx (clength * scale) !
                (length f_fl - 1)) mod
              ((fri_layer_lengths (length f_fl) (clength * scale) !
                (length f_fl - 1)) div 2))
            f_final actual_chunk"
          using step_raw raw_eq' idx_eq by simp
        have lookup_final:
          "fmlookup (HashMap final_state)
            (QueryIndexChallenge (PQueryCounter query_state + i)
              (state_after_query_chunks (PState query_state)
                prefix_chunks i)) =
          Some raw"
        proof -
          have lookup_suc':
            "fmlookup (HashMap s_suc)
              (QueryIndexChallenge (PQueryCounter query_state + i)
                (state_after_query_chunks (PState query_state)
                  prefix_chunks i)) =
            Some raw"
            using lookup_suc_raw state_i counter_i by simp
          show ?thesis
            by (rule hash_extension_lookup[OF lookup_suc' suffix_ext])
        qed
        show ?thesis
          by (rule that[OF _ len_prefix_idxs len_prefix_chunks
                len_suffix_idxs len_suffix_chunks chunk_shape prefix_rounds
                suffix_rounds transcript_all auth_final step_idx
                lookup_final])
            (use idx_eq raw_eq' in simp)
      qed
    qed
  qed
qed

lemma ntimes_verifier_query_rounds_selected_composition_fri_last_step_with_prefix_at:
  fixes query_state final_state :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    and i_bound: "i < rounds"
    and nonempty: "0 < length fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length fl) (clength * scale) !
          (length fl - 1) \<and>
        fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! (length fl - 1) <
        fri_layer_lengths (length fl) (clength * scale) !
          (length fl - 1)"
  obtains raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks actual_chunk axp axp_path axn axn_path where
    "idx = index (to_nat raw)"
    "length prefix_query_idxs = i"
    "length prefix_chunks = i"
    "length suffix_query_idxs = rounds - Suc i"
    "length suffix_chunks = rounds - Suc i"
    "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    "\<And>k. k < i \<Longrightarrow>
      verifier_query_round_chunk (prefix_query_idxs ! k)
        (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    "\<And>k. k < rounds - Suc i \<Longrightarrow>
      verifier_query_round_chunk (suffix_query_idxs ! k)
        (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
    "PTranscript query_state =
      List.concat (prefix_chunks @ chunk # suffix_chunks) @
        PTranscript final_state"
    "fri_layer_chunk_authenticated
      (snd (fl ! (length fl - 1)))
      (fri_layer_lengths (length fl) (clength * scale) !
        (length fl - 1))
      (fri_layer_indices (length fl) idx (clength * scale) !
        (length fl - 1))
      actual_chunk final_state"
    "fri_layer_step_evidence
      (snd (fl ! (length fl - 1)))
      (fst (fl ! (length fl - 1)))
      (fri_layer_lengths (length fl) (clength * scale) !
        (length fl - 1))
      (fri_layer_indices (length fl) idx (clength * scale) !
        (length fl - 1))
      (2 ^ (length fl - 1))
      (fri_sibling_index
        (fri_layer_lengths (length fl) (clength * scale) !
          (length fl - 1))
        (fri_layer_indices (length fl) idx (clength * scale) !
          (length fl - 1)))
      axp axp_path axn axn_path
      ((fri_layer_indices (length fl) idx (clength * scale) !
          (length fl - 1)) mod
        ((fri_layer_lengths (length fl) (clength * scale) !
          (length fl - 1)) div 2))
      final actual_chunk"
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge (PQueryCounter query_state + i)
        (state_after_query_chunks (PState query_state) prefix_chunks i)) =
      Some raw"
proof -
  let ?round = "verifier_query_round_program fr f_fl f_final as fl final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
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
          set_dist
            (execute
              (verifier_query_round_after_index_program fr f_fl f_final as
                fl final raw) s0)"
      by (auto elim!: set_dist_bindE)
    have lookup_s0:
      "fmlookup (HashMap s0)
        (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
      Some raw"
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
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw'"
      have s0_suc: "s0 \<le> s_suc"
        using verifier_query_round_after_index_program_outcome[OF after]
        by simp
      have lookup_suc_raw:
        "fmlookup (HashMap s_suc)
          (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
        Some raw"
        by (rule hash_extension_lookup[OF lookup_s0 s0_suc])
      have raw_eq': "raw = raw'"
        using lookup_suc lookup_suc_raw by simp
      from verifier_query_round_after_index_composition_fri_last_step_evidence
          [OF after nonempty raw_layer]
      obtain actual_chunk axp axp_path axn axn_path where
        auth_suc:
          "fri_layer_chunk_authenticated
            (snd (fl ! (length fl - 1)))
            (fri_layer_lengths (length fl) (clength * scale) !
              (length fl - 1))
            (fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! (length fl - 1))
            actual_chunk s_suc"
        and step_raw:
          "fri_layer_step_evidence
            (snd (fl ! (length fl - 1)))
            (fst (fl ! (length fl - 1)))
            (fri_layer_lengths (length fl) (clength * scale) !
              (length fl - 1))
            (fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! (length fl - 1))
            (2 ^ (length fl - 1))
            (fri_sibling_index
              (fri_layer_lengths (length fl) (clength * scale) !
                (length fl - 1))
              (fri_layer_indices (length fl) (index (to_nat raw))
                (clength * scale) ! (length fl - 1)))
            axp axp_path axn axn_path
            ((fri_layer_indices (length fl) (index (to_nat raw))
                (clength * scale) ! (length fl - 1)) mod
              ((fri_layer_lengths (length fl) (clength * scale) !
                (length fl - 1)) div 2))
            final actual_chunk"
        by blast
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
          and suffix_ext: "s_suc \<le> final_state"
          and suffix_rounds:
            "\<And>k. k < rounds - Suc i \<Longrightarrow>
              verifier_query_round_chunk (suffix_query_idxs ! k)
                (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
        have transcript_all:
          "PTranscript query_state =
            List.concat (prefix_chunks @ chunk # suffix_chunks) @
              PTranscript final_state"
          using transcript_prefix transcript_round transcript_suffix by simp
        have auth_final_raw:
          "fri_layer_chunk_authenticated
            (snd (fl ! (length fl - 1)))
            (fri_layer_lengths (length fl) (clength * scale) !
              (length fl - 1))
            (fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) !
              (length fl - 1))
            actual_chunk final_state"
          by (rule fri_layer_chunk_authenticated_mono[OF auth_suc suffix_ext])
        have auth_final:
          "fri_layer_chunk_authenticated
            (snd (fl ! (length fl - 1)))
            (fri_layer_lengths (length fl) (clength * scale) !
              (length fl - 1))
            (fri_layer_indices (length fl) idx (clength * scale) !
              (length fl - 1))
            actual_chunk final_state"
          using auth_final_raw raw_eq' idx_eq by simp
        have step_idx:
          "fri_layer_step_evidence
            (snd (fl ! (length fl - 1)))
            (fst (fl ! (length fl - 1)))
            (fri_layer_lengths (length fl) (clength * scale) !
              (length fl - 1))
            (fri_layer_indices (length fl) idx (clength * scale) !
              (length fl - 1))
            (2 ^ (length fl - 1))
            (fri_sibling_index
              (fri_layer_lengths (length fl) (clength * scale) !
                (length fl - 1))
              (fri_layer_indices (length fl) idx (clength * scale) !
                (length fl - 1)))
            axp axp_path axn axn_path
            ((fri_layer_indices (length fl) idx (clength * scale) !
                (length fl - 1)) mod
              ((fri_layer_lengths (length fl) (clength * scale) !
                (length fl - 1)) div 2))
            final actual_chunk"
          using step_raw raw_eq' idx_eq by simp
        have lookup_final:
          "fmlookup (HashMap final_state)
            (QueryIndexChallenge (PQueryCounter query_state + i)
              (state_after_query_chunks (PState query_state)
                prefix_chunks i)) =
          Some raw"
        proof -
          have lookup_suc':
            "fmlookup (HashMap s_suc)
              (QueryIndexChallenge (PQueryCounter query_state + i)
                (state_after_query_chunks (PState query_state)
                  prefix_chunks i)) =
            Some raw"
            using lookup_suc_raw state_i counter_i by simp
          show ?thesis
            by (rule hash_extension_lookup[OF lookup_suc' suffix_ext])
        qed
        show ?thesis
          by (rule that[OF _ len_prefix_idxs len_prefix_chunks
                len_suffix_idxs len_suffix_chunks chunk_shape prefix_rounds
                suffix_rounds transcript_all auth_final step_idx
                lookup_final])
            (use idx_eq raw_eq' in simp)
      qed
    qed
  qed
qed

lemma generic_fri_forced_value_eq_from_authenticated_step:
  assumes forced:
    "generic_fri_round_forced_next_value roots challenges query_idxs
      round_layers round_idx layer_idx v"
    and recorded_auth:
    "generic_fri_recorded_layer_chunk_authenticated roots query_idxs
      round_layers final_state round_idx layer_idx"
    and actual_auth:
    "fri_layer_chunk_authenticated (roots ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      actual_chunk final_state"
    and actual_step:
    "fri_layer_step_evidence
      (roots ! layer_idx)
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
      axp axp_path axn axn_path
      (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
      actual_value actual_chunk"
    and no_merkle:
    "\<not> partial_merkle_inconsistency_bad s (Some (result, final_state))"
  shows "v = actual_value"
proof -
  from forced obtain rxp rxp_path rxn rxn_path where recorded_step:
    "fri_layer_step_evidence
      (roots ! layer_idx)
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
      rxp rxp_path rxn rxn_path
      (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
      v
      (round_layers ! round_idx ! layer_idx)"
    unfolding generic_fri_round_forced_next_value_def by blast
  have recorded_chunk:
    "fri_layer_chunk_authenticated (roots ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (round_layers ! round_idx ! layer_idx) final_state"
    using recorded_auth
    unfolding generic_fri_recorded_layer_chunk_authenticated_def .
  have rxp_eq: "rxp = axp"
    by (rule fri_layer_authenticated_base_values_eq_if_no_partial_merkle
        [OF no_merkle recorded_chunk actual_auth])
      (use fri_layer_step_evidenceD(4)[OF recorded_step]
        fri_layer_step_evidenceD(4)[OF actual_step] in simp_all)
  have rxn_eq: "rxn = axn"
    by (rule fri_layer_authenticated_sibling_values_eq_if_no_partial_merkle
        [OF no_merkle recorded_chunk actual_auth])
      (use fri_layer_step_evidenceD(4)[OF recorded_step]
        fri_layer_step_evidenceD(4)[OF actual_step] in simp_all)
  show ?thesis
    using fri_layer_step_evidenceD(3)[OF recorded_step]
      fri_layer_step_evidenceD(3)[OF actual_step]
      rxp_eq rxn_eq
    by simp
qed

lemma generic_fri_final_conflict_false_from_authenticated_step:
  assumes forced:
    "generic_fri_round_forced_next_value roots challenges query_idxs
      round_layers round_idx layer_idx v"
    and recorded_auth:
    "generic_fri_recorded_layer_chunk_authenticated roots query_idxs
      round_layers final_state round_idx layer_idx"
    and actual_auth:
    "fri_layer_chunk_authenticated (roots ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      actual_chunk final_state"
    and actual_step:
    "fri_layer_step_evidence
      (roots ! layer_idx)
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
      axp axp_path axn axn_path
      (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
      final_value actual_chunk"
    and no_merkle:
    "\<not> partial_merkle_inconsistency_bad s (Some (result, final_state))"
    and conflict: "v \<noteq> final_value"
  shows False
  using generic_fri_forced_value_eq_from_authenticated_step
    [OF forced recorded_auth actual_auth actual_step no_merkle]
    conflict
  by simp

lemma generic_fri_selected_final_step_missing_false_from_authenticated_step:
  fixes root challenge final_value :: 'f
    and final_state :: "('f, 'a) protocol_channel_scheme"
  assumes actual_auth:
    "fri_layer_chunk_authenticated root len idx actual_chunk final_state"
    and actual_step:
    "fri_layer_step_evidence root challenge len idx pw sibling_idx
      axp axp_path axn axn_path next_idx final_value actual_chunk"
    and missing:
    "\<And>actual_chunk axp axp_path axn axn_path.
      \<not> (fri_layer_chunk_authenticated root len idx actual_chunk final_state \<and>
        fri_layer_step_evidence root challenge len idx pw sibling_idx
          axp axp_path axn axn_path next_idx final_value actual_chunk)"
  shows False
  using actual_auth actual_step missing by blast

end

end
