theory Soundness_FRI_RO_Actual_Query_Fold_Evidence
  imports Soundness_FRI_RO_Actual_Query_Accepted_Evidence
begin


context soundness
begin

lemma ro_fri_layer_opening_step_outcome_evidence:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some ((next_idx, next_value, next_len, next_pow), t) \<in>
      set_dist
        (execute
          (ro_fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
  obtains xp xp_path xn xn_path chunk where
    "xp = x"
    "next_idx = idx mod (len div 2)"
    "next_len = len div 2"
    "next_pow = pw + pw"
    "fri_layer_step_evidence rt b len idx pw
      (fri_sibling_index len idx) xp xp_path xn xn_path
      next_idx next_value chunk"
    "PTranscript s = chunk @ PTranscript t"
proof -
  from ro_fri_layer_opening_step_outcome_with_lookup_chain[OF outcome]
  obtain xp xp_path xn xn_path folded chunk where
    out_eq:
      "(next_idx, next_value, next_len, next_pow) =
        (idx mod (len div 2), folded, len div 2, pw + pw)"
    and xp_eq: "xp = x"
    and folded_eq:
      "folded = fri_fold_value b xp xn
        (fri_fold_denominator ((h ^ idx) * shift) pw)"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and transcript: "PTranscript s = chunk @ PTranscript t"
    and chain:
      "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    and ext: "s \<le> t"
    and counter: "PQueryCounter t = PQueryCounter s"
    .
  have next_idx_eq: "next_idx = idx mod (len div 2)"
    using out_eq by simp
  have next_value_eq: "next_value = folded"
    using out_eq by simp
  have next_len_eq: "next_len = len div 2"
    using out_eq by simp
  have next_pow_eq: "next_pow = pw + pw"
    using out_eq by simp
  have evidence:
      "fri_layer_step_evidence rt b len idx pw
        (fri_sibling_index len idx) xp xp_path xn xn_path
        next_idx next_value chunk"
    by (rule fri_layer_step_evidenceI)
      (use next_idx_eq next_value_eq folded_eq chunk in simp_all)
  show ?thesis
    by (rule that[OF xp_eq next_idx_eq next_len_eq next_pow_eq evidence transcript])
qed


definition ro_fri_fold_recorded_chain_evidence
  :: "('f \<times> 'f) list \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      'f list list \<Rightarrow> 'f \<Rightarrow> bool"
where
  "ro_fri_fold_recorded_chain_evidence bfs idx x len pw layer_chunks
      out_value \<longleftrightarrow>
    (\<exists>values.
      length values = Suc (length bfs) \<and>
      values ! 0 = x \<and>
      values ! length bfs = out_value \<and>
      (\<forall>j < length bfs.
        \<exists>xp_path xn xn_path.
          fri_layer_step_evidence
            (snd (bfs ! j))
            (fst (bfs ! j))
            (fri_layer_lengths (length bfs) len ! j)
            (fri_layer_indices (length bfs) idx len ! j)
            (pw * 2 ^ j)
            (fri_sibling_index
              (fri_layer_lengths (length bfs) len ! j)
              (fri_layer_indices (length bfs) idx len ! j))
            (values ! j) xp_path xn xn_path
            ((fri_layer_indices (length bfs) idx len ! j) mod
              ((fri_layer_lengths (length bfs) len ! j) div 2))
            (values ! Suc j)
            (layer_chunks ! j)))"


lemma mfold_ro_fri_layer_opening_steps_recorded_chain_evidence_exists:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some ((out_idx, out_value, out_len, out_pow), t) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (map ro_fri_layer_opening_step bfs))
          s)"
  shows
    "\<exists>layer_chunks chunk.
      fri_layers_transcript (length bfs) len layer_chunks chunk \<and>
      PTranscript s = chunk @ PTranscript t \<and>
      ro_fri_fold_recorded_chain_evidence bfs idx x len pw layer_chunks
        out_value"
  using outcome
proof (induction bfs arbitrary: idx x len pw s
    out_idx out_value out_len out_pow t)
  case Nil
  have out_eq:
      "(out_idx, out_value, out_len, out_pow) = (idx, x, len, pw)"
    and t_eq: "t = s"
    using Nil.prems by simp_all
  have layers: "fri_layers_transcript 0 len [] []"
    unfolding fri_layers_transcript_def by simp
  have transcript: "PTranscript s = [] @ PTranscript t"
    using t_eq by simp
  have chain:
      "ro_fri_fold_recorded_chain_evidence [] idx x len pw [] out_value"
    unfolding ro_fri_fold_recorded_chain_evidence_def
    using out_eq
    by (intro exI[of _ "[x]"]) simp
  show ?case
    by (intro exI[of _ "[]"] exI[of _ "[]"])
      (use layers transcript chain in simp)
next
  case (Cons bf bfs)
  obtain b rt where bf_eq: "bf = (b, rt)"
    by (cases bf)
  from Cons.prems
  obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist
          (execute (ro_fri_layer_opening_step bf (idx, x, len, pw)) s)"
    and tail:
      "Some ((out_idx, out_value, out_len, out_pow), t) \<in>
        set_dist
          (execute
            (mfold out1 (map ro_fri_layer_opening_step bfs)) s1)"
    by (auto elim!: set_dist_bindE)
  obtain idx1 x1 len1 pw1 where out1_eq:
      "out1 = (idx1, x1, len1, pw1)"
    by (cases out1)
  have head_tuple:
      "Some ((idx1, x1, len1, pw1), s1) \<in>
        set_dist
          (execute
            (ro_fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
    using head out1_eq bf_eq by simp
  from ro_fri_layer_opening_step_outcome_evidence[OF head_tuple]
  obtain xp xp_path xn xn_path head_chunk where
    xp_eq: "xp = x"
    and idx1_eq: "idx1 = idx mod (len div 2)"
    and len1_eq: "len1 = len div 2"
    and pw1_eq: "pw1 = pw + pw"
    and head_evidence:
      "fri_layer_step_evidence rt b len idx pw
        (fri_sibling_index len idx) xp xp_path xn xn_path
        idx1 x1 head_chunk"
    and head_transcript:
      "PTranscript s = head_chunk @ PTranscript s1"
    .
  from Cons.IH[OF tail[unfolded out1_eq]]
  obtain tail_chunks tail_chunk where
    tail_layers:
      "fri_layers_transcript (length bfs) len1 tail_chunks tail_chunk"
    and tail_transcript:
      "PTranscript s1 = tail_chunk @ PTranscript t"
    and tail_chain:
      "ro_fri_fold_recorded_chain_evidence bfs idx1 x1 len1 pw1
        tail_chunks out_value"
    by blast
  from tail_chain obtain tail_values where
    tail_values_len: "length tail_values = Suc (length bfs)"
    and tail_values_head: "tail_values ! 0 = x1"
    and tail_values_final: "tail_values ! length bfs = out_value"
    and tail_steps:
      "\<forall>j < length bfs.
        \<exists>xp_path xn xn_path.
          fri_layer_step_evidence
            (snd (bfs ! j))
            (fst (bfs ! j))
            (fri_layer_lengths (length bfs) len1 ! j)
            (fri_layer_indices (length bfs) idx1 len1 ! j)
            (pw1 * 2 ^ j)
            (fri_sibling_index
              (fri_layer_lengths (length bfs) len1 ! j)
              (fri_layer_indices (length bfs) idx1 len1 ! j))
            (tail_values ! j) xp_path xn xn_path
            ((fri_layer_indices (length bfs) idx1 len1 ! j) mod
              ((fri_layer_lengths (length bfs) len1 ! j) div 2))
            (tail_values ! Suc j)
            (tail_chunks ! j)"
    unfolding ro_fri_fold_recorded_chain_evidence_def by blast
  let ?layer_chunks = "head_chunk # tail_chunks"
  let ?chunk = "head_chunk @ tail_chunk"
  let ?values = "x # tail_values"
  have layers:
      "fri_layers_transcript (length (bf # bfs)) len ?layer_chunks ?chunk"
    using fri_layer_step_evidenceD(4)[OF head_evidence] tail_layers
    unfolding fri_layers_transcript_def len1_eq
    by auto
  have transcript: "PTranscript s = ?chunk @ PTranscript t"
    using head_transcript tail_transcript by simp
  have values_len: "length ?values = Suc (length (bf # bfs))"
    using tail_values_len by simp
  have values_head: "?values ! 0 = x"
    by simp
  have values_final: "?values ! length (bf # bfs) = out_value"
    using tail_values_final tail_values_len by simp
  have steps:
      "\<forall>j < length (bf # bfs).
        \<exists>xp_path xn xn_path.
          fri_layer_step_evidence
            (snd ((bf # bfs) ! j))
            (fst ((bf # bfs) ! j))
            (fri_layer_lengths (length (bf # bfs)) len ! j)
            (fri_layer_indices (length (bf # bfs)) idx len ! j)
            (pw * 2 ^ j)
            (fri_sibling_index
              (fri_layer_lengths (length (bf # bfs)) len ! j)
              (fri_layer_indices (length (bf # bfs)) idx len ! j))
            (?values ! j) xp_path xn xn_path
            ((fri_layer_indices (length (bf # bfs)) idx len ! j) mod
              ((fri_layer_lengths (length (bf # bfs)) len ! j) div 2))
            (?values ! Suc j)
            (?layer_chunks ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length (bf # bfs)"
    show
      "\<exists>xp_path xn xn_path.
        fri_layer_step_evidence
          (snd ((bf # bfs) ! j))
          (fst ((bf # bfs) ! j))
          (fri_layer_lengths (length (bf # bfs)) len ! j)
          (fri_layer_indices (length (bf # bfs)) idx len ! j)
          (pw * 2 ^ j)
          (fri_sibling_index
            (fri_layer_lengths (length (bf # bfs)) len ! j)
            (fri_layer_indices (length (bf # bfs)) idx len ! j))
          (?values ! j) xp_path xn xn_path
          ((fri_layer_indices (length (bf # bfs)) idx len ! j) mod
            ((fri_layer_lengths (length (bf # bfs)) len ! j) div 2))
          (?values ! Suc j)
          (?layer_chunks ! j)"
    proof (cases j)
      case 0
      show ?thesis
        using head_evidence xp_eq tail_values_head bf_eq idx1_eq
        by (auto simp: "0")
    next
      case (Suc k)
      then have k_bound: "k < length bfs"
        using j_bound by simp
      from tail_steps[rule_format, OF k_bound]
      obtain k_xp_path k_xn k_xn_path where k_step:
        "fri_layer_step_evidence
          (snd (bfs ! k))
          (fst (bfs ! k))
          (fri_layer_lengths (length bfs) len1 ! k)
          (fri_layer_indices (length bfs) idx1 len1 ! k)
          (pw1 * 2 ^ k)
          (fri_sibling_index
            (fri_layer_lengths (length bfs) len1 ! k)
            (fri_layer_indices (length bfs) idx1 len1 ! k))
          (tail_values ! k) k_xp_path k_xn k_xn_path
          ((fri_layer_indices (length bfs) idx1 len1 ! k) mod
            ((fri_layer_lengths (length bfs) len1 ! k) div 2))
          (tail_values ! Suc k)
          (tail_chunks ! k)"
        by blast
      have pw_step: "pw1 * 2 ^ k = pw * 2 ^ Suc k"
        using pw1_eq
        by (simp add: add_mult_distrib distrib_left mult.assoc mult_2)
      show ?thesis
        using k_step Suc idx1_eq len1_eq pw_step
        by auto
    qed
  qed
  have chain:
      "ro_fri_fold_recorded_chain_evidence (bf # bfs) idx x len pw
        ?layer_chunks out_value"
    unfolding ro_fri_fold_recorded_chain_evidence_def
    by (intro exI[of _ ?values])
      (use values_len values_head values_final steps in simp)
  show ?case
    by (intro exI[of _ ?layer_chunks] exI[of _ ?chunk])
      (use layers transcript chain in blast)
qed


lemma mfold_ro_fri_layer_opening_steps_recorded_chain_evidence:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some ((out_idx, out_value, out_len, out_pow), t) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (map ro_fri_layer_opening_step bfs))
          s)"
  obtains layer_chunks chunk where
    "fri_layers_transcript (length bfs) len layer_chunks chunk"
    "PTranscript s = chunk @ PTranscript t"
    "ro_fri_fold_recorded_chain_evidence bfs idx x len pw layer_chunks
      out_value"
  using
    mfold_ro_fri_layer_opening_steps_recorded_chain_evidence_exists[OF outcome]
  by blast
lemma ro_recorded_query_fri_accepted_evidence_recorded_chains:
  assumes accepted:
    "ro_recorded_query_fri_accepted_evidence
      fr f_fl f_final as fl final raw
      trace_layers composition_layers final_state"
  obtains fv where
    "ro_fri_fold_recorded_chain_evidence
      f_fl (index (to_nat raw)) (hd fv) (clength * scale) 1
      trace_layers f_final"
    "ro_fri_fold_recorded_chain_evidence
      fl (index (to_nat raw))
      (cp_eval as fv (h ^ index (to_nat raw) * shift))
      (clength * scale) 1 composition_layers final"
proof -
  from accepted obtain round_final fv s1 s2 trace_chunk
      f_i f_len f_pow composition_chunk c_i c_len c_pow where
    trace_shape:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layers trace_chunk"
    and trace_transcript:
      "PTranscript s1 = trace_chunk @ PTranscript s2"
    and composition_shape:
      "fri_layers_transcript (length fl) (clength * scale)
        composition_layers composition_chunk"
    and composition_transcript:
      "PTranscript s2 = composition_chunk @ PTranscript round_final"
    and trace_fri:
      "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw), hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl))
            s1)"
    and composition_fri:
      "Some ((c_i, final, c_len, c_pow), round_final) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw),
                cp_eval as fv (h ^ index (to_nat raw) * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl))
            s2)"
    unfolding ro_recorded_query_fri_accepted_evidence_def
    by blast
  from mfold_ro_fri_layer_opening_steps_recorded_chain_evidence[
      OF trace_fri[unfolded ro_receive_query_commits_def]]
  obtain actual_trace_layers actual_trace_chunk where
    actual_trace_shape:
      "fri_layers_transcript (length f_fl) (clength * scale)
        actual_trace_layers actual_trace_chunk"
    and actual_trace_transcript:
      "PTranscript s1 = actual_trace_chunk @ PTranscript s2"
    and actual_trace_chain:
      "ro_fri_fold_recorded_chain_evidence
        f_fl (index (to_nat raw)) (hd fv) (clength * scale) 1
        actual_trace_layers f_final"
    .
  have trace_chunk_eq: "actual_trace_chunk = trace_chunk"
    using actual_trace_transcript trace_transcript by simp
  have actual_trace_shape_recorded:
      "fri_layers_transcript (length f_fl) (clength * scale)
        actual_trace_layers trace_chunk"
    using actual_trace_shape trace_chunk_eq by simp
  have trace_layers_eq: "actual_trace_layers = trace_layers"
    by (rule fri_layers_transcript_unique[
          OF actual_trace_shape_recorded trace_shape])
  have trace_chain:
      "ro_fri_fold_recorded_chain_evidence
        f_fl (index (to_nat raw)) (hd fv) (clength * scale) 1
        trace_layers f_final"
    using actual_trace_chain trace_layers_eq by simp
  from mfold_ro_fri_layer_opening_steps_recorded_chain_evidence[
      OF composition_fri[unfolded ro_receive_query_commits_def]]
  obtain actual_composition_layers actual_composition_chunk where
    actual_composition_shape:
      "fri_layers_transcript (length fl) (clength * scale)
        actual_composition_layers actual_composition_chunk"
    and actual_composition_transcript:
      "PTranscript s2 =
        actual_composition_chunk @ PTranscript round_final"
    and actual_composition_chain:
      "ro_fri_fold_recorded_chain_evidence
        fl (index (to_nat raw))
        (cp_eval as fv (h ^ index (to_nat raw) * shift))
        (clength * scale) 1 actual_composition_layers final"
    .
  have composition_chunk_eq:
      "actual_composition_chunk = composition_chunk"
    using actual_composition_transcript composition_transcript by simp
  have actual_composition_shape_recorded:
      "fri_layers_transcript (length fl) (clength * scale)
        actual_composition_layers composition_chunk"
    using actual_composition_shape composition_chunk_eq by simp
  have composition_layers_eq:
      "actual_composition_layers = composition_layers"
    by (rule fri_layers_transcript_unique[
          OF actual_composition_shape_recorded composition_shape])
  have composition_chain:
      "ro_fri_fold_recorded_chain_evidence
        fl (index (to_nat raw))
        (cp_eval as fv (h ^ index (to_nat raw) * shift))
        (clength * scale) 1 composition_layers final"
    using actual_composition_chain composition_layers_eq by simp
  show ?thesis
    by (rule that[OF trace_chain composition_chain])
qed
end
end
