(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Bridge.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Bridge
  imports
    Staged_Security_Experiment_Composition_Query_Residual
    Soundness_Query_Opening_Consistency
    Soundness_Bound_Table_Partial_Openings
    Soundness_Aligned_Partial_Query_Prefix
begin

text \<open>
  Narrow bridge from the composition-drift query residual to the
  candidate-opening query target.  This is kept separate from the residual
  split theory because the surrounding staged soundness layers are already
  heavy to consolidate.
\<close>

context soundness
begin

lemma partial_query_openings_consistent_synthetic:
  assumes idx_sample: "idx \<in> query_sample_space"
  obtains trace_openings composition_openings where
    "partial_query_openings_consistent trace_openings composition_openings
      as idx"
proof -
  let ?trace_openings =
    "map (\<lambda>j.
      \<lparr> opening_root = 0,
        opening_length = scale * clength,
        opening_index = j,
        opening_value = 0,
        opening_path = [] \<rparr>) (powers_scaled idx)"
  let ?composition_openings =
    "[\<lparr> opening_root = 0,
        opening_length = scale * clength,
        opening_index = idx,
        opening_value =
          cp_eval as (map opening_value ?trace_openings) (h ^ idx * shift),
        opening_path = [] \<rparr>,
      \<lparr> opening_root = 0,
        opening_length = scale * clength,
        opening_index = fri_sibling_index (scale * clength) idx,
        opening_value = 0,
        opening_path = [] \<rparr>]"
  have trace_indices:
    "map opening_index ?trace_openings = powers_scaled idx"
    by (simp add: o_def)
  have comp_indices:
    "map opening_index ?composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    by simp
  have consistent:
    "partial_query_openings_consistent ?trace_openings
      ?composition_openings as idx"
    by (rule partial_query_openings_consistentI
        [OF idx_sample trace_indices comp_indices])
      simp
  show ?thesis
    by (rule that[OF consistent])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hitI_from_prefix_receive_synthetic:
  assumes i_bound: "i < rounds"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
  shows
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  obtain trace_openings composition_openings where consistent:
    "partial_query_openings_consistent trace_openings composition_openings
      (staged_alphas data) (index (to_nat raw))"
  proof (rule partial_query_openings_consistent_synthetic)
    show "index (to_nat raw) \<in> query_sample_space"
      using index_less_query_sample_space
      unfolding query_sample_space_def by simp
  qed
  have component:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit
      A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      (staged_alphas data) i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hitI_from_prefix_receive
        [OF i_bound builder prefix_receive consistent])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hitI
      [OF component])
qed

definition checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
  :: "('f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool)"
where
  "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
      A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        staged_composition_fri_roots data \<noteq> [] \<and>
        (\<exists>i trace_openings composition_openings.
          partial_authenticated_table (staged_trace_root data)
            (scale * clength) trace_openings final_state \<and>
          partial_authenticated_table (hd (staged_composition_fri_roots data))
            (scale * clength) composition_openings final_state \<and>
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
            ((replicate rounds []) [i := trace_openings])
            ((replicate rounds []) [i := composition_openings])
            (staged_alphas data) i
            (Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state))))"

lemma checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hitI:
  assumes comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and comp_auth:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings final_state"
    and component:
      "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        (staged_alphas data) i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  have witness:
    "\<exists>j trace_openings' composition_openings'.
      partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings' final_state \<and>
      partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings' final_state \<and>
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
        ((replicate rounds []) [j := trace_openings'])
        ((replicate rounds []) [j := composition_openings'])
        (staged_alphas data) j
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    by (intro exI[of _ i] exI[of _ trace_openings]
        exI[of _ composition_openings] conjI)
      (use trace_auth comp_auth component in simp_all)
  show ?thesis
    unfolding
      checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_def
    using comp_nonempty witness by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_imp_compact:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
      A out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit
      A out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix alpha_prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed, auto split: prod.splits)
  from hit[unfolded out_eq
      checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_def]
  obtain i trace_openings composition_openings where component:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      (staged_alphas data) i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by auto
  show ?thesis
    unfolding out_eq
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hitI
        [OF component])
qed

lemma checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_le_compact:
  "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
        A)
      adversary_initial_state \<le>
    wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit
        A)
      adversary_initial_state"
  by (rule wp_event_mono)
    (rule
      checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_imp_compact)

lemma checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hitI_from_current_openings:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    and i_bound: "i < rounds"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and final_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and comp_auth:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings final_state"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  from checked_staged_transcript_program_query_prefix_receive_final_lookup_support
      [OF wf controlled i_bound builder verifier final_lookup]
  obtain prefix prefix_state raw_state where prefix_receive:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    by blast
  have component:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      (staged_alphas data) i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hitI_from_prefix_receive
        [OF i_bound builder prefix_receive consistent])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hitI
        [OF comp_nonempty trace_auth comp_auth component])
qed

definition checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
  :: "('f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool)"
where
  "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
      A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        staged_composition_fri_roots data \<noteq> [] \<and>
        (\<exists>i trace_openings composition_openings.
          partial_authenticated_table (staged_trace_root data)
            (scale * clength) trace_openings final_state \<and>
          partial_authenticated_table (hd (staged_composition_fri_roots data))
            (scale * clength) composition_openings final_state \<and>
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
            A
            ((replicate rounds []) [i := trace_openings])
            ((replicate rounds []) [i := composition_openings])
            i
            (Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state))))"

lemma checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefixI:
  assumes comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and comp_auth:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings final_state"
    and component:
      "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
        A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  have witness:
    "\<exists>j trace_openings' composition_openings'.
      partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings' final_state \<and>
      partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings' final_state \<and>
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
        A
        ((replicate rounds []) [j := trace_openings'])
        ((replicate rounds []) [j := composition_openings'])
        j
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    by (intro exI[of _ i] exI[of _ trace_openings]
        exI[of _ composition_openings] conjI)
      (use trace_auth comp_auth component in simp_all)
  show ?thesis
    unfolding
      checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix_def
    using comp_nonempty witness by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefixI_from_current_openings:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    and i_bound: "i < rounds"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and final_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and comp_auth:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings final_state"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  from checked_staged_transcript_program_query_prefix_receive_final_lookup_support_with_alphas
      [OF wf controlled i_bound builder verifier final_lookup]
  obtain prefix prefix_state raw_state where prefix_receive:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    by blast
  have component:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefixI_from_prefix_receive
        [OF i_bound builder prefix_receive alphas_eq consistent])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefixI
        [OF comp_nonempty trace_auth comp_auth component])
qed

lemma selected_query_chunks_match_verifier_lengths:
  assumes i_bound: "i < rounds"
    and len_prefix_chunks: "length prefix_chunks = i"
    and len_suffix_chunks: "length suffix_chunks = rounds - Suc i"
    and chunk_shape:
      "verifier_query_round_chunk idx trace_roots composition_roots chunk"
    and prefix_rounds:
      "\<And>j. j < i \<Longrightarrow>
        verifier_query_round_chunk (prefix_query_idxs ! j)
          trace_roots composition_roots (prefix_chunks ! j)"
    and suffix_rounds:
      "\<And>j. j < rounds - Suc i \<Longrightarrow>
        verifier_query_round_chunk (suffix_query_idxs ! j)
          trace_roots composition_roots (suffix_chunks ! j)"
  shows
    "length (prefix_chunks @ chunk # suffix_chunks) = rounds"
    "\<And>j. j < rounds \<Longrightarrow>
      length ((prefix_chunks @ chunk # suffix_chunks) ! j) =
        verifier_query_round_transcript_length (query_idxs ! j)
          trace_roots composition_roots"
proof -
  show "length (prefix_chunks @ chunk # suffix_chunks) = rounds"
    using len_prefix_chunks len_suffix_chunks i_bound by simp
next
  fix j
  assume j_bound: "j < rounds"
  let ?chunks = "prefix_chunks @ chunk # suffix_chunks"
  show
    "length (?chunks ! j) =
      verifier_query_round_transcript_length (query_idxs ! j)
        trace_roots composition_roots"
  proof (cases "j < i")
    case True
    have nth_eq: "?chunks ! j = prefix_chunks ! j"
      using True len_prefix_chunks by (simp add: nth_append)
    have
      "length (prefix_chunks ! j) =
        verifier_query_round_transcript_length
          (prefix_query_idxs ! j) trace_roots composition_roots"
      by (rule verifier_query_round_chunk_length[OF prefix_rounds[OF True]])
    then show ?thesis
      using nth_eq
      by (simp add: verifier_query_round_transcript_length_index_irrelevant)
  next
    case False
    note not_lt = False
    show ?thesis
    proof (cases "j = i")
      case True
      have nth_eq: "?chunks ! j = chunk"
        using True len_prefix_chunks by (simp add: nth_append)
      have
        "length chunk =
          verifier_query_round_transcript_length idx trace_roots
            composition_roots"
        by (rule verifier_query_round_chunk_length[OF chunk_shape])
      then show ?thesis
        using nth_eq
        by (simp add: verifier_query_round_transcript_length_index_irrelevant)
    next
      case False
      note not_eq = False
      let ?k = "j - Suc i"
      have ge: "Suc i \<le> j"
        using not_lt not_eq by linarith
      have k_bound: "?k < rounds - Suc i"
        using ge j_bound by linarith
      have nth_eq: "?chunks ! j = suffix_chunks ! ?k"
        using ge len_prefix_chunks by (simp add: nth_append)
      have
        "length (suffix_chunks ! ?k) =
          verifier_query_round_transcript_length
            (suffix_query_idxs ! ?k) trace_roots composition_roots"
        by (rule verifier_query_round_chunk_length
            [OF suffix_rounds[OF k_bound]])
      then show ?thesis
        using nth_eq
        by (simp add: verifier_query_round_transcript_length_index_irrelevant)
    qed
  qed
qed

lemma selected_query_chunks_eq_staged:
  assumes builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and query_idxs_len: "length query_idxs = rounds"
    and chunks_len: "length query_chunks = rounds"
    and concat_eq:
      "List.concat query_chunks @ trailing =
        List.concat (staged_query_chunks data)"
    and parser_chunk_len:
      "\<And>j. j < rounds \<Longrightarrow>
        length (query_chunks ! j) =
          verifier_query_round_transcript_length (query_idxs ! j)
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)"
  shows "query_chunks = staged_query_chunks data \<and> trailing = []"
proof -
  from checked_staged_transcript_program_query_chunks_match_verifier_lengths
      [OF builder]
  obtain staged_query_idxs where staged_match:
    "staged_query_chunks_match_verifier_lengths data staged_query_idxs"
    by blast
  have staged_match_query_idxs:
    "staged_query_chunks_match_verifier_lengths data query_idxs"
    by (rule staged_query_chunks_match_verifier_lengths_transfer
        [OF staged_match query_idxs_len])
  show ?thesis
    by (rule query_chunks_eq_staged_if_matching_lengths
        [OF chunks_len concat_eq parser_chunk_len
          staged_match_query_idxs])
qed

lemma selected_query_prefix_state_eq_staged:
  assumes len_prefix_chunks: "length prefix_chunks = i"
    and chunks_eq:
      "prefix_chunks @ chunk # suffix_chunks = staged_query_chunks data"
    and query_state_hash: "PState query_state = staged_query_start_hash data"
  shows
    "state_after_query_chunks (PState query_state) prefix_chunks i =
      state_after_query_chunks
        (staged_query_start_hash data) (staged_query_chunks data) i"
proof -
  have
    "state_after_query_chunks (staged_query_start_hash data)
      (prefix_chunks @ chunk # suffix_chunks) i =
     state_after_query_chunks (staged_query_start_hash data)
      prefix_chunks i"
    by (rule state_after_query_chunks_append_prefix[OF len_prefix_chunks])
  then show ?thesis
    using chunks_eq query_state_hash by simp
qed

definition checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit
  :: "('f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool)"
where
  "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit
      A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (let s =
          verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)
         in \<exists>i trace_openings composition_openings.
          (trace_openings, composition_openings) \<in>
            query_header_supported_partial_opening_witnesses s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              (staged_alphas data)
              (staged_degree data)
              (staged_composition_fri_roots data)
              (staged_composition_final data) \<and>
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
            ((replicate rounds []) [i := trace_openings])
            ((replicate rounds []) [i := composition_openings])
            (staged_alphas data) i
            (Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state))))"

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hitI:
  assumes witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
    and component:
      "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        (staged_alphas data) i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  have ex:
    "\<exists>j trace_openings' composition_openings'.
      (trace_openings', composition_openings') \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<and>
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
        ((replicate rounds []) [j := trace_openings'])
        ((replicate rounds []) [j := composition_openings'])
        (staged_alphas data) j
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    by (intro exI[of _ i] exI[of _ trace_openings]
        exI[of _ composition_openings] conjI)
      (use witness component in simp_all)
  show ?thesis
    unfolding
      checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_def
      Let_def
    using ex by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_imp_compact:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit
      A out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit
      A out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_def
    by simp
next
  case (Some packed)
  then obtain alpha_prefix alpha_prefix_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state)"
    by (cases packed, auto split: prod.splits)
  from hit[unfolded out_eq
      checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_def
      Let_def]
  obtain i trace_openings composition_openings where component:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      (staged_alphas data) i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by auto
  show ?thesis
    unfolding out_eq
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hitI
        [OF component])
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hitE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains i trace_openings composition_openings where
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit
      A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      (staged_alphas data) i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  from hit[unfolded
      checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_def
      Let_def]
  obtain i trace_openings composition_openings where witness:
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    and component:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit
      A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      (staged_alphas data) i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by auto
  show ?thesis
    by (rule that[OF witness component])
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_le_compact:
  "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit
        A)
      adversary_initial_state \<le>
    wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit
        A)
      adversary_initial_state"
  by (rule wp_event_mono)
    (rule
      checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_imp_compact)

definition checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
  :: "('f staged_adversary \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool)"
where
  "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
      A out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (let s =
          verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)
         in \<exists>i trace_openings composition_openings.
          (trace_openings, composition_openings) \<in>
            query_header_supported_partial_opening_witnesses s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              (staged_alphas data)
              (staged_degree data)
              (staged_composition_fri_roots data)
              (staged_composition_final data) \<and>
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
            A
            ((replicate rounds []) [i := trace_openings])
            ((replicate rounds []) [i := composition_openings])
            i
            (Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state))))"

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefixI:
  assumes witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
    and component:
      "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  have ex:
    "\<exists>j trace_openings' composition_openings'.
      (trace_openings', composition_openings') \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<and>
      checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix A
        ((replicate rounds []) [j := trace_openings'])
        ((replicate rounds []) [j := composition_openings'])
        j
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
    by (intro exI[of _ i] exI[of _ trace_openings]
        exI[of _ composition_openings] conjI)
      (use witness component in simp_all)
  show ?thesis
    unfolding
      checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_def
      Let_def
    using ex by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefixE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains i trace_openings composition_openings where
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  from hit[unfolded
      checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_def
      Let_def]
  obtain i trace_openings composition_openings where witness:
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    and component:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by auto
  show ?thesis
    by (rule that[OF witness component])
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_query_prefixE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains i trace_openings composition_openings query_prefix query_prefix_state
      raw raw_state where
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    "i < rounds"
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((query_prefix, query_prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i)
      (Some (((query_prefix, query_prefix_state), raw), raw_state))"
proof -
  from checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefixE
      [OF hit]
  obtain i trace_openings composition_openings where witness:
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    and component:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by blast
  from checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefixE
      [OF component]
  obtain query_prefix query_prefix_state raw raw_state where
    i_bound: "i < rounds"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((query_prefix, query_prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i)
        (Some (((query_prefix, query_prefix_state), raw), raw_state))"
    by blast
  show ?thesis
    by (rule that[OF witness i_bound builder prefix_receive target_hit])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_header_authenticated_candidate_opening_query_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit
      A
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_supported_openingsE
        [OF wf controlled support hit])
    fix s trace_table i raw trace_openings composition_openings
    assume s_def: "s = ?s"
      and i_bound: "i < rounds"
      and final_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
        Some raw"
      and witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
      and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
    have data_support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
          [OF support])
    from checked_staged_security_experiment_with_data_state_outcomeE
        [OF data_support]
    obtain builder verifier where
      builder:
        "Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state)"
      and verifier:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
      by blast
    from checked_staged_transcript_program_query_prefix_receive_final_lookup_support
        [OF wf controlled i_bound builder verifier final_lookup]
    obtain query_prefix query_prefix_state raw_state where prefix_receive:
      "Some (((query_prefix, query_prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
      by blast
    have component:
      "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit
        A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        (staged_alphas data) i
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hitI_from_prefix_receive
          [OF i_bound builder prefix_receive consistent])
    show ?thesis
      by (rule
          checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hitI
          [OF _ component])
        (use witness s_def in simp)
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_header_authenticated_candidate_opening_query_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit
        A)
      adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        out"
  show
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit
      A out"
  proof (cases out)
    case None
    then show ?thesis
      using hit
      unfolding
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      by simp
  next
    case (Some packed)
    then obtain prefix prefix_state data attacker_state result final_state
      where out_eq:
        "out =
          Some (((((prefix, prefix_state), data), attacker_state), result),
            final_state)"
      by (cases packed, auto split: prod.splits)
    show ?thesis
      unfolding out_eq
      by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_header_authenticated_candidate_opening_query_hit_on_support
          [OF wf controlled])
        (use support hit out_eq in simp_all)
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_header_authenticated_candidate_opening_query_hit_from_prefix_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
      A
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_supported_openingsE
        [OF wf controlled support hit])
    fix s trace_table i raw trace_openings composition_openings
    assume s_def: "s = ?s"
      and i_bound: "i < rounds"
      and final_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
        Some raw"
      and witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
      and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
    have data_support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
          [OF support])
    from checked_staged_security_experiment_with_data_state_outcomeE
        [OF data_support]
    obtain builder verifier where
      builder:
        "Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state)"
      and verifier:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
      by blast
    from checked_staged_transcript_program_query_prefix_receive_final_lookup_support_with_alphas
        [OF wf controlled i_bound builder verifier final_lookup]
    obtain query_prefix query_prefix_state raw_state where prefix_receive:
      "Some (((query_prefix, query_prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
      and alphas_eq: "sqp_alphas query_prefix = staged_alphas data"
      by blast
    have component:
      "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
        A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefixI_from_prefix_receive
          [OF i_bound builder prefix_receive alphas_eq consistent])
    show ?thesis
      by (rule
          checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefixI
          [OF _ component])
        (use witness s_def in simp)
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_header_authenticated_candidate_opening_query_hit_from_prefix:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
        A)
      adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        out"
  show
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
      A out"
  proof (cases out)
    case None
    then show ?thesis
      using hit
      unfolding
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      by simp
  next
    case (Some packed)
    then obtain prefix prefix_state data attacker_state result final_state
      where out_eq:
        "out =
          Some (((((prefix, prefix_state), data), attacker_state), result),
            final_state)"
      by (cases packed, auto split: prod.splits)
    show ?thesis
      unfolding out_eq
      by (rule
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_header_authenticated_candidate_opening_query_hit_from_prefix_on_support
          [OF wf controlled])
        (use support hit out_eq in simp_all)
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_header_authenticated:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and header_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit
          A)
        adversary_initial_state \<le> (Q::prob)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> Q"
  by (rule order.trans
      [OF
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_header_authenticated_candidate_opening_query_hit
        header_bound])
    (use wf controlled in simp_all)

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_header_authenticated_from_prefix:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and header_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
          A)
        adversary_initial_state \<le> (Q::prob)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> Q"
  by (rule order.trans
      [OF
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_header_authenticated_candidate_opening_query_hit_from_prefix
        header_bound])
    (use wf controlled in simp_all)

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_header_authenticated_and_without_query:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and header_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit
          A)
        adversary_initial_state \<le> (Q::prob)"
    and without_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
        adversary_initial_state \<le> (W::prob)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> Q + W"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_query_and_without_query)
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> Q"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_header_authenticated
        [OF wf controlled header_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le> W"
    by (rule without_bound)
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_alpha_bad_trace_openingsE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  obtains s trace_table witness_out query_idxs trace_openings
      witness_as witness_dg witness_composition_fri_roots witness_final
      witness_rest where
    "s = verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
    "witness_out \<in> set_dist (execute verify_monad s)"
    "accepted_with_partial_trace_openings s witness_out
      (staged_trace_root data) query_idxs trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "verifier_header_transcript s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      witness_as witness_dg witness_composition_fri_roots witness_final
      witness_rest"
    "witness_as = staged_alphas data"
    "staged_alphas data \<in> composition_trace_bad_alpha_space trace_table"
    "\<not> staged_alphas data \<in>
      alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space (fst prefix)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    by blast
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_supportedE
        [OF wf controlled support hit])
    fix s trace_table
    assume s_def:
        "s = verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      and trace_candidate:
        "trace_table \<in>
          alpha_header_supported_partial_trace_table_candidates s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)"
      and trace_bad:
        "staged_alphas data \<in> composition_trace_bad_alpha_space trace_table"
      and not_prefix:
        "\<not> staged_alphas data \<in>
          alpha_prefix_union_bad_sets prefix_state
            composition_trace_bad_alpha_space (fst prefix)"
    show ?thesis
    proof (rule alpha_header_supported_partial_trace_table_candidatesE
        [OF trace_candidate])
      fix witness_out query_idxs trace_openings witness_as witness_dg
          witness_composition_fri_roots witness_final witness_rest
      assume witness_out:
          "witness_out \<in> set_dist (execute verify_monad s)"
        and partial:
          "accepted_with_partial_trace_openings s witness_out
            (staged_trace_root data) query_idxs trace_openings"
        and partial_candidate:
          "partial_trace_table_candidate trace_table trace_openings"
        and header:
          "verifier_header_transcript s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            witness_as witness_dg witness_composition_fri_roots
            witness_final witness_rest"
      have staged_header_s:
        "verifier_header_transcript s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)
          (List.concat (staged_query_chunks data))"
        using staged_header by (simp add: s_def[symmetric])
      have as_eq: "witness_as = staged_alphas data"
        using verifier_header_transcript_unique[OF staged_header_s header]
        by simp
      show ?thesis
        by (rule that[OF s_def witness_out partial partial_candidate
              header as_eq trace_bad not_prefix])
    qed
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_table_witnessE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  obtains s trace_table composition_table query_idxs f bound_trace_openings
      bound_composition_openings where
    "s = verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
    "composition_bad_context s (Some (result, final_state)) trace_table
      composition_table (staged_alphas data) query_idxs f"
    "common_denominator_degree_bounds f (staged_alphas data)"
    "random_combination_common_denominator_hides_violations f
      (staged_alphas data)"
    "partial_trace_table_candidate trace_table bound_trace_openings"
    "partial_composition_table_candidate composition_table
      bound_composition_openings"
    "trace_table_low_degree trace_table"
    "composition_table_low_degree maxDegree composition_table"
    "all_queries_consistent trace_table composition_table
      (staged_alphas data)"
    "\<not> staged_alphas data \<in>
      alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space (fst prefix)"
proof -
  from checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_supportedE
      [OF wf controlled support hit]
  obtain s trace_table where
    s_def:
      "s = verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    and random_bad:
      "composition_randomization_bad s (Some (result, final_state))"
    and not_prefix:
      "\<not> staged_alphas data \<in>
        alpha_prefix_union_bad_sets prefix_state
          composition_trace_bad_alpha_space (fst prefix)"
    by blast
  from random_bad
  obtain trace_table' composition_table as query_idxs f where bad_context:
      "composition_bad_context s (Some (result, final_state)) trace_table'
        composition_table as query_idxs f"
    and bounds: "common_denominator_degree_bounds f as"
    and hides:
      "random_combination_common_denominator_hides_violations f as"
    unfolding composition_randomization_bad_def by blast
  have bound_as:
    "accepted_with_bound_tables s (Some (result, final_state)) trace_table'
      composition_table as query_idxs"
    using bad_context unfolding composition_bad_context_def by blast
  from bound_as obtain fr f_fri_roots f_final dg composition_fri_roots
      final rest where header_as:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding accepted_with_bound_tables_def by blast
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    by blast
  have staged_header:
    "verifier_header_transcript s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    unfolding s_def
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  have as_eq: "as = staged_alphas data"
    using verifier_header_transcript_unique[OF header_as staged_header]
    by simp
  have bad_context_staged:
    "composition_bad_context s (Some (result, final_state)) trace_table'
      composition_table (staged_alphas data) query_idxs f"
    using bad_context as_eq by simp
  have bounds_staged:
    "common_denominator_degree_bounds f (staged_alphas data)"
    using bounds as_eq by simp
  have hides_staged:
    "random_combination_common_denominator_hides_violations f
      (staged_alphas data)"
    using hides as_eq by simp
  have bound:
    "accepted_with_bound_tables s (Some (result, final_state)) trace_table'
      composition_table (staged_alphas data) query_idxs"
    using bad_context_staged unfolding composition_bad_context_def by blast
  from accepted_with_bound_tables_partial_opening_witnesses_Some[OF bound]
  obtain fr f_fri_roots f_final dg composition_fri_roots final rest
      bound_trace_openings bound_composition_openings where
    trace_candidate:
      "partial_trace_table_candidate trace_table' bound_trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        bound_composition_openings"
    by blast
  have trace_low: "trace_table_low_degree trace_table'"
  proof -
    have deg_f: "degree f < clength"
      and trace_table_eq: "trace_table' = map (poly f) eval_domain"
      using bad_context_staged unfolding composition_bad_context_def by blast+
    show ?thesis
      unfolding trace_table_low_degree_def
      using deg_f trace_table_eq by blast
  qed
  have comp_low:
    "composition_table_low_degree maxDegree composition_table"
    using bad_context_staged unfolding composition_bad_context_def by blast
  have all_queries:
    "all_queries_consistent trace_table' composition_table
      (staged_alphas data)"
    using bad_context_staged unfolding composition_bad_context_def by blast
  show ?thesis
    by (rule that[OF s_def bad_context_staged bounds_staged hides_staged
          trace_candidate comp_candidate trace_low comp_low all_queries
          not_prefix])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_aligned_openingsE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  obtains s trace_table composition_table query_idxs f i raw
      header_trace_openings header_composition_openings
      bound_trace_openings bound_composition_openings where
    "s = verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
    "composition_bad_context s (Some (result, final_state)) trace_table
      composition_table (staged_alphas data) query_idxs f"
    "i < rounds"
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some raw"
    "index (to_nat raw) = query_idxs ! i"
    "(header_trace_openings, header_composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    "partial_query_openings_consistent header_trace_openings
      header_composition_openings (staged_alphas data) (query_idxs ! i)"
    "partial_trace_table_candidate trace_table bound_trace_openings"
    "partial_composition_table_candidate composition_table
      bound_composition_openings"
    "all_queries_consistent trace_table composition_table
      (staged_alphas data)"
    "\<not> staged_alphas data \<in>
      alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space (fst prefix)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_supported_openingsE
        [OF wf controlled support hit])
    fix s' trace_table' i raw header_trace_openings
        header_composition_openings
    assume s'_def: "s' = ?s"
      and i_bound: "i < rounds"
      and final_lookup:
        "fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
          Some raw"
      and header_witness:
        "(header_trace_openings, header_composition_openings) \<in>
          query_header_supported_partial_opening_witnesses s'
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)"
      and header_consistent:
        "partial_query_openings_consistent header_trace_openings
          header_composition_openings (staged_alphas data)
          (index (to_nat raw))"
    show ?thesis
    proof (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_table_witnessE
          [OF wf controlled support hit])
      fix s trace_table composition_table query_idxs f bound_trace_openings
          bound_composition_openings
      assume s_def: "s = ?s"
        and bad_context:
          "composition_bad_context s (Some (result, final_state)) trace_table
            composition_table (staged_alphas data) query_idxs f"
        and trace_candidate:
          "partial_trace_table_candidate trace_table bound_trace_openings"
        and comp_candidate:
          "partial_composition_table_candidate composition_table
            bound_composition_openings"
        and all_queries:
          "all_queries_consistent trace_table composition_table
            (staged_alphas data)"
        and not_prefix:
          "\<not> staged_alphas data \<in>
            alpha_prefix_union_bad_sets prefix_state
              composition_trace_bad_alpha_space (fst prefix)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  have bound:
    "accepted_with_bound_tables s (Some (result, final_state)) trace_table
      composition_table (staged_alphas data) query_idxs"
    using bad_context unfolding composition_bad_context_def by blast
  have shape:
    "accepted_transcript_shape s (Some (result, final_state))
      (staged_alphas data) query_idxs"
    using bound unfolding accepted_with_bound_tables_def
      accepted_with_tables_def by simp
  have shape_s:
    "accepted_transcript_shape ?s (Some (result, final_state))
      (staged_alphas data) query_idxs"
    using shape s_def by simp
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled data_support shape_s]
  obtain raw_idxs where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>j. j < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
        Some (raw_idxs ! j)"
    by blast
  have raw_eq: "raw = raw_idxs ! i"
    using final_lookup lookup[OF i_bound] by simp
  have idx_eq: "index (to_nat raw) = query_idxs ! i"
    using raw_eq query_idxs_eq len_raw i_bound by simp
  have header_witness_s:
    "(header_trace_openings, header_composition_openings) \<in>
      query_header_supported_partial_opening_witnesses s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    using header_witness s'_def s_def by simp
  have header_consistent_idx:
    "partial_query_openings_consistent header_trace_openings
      header_composition_openings (staged_alphas data) (query_idxs ! i)"
    using header_consistent idx_eq by simp
      show ?thesis
        by (rule that[OF s_def bad_context i_bound final_lookup idx_eq
              header_witness_s header_consistent_idx trace_candidate
              comp_candidate all_queries not_prefix])
    qed
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_authenticated_witnessE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  obtains s trace_table composition_table query_idxs f i raw
      header_trace_openings header_composition_openings
      bound_trace_openings bound_composition_openings
      witness_result witness_final_state witness_rest where
    "s = verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
    "composition_bad_context s (Some (result, final_state)) trace_table
      composition_table (staged_alphas data) query_idxs f"
    "i < rounds"
    "index (to_nat raw) = query_idxs ! i"
    "Some (witness_result, witness_final_state) \<in>
      set_dist (execute verify_monad s)"
    "partial_authenticated_table (staged_trace_root data)
      (scale * clength) header_trace_openings witness_final_state"
    "partial_authenticated_table (hd (staged_composition_fri_roots data))
      (scale * clength) header_composition_openings witness_final_state"
    "verifier_header_transcript s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      witness_rest"
    "partial_query_openings_consistent header_trace_openings
      header_composition_openings (staged_alphas data) (query_idxs ! i)"
    "partial_trace_table_candidate trace_table bound_trace_openings"
    "partial_composition_table_candidate composition_table
      bound_composition_openings"
    "all_queries_consistent trace_table composition_table
      (staged_alphas data)"
    "\<not> staged_alphas data \<in>
      alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space (fst prefix)"
proof -
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_aligned_openingsE
        [OF wf controlled support hit])
    fix s trace_table composition_table query_idxs f i raw
        header_trace_openings header_composition_openings
        bound_trace_openings bound_composition_openings
    assume s_def:
        "s = verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      and bad_context:
        "composition_bad_context s (Some (result, final_state))
          trace_table composition_table (staged_alphas data) query_idxs f"
      and i_bound: "i < rounds"
      and idx_eq: "index (to_nat raw) = query_idxs ! i"
      and header_witness:
        "(header_trace_openings, header_composition_openings) \<in>
          query_header_supported_partial_opening_witnesses s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)"
      and header_consistent:
        "partial_query_openings_consistent header_trace_openings
          header_composition_openings (staged_alphas data) (query_idxs ! i)"
      and trace_candidate:
        "partial_trace_table_candidate trace_table bound_trace_openings"
      and comp_candidate:
        "partial_composition_table_candidate composition_table
          bound_composition_openings"
      and all_queries:
        "all_queries_consistent trace_table composition_table
          (staged_alphas data)"
      and not_prefix:
        "\<not> staged_alphas data \<in>
          alpha_prefix_union_bad_sets prefix_state
            composition_trace_bad_alpha_space (fst prefix)"
    show ?thesis
    proof (rule query_header_supported_partial_opening_witnessesE
        [OF header_witness])
      fix witness_result witness_final_state witness_rest
      assume witness_out:
          "Some (witness_result, witness_final_state) \<in>
            set_dist (execute verify_monad s)"
        and trace_auth:
          "partial_authenticated_table (staged_trace_root data)
            (scale * clength) header_trace_openings witness_final_state"
        and comp_auth:
          "partial_authenticated_table (hd (staged_composition_fri_roots data))
            (scale * clength) header_composition_openings
            witness_final_state"
        and header:
          "verifier_header_transcript s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)
            witness_rest"
      show ?thesis
        by (rule that[OF s_def bad_context i_bound idx_eq witness_out
              trace_auth comp_auth header header_consistent trace_candidate
              comp_candidate all_queries not_prefix])
    qed
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_current_openingsE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  obtains s trace_table composition_table query_idxs f i raw
      trace_openings composition_openings
      trace_openingss composition_openingss where
    "s = verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
    "composition_bad_context s (Some (result, final_state)) trace_table
      composition_table (staged_alphas data) query_idxs f"
    "i < rounds"
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some raw"
    "index (to_nat raw) = query_idxs ! i"
    "staged_composition_fri_roots data \<noteq> []"
    "partial_authenticated_table (staged_trace_root data)
      (scale * clength) trace_openings final_state"
    "partial_authenticated_table (hd (staged_composition_fri_roots data))
      (scale * clength) composition_openings final_state"
    "partial_query_openings_consistent trace_openings composition_openings
      (staged_alphas data) (query_idxs ! i)"
    "partial_trace_table_candidate trace_table trace_openingss"
    "partial_composition_table_candidate composition_table
      composition_openingss"
    "trace_openings = trace_openingss ! i"
    "composition_openings = composition_openingss ! i"
    "all_queries_consistent trace_table composition_table
      (staged_alphas data)"
    "\<not> staged_alphas data \<in>
      alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space (fst prefix)"
proof -
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_aligned_openingsE
        [OF wf controlled support hit])
    fix s trace_table composition_table query_idxs f i raw
        header_trace_openings header_composition_openings
        bound_trace_openings bound_composition_openings
    assume s_def:
        "s = verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      and bad_context:
        "composition_bad_context s (Some (result, final_state))
          trace_table composition_table (staged_alphas data) query_idxs f"
      and i_bound: "i < rounds"
      and final_lookup:
        "fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some raw"
      and idx_eq: "index (to_nat raw) = query_idxs ! i"
      and all_queries:
        "all_queries_consistent trace_table composition_table
          (staged_alphas data)"
      and not_prefix:
        "\<not> staged_alphas data \<in>
          alpha_prefix_union_bad_sets prefix_state
            composition_trace_bad_alpha_space (fst prefix)"
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    have data_support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
          [OF support])
    from checked_staged_security_experiment_with_data_state_outcomeE
        [OF data_support]
    obtain builder verifier where
      builder:
        "Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state)"
      and verifier:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
      by blast
    have staged_header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        (List.concat (staged_query_chunks data))"
      by (rule checked_staged_transcript_program_outcome_header_transcript
          [OF wf controlled builder])
    have bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table (staged_alphas data) query_idxs"
      using bad_context unfolding composition_bad_context_def by blast
    show ?thesis
    proof (rule accepted_with_bound_tables_partial_opening_witnesses_Some
        [OF bound])
      fix fr f_fri_roots f_final dg composition_fri_roots final rest
          trace_openingss composition_openingss
      assume header:
          "verifier_header_transcript s fr f_fri_roots f_final
            (staged_alphas data) dg composition_fri_roots final rest"
        and comp_nonempty: "composition_fri_roots \<noteq> []"
        and trace_partial:
          "accepted_with_partial_trace_openings s
            (Some (result, final_state)) fr query_idxs trace_openingss"
        and comp_partial:
          "accepted_with_partial_composition_openings s
            (Some (result, final_state)) (hd composition_fri_roots)
            query_idxs composition_openingss"
        and trace_candidate:
          "partial_trace_table_candidate trace_table trace_openingss"
        and comp_candidate:
          "partial_composition_table_candidate composition_table
            composition_openingss"
      have header_s:
        "verifier_header_transcript ?s fr f_fri_roots f_final
          (staged_alphas data) dg composition_fri_roots final rest"
        using header s_def by simp
      have header_eq:
        "fr = staged_trace_root data \<and>
         f_fri_roots = staged_trace_fri_roots data \<and>
         f_final = staged_trace_final data \<and>
         dg = staged_degree data \<and>
         composition_fri_roots = staged_composition_fri_roots data \<and>
         final = staged_composition_final data \<and>
         rest = List.concat (staged_query_chunks data)"
        using verifier_header_transcript_unique[OF staged_header header_s]
        by simp
      have query_len: "length query_idxs = rounds"
        by (rule accepted_with_bound_tables_shapes(4)[OF bound])
      have idx_mem: "query_idxs ! i \<in> set query_idxs"
        by (rule nth_mem) (use i_bound query_len in simp)
      have idx_sample: "query_idxs ! i \<in> query_sample_space"
        by (rule accepted_with_bound_tables_query_sample_space
            [OF bound idx_mem])
      have consistent_round:
        "partial_query_round_consistent trace_openingss
          composition_openingss (staged_alphas data) i (query_idxs ! i)"
        by (rule partial_query_round_consistent_from_all_queries_consistent
            [OF trace_partial comp_partial trace_candidate comp_candidate
              i_bound idx_sample all_queries])
      have consistent:
        "partial_query_openings_consistent (trace_openingss ! i)
          (composition_openingss ! i) (staged_alphas data) (query_idxs ! i)"
        using consistent_round
        unfolding partial_query_round_consistent_def
          partial_query_openings_consistent_def
        by simp
      have trace_auth:
        "partial_authenticated_table (staged_trace_root data)
          (scale * clength) (trace_openingss ! i) final_state"
        using trace_partial header_eq i_bound
        unfolding accepted_with_partial_trace_openings_def by blast
      have comp_auth:
        "partial_authenticated_table
          (hd (staged_composition_fri_roots data)) (scale * clength)
          (composition_openingss ! i) final_state"
        using comp_partial header_eq i_bound
        unfolding accepted_with_partial_composition_openings_def by simp
      have comp_nonempty_staged:
        "staged_composition_fri_roots data \<noteq> []"
        using comp_nonempty header_eq by simp
      show ?thesis
        by (rule that[OF s_def bad_context i_bound final_lookup idx_eq
              comp_nonempty_staged trace_auth comp_auth consistent
              trace_candidate comp_candidate refl refl all_queries not_prefix])
    qed
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_authenticated_candidate_opening_query_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
      A
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_current_openingsE
        [OF wf controlled support hit])
    fix s trace_table composition_table query_idxs f i raw trace_openings
        composition_openings trace_openingss composition_openingss
    assume i_bound: "i < rounds"
      and final_lookup:
        "fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some raw"
      and idx_eq: "index (to_nat raw) = query_idxs ! i"
      and comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
      and trace_auth:
        "partial_authenticated_table (staged_trace_root data)
          (scale * clength) trace_openings final_state"
      and comp_auth:
        "partial_authenticated_table
          (hd (staged_composition_fri_roots data)) (scale * clength)
          composition_openings final_state"
      and consistent:
        "partial_query_openings_consistent trace_openings
          composition_openings (staged_alphas data) (query_idxs ! i)"
    have consistent_raw:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
      using consistent idx_eq by simp
    show ?thesis
      by (rule
          checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hitI_from_current_openings
          [OF wf controlled comp_nonempty i_bound builder verifier
            final_lookup trace_auth comp_auth consistent_raw])
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_authenticated_candidate_opening_query_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
        A)
      adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        out"
  show
    "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
      A out"
  proof (cases out)
    case None
    then show ?thesis
      using hit
      unfolding
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      by simp
  next
    case (Some packed)
    then obtain prefix prefix_state data attacker_state result final_state
      where out_eq:
        "out =
          Some (((((prefix, prefix_state), data), attacker_state), result),
            final_state)"
      by (cases packed, auto split: prod.splits)
    show ?thesis
      unfolding out_eq
      by (rule
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_authenticated_candidate_opening_query_hit_on_support
          [OF wf controlled])
        (use support hit out_eq in simp_all)
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_authenticated:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and authenticated_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
          A)
        adversary_initial_state \<le> (Q::prob)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> Q"
  by (rule order.trans
      [OF
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_authenticated_candidate_opening_query_hit
        authenticated_bound])
    (use wf controlled in simp_all)

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_authenticated_candidate_opening_query_hit_from_prefix_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
      A
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_current_openingsE
        [OF wf controlled support hit])
    fix s trace_table composition_table query_idxs f i raw trace_openings
        composition_openings trace_openingss composition_openingss
    assume i_bound: "i < rounds"
      and final_lookup:
        "fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some raw"
      and idx_eq: "index (to_nat raw) = query_idxs ! i"
      and comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
      and trace_auth:
        "partial_authenticated_table (staged_trace_root data)
          (scale * clength) trace_openings final_state"
      and comp_auth:
        "partial_authenticated_table
          (hd (staged_composition_fri_roots data)) (scale * clength)
          composition_openings final_state"
      and consistent:
        "partial_query_openings_consistent trace_openings
          composition_openings (staged_alphas data) (query_idxs ! i)"
    have consistent_raw:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
      using consistent idx_eq by simp
    show ?thesis
      by (rule
          checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefixI_from_current_openings
          [OF wf controlled comp_nonempty i_bound builder verifier
            final_lookup trace_auth comp_auth consistent_raw])
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_authenticated_candidate_opening_query_hit_from_prefix:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
        A)
      adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        out"
  show
    "checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
      A out"
  proof (cases out)
    case None
    then show ?thesis
      using hit
      unfolding
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      by simp
  next
    case (Some packed)
    then obtain prefix prefix_state data attacker_state result final_state
      where out_eq:
        "out =
          Some (((((prefix, prefix_state), data), attacker_state), result),
            final_state)"
      by (cases packed, auto split: prod.splits)
    show ?thesis
      unfolding out_eq
      by (rule
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_authenticated_candidate_opening_query_hit_from_prefix_on_support
          [OF wf controlled])
        (use support hit out_eq in simp_all)
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_authenticated_from_prefix:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and authenticated_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
          A)
        adversary_initial_state \<le> (Q::prob)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> Q"
  by (rule order.trans
      [OF
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_authenticated_candidate_opening_query_hit_from_prefix
        authenticated_bound])
    (use wf controlled in simp_all)

lemma checked_staged_security_with_actual_alpha_prefix_aligned_transcript_query_bad_imp_candidate_opening_hit_from_prefix_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and bad:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        query_bad_with_aligned_transcript_partial_candidates
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state))"
  obtains i trace_openings composition_openings where
    "i < rounds"
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A trace_openings composition_openings i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  from bad obtain fr f_fri_roots f_final as dg composition_fri_roots
      final query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent
        ?s (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      query_bad_with_aligned_transcript_partial_candidates_def
    by auto
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as
      query_idxs"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_shape
        [OF partial])
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled data_support shape]
  obtain raw_idxs where
    as_eq: "as = staged_alphas data"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<forall>i<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    by blast
  have zero_bound: "0 < rounds"
    by (rule rounds_positive)
  let ?raw = "raw_idxs ! 0"
  have lookup0:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge 0
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) 0)) =
      Some ?raw"
    using lookup zero_bound by simp
  from checked_staged_transcript_program_query_prefix_receive_final_lookup_support_with_alphas
      [OF wf controlled zero_bound builder verifier lookup0]
  obtain prefix prefix_state raw_state where prefix_receive:
    "Some (((prefix, prefix_state), ?raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A 0)
          adversary_initial_state)"
    and prefix_alphas: "sqp_alphas prefix = staged_alphas data"
    by blast
  have idx_eq: "query_idxs ! 0 = index (to_nat ?raw)"
    using query_idxs_eq len_raw zero_bound by simp
  have alphas_eq: "as = sqp_alphas prefix"
    using as_eq prefix_alphas by simp
  have hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix
      A trace_openings composition_openings 0
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_candidate_opening_hit_from_prefix
        [OF partial zero_bound idx_eq alphas_eq builder prefix_receive])
  show ?thesis
    by (rule that[OF zero_bound hit])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_authenticated_and_without_query:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and authenticated_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
          A)
        adversary_initial_state \<le> (Q::prob)"
    and without_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
        adversary_initial_state \<le> (W::prob)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> Q + W"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_query_and_without_query)
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> Q"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_authenticated
        [OF wf controlled authenticated_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le> W"
    by (rule without_bound)
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_authenticated_from_prefix_and_without_query:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and authenticated_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
          A)
        adversary_initial_state \<le> (Q::prob)"
    and without_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
        adversary_initial_state \<le> (W::prob)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> Q + W"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_query_and_without_query)
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> Q"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_authenticated_from_prefix
        [OF wf controlled authenticated_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le> W"
    by (rule without_bound)
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_candidate_opening_query_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit
      A
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_supported_openingsE
        [OF wf controlled support hit])
    fix s trace_table i raw trace_openings composition_openings
    assume i_bound: "i < rounds"
      and final_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
        Some raw"
      and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
    have data_support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
          [OF support])
    from checked_staged_security_experiment_with_data_state_outcomeE
        [OF data_support]
    obtain builder verifier where
      builder:
        "Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state)"
      and verifier:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
      by blast
    from checked_staged_transcript_program_query_prefix_receive_final_lookup_support
        [OF wf controlled i_bound builder verifier final_lookup]
    obtain query_prefix query_prefix_state raw_state where prefix_receive:
      "Some (((query_prefix, query_prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
      by blast
    have component:
      "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit
        A
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        (staged_alphas data) i
        (Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state))"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hitI_from_prefix_receive
          [OF i_bound builder prefix_receive consistent])
    show ?thesis
      by (rule
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hitI
          [OF component])
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_candidate_opening_query_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit
        A)
      adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        out"
  show
    "checked_staged_security_with_actual_alpha_prefix_composition_candidate_opening_query_hit
      A out"
  proof (cases out)
    case None
    then show ?thesis
      using hit
      unfolding
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      by simp
  next
    case (Some packed)
    then obtain prefix prefix_state data attacker_state result final_state
      where out_eq:
        "out =
          Some (((((prefix, prefix_state), data), attacker_state), result),
            final_state)"
      by (cases packed, auto split: prod.splits)
    show ?thesis
      unfolding out_eq
      by (rule
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_candidate_opening_query_hit_on_support
          [OF wf controlled])
        (use support hit out_eq in simp_all)
  qed
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_authenticated_query_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and authenticated_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit
          A)
        adversary_initial_state \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      Q +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have without_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le> 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_bound
        [OF wf controlled])
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> Q + 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_authenticated_and_without_query
        [OF wf controlled authenticated_bound without_bound])
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (Q + 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_composition_candidate_drift_and_budgets
        [OF wf controlled drift_bound])
  then show ?thesis
    by simp
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_header_authenticated_query_from_prefix_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and header_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
          A)
        adversary_initial_state \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      Q +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have without_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le> 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_bound
        [OF wf controlled])
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> Q + 0"
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_query_and_without_query)
    show
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        adversary_initial_state \<le> Q"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_header_authenticated_from_prefix
          [OF wf controlled header_bound])
    show
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
        adversary_initial_state \<le> 0"
      by (rule without_bound)
  qed
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (Q + 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_composition_candidate_drift_and_budgets
        [OF wf controlled drift_bound])
  then show ?thesis
    by simp
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_authenticated_query_from_prefix_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and authenticated_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_authenticated_candidate_opening_query_hit_from_prefix
          A)
        adversary_initial_state \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      Q +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have without_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le> 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_bound
        [OF wf controlled])
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> Q + 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_authenticated_from_prefix_and_without_query
        [OF wf controlled authenticated_bound without_bound])
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (Q + 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_composition_candidate_drift_and_budgets
        [OF wf controlled drift_bound])
  then show ?thesis
    by simp
qed

end

end
