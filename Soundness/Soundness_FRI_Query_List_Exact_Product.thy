(*  Title:      Stark/Soundness_FRI_Query_List_Exact_Product.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_List_Exact_Product
  imports Soundness_FRI_Query_List_Prequery
begin

text \<open>
  Exact product accounting for sampled FRI query-index lists.

  The preceding layer proves the product theorem in raw field space.  This
  layer converts raw-list preimages to query-index-list targets using the
  current exact-uniformity assumptions for the modulo sampler.
\<close>

context soundness
begin

definition verifier_after_composition_fri_raw_list_path_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat list set \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "verifier_after_composition_fri_raw_list_path_hit s Q out \<longleftrightarrow>
      (\<exists>final query_state raws.
        Some (final, query_state) \<in> set_dist (execute read s) \<and>
        raws \<in> query_index_raw_list_preimage Q \<and>
        query_rounds_raw_list_path_hit query_state raws rounds out)"

lemma verifier_after_composition_fri_raw_list_path_hitI:
  assumes read_final:
    "Some (final, query_state) \<in> set_dist (execute read s)"
    and raw_in: "raws \<in> query_index_raw_list_preimage Q"
    and len_raws: "length raws = rounds"
    and len_chunks: "length chunks = rounds"
    and state:
      "PState t = state_after_query_chunks (PState query_state) chunks rounds"
    and fresh:
      "query_index_list_path_fresh query_state rounds chunks raws"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) chunks i)) =
        Some (raws ! i)"
    and out_eq: "out = Some (results, t)"
  shows "verifier_after_composition_fri_raw_list_path_hit s Q out"
proof -
  have path: "query_rounds_raw_list_path_hit query_state raws rounds out"
    unfolding out_eq
    by (rule query_rounds_raw_list_path_hitI
        [OF len_raws len_chunks state fresh lookup])
  show ?thesis
    unfolding verifier_after_composition_fri_raw_list_path_hit_def
    by (intro exI[of _ final] exI[of _ query_state] exI[of _ raws]
        conjI read_final raw_in path)
qed

lemma staged_security_with_data_state_query_index_list_path_fresh_SomeE:
  assumes hit:
    "staged_security_with_data_state_query_index_list_path_fresh Q
      (Some (((data, attacker_state), result), final_state))"
  obtains raw_idxs query_idxs where
    "length raw_idxs = rounds"
    "query_idxs \<in> Q"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup
        (HashMap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      None"
proof -
  have hit_ex:
    "\<exists>raw_idxs query_idxs.
      length raw_idxs = rounds \<and>
      query_idxs \<in> Q \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      (\<forall>i<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i) \<and>
        fmlookup
          (HashMap
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        None)"
    using hit
    unfolding staged_security_with_data_state_query_index_list_path_fresh_def
    by simp
  from hit_ex obtain raw_idxs query_idxs where len:
    "length raw_idxs = rounds"
    and in_Q: "query_idxs \<in> Q"
    and map_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookups:
      "\<forall>i<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i) \<and>
        fmlookup
          (HashMap
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        None"
    by blast
  show ?thesis
  proof (rule that[OF len in_Q map_eq])
    fix i
    assume "i < rounds"
    then show
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
      using lookups by blast
  next
    fix i
    assume "i < rounds"
    then show
      "fmlookup
        (HashMap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      None"
      using lookups by blast
  qed
qed

lemma staged_security_with_data_state_query_index_list_path_fresh_None[simp]:
  "\<not> staged_security_with_data_state_query_index_list_path_fresh Q None"
  unfolding staged_security_with_data_state_query_index_list_path_fresh_def
  by simp

lemma staged_security_with_data_state_query_index_list_path_fresh_caseD:
  assumes hit:
    "staged_security_with_data_state_query_index_list_path_fresh Q
      (case out of
        None \<Rightarrow> None
      | Some (result, final_state) \<Rightarrow>
          Some (((data, attacker_state), result), final_state))"
  shows
    "\<exists>result final_state raw_idxs query_idxs.
      out = Some (result, final_state) \<and>
      length raw_idxs = rounds \<and>
      query_idxs \<in> Q \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      (\<forall>i < rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)) \<and>
      (\<forall>i < rounds.
        fmlookup
          (HashMap
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        None)"
proof (cases out)
  case None
  then show ?thesis
    using hit by simp
next
  case (Some pair)
  then obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    by (cases pair) simp
  have hit_ex:
    "\<exists>raw_idxs query_idxs.
      length raw_idxs = rounds \<and>
      query_idxs \<in> Q \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      (\<forall>i<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i) \<and>
        fmlookup
          (HashMap
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        None)"
    using hit out_eq
    unfolding staged_security_with_data_state_query_index_list_path_fresh_def
    by simp
  from hit_ex obtain raw_idxs query_idxs where
    "length raw_idxs = rounds"
    "query_idxs \<in> Q"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "\<forall>i<rounds.
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some (raw_idxs ! i) \<and>
      fmlookup
        (HashMap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
      None"
    by blast
  then show ?thesis
    using out_eq by blast
qed

lemma staged_security_with_data_state_query_index_list_path_fresh_caseE:
  assumes hit:
    "staged_security_with_data_state_query_index_list_path_fresh Q
      (case out of
        None \<Rightarrow> None
      | Some (result, final_state) \<Rightarrow>
          Some (((data, attacker_state), result), final_state))"
  obtains result final_state raw_idxs query_idxs where
    "out = Some (result, final_state)"
    "length raw_idxs = rounds"
    "query_idxs \<in> Q"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup
        (HashMap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      None"
proof (cases out)
  case None
  then have False
    using hit by simp
  then show ?thesis by simp
next
  case (Some pair)
  then obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    by (cases pair) simp
  have hit_some:
    "staged_security_with_data_state_query_index_list_path_fresh Q
      (Some (((data, attacker_state), result), final_state))"
    using hit out_eq by simp
  from staged_security_with_data_state_query_index_list_path_fresh_SomeE
      [OF hit_some]
  obtain raw_idxs query_idxs where
    len: "length raw_idxs = rounds"
    and in_Q: "query_idxs \<in> Q"
    and map_eq: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    and fresh:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup
          (HashMap
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        None"
    by blast
  show ?thesis
    by (rule that[OF out_eq len in_Q map_eq lookup fresh])
qed

lemma verifier_header_transcript_from_prefix_read:
  assumes len_trace: "length f_roots = ceil_log clength"
    and len_alpha: "length as = length spec"
    and len_comp: "length comp_roots = ceil_log (to_nat dg + 1)"
    and transcript_prefix:
      "PTranscript s =
        [fr] @ f_roots @ [f_final] @ as @ [dg] @
        comp_roots @ PTranscript prefix_state"
    and read_prefix: "PTranscript prefix_state = final # rest"
    and query_rest: "PTranscript query_state = rest"
  shows
    "verifier_header_transcript s fr f_roots f_final as dg
      comp_roots final (PTranscript query_state)"
proof -
  have transcript:
    "PTranscript s =
      verifier_header_messages fr f_roots f_final as dg comp_roots final @
        PTranscript query_state"
    using transcript_prefix read_prefix query_rest
    unfolding verifier_header_messages_def
    by simp
  show ?thesis
    unfolding verifier_header_transcript_def
    using transcript len_trace len_alpha len_comp by simp
qed

lemma verifier_composition_fri_prefix_outcome_basicD:
  assumes outcome:
    "Some ((fr, f_fl, f_final, as, dg, fl), t) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
  shows
    "length f_fl = ceil_log clength \<and>
     length as = length spec \<and>
     length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s =
       [fr] @ map snd f_fl @ [f_final] @ as @ [dg] @
       map snd fl @ PTranscript t \<and>
     PState t =
       foldl concat
        (concat
          (foldl concat
            (concat
              (foldl concat (concat (PState s) fr) (map snd f_fl))
              f_final)
            as)
          dg)
        (map snd fl) \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  have full: "length f_fl = ceil_log clength \<and>
     length as = length spec \<and>
     length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s =
       [fr] @ map snd f_fl @ [f_final] @ as @ [dg] @
       map snd fl @ PTranscript t \<and>
     PState t =
       foldl concat
        (concat
          (foldl concat
            (concat
              (foldl concat (concat (PState s) fr) (map snd f_fl))
              f_final)
            as)
          dg)
        (map snd fl) \<and>
     s \<le> t \<and>
     PQueryCounter t = PQueryCounter s \<and>
     (\<forall>i < length f_fl.
        fmlookup (HashMap t)
          (TraceFriChallenge (PTraceFriCounter s + i)
            (foldl concat (concat (PState s) fr)
              (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))) \<and>
     (\<forall>i < length fl.
        fmlookup (HashMap t)
          (CompositionFriChallenge (PCompositionFriCounter s + i)
            (foldl concat
              (concat
                (foldl concat
                  (concat
                    (foldl concat (concat (PState s) fr) (map snd f_fl))
                    f_final)
                  as)
                dg)
              (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i)))"
    by (rule verifier_composition_fri_prefix_outcome[OF outcome])
  then show ?thesis by simp
qed

lemma alpha_round_preserves_query_lookup:
  assumes outcome: "Some (a, t) \<in> set_dist (execute alpha_round s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
proof -
  from outcome obtain a0 s0 a1 s1 s2 where
    rand: "Some (a0, s0) \<in> set_dist (execute receive_alpha_challenge s)"
    and read_a: "Some (a1, s1) \<in> set_dist (execute read s0)"
    and assert_a: "Some ((), s2) \<in> set_dist (execute (assert (a0 = a1)) s1)"
    and ret_a: "Some (a, t) \<in> set_dist (execute (return a1) s2)"
    unfolding alpha_round_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  have neq:
    "QueryIndexChallenge i x \<noteq>
      AlphaChallenge (PAlphaCounter s) (PState s)"
    by simp
  have rand_lookup:
    "fmlookup (HashMap s0) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
    by (rule receive_alpha_challenge_preserves_other_lookup[OF rand neq])
  have read_lookup:
    "HashMap s1 = HashMap s0"
    by (rule read_preserves_hash_map[OF read_a])
  have s2_eq: "s2 = s1"
    using assert_a unfolding assert_def
    by (cases "a0 = a1") (auto simp: throw_no_outcome)
  have t_eq: "t = s2"
    using ret_a by simp
  show ?thesis
    using rand_lookup read_lookup unfolding t_eq s2_eq by simp
qed

lemma receive_trace_fri_commits_preserves_query_lookup:
  assumes outcome:
    "Some ((b, r), t) \<in> set_dist (execute receive_trace_fri_commits s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s_read)"
    unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  have read_lookup:
    "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have neq:
    "QueryIndexChallenge i x \<noteq>
      TraceFriChallenge (PTraceFriCounter s_read) (PState s_read)"
    by simp
  have rand_lookup:
    "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s_read) (QueryIndexChallenge i x)"
    by (rule receive_trace_fri_challenge_preserves_other_lookup
        [OF rand_b neq])
  show ?thesis
    using rand_lookup read_lookup by simp
qed

lemma receive_composition_fri_commits_preserves_query_lookup:
  assumes outcome:
    "Some ((b, r), t) \<in>
      set_dist (execute receive_composition_fri_commits s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in>
        set_dist (execute receive_composition_fri_challenge s_read)"
    unfolding receive_composition_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  have read_lookup:
    "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have neq:
    "QueryIndexChallenge i x \<noteq>
      CompositionFriChallenge
        (PCompositionFriCounter s_read) (PState s_read)"
    by simp
  have rand_lookup:
    "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s_read) (QueryIndexChallenge i x)"
    by (rule receive_composition_fri_challenge_preserves_other_lookup
        [OF rand_b neq])
  show ?thesis
    using rand_lookup read_lookup by simp
qed

lemma verifier_composition_fri_prefix_preserves_query_lookup:
  assumes outcome:
    "Some ((fr, f_fl, f_final, as, dg, fl), t) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
proof -
  let ?key = "QueryIndexChallenge i x"
  from outcome obtain s1 s2 s3 s4 s5 s6 s7 where
    read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    and trace_fri:
      "Some (f_fl, s2) \<in>
        set_dist (execute
          (ntimes receive_trace_fri_commits (ceil_log clength)) s1)"
    and read_f_final: "Some (f_final, s3) \<in> set_dist (execute read s2)"
    and alpha_out:
      "Some (as, s4) \<in>
        set_dist (execute (mmap (replicate (length spec) alpha_round)) s3)"
    and read_dg: "Some (dg, s5) \<in> set_dist (execute read s4)"
    and degree_assert:
      "Some ((), s6) \<in>
        set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
    and comp_fri:
      "Some (fl, s7) \<in>
        set_dist (execute
          (ntimes receive_composition_fri_commits
            (ceil_log (to_nat dg + 1))) s6)"
    and ret:
      "Some ((fr, f_fl, f_final, as, dg, fl), t) \<in>
        set_dist (execute (return (fr, f_fl, f_final, as, dg, fl)) s7)"
    unfolding verifier_composition_fri_prefix_def
    by (auto elim!: set_dist_bindE)
  have lookup_s1:
    "fmlookup (HashMap s1) ?key = fmlookup (HashMap s) ?key"
    using read_preserves_hash_map[OF read_fr] by simp
  have lookup_s2:
    "fmlookup (HashMap s2) ?key = fmlookup (HashMap s1) ?key"
  proof (rule ntimes_preserves_lookup[OF _ trace_fri])
    fix y u v
    assume out: "Some (y, v) \<in> set_dist (execute receive_trace_fri_commits u)"
    obtain b r where y_eq: "y = (b, r)"
      by (cases y) simp
    show "fmlookup (HashMap v) ?key = fmlookup (HashMap u) ?key"
      by (rule receive_trace_fri_commits_preserves_query_lookup
          [OF out[unfolded y_eq]])
  qed
  have lookup_s3:
    "fmlookup (HashMap s3) ?key = fmlookup (HashMap s2) ?key"
    using read_preserves_hash_map[OF read_f_final] by simp
  have lookup_s4:
    "fmlookup (HashMap s4) ?key = fmlookup (HashMap s3) ?key"
  proof (rule mmap_preserves_lookup[OF _ alpha_out])
    fix m y u v
    assume m_in: "m \<in> set (replicate (length spec) alpha_round)"
      and out: "Some (y, v) \<in> set_dist (execute m u)"
    then have m_eq: "m = alpha_round"
      by simp
    show "fmlookup (HashMap v) ?key = fmlookup (HashMap u) ?key"
      using alpha_round_preserves_query_lookup[OF out[unfolded m_eq]] .
  qed
  have lookup_s5:
    "fmlookup (HashMap s5) ?key = fmlookup (HashMap s4) ?key"
    using read_preserves_hash_map[OF read_dg] by simp
  have s6_eq: "s6 = s5"
    using degree_assert unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
  have lookup_s7:
    "fmlookup (HashMap s7) ?key = fmlookup (HashMap s6) ?key"
  proof (rule ntimes_preserves_lookup[OF _ comp_fri])
    fix y u v
    assume out: "Some (y, v) \<in>
      set_dist (execute receive_composition_fri_commits u)"
    obtain b r where y_eq: "y = (b, r)"
      by (cases y) simp
    show "fmlookup (HashMap v) ?key = fmlookup (HashMap u) ?key"
      by (rule receive_composition_fri_commits_preserves_query_lookup
          [OF out[unfolded y_eq]])
  qed
  have t_eq: "t = s7"
    using ret by simp
  show ?thesis
    using lookup_s1 lookup_s2 lookup_s3 lookup_s4 lookup_s5 lookup_s7
    unfolding t_eq s6_eq by simp
qed

lemma query_index_raw_singleton_card_uniform:
  assumes b_in: "b \<in> query_sample_space"
  shows "card (query_index_raw_preimage {b}) =
    size div query_sample_space_size"
proof -
  have subset: "{b} \<subseteq> query_sample_space"
    using b_in by simp
  have "card (query_index_raw_preimage {b}) =
      (size div query_sample_space_size) * card {b}"
    unfolding card_query_index_raw_preimage_eq_nat_preimage
    apply (rule card_query_index_nat_preimage_uniform_range)
    apply (rule to_nat_range)
    using query_sample_space_size_dvd subset
        unfolding query_sample_space_size_def by simp_all
  then show ?thesis
    by simp
qed

lemma query_index_raw_list_fixed_preimage_card_bound:
  assumes len: "length query_idxs = rounds"
    and subset: "set query_idxs \<subseteq> query_sample_space"
  shows "card {raws.
      length raws = rounds \<and>
      map (\<lambda>raw. index (to_nat raw)) raws = query_idxs}
    \<le> (size div query_sample_space_size) ^ rounds"
  using len subset
proof (induction rounds arbitrary: query_idxs)
  case 0
  then have "{raws.
      length raws = 0 \<and>
      map (\<lambda>raw. index (to_nat raw)) raws = query_idxs} = {[]}"
    by auto
  then show ?case by simp
next
  case (Suc n)
  obtain q qs where query_eq: "query_idxs = q # qs"
    using Suc.prems(1) by (cases query_idxs) auto
  have len_qs: "length qs = n"
    using Suc.prems(1) unfolding query_eq by simp
  have q_in: "q \<in> query_sample_space"
    using Suc.prems(2) unfolding query_eq by simp
  have qs_subset: "set qs \<subseteq> query_sample_space"
    using Suc.prems(2) unfolding query_eq by simp
  let ?A = "{raws.
      length raws = Suc n \<and>
      map (\<lambda>raw. index (to_nat raw)) raws = q # qs}"
  let ?B = "query_index_raw_preimage {q}"
  let ?C = "{raws.
      length raws = n \<and>
      map (\<lambda>raw. index (to_nat raw)) raws = qs}"
  have A_eq: "?A = (\<lambda>(raw, raws). raw # raws) ` (?B \<times> ?C)"
  proof
    show "?A \<subseteq> (\<lambda>(raw, raws). raw # raws) ` (?B \<times> ?C)"
    proof
      fix raws
      assume raws_in: "raws \<in> ?A"
      then obtain raw tail where raws_eq: "raws = raw # tail"
        by (cases raws) auto
      have raw_in: "raw \<in> ?B"
        using raws_in unfolding raws_eq query_index_raw_preimage_def by simp
      have tail_in: "tail \<in> ?C"
        using raws_in unfolding raws_eq by simp
      show "raws \<in> (\<lambda>(raw, raws). raw # raws) ` (?B \<times> ?C)"
        unfolding raws_eq by (intro image_eqI[of _ _ "(raw, tail)"])
          (use raw_in tail_in in simp_all)
    qed
  next
    show "(\<lambda>(raw, raws). raw # raws) ` (?B \<times> ?C) \<subseteq> ?A"
      unfolding query_index_raw_preimage_def by auto
  qed
  have inj: "inj_on (\<lambda>(raw, raws). raw # raws) (?B \<times> ?C)"
    unfolding inj_on_def by auto
  have finite_B: "finite ?B"
    by simp
  have finite_C: "finite ?C"
  proof -
    have "?C \<subseteq> {xs. length xs = n}"
      by auto
    then show ?thesis
      by (auto intro: List.finite_list_length)
  qed
  have "card ?A = card ((\<lambda>(raw, raws). raw # raws) ` (?B \<times> ?C))"
    unfolding A_eq by simp
  also have "... = card (?B \<times> ?C)"
    by (rule card_image[OF inj])
  also have "... = card ?B * card ?C"
    using finite_B finite_C by simp
  also have "... \<le>
      (size div query_sample_space_size) *
      (size div query_sample_space_size) ^ n"
  proof (rule mult_mono)
    show "card ?B \<le> size div query_sample_space_size"
      using query_index_raw_singleton_card_uniform[OF q_in] by simp
    show "card ?C \<le> (size div query_sample_space_size) ^ n"
      by (rule Suc.IH[OF len_qs qs_subset])
    show "0 \<le> size div query_sample_space_size" by simp
    show "0 \<le> card ?C" by simp
  qed
  also have "... = (size div query_sample_space_size) ^ Suc n"
    by simp
  finally show ?case
    unfolding query_eq .
qed

lemma query_index_raw_list_preimage_card_bound:
  assumes subset: "Q \<subseteq> fri_query_index_list_space"
  shows "card (query_index_raw_list_preimage Q)
    \<le> card Q * (size div query_sample_space_size) ^ rounds"
proof -
  let ?fiber = "\<lambda>query_idxs. {raws.
      length raws = rounds \<and>
      map (\<lambda>raw. index (to_nat raw)) raws = query_idxs}"
  have finite_Q: "finite Q"
    using subset by (rule finite_subset) (rule finite_fri_query_index_list_space)
  have preimage_eq:
    "query_index_raw_list_preimage Q = (\<Union>query_idxs \<in> Q. ?fiber query_idxs)"
    unfolding query_index_raw_list_preimage_def by auto
  have finite_fiber: "\<And>query_idxs. finite (?fiber query_idxs)"
  proof -
    fix query_idxs
    have "?fiber query_idxs \<subseteq> {xs. length xs = rounds}"
      by auto
    then show "finite (?fiber query_idxs)"
      by (auto intro: List.finite_list_length)
  qed
  have "card (query_index_raw_list_preimage Q) =
      card (\<Union>query_idxs \<in> Q. ?fiber query_idxs)"
    unfolding preimage_eq ..
  also have "... \<le> (\<Sum>query_idxs \<in> Q. card (?fiber query_idxs))"
    using finite_Q by (auto intro: card_UN_le)
  also have "... \<le>
      (\<Sum>query_idxs \<in> Q.
        (size div query_sample_space_size) ^ rounds)"
  proof (rule sum_mono)
    fix query_idxs
    assume query_in: "query_idxs \<in> Q"
    have len: "length query_idxs = rounds"
      using query_in subset unfolding fri_query_index_list_space_def by auto
    have entries: "set query_idxs \<subseteq> query_sample_space"
      using query_in subset unfolding fri_query_index_list_space_def by auto
    show "card (?fiber query_idxs)
      \<le> (size div query_sample_space_size) ^ rounds"
      by (rule query_index_raw_list_fixed_preimage_card_bound[OF len entries])
  qed
  also have "... = card Q * (size div query_sample_space_size) ^ rounds"
    using finite_Q by simp
  finally show ?thesis .
qed

lemma query_index_raw_list_preimage_probability_bound:
  assumes subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "nnreal (card (query_index_raw_list_preimage Q)) *
      (1 / nnreal size) ^ rounds
    \<le> nnreal (card Q) *
      (1 / nnreal (card query_sample_space)) ^ rounds"
proof -
  let ?d = "size div query_sample_space_size"
  have card_le:
    "card (query_index_raw_list_preimage Q)
      \<le> card Q * ?d ^ rounds"
    by (rule query_index_raw_list_preimage_card_bound[OF subset])
  have dvd: "query_sample_space_size dvd size"
    using query_sample_space_size_dvd
    unfolding query_sample_space_size_def by simp
  have size_eq: "size = ?d * query_sample_space_size"
    using dvd query_sample_space_size_pos by (simp add: dvd_eq_mod_eq_0)
  have size_pos: "0 < size"
    using size_card by simp
  have d_pos: "0 < ?d"
  proof (cases ?d)
    case 0
    then show ?thesis
      using size_eq size_pos by simp
  next
    case (Suc n)
    then show ?thesis by simp
  qed
  have le:
    "nnreal (card (query_index_raw_list_preimage Q)) *
      (1 / nnreal size) ^ rounds
    \<le> nnreal (card Q * ?d ^ rounds) *
      (1 / nnreal size) ^ rounds"
    using card_le apply (simp add: mult_right_mono)
    by (metis mult_right_mono of_nat_le_iff of_nat_mult of_nat_power zero_least)
  have prod_eq:
    "nnreal (card Q * ?d ^ rounds) *
      (1 / nnreal size) ^ rounds =
      nnreal (card Q) *
      (1 / nnreal (card query_sample_space)) ^ rounds"
  proof -
    have card_space_eq:
      "card query_sample_space = query_sample_space_size"
      by (rule card_query_sample_space)
    have base_eq:
      "nnreal ?d * (1 / nnreal size) =
        1 / nnreal (card query_sample_space)"
    proof (rule nn2real_eq_iff[THEN iffD1])
      have real_base:
        "real ?d / real size = 1 / real query_sample_space_size"
      proof -
        have real_size_eq:
          "real size = real ?d * real query_sample_space_size"
          using arg_cong[OF size_eq, of real]
          by (simp add: of_nat_mult)
        have "real ?d / real size =
            real ?d / (real ?d * real query_sample_space_size)"
          using real_size_eq by simp
        also have "... = 1 / real query_sample_space_size"
          using d_pos query_sample_space_size_pos
          by (simp add: field_simps)
        finally show ?thesis .
      qed
      show "nn2real (nnreal ?d * (1 / nnreal size)) =
        nn2real (1 / nnreal (card query_sample_space))"
      proof -
        have lhs_eq:
          "nn2real (nnreal ?d * (1 / nnreal size)) =
            real ?d / real size"
        proof -
          have "nn2real (nnreal ?d * (1 / nnreal size)) =
              real ?d * (1 / real size)"
            by (simp only: nn2real_mult nn2real_nnreal
                nn2real_divide nn2real_1)
          also have "... = real ?d / real size"
            by (simp add: divide_inverse)
          finally show ?thesis .
        qed
        have rhs_eq:
          "nn2real (1 / nnreal (card query_sample_space)) =
            1 / real query_sample_space_size"
          unfolding card_space_eq
          by (simp only: nn2real_divide nn2real_1 nn2real_nnreal)
        show ?thesis
          using real_base lhs_eq rhs_eq by simp
      qed
    qed
    have
      "nnreal (card Q * ?d ^ rounds) * (1 / nnreal size) ^ rounds =
       nnreal (card Q) * (nnreal ?d * (1 / nnreal size)) ^ rounds"
      by (simp add: of_nat_mult of_nat_power power_mult_distrib
          ac_simps)
    also have "... =
       nnreal (card Q) *
         (1 / nnreal (card query_sample_space)) ^ rounds"
      using base_eq by simp
    finally show ?thesis .
  qed
  show ?thesis
    using le prod_eq by simp
qed

lemma wp_ntimes_verifier_query_round_program_query_list_path_product_bound:
  assumes subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
        rounds)
      (\<lambda>out. \<exists>raws \<in> query_index_raw_list_preimage Q.
        query_rounds_raw_list_path_hit s raws rounds out)
      s \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
proof -
  have raw_bound:
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
        rounds)
      (\<lambda>out. \<exists>raws \<in> query_index_raw_list_preimage Q.
        query_rounds_raw_list_path_hit s raws rounds out)
      s \<le>
      nnreal (card (query_index_raw_list_preimage Q)) *
        (1 / nnreal size) ^ rounds"
    by (rule wp_ntimes_verifier_query_round_program_raw_list_preimage_path_hit_bound)
  also have "... \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
    by (rule query_index_raw_list_preimage_probability_bound[OF subset])
  finally show ?thesis .
qed

lemma read_outcome_unique_state:
  assumes out1: "Some (x, t) \<in> set_dist (execute read s)"
    and out2: "Some (y, u) \<in> set_dist (execute read s)"
  shows "x = y \<and> t = u"
proof -
  from read_outcome[OF out1] obtain rest where
    tr: "PTranscript s = x # rest"
    by blast
  have out1_eq:
    "t = s\<lparr>PState := concat (PState s) x, PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF out1 tr] by simp
  have out2_eq:
    "y = x \<and>
     u = s\<lparr>PState := concat (PState s) x, PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF out2 tr] by simp
  then show ?thesis
    using out1_eq by simp
qed

lemma wp_verifier_after_composition_fri_raw_list_path_product_bound:
  assumes subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (verifier_after_composition_fri header)
      (verifier_after_composition_fri_raw_list_path_hit s Q) s \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
proof -
  obtain fr f_fl f_final as dg fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg, fl)"
    by (cases header) auto
  have after_eq:
    "verifier_after_composition_fri header =
      (read \<bind>
        (\<lambda>final.
          ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds))"
    unfolding header_eq verifier_after_composition_fri_def by simp
  show ?thesis
    unfolding after_eq
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> verifier_after_composition_fri_raw_list_path_hit s Q None"
      unfolding verifier_after_composition_fri_raw_list_path_hit_def
        query_rounds_raw_list_path_hit_def
      by simp
  next
    fix final query_state
    assume read_final:
      "Some (final, query_state) \<in> set_dist (execute read s)"
    have mono:
      "wp_event
        (ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds)
        (verifier_after_composition_fri_raw_list_path_hit s Q)
        query_state \<le>
       wp_event
        (ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds)
        (\<lambda>out. \<exists>raws \<in> query_index_raw_list_preimage Q.
          query_rounds_raw_list_path_hit query_state raws rounds out)
        query_state"
    proof (rule wp_event_mono_on_support)
      fix out
      assume hit:
        "verifier_after_composition_fri_raw_list_path_hit s Q out"
      from hit obtain final' query_state' raws where
        read':
          "Some (final', query_state') \<in> set_dist (execute read s)"
        and raw_in: "raws \<in> query_index_raw_list_preimage Q"
        and path:
          "query_rounds_raw_list_path_hit query_state' raws rounds out"
        unfolding verifier_after_composition_fri_raw_list_path_hit_def
        by blast
      have "query_state' = query_state"
        using read_outcome_unique_state[OF read' read_final] by simp
      then show "\<exists>raws\<in>query_index_raw_list_preimage Q.
        query_rounds_raw_list_path_hit query_state raws rounds out"
        using raw_in path by blast
    qed
    also have "... \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
      by (rule
          wp_ntimes_verifier_query_round_program_query_list_path_product_bound
          [OF subset])
    finally show
      "wp_event
        (ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds)
        (verifier_after_composition_fri_raw_list_path_hit s Q)
        query_state
      \<le> nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds" .
      qed
qed

lemma verifier_after_composition_fri_query_index_list_path_fresh_imp_raw_hit_after_prefix:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix:
      "Some (header, prefix_state) \<in>
        set_dist
          (execute verifier_composition_fri_prefix
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and suffix:
      "out \<in> set_dist
        (execute (verifier_after_composition_fri header) prefix_state)"
    and hit:
      "staged_security_with_data_state_query_index_list_path_fresh Q
        (case out of
          None \<Rightarrow> None
        | Some (result, final_state) \<Rightarrow>
            Some (((data, attacker_state), result), final_state))"
  shows "verifier_after_composition_fri_raw_list_path_hit prefix_state Q out"
proof (cases out)
  case None
  then show ?thesis
    using hit by simp
next
  case (Some result_state)
  then obtain result final_state where
    out_eq: "out = Some (result, final_state)"
    by (cases result_state) simp
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have hit_some:
    "staged_security_with_data_state_query_index_list_path_fresh Q
      (Some (((data, attacker_state), result), final_state))"
    using hit out_eq by simp
  from staged_security_with_data_state_query_index_list_path_fresh_SomeE
      [OF hit_some]
  obtain raw_idxs_hit query_idxs_hit where
    len_hit: "length raw_idxs_hit = rounds"
    and query_hit_in: "query_idxs_hit \<in> Q"
    and query_hit_eq:
      "query_idxs_hit = map (\<lambda>raw. index (to_nat raw)) raw_idxs_hit"
    and lookup_hit:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs_hit ! i)"
    and fresh_hit:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap ?s)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        None"
    by blast
  obtain fr f_fl f_final as dg fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg, fl)"
    by (cases header) auto
  from suffix[unfolded out_eq header_eq verifier_after_composition_fri_def]
  obtain final query_state where
    read_final:
      "Some (final, query_state) \<in> set_dist (execute read prefix_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    by (auto elim!: set_dist_bindE)
  from ntimes_verifier_query_rounds_outcome[OF query_out]
  obtain raw_idxs query_idxs query_chunks where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and tr_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and state_final:
      "PState final_state =
        state_after_query_chunks (PState query_state) query_chunks rounds"
    and round_chunks:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and lookups:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    by blast
  from read_outcome[OF read_final] have query_counter:
    "PQueryCounter query_state = PQueryCounter prefix_state"
    by blast
  have prefix_basic:
    "length f_fl = ceil_log clength \<and>
     length as = length spec \<and>
     length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript ?s =
       [fr] @ map snd f_fl @ [f_final] @ as @ [dg] @
       map snd fl @ PTranscript prefix_state \<and>
     PState prefix_state =
       foldl concat
        (concat
          (foldl concat
            (concat
              (foldl concat (concat (PState ?s) fr) (map snd f_fl))
              f_final)
            as)
          dg)
        (map snd fl) \<and>
     PQueryCounter prefix_state = PQueryCounter ?s"
    by (rule verifier_composition_fri_prefix_outcome_basicD
        [OF prefix[unfolded header_eq]])
  have prefix_counter: "PQueryCounter prefix_state = PQueryCounter ?s"
    using prefix_basic by simp
  have local_counter: "PQueryCounter query_state = 0"
    using query_counter prefix_counter
    unfolding verifier_state_from_adversary_def by simp
  have prefix_res:
    "length f_fl = ceil_log clength \<and>
     length as = length spec \<and>
     length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript ?s =
       [fr] @ map snd f_fl @ [f_final] @ as @ [dg] @
       map snd fl @ PTranscript prefix_state \<and>
     PState prefix_state =
       foldl concat
        (concat
          (foldl concat
            (concat
              (foldl concat (concat (PState ?s) fr) (map snd f_fl))
              f_final)
            as)
          dg)
        (map snd fl)"
    using prefix_basic by simp
  from read_outcome[OF read_final] obtain rest_query where
    tr_prefix: "PTranscript prefix_state = final # rest_query"
    and state_query:
      "PState query_state = concat (PState prefix_state) final"
    and tr_read_query: "PTranscript query_state = rest_query"
    by blast
  have lookup_query:
    "\<And>i x. fmlookup (HashMap query_state)
        (QueryIndexChallenge i x) =
      fmlookup (HashMap ?s) (QueryIndexChallenge i x)"
  proof -
    have query_state_eq:
      "query_state =
        prefix_state\<lparr>PState := concat (PState prefix_state) final,
          PTranscript := rest_query\<rparr>"
      using read_nonempty_outcome[OF read_final tr_prefix] by simp
    have hash_prefix:
      "\<And>i x. fmlookup (HashMap prefix_state)
          (QueryIndexChallenge i x) =
        fmlookup (HashMap ?s) (QueryIndexChallenge i x)"
      by (rule verifier_composition_fri_prefix_preserves_query_lookup
          [OF prefix[unfolded header_eq]])
    show "\<And>i x. fmlookup (HashMap query_state)
        (QueryIndexChallenge i x) =
      fmlookup (HashMap ?s) (QueryIndexChallenge i x)"
      using query_state_eq hash_prefix by simp
  qed
  have len_trace_actual: "length (map snd f_fl) = ceil_log clength"
    using prefix_res by simp
  have len_alpha_actual: "length as = length spec"
    using prefix_res by simp
  have len_comp_actual:
    "length (map snd fl) = ceil_log (to_nat dg + 1)"
    using prefix_res by simp
  have transcript_prefix_actual:
    "PTranscript ?s =
      [fr] @ map snd f_fl @ [f_final] @ as @ [dg] @
      map snd fl @ PTranscript prefix_state"
    using prefix_res by simp
  have header_actual:
    "verifier_header_transcript ?s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    by (rule verifier_header_transcript_from_prefix_read
        [OF len_trace_actual len_alpha_actual len_comp_actual
          transcript_prefix_actual tr_prefix tr_read_query])
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
  have header_unique:
    "fr = staged_trace_root data \<and>
     map snd f_fl = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     map snd fl = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     PTranscript query_state = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header_actual staged_header]
    by simp
  have prefix_state_query:
    "PState query_state = staged_query_start_hash data"
    using state_query prefix_res header_unique
    unfolding staged_query_start_hash_def
      staged_composition_fri_start_hash_def
      staged_trace_fri_start_hash_def
    by simp
  have chunks_eq: "query_chunks = staged_query_chunks data"
  proof -
    from checked_staged_transcript_program_query_chunks_match_verifier_lengths
        [OF builder]
    obtain staged_query_idxs where
      staged_match:
        "staged_query_chunks_match_verifier_lengths data staged_query_idxs"
      by blast
    have query_idxs_len: "length query_idxs = rounds"
      using query_idxs_eq len_raw by simp
    have staged_match_query_idxs:
      "staged_query_chunks_match_verifier_lengths data query_idxs"
      by (rule staged_query_chunks_match_verifier_lengths_transfer
          [OF staged_match query_idxs_len])
    have parser_chunk_len:
      "\<And>i. i < rounds \<Longrightarrow>
        length (query_chunks ! i) =
          verifier_query_round_transcript_length (query_idxs ! i)
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)"
    proof -
      fix i
      assume i_bound: "i < rounds"
      show
        "length (query_chunks ! i) =
          verifier_query_round_transcript_length (query_idxs ! i)
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)"
        using verifier_query_round_chunk_length
            [OF round_chunks[OF i_bound]] header_unique
        by simp
    qed
    have concat_staged:
      "List.concat query_chunks @ PTranscript final_state =
        List.concat (staged_query_chunks data)"
      using tr_query header_unique by simp
    then show ?thesis
      using query_chunks_eq_staged_if_matching_lengths
          [OF len_chunks concat_staged parser_chunk_len staged_match_query_idxs]
      by simp
  qed
  have raw_eq:
    "\<And>i. i < rounds \<Longrightarrow> raw_idxs ! i = raw_idxs_hit ! i"
    using lookups lookup_hit local_counter prefix_state_query chunks_eq
    by simp
  have raw_idxs_eq: "raw_idxs = raw_idxs_hit"
    by (rule nth_equalityI)
      (use len_raw len_hit raw_eq in simp_all)
  have raw_in: "raw_idxs \<in> query_index_raw_list_preimage Q"
    unfolding query_index_raw_list_preimage_def
    using len_raw raw_idxs_eq query_hit_in query_hit_eq by blast
  have local_fresh:
    "query_index_list_path_fresh query_state rounds query_chunks raw_idxs"
    unfolding query_index_list_path_fresh_def
    using len_raw len_chunks fresh_hit local_counter prefix_state_query
      chunks_eq lookup_query
    by simp
  show ?thesis
    by (rule verifier_after_composition_fri_raw_list_path_hitI
        [where final=final and query_state=query_state and raws=raw_idxs
          and chunks=query_chunks and t=final_state and results=result,
          OF read_final raw_in len_raw len_chunks state_final local_fresh
            lookups out_eq])
qed

lemma verifier_after_composition_fri_query_index_list_path_fresh_product_bound_after_prefix:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "Q \<subseteq> fri_query_index_list_space"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix:
      "Some (header, prefix_state) \<in>
        set_dist
          (execute verifier_composition_fri_prefix
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
  shows
    "wp_event (verifier_after_composition_fri header)
      (\<lambda>out.
        staged_security_with_data_state_query_index_list_path_fresh Q
          (case out of
            None \<Rightarrow> None
          | Some (result, final_state) \<Rightarrow>
              Some (((data, attacker_state), result), final_state)))
      prefix_state
      \<le> nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  let ?P =
    "\<lambda>out.
      staged_security_with_data_state_query_index_list_path_fresh Q
        (case out of
          None \<Rightarrow> None
        | Some (result, final_state) \<Rightarrow>
            Some (((data, attacker_state), result), final_state))"
  have event_mono:
    "wp_event (verifier_after_composition_fri header)
      ?P prefix_state
    \<le>
    wp_event (verifier_after_composition_fri header)
      (verifier_after_composition_fri_raw_list_path_hit prefix_state Q)
      prefix_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume suffix:
      "out \<in>
        set_dist
          (execute (verifier_after_composition_fri header) prefix_state)"
      and hit:
        "staged_security_with_data_state_query_index_list_path_fresh Q
          (case out of
            None \<Rightarrow> None
          | Some (result, final_state) \<Rightarrow>
              Some (((data, attacker_state), result), final_state))"
    show "verifier_after_composition_fri_raw_list_path_hit prefix_state Q out"
      by (rule
          verifier_after_composition_fri_query_index_list_path_fresh_imp_raw_hit_after_prefix
          [OF wf controlled builder prefix suffix hit])
  qed
  also have "... \<le>
    nnreal (card Q) *
      (1 / nnreal (card query_sample_space)) ^ rounds"
    by (rule wp_verifier_after_composition_fri_raw_list_path_product_bound
        [OF subset])
  finally show ?thesis .
qed

lemma verify_monad_query_index_list_path_fresh_product_bound_after_builder:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "Q \<subseteq> fri_query_index_list_space"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
  shows
    "wp_event verify_monad
      (\<lambda>out.
        staged_security_with_data_state_query_index_list_path_fresh Q
          (case out of
            None \<Rightarrow> None
          | Some (result, final_state) \<Rightarrow>
              Some (((data, attacker_state), result), final_state)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  note verify_decomp = verify_monad_composition_fri_decomposition
  show ?thesis
    unfolding verify_decomp
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> staged_security_with_data_state_query_index_list_path_fresh Q
      (case None of None \<Rightarrow> None
        | Some (result, final_state) \<Rightarrow>
            Some (((data, attacker_state), result), final_state))"
      by simp
  next
    fix header prefix_state
    assume prefix:
      "Some (header, prefix_state) \<in>
        set_dist (execute verifier_composition_fri_prefix ?s)"
    show
      "wp_event (verifier_after_composition_fri header)
        (\<lambda>out.
          staged_security_with_data_state_query_index_list_path_fresh Q
            (case out of
              None \<Rightarrow> None
            | Some (result, final_state) \<Rightarrow>
                Some (((data, attacker_state), result), final_state)))
        prefix_state
      \<le> nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
      by (rule
          verifier_after_composition_fri_query_index_list_path_fresh_product_bound_after_prefix
          [OF wf controlled subset builder prefix])
  qed
qed

lemma checked_staged_security_with_data_state_query_index_list_path_fresh_product_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_index_list_path_fresh Q)
      adversary_initial_state \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
proof -
  let ?P = "staged_security_with_data_state_query_index_list_path_fresh Q"
  have none: "\<not> ?P None"
    by simp
  have cont_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (\<lambda>out.
          ?P
            (case out of
              None \<Rightarrow> None
            | Some (result, final_state) \<Rightarrow>
                Some (((data, attacker_state), result), final_state)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        \<le> nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds"
    by (rule verify_monad_query_index_list_path_fresh_product_bound_after_builder
        [OF wf controlled subset])
  show ?thesis
    by (rule checked_staged_security_with_data_state_bound_from_data_cont
        [OF none cont_bound])
qed

lemma checked_staged_security_with_data_state_query_index_list_hit_exact_product_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule
      checked_staged_security_with_data_state_query_index_list_hit_bound_from_path_fresh
      [OF wf controlled
        checked_staged_security_with_data_state_query_index_list_path_fresh_product_bound
          [OF wf controlled subset]])

lemma checked_staged_security_trace_fri_query_index_list_set_hit_exact_product_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule
      checked_staged_security_trace_fri_query_index_list_set_hit_bound_from_path_fresh
      [OF wf controlled
        checked_staged_security_with_data_state_query_index_list_path_fresh_product_bound
          [OF wf controlled subset]])

lemma checked_staged_security_composition_fri_query_index_list_set_hit_exact_product_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule
      checked_staged_security_composition_fri_query_index_list_set_hit_bound_from_path_fresh
      [OF wf controlled
        checked_staged_security_with_data_state_query_index_list_path_fresh_product_bound
          [OF wf controlled subset]])

lemma checked_staged_security_trace_fri_query_challenge_pair_set_hit_exact_product_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection: "fst ` P \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule
      checked_staged_security_trace_fri_query_challenge_pair_set_hit_bound_from_path_fresh
      [OF wf controlled projection
        checked_staged_security_with_data_state_query_index_list_path_fresh_product_bound
          [OF wf controlled subset]])

lemma checked_staged_security_composition_fri_query_challenge_pair_set_hit_exact_product_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection: "\<And>dg. fst ` P dg \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule
      checked_staged_security_composition_fri_query_challenge_pair_set_hit_bound_from_path_fresh
      [OF wf controlled projection
        checked_staged_security_with_data_state_query_index_list_path_fresh_product_bound
          [OF wf controlled subset]])

end

end
