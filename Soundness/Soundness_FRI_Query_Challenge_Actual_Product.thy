(*  Title:      Stark/Soundness_FRI_Query_Challenge_Actual_Product.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_Challenge_Actual_Product
  imports Soundness_FRI_Query_Challenge_Fresh_Split
begin

text \<open>
  Verifier-local pair-product bounds with actual FRI challenge-path freshness.

  This replaces the global trace-FRI future-fresh premise in the fixed
  challenge product bound by the concrete freshness evidence carried by
  the trace FRI challenge-list freshness event.
\<close>

context soundness
begin

lemma verifier_trace_fri_prefix_preserves_query_lookup:
  assumes outcome:
    "Some ((fr, f_fl), t) \<in>
      set_dist (execute verifier_trace_fri_prefix s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
proof -
  let ?key = "QueryIndexChallenge i x"
  from outcome obtain s1 s2 where
    read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    and trace_fri:
      "Some (f_fl, s2) \<in>
        set_dist (execute
          (ntimes receive_trace_fri_commits (ceil_log clength)) s1)"
    and ret:
      "Some ((fr, f_fl), t) \<in> set_dist (execute (return (fr, f_fl)) s2)"
    unfolding verifier_trace_fri_prefix_def
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
  have t_eq: "t = s2"
    using ret by simp
  show ?thesis
    using lookup_s1 lookup_s2 unfolding t_eq by simp
qed

lemma wp_trace_fri_query_challenge_pair_set_hit_fixed_challenge_actual_fresh_bound:
  assumes query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenges_space:
      "challenges \<in> fri_challenge_space (ceil_log clength)"
    and projection:
      "fst ` (Pairs \<inter> (UNIV \<times> {challenges})) \<subseteq> Queries"
    and subset: "Queries \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad
      (\<lambda>out. trace_fri_challenge_list_fresh_hit s {challenges} out \<and>
        trace_fri_query_challenge_pair_set_hit s Pairs out) s \<le>
      (1 / nnreal (CARD('f) ^ ceil_log clength)) *
        (nnreal (card Queries) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
proof -
  let ?Hit =
    "\<lambda>out. trace_fri_challenge_list_fresh_hit s {challenges} out \<and>
      trace_fri_query_challenge_pair_set_hit s Pairs out"
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl), _) \<Rightarrow>
          map fst f_fl = challenges \<and>
          trace_fri_challenge_path_fresh s fr (map snd f_fl)
            (length (map snd f_fl))"
  let ?D =
    "nnreal (card Queries) *
      (1 / nnreal (card query_sample_space)) ^ rounds"
  have bind_bound:
    "wp_event verify_monad ?Hit s \<le>
      wp_event verifier_trace_fri_prefix ?Head s * ?D"
    unfolding verify_monad_trace_fri_decomposition
  proof (rule wp_event_bind_bound_by_head_and_cont)
  show "\<not> ?Hit None"
    unfolding trace_fri_challenge_list_fresh_hit_def
      trace_fri_query_challenge_pair_set_hit_def
      accepted_fri_challenges_def
      accepted_fri_opening_transcript_def
    by blast
next
  fix header prefix_state
  assume prefix:
    "Some (header, prefix_state) \<in>
      set_dist (execute verifier_trace_fri_prefix s)"
    and not_head: "\<not> ?Head (Some (header, prefix_state))"
  obtain fr f_fl where header_eq: "header = (fr, f_fl)"
    by (cases header) auto
  have not_head':
    "map fst f_fl \<noteq> challenges \<or>
      \<not> trace_fri_challenge_path_fresh s fr (map snd f_fl)
        (length (map snd f_fl))"
    using not_head unfolding header_eq by simp
  have zero_le:
    "wp_event (verifier_after_trace_fri header) ?Hit prefix_state \<le> 0"
  proof (rule order_trans)
    show "wp_event (verifier_after_trace_fri header) ?Hit prefix_state \<le>
        wp_event (verifier_after_trace_fri header)
          (\<lambda>_. False) prefix_state"
    proof (rule wp_event_mono_on_support)
      fix out
      assume suffix:
        "out \<in>
          set_dist (execute (verifier_after_trace_fri header) prefix_state)"
        and hit: "?Hit out"
      from hit obtain result :: "unit list" and final_state where out_eq:
        "out = Some (result, final_state)"
        unfolding trace_fri_challenge_list_fresh_hit_def
          accepted_fri_challenges_def
        by blast
      have prefix':
        "Some ((fr, f_fl), prefix_state) \<in>
          set_dist (execute verifier_trace_fri_prefix s)"
        using prefix header_eq by simp
      have suffix':
        "Some (result, final_state) \<in>
          set_dist
            (execute (verifier_after_trace_fri (fr, f_fl)) prefix_state)"
        using suffix header_eq out_eq by simp
      from hit obtain trace_roots trace_bs trace_final fri_dg
          composition_roots composition_bs composition_final query_idxs
          trace_round_layers composition_round_layers where
        openings:
          "accepted_fri_opening_transcript s out trace_roots trace_bs
            trace_final fri_dg composition_roots composition_bs
            composition_final query_idxs trace_round_layers
            composition_round_layers"
        unfolding trace_fri_query_challenge_pair_set_hit_def by blast
      have pair_challenges:
        "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
        by (rule accepted_fri_opening_transcript_challenges[OF openings])
      from hit obtain trace_bs' dg' comp_bs' where
        fresh_challenges:
          "accepted_fri_challenges s out trace_bs' dg' comp_bs'"
        and trace_bs'_in: "trace_bs' \<in> {challenges}"
        unfolding trace_fri_challenge_list_fresh_hit_def by blast
      have trace_bs_eq: "trace_bs = trace_bs'"
        using accepted_fri_challenges_unique
          [OF pair_challenges[unfolded out_eq]
            fresh_challenges[unfolded out_eq]]
        by simp
      have prefix_trace_eq: "trace_bs = map fst f_fl"
        by (rule verifier_after_trace_fri_header_agrees_with_accepted_challenges
            [OF prefix' suffix' pair_challenges[unfolded out_eq]])
      have fresh_hit:
        "trace_fri_challenge_list_fresh_hit s {challenges}
          (Some (result, final_state))"
        using hit out_eq by simp
      have concrete_fresh:
        "trace_fri_challenge_path_fresh s fr (map snd f_fl)
          (length (map snd f_fl))"
        by (rule verifier_after_trace_fri_header_roots_agree_with_fresh_hit
            [OF prefix' suffix' fresh_hit])
      have head_holds:
        "map fst f_fl = challenges \<and>
          trace_fri_challenge_path_fresh s fr (map snd f_fl)
            (length (map snd f_fl))"
        using prefix_trace_eq trace_bs_eq trace_bs'_in concrete_fresh by simp
      show False
        using not_head' head_holds by blast
    qed
  next
    show "wp_event (verifier_after_trace_fri header)
        (\<lambda>_. False) prefix_state \<le> 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
  qed
  show "wp_event (verifier_after_trace_fri header) ?Hit prefix_state = 0"
    by (rule antisym[OF zero_le]) simp
next
  fix header prefix_state
  assume prefix:
    "Some (header, prefix_state) \<in>
      set_dist (execute verifier_trace_fri_prefix s)"
    and head: "?Head (Some (header, prefix_state))"
  obtain fr f_fl where header_eq: "header = (fr, f_fl)"
    by (cases header) auto
  have f_fl_eq: "map fst f_fl = challenges"
    using head unfolding header_eq by simp
  have future_prefix: "query_future_fresh prefix_state"
    by (rule verifier_trace_fri_prefix_preserves_query_future_fresh_exact
        [OF query_future prefix])
  have counter_prefix: "PQueryCounter prefix_state = PQueryCounter s"
    using verifier_trace_fri_prefix_outcome[OF prefix[unfolded header_eq]]
    by simp
	  have event_bound:
	    "wp_event (verifier_after_trace_fri header)
	      (\<lambda>out. \<exists>query_idxs \<in> Queries.
	        query_rounds_index_list_hit s query_idxs rounds out)
	      prefix_state \<le> ?D"
    by (rule wp_verifier_after_trace_fri_query_index_list_set_bound
        [OF future_prefix counter_prefix raw_bound subset])
  have hit_to_query:
    "wp_event (verifier_after_trace_fri header) ?Hit prefix_state \<le>
      wp_event (verifier_after_trace_fri header)
        (\<lambda>out. \<exists>query_idxs \<in> Queries.
          query_rounds_index_list_hit s query_idxs rounds out) prefix_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume suffix:
      "out \<in>
        set_dist (execute (verifier_after_trace_fri header) prefix_state)"
      and hit: "?Hit out"
    from hit obtain trace_roots trace_bs trace_final fri_dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers where
      openings:
        "accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final fri_dg composition_roots composition_bs
          composition_final query_idxs trace_round_layers
          composition_round_layers"
      and pair: "(query_idxs, trace_bs) \<in> Pairs"
      unfolding trace_fri_query_challenge_pair_set_hit_def by blast
    from openings obtain result :: "unit list" and final_state where out_eq:
      "out = Some (result, final_state)"
      unfolding accepted_fri_opening_transcript_def by blast
    have prefix':
      "Some ((fr, f_fl), prefix_state) \<in>
        set_dist (execute verifier_trace_fri_prefix s)"
      using prefix header_eq by simp
    have suffix':
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_trace_fri (fr, f_fl)) prefix_state)"
      using suffix header_eq out_eq by simp
    have challenges_openings:
      "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
      by (rule accepted_fri_opening_transcript_challenges[OF openings])
    have trace_eq: "trace_bs = map fst f_fl"
      by (rule verifier_after_trace_fri_header_agrees_with_accepted_challenges
          [OF prefix' suffix' challenges_openings[unfolded out_eq]])
    have query_in: "query_idxs \<in> Queries"
    proof -
      have "query_idxs \<in> fst ` (Pairs \<inter> (UNIV \<times> {challenges}))"
        using pair trace_eq f_fl_eq by force
      then show ?thesis
        using projection by blast
    qed
    have query_hit:
      "query_rounds_index_list_hit s query_idxs rounds out"
      by (rule accepted_fri_opening_transcript_imp_query_rounds_index_list_hit
          [OF openings])
    show "\<exists>query_idxs \<in> Queries.
      query_rounds_index_list_hit s query_idxs rounds out"
      using query_in query_hit by blast
  qed
  show "wp_event (verifier_after_trace_fri header) ?Hit prefix_state \<le> ?D"
    by (rule order_trans[OF hit_to_query event_bound])
  qed
  have head_bound:
    "wp_event verifier_trace_fri_prefix ?Head s \<le>
      1 / nnreal (CARD('f) ^ ceil_log clength)"
  proof -
    let ?HeadSet =
      "\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((fr, f_fl), _) \<Rightarrow>
            map fst f_fl \<in> {challenges} \<and>
            trace_fri_challenge_path_fresh s fr (map snd f_fl)
              (length (map snd f_fl))"
    have subset: "{challenges} \<subseteq> fri_challenge_space (ceil_log clength)"
      using challenges_space by simp
    have mono:
      "wp_event verifier_trace_fri_prefix ?Head s \<le>
        wp_event verifier_trace_fri_prefix ?HeadSet s"
      by (rule wp_event_mono) (auto split: option.splits prod.splits)
    have "wp_event verifier_trace_fri_prefix ?Head s \<le>
        nnreal (card {challenges}) /
          nnreal (CARD('f) ^ ceil_log clength)"
      by (rule order_trans[OF mono])
        (rule wp_verifier_trace_fri_prefix_challenge_list_actual_fresh_bound
          [OF subset])
    then show ?thesis
      by simp
  qed
  have "wp_event verify_monad ?Hit s \<le>
      wp_event verifier_trace_fri_prefix ?Head s * ?D"
    by (rule bind_bound)
  also have "... \<le>
      (1 / nnreal (CARD('f) ^ ceil_log clength)) * ?D"
    by (rule mult_right_mono[OF head_bound]) simp
  finally show ?thesis .
qed

lemma wp_trace_fri_query_challenge_pair_set_hit_challenge_fresh_fiber_sum:
  assumes query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenge_subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and projection:
      "\<And>challenges.
        challenges \<in> B \<Longrightarrow>
        fst ` (P \<inter> (UNIV \<times> {challenges})) \<subseteq> Q challenges"
    and subset:
      "\<And>challenges. challenges \<in> B \<Longrightarrow>
        Q challenges \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad
      (\<lambda>out. trace_fri_challenge_list_fresh_hit s B out \<and>
        trace_fri_query_challenge_pair_set_hit s P out) s \<le>
      (\<Sum>challenges \<in> B.
        (1 / nnreal (CARD('f) ^ ceil_log clength)) *
          (nnreal (card (Q challenges)) *
            (1 / nnreal (card query_sample_space)) ^ rounds))"
proof -
  let ?E =
    "\<lambda>challenges out.
      trace_fri_challenge_list_fresh_hit s {challenges} out \<and>
      trace_fri_query_challenge_pair_set_hit s P out"
  let ?C =
    "\<lambda>challenges.
      (1 / nnreal (CARD('f) ^ ceil_log clength)) *
        (nnreal (card (Q challenges)) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
  have split:
    "wp_event verify_monad
      (\<lambda>out. trace_fri_challenge_list_fresh_hit s B out \<and>
        trace_fri_query_challenge_pair_set_hit s P out) s \<le>
      wp_event verify_monad
        (\<lambda>out. \<exists>challenges \<in> B. ?E challenges out) s"
  proof (rule wp_event_mono)
    fix out
    assume hit:
      "trace_fri_challenge_list_fresh_hit s B out \<and>
       trace_fri_query_challenge_pair_set_hit s P out"
    then obtain trace_bs :: "'f list" and dg :: 'f and comp_bs :: "'f list"
        and fr :: 'f and trace_roots :: "'f list" and trace_final :: 'f
        and as :: "'f list" and composition_roots :: "'f list"
        and final :: 'f and rest :: "'f list" where
      accepted:
        "accepted_fri_challenges s out trace_bs dg comp_bs"
      and header:
        "verifier_header_transcript s fr trace_roots trace_final as dg
          composition_roots final rest"
      and trace_bs_in: "trace_bs \<in> B"
      and fresh_path:
        "trace_fri_challenge_path_fresh s fr trace_roots
          (length trace_roots)"
      unfolding trace_fri_challenge_list_fresh_hit_def by blast
    have singleton_fresh:
      "trace_fri_challenge_list_fresh_hit s {trace_bs} out"
      unfolding trace_fri_challenge_list_fresh_hit_def
    proof (intro exI conjI)
      show "accepted_fri_challenges s out trace_bs dg comp_bs"
        by (rule accepted)
      show "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots final rest"
        by (rule header)
      show "trace_bs \<in> {trace_bs}"
        by simp
      show "trace_fri_challenge_path_fresh s fr trace_roots
        (length trace_roots)"
        by (rule fresh_path)
    qed

    show "\<exists>challenges \<in> B. ?E challenges out"
      using singleton_fresh hit trace_bs_in
      by (intro bexI[of _ trace_bs]) simp_all
  qed
  also have "... \<le> (\<Sum>challenges \<in> B. ?C challenges)"
  proof (rule wp_event_finite_union_bound_fri_exact)
    show "finite B"
      using challenge_subset by (rule finite_subset)
        (rule finite_fri_challenge_space)
  next
    fix challenges
    assume challenges_in: "challenges \<in> B"
    have challenges_space:
      "challenges \<in> fri_challenge_space (ceil_log clength)"
      using challenge_subset challenges_in by blast
    show "wp_event verify_monad (?E challenges) s \<le> ?C challenges"
      by (rule
          wp_trace_fri_query_challenge_pair_set_hit_fixed_challenge_actual_fresh_bound
          [OF query_future raw_bound challenges_space
            projection[OF challenges_in] subset[OF challenges_in]])
  qed
  finally show ?thesis .
qed

lemma wp_composition_fri_query_challenge_pair_set_hit_fixed_challenge_actual_fresh_bound:
  assumes query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenges_space:
      "challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and projection:
      "fst ` (Pairs dg \<inter> (UNIV \<times> {challenges})) \<subseteq> Queries"
    and subset: "Queries \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad
      (\<lambda>out.
        composition_fri_challenge_list_fresh_hit s
          (\<lambda>dg'. if dg' = dg then {challenges} else {}) out \<and>
        composition_fri_query_challenge_pair_set_hit s Pairs out) s \<le>
      (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
        (nnreal (card Queries) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
proof -
  let ?B = "\<lambda>dg'. if dg' = dg then {challenges} else {}"
  let ?Hit =
    "\<lambda>out. composition_fri_challenge_list_fresh_hit s ?B out \<and>
      composition_fri_query_challenge_pair_set_hit s Pairs out"
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl, f_final, as, dg', fl), _) \<Rightarrow>
          dg' = dg \<and> map fst fl = challenges \<and>
          composition_fri_challenge_path_fresh s fr (map snd f_fl)
            f_final as dg' (map snd fl) (length (map snd fl))"
  let ?D =
    "nnreal (card Queries) *
      (1 / nnreal (card query_sample_space)) ^ rounds"
  have bind_bound:
    "wp_event verify_monad ?Hit s \<le>
      wp_event verifier_composition_fri_prefix ?Head s * ?D"
    unfolding verify_monad_composition_fri_decomposition
  proof (rule wp_event_bind_bound_by_head_and_cont)
  show "\<not> ?Hit None"
    unfolding composition_fri_challenge_list_fresh_hit_def
      composition_fri_query_challenge_pair_set_hit_def
      accepted_fri_challenges_def
      accepted_fri_opening_transcript_def
    by blast
next
  fix header prefix_state
  assume prefix:
    "Some (header, prefix_state) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
    and not_head: "\<not> ?Head (Some (header, prefix_state))"
  obtain fr f_fl f_final as dg' fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg', fl)"
    by (cases header) auto
  have not_head':
    "dg' \<noteq> dg \<or> map fst fl \<noteq> challenges \<or>
      \<not> composition_fri_challenge_path_fresh s fr (map snd f_fl)
        f_final as dg' (map snd fl) (length (map snd fl))"
    using not_head unfolding header_eq by simp
  have zero_le:
    "wp_event (verifier_after_composition_fri header) ?Hit prefix_state \<le> 0"
  proof (rule order_trans)
    show "wp_event (verifier_after_composition_fri header) ?Hit prefix_state \<le>
        wp_event (verifier_after_composition_fri header)
          (\<lambda>_. False) prefix_state"
    proof (rule wp_event_mono_on_support)
      fix out
      assume suffix:
        "out \<in>
          set_dist
            (execute (verifier_after_composition_fri header) prefix_state)"
        and hit: "?Hit out"
      from hit obtain result :: "unit list" and final_state where out_eq:
        "out = Some (result, final_state)"
        unfolding composition_fri_challenge_list_fresh_hit_def
          accepted_fri_challenges_def
        by blast
      have prefix':
        "Some ((fr, f_fl, f_final, as, dg', fl), prefix_state) \<in>
          set_dist (execute verifier_composition_fri_prefix s)"
        using prefix header_eq by simp
      have suffix':
        "Some (result, final_state) \<in>
          set_dist
            (execute
              (verifier_after_composition_fri
                (fr, f_fl, f_final, as, dg', fl))
              prefix_state)"
        using suffix header_eq out_eq by simp
      from hit obtain trace_roots trace_bs trace_final fri_dg
          composition_roots composition_bs composition_final query_idxs
          trace_round_layers composition_round_layers where
        openings:
          "accepted_fri_opening_transcript s out trace_roots trace_bs
            trace_final fri_dg composition_roots composition_bs
            composition_final query_idxs trace_round_layers
            composition_round_layers"
        unfolding composition_fri_query_challenge_pair_set_hit_def by blast
      have pair_challenges:
        "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
        by (rule accepted_fri_opening_transcript_challenges[OF openings])
      from hit obtain trace_bs' dg'' comp_bs' where
        fresh_challenges:
          "accepted_fri_challenges s out trace_bs' dg'' comp_bs'"
        and comp_bs'_in:
          "comp_bs' \<in> (if dg'' = dg then {challenges} else {})"
        unfolding composition_fri_challenge_list_fresh_hit_def by blast
      have challenge_eqs:
        "fri_dg = dg'' \<and> composition_bs = comp_bs'"
        using accepted_fri_challenges_unique
          [OF pair_challenges[unfolded out_eq]
            fresh_challenges[unfolded out_eq]]
        by simp
      have prefix_eqs:
        "fri_dg = dg' \<and> composition_bs = map fst fl"
        by (rule verifier_after_composition_fri_header_agrees_with_accepted_challenges
            [OF prefix' suffix' pair_challenges[unfolded out_eq]])
      have fresh_hit:
        "composition_fri_challenge_list_fresh_hit s ?B
          (Some (result, final_state))"
        using hit out_eq by simp
      have concrete_fresh:
        "composition_fri_challenge_path_fresh s fr (map snd f_fl)
          f_final as dg' (map snd fl) (length (map snd fl))"
        by (rule verifier_after_composition_fri_header_roots_agree_with_fresh_hit
            [OF prefix' suffix' fresh_hit])
      have dg_eq': "dg'' = dg"
        using comp_bs'_in by (cases "dg'' = dg") auto
      have comp_bs'_eq: "comp_bs' = map fst fl"
        using challenge_eqs prefix_eqs by simp
      have comp_bs'_challenges: "comp_bs' = challenges"
        using comp_bs'_in dg_eq' by simp
      have dg'_eq: "dg' = dg"
        using challenge_eqs prefix_eqs dg_eq' by simp
      have fl_challenges: "map fst fl = challenges"
        using comp_bs'_eq comp_bs'_challenges by simp
      have head_holds:
        "dg' = dg \<and> map fst fl = challenges \<and>
          composition_fri_challenge_path_fresh s fr (map snd f_fl)
            f_final as dg' (map snd fl) (length (map snd fl))"
        using dg'_eq fl_challenges concrete_fresh by simp
      show False
        using not_head' head_holds by blast
    qed
  next
    show "wp_event (verifier_after_composition_fri header)
        (\<lambda>_. False) prefix_state \<le> 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
  qed
  show "wp_event (verifier_after_composition_fri header) ?Hit prefix_state = 0"
    by (rule antisym[OF zero_le]) simp
next
  fix header prefix_state
  assume prefix:
    "Some (header, prefix_state) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
    and head: "?Head (Some (header, prefix_state))"
  obtain fr f_fl f_final as dg' fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg', fl)"
    by (cases header) auto
  have dg_eq: "dg' = dg" and fl_eq: "map fst fl = challenges"
    using head unfolding header_eq by simp_all
  have future_prefix: "query_future_fresh prefix_state"
    by (rule verifier_composition_fri_prefix_preserves_query_future_fresh
        [OF query_future prefix])
  have counter_prefix: "PQueryCounter prefix_state = PQueryCounter s"
    using verifier_composition_fri_prefix_outcome[OF prefix[unfolded header_eq]]
    by simp
	  have event_bound:
	    "wp_event (verifier_after_composition_fri header)
	      (\<lambda>out. \<exists>query_idxs \<in> Queries.
	        query_rounds_index_list_hit s query_idxs rounds out)
	      prefix_state \<le> ?D"
    by (rule wp_verifier_after_composition_fri_query_index_list_set_bound
        [OF future_prefix counter_prefix raw_bound subset])
  have hit_to_query:
    "wp_event (verifier_after_composition_fri header) ?Hit prefix_state \<le>
      wp_event (verifier_after_composition_fri header)
        (\<lambda>out. \<exists>query_idxs \<in> Queries.
          query_rounds_index_list_hit s query_idxs rounds out) prefix_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume suffix:
      "out \<in>
        set_dist
          (execute (verifier_after_composition_fri header) prefix_state)"
      and hit: "?Hit out"
    from hit obtain trace_roots trace_bs trace_final fri_dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers where
      openings:
        "accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final fri_dg composition_roots composition_bs
          composition_final query_idxs trace_round_layers
          composition_round_layers"
      and pair: "(query_idxs, composition_bs) \<in> Pairs fri_dg"
      unfolding composition_fri_query_challenge_pair_set_hit_def by blast
    from openings obtain result :: "unit list" and final_state where out_eq:
      "out = Some (result, final_state)"
      unfolding accepted_fri_opening_transcript_def by blast
    have prefix':
      "Some ((fr, f_fl, f_final, as, dg', fl), prefix_state) \<in>
        set_dist (execute verifier_composition_fri_prefix s)"
      using prefix header_eq by simp
    have suffix':
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (verifier_after_composition_fri
              (fr, f_fl, f_final, as, dg', fl))
            prefix_state)"
      using suffix header_eq out_eq by simp
    have challenges_openings:
      "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
      by (rule accepted_fri_opening_transcript_challenges[OF openings])
    have eqs: "fri_dg = dg' \<and> composition_bs = map fst fl"
      by (rule verifier_after_composition_fri_header_agrees_with_accepted_challenges
          [OF prefix' suffix' challenges_openings[unfolded out_eq]])
    have query_in: "query_idxs \<in> Queries"
    proof -
      have "query_idxs \<in> fst ` (Pairs dg \<inter> (UNIV \<times> {challenges}))"
        using pair eqs dg_eq fl_eq by force
      then show ?thesis
        using projection by blast
    qed
    have query_hit:
      "query_rounds_index_list_hit s query_idxs rounds out"
      by (rule accepted_fri_opening_transcript_imp_query_rounds_index_list_hit
          [OF openings])
    show "\<exists>query_idxs \<in> Queries.
      query_rounds_index_list_hit s query_idxs rounds out"
      using query_in query_hit by blast
  qed
  show "wp_event (verifier_after_composition_fri header) ?Hit prefix_state \<le>
      ?D"
    by (rule order_trans[OF hit_to_query event_bound])
  qed
  have head_bound:
    "wp_event verifier_composition_fri_prefix ?Head s \<le>
      1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
  proof -
    let ?B = "\<lambda>dg'. if dg' = dg then {challenges} else {}"
    let ?HeadSet =
      "\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((fr, f_fl, f_final, as, dg', fl), _) \<Rightarrow>
            map fst fl \<in> ?B dg' \<and>
            composition_fri_challenge_path_fresh s fr (map snd f_fl)
              f_final as dg' (map snd fl) (length (map snd fl))"
    have subset:
      "\<And>dg'. ?B dg' \<subseteq>
        fri_challenge_space (ceil_log (to_nat dg' + 1))"
      using challenges_space by auto
    have bound:
      "\<And>dg'. nnreal (card (?B dg')) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg' + 1)) \<le>
        1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
      using challenges_space by auto
    have mono:
      "wp_event verifier_composition_fri_prefix ?Head s \<le>
        wp_event verifier_composition_fri_prefix ?HeadSet s"
      by (rule wp_event_mono) (auto split: option.splits prod.splits)
    show ?thesis
      by (rule order_trans[OF mono])
        (rule wp_verifier_composition_fri_prefix_challenge_list_actual_fresh_bound
          [OF subset bound])
  qed
  have "wp_event verify_monad ?Hit s \<le>
      wp_event verifier_composition_fri_prefix ?Head s * ?D"
    by (rule bind_bound)
  also have "... \<le>
      (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) * ?D"
    by (rule mult_right_mono[OF head_bound]) simp
  finally show ?thesis .
qed

lemma wp_composition_fri_query_challenge_pair_set_hit_challenge_fresh_fiber_sum:
  assumes query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenge_subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and projection:
      "\<And>dg challenges.
        challenges \<in> B dg \<Longrightarrow>
        fst ` (P dg \<inter> (UNIV \<times> {challenges})) \<subseteq>
          Q dg challenges"
    and subset:
      "\<And>dg challenges. challenges \<in> B dg \<Longrightarrow>
        Q dg challenges \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad
      (\<lambda>out. composition_fri_challenge_list_fresh_hit s B out \<and>
        composition_fri_query_challenge_pair_set_hit s P out) s \<le>
      (\<Sum>dg \<in> UNIV.
        \<Sum>challenges \<in> B dg.
          (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
            (nnreal (card (Q dg challenges)) *
              (1 / nnreal (card query_sample_space)) ^ rounds))"
proof -
  let ?I = "SIGMA dg:UNIV. B dg"
  let ?E =
    "\<lambda>p out.
      composition_fri_challenge_list_fresh_hit s
        (\<lambda>dg'. if dg' = fst p then {snd p} else {}) out \<and>
      composition_fri_query_challenge_pair_set_hit s P out"
  let ?C =
    "\<lambda>p.
      (1 / nnreal (CARD('f) ^ ceil_log (to_nat (fst p) + 1))) *
        (nnreal (card (Q (fst p) (snd p))) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
  have split:
    "wp_event verify_monad
      (\<lambda>out. composition_fri_challenge_list_fresh_hit s B out \<and>
        composition_fri_query_challenge_pair_set_hit s P out) s \<le>
      wp_event verify_monad
        (\<lambda>out. \<exists>p \<in> ?I. ?E p out) s"
  proof (rule wp_event_mono)
    fix out
    assume hit:
      "composition_fri_challenge_list_fresh_hit s B out \<and>
       composition_fri_query_challenge_pair_set_hit s P out"
    then obtain trace_bs dg comp_bs fr trace_roots trace_final as
        composition_roots final rest where
      accepted:
        "accepted_fri_challenges s out trace_bs dg comp_bs"
      and comp_bs_in: "comp_bs \<in> B dg"
      and header:
        "verifier_header_transcript s fr trace_roots trace_final as dg
          composition_roots final rest"
      and fresh_path:
        "composition_fri_challenge_path_fresh s fr trace_roots trace_final
          as dg composition_roots (length composition_roots)"
      unfolding composition_fri_challenge_list_fresh_hit_def by blast
    have singleton_fresh:
      "composition_fri_challenge_list_fresh_hit s
        (\<lambda>dg'. if dg' = dg then {comp_bs} else {}) out"
      unfolding composition_fri_challenge_list_fresh_hit_def
    proof (intro exI conjI)
      show "accepted_fri_challenges s out trace_bs dg comp_bs"
        by (rule accepted)
      show "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots final rest"
        by (rule header)
      show "comp_bs \<in> (if dg = dg then {comp_bs} else {})"
        by simp
      show "composition_fri_challenge_path_fresh s fr trace_roots trace_final
        as dg composition_roots (length composition_roots)"
        by (rule fresh_path)
    qed
    have p_in: "(dg, comp_bs) \<in> ?I"
      using comp_bs_in by simp
    have singleton_fresh':
      "composition_fri_challenge_list_fresh_hit s
        (\<lambda>dg'. if dg' = fst (dg, comp_bs) then {snd (dg, comp_bs)}
          else {}) out"
      using singleton_fresh by (simp only: fst_conv snd_conv)
    have e_hit: "?E (dg, comp_bs) out"
      using singleton_fresh' hit by simp
    show "\<exists>p \<in> ?I. ?E p out"
      using p_in e_hit by blast
  qed
  also have "... \<le> (\<Sum>p \<in> ?I. ?C p)"
  proof (rule wp_event_finite_union_bound_fri_exact)
    show "finite ?I"
      apply (rule finite_SigmaI)
      using challenge_subset finite_fri_challenge_space
       apply (auto intro: finite_subset)
      by (meson finite_fri_challenge_space rev_finite_subset)
  next
    fix p
    assume p_in: "p \<in> ?I"
    obtain dg challenges where p_eq: "p = (dg, challenges)"
      by (cases p) auto
    have challenges_in: "challenges \<in> B dg"
      using p_in p_eq by simp
    have challenges_space:
      "challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
      using challenge_subset challenges_in by blast
    show "wp_event verify_monad (?E p) s \<le> ?C p"
      unfolding p_eq
      apply (rule wp_composition_fri_query_challenge_pair_set_hit_fixed_challenge_actual_fresh_bound)
      using query_future raw_bound challenges_space
            projection[OF challenges_in] subset[OF challenges_in]
      by auto
  qed
  finally have bound:
    "wp_event verify_monad
      (\<lambda>out. composition_fri_challenge_list_fresh_hit s B out \<and>
        composition_fri_query_challenge_pair_set_hit s P out) s \<le>
      (\<Sum>p \<in> ?I. ?C p)" .
  have finite_B: "\<And>dg. finite (B dg)"
    by (meson challenge_subset finite_fri_challenge_space finite_subset)
  have sigma_eq:
    "(\<Sum>p \<in> ?I. ?C p) =
      (\<Sum>dg \<in> UNIV.
        \<Sum>challenges \<in> B dg.
          (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
            (nnreal (card (Q dg challenges)) *
              (1 / nnreal (card query_sample_space)) ^ rounds))"
    by (subst sum.Sigma) (simp_all add: finite_B case_prod_beta)
  show ?thesis
    using bound sigma_eq by simp
qed

definition staged_security_trace_fri_pair_challenge_query_path_fresh
  :: "(nat list \<times> 'f list) set \<Rightarrow> 'f list set \<Rightarrow>
      nat list set \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times>
          unit list) \<times> 'f protocol_channel) option \<Rightarrow> bool"
where
  "staged_security_trace_fri_pair_challenge_query_path_fresh P B Q out
    \<longleftrightarrow>
      staged_security_trace_fri_pair_challenge_fresh P B out \<and>
      staged_security_with_data_state_query_index_list_path_fresh Q out"

definition staged_security_composition_fri_pair_challenge_query_path_fresh
  :: "('f \<Rightarrow> (nat list \<times> 'f list) set) \<Rightarrow>
      ('f \<Rightarrow> 'f list set) \<Rightarrow> nat list set \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times>
          unit list) \<times> 'f protocol_channel) option \<Rightarrow> bool"
where
  "staged_security_composition_fri_pair_challenge_query_path_fresh P B Q out
    \<longleftrightarrow>
      staged_security_composition_fri_pair_challenge_fresh P B out \<and>
      staged_security_with_data_state_query_index_list_path_fresh Q out"

definition verifier_after_trace_fri_raw_list_path_hit
  :: "'f \<times> ('f \<times> 'f) list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> nat list set \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "verifier_after_trace_fri_raw_list_path_hit header s Q out \<longleftrightarrow>
      (\<exists>fr f_fl f_final s3 as s4 dg s5 s6 fl s7 final query_state raws.
        header = (fr, f_fl) \<and>
        Some (f_final, s3) \<in> set_dist (execute read s) \<and>
        Some (as, s4) \<in>
          set_dist (execute (mmap (replicate (length spec) alpha_round)) s3) \<and>
        Some (dg, s5) \<in> set_dist (execute read s4) \<and>
        Some ((), s6) \<in>
          set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5) \<and>
        Some (fl, s7) \<in>
          set_dist (execute
            (ntimes receive_composition_fri_commits
              (ceil_log (to_nat dg + 1))) s6) \<and>
        Some (final, query_state) \<in> set_dist (execute read s7) \<and>
        raws \<in> query_index_raw_list_preimage Q \<and>
        query_rounds_raw_list_path_hit query_state raws rounds out)"

lemma verifier_after_trace_fri_staged_query_path_fresh_imp_raw_list_path_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix:
      "Some ((fr, f_fl), prefix_state) \<in>
        set_dist
          (execute verifier_trace_fri_prefix
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and suffix:
      "out \<in>
        set_dist
          (execute (verifier_after_trace_fri (fr, f_fl)) prefix_state)"
    and hit:
      "staged_security_with_data_state_query_index_list_path_fresh Q
        (case out of
          None \<Rightarrow> None
        | Some (result, final_state) \<Rightarrow>
            Some (((data, attacker_state), result), final_state))"
  shows "verifier_after_trace_fri_raw_list_path_hit (fr, f_fl) prefix_state Q out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding staged_security_with_data_state_query_index_list_path_fresh_def
    by simp
next
  case (Some pair)
  then obtain result :: "unit list" and final_state where out_eq:
    "out = Some (result, final_state)"
    by (cases pair) simp
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from suffix[unfolded out_eq verifier_after_trace_fri_def]
  obtain f_final s3 as s4 dg s5 s6 fl s7 final query_state where
    read_trace_final:
      "Some (f_final, s3) \<in> set_dist (execute read prefix_state)"
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
    and read_final:
      "Some (final, query_state) \<in> set_dist (execute read s7)"
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
  have trace_prefix_res:
    "length f_fl = ceil_log clength \<and>
     PTranscript ?s = [fr] @ map snd f_fl @ PTranscript prefix_state \<and>
     PState prefix_state =
       foldl concat (concat (PState ?s) fr) (map snd f_fl) \<and>
     PQueryCounter prefix_state = PQueryCounter ?s"
    using verifier_trace_fri_prefix_outcome[OF prefix] by simp
  from read_outcome[OF read_trace_final] obtain rest3 where
    tr_prefix: "PTranscript prefix_state = f_final # rest3"
    and tr_s3: "PTranscript s3 = rest3"
    and state_s3: "PState s3 = concat (PState prefix_state) f_final"
    and counter_s3: "PQueryCounter s3 = PQueryCounter prefix_state"
    by blast
  have alpha_res:
    "length as = length spec \<and>
     PTranscript s3 = as @ PTranscript s4 \<and>
     PState s4 = foldl concat (PState s3) as \<and>
     PQueryCounter s4 = PQueryCounter s3"
    using mmap_alpha_round_outcome[OF alpha_out] by simp
  from read_outcome[OF read_dg] obtain rest5 where
    tr_s4: "PTranscript s4 = dg # rest5"
    and tr_s5: "PTranscript s5 = rest5"
    and state_s5: "PState s5 = concat (PState s4) dg"
    and counter_s5: "PQueryCounter s5 = PQueryCounter s4"
    by blast
  have s6_eq: "s6 = s5"
    using degree_assert unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
  have comp_res:
    "length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s6 = map snd fl @ PTranscript s7 \<and>
     PState s7 = foldl concat (PState s6) (map snd fl) \<and>
     PQueryCounter s7 = PQueryCounter s6"
    using ntimes_receive_composition_fri_commits_outcome[OF comp_fri]
    by simp
  from read_outcome[OF read_final] obtain rest_query where
    tr_s7: "PTranscript s7 = final # rest_query"
    and tr_read_query: "PTranscript query_state = rest_query"
    and state_query: "PState query_state = concat (PState s7) final"
    and counter_query_s7: "PQueryCounter query_state = PQueryCounter s7"
    by blast
  have local_counter: "PQueryCounter query_state = 0"
    using trace_prefix_res counter_s3 alpha_res counter_s5 s6_eq comp_res
      counter_query_s7
    unfolding verifier_state_from_adversary_def by simp
  have prefix_lookup:
    "\<And>i x. fmlookup (HashMap prefix_state)
        (QueryIndexChallenge i x) =
      fmlookup (HashMap ?s) (QueryIndexChallenge i x)"
    by (rule verifier_trace_fri_prefix_preserves_query_lookup[OF prefix])
  have s3_lookup:
    "HashMap s3 = HashMap prefix_state"
    by (rule read_preserves_hash_map[OF read_trace_final])
  have s4_lookup:
    "\<And>i x. fmlookup (HashMap s4) (QueryIndexChallenge i x) =
      fmlookup (HashMap s3) (QueryIndexChallenge i x)"
  proof -
    fix i x
    show "fmlookup (HashMap s4) (QueryIndexChallenge i x) =
      fmlookup (HashMap s3) (QueryIndexChallenge i x)"
    proof (rule mmap_preserves_lookup[OF _ alpha_out])
      fix m y u v
      assume m_in: "m \<in> set (replicate (length spec) alpha_round)"
        and out: "Some (y, v) \<in> set_dist (execute m u)"
      then have m_eq: "m = alpha_round"
        by simp
      show "fmlookup (HashMap v) (QueryIndexChallenge i x) =
        fmlookup (HashMap u) (QueryIndexChallenge i x)"
        using alpha_round_preserves_query_lookup[OF out[unfolded m_eq]] .
    qed
  qed
  have s5_lookup:
    "HashMap s5 = HashMap s4"
    by (rule read_preserves_hash_map[OF read_dg])
  have s7_lookup:
    "\<And>i x. fmlookup (HashMap s7) (QueryIndexChallenge i x) =
      fmlookup (HashMap s6) (QueryIndexChallenge i x)"
  proof -
    fix i x
    show "fmlookup (HashMap s7) (QueryIndexChallenge i x) =
      fmlookup (HashMap s6) (QueryIndexChallenge i x)"
    proof (rule ntimes_preserves_lookup[OF _ comp_fri])
      fix y u v
      assume out:
        "Some (y, v) \<in>
          set_dist (execute receive_composition_fri_commits u)"
      obtain b r where y_eq: "y = (b, r)"
        by (cases y) simp
      show "fmlookup (HashMap v) (QueryIndexChallenge i x) =
        fmlookup (HashMap u) (QueryIndexChallenge i x)"
        by (rule receive_composition_fri_commits_preserves_query_lookup
            [OF out[unfolded y_eq]])
    qed
  qed
  have query_lookup:
    "HashMap query_state = HashMap s7"
    by (rule read_preserves_hash_map[OF read_final])
  have header_actual:
    "verifier_header_transcript ?s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    using trace_prefix_res tr_prefix tr_s3 alpha_res tr_s4 tr_s5 s6_eq
      comp_res tr_s7 tr_read_query
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
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
    using trace_prefix_res state_s3 alpha_res state_s5 s6_eq comp_res
      state_query header_unique
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
        using verifier_query_round_chunk_length[OF round_chunks[OF i_bound]]
          header_unique
        by simp
    qed
    have concat_staged:
      "List.concat query_chunks @ PTranscript final_state =
        List.concat (staged_query_chunks data)"
      using tr_query header_unique by simp
    then show ?thesis
      using query_chunks_eq_staged_if_matching_lengths
          [OF len_chunks concat_staged parser_chunk_len
            staged_match_query_idxs]
      by simp
  qed
  from hit out_eq obtain raw_idxs_hit query_idxs_hit where
    query_hit_in: "query_idxs_hit \<in> Q"
    and len_hit: "length raw_idxs_hit = rounds"
    and query_hit_eq:
      "query_idxs_hit =
        map (\<lambda>raw. index (to_nat raw)) raw_idxs_hit"
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
    unfolding staged_security_with_data_state_query_index_list_path_fresh_def
    by auto
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
  have query_lookup_start:
    "\<And>i x. fmlookup (HashMap query_state) (QueryIndexChallenge i x) =
      fmlookup (HashMap ?s) (QueryIndexChallenge i x)"
    using prefix_lookup s3_lookup s4_lookup s5_lookup s6_eq
      s7_lookup query_lookup by simp
  have local_fresh:
    "query_index_list_path_fresh query_state rounds query_chunks raw_idxs"
    unfolding query_index_list_path_fresh_def
  proof (intro conjI allI impI)
    show "length raw_idxs = rounds"
      using len_raw .
  next
    show "length query_chunks = rounds"
      using len_chunks .
  next
    fix i
    assume i_bound: "i < rounds"
    let ?x =
      "state_after_query_chunks (staged_query_start_hash data)
        (staged_query_chunks data) i"
    have "fmlookup (HashMap query_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) query_chunks i)) =
      fmlookup (HashMap ?s) (QueryIndexChallenge i ?x)"
      using local_counter prefix_state_query chunks_eq
        query_lookup_start[of i ?x] by simp
    also have "... = None"
      by (rule fresh_hit[OF i_bound])
    finally show
      "fmlookup (HashMap query_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) query_chunks i)) =
        None" .
  qed
  have path:
    "query_rounds_raw_list_path_hit query_state raw_idxs rounds out"
    unfolding query_rounds_raw_list_path_hit_def out_eq
    using len_raw len_chunks state_final local_fresh lookups
    by auto
  have witness:
    "(fr, f_fl) = (fr, f_fl) \<and>
      Some (f_final, s3) \<in> set_dist (execute read prefix_state) \<and>
      Some (as, s4) \<in>
        set_dist (execute (mmap (replicate (length spec) alpha_round)) s3) \<and>
      Some (dg, s5) \<in> set_dist (execute read s4) \<and>
      Some ((), s6) \<in>
        set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5) \<and>
      Some (fl, s7) \<in>
        set_dist (execute
          (ntimes receive_composition_fri_commits
            (ceil_log (to_nat dg + 1))) s6) \<and>
      Some (final, query_state) \<in> set_dist (execute read s7) \<and>
      raw_idxs \<in> query_index_raw_list_preimage Q \<and>
      query_rounds_raw_list_path_hit query_state raw_idxs rounds out"
    using read_trace_final alpha_out read_dg degree_assert comp_fri
      read_final raw_in path by simp
  show ?thesis
    unfolding verifier_after_trace_fri_raw_list_path_hit_def
    using witness by blast
qed

lemma verifier_after_composition_fri_staged_query_path_fresh_imp_raw_list_path_hit:
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
          (execute
            verifier_composition_fri_prefix
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and suffix:
      "out \<in>
        set_dist
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
    using hit
    unfolding staged_security_with_data_state_query_index_list_path_fresh_def
    by simp
next
  case (Some pair)
  then obtain result :: "unit list" and final_state where out_eq:
    "out = Some (result, final_state)"
    by (cases pair) simp
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
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
  have prefix_counter:
    "PQueryCounter prefix_state = PQueryCounter ?s"
    using verifier_composition_fri_prefix_outcome
        [OF prefix[unfolded header_eq]]
    by simp
  have local_counter: "PQueryCounter query_state = 0"
    using query_counter prefix_counter
    unfolding verifier_state_from_adversary_def by simp
  have prefix_lookup:
    "\<And>i x. fmlookup (HashMap prefix_state)
        (QueryIndexChallenge i x) =
      fmlookup (HashMap ?s) (QueryIndexChallenge i x)"
    by (rule verifier_composition_fri_prefix_preserves_query_lookup
        [OF prefix[unfolded header_eq]])
  have read_lookup: "HashMap query_state = HashMap prefix_state"
    by (rule read_preserves_hash_map[OF read_final])
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
    using verifier_composition_fri_prefix_outcome
        [OF prefix[unfolded header_eq]]
    by simp
  from read_outcome[OF read_final] obtain rest_query where
    tr_prefix: "PTranscript prefix_state = final # rest_query"
    and state_query: "PState query_state = concat (PState prefix_state) final"
    and tr_read_query: "PTranscript query_state = rest_query"
    by blast
  have header_actual:
    "verifier_header_transcript ?s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    unfolding verifier_header_transcript_def verifier_header_messages_def
    using prefix_res tr_prefix tr_read_query by simp
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
        using verifier_query_round_chunk_length[OF round_chunks[OF i_bound]]
          header_unique
        by simp
    qed
    have concat_staged:
      "List.concat query_chunks @ PTranscript final_state =
        List.concat (staged_query_chunks data)"
      using tr_query header_unique by simp
    then show ?thesis
      using query_chunks_eq_staged_if_matching_lengths
          [OF len_chunks concat_staged parser_chunk_len
            staged_match_query_idxs]
      by simp
  qed
  from hit out_eq obtain raw_idxs_hit query_idxs_hit where
    query_hit_in: "query_idxs_hit \<in> Q"
    and len_hit: "length raw_idxs_hit = rounds"
    and query_hit_eq:
      "query_idxs_hit =
        map (\<lambda>raw. index (to_nat raw)) raw_idxs_hit"
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
    unfolding staged_security_with_data_state_query_index_list_path_fresh_def
    by auto
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
  have query_lookup_start:
    "\<And>i x. fmlookup (HashMap query_state) (QueryIndexChallenge i x) =
      fmlookup (HashMap ?s) (QueryIndexChallenge i x)"
    using prefix_lookup read_lookup by simp
  have local_fresh:
    "query_index_list_path_fresh query_state rounds query_chunks raw_idxs"
    unfolding query_index_list_path_fresh_def
  proof (intro conjI allI impI)
    show "length raw_idxs = rounds"
      using len_raw .
  next
    show "length query_chunks = rounds"
      using len_chunks .
  next
    fix i
    assume i_bound: "i < rounds"
    let ?x =
      "state_after_query_chunks (staged_query_start_hash data)
        (staged_query_chunks data) i"
    have "fmlookup (HashMap query_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) query_chunks i)) =
      fmlookup (HashMap ?s) (QueryIndexChallenge i ?x)"
      using local_counter prefix_state_query chunks_eq
        query_lookup_start[of i ?x] by simp
    also have "... = None"
      by (rule fresh_hit[OF i_bound])
    finally show
      "fmlookup (HashMap query_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) query_chunks i)) =
        None" .
  qed
  have path:
    "query_rounds_raw_list_path_hit query_state raw_idxs rounds out"
    unfolding query_rounds_raw_list_path_hit_def out_eq
    using len_raw len_chunks state_final local_fresh lookups
    by auto
  show ?thesis
    unfolding verifier_after_composition_fri_raw_list_path_hit_def
    by (intro exI[of _ final] exI[of _ query_state]
        exI[of _ raw_idxs] conjI)
      (use read_final raw_in path in simp_all)
qed

lemma staged_security_trace_fri_pair_challenge_fresh_imp_query_index_list_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and projection: "fst ` P \<subseteq> Q"
    and hit: "staged_security_trace_fri_pair_challenge_fresh P B out"
  shows "staged_security_with_data_query_index_list_set_hit Q out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding staged_security_trace_fri_pair_challenge_fresh_def
      staged_security_with_data_state_verifier_event_def
      staged_security_with_data_query_index_list_set_hit_def
    by simp
next
  case (Some packed)
  then obtain data attacker_state result final_state where out_eq:
    "out = Some (((data, attacker_state), result), final_state)"
    by (cases packed) (auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from hit out_eq have pair_hit:
    "trace_fri_query_challenge_pair_set_hit ?s P
      (Some (result, final_state))"
    unfolding staged_security_trace_fri_pair_challenge_fresh_def
      staged_security_with_data_state_verifier_event_def
    by simp
  have trace_hit:
    "trace_fri_query_index_list_set_hit ?s Q
      (Some (result, final_state))"
    by (rule trace_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit
        [OF pair_hit projection])
  from trace_hit obtain trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers where
    fri:
      "accepted_fri_opening_transcript ?s (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final query_idxs trace_round_layers
        composition_round_layers"
    and query_in: "query_idxs \<in> Q"
    unfolding trace_fri_query_index_list_set_hit_def by blast
  from accepted_fri_opening_transcript_imp_accepted_transcript_shape[OF fri]
  obtain as where shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as query_idxs"
    by blast
  from checked_staged_security_with_data_state_accepted_shape_query_keys
      [OF wf controlled support[unfolded out_eq] shape]
  obtain raw_idxs where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    by blast
  show ?thesis
    unfolding out_eq staged_security_with_data_query_index_list_set_hit_def
    using len_raw query_in query_idxs_eq lookup by auto
qed

lemma staged_security_composition_fri_pair_challenge_fresh_imp_query_index_list_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and projection: "\<And>dg. fst ` P dg \<subseteq> Q"
    and hit: "staged_security_composition_fri_pair_challenge_fresh P B out"
  shows "staged_security_with_data_query_index_list_set_hit Q out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding staged_security_composition_fri_pair_challenge_fresh_def
      staged_security_with_data_state_verifier_event_def
      staged_security_with_data_query_index_list_set_hit_def
    by simp
next
  case (Some packed)
  then obtain data attacker_state result final_state where out_eq:
    "out = Some (((data, attacker_state), result), final_state)"
    by (cases packed) (auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from hit out_eq have pair_hit:
    "composition_fri_query_challenge_pair_set_hit ?s P
      (Some (result, final_state))"
    unfolding staged_security_composition_fri_pair_challenge_fresh_def
      staged_security_with_data_state_verifier_event_def
    by simp
  have composition_hit:
    "composition_fri_query_index_list_set_hit ?s Q
      (Some (result, final_state))"
    by (rule
        composition_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit
        [OF pair_hit projection])
  from composition_hit obtain trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers where
    fri:
      "accepted_fri_opening_transcript ?s (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final query_idxs trace_round_layers
        composition_round_layers"
    and query_in: "query_idxs \<in> Q"
    unfolding composition_fri_query_index_list_set_hit_def by blast
  from accepted_fri_opening_transcript_imp_accepted_transcript_shape[OF fri]
  obtain as where shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as query_idxs"
    by blast
  from checked_staged_security_with_data_state_accepted_shape_query_keys
      [OF wf controlled support[unfolded out_eq] shape]
  obtain raw_idxs where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    by blast
  show ?thesis
    unfolding out_eq staged_security_with_data_query_index_list_set_hit_def
    using len_raw query_in query_idxs_eq lookup by auto
qed

lemma checked_staged_security_trace_fri_pair_challenge_fresh_bound_from_query_path_fresh:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection: "fst ` P \<subseteq> Q"
    and path_branch_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_trace_fri_pair_challenge_query_path_fresh P B Q)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_trace_fri_pair_challenge_fresh P B)
      adversary_initial_state \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  have event_mono:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_trace_fri_pair_challenge_fresh P B)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_trace_fri_pair_challenge_query_path_fresh P B Q out \<or>
        staged_security_with_data_state_query_index_list_prequery_hit A Q out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit: "staged_security_trace_fri_pair_challenge_fresh P B out"
    have query_hit:
      "staged_security_with_data_query_index_list_set_hit Q out"
      by (rule
          staged_security_trace_fri_pair_challenge_fresh_imp_query_index_list_hit
          [OF wf controlled support projection hit])
    show
      "staged_security_trace_fri_pair_challenge_query_path_fresh P B Q out \<or>
       staged_security_with_data_state_query_index_list_prequery_hit A Q out"
    proof (cases out)
      case None
      then show ?thesis
        using query_hit
        unfolding staged_security_with_data_query_index_list_set_hit_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed) (auto split: prod.splits)
      have split:
        "staged_security_with_data_state_query_index_list_path_fresh Q
          (Some (((data, attacker_state), result), final_state)) \<or>
         hash_relation_hit
          (checked_staged_query_index_list_relation A Q)
          adversary_initial_state attacker_state"
        apply (rule
            checked_staged_security_with_data_state_query_index_list_fresh_or_prequeried)
        using support query_hit unfolding out_eq by simp_all
      then show ?thesis
      proof
        assume fresh:
          "staged_security_with_data_state_query_index_list_path_fresh Q
            (Some (((data, attacker_state), result), final_state))"
        have pair_fresh:
          "staged_security_trace_fri_pair_challenge_fresh P B
            (Some (((data, attacker_state), result), final_state))"
          using hit out_eq by simp
        then have
          "staged_security_trace_fri_pair_challenge_query_path_fresh P B Q
            out"
          unfolding out_eq
            staged_security_trace_fri_pair_challenge_query_path_fresh_def
          using fresh pair_fresh by simp
        then show ?thesis ..
      next
        assume prequery:
          "hash_relation_hit
            (checked_staged_query_index_list_relation A Q)
            adversary_initial_state attacker_state"
        then have
          "staged_security_with_data_state_query_index_list_prequery_hit A Q
            out"
          unfolding out_eq
            staged_security_with_data_state_query_index_list_prequery_hit_def
          by simp
        then show ?thesis ..
      qed
    qed
  qed
  have union_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_trace_fri_pair_challenge_query_path_fresh P B Q out \<or>
        staged_security_with_data_state_query_index_list_prequery_hit A Q out)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_trace_fri_pair_challenge_query_path_fresh P B Q)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_prequery_hit A Q)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  have prequery_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_index_list_prequery_hit A Q)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_with_data_state_query_index_list_prequery_hit_bound
        [OF wf controlled])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_trace_fri_pair_challenge_fresh P B)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_trace_fri_pair_challenge_query_path_fresh P B Q)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_prequery_hit A Q)
        adversary_initial_state"
    by (rule order_trans[OF event_mono union_bound])
  also have "... \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule add_mono[OF path_branch_bound prequery_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_pair_challenge_fresh_bound_from_query_path_fresh:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection: "\<And>dg. fst ` P dg \<subseteq> Q"
    and path_branch_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_composition_fri_pair_challenge_query_path_fresh P B Q)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_composition_fri_pair_challenge_fresh P B)
      adversary_initial_state \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  have event_mono:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_composition_fri_pair_challenge_fresh P B)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_composition_fri_pair_challenge_query_path_fresh P B Q out \<or>
        staged_security_with_data_state_query_index_list_prequery_hit A Q out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit: "staged_security_composition_fri_pair_challenge_fresh P B out"
    have query_hit:
      "staged_security_with_data_query_index_list_set_hit Q out"
      by (rule
          staged_security_composition_fri_pair_challenge_fresh_imp_query_index_list_hit
          [OF wf controlled support projection hit])
    show
      "staged_security_composition_fri_pair_challenge_query_path_fresh P B Q out \<or>
       staged_security_with_data_state_query_index_list_prequery_hit A Q out"
    proof (cases out)
      case None
      then show ?thesis
        using query_hit
        unfolding staged_security_with_data_query_index_list_set_hit_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed) (auto split: prod.splits)
      have split:
        "staged_security_with_data_state_query_index_list_path_fresh Q
          (Some (((data, attacker_state), result), final_state)) \<or>
         hash_relation_hit
          (checked_staged_query_index_list_relation A Q)
          adversary_initial_state attacker_state"
        apply (rule
            checked_staged_security_with_data_state_query_index_list_fresh_or_prequeried)
        using support query_hit unfolding out_eq by simp_all
      then show ?thesis
      proof
        assume fresh:
          "staged_security_with_data_state_query_index_list_path_fresh Q
            (Some (((data, attacker_state), result), final_state))"
        have pair_fresh:
          "staged_security_composition_fri_pair_challenge_fresh P B
            (Some (((data, attacker_state), result), final_state))"
          using hit out_eq by simp
        then have
          "staged_security_composition_fri_pair_challenge_query_path_fresh
            P B Q out"
          unfolding out_eq
            staged_security_composition_fri_pair_challenge_query_path_fresh_def
          using fresh pair_fresh by simp
        then show ?thesis ..
      next
        assume prequery:
          "hash_relation_hit
            (checked_staged_query_index_list_relation A Q)
            adversary_initial_state attacker_state"
        then have
          "staged_security_with_data_state_query_index_list_prequery_hit A Q
            out"
          unfolding out_eq
            staged_security_with_data_state_query_index_list_prequery_hit_def
          by simp
        then show ?thesis ..
      qed
    qed
  qed
  have union_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_composition_fri_pair_challenge_query_path_fresh P B Q out \<or>
        staged_security_with_data_state_query_index_list_prequery_hit A Q out)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_composition_fri_pair_challenge_query_path_fresh P B Q)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_prequery_hit A Q)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  have prequery_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_index_list_prequery_hit A Q)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_with_data_state_query_index_list_prequery_hit_bound
        [OF wf controlled])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_composition_fri_pair_challenge_fresh P B)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_composition_fri_pair_challenge_query_path_fresh P B Q)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_prequery_hit A Q)
        adversary_initial_state"
    by (rule order_trans[OF event_mono union_bound])
  also have "... \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule add_mono[OF path_branch_bound prequery_bound])
  finally show ?thesis by simp
qed

lemma checked_staged_security_composition_fri_pair_challenge_query_path_fresh_fixed_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and challenges_space:
      "challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and projection:
      "fst ` (P dg \<inter> (UNIV \<times> {challenges})) \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_composition_fri_pair_challenge_query_path_fresh P
        (\<lambda>dg'. if dg' = dg then {challenges} else {}) Q)
      adversary_initial_state \<le>
      (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
        (nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
proof (rule checked_staged_security_with_data_state_bound_from_data_cont)
  let ?B = "\<lambda>dg'. if dg' = dg then {challenges} else {}"
  let ?D =
    "nnreal (card Q) *
      (1 / nnreal (card query_sample_space)) ^ rounds"
  show "\<not> staged_security_composition_fri_pair_challenge_query_path_fresh
      P ?B Q None"
    unfolding
      staged_security_composition_fri_pair_challenge_query_path_fresh_def
      staged_security_composition_fri_pair_challenge_fresh_def
      staged_security_with_data_state_verifier_event_def
    by simp
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  let ?B = "\<lambda>dg'. if dg' = dg then {challenges} else {}"
  let ?Event =
    "\<lambda>out.
      staged_security_composition_fri_pair_challenge_query_path_fresh P ?B Q
        (case out of
          None \<Rightarrow> None
        | Some (result, final_state) \<Rightarrow>
            Some (((data, attacker_state), result), final_state))"
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl, f_final, as, dg', fl), _) \<Rightarrow>
          dg' = dg \<and> map fst fl = challenges \<and>
          composition_fri_challenge_path_fresh ?s fr (map snd f_fl)
            f_final as dg' (map snd fl) (length (map snd fl))"
  show "wp_event verify_monad ?Event ?s \<le>
      (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
        (nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
    unfolding verify_monad_composition_fri_decomposition
  proof (rule order_trans)
    show "wp_event
        (verifier_composition_fri_prefix \<bind>
          verifier_after_composition_fri)
        ?Event ?s
      \<le> wp_event verifier_composition_fri_prefix ?Head ?s *
        (nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
    proof (rule wp_event_bind_bound_by_head_and_cont)
      show "\<not> ?Event None"
        unfolding
          staged_security_composition_fri_pair_challenge_query_path_fresh_def
          staged_security_composition_fri_pair_challenge_fresh_def
          staged_security_with_data_state_verifier_event_def
        by simp
    next
      fix header prefix_state
      assume prefix:
        "Some (header, prefix_state) \<in>
          set_dist (execute verifier_composition_fri_prefix ?s)"
        and not_head: "\<not> ?Head (Some (header, prefix_state))"
      obtain fr f_fl f_final as dg' fl where header_eq:
        "header = (fr, f_fl, f_final, as, dg', fl)"
        by (cases header) auto
      have not_head':
        "dg' \<noteq> dg \<or> map fst fl \<noteq> challenges \<or>
          \<not> composition_fri_challenge_path_fresh ?s fr (map snd f_fl)
            f_final as dg' (map snd fl) (length (map snd fl))"
        using not_head unfolding header_eq by simp
      show "wp_event (verifier_after_composition_fri header) ?Event
          prefix_state = 0"
      proof (rule antisym)
        show "wp_event (verifier_after_composition_fri header) ?Event
            prefix_state \<le> 0"
        proof (rule order_trans)
          show "wp_event (verifier_after_composition_fri header) ?Event
              prefix_state \<le>
            wp_event (verifier_after_composition_fri header)
              (\<lambda>_. False) prefix_state"
          proof (rule wp_event_mono_on_support)
            fix out
            assume suffix:
              "out \<in>
                set_dist
                  (execute (verifier_after_composition_fri header)
                    prefix_state)"
              and hit: "?Event out"
            show False
            proof (cases out)
              case None
              then show ?thesis
                using hit
                unfolding
                  staged_security_composition_fri_pair_challenge_query_path_fresh_def
                  staged_security_composition_fri_pair_challenge_fresh_def
                  staged_security_with_data_state_verifier_event_def
                by simp
            next
              case (Some pair)
              then obtain result :: "unit list" and final_state where out_eq:
                "out = Some (result, final_state)"
                by (cases pair) simp
              from hit out_eq have fresh:
                "composition_fri_challenge_list_fresh_hit ?s ?B
                  (Some (result, final_state))"
                and pair_hit:
                "composition_fri_query_challenge_pair_set_hit ?s P
                  (Some (result, final_state))"
                unfolding
                  staged_security_composition_fri_pair_challenge_query_path_fresh_def
                  staged_security_composition_fri_pair_challenge_fresh_def
                  staged_security_with_data_state_verifier_event_def
                by simp_all
              have prefix':
                "Some ((fr, f_fl, f_final, as, dg', fl), prefix_state) \<in>
                  set_dist (execute verifier_composition_fri_prefix ?s)"
                using prefix header_eq by simp
              have suffix':
                "Some (result, final_state) \<in>
                  set_dist
                    (execute
                      (verifier_after_composition_fri
                        (fr, f_fl, f_final, as, dg', fl))
                      prefix_state)"
                using suffix header_eq out_eq by simp
              from pair_hit obtain trace_roots trace_bs trace_final fri_dg
                  composition_roots composition_bs composition_final query_idxs
                  trace_round_layers composition_round_layers where
                openings:
                  "accepted_fri_opening_transcript ?s
                    (Some (result, final_state)) trace_roots trace_bs
                    trace_final fri_dg composition_roots composition_bs
                    composition_final query_idxs trace_round_layers
                    composition_round_layers"
                unfolding composition_fri_query_challenge_pair_set_hit_def
                by blast
              have pair_challenges:
                "accepted_fri_challenges ?s (Some (result, final_state))
                  trace_bs fri_dg composition_bs"
                by (rule accepted_fri_opening_transcript_challenges
                    [OF openings])
              from fresh obtain trace_bs' dg'' comp_bs' where
                fresh_challenges:
                  "accepted_fri_challenges ?s (Some (result, final_state))
                    trace_bs' dg'' comp_bs'"
                and comp_bs'_in:
                  "comp_bs' \<in>
                    (if dg'' = dg then {challenges} else {})"
                unfolding composition_fri_challenge_list_fresh_hit_def
                by blast
              have challenge_eqs:
                "fri_dg = dg'' \<and> composition_bs = comp_bs'"
                using accepted_fri_challenges_unique
                  [OF pair_challenges fresh_challenges]
                by simp
              have prefix_eqs:
                "fri_dg = dg' \<and> composition_bs = map fst fl"
                by (rule
                    verifier_after_composition_fri_header_agrees_with_accepted_challenges
                    [OF prefix' suffix' pair_challenges])
              have concrete_fresh:
                "composition_fri_challenge_path_fresh ?s fr (map snd f_fl)
                  f_final as dg' (map snd fl) (length (map snd fl))"
                by (rule
                    verifier_after_composition_fri_header_roots_agree_with_fresh_hit
                    [OF prefix' suffix' fresh])
              have dg''_eq: "dg'' = dg"
                using comp_bs'_in by (cases "dg'' = dg") auto
              have dg'_eq: "dg' = dg"
                using challenge_eqs prefix_eqs dg''_eq by simp
              have fl_challenges: "map fst fl = challenges"
                using comp_bs'_in prefix_eqs challenge_eqs dg''_eq by simp
              have head_holds:
                "dg' = dg \<and> map fst fl = challenges \<and>
                  composition_fri_challenge_path_fresh ?s fr (map snd f_fl)
                    f_final as dg' (map snd fl) (length (map snd fl))"
                using dg'_eq fl_challenges concrete_fresh by simp
              show ?thesis
                using not_head' head_holds by blast
            qed
          qed
        next
          show "wp_event (verifier_after_composition_fri header)
              (\<lambda>_. False) prefix_state \<le> 0"
            unfolding wp_event_def wp_def dist_expect_def by simp
        qed
      next
        show "0 \<le>
          wp_event (verifier_after_composition_fri header) ?Event
            prefix_state"
          by simp
      qed
    next
      fix header prefix_state
      assume prefix:
        "Some (header, prefix_state) \<in>
          set_dist (execute verifier_composition_fri_prefix ?s)"
        and head: "?Head (Some (header, prefix_state))"
      have event_mono:
        "wp_event (verifier_after_composition_fri header) ?Event
          prefix_state \<le>
        wp_event (verifier_after_composition_fri header)
          (verifier_after_composition_fri_raw_list_path_hit prefix_state Q)
          prefix_state"
      proof (rule wp_event_mono_on_support)
        fix out
        assume suffix:
          "out \<in>
            set_dist
              (execute (verifier_after_composition_fri header) prefix_state)"
          and hit: "?Event out"
        from hit have path_hit:
          "staged_security_with_data_state_query_index_list_path_fresh Q
            (case out of
              None \<Rightarrow> None
            | Some (result, final_state) \<Rightarrow>
                Some (((data, attacker_state), result), final_state))"
          unfolding
            staged_security_composition_fri_pair_challenge_query_path_fresh_def
          by simp
        show
          "verifier_after_composition_fri_raw_list_path_hit prefix_state Q
            out"
          by (rule
              verifier_after_composition_fri_staged_query_path_fresh_imp_raw_list_path_hit
              [OF wf controlled builder prefix suffix path_hit])
      qed
      also have "... \<le>
        nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds"
        by (rule wp_verifier_after_composition_fri_raw_list_path_product_bound
            [OF subset])
      finally show
        "wp_event (verifier_after_composition_fri header) ?Event
          prefix_state
        \<le> nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds" .
    qed
  next
    show "wp_event verifier_composition_fri_prefix ?Head ?s *
        (nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds)
      \<le>
      (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
        (nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
    proof (rule mult_right_mono)
      show "wp_event verifier_composition_fri_prefix ?Head ?s \<le>
        1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
      proof -
        let ?B = "\<lambda>dg'. if dg' = dg then {challenges} else {}"
        let ?HeadSet =
          "\<lambda>out. case out of
              None \<Rightarrow> False
            | Some ((fr, f_fl, f_final, as, dg', fl), _) \<Rightarrow>
                map fst fl \<in> ?B dg' \<and>
                composition_fri_challenge_path_fresh ?s fr (map snd f_fl)
                  f_final as dg' (map snd fl) (length (map snd fl))"
        have mono:
          "wp_event verifier_composition_fri_prefix ?Head ?s \<le>
            wp_event verifier_composition_fri_prefix ?HeadSet ?s"
          by (rule wp_event_mono) (auto split: option.splits prod.splits)
        have subset:
          "\<And>dg'. ?B dg' \<subseteq>
            fri_challenge_space (ceil_log (to_nat dg' + 1))"
          using challenges_space by auto
        have bound:
          "\<And>dg'. nnreal (card (?B dg')) /
            nnreal (CARD('f) ^ ceil_log (to_nat dg' + 1)) \<le>
            1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
          using challenges_space by auto
        have set_bound:
          "wp_event verifier_composition_fri_prefix ?HeadSet ?s \<le>
            1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
          by (rule
              wp_verifier_composition_fri_prefix_challenge_list_actual_fresh_bound
              [OF subset bound])
        show ?thesis
          by (rule order_trans[OF mono set_bound])
      qed
      show "0 \<le> nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
        by simp
    qed
  qed
qed

lemma checked_staged_security_composition_fri_pair_challenge_query_path_fresh_fiber_sum:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and challenge_subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and projection:
      "\<And>dg challenges.
        challenges \<in> B dg \<Longrightarrow>
        fst ` (P dg \<inter> (UNIV \<times> {challenges})) \<subseteq>
          Q dg challenges"
    and subset:
      "\<And>dg challenges. challenges \<in> B dg \<Longrightarrow>
        Q dg challenges \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_composition_fri_pair_challenge_query_path_fresh P
        B
        (\<Union>dg \<in> UNIV. \<Union>challenges \<in> B dg. Q dg challenges))
      adversary_initial_state \<le>
      (\<Sum>dg \<in> UNIV.
        \<Sum>challenges \<in> B dg.
          (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
            (nnreal (card (Q dg challenges)) *
              (1 / nnreal (card query_sample_space)) ^ rounds))"
proof -
  let ?Q = "(\<Union>dg \<in> UNIV. \<Union>challenges \<in> B dg. Q dg challenges)"
  let ?I = "SIGMA dg:UNIV. B dg"
  let ?E =
    "\<lambda>p.
      staged_security_composition_fri_pair_challenge_query_path_fresh P
        (\<lambda>dg'. if dg' = fst p then {snd p} else {})
        (Q (fst p) (snd p))"
  let ?C =
    "\<lambda>p.
      (1 / nnreal (CARD('f) ^ ceil_log (to_nat (fst p) + 1))) *
        (nnreal (card (Q (fst p) (snd p))) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
  have split:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_composition_fri_pair_challenge_query_path_fresh P B ?Q)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out. \<exists>p \<in> ?I. ?E p out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
      "staged_security_composition_fri_pair_challenge_query_path_fresh P B ?Q
        out"
    show "\<exists>p \<in> ?I. ?E p out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          staged_security_composition_fri_pair_challenge_query_path_fresh_def
          staged_security_composition_fri_pair_challenge_fresh_def
          staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed) (auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from hit out_eq have pair_hit:
        "composition_fri_query_challenge_pair_set_hit ?s P
          (Some (result, final_state))"
        and fresh:
        "composition_fri_challenge_list_fresh_hit ?s B
          (Some (result, final_state))"
        and path:
        "staged_security_with_data_state_query_index_list_path_fresh ?Q out"
        unfolding
          staged_security_composition_fri_pair_challenge_query_path_fresh_def
          staged_security_composition_fri_pair_challenge_fresh_def
          staged_security_with_data_state_verifier_event_def
        by simp_all
      from fresh obtain trace_bs dg comp_bs fr trace_roots trace_final as
          composition_roots final rest where
        accepted:
          "accepted_fri_challenges ?s (Some (result, final_state))
            trace_bs dg comp_bs"
        and comp_bs_in: "comp_bs \<in> B dg"
        and header:
          "verifier_header_transcript ?s fr trace_roots trace_final as dg
            composition_roots final rest"
        and fresh_path:
          "composition_fri_challenge_path_fresh ?s fr trace_roots
            trace_final as dg composition_roots (length composition_roots)"
        unfolding composition_fri_challenge_list_fresh_hit_def by blast
      from pair_hit obtain trace_roots' trace_bs' trace_final' fri_dg
          composition_roots' composition_bs' composition_final' query_idxs
          trace_round_layers composition_round_layers where
        openings:
          "accepted_fri_opening_transcript ?s
            (Some (result, final_state)) trace_roots' trace_bs'
            trace_final' fri_dg composition_roots' composition_bs'
            composition_final' query_idxs trace_round_layers
            composition_round_layers"
        and pair: "(query_idxs, composition_bs') \<in> P fri_dg"
        unfolding composition_fri_query_challenge_pair_set_hit_def by blast
      have pair_challenges:
        "accepted_fri_challenges ?s (Some (result, final_state))
          trace_bs' fri_dg composition_bs'"
        by (rule accepted_fri_opening_transcript_challenges[OF openings])
      have eqs: "fri_dg = dg \<and> composition_bs' = comp_bs"
        using accepted_fri_challenges_unique[OF pair_challenges accepted]
        by simp
      have query_in: "query_idxs \<in> Q dg comp_bs"
      proof -
        have "query_idxs \<in>
            fst ` (P dg \<inter> (UNIV \<times> {comp_bs}))"
          using pair eqs by force
        then show ?thesis
          using projection[OF comp_bs_in] by blast
      qed
      from path out_eq obtain raw_idxs query_idxs_path where
        len_raw: "length raw_idxs = rounds"
        and query_path_in: "query_idxs_path \<in> ?Q"
        and query_path_eq:
          "query_idxs_path =
            map (\<lambda>raw. index (to_nat raw)) raw_idxs"
        and lookup:
          "\<And>i. i < rounds \<Longrightarrow>
            fmlookup (HashMap final_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
            Some (raw_idxs ! i)"
        and fresh_lookup:
          "\<And>i. i < rounds \<Longrightarrow>
            fmlookup (HashMap ?s)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
            None"
        unfolding staged_security_with_data_state_query_index_list_path_fresh_def
        by auto
      from accepted_fri_opening_transcript_imp_accepted_transcript_shape[OF openings]
      obtain as_shape where shape:
        "accepted_transcript_shape ?s (Some (result, final_state))
          as_shape query_idxs"
        by blast
      from checked_staged_security_with_data_state_accepted_shape_query_keys
          [OF wf controlled support[unfolded out_eq] shape]
      obtain raw_idxs_pair where
        len_raw_pair: "length raw_idxs_pair = rounds"
        and query_idxs_eq:
          "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs_pair"
        and lookup_pair:
          "\<And>i. i < rounds \<Longrightarrow>
            fmlookup (HashMap final_state)
            (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
            Some (raw_idxs_pair ! i)"
        by blast
      have raw_eq:
        "\<And>i. i < rounds \<Longrightarrow> raw_idxs ! i = raw_idxs_pair ! i"
        using lookup lookup_pair by simp
      have raw_idxs_eq: "raw_idxs = raw_idxs_pair"
        by (rule nth_equalityI)
          (use len_raw len_raw_pair raw_eq in simp_all)
      have path_witness:
        "length raw_idxs = rounds \<and>
          query_idxs \<in> Q dg comp_bs \<and>
          query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
          (\<forall>i < rounds.
            fmlookup (HashMap final_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
              Some (raw_idxs ! i) \<and>
            fmlookup (HashMap ?s)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
              None)"
        using len_raw raw_idxs_eq query_in query_idxs_eq lookup
          fresh_lookup by auto
      have path_body:
        "\<exists>raw_idxs query_idxs.
          length raw_idxs = rounds \<and>
          query_idxs \<in> Q dg comp_bs \<and>
          query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
          (\<forall>i < rounds.
            fmlookup (HashMap final_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
              Some (raw_idxs ! i) \<and>
            fmlookup (HashMap ?s)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
              None)"
        using path_witness by blast
      have path_single:
        "staged_security_with_data_state_query_index_list_path_fresh
          (Q dg comp_bs) out"
        unfolding out_eq
          staged_security_with_data_state_query_index_list_path_fresh_def
        using path_body by simp
      have fresh_single:
        "composition_fri_challenge_list_fresh_hit ?s
          (\<lambda>dg'. if dg' = dg then {comp_bs} else {})
          (Some (result, final_state))"
      proof -
        have witness:
          "accepted_fri_challenges ?s (Some (result, final_state))
              trace_bs dg comp_bs \<and>
            verifier_header_transcript ?s fr trace_roots trace_final as dg
              composition_roots final rest \<and>
            comp_bs \<in> (if dg = dg then {comp_bs} else {}) \<and>
            composition_fri_challenge_path_fresh ?s fr trace_roots
              trace_final as dg composition_roots (length composition_roots)"
          using accepted header fresh_path by simp
        show ?thesis
          unfolding composition_fri_challenge_list_fresh_hit_def
          using witness by blast
      qed
      have singleton:
        "?E (dg, comp_bs) out"
      proof -
        have fresh_single_pair:
          "composition_fri_challenge_list_fresh_hit ?s
            (\<lambda>dg'. if dg' = dg then {snd (dg, comp_bs)} else {})
            (Some (result, final_state))"
        proof -
          have
            "(\<lambda>dg'. if dg' = dg then {comp_bs} else {}) =
             (\<lambda>dg'. if dg' = dg then {snd (dg, comp_bs)} else {})"
            by (rule ext) (simp add: prod.sel)
          then show ?thesis
            using fresh_single by simp
        qed
        show ?thesis
        unfolding out_eq
          staged_security_composition_fri_pair_challenge_query_path_fresh_def
          staged_security_composition_fri_pair_challenge_fresh_def
          staged_security_with_data_state_verifier_event_def
          using pair_hit fresh_single_pair path_single out_eq by simp
      qed
      show ?thesis
        by (intro bexI[of _ "(dg, comp_bs)"])
          (use comp_bs_in singleton in simp_all)
    qed
  qed
  also have "... \<le> (\<Sum>p \<in> ?I. ?C p)"
  proof (rule wp_event_finite_union_bound_fri_exact)
    show "finite ?I"
      by (rule finite_SigmaI)
        (use challenge_subset finite_fri_challenge_space in
          \<open>auto intro: finite_subset[OF challenge_subset]\<close>)
  next
    fix p
    assume p_in: "p \<in> ?I"
    obtain dg challenges where p_eq: "p = (dg, challenges)"
      by (cases p) auto
    have challenges_in: "challenges \<in> B dg"
      using p_in p_eq by simp
    have challenges_space:
      "challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
      using challenge_subset[of dg] challenges_in by blast
    have fixed_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_composition_fri_pair_challenge_query_path_fresh P
          (\<lambda>dg'. if dg' = dg then {challenges} else {})
          (Q dg challenges))
        adversary_initial_state \<le>
        (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
          (nnreal (card (Q dg challenges)) *
            (1 / nnreal (card query_sample_space)) ^ rounds)"
      by (rule
          checked_staged_security_composition_fri_pair_challenge_query_path_fresh_fixed_bound
          [where dg = dg and challenges = challenges
            and Q = "Q dg challenges" and P = P,
            OF wf controlled challenges_space
              projection[OF challenges_in] subset[OF challenges_in]])
    have event_eq:
      "?E p =
        staged_security_composition_fri_pair_challenge_query_path_fresh P
          (\<lambda>dg'. if dg' = dg then {challenges} else {})
          (Q dg challenges)"
      unfolding p_eq
        staged_security_composition_fri_pair_challenge_query_path_fresh_def
        staged_security_composition_fri_pair_challenge_fresh_def
        composition_fri_challenge_list_fresh_hit_def
      by (rule ext) (simp add: prod.sel)
    have cost_eq:
      "?C p =
        (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
          (nnreal (card (Q dg challenges)) *
            (1 / nnreal (card query_sample_space)) ^ rounds)"
      unfolding p_eq by simp
    show "wp_event (checked_staged_security_experiment_with_data_state A)
        (?E p) adversary_initial_state \<le> ?C p"
      using fixed_bound unfolding event_eq cost_eq .
  qed
  finally have bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_composition_fri_pair_challenge_query_path_fresh P
        B ?Q)
      adversary_initial_state \<le> (\<Sum>p \<in> ?I. ?C p)" .
  have finite_B: "\<And>dg. finite (B dg)"
    by (meson challenge_subset finite_fri_challenge_space finite_subset)
  have sigma_eq:
    "(\<Sum>p \<in> ?I. ?C p) =
      (\<Sum>dg \<in> UNIV.
        \<Sum>challenges \<in> B dg.
          (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
            (nnreal (card (Q dg challenges)) *
              (1 / nnreal (card query_sample_space)) ^ rounds))"
    by (subst sum.Sigma) (simp_all add: finite_B case_prod_beta)
  show ?thesis
    using bound sigma_eq by simp
qed

end

end
