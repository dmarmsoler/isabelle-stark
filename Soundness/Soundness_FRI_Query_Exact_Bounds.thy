(*  Title:      Stark/Soundness_FRI_Query_Exact_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_Exact_Bounds
  imports Soundness_FRI_Query_Exact_Verifier
begin

text \<open>
  Exact sampled-query bounds for the FRI query-list events.

  This layer connects the verifier-level query-index-list consumption theorem
  to the trace/composition sampled FRI events.  It stays separate from the raw
  verifier decomposition to keep theory finalization predictable.
\<close>

context soundness
begin

lemma wp_event_finite_union_bound_fri_exact:
  fixes B :: "'i \<Rightarrow> prob"
  assumes finite: "finite I"
    and bounds: "\<And>i. i \<in> I \<Longrightarrow> wp_event m (E i) s \<le> B i"
  shows
    "wp_event m (\<lambda>out. \<exists>i \<in> I. E i out) s \<le> (\<Sum>i\<in>I. B i)"
  using finite bounds
proof (induction I)
  case empty
  show ?case
    unfolding wp_event_def wp_def dist_expect_def by simp
next
  case (insert i I)
  have split:
    "wp_event m (\<lambda>out. \<exists>j \<in> insert i I. E j out) s \<le>
      wp_event m (E i) s +
      wp_event m (\<lambda>out. \<exists>j \<in> I. E j out) s"
  proof -
    have "wp_event m (\<lambda>out. \<exists>j \<in> insert i I. E j out) s \<le>
        wp_event m (\<lambda>out. E i out \<or> (\<exists>j \<in> I. E j out)) s"
      by (rule wp_event_mono) auto
    also have "... \<le>
        wp_event m (E i) s +
        wp_event m (\<lambda>out. \<exists>j \<in> I. E j out) s"
      by (rule wp_event_union_bound)
    finally show ?thesis .
  qed
  have tail:
    "wp_event m (\<lambda>out. \<exists>j \<in> I. E j out) s \<le> (\<Sum>j\<in>I. B j)"
    by (rule insert.IH) (use insert.prems in blast)
  have "wp_event m (E i) s +
      wp_event m (\<lambda>out. \<exists>j \<in> I. E j out) s \<le>
      B i + (\<Sum>j\<in>I. B j)"
    by (intro add_mono tail insert.prems) simp
  also have "... = (\<Sum>j\<in>insert i I. B j)"
    using insert.hyps by simp
  finally show ?case
    by (rule order_trans[OF split])
qed

lemma weighted_query_fiber_sum_eq:
  fixes I :: "'i set" and f :: "'i \<Rightarrow> nat"
  assumes fin: "finite I"
    and A_pos: "0 < A"
    and B_pos: "0 < B"
  shows
    "(\<Sum>x \<in> I.
      (1 / nnreal A) * ((1 / nnreal B) ^ rounds * nnreal (f x))) =
     nnreal (\<Sum>x \<in> I. f x) / (nnreal A * nnreal B ^ rounds)"
proof -
  have sum_nnreal:
    "(\<Sum>x \<in> I. nnreal (f x)) = nnreal (\<Sum>x \<in> I. f x)"
    using fin by induction simp_all
  have
    "(\<Sum>x \<in> I.
      (1 / nnreal A) * ((1 / nnreal B) ^ rounds * nnreal (f x))) =
     (\<Sum>x \<in> I. nnreal (f x) / (nnreal A * nnreal B ^ rounds))"
    using A_pos B_pos
    by (intro sum.cong refl)
      (transfer, simp add: field_simps power_divide)
  also have "... =
      (\<Sum>x \<in> I. nnreal (f x)) / (nnreal A * nnreal B ^ rounds)"
    by (rule sum_divide_nnreal[OF fin])
  also have "... =
      nnreal (\<Sum>x \<in> I. f x) / (nnreal A * nnreal B ^ rounds)"
    by (simp add: sum_nnreal)
  finally show ?thesis .
qed

lemma accepted_fri_opening_transcript_imp_query_rounds_index_list_hit:
  assumes openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
  shows "query_rounds_index_list_hit s query_idxs rounds out"
proof -
  from openings obtain result final_state query_start_state rest raw_idxs
      query_chunks trailing where
    out_eq: "out = Some (result, final_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks query_start_state query_chunks i)) =
          Some (raw_idxs ! i)"
    unfolding accepted_fri_opening_transcript_def
      verifier_query_indices_derived_def
    by blast
  show ?thesis
    unfolding query_rounds_index_list_hit_def
    apply (rule exI[where x=result])
    apply (rule exI[where x=final_state])
    apply (rule exI[where x=raw_idxs])
    using out_eq len_raw query_idxs_eq lookup
    by auto
qed

lemma trace_fri_query_index_list_set_hit_imp_query_rounds_index_list_hit:
  assumes hit: "trace_fri_query_index_list_set_hit s Q out"
  shows
    "\<exists>query_idxs \<in> Q.
      query_rounds_index_list_hit s query_idxs rounds out"
proof -
  from hit obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final query_idxs trace_round_layers
      composition_round_layers where
    openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        query_idxs trace_round_layers composition_round_layers"
    and query_in: "query_idxs \<in> Q"
    unfolding trace_fri_query_index_list_set_hit_def by blast
  have "query_rounds_index_list_hit s query_idxs rounds out"
    by (rule accepted_fri_opening_transcript_imp_query_rounds_index_list_hit
        [OF openings])
  then show ?thesis
    using query_in by blast
qed

lemma composition_fri_query_index_list_set_hit_imp_query_rounds_index_list_hit:
  assumes hit: "composition_fri_query_index_list_set_hit s Q out"
  shows
    "\<exists>query_idxs \<in> Q.
      query_rounds_index_list_hit s query_idxs rounds out"
proof -
  from hit obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final query_idxs trace_round_layers
      composition_round_layers where
    openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        query_idxs trace_round_layers composition_round_layers"
    and query_in: "query_idxs \<in> Q"
    unfolding composition_fri_query_index_list_set_hit_def by blast
  have "query_rounds_index_list_hit s query_idxs rounds out"
    by (rule accepted_fri_opening_transcript_imp_query_rounds_index_list_hit
        [OF openings])
  then show ?thesis
    using query_in by blast
qed

lemma wp_trace_fri_query_index_list_set_hit_exact_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad (trace_fri_query_index_list_set_hit s Q) s \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof -
  have event_bound:
    "wp_event verify_monad
      (\<lambda>out. \<exists>query_idxs \<in> Q.
        query_rounds_index_list_hit s query_idxs rounds out) s \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule wp_verify_monad_query_index_list_set_bound
        [OF future raw_bound subset])
  show ?thesis
    by (rule order_trans[OF _ event_bound])
      (rule wp_event_mono,
        rule trace_fri_query_index_list_set_hit_imp_query_rounds_index_list_hit)
qed

lemma wp_composition_fri_query_index_list_set_hit_exact_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad (composition_fri_query_index_list_set_hit s Q) s \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof -
  have event_bound:
    "wp_event verify_monad
      (\<lambda>out. \<exists>query_idxs \<in> Q.
        query_rounds_index_list_hit s query_idxs rounds out) s \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule wp_verify_monad_query_index_list_set_bound
        [OF future raw_bound subset])
  show ?thesis
    by (rule order_trans[OF _ event_bound])
      (rule wp_event_mono,
        rule composition_fri_query_index_list_set_hit_imp_query_rounds_index_list_hit)
qed

lemma wp_trace_fri_query_challenge_pair_set_hit_bound_from_query_projection:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and projection: "fst ` P \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad (trace_fri_query_challenge_pair_set_hit s P) s \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof -
  have event_bound:
    "wp_event verify_monad (trace_fri_query_index_list_set_hit s Q) s \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule wp_trace_fri_query_index_list_set_hit_exact_bound
        [OF future raw_bound subset])
  show ?thesis
    by (rule order_trans[OF _ event_bound])
      (rule wp_event_mono,
        rule trace_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit
          [OF _ projection])
qed

lemma
  wp_composition_fri_query_challenge_pair_set_hit_bound_from_query_projection:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and projection: "\<And>dg. fst ` P dg \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s P) s \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof -
  have event_bound:
    "wp_event verify_monad (composition_fri_query_index_list_set_hit s Q) s
      \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule wp_composition_fri_query_index_list_set_hit_exact_bound
        [OF future raw_bound subset])
  show ?thesis
    by (rule order_trans[OF _ event_bound])
      (rule wp_event_mono,
        rule composition_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit
          [OF _ projection])
qed

lemma wp_trace_fri_sampled_query_pair_set_hit_bound_from_query_projection:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and projection:
      "\<And>trace_table roots final round_layers layers.
        fst ` R trace_table roots final round_layers layers \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_pair_set_hit R s) s \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof -
  have event_bound:
    "wp_event verify_monad (trace_fri_query_index_list_set_hit s Q) s \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule wp_trace_fri_query_index_list_set_hit_exact_bound
        [OF future raw_bound subset])
  show ?thesis
    by (rule order_trans[OF _ event_bound])
      (rule wp_event_mono,
        rule trace_fri_sampled_query_pair_set_hit_imp_query_index_list_set_hit
          [OF _ projection])
qed

lemma wp_composition_fri_sampled_query_pair_set_hit_bound_from_query_projection:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and projection:
      "\<And>dg composition_table roots final round_layers layers.
        fst ` R dg composition_table roots final round_layers layers \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_query_pair_set_hit R s) s \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof -
  have event_bound:
    "wp_event verify_monad (composition_fri_query_index_list_set_hit s Q) s
      \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule wp_composition_fri_query_index_list_set_hit_exact_bound
        [OF future raw_bound subset])
  show ?thesis
    by (rule order_trans[OF _ event_bound])
      (rule wp_event_mono,
        rule composition_fri_sampled_query_pair_set_hit_imp_query_index_list_set_hit
          [OF _ projection])
qed

lemma wp_verifier_after_trace_fri_query_index_list_set_bound:
  assumes future: "query_future_fresh t"
    and counter: "PQueryCounter t = PQueryCounter s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (verifier_after_trace_fri header)
      (\<lambda>out. \<exists>query_idxs \<in> Q.
        query_rounds_index_list_hit s query_idxs rounds out) t \<le>
      nnreal (card Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof -
  obtain fr f_fl where header_eq: "header = (fr, f_fl)"
    by (cases header) auto
  let ?E =
    "\<lambda>out. \<exists>query_idxs \<in> Q.
      query_rounds_index_list_hit s query_idxs rounds out"
  let ?C =
    "nnreal (card Q) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
  have after_eq:
    "verifier_after_trace_fri header =
      (read \<bind>
        (\<lambda>f_final.
          mmap (replicate (length spec) alpha_round) \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. ntimes receive_composition_fri_commits
                (ceil_log (to_nat dg + 1)) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds)))))))"
    unfolding header_eq verifier_after_trace_fri_def by simp
  show ?thesis
    unfolding after_eq
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?E None"
      by simp
  next
    fix f_final s1
    assume read_f_final: "Some (f_final, s1) \<in> set_dist (execute read t)"
    have future_s1: "query_future_fresh s1"
      by (rule read_preserves_query_future_fresh[OF future read_f_final])
    from read_outcome[OF read_f_final] obtain rest1 where
      counter_s1_t: "PQueryCounter s1 = PQueryCounter t"
      by blast
    have counter_s1: "PQueryCounter s1 = PQueryCounter s"
      using counter_s1_t counter by simp
    show
      "wp_event
        (mmap (replicate (length spec) alpha_round) \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. ntimes receive_composition_fri_commits
                (ceil_log (to_nat dg + 1)) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds)))))) ?E s1 \<le> ?C"
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?E None"
        by simp
    next
      fix as s2
      assume alpha_out:
        "Some (as, s2) \<in>
          set_dist
            (execute (mmap (replicate (length spec) alpha_round)) s1)"
      have future_s2: "query_future_fresh s2"
        by (rule mmap_alpha_round_preserves_query_future_fresh
            [OF future_s1 alpha_out])
      have counter_s2_s1: "PQueryCounter s2 = PQueryCounter s1"
        using mmap_alpha_round_outcome[OF alpha_out] by simp
      have counter_s2: "PQueryCounter s2 = PQueryCounter s"
        using counter_s2_s1 counter_s1 by simp
      show
        "wp_event
          (read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. ntimes receive_composition_fri_commits
                (ceil_log (to_nat dg + 1)) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds))))) ?E s2 \<le> ?C"
      proof (rule wp_event_bind_bound_by_cont)
        show "\<not> ?E None"
          by simp
      next
        fix dg s3
        assume read_dg: "Some (dg, s3) \<in> set_dist (execute read s2)"
        have future_s3: "query_future_fresh s3"
          by (rule read_preserves_query_future_fresh[OF future_s2 read_dg])
        from read_outcome[OF read_dg] obtain rest3 where
          counter_s3_s2: "PQueryCounter s3 = PQueryCounter s2"
          by blast
        have counter_s3: "PQueryCounter s3 = PQueryCounter s"
          using counter_s3_s2 counter_s2 by simp
        show
          "wp_event
            (assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. ntimes receive_composition_fri_commits
                (ceil_log (to_nat dg + 1)) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds)))) ?E s3 \<le> ?C"
        proof (rule wp_event_bind_bound_by_cont)
          show "\<not> ?E None"
            by simp
        next
          fix unit s4
          assume assert_out:
            "Some (unit, s4) \<in>
              set_dist (execute (assert (to_nat dg \<le> maxDegree)) s3)"
          have s4_eq: "s4 = s3"
            using assert_out unfolding assert_def
            by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
          have future_s4: "query_future_fresh s4"
            using future_s3 s4_eq by simp
          have counter_s4: "PQueryCounter s4 = PQueryCounter s"
            using counter_s3 s4_eq by simp
          show
            "wp_event
              (ntimes receive_composition_fri_commits
                (ceil_log (to_nat dg + 1)) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds))) ?E s4 \<le> ?C"
          proof (rule wp_event_bind_bound_by_cont)
            show "\<not> ?E None"
              by simp
          next
            fix fl s5
            assume comp_fri:
              "Some (fl, s5) \<in>
                set_dist
                  (execute
                    (ntimes receive_composition_fri_commits
                      (ceil_log (to_nat dg + 1))) s4)"
            have future_s5: "query_future_fresh s5"
              by (rule ntimes_receive_composition_fri_commits_preserves_query_future_fresh
                  [OF comp_fri future_s4])
            have counter_s5_s4: "PQueryCounter s5 = PQueryCounter s4"
              using ntimes_receive_composition_fri_commits_outcome[OF comp_fri]
              by simp
            have counter_s5: "PQueryCounter s5 = PQueryCounter s"
              using counter_s5_s4 counter_s4 by simp
            show
              "wp_event
                (read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds)) ?E s5 \<le> ?C"
            proof (rule wp_event_bind_bound_by_cont)
              show "\<not> ?E None"
                by simp
            next
              fix final query_state
              assume read_final:
                "Some (final, query_state) \<in> set_dist (execute read s5)"
              have future_query: "query_future_fresh query_state"
                by (rule read_preserves_query_future_fresh
                    [OF future_s5 read_final])
              from read_outcome[OF read_final] obtain rest where
                counter_query_s5:
                  "PQueryCounter query_state = PQueryCounter s5"
                by blast
              have counter_query:
                "PQueryCounter query_state = PQueryCounter s"
                using counter_query_s5 counter_s5 by simp
              have event_mono:
                "wp_event
                  (ntimes
                    (verifier_query_round_program fr f_fl f_final as fl
                      final)
                    rounds)
                  ?E query_state \<le>
                 wp_event
                  (ntimes
                    (verifier_query_round_program fr f_fl f_final as fl
                      final)
                    rounds)
                  (\<lambda>out. \<exists>query_idxs \<in> Q.
                    query_rounds_index_list_hit query_state query_idxs
                      rounds out)
                  query_state"
              proof (rule wp_event_mono)
                fix out
                assume "\<exists>query_idxs\<in>Q.
                  query_rounds_index_list_hit s query_idxs rounds out"
                then obtain query_idxs where
                  query_in: "query_idxs \<in> Q"
                  and hit:
                    "query_rounds_index_list_hit s query_idxs rounds out"
                  by blast
                have
                  "query_rounds_index_list_hit query_state query_idxs rounds
                    out"
                  by (rule query_rounds_index_list_hit_counter_eq
                      [OF counter_query hit])
                then show "\<exists>query_idxs\<in>Q.
                  query_rounds_index_list_hit query_state query_idxs rounds
                    out"
                  using query_in by blast
              qed
              also have "... \<le> ?C"
                by (rule wp_ntimes_verifier_query_round_program_fri_index_list_set_bound
                    [OF future_query raw_bound subset])
              finally show
                "wp_event
                  (ntimes
                    (verifier_query_round_program fr f_fl f_final as fl
                      final)
                    rounds)
                  ?E query_state \<le> ?C" .
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma verifier_trace_fri_prefix_preserves_query_future_fresh_exact:
  assumes future: "query_future_fresh s"
    and prefix:
      "Some (header, t) \<in> set_dist (execute verifier_trace_fri_prefix s)"
  shows "query_future_fresh t"
proof -
  obtain fr f_fl where header_eq: "header = (fr, f_fl)"
    by (cases header) auto
  from prefix[unfolded verifier_trace_fri_prefix_def header_eq]
  obtain s1 where
    read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    and trace_fri:
      "Some (f_fl, t) \<in>
        set_dist
          (execute (ntimes receive_trace_fri_commits (ceil_log clength))
            s1)"
    by (auto elim!: set_dist_bindE)
  have future_s1: "query_future_fresh s1"
    by (rule read_preserves_query_future_fresh[OF future read_fr])
  show ?thesis
    by (rule ntimes_receive_trace_fri_commits_preserves_query_future_fresh
        [OF trace_fri future_s1])
qed

lemma wp_trace_fri_query_challenge_pair_set_hit_fixed_challenge_bound:
  assumes trace_future: "trace_fri_future_fresh s"
    and query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenges_space:
      "challenges \<in> fri_challenge_space (ceil_log clength)"
    and projection:
      "fst ` (P \<inter> (UNIV \<times> {challenges})) \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad
      (\<lambda>out. trace_fri_challenge_list_set_hit s {challenges} out \<and>
        trace_fri_query_challenge_pair_set_hit s P out) s \<le>
      (1 / nnreal (CARD('f) ^ ceil_log clength)) *
        (nnreal (card Q) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds)"
proof -
  let ?Hit =
    "\<lambda>out. trace_fri_challenge_list_set_hit s {challenges} out \<and>
      trace_fri_query_challenge_pair_set_hit s P out"
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((_, f_fl), _) \<Rightarrow> map fst f_fl \<in> {challenges}"
  let ?D =
    "nnreal (card Q) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
  have bind_bound:
    "wp_event (verifier_trace_fri_prefix \<bind> verifier_after_trace_fri)
      ?Hit s \<le> wp_event verifier_trace_fri_prefix ?Head s * ?D"
  proof (rule wp_event_bind_bound_by_head_and_cont)
  show "\<not> ?Hit None"
    unfolding trace_fri_challenge_list_set_hit_def
      trace_fri_query_challenge_pair_set_hit_def
      accepted_fri_opening_transcript_def
    by blast
next
  fix header prefix_state
  assume prefix:
    "Some (header, prefix_state) \<in>
      set_dist (execute verifier_trace_fri_prefix s)"
    and not_head:
      "\<not> (case Some (header, prefix_state) of None \<Rightarrow> False
        | Some ((_, f_fl), _) \<Rightarrow> map fst f_fl \<in> {challenges})"
  obtain fr f_fl where header_eq: "header = (fr, f_fl)"
    by (cases header) auto
  have neq: "map fst f_fl \<noteq> challenges"
    using not_head unfolding header_eq by simp
  have zero_le:
    "wp_event (verifier_after_trace_fri header)
      (\<lambda>out. trace_fri_challenge_list_set_hit s {challenges} out \<and>
        trace_fri_query_challenge_pair_set_hit s P out) prefix_state
      \<le> 0"
  proof (rule order_trans)
    show
      "wp_event (verifier_after_trace_fri header)
        (\<lambda>out. trace_fri_challenge_list_set_hit s {challenges} out \<and>
          trace_fri_query_challenge_pair_set_hit s P out) prefix_state
        \<le>
        wp_event (verifier_after_trace_fri header)
          (\<lambda>_. False) prefix_state"
    proof (rule wp_event_mono_on_support)
      fix out
      assume suffix:
        "out \<in>
          set_dist (execute (verifier_after_trace_fri header) prefix_state)"
        and hit:
          "trace_fri_challenge_list_set_hit s {challenges} out \<and>
           trace_fri_query_challenge_pair_set_hit s P out"
      from hit obtain trace_bs fri_dg composition_bs where
        challenges_hit:
          "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
        and trace_in: "trace_bs \<in> {challenges}"
        unfolding trace_fri_challenge_list_set_hit_def
        by blast
      from challenges_hit obtain result final_state where out_eq:
        "out = Some (result, final_state)"
        unfolding accepted_fri_challenges_def by blast
      have prefix':
        "Some ((fr, f_fl), prefix_state) \<in>
          set_dist (execute verifier_trace_fri_prefix s)"
        using prefix header_eq by simp
      have suffix':
        "Some (result, final_state) \<in>
          set_dist
            (execute (verifier_after_trace_fri (fr, f_fl)) prefix_state)"
        using suffix header_eq out_eq by simp
      from verifier_after_trace_fri_accepted_fri_challenges[OF prefix' suffix']
      obtain dg' comp_bs' where challenges_prefix:
        "accepted_fri_challenges s (Some (result, final_state))
          (map fst f_fl) dg' comp_bs'"
        by blast
      have trace_eq: "trace_bs = map fst f_fl"
        using accepted_fri_challenges_unique
          [OF challenges_prefix challenges_hit[unfolded out_eq]]
        by simp
      show False
        using neq trace_eq trace_in by simp
    qed
  next
    show
      "wp_event (verifier_after_trace_fri header)
        (\<lambda>_. False) prefix_state \<le> 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
  qed
  show
    "wp_event (verifier_after_trace_fri header)
      (\<lambda>out. trace_fri_challenge_list_set_hit s {challenges} out \<and>
        trace_fri_query_challenge_pair_set_hit s P out) prefix_state = 0"
    by (rule antisym[OF zero_le]) simp
next
  fix header prefix_state
  assume prefix:
    "Some (header, prefix_state) \<in>
      set_dist (execute verifier_trace_fri_prefix s)"
    and head:
      "(case Some (header, prefix_state) of None \<Rightarrow> False
        | Some ((_, f_fl), _) \<Rightarrow> map fst f_fl \<in> {challenges})"
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
      (\<lambda>out. \<exists>query_idxs \<in> Q.
        query_rounds_index_list_hit s query_idxs rounds out)
      prefix_state \<le> ?D"
    by (rule wp_verifier_after_trace_fri_query_index_list_set_bound
        [OF future_prefix counter_prefix raw_bound subset])
  have hit_to_query:
    "wp_event (verifier_after_trace_fri header)
      (\<lambda>out. trace_fri_challenge_list_set_hit s {challenges} out \<and>
        trace_fri_query_challenge_pair_set_hit s P out) prefix_state
      \<le>
      wp_event (verifier_after_trace_fri header)
        (\<lambda>out. \<exists>query_idxs \<in> Q.
          query_rounds_index_list_hit s query_idxs rounds out) prefix_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume suffix:
      "out \<in>
        set_dist (execute (verifier_after_trace_fri header) prefix_state)"
      and hit:
        "trace_fri_challenge_list_set_hit s {challenges} out \<and>
         trace_fri_query_challenge_pair_set_hit s P out"
    from hit obtain trace_roots trace_bs trace_final fri_dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers where
      openings:
        "accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final fri_dg composition_roots composition_bs
          composition_final query_idxs trace_round_layers
          composition_round_layers"
      and pair: "(query_idxs, trace_bs) \<in> P"
      unfolding trace_fri_query_challenge_pair_set_hit_def by blast
    from openings obtain result final_state where out_eq:
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
    from verifier_after_trace_fri_accepted_fri_challenges[OF prefix' suffix']
    obtain dg' comp_bs' where challenges_prefix:
      "accepted_fri_challenges s (Some (result, final_state))
        (map fst f_fl) dg' comp_bs'"
      by blast
    have challenges_openings:
      "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
      using openings
      unfolding accepted_fri_opening_transcript_def
      apply (elim exE conjE)
      apply assumption
      done
    have trace_eq: "trace_bs = map fst f_fl"
      using accepted_fri_challenges_unique
        [OF challenges_prefix challenges_openings[unfolded out_eq]]
      by simp
    have query_in: "query_idxs \<in> Q"
    proof -
      have "query_idxs \<in> fst ` (P \<inter> (UNIV \<times> {challenges}))"
        using pair trace_eq f_fl_eq by force
      then show ?thesis
        using projection by blast
    qed
    have query_hit:
      "query_rounds_index_list_hit s query_idxs rounds out"
      by (rule accepted_fri_opening_transcript_imp_query_rounds_index_list_hit
          [OF openings])
    show "\<exists>query_idxs \<in> Q.
      query_rounds_index_list_hit s query_idxs rounds out"
      using query_in query_hit by blast
  qed
  show
    "wp_event (verifier_after_trace_fri header)
      (\<lambda>out. trace_fri_challenge_list_set_hit s {challenges} out \<and>
        trace_fri_query_challenge_pair_set_hit s P out) prefix_state
      \<le> ?D"
    by (rule order_trans[OF hit_to_query event_bound])
  qed
  have head_bound:
    "wp_event verifier_trace_fri_prefix ?Head s \<le>
      1 / nnreal (CARD('f) ^ ceil_log clength)"
  proof -
    have "wp_event verifier_trace_fri_prefix ?Head s \<le>
        nnreal (card {challenges}) / nnreal (CARD('f) ^ ceil_log clength)"
      by (rule wp_verifier_trace_fri_prefix_challenge_space_set_bound
          [where B = "{challenges}", OF trace_future])
        (use challenges_space in auto)
    then show ?thesis by simp
  qed
  show ?thesis
    unfolding verify_monad_trace_fri_decomposition
    apply (rule order_trans)
     apply (rule bind_bound)
    apply (rule mult_right_mono[OF head_bound])
    apply simp
    done
qed

lemma wp_trace_fri_query_challenge_pair_set_hit_bound_from_query_fiber_sum:
  assumes trace_future: "trace_fri_future_fresh s"
    and query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and projection:
      "\<And>challenges.
        fst ` (P \<inter> (UNIV \<times> {challenges})) \<subseteq>
          Q challenges"
    and subset: "\<And>challenges. Q challenges \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad
      (trace_fri_query_challenge_pair_set_hit s P) s \<le>
      (\<Sum>challenges \<in> fri_challenge_space (ceil_log clength).
        (1 / nnreal (CARD('f) ^ ceil_log clength)) *
          (nnreal (card (Q challenges)) *
            (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds))"
proof -
  let ?I = "fri_challenge_space (ceil_log clength)"
  let ?E =
    "\<lambda>challenges out.
      trace_fri_challenge_list_set_hit s {challenges} out \<and>
      trace_fri_query_challenge_pair_set_hit s P out"
  let ?B =
    "\<lambda>challenges.
      (1 / nnreal (CARD('f) ^ ceil_log clength)) *
        (nnreal (card (Q challenges)) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds)"
  have split:
    "wp_event verify_monad
      (trace_fri_query_challenge_pair_set_hit s P) s \<le>
      wp_event verify_monad
        (\<lambda>out. \<exists>challenges \<in> ?I. ?E challenges out) s"
  proof (rule wp_event_mono)
    fix out
    assume hit: "trace_fri_query_challenge_pair_set_hit s P out"
    from hit obtain trace_roots trace_bs trace_final fri_dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers where
      openings:
        "accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final fri_dg composition_roots composition_bs
          composition_final query_idxs trace_round_layers
          composition_round_layers"
      unfolding trace_fri_query_challenge_pair_set_hit_def by blast
    have challenges:
      "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
      using openings
      unfolding accepted_fri_opening_transcript_def
      apply (elim exE conjE)
      apply assumption
      done
    have trace_space: "trace_bs \<in> ?I"
      by (rule accepted_fri_challenges_trace_space[OF challenges])
    have challenge_hit:
      "trace_fri_challenge_list_set_hit s {trace_bs} out"
      unfolding trace_fri_challenge_list_set_hit_def
      using challenges by blast
    show "\<exists>challenges \<in> ?I. ?E challenges out"
      using trace_space challenge_hit hit by blast
  qed
  also have "... \<le> (\<Sum>challenges \<in> ?I. ?B challenges)"
  proof (rule wp_event_finite_union_bound_fri_exact)
    show "finite ?I"
      by (rule finite_fri_challenge_space)
  next
    fix challenges
    assume challenges: "challenges \<in> ?I"
    show
      "wp_event verify_monad (?E challenges) s \<le> ?B challenges"
      by (rule wp_trace_fri_query_challenge_pair_set_hit_fixed_challenge_bound
          [OF trace_future query_future raw_bound challenges
            projection subset])
  qed
  finally show ?thesis .
qed

lemma wp_trace_fri_query_challenge_pair_set_hit_bound_from_query_fibers:
  fixes C :: prob
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and projection:
      "\<And>challenges.
        fst ` (P \<inter> (UNIV \<times> {challenges})) \<subseteq>
          Q challenges"
    and subset: "\<And>challenges. Q challenges \<subseteq> fri_query_index_list_space"
    and bound:
      "\<And>challenges.
        nnreal (card (Q challenges)) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_query_challenge_pair_set_hit s P) s \<le> C"
  unfolding verify_monad_trace_fri_decomposition
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> trace_fri_query_challenge_pair_set_hit s P None"
    unfolding trace_fri_query_challenge_pair_set_hit_def
      accepted_fri_opening_transcript_def
    by blast
next
  fix header prefix_state
  assume prefix:
    "Some (header, prefix_state) \<in>
      set_dist (execute verifier_trace_fri_prefix s)"
  obtain fr f_fl where header_eq: "header = (fr, f_fl)"
    by (cases header) auto
  have future_prefix: "query_future_fresh prefix_state"
    by (rule verifier_trace_fri_prefix_preserves_query_future_fresh_exact
        [OF future prefix])
  have counter_prefix: "PQueryCounter prefix_state = PQueryCounter s"
    using verifier_trace_fri_prefix_outcome[OF prefix[unfolded header_eq]]
    by simp
  let ?Q = "Q (map fst f_fl)"
  have event_bound:
    "wp_event (verifier_after_trace_fri header)
      (\<lambda>out. \<exists>query_idxs \<in> ?Q.
        query_rounds_index_list_hit s query_idxs rounds out)
      prefix_state \<le>
      nnreal (card ?Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule wp_verifier_after_trace_fri_query_index_list_set_bound
        [OF future_prefix counter_prefix raw_bound subset])
  have pair_to_query:
    "wp_event (verifier_after_trace_fri header)
      (trace_fri_query_challenge_pair_set_hit s P) prefix_state \<le>
     wp_event (verifier_after_trace_fri header)
      (\<lambda>out. \<exists>query_idxs \<in> ?Q.
        query_rounds_index_list_hit s query_idxs rounds out) prefix_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume suffix:
      "out \<in>
        set_dist (execute (verifier_after_trace_fri header) prefix_state)"
      and hit: "trace_fri_query_challenge_pair_set_hit s P out"
    from hit obtain trace_roots trace_bs trace_final fri_dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers where
      openings:
        "accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final fri_dg composition_roots composition_bs
          composition_final query_idxs trace_round_layers
          composition_round_layers"
      and pair: "(query_idxs, trace_bs) \<in> P"
      unfolding trace_fri_query_challenge_pair_set_hit_def by blast
    from openings obtain result final_state where out_eq:
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
    from verifier_after_trace_fri_accepted_fri_challenges[OF prefix' suffix']
    obtain dg' comp_bs' where challenges_prefix:
      "accepted_fri_challenges s (Some (result, final_state))
        (map fst f_fl) dg' comp_bs'"
      by blast
    have challenges_openings:
      "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
      using openings
      unfolding accepted_fri_opening_transcript_def
      apply (elim exE conjE)
      apply assumption
      done
    have trace_eq: "trace_bs = map fst f_fl"
      using accepted_fri_challenges_unique
        [OF challenges_prefix challenges_openings[unfolded out_eq]]
      by simp
    have query_in: "query_idxs \<in> ?Q"
    proof -
      have "query_idxs \<in>
          fst ` (P \<inter> (UNIV \<times> {map fst f_fl}))"
        using pair trace_eq by force
      then show ?thesis
        using projection[of "map fst f_fl"] by blast
    qed
    have query_hit:
      "query_rounds_index_list_hit s query_idxs rounds out"
      by (rule accepted_fri_opening_transcript_imp_query_rounds_index_list_hit
          [OF openings])
    show "\<exists>query_idxs \<in> ?Q.
      query_rounds_index_list_hit s query_idxs rounds out"
      using query_in query_hit by blast
  qed
  show
    "wp_event (verifier_after_trace_fri header)
      (trace_fri_query_challenge_pair_set_hit s P) prefix_state \<le> C"
    by (rule order_trans[OF pair_to_query])
      (rule order_trans[OF event_bound bound])
qed

lemma wp_trace_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_fibers:
  fixes C_challenge C_query :: prob
  assumes trace_future: "trace_fri_future_fresh s"
    and query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenge_subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and challenge_bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le>
        C_challenge"
    and projection:
      "\<And>challenges.
        fst ` ((P \<inter> (UNIV \<times> (- B))) \<inter>
          (UNIV \<times> {challenges})) \<subseteq> Q challenges"
    and subset: "\<And>challenges. Q challenges \<subseteq> fri_query_index_list_space"
    and query_bound:
      "\<And>challenges.
        nnreal (card (Q challenges)) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds \<le> C_query"
  shows
    "wp_event verify_monad
      (trace_fri_query_challenge_pair_set_hit s P) s \<le>
      C_challenge + C_query"
proof -
  let ?Outside = "P \<inter> (UNIV \<times> (- B))"
  have split:
    "wp_event verify_monad
      (trace_fri_query_challenge_pair_set_hit s P) s \<le>
     wp_event verify_monad
      (\<lambda>out. trace_fri_challenge_list_set_hit s B out \<or>
        trace_fri_query_challenge_pair_set_hit s ?Outside out) s"
  proof (rule wp_event_mono)
    fix out
    assume hit: "trace_fri_query_challenge_pair_set_hit s P out"
    from hit obtain trace_roots trace_bs trace_final fri_dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers where
      openings:
        "accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final fri_dg composition_roots composition_bs
          composition_final query_idxs trace_round_layers
          composition_round_layers"
      and pair: "(query_idxs, trace_bs) \<in> P"
      unfolding trace_fri_query_challenge_pair_set_hit_def by blast
    show
      "trace_fri_challenge_list_set_hit s B out \<or>
        trace_fri_query_challenge_pair_set_hit s ?Outside out"
    proof (cases "trace_bs \<in> B")
      case True
      have challenges:
        "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
        using openings
        unfolding accepted_fri_opening_transcript_def
        apply (elim exE conjE)
        apply assumption
        done
      then have "trace_fri_challenge_list_set_hit s B out"
        using True unfolding trace_fri_challenge_list_set_hit_def by blast
      then show ?thesis by simp
    next
      case False
      have "(query_idxs, trace_bs) \<in> ?Outside"
        using pair False by simp
      then have "trace_fri_query_challenge_pair_set_hit s ?Outside out"
        unfolding trace_fri_query_challenge_pair_set_hit_def
        using openings by blast
      then show ?thesis by simp
    qed
  qed
  also have "... \<le>
      wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s +
      wp_event verify_monad
        (trace_fri_query_challenge_pair_set_hit s ?Outside) s"
    by (rule wp_event_union_bound)
  also have "... \<le> C_challenge + C_query"
  proof (rule add_mono)
    show "wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s
      \<le> C_challenge"
      by (rule order_trans[
          OF wp_verify_monad_trace_fri_challenge_list_set_bound
            [OF trace_future challenge_subset] challenge_bound])
    show
      "wp_event verify_monad
        (trace_fri_query_challenge_pair_set_hit s ?Outside) s \<le>
        C_query"
      by (rule wp_trace_fri_query_challenge_pair_set_hit_bound_from_query_fibers
          [OF query_future raw_bound projection subset query_bound])
  qed
  finally show ?thesis .
qed

lemma
  wp_composition_fri_query_challenge_pair_set_hit_bound_from_query_fibers:
  fixes C :: prob
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and projection:
      "\<And>dg challenges.
        fst ` (P dg \<inter> (UNIV \<times> {challenges})) \<subseteq>
          Q dg challenges"
    and subset: "\<And>dg challenges. Q dg challenges \<subseteq> fri_query_index_list_space"
    and bound:
      "\<And>dg challenges.
        nnreal (card (Q dg challenges)) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s P) s \<le> C"
  unfolding verify_monad_composition_fri_decomposition
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> composition_fri_query_challenge_pair_set_hit s P None"
    unfolding composition_fri_query_challenge_pair_set_hit_def
      accepted_fri_opening_transcript_def
    by blast
next
  fix header prefix_state
  assume prefix:
    "Some (header, prefix_state) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
  obtain fr f_fl f_final as dg fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg, fl)"
    by (cases header) auto
  have future_prefix: "query_future_fresh prefix_state"
    by (rule verifier_composition_fri_prefix_preserves_query_future_fresh
        [OF future prefix])
  have counter_prefix: "PQueryCounter prefix_state = PQueryCounter s"
    using verifier_composition_fri_prefix_outcome[OF prefix[unfolded header_eq]]
    by simp
  let ?Q = "Q dg (map fst fl)"
  have event_bound:
    "wp_event (verifier_after_composition_fri header)
      (\<lambda>out. \<exists>query_idxs \<in> ?Q.
        query_rounds_index_list_hit s query_idxs rounds out)
      prefix_state \<le>
      nnreal (card ?Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule wp_verifier_after_composition_fri_query_index_list_set_bound
        [OF future_prefix counter_prefix raw_bound subset])
  have pair_to_query:
    "wp_event (verifier_after_composition_fri header)
      (composition_fri_query_challenge_pair_set_hit s P) prefix_state \<le>
     wp_event (verifier_after_composition_fri header)
      (\<lambda>out. \<exists>query_idxs \<in> ?Q.
        query_rounds_index_list_hit s query_idxs rounds out) prefix_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume suffix:
      "out \<in>
        set_dist (execute (verifier_after_composition_fri header)
          prefix_state)"
      and hit: "composition_fri_query_challenge_pair_set_hit s P out"
    from hit obtain trace_roots trace_bs trace_final fri_dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers where
      openings:
        "accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final fri_dg composition_roots composition_bs
          composition_final query_idxs trace_round_layers
          composition_round_layers"
      and pair: "(query_idxs, composition_bs) \<in> P fri_dg"
      unfolding composition_fri_query_challenge_pair_set_hit_def by blast
    from openings obtain result final_state where out_eq:
      "out = Some (result, final_state)"
      unfolding accepted_fri_opening_transcript_def by blast
    have prefix':
      "Some ((fr, f_fl, f_final, as, dg, fl), prefix_state) \<in>
        set_dist (execute verifier_composition_fri_prefix s)"
      using prefix header_eq by simp
    have suffix':
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (verifier_after_composition_fri
              (fr, f_fl, f_final, as, dg, fl))
            prefix_state)"
      using suffix header_eq out_eq by simp
    have challenges_prefix:
      "accepted_fri_challenges s (Some (result, final_state))
        (map fst f_fl) dg (map fst fl)"
      by (rule verifier_after_composition_fri_accepted_fri_challenges
          [OF prefix' suffix'])
    have challenges_openings:
      "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
      using openings
      unfolding accepted_fri_opening_transcript_def
      apply (elim exE conjE)
      apply assumption
      done
    have eqs: "fri_dg = dg \<and> composition_bs = map fst fl"
      using accepted_fri_challenges_unique
        [OF challenges_prefix challenges_openings[unfolded out_eq]]
      by simp
    have query_in: "query_idxs \<in> ?Q"
    proof -
      have "query_idxs \<in>
          fst ` (P dg \<inter> (UNIV \<times> {map fst fl}))"
        using pair eqs by force
      then show ?thesis
        using projection[of dg "map fst fl"] by blast
    qed
    have query_hit:
      "query_rounds_index_list_hit s query_idxs rounds out"
      by (rule accepted_fri_opening_transcript_imp_query_rounds_index_list_hit
          [OF openings])
    show "\<exists>query_idxs \<in> ?Q.
      query_rounds_index_list_hit s query_idxs rounds out"
      using query_in query_hit by blast
  qed
  show
    "wp_event (verifier_after_composition_fri header)
      (composition_fri_query_challenge_pair_set_hit s P) prefix_state \<le> C"
    by (rule order_trans[OF pair_to_query])
      (rule order_trans[OF event_bound bound])
qed

lemma wp_composition_fri_query_challenge_pair_set_hit_fixed_challenge_bound:
  assumes composition_future: "composition_fri_future_fresh s"
    and query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenges_space:
      "challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and projection:
      "fst ` (P dg \<inter> (UNIV \<times> {challenges})) \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad
      (\<lambda>out.
        composition_fri_challenge_list_set_hit s
          (\<lambda>dg'. if dg' = dg then {challenges} else {}) out \<and>
        composition_fri_query_challenge_pair_set_hit s P out) s \<le>
      (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
        (nnreal (card Q) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds)"
proof -
  let ?B = "\<lambda>dg'. if dg' = dg then {challenges} else {}"
  let ?Hit =
    "\<lambda>out. composition_fri_challenge_list_set_hit s ?B out \<and>
      composition_fri_query_challenge_pair_set_hit s P out"
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((_, _, _, _, dg', fl), _) \<Rightarrow>
          dg' = dg \<and> map fst fl = challenges"
  let ?D =
    "nnreal (card Q) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
  have bind_bound:
    "wp_event
      (verifier_composition_fri_prefix \<bind> verifier_after_composition_fri)
      ?Hit s \<le> wp_event verifier_composition_fri_prefix ?Head s * ?D"
  proof (rule wp_event_bind_bound_by_head_and_cont)
  show "\<not> ?Hit None"
    unfolding composition_fri_challenge_list_set_hit_def
      composition_fri_query_challenge_pair_set_hit_def
      accepted_fri_opening_transcript_def
    by blast
next
  fix header prefix_state
  assume prefix:
    "Some (header, prefix_state) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
    and not_head:
      "\<not> (case Some (header, prefix_state) of None \<Rightarrow> False
        | Some ((_, _, _, _, dg', fl), _) \<Rightarrow>
            dg' = dg \<and> map fst fl = challenges)"
  obtain fr f_fl f_final as dg' fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg', fl)"
    by (cases header) auto
  have not_fixed: "dg' \<noteq> dg \<or> map fst fl \<noteq> challenges"
    using not_head unfolding header_eq by simp
  have zero_le:
    "wp_event (verifier_after_composition_fri header)
      (\<lambda>out.
        composition_fri_challenge_list_set_hit s
          (\<lambda>dg'. if dg' = dg then {challenges} else {}) out \<and>
        composition_fri_query_challenge_pair_set_hit s P out) prefix_state
      \<le> 0"
  proof (rule order_trans)
    show
      "wp_event (verifier_after_composition_fri header)
        (\<lambda>out.
          composition_fri_challenge_list_set_hit s
            (\<lambda>dg'. if dg' = dg then {challenges} else {}) out \<and>
          composition_fri_query_challenge_pair_set_hit s P out) prefix_state
        \<le>
        wp_event (verifier_after_composition_fri header)
          (\<lambda>_. False) prefix_state"
    proof (rule wp_event_mono_on_support)
      fix out
      assume suffix:
        "out \<in>
          set_dist
            (execute (verifier_after_composition_fri header) prefix_state)"
        and hit:
          "composition_fri_challenge_list_set_hit s
            (\<lambda>dg'. if dg' = dg then {challenges} else {}) out \<and>
           composition_fri_query_challenge_pair_set_hit s P out"
      from hit obtain trace_bs fri_dg composition_bs where
        challenges_hit:
          "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
        and comp_in:
          "composition_bs \<in>
            (if fri_dg = dg then {challenges} else {})"
        unfolding composition_fri_challenge_list_set_hit_def
        by blast
      from challenges_hit obtain result final_state where out_eq:
        "out = Some (result, final_state)"
        unfolding accepted_fri_challenges_def by blast
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
      have challenges_prefix:
        "accepted_fri_challenges s (Some (result, final_state))
          (map fst f_fl) dg' (map fst fl)"
        by (rule verifier_after_composition_fri_accepted_fri_challenges
            [OF prefix' suffix'])
      have eqs: "fri_dg = dg' \<and> composition_bs = map fst fl"
        using accepted_fri_challenges_unique
          [OF challenges_prefix challenges_hit[unfolded out_eq]]
        by simp
      have fixed: "fri_dg = dg \<and> composition_bs = challenges"
        using comp_in by (cases "fri_dg = dg") auto
      show False
        using not_fixed eqs fixed by simp
    qed
  next
    show
      "wp_event (verifier_after_composition_fri header)
        (\<lambda>_. False) prefix_state \<le> 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
  qed
  show
    "wp_event (verifier_after_composition_fri header)
      (\<lambda>out.
        composition_fri_challenge_list_set_hit s
          (\<lambda>dg'. if dg' = dg then {challenges} else {}) out \<and>
        composition_fri_query_challenge_pair_set_hit s P out) prefix_state
      = 0"
    by (rule antisym[OF zero_le]) simp
next
  fix header prefix_state
  assume prefix:
    "Some (header, prefix_state) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
    and head:
      "(case Some (header, prefix_state) of None \<Rightarrow> False
        | Some ((_, _, _, _, dg', fl), _) \<Rightarrow>
            dg' = dg \<and> map fst fl = challenges)"
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
      (\<lambda>out. \<exists>query_idxs \<in> Q.
        query_rounds_index_list_hit s query_idxs rounds out)
      prefix_state \<le> ?D"
    by (rule wp_verifier_after_composition_fri_query_index_list_set_bound
        [OF future_prefix counter_prefix raw_bound subset])
  have hit_to_query:
    "wp_event (verifier_after_composition_fri header)
      (\<lambda>out.
        composition_fri_challenge_list_set_hit s
          (\<lambda>dg'. if dg' = dg then {challenges} else {}) out \<and>
        composition_fri_query_challenge_pair_set_hit s P out) prefix_state
      \<le>
      wp_event (verifier_after_composition_fri header)
        (\<lambda>out. \<exists>query_idxs \<in> Q.
          query_rounds_index_list_hit s query_idxs rounds out) prefix_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume suffix:
      "out \<in>
        set_dist (execute (verifier_after_composition_fri header)
          prefix_state)"
      and hit:
        "composition_fri_challenge_list_set_hit s
          (\<lambda>dg'. if dg' = dg then {challenges} else {}) out \<and>
         composition_fri_query_challenge_pair_set_hit s P out"
    from hit obtain trace_roots trace_bs trace_final fri_dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers where
      openings:
        "accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final fri_dg composition_roots composition_bs
          composition_final query_idxs trace_round_layers
          composition_round_layers"
      and pair: "(query_idxs, composition_bs) \<in> P fri_dg"
      unfolding composition_fri_query_challenge_pair_set_hit_def by blast
    from openings obtain result final_state where out_eq:
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
    have challenges_prefix:
      "accepted_fri_challenges s (Some (result, final_state))
        (map fst f_fl) dg' (map fst fl)"
      by (rule verifier_after_composition_fri_accepted_fri_challenges
          [OF prefix' suffix'])
    have challenges_openings:
      "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
      using openings
      unfolding accepted_fri_opening_transcript_def
      apply (elim exE conjE)
      apply assumption
      done
    have eqs: "fri_dg = dg' \<and> composition_bs = map fst fl"
      using accepted_fri_challenges_unique
        [OF challenges_prefix challenges_openings[unfolded out_eq]]
      by simp
    have query_in: "query_idxs \<in> Q"
    proof -
      have "query_idxs \<in> fst ` (P dg \<inter> (UNIV \<times> {challenges}))"
        using pair eqs dg_eq fl_eq by force
      then show ?thesis
        using projection by blast
    qed
    have query_hit:
      "query_rounds_index_list_hit s query_idxs rounds out"
      by (rule accepted_fri_opening_transcript_imp_query_rounds_index_list_hit
          [OF openings])
    show "\<exists>query_idxs \<in> Q.
      query_rounds_index_list_hit s query_idxs rounds out"
      using query_in query_hit by blast
  qed
  show
    "wp_event (verifier_after_composition_fri header)
      (\<lambda>out.
        composition_fri_challenge_list_set_hit s
          (\<lambda>dg'. if dg' = dg then {challenges} else {}) out \<and>
        composition_fri_query_challenge_pair_set_hit s P out) prefix_state
      \<le> ?D"
    by (rule order_trans[OF hit_to_query event_bound])
  qed
  have head_bound:
    "wp_event verifier_composition_fri_prefix ?Head s \<le>
      1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
  proof (rule order_trans)
    let ?SetHead =
      "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((_, _, _, _, dg', fl), _) \<Rightarrow> map fst fl \<in> ?B dg'"
    show "wp_event verifier_composition_fri_prefix ?Head s \<le>
        wp_event verifier_composition_fri_prefix ?SetHead s"
      by (rule wp_event_mono_on_support)
        (auto split: option.splits prod.splits)
    show "wp_event verifier_composition_fri_prefix ?SetHead s \<le>
        1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
      by (rule wp_verifier_composition_fri_prefix_challenge_space_set_bound
          [OF composition_future])
        (use challenges_space in auto)
  qed
  show ?thesis
    unfolding verify_monad_composition_fri_decomposition
    apply (rule order_trans)
     apply (rule bind_bound)
    apply (rule mult_right_mono[OF head_bound])
    apply simp
    done
qed

lemma wp_composition_fri_query_challenge_pair_set_hit_bound_from_query_fiber_sum:
  assumes composition_future: "composition_fri_future_fresh s"
    and query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and projection:
      "\<And>dg challenges.
        fst ` (P dg \<inter> (UNIV \<times> {challenges})) \<subseteq>
          Q dg challenges"
    and subset:
      "\<And>dg challenges. Q dg challenges \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s P) s \<le>
      (\<Sum>dg \<in> UNIV.
        \<Sum>challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
          (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
            (nnreal (card (Q dg challenges)) *
              (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds))"
proof -
  let ?I =
    "SIGMA dg:UNIV. fri_challenge_space (ceil_log (to_nat dg + 1))"
  let ?E =
    "\<lambda>p out.
      composition_fri_challenge_list_set_hit s
        (\<lambda>dg'. if dg' = fst p then {snd p} else {}) out \<and>
      composition_fri_query_challenge_pair_set_hit s P out"
  let ?B =
    "\<lambda>p.
      (1 / nnreal (CARD('f) ^ ceil_log (to_nat (fst p) + 1))) *
        (nnreal (card (Q (fst p) (snd p))) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds)"
  have split:
    "wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s P) s \<le>
      wp_event verify_monad
        (\<lambda>out. \<exists>p \<in> ?I. ?E p out) s"
  proof (rule wp_event_mono)
    fix out
    assume hit: "composition_fri_query_challenge_pair_set_hit s P out"
    from hit obtain trace_roots trace_bs trace_final fri_dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers where
      openings:
        "accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final fri_dg composition_roots composition_bs
          composition_final query_idxs trace_round_layers
          composition_round_layers"
      unfolding composition_fri_query_challenge_pair_set_hit_def by blast
    have challenges:
      "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
      using openings
      unfolding accepted_fri_opening_transcript_def
      apply (elim exE conjE)
      apply assumption
      done
    have comp_space:
      "composition_bs \<in> fri_challenge_space (ceil_log (to_nat fri_dg + 1))"
      by (rule accepted_fri_challenges_composition_space[OF challenges])
    have challenge_hit:
      "composition_fri_challenge_list_set_hit s
        (\<lambda>dg'. if dg' = fri_dg then {composition_bs} else {}) out"
      unfolding composition_fri_challenge_list_set_hit_def
      using challenges by auto
    have "(fri_dg, composition_bs) \<in> ?I"
      using comp_space by simp
    then show "\<exists>p \<in> ?I. ?E p out"
    proof (intro bexI[where x = "(fri_dg, composition_bs)"])
      show "?E (fri_dg, composition_bs) out"
        using challenge_hit hit by (simp only: fst_conv snd_conv)
      show "(fri_dg, composition_bs) \<in> ?I"
        using comp_space by simp
    qed
  qed
  also have "... \<le> (\<Sum>p \<in> ?I. ?B p)"
  proof (rule wp_event_finite_union_bound_fri_exact)
    show "finite ?I"
      by (simp add: finite_fri_challenge_space)
  next
    fix p
    assume p_in: "p \<in> ?I"
    obtain dg challenges where p_eq: "p = (dg, challenges)"
      by (cases p)
    have challenges:
      "challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
      using p_in p_eq by simp
    have fixed_bound:
      "wp_event verify_monad
        (\<lambda>out. composition_fri_challenge_list_set_hit s
          (\<lambda>dg'. if dg' = dg then {challenges} else {}) out \<and>
          composition_fri_query_challenge_pair_set_hit s P out) s
        \<le> 1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) *
          (nnreal (card (Q dg challenges)) *
            (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds)"
      by (rule
          wp_composition_fri_query_challenge_pair_set_hit_fixed_challenge_bound
            [OF composition_future query_future raw_bound challenges
              projection subset])
    show "wp_event verify_monad (?E p) s \<le> ?B p"
      unfolding p_eq using fixed_bound by (simp only: fst_conv snd_conv)
  qed
  also have "... =
      (\<Sum>dg \<in> UNIV.
        \<Sum>challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
          (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
            (nnreal (card (Q dg challenges)) *
              (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds))"
    by (subst sum.Sigma) (simp_all add: finite_fri_challenge_space case_prod_beta)
  finally show ?thesis .
qed

lemma wp_composition_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_fibers:
  fixes C_challenge C_query :: prob
  assumes composition_future: "composition_fri_future_fresh s"
    and query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenge_subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and challenge_bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C_challenge"
    and projection:
      "\<And>dg challenges.
        fst ` ((P dg \<inter> (UNIV \<times> (- B dg))) \<inter>
          (UNIV \<times> {challenges})) \<subseteq> Q dg challenges"
    and subset:
      "\<And>dg challenges. Q dg challenges \<subseteq> fri_query_index_list_space"
    and query_bound:
      "\<And>dg challenges.
        nnreal (card (Q dg challenges)) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds \<le> C_query"
  shows
    "wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s P) s \<le>
      C_challenge + C_query"
proof -
  let ?Outside = "\<lambda>dg. P dg \<inter> (UNIV \<times> (- B dg))"
  have split:
    "wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s P) s \<le>
     wp_event verify_monad
      (\<lambda>out. composition_fri_challenge_list_set_hit s B out \<or>
        composition_fri_query_challenge_pair_set_hit s ?Outside out) s"
  proof (rule wp_event_mono)
    fix out
    assume hit: "composition_fri_query_challenge_pair_set_hit s P out"
    from hit obtain trace_roots trace_bs trace_final fri_dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers where
      openings:
        "accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final fri_dg composition_roots composition_bs
          composition_final query_idxs trace_round_layers
          composition_round_layers"
      and pair: "(query_idxs, composition_bs) \<in> P fri_dg"
      unfolding composition_fri_query_challenge_pair_set_hit_def by blast
    show
      "composition_fri_challenge_list_set_hit s B out \<or>
        composition_fri_query_challenge_pair_set_hit s ?Outside out"
    proof (cases "composition_bs \<in> B fri_dg")
      case True
      have challenges:
        "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
        using openings
        unfolding accepted_fri_opening_transcript_def
        apply (elim exE conjE)
        apply assumption
        done
      then have "composition_fri_challenge_list_set_hit s B out"
        using True unfolding composition_fri_challenge_list_set_hit_def
        by blast
      then show ?thesis by simp
    next
      case False
      have "(query_idxs, composition_bs) \<in> ?Outside fri_dg"
        using pair False by simp
      then have
        "composition_fri_query_challenge_pair_set_hit s ?Outside out"
        unfolding composition_fri_query_challenge_pair_set_hit_def
        using openings by blast
      then show ?thesis by simp
    qed
  qed
  also have "... \<le>
      wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s +
      wp_event verify_monad
        (composition_fri_query_challenge_pair_set_hit s ?Outside) s"
    by (rule wp_event_union_bound)
  also have "... \<le> C_challenge + C_query"
  proof (rule add_mono)
    show
      "wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s
        \<le> C_challenge"
      by (rule wp_verify_monad_composition_fri_challenge_list_set_bound
          [OF composition_future challenge_subset challenge_bound])
    show
      "wp_event verify_monad
        (composition_fri_query_challenge_pair_set_hit s ?Outside) s \<le>
        C_query"
      by (rule
          wp_composition_fri_query_challenge_pair_set_hit_bound_from_query_fibers
          [OF query_future raw_bound projection subset query_bound])
  qed
  finally show ?thesis .
qed

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_challenge_cover_and_query_fibers:
  fixes C_challenge C_query :: prob
  assumes trace_future: "trace_fri_future_fresh s"
    and query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenge_subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and challenge_bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le>
        C_challenge"
    and projection:
      "\<And>challenges.
        fst `
          (((trace_fri_sampled_query_bad_pair_union \<inter>
              (fri_query_index_list_space \<times> UNIV)) \<inter>
             (UNIV \<times> (- B))) \<inter>
            (UNIV \<times> {challenges})) \<subseteq> Q challenges"
    and subset: "\<And>challenges. Q challenges \<subseteq> fri_query_index_list_space"
    and query_bound:
      "\<And>challenges.
        nnreal (card (Q challenges)) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds \<le> C_query"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s \<le>
      C_challenge + C_query"
proof -
  let ?P =
    "trace_fri_sampled_query_bad_pair_union \<inter>
      (fri_query_index_list_space \<times> UNIV)"
  have "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> wp_event verify_monad
        (trace_fri_query_challenge_pair_set_hit s ?P) s"
    by (rule
        wp_trace_fri_sampled_query_bad_candidate_bound_by_restricted_query_challenge_union_hit)
  also have "... \<le> C_challenge + C_query"
    by (rule
        wp_trace_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_fibers
        [OF trace_future query_future raw_bound challenge_subset
          challenge_bound projection subset query_bound])
  finally show ?thesis .
qed

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_challenge_cover_and_query_fibers:
  fixes C_challenge C_query :: prob
  assumes composition_future: "composition_fri_future_fresh s"
    and query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenge_subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and challenge_bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C_challenge"
    and projection:
      "\<And>dg challenges.
        fst `
          (((composition_fri_sampled_query_bad_pair_union dg \<inter>
              (fri_query_index_list_space \<times> UNIV)) \<inter>
             (UNIV \<times> (- B dg))) \<inter>
            (UNIV \<times> {challenges})) \<subseteq> Q dg challenges"
    and subset:
      "\<And>dg challenges. Q dg challenges \<subseteq> fri_query_index_list_space"
    and query_bound:
      "\<And>dg challenges.
        nnreal (card (Q dg challenges)) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds \<le> C_query"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_query_bad_candidate s) s \<le>
      C_challenge + C_query"
proof -
  let ?P =
    "\<lambda>dg. composition_fri_sampled_query_bad_pair_union dg \<inter>
      (fri_query_index_list_space \<times> UNIV)"
  have "wp_event verify_monad
      (composition_fri_sampled_query_bad_candidate s) s \<le>
    wp_event verify_monad
      (composition_fri_query_challenge_pair_set_hit s ?P) s"
    by (rule
        wp_composition_fri_sampled_query_bad_candidate_bound_by_restricted_query_challenge_union_hit)
  also have "... \<le> C_challenge + C_query"
    by (rule
        wp_composition_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_fibers
        [OF composition_future query_future raw_bound challenge_subset
          challenge_bound projection subset query_bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_fibers:
  fixes C_challenge C_query :: prob
  assumes trace_future: "trace_fri_future_fresh s"
    and query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenge_subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and challenge_bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le>
        C_challenge"
    and query_bound:
      "\<And>challenges.
        nnreal
          (card
            (generic_fri_sampled_query_query_fiber trace_table_low_degree
              (Not \<circ> trace_table_low_degree) (clength - 1) challenges)) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds \<le> C_query"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s \<le>
      C_challenge + C_query"
proof (rule
    wp_trace_fri_sampled_query_bad_candidate_bound_from_challenge_cover_and_query_fibers
    [OF trace_future query_future raw_bound challenge_subset challenge_bound])
  fix challenges
  show
    "fst `
      (((trace_fri_sampled_query_bad_pair_union \<inter>
          (fri_query_index_list_space \<times> UNIV)) \<inter>
        (UNIV \<times> (- B))) \<inter>
        (UNIV \<times> {challenges}))
      \<subseteq>
      generic_fri_sampled_query_query_fiber trace_table_low_degree
        (Not \<circ> trace_table_low_degree) (clength - 1) challenges"
    unfolding trace_fri_sampled_query_bad_pair_union_def
      generic_fri_sampled_query_query_fiber_def
      generic_fri_sampled_query_restricted_bad_pairs_def
      fri_query_challenge_pair_query_fiber_def
    by auto
next
  fix challenges
  show
    "generic_fri_sampled_query_query_fiber trace_table_low_degree
      (Not \<circ> trace_table_low_degree) (clength - 1) challenges
    \<subseteq> fri_query_index_list_space"
    by (rule generic_fri_sampled_query_query_fiber_subset)
next
  fix challenges
  show
    "nnreal
      (card
        (generic_fri_sampled_query_query_fiber trace_table_low_degree
          (Not \<circ> trace_table_low_degree) (clength - 1) challenges)) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds \<le> C_query"
    by (rule query_bound)
qed

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_generic_challenge_cover_and_fibers:
  fixes C_challenge C_query :: prob
  assumes composition_future: "composition_fri_future_fresh s"
    and query_future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and challenge_subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and challenge_bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C_challenge"
    and query_bound:
      "\<And>dg challenges.
        nnreal
          (card
            (generic_fri_sampled_query_query_fiber
              (composition_table_low_degree (to_nat dg))
              (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg)
              challenges)) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds \<le> C_query"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_query_bad_candidate s) s \<le>
      C_challenge + C_query"
proof (rule
    wp_composition_fri_sampled_query_bad_candidate_bound_from_challenge_cover_and_query_fibers
    [OF composition_future query_future raw_bound challenge_subset
      challenge_bound])
  fix dg challenges
  show
    "fst `
      (((composition_fri_sampled_query_bad_pair_union dg \<inter>
          (fri_query_index_list_space \<times> UNIV)) \<inter>
        (UNIV \<times> (- B dg))) \<inter>
        (UNIV \<times> {challenges}))
      \<subseteq>
      generic_fri_sampled_query_query_fiber
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg)
        challenges"
    unfolding composition_fri_sampled_query_bad_pair_union_def
      generic_fri_sampled_query_query_fiber_def
      generic_fri_sampled_query_restricted_bad_pairs_def
      fri_query_challenge_pair_query_fiber_def
    by auto
next
  fix dg challenges
  show
    "generic_fri_sampled_query_query_fiber
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg)
      challenges
    \<subseteq> fri_query_index_list_space"
    by (rule generic_fri_sampled_query_query_fiber_subset)
next
  fix dg challenges
  show
    "nnreal
      (card
        (generic_fri_sampled_query_query_fiber
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg)
          challenges)) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds \<le> C_query"
    by (rule query_bound)
qed

end

end
