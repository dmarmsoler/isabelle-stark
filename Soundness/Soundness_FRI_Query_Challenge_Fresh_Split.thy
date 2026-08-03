(*  Title:      Stark/Soundness_FRI_Query_Challenge_Fresh_Split.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_Challenge_Fresh_Split
  imports Soundness_FRI_Query_Fiber_Exact_Staged_Bounds
begin

text \<open>
  Staged split for FRI query/challenge pair events.

  The exact pair-fraction route must keep the query/challenge pair event until
  the challenge-list probability has been accounted for.  This layer separates
  only the challenge prequery side event, leaving the fresh branch as the
  original pair hit conjoined with path freshness of the relevant FRI
  challenge keys.
\<close>

context soundness
begin

lemma verifier_after_trace_fri_concrete_header_transcript:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((fr, f_fl), prefix_state) \<in>
      set_dist (execute verifier_trace_fri_prefix s)"
    and suffix:
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_trace_fri (fr, f_fl)) prefix_state)"
  obtains f_final as dg fl final query_state where
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
proof -
  have prefix_res:
    "PTranscript s = [fr] @ map snd f_fl @ PTranscript prefix_state \<and>
     PState prefix_state =
        foldl concat (concat (PState s) fr) (map snd f_fl)"
    using verifier_trace_fri_prefix_outcome[OF prefix] by simp
  have len_f_fl: "length f_fl = ceil_log clength"
    using verifier_trace_fri_prefix_outcome[OF prefix] by simp
  from suffix obtain f_final s3 as s4 dg s5 s6 fl s7 final query_state where
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
        set_dist (execute
          (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
    unfolding verifier_after_trace_fri_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_trace_final] obtain rest3 where
    tr_prefix: "PTranscript prefix_state = f_final # rest3"
    and tr_s3: "PTranscript s3 = rest3"
    by blast
  have alpha_res:
    "length as = length spec \<and>
     PTranscript s3 = as @ PTranscript s4"
    using mmap_alpha_round_outcome[OF alpha_out] by simp
  from read_outcome[OF read_dg] obtain rest5 where
    tr_s4: "PTranscript s4 = dg # rest5"
    and tr_s5: "PTranscript s5 = rest5"
    by blast
  have s6_eq: "s6 = s5"
    using degree_assert unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
  have comp_res:
    "length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s6 = map snd fl @ PTranscript s7"
    using ntimes_receive_composition_fri_commits_outcome[OF comp_fri]
    by simp
  from read_outcome[OF read_final] obtain rest_query where
    tr_s7: "PTranscript s7 = final # rest_query"
    and tr_query: "PTranscript query_state = rest_query"
    by blast
  have header:
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    using prefix_res len_f_fl tr_prefix tr_s3 alpha_res tr_s4 tr_s5 s6_eq comp_res
      tr_s7 tr_query
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
  show thesis
    by (rule that[OF header query_out])
qed

lemma verifier_after_trace_fri_header_agrees_with_accepted_challenges:
  assumes prefix:
    "Some ((fr, f_fl), prefix_state) \<in>
      set_dist (execute verifier_trace_fri_prefix s)"
    and suffix:
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_trace_fri (fr, f_fl)) prefix_state)"
    and accepted:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
  shows "trace_bs = map fst f_fl"
proof -
  from verifier_after_trace_fri_accepted_fri_challenges[OF prefix suffix]
  obtain dg' comp_bs' where replay:
    "accepted_fri_challenges s (Some (result, final_state))
      (map fst f_fl) dg' comp_bs'"
    by blast
  show ?thesis
    using accepted_fri_challenges_unique[OF replay accepted] by simp
qed

lemma verifier_after_trace_fri_header_roots_agree_with_fresh_hit:
  assumes prefix:
    "Some ((fr, f_fl), prefix_state) \<in>
      set_dist (execute verifier_trace_fri_prefix s)"
    and suffix:
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_trace_fri (fr, f_fl)) prefix_state)"
    and fresh:
      "trace_fri_challenge_list_fresh_hit s B
        (Some (result, final_state))"
  shows "trace_fri_challenge_path_fresh s fr (map snd f_fl)
    (length (map snd f_fl))"
proof -
  from fresh obtain trace_bs dg comp_bs fr' trace_roots' trace_final' as'
      composition_roots' final' rest' where
    accepted:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
    and header_hit:
      "verifier_header_transcript s fr' trace_roots' trace_final' as' dg
        composition_roots' final' rest'"
    and fresh_path:
      "trace_fri_challenge_path_fresh s fr' trace_roots'
        (length trace_roots')"
    unfolding trace_fri_challenge_list_fresh_hit_def by blast
  from verifier_after_trace_fri_accepted_fri_challenges[OF prefix suffix]
  obtain dg0 comp_bs0 where replay:
    "accepted_fri_challenges s (Some (result, final_state))
      (map fst f_fl) dg0 comp_bs0"
    by blast
  have dg_eq: "dg = dg0"
    using accepted_fri_challenges_unique[OF accepted replay] by simp
  from verifier_after_trace_fri_concrete_header_transcript[OF prefix suffix]
  obtain f_final0::'f and as0:: "'f list" and dg1::'f and fl0:: "('f \<times> 'f) list" and final0:: 'f and query_state0:: "('f, 'a) protocol_channel_scheme" where
    header_concrete:
      "verifier_header_transcript s fr (map snd f_fl) f_final0 as0 dg1
        (map snd fl0) final0 (PTranscript query_state0)"
    by metis
  from accepted_fri_challenges_headerE[OF replay]
  obtain fr0::'f and f_fl0:: "('f \<times> 'f) list" and f_final0'::'f and as0':: "'f list" and fl0':: "('f \<times> 'f) list" and final0'::'f and rest0':: "'f list" where
    header_replay:
      "verifier_header_transcript s fr0 (map snd f_fl0) f_final0' as0'
        dg0 (map snd fl0') final0' rest0'"
    by metis
  have replay_unique:
    "fr0 = fr \<and> map snd f_fl0 = map snd f_fl \<and> dg0 = dg1"
    using verifier_header_transcript_unique[OF header_replay header_concrete]
    by simp
  from accepted_fri_challenges_headerE[OF accepted]
  obtain fr1::'f and f_fl1:: "('f \<times> 'f) list" and f_final1::'f and as1:: "'f list" and fl1:: "('f \<times> 'f) list" and final1::'f and rest1 where
    header_accepted:
      "verifier_header_transcript s fr1 (map snd f_fl1) f_final1 as1 dg
        (map snd fl1) final1 rest1"
    by metis
  have accepted_unique_header:
    "fr1 = fr0 \<and> map snd f_fl1 = map snd f_fl0"
    using verifier_header_transcript_unique[OF header_accepted header_replay]
      dg_eq
    by simp
  have hit_unique:
    "fr' = fr1 \<and> trace_roots' = map snd f_fl1"
    using verifier_header_transcript_unique[OF header_hit header_accepted]
    by simp
  show ?thesis
    using fresh_path hit_unique accepted_unique_header replay_unique by simp
qed

lemma verifier_after_composition_fri_concrete_header_transcript:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((fr, f_fl, f_final, as, dg, fl), prefix_state) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
    and suffix:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (verifier_after_composition_fri
              (fr, f_fl, f_final, as, dg, fl))
            prefix_state)"
  obtains final query_state where
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
proof -
  have prefix_res:
    "PTranscript s =
       [fr] @ map snd f_fl @ [f_final] @ as @ [dg] @
       map snd fl @ PTranscript prefix_state"
    using verifier_composition_fri_prefix_outcome[OF prefix] by simp
  from suffix obtain final query_state where
    read_final:
      "Some (final, query_state) \<in>
        set_dist (execute read prefix_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    unfolding verifier_after_composition_fri_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_final] obtain rest_query where
    tr_prefix: "PTranscript prefix_state = final # rest_query"
    and tr_query: "PTranscript query_state = rest_query"
    by blast
  have len_f_fl: "length f_fl = ceil_log clength"
    using verifier_composition_fri_prefix_outcome[OF prefix] by simp
  have len_as: "length as = length spec"
    using verifier_composition_fri_prefix_outcome[OF prefix] by simp
  have len_fl: "length fl = ceil_log (to_nat dg + 1)"
    using verifier_composition_fri_prefix_outcome[OF prefix] by simp
  have header:
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    using prefix_res len_f_fl len_as len_fl tr_prefix tr_query
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
  show thesis
    by (rule that[OF header query_out])
qed

lemma verifier_after_composition_fri_header_agrees_with_accepted_challenges:
  assumes prefix:
    "Some ((fr, f_fl, f_final, as, dg, fl), prefix_state) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
    and suffix:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (verifier_after_composition_fri
              (fr, f_fl, f_final, as, dg, fl))
            prefix_state)"
    and accepted:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg'
        comp_bs"
  shows "dg' = dg \<and> comp_bs = map fst fl"
proof -
  have replay:
    "accepted_fri_challenges s (Some (result, final_state))
      (map fst f_fl) dg (map fst fl)"
    by (rule verifier_after_composition_fri_accepted_fri_challenges
        [OF prefix suffix])
  show ?thesis
    using accepted_fri_challenges_unique[OF replay accepted] by simp
qed

lemma verifier_after_composition_fri_header_roots_agree_with_fresh_hit:
  assumes prefix:
    "Some ((fr, f_fl, f_final, as, dg, fl), prefix_state) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
    and suffix:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (verifier_after_composition_fri
              (fr, f_fl, f_final, as, dg, fl))
            prefix_state)"
    and fresh:
      "composition_fri_challenge_list_fresh_hit s B
        (Some (result, final_state))"
  shows "composition_fri_challenge_path_fresh s fr (map snd f_fl) f_final
    as dg (map snd fl) (length (map snd fl))"
proof -
  from fresh obtain trace_bs dg' comp_bs fr' trace_roots' trace_final' as'
      composition_roots' final' rest' where
    accepted:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg'
        comp_bs"
    and header_hit:
      "verifier_header_transcript s fr' trace_roots' trace_final' as' dg'
        composition_roots' final' rest'"
    and fresh_path:
      "composition_fri_challenge_path_fresh s fr' trace_roots' trace_final'
        as' dg' composition_roots' (length composition_roots')"
    unfolding composition_fri_challenge_list_fresh_hit_def by blast
  from verifier_after_composition_fri_concrete_header_transcript[OF prefix suffix]
  obtain final0:: 'f and query_state0:: "('f, 'a) protocol_channel_scheme" where
    header_concrete:
      "verifier_header_transcript s fr (map snd f_fl) f_final as dg
        (map snd fl) final0 (PTranscript query_state0)"
    by blast
  have "fr' = fr \<and>
      trace_roots' = map snd f_fl \<and>
      trace_final' = f_final \<and>
      as' = as \<and>
      dg' = dg \<and>
      composition_roots' = map snd fl"
    using verifier_header_transcript_unique[OF header_hit header_concrete]
    by simp
  then show ?thesis
    using fresh_path by simp
qed

definition staged_security_trace_fri_pair_challenge_fresh
  :: "(nat list \<times> 'f list) set \<Rightarrow> 'f list set \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times>
          unit list) \<times> 'f protocol_channel) option \<Rightarrow> bool"
where
  "staged_security_trace_fri_pair_challenge_fresh P B out \<longleftrightarrow>
    staged_security_with_data_state_verifier_event
      (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P) out \<and>
    staged_security_with_data_state_verifier_event
      (\<lambda>s. trace_fri_challenge_list_fresh_hit s B) out"

definition staged_security_composition_fri_pair_challenge_fresh
  :: "('f \<Rightarrow> (nat list \<times> 'f list) set) \<Rightarrow>
      ('f \<Rightarrow> 'f list set) \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times>
          unit list) \<times> 'f protocol_channel) option \<Rightarrow> bool"
where
  "staged_security_composition_fri_pair_challenge_fresh P B out \<longleftrightarrow>
    staged_security_with_data_state_verifier_event
      (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P) out \<and>
    staged_security_with_data_state_verifier_event
      (\<lambda>s. composition_fri_challenge_list_fresh_hit s B) out"

lemma checked_staged_security_trace_fri_query_challenge_pair_set_hit_split_challenge_fresh:
  assumes projection: "snd ` P \<subseteq> B"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_trace_fri_pair_challenge_fresh P B)
      adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_prequery_hit s B))
      adversary_initial_state"
proof -
  have event_mono:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_trace_fri_pair_challenge_fresh P B out \<or>
        staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_prequery_hit s B) out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P) out"
    show
      "staged_security_trace_fri_pair_challenge_fresh P B out \<or>
       staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_prequery_hit s B) out"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding staged_security_with_data_state_verifier_event_def
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
        unfolding staged_security_with_data_state_verifier_event_def by simp
      have challenge_hit:
        "trace_fri_challenge_list_set_hit ?s B
          (Some (result, final_state))"
        by (rule trace_fri_query_challenge_pair_set_hit_imp_challenge_list_set_hit
            [OF pair_hit projection])
      from trace_fri_challenge_list_set_hit_imp_fresh_or_prequery
          [OF challenge_hit]
      show ?thesis
      proof
        assume fresh:
          "trace_fri_challenge_list_fresh_hit ?s B
            (Some (result, final_state))"
        then have "staged_security_trace_fri_pair_challenge_fresh P B out"
          using hit out_eq unfolding
            staged_security_trace_fri_pair_challenge_fresh_def
            staged_security_with_data_state_verifier_event_def
          by simp
        then show ?thesis by simp
      next
        assume prequery:
          "trace_fri_challenge_list_prequery_hit ?s B
            (Some (result, final_state))"
        then have
          "staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_challenge_list_prequery_hit s B) out"
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          by simp
        then show ?thesis by simp
      qed
    qed
  qed
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_trace_fri_pair_challenge_fresh P B)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_prequery_hit s B))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_query_challenge_pair_set_hit_bound_from_challenge_fresh:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and projection: "snd ` P \<subseteq> B"
    and fresh_branch_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_trace_fri_pair_challenge_fresh P B)
        adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have split:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_trace_fri_pair_challenge_fresh P B)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_prequery_hit s B))
        adversary_initial_state"
    by (rule
        checked_staged_security_trace_fri_query_challenge_pair_set_hit_split_challenge_fresh
        [OF projection])
  have prequery_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_prequery_hit s B))
      adversary_initial_state \<le>
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule checked_staged_security_trace_fri_verifier_prequery_hit_bound
        [OF wf controlled finite_B])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule order_trans[OF split])
      (rule add_mono[OF fresh_branch_bound prequery_bound])
  then show ?thesis .
qed

lemma checked_staged_security_composition_fri_query_challenge_pair_set_hit_split_challenge_fresh:
  assumes projection: "\<And>dg. snd ` P dg \<subseteq> B dg"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_composition_fri_pair_challenge_fresh P B)
      adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_prequery_hit s B))
      adversary_initial_state"
proof -
  have event_mono:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_composition_fri_pair_challenge_fresh P B out \<or>
        staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_challenge_list_prequery_hit s B) out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P) out"
    show
      "staged_security_composition_fri_pair_challenge_fresh P B out \<or>
       staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_prequery_hit s B) out"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding staged_security_with_data_state_verifier_event_def
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
        unfolding staged_security_with_data_state_verifier_event_def by simp
      have challenge_hit:
        "composition_fri_challenge_list_set_hit ?s B
          (Some (result, final_state))"
        by (rule
            composition_fri_query_challenge_pair_set_hit_imp_challenge_list_set_hit
            [OF pair_hit projection])
      from composition_fri_challenge_list_set_hit_imp_fresh_or_prequery
          [OF challenge_hit]
      show ?thesis
      proof
        assume fresh:
          "composition_fri_challenge_list_fresh_hit ?s B
            (Some (result, final_state))"
        then have
          "staged_security_composition_fri_pair_challenge_fresh P B out"
          using hit out_eq unfolding
            staged_security_composition_fri_pair_challenge_fresh_def
            staged_security_with_data_state_verifier_event_def
          by simp
        then show ?thesis by simp
      next
        assume prequery:
          "composition_fri_challenge_list_prequery_hit ?s B
            (Some (result, final_state))"
        then have
          "staged_security_with_data_state_verifier_event
            (\<lambda>s. composition_fri_challenge_list_prequery_hit s B) out"
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          by simp
        then show ?thesis by simp
      qed
    qed
  qed
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_composition_fri_pair_challenge_fresh P B)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_challenge_list_prequery_hit s B))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_query_challenge_pair_set_hit_bound_from_challenge_fresh:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and projection: "\<And>dg. snd ` P dg \<subseteq> B dg"
    and fresh_branch_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_composition_fri_pair_challenge_fresh P B)
        adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have split:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_composition_fri_pair_challenge_fresh P B)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_challenge_list_prequery_hit s B))
        adversary_initial_state"
    by (rule
        checked_staged_security_composition_fri_query_challenge_pair_set_hit_split_challenge_fresh
        [OF projection])
  have prequery_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_prequery_hit s B))
      adversary_initial_state \<le>
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule checked_staged_security_composition_fri_verifier_prequery_hit_bound
        [OF wf controlled finite_B])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule order_trans[OF split])
      (rule add_mono[OF fresh_branch_bound prequery_bound])
  then show ?thesis .
qed

end

end
