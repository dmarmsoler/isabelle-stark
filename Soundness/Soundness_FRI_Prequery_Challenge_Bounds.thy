(*  Title:      Stark/Soundness_FRI_Prequery_Challenge_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Prequery_Challenge_Bounds
  imports Soundness_FRI_Prequery_Core
begin

text \<open>
  Staged and verifier-local FRI challenge-list accounting built on the
  prequery core definitions and relation bounds.
\<close>

context soundness
begin

definition trace_fri_root_path_fresh_from
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> bool"
where
  "trace_fri_root_path_fresh_from s roots n \<longleftrightarrow>
    (\<forall>i < n.
      i < length roots \<longrightarrow>
      fmlookup (HashMap s)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (PState s) (take (Suc i) roots))) = None)"

definition composition_fri_root_path_fresh_from
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> bool"
where
  "composition_fri_root_path_fresh_from s roots n \<longleftrightarrow>
    (\<forall>i < n.
      i < length roots \<longrightarrow>
      fmlookup (HashMap s)
        (CompositionFriChallenge (PCompositionFriCounter s + i)
          (foldl concat (PState s) (take (Suc i) roots))) = None)"

lemma trace_fri_challenge_path_fresh_after_read_iff:
  assumes read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
  shows
    "trace_fri_challenge_path_fresh s fr roots n \<longleftrightarrow>
      trace_fri_root_path_fresh_from s1 roots n"
proof -
  have state: "PState s1 = concat (PState s) fr"
    using read_outcome[OF read_fr] by blast
  have counter: "PTraceFriCounter s1 = PTraceFriCounter s"
    using read_outcome[OF read_fr] by blast
  have hash: "HashMap s1 = HashMap s"
    by (rule read_preserves_hash_map[OF read_fr])
  show ?thesis
    unfolding trace_fri_challenge_path_fresh_def
      trace_fri_root_path_fresh_from_def
    by (simp add: trace_fri_challenge_key_at_def state counter hash)
qed

lemma receive_trace_fri_commits_preserves_trace_root_path_fresh_tail:
  assumes path:
    "trace_fri_root_path_fresh_from s (r # roots) (Suc n)"
    and outcome:
      "Some ((b, r), t) \<in> set_dist (execute receive_trace_fri_commits s)"
  shows "trace_fri_root_path_fresh_from t roots n"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s_read)"
    unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_r] have read_state:
    "PState s_read = concat (PState s) r"
    by blast
  from read_outcome[OF read_r] have read_counter:
    "PTraceFriCounter s_read = PTraceFriCounter s"
    by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have counter_t:
    "PTraceFriCounter t = Suc (PTraceFriCounter s)"
    using receive_trace_fri_challenge_counter_outcome[OF rand_b]
      read_counter by simp
  have state_t: "PState t = concat (PState s) r"
    using receive_trace_fri_challenge_outcome[OF rand_b] read_state by simp
  show ?thesis
    unfolding trace_fri_root_path_fresh_from_def
  proof (intro allI impI)
    fix i
    assume i_lt: "i < n"
      and i_len: "i < length roots"
    let ?key =
      "TraceFriChallenge (PTraceFriCounter t + i)
        (foldl concat (PState t) (take (Suc i) roots))"
    have key_eq:
      "?key =
        TraceFriChallenge (PTraceFriCounter s + Suc i)
          (foldl concat (PState s) (take (Suc (Suc i)) (r # roots)))"
      using counter_t state_t by simp
    have neq:
      "?key \<noteq> TraceFriChallenge (PTraceFriCounter s_read) (PState s_read)"
      using counter_t read_counter by simp
    have "fmlookup (HashMap t) ?key =
        fmlookup (HashMap s_read) ?key"
      by (rule receive_trace_fri_challenge_preserves_other_lookup
          [OF rand_b neq])
    also have "... = fmlookup (HashMap s) ?key"
      using read_hash by simp
    also have "... = None"
    proof -
      have "Suc i < Suc n"
        using i_lt by simp
      moreover have "Suc i < length (r # roots)"
        using i_len by simp
      ultimately show ?thesis
        using path unfolding trace_fri_root_path_fresh_from_def key_eq
        by blast
    qed
    finally show "fmlookup (HashMap t) ?key = None" .
  qed
qed

lemma wp_receive_trace_fri_commits_actual_fresh_set:
  shows
    "wp_event receive_trace_fri_commits
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((b, r), _) \<Rightarrow>
            b \<in> B \<and>
            fmlookup (HashMap s)
              (TraceFriChallenge (PTraceFriCounter s)
                (concat (PState s) r)) = None) s
      \<le> nnreal (card B) / nnreal size"
  unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> (case None of None \<Rightarrow> False
      | Some ((b, r), _) \<Rightarrow>
          b \<in> B \<and>
          fmlookup (HashMap s)
            (TraceFriChallenge (PTraceFriCounter s)
              (concat (PState s) r)) = None)"
    by simp
next
  fix r s_read
  assume read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
  have read_state: "PState s_read = concat (PState s) r"
    using read_outcome[OF read_r] by blast
  have read_counter: "PTraceFriCounter s_read = PTraceFriCounter s"
    using read_outcome[OF read_r] by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  let ?fresh =
    "fmlookup (HashMap s_read)
      (TraceFriChallenge (PTraceFriCounter s_read) (PState s_read)) = None"
  let ?Q =
    "\<lambda>out :: (('f \<times> 'f) \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some ((b, r'), _) \<Rightarrow>
          b \<in> B \<and>
          fmlookup (HashMap s)
            (TraceFriChallenge (PTraceFriCounter s)
              (concat (PState s) r')) = None"
  show "wp_event
      (receive_trace_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q
      s_read
      \<le> nnreal (card B) / nnreal size"
  proof (cases ?fresh)
    case True
    have fresh_key:
      "fmlookup (HashMap s)
        (TraceFriChallenge (PTraceFriCounter s) (concat (PState s) r)) =
        None"
      using True by (simp add: read_state read_counter read_hash)
    have cont_eq:
      "(\<lambda>out. case out of
          None \<Rightarrow> (0 :: prob)
        | Some (b, u) \<Rightarrow>
            wp (return (b, r)) (\<lambda>out. if ?Q out then 1 else 0) u) =
       (\<lambda>out :: ('f \<times> ('f, 'a) protocol_channel_scheme) option.
          if (case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B)
          then 1 else 0)"
      by (rule ext)
        (auto simp: wpsimps fresh_key split: option.splits prod.splits)
    have "wp_event
        (receive_trace_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q
        s_read =
        wp_event receive_trace_fri_challenge
          (\<lambda>out. case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B)
          s_read"
      unfolding wp_event_def by (simp add: wpsimps cont_eq)
    also have "... = nnreal (card B) / nnreal size"
      by (rule wp_receive_trace_fri_challenge_fresh_set[OF True])
    finally show ?thesis by simp
  next
    case False
    have not_fresh_s:
      "fmlookup (HashMap s)
        (TraceFriChallenge (PTraceFriCounter s) (concat (PState s) r))
        \<noteq> None"
      using False by (simp add: read_state read_counter read_hash)
    have "wp_event
        (receive_trace_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q
        s_read
        \<le> wp_event
          (receive_trace_fri_challenge \<bind> (\<lambda>b. return (b, r)))
          (\<lambda>_ :: (('f \<times> 'f) \<times>
            ('f, 'a) protocol_channel_scheme) option. False) s_read"
      by (rule wp_event_mono_on_support)
        (use not_fresh_s in
          \<open>auto simp: wpsimps elim!: set_dist_bindE
            split: option.splits prod.splits\<close>)
    also have "... = 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
    finally have zero_bound:
      "wp_event
        (receive_trace_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q
        s_read \<le> 0" .
    also have "... \<le> nnreal (card B) / nnreal size"
      by simp
    finally show ?thesis .
  qed
qed

lemma wp_ntimes_receive_trace_fri_commits_exact_challenges_actual_fresh_bound:
  assumes len: "length bs = n"
  shows
    "wp_event (ntimes receive_trace_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs = bs \<and>
            trace_fri_root_path_fresh_from s (map snd brs) n) s
      \<le> (1 / nnreal size) ^ n"
  using len
proof (induction n arbitrary: s bs)
  case 0
  then have bs_empty: "bs = []"
    by simp
  show ?case
    unfolding bs_empty by (simp add: wp_event_def wpsimps
      trace_fri_root_path_fresh_from_def)
next
  case (Suc n)
  obtain b bs' where bs_eq: "bs = b # bs'"
    using Suc.prems by (cases bs) auto
  have len_bs': "length bs' = n"
    using Suc.prems bs_eq by simp
  let ?tail =
    "(ntimes receive_trace_fri_commits n ::
      (('f \<times> 'f) list, ('f, 'a) protocol_channel_scheme) state_monad)"
  let ?Q =
    "\<lambda>out :: ((('f \<times> 'f) list) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow>
          map fst brs = bs \<and>
          trace_fri_root_path_fresh_from s (map snd brs) (Suc n)"
  let ?Head =
    "\<lambda>out :: (('f \<times> 'f) \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some ((b0, r0), _) \<Rightarrow>
          b0 \<in> {b} \<and>
          fmlookup (HashMap s)
            (TraceFriChallenge (PTraceFriCounter s)
              (concat (PState s) r0)) = None"
  have head_bound:
    "wp_event receive_trace_fri_commits ?Head s \<le> 1 / nnreal size"
  proof -
    have "wp_event receive_trace_fri_commits ?Head s
        \<le> nnreal (card ({b} :: 'f set)) / nnreal size"
      by (rule wp_receive_trace_fri_commits_actual_fresh_set)
    then show ?thesis by simp
  qed
  have bind_bound:
    "wp_event
      (receive_trace_fri_commits \<bind>
        (\<lambda>br :: 'f \<times> 'f.
          ?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs))))
      ?Q s
      \<le> wp_event receive_trace_fri_commits ?Head s *
        (1 / nnreal size) ^ n"
  proof (rule wp_event_bind_bound_by_head_and_cont[where P = ?Head])
    show "\<not> ?Q None"
      by simp
  next
    fix br t
    assume not_head: "\<not> ?Head (Some (br, t))"
    obtain b0 r0 where br_eq: "br = (b0, r0)"
      by (cases br)
    have cont_false:
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t
       \<le> wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        (\<lambda>_ :: ((('f \<times> 'f) list) \<times>
          ('f, 'a) protocol_channel_scheme) option. False) t"
      by (rule wp_event_mono_on_support)
        (use not_head bs_eq br_eq in
          \<open>auto simp: wpsimps trace_fri_root_path_fresh_from_def
            elim!: set_dist_bindE split: option.splits prod.splits\<close>)
    also have "... = 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
    finally have le_zero:
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t \<le> 0" .
    show
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t = 0"
      by (rule antisym[OF le_zero]) simp
  next
    fix br t
    assume head:
      "Some (br, t) \<in> set_dist (execute receive_trace_fri_commits s)"
      and head_hit: "?Head (Some (br, t))"
    obtain b0 r0 where br_eq: "br = (b0, r0)"
      by (cases br)
    have b0_eq: "b0 = b"
      using head_hit unfolding br_eq by simp
    let ?TailQ =
      "\<lambda>out :: ((('f \<times> 'f) list) \<times>
          ('f, 'a) protocol_channel_scheme) option.
        case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs = bs' \<and>
            trace_fri_root_path_fresh_from t (map snd brs) n"
    have cont_le:
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t \<le> wp_event ?tail ?TailQ t"
	    proof (rule wp_event_bind_bound_by_head_event)
	      show "wp_event ?tail ?TailQ t \<le> wp_event ?tail ?TailQ t"
	        by simp
	    next
	      show "?Q None \<Longrightarrow> ?TailQ None"
	        by simp
    next
      fix brs u out
      assume tail_out:
          "Some (brs, u) \<in> set_dist (execute ?tail t)"
        and ret_out:
          "out \<in> set_dist (execute (return (br # brs)) u)"
        and hit: "?Q out"
      have out_eq: "out = Some (br # brs, u)"
        using ret_out
        unfolding set_dist_def return.rep_eq dist_return_def
          dist_delta_dist delta_map_def by simp
      have map_eq: "map fst brs = bs'"
        using hit out_eq b0_eq bs_eq br_eq by simp
      have path_full:
        "trace_fri_root_path_fresh_from s (map snd (br # brs)) (Suc n)"
        using hit out_eq by simp
      have path_full':
        "trace_fri_root_path_fresh_from s (r0 # map snd brs) (Suc n)"
        using path_full unfolding br_eq by simp
      have path_tail:
        "trace_fri_root_path_fresh_from t (map snd brs) n"
        by (rule receive_trace_fri_commits_preserves_trace_root_path_fresh_tail
            [OF path_full' head[unfolded br_eq]])
      show "?TailQ (Some (brs, u))"
        using map_eq path_tail by simp
    qed
    also have "... \<le> (1 / nnreal size) ^ n"
      by (rule Suc.IH[OF len_bs'])
    finally show
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t \<le> (1 / nnreal size) ^ n" .
  qed
  have "wp_event (ntimes receive_trace_fri_commits (Suc n)) ?Q s
      \<le> wp_event receive_trace_fri_commits ?Head s *
        (1 / nnreal size) ^ n"
    using bind_bound by simp
  also have "... \<le> (1 / nnreal size) * (1 / nnreal size) ^ n"
    by (rule mult_right_mono[OF head_bound]) simp
  also have "... = (1 / nnreal size) ^ Suc n"
    by simp
  finally show ?case .
qed

lemma wp_ntimes_receive_trace_fri_commits_finite_set_actual_fresh_bound:
  assumes finite_B: "finite B"
    and lengths: "\<And>bs. bs \<in> B \<Longrightarrow> length bs = n"
  shows
    "wp_event (ntimes receive_trace_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs \<in> B \<and>
            trace_fri_root_path_fresh_from s (map snd brs) n) s
      \<le> nnreal (card B) / (nnreal size) ^ n"
proof -
  let ?P =
    "\<lambda>bs out. case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow>
          map fst brs = bs \<and>
          trace_fri_root_path_fresh_from s (map snd brs) n"
  have event_mono:
    "wp_event (ntimes receive_trace_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs \<in> B \<and>
            trace_fri_root_path_fresh_from s (map snd brs) n) s
      \<le> wp_event (ntimes receive_trace_fri_commits n)
        (\<lambda>out. \<exists>bs \<in> B. ?P bs out) s"
    by (rule wp_event_mono) (auto split: option.splits prod.splits)
  also have "... \<le> (\<Sum>bs\<in>B. (1 / nnreal size) ^ n)"
    by (rule wp_event_finite_UN_bound[OF finite_B])
      (rule wp_ntimes_receive_trace_fri_commits_exact_challenges_actual_fresh_bound
        [OF lengths])
  also have "... = nnreal (card B) * ((1 / nnreal size) ^ n)"
    using finite_B by simp
  also have "... = nnreal (card B) / (nnreal size) ^ n"
    using size_card by transfer (simp add: power_divide)
  finally show ?thesis .
qed

lemma wp_ntimes_receive_trace_fri_commits_challenge_space_actual_fresh_bound:
  assumes subset: "B \<subseteq> fri_challenge_space n"
  shows
    "wp_event (ntimes receive_trace_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs \<in> B \<and>
            trace_fri_root_path_fresh_from s (map snd brs) n) s
      \<le> nnreal (card B) / nnreal (CARD('f) ^ n)"
proof -
  have finite_B: "finite B"
    by (rule finite_subset[OF subset finite_fri_challenge_space])
  have lengths: "\<And>bs. bs \<in> B \<Longrightarrow> length bs = n"
    using subset unfolding fri_challenge_space_def by auto
  have "wp_event (ntimes receive_trace_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs \<in> B \<and>
            trace_fri_root_path_fresh_from s (map snd brs) n) s
      \<le> nnreal (card B) / (nnreal size) ^ n"
    by (rule wp_ntimes_receive_trace_fri_commits_finite_set_actual_fresh_bound
        [OF finite_B lengths])
  also have "... = nnreal (card B) / nnreal (CARD('f) ^ n)"
    using size_card by simp
  finally show ?thesis .
qed

lemma wp_verifier_trace_fri_prefix_challenge_list_actual_fresh_bound:
  assumes subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
  shows
    "wp_event verifier_trace_fri_prefix
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((fr, f_fl), _) \<Rightarrow>
            map fst f_fl \<in> B \<and>
            trace_fri_challenge_path_fresh s fr (map snd f_fl)
              (length (map snd f_fl))) s
      \<le> nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
proof -
  let ?Q =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl), _) \<Rightarrow>
          map fst f_fl \<in> B \<and>
          trace_fri_challenge_path_fresh s fr (map snd f_fl)
            (length (map snd f_fl))"
  let ?C = "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
  show ?thesis
    unfolding verifier_trace_fri_prefix_def
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?Q None"
      by simp
  next
    fix fr s1
    assume read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    let ?Head =
      "\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (f_fl, _) \<Rightarrow>
            map fst f_fl \<in> B \<and>
            trace_fri_root_path_fresh_from s1 (map snd f_fl)
              (ceil_log clength)"
    have trace_bound:
      "wp_event (ntimes receive_trace_fri_commits (ceil_log clength))
        ?Head s1 \<le> ?C"
      by (rule wp_ntimes_receive_trace_fri_commits_challenge_space_actual_fresh_bound
          [OF subset])
    show "wp_event
        (ntimes receive_trace_fri_commits (ceil_log clength) \<bind>
          (\<lambda>f_fl. return (fr, f_fl)))
        ?Q s1 \<le> ?C"
    proof (rule wp_event_bind_bound_by_head_event[OF trace_bound])
      show "?Q None \<Longrightarrow> ?Head None"
        by simp
    next
      fix f_fl t out
      assume trace_out:
          "Some (f_fl, t) \<in>
            set_dist
              (execute (ntimes receive_trace_fri_commits (ceil_log clength))
                s1)"
        and cont:
          "out \<in> set_dist (execute (return (fr, f_fl)) t)"
        and hit: "?Q out"
      have out_eq: "out = Some ((fr, f_fl), t)"
        using cont
        unfolding set_dist_def return.rep_eq dist_return_def
          dist_delta_dist delta_map_def by simp
      have len: "length f_fl = ceil_log clength"
        using ntimes_receive_trace_fri_commits_outcome[OF trace_out] by simp
      have path:
        "trace_fri_root_path_fresh_from s1 (map snd f_fl)
          (ceil_log clength)"
        using hit out_eq len
          trace_fri_challenge_path_fresh_after_read_iff[OF read_fr]
        by simp
      show "?Head (Some (f_fl, t))"
        using hit out_eq path by simp
    qed
  qed
qed

lemma wp_verify_monad_trace_fri_challenge_list_fresh_hit_actual_bound:
  assumes subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
  shows
    "wp_event verify_monad (trace_fri_challenge_list_fresh_hit s B) s \<le>
      nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
proof -
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl), _) \<Rightarrow>
          map fst f_fl \<in> B \<and>
          trace_fri_challenge_path_fresh s fr (map snd f_fl)
            (length (map snd f_fl))"
  have prefix_bound:
    "wp_event verifier_trace_fri_prefix ?Head s \<le>
      nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verifier_trace_fri_prefix_challenge_list_actual_fresh_bound
        [OF subset])
  show ?thesis
    unfolding verify_monad_trace_fri_decomposition
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show "trace_fri_challenge_list_fresh_hit s B None \<Longrightarrow>
      ?Head None"
      unfolding trace_fri_challenge_list_fresh_hit_def
        accepted_fri_challenges_def by blast
  next
    fix header prefix_state out
    assume prefix:
      "Some (header, prefix_state) \<in>
        set_dist (execute verifier_trace_fri_prefix s)"
      and suffix:
        "out \<in>
          set_dist (execute (verifier_after_trace_fri header) prefix_state)"
      and hit: "trace_fri_challenge_list_fresh_hit s B out"
    obtain fr f_fl where header_eq: "header = (fr, f_fl)"
      by (cases header) auto
    from hit obtain trace_bs dg comp_bs fr' trace_roots' trace_final' as'
        composition_roots' final' rest' where
      challenges_hit: "accepted_fri_challenges s out trace_bs dg comp_bs"
      and header_hit:
        "verifier_header_transcript s fr' trace_roots' trace_final' as' dg
          composition_roots' final' rest'"
      and trace_bs_B: "trace_bs \<in> B"
      and fresh_hit:
        "trace_fri_challenge_path_fresh s fr' trace_roots'
          (length trace_roots')"
      unfolding trace_fri_challenge_list_fresh_hit_def by blast
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
    obtain dg' comp_bs' where
      challenges_prefix:
        "accepted_fri_challenges s (Some (result, final_state))
          (map fst f_fl) dg' comp_bs'"
      by blast
    have trace_bs_eq: "trace_bs = map fst f_fl"
      using accepted_fri_challenges_unique
        [OF challenges_prefix challenges_hit[unfolded out_eq]]
      by simp
	    from challenges_prefix obtain result0 final_state0 fr0 f_fl0
	        trace_final0 as0 fl0 final0 query_state0 where body0:
	      "Some (result, final_state) = Some (result0, final_state0) \<and>
	        verifier_header_transcript s fr0 (map snd f_fl0) trace_final0 as0
	          dg' (map snd fl0) final0 (PTranscript query_state0) \<and>
	        PState query_state0 =
	          verifier_header_state s fr0 (map snd f_fl0) trace_final0 as0
	            dg' (map snd fl0) final0 \<and>
	        Some (result0, final_state0) \<in>
	          set_dist (execute
	            (ntimes
	              (verifier_query_round_program fr0 f_fl0 trace_final0 as0
	                fl0 final0)
	              rounds)
	            query_state0) \<and>
	        PQueryCounter query_state0 = PQueryCounter s \<and>
	        map fst f_fl = map fst f_fl0 \<and>
	        comp_bs' = map fst fl0 \<and>
	        (\<forall>i < length f_fl0.
	          fmlookup (HashMap query_state0)
	            (TraceFriChallenge (PTraceFriCounter s + i)
	              (foldl concat (concat (PState s) fr0)
	                (take (Suc i) (map snd f_fl0)))) =
	          Some (fst (f_fl0 ! i))) \<and>
	        (\<forall>i < length fl0.
	          fmlookup (HashMap query_state0)
	            (CompositionFriChallenge (PCompositionFriCounter s + i)
	              (foldl concat
	                (concat
	                  (foldl concat
	                    (concat
	                      (foldl concat (concat (PState s) fr0)
	                        (map snd f_fl0))
	                      trace_final0)
	                    as0)
	                  dg')
	                (take (Suc i) (map snd fl0)))) =
	          Some (fst (fl0 ! i)))"
	      unfolding accepted_fri_challenges_def by blast
	    have header_prefix0:
	      "verifier_header_transcript s fr0 (map snd f_fl0) trace_final0 as0
	        dg' (map snd fl0) final0 (PTranscript query_state0)"
	      using body0 by simp
	    have trace_bs0: "map fst f_fl = map fst f_fl0"
	      using body0 by simp
	    have prefix_res:
	      "PTranscript s = [fr] @ map snd f_fl @ PTranscript prefix_state"
	      using verifier_trace_fri_prefix_outcome[OF prefix'] by simp
	    have len_f_fl: "length f_fl = ceil_log clength"
	      using verifier_trace_fri_prefix_outcome[OF prefix'] by simp
	    have fr0_eq: "fr0 = fr"
	      using prefix_res header_prefix0
	      unfolding verifier_header_transcript_def verifier_header_messages_def
	      by simp
	    have len_f_fl0: "length f_fl0 = ceil_log clength"
	      using header_prefix0
	      unfolding verifier_header_transcript_def by simp
	    have roots0_eq: "map snd f_fl0 = map snd f_fl"
	    proof -
	      let ?rest0 =
	        "trace_final0 # as0 @ dg' # map snd fl0 @ final0 #
	          PTranscript query_state0"
	      have prefix0:
	        "PTranscript s = [fr] @ map snd f_fl0 @ ?rest0"
	        using header_prefix0 fr0_eq
	        unfolding verifier_header_transcript_def verifier_header_messages_def
	        by simp
	      have eq:
	        "[fr] @ map snd f_fl @ PTranscript prefix_state =
	          [fr] @ map snd f_fl0 @ ?rest0"
	        using prefix_res prefix0 by simp
	      have take_eq:
	        "take (Suc (length (map snd f_fl)))
	            ([fr] @ map snd f_fl @ PTranscript prefix_state) =
	          take (Suc (length (map snd f_fl)))
	            ([fr] @ map snd f_fl0 @ ?rest0)"
	        using eq by simp
	      then show ?thesis
	        using len_f_fl len_f_fl0 by simp
	    qed
    have header_prefix:
      "verifier_header_transcript s fr (map snd f_fl) trace_final0 as0
        dg' (map snd fl0) final0 (PTranscript query_state0)"
      using header_prefix0 fr0_eq roots0_eq by simp
    have roots_eq:
      "fr' = fr \<and> trace_roots' = map snd f_fl"
      using verifier_header_transcript_unique[OF header_prefix header_hit]
      by simp
    then have fresh_prefix:
      "trace_fri_challenge_path_fresh s fr (map snd f_fl)
        (length (map snd f_fl))"
      using fresh_hit by simp
    show "?Head (Some (header, prefix_state))"
      using trace_bs_B trace_bs_eq fresh_prefix header_eq by simp
  qed
qed

lemma receive_composition_fri_commits_preserves_composition_root_path_fresh_tail:
  assumes path:
    "composition_fri_root_path_fresh_from s (r # roots) (Suc n)"
    and outcome:
      "Some ((b, r), t) \<in> set_dist (execute receive_composition_fri_commits s)"
  shows "composition_fri_root_path_fresh_from t roots n"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in>
        set_dist (execute receive_composition_fri_challenge s_read)"
    unfolding receive_composition_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_r] have read_state:
    "PState s_read = concat (PState s) r"
    by blast
  from read_outcome[OF read_r] have read_counter:
    "PCompositionFriCounter s_read = PCompositionFriCounter s"
    by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have counter_t:
    "PCompositionFriCounter t = Suc (PCompositionFriCounter s)"
    using receive_composition_fri_challenge_counter_outcome[OF rand_b]
      read_counter by simp
  have state_t: "PState t = concat (PState s) r"
    using receive_composition_fri_challenge_outcome[OF rand_b] read_state
    by simp
  show ?thesis
    unfolding composition_fri_root_path_fresh_from_def
  proof (intro allI impI)
    fix i
    assume i_lt: "i < n"
      and i_len: "i < length roots"
    let ?key =
      "CompositionFriChallenge (PCompositionFriCounter t + i)
        (foldl concat (PState t) (take (Suc i) roots))"
    have key_eq:
      "?key =
        CompositionFriChallenge (PCompositionFriCounter s + Suc i)
          (foldl concat (PState s) (take (Suc (Suc i)) (r # roots)))"
      using counter_t state_t by simp
    have neq:
      "?key \<noteq>
        CompositionFriChallenge (PCompositionFriCounter s_read)
          (PState s_read)"
      using counter_t read_counter by simp
    have "fmlookup (HashMap t) ?key =
        fmlookup (HashMap s_read) ?key"
      by (rule receive_composition_fri_challenge_preserves_other_lookup
          [OF rand_b neq])
    also have "... = fmlookup (HashMap s) ?key"
      using read_hash by simp
    also have "... = None"
    proof -
      have "Suc i < Suc n"
        using i_lt by simp
      moreover have "Suc i < length (r # roots)"
        using i_len by simp
      ultimately show ?thesis
        using path unfolding composition_fri_root_path_fresh_from_def key_eq
        by blast
    qed
    finally show "fmlookup (HashMap t) ?key = None" .
  qed
qed

lemma wp_receive_composition_fri_commits_actual_fresh_set:
  shows
    "wp_event receive_composition_fri_commits
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((b, r), _) \<Rightarrow>
            b \<in> B \<and>
            fmlookup (HashMap s)
              (CompositionFriChallenge (PCompositionFriCounter s)
                (concat (PState s) r)) = None) s
      \<le> nnreal (card B) / nnreal size"
  unfolding receive_composition_fri_commits_def receive_fri_commits_with_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> (case None of None \<Rightarrow> False
      | Some ((b, r), _) \<Rightarrow>
          b \<in> B \<and>
          fmlookup (HashMap s)
            (CompositionFriChallenge (PCompositionFriCounter s)
              (concat (PState s) r)) = None)"
    by simp
next
  fix r s_read
  assume read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
  have read_state: "PState s_read = concat (PState s) r"
    using read_outcome[OF read_r] by blast
  have read_counter:
    "PCompositionFriCounter s_read = PCompositionFriCounter s"
    using read_outcome[OF read_r] by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  let ?fresh =
    "fmlookup (HashMap s_read)
      (CompositionFriChallenge (PCompositionFriCounter s_read)
        (PState s_read)) = None"
  let ?Q =
    "\<lambda>out :: (('f \<times> 'f) \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some ((b, r'), _) \<Rightarrow>
          b \<in> B \<and>
          fmlookup (HashMap s)
            (CompositionFriChallenge (PCompositionFriCounter s)
              (concat (PState s) r')) = None"
  show "wp_event
      (receive_composition_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q
      s_read
      \<le> nnreal (card B) / nnreal size"
  proof (cases ?fresh)
    case True
    have fresh_key:
      "fmlookup (HashMap s)
        (CompositionFriChallenge (PCompositionFriCounter s)
          (concat (PState s) r)) = None"
      using True by (simp add: read_state read_counter read_hash)
    have cont_eq:
      "(\<lambda>out. case out of
          None \<Rightarrow> (0 :: prob)
        | Some (b, u) \<Rightarrow>
            wp (return (b, r)) (\<lambda>out. if ?Q out then 1 else 0) u) =
       (\<lambda>out :: ('f \<times> ('f, 'a) protocol_channel_scheme) option.
          if (case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B)
          then 1 else 0)"
      by (rule ext)
        (auto simp: wpsimps fresh_key split: option.splits prod.splits)
    have "wp_event
        (receive_composition_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q
        s_read =
        wp_event receive_composition_fri_challenge
          (\<lambda>out. case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B)
          s_read"
      unfolding wp_event_def by (simp add: wpsimps cont_eq)
    also have "... = nnreal (card B) / nnreal size"
      by (rule wp_receive_composition_fri_challenge_fresh_set[OF True])
    finally show ?thesis by simp
  next
    case False
    have not_fresh_s:
      "fmlookup (HashMap s)
        (CompositionFriChallenge (PCompositionFriCounter s)
          (concat (PState s) r)) \<noteq> None"
      using False by (simp add: read_state read_counter read_hash)
    have "wp_event
        (receive_composition_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q
        s_read
        \<le> wp_event
          (receive_composition_fri_challenge \<bind> (\<lambda>b. return (b, r)))
          (\<lambda>_ :: (('f \<times> 'f) \<times>
            ('f, 'a) protocol_channel_scheme) option. False) s_read"
      by (rule wp_event_mono_on_support)
        (use not_fresh_s in
          \<open>auto simp: wpsimps elim!: set_dist_bindE
            split: option.splits prod.splits\<close>)
    also have "... = 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
    finally have zero_bound:
      "wp_event
        (receive_composition_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q
        s_read \<le> 0" .
    also have "... \<le> nnreal (card B) / nnreal size"
      by simp
    finally show ?thesis .
  qed
qed

lemma wp_ntimes_receive_composition_fri_commits_exact_challenges_actual_fresh_bound:
  assumes len: "length bs = n"
  shows
    "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs = bs \<and>
            composition_fri_root_path_fresh_from s (map snd brs) n) s
      \<le> (1 / nnreal size) ^ n"
  using len
proof (induction n arbitrary: s bs)
  case 0
  then have bs_empty: "bs = []"
    by simp
  show ?case
    unfolding bs_empty by (simp add: wp_event_def wpsimps
      composition_fri_root_path_fresh_from_def)
next
  case (Suc n)
  obtain b bs' where bs_eq: "bs = b # bs'"
    using Suc.prems by (cases bs) auto
  have len_bs': "length bs' = n"
    using Suc.prems bs_eq by simp
  let ?tail =
    "(ntimes receive_composition_fri_commits n ::
      (('f \<times> 'f) list, ('f, 'a) protocol_channel_scheme) state_monad)"
  let ?Q =
    "\<lambda>out :: ((('f \<times> 'f) list) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow>
          map fst brs = bs \<and>
          composition_fri_root_path_fresh_from s (map snd brs) (Suc n)"
  let ?Head =
    "\<lambda>out :: (('f \<times> 'f) \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some ((b0, r0), _) \<Rightarrow>
          b0 \<in> {b} \<and>
          fmlookup (HashMap s)
            (CompositionFriChallenge (PCompositionFriCounter s)
              (concat (PState s) r0)) = None"
  have head_bound:
    "wp_event receive_composition_fri_commits ?Head s \<le> 1 / nnreal size"
  proof -
    have "wp_event receive_composition_fri_commits ?Head s
        \<le> nnreal (card ({b} :: 'f set)) / nnreal size"
      by (rule wp_receive_composition_fri_commits_actual_fresh_set)
    then show ?thesis by simp
  qed
  have bind_bound:
    "wp_event
      (receive_composition_fri_commits \<bind>
        (\<lambda>br :: 'f \<times> 'f.
          ?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs))))
      ?Q s
      \<le> wp_event receive_composition_fri_commits ?Head s *
        (1 / nnreal size) ^ n"
  proof (rule wp_event_bind_bound_by_head_and_cont[where P = ?Head])
    show "\<not> ?Q None"
      by simp
  next
    fix br t
    assume not_head: "\<not> ?Head (Some (br, t))"
    obtain b0 r0 where br_eq: "br = (b0, r0)"
      by (cases br)
    have cont_false:
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t
       \<le> wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        (\<lambda>_ :: ((('f \<times> 'f) list) \<times>
          ('f, 'a) protocol_channel_scheme) option. False) t"
      by (rule wp_event_mono_on_support)
        (use not_head bs_eq br_eq in
          \<open>auto simp: wpsimps composition_fri_root_path_fresh_from_def
            elim!: set_dist_bindE split: option.splits prod.splits\<close>)
    also have "... = 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
    finally have le_zero:
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t \<le> 0" .
    show
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t = 0"
      by (rule antisym[OF le_zero]) simp
  next
    fix br t
    assume head:
      "Some (br, t) \<in>
        set_dist (execute receive_composition_fri_commits s)"
      and head_hit: "?Head (Some (br, t))"
    obtain b0 r0 where br_eq: "br = (b0, r0)"
      by (cases br)
    have b0_eq: "b0 = b"
      using head_hit unfolding br_eq by simp
    let ?TailQ =
      "\<lambda>out :: ((('f \<times> 'f) list) \<times>
          ('f, 'a) protocol_channel_scheme) option.
        case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs = bs' \<and>
            composition_fri_root_path_fresh_from t (map snd brs) n"
    have cont_le:
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t \<le> wp_event ?tail ?TailQ t"
	    proof (rule wp_event_bind_bound_by_head_event)
	      show "wp_event ?tail ?TailQ t \<le> wp_event ?tail ?TailQ t"
	        by simp
	    next
	      show "?Q None \<Longrightarrow> ?TailQ None"
	        by simp
    next
      fix brs u out
      assume tail_out:
          "Some (brs, u) \<in> set_dist (execute ?tail t)"
        and ret_out:
          "out \<in> set_dist (execute (return (br # brs)) u)"
        and hit: "?Q out"
      have out_eq: "out = Some (br # brs, u)"
        using ret_out
        unfolding set_dist_def return.rep_eq dist_return_def
          dist_delta_dist delta_map_def by simp
      have map_eq: "map fst brs = bs'"
        using hit out_eq b0_eq bs_eq br_eq by simp
	      have path_full:
	        "composition_fri_root_path_fresh_from s (map snd (br # brs))
	          (Suc n)"
	        using hit out_eq by simp
	      have path_full':
	        "composition_fri_root_path_fresh_from s (r0 # map snd brs)
	          (Suc n)"
	        using path_full unfolding br_eq by simp
	      have path_tail:
	        "composition_fri_root_path_fresh_from t (map snd brs) n"
	        by (rule
	            receive_composition_fri_commits_preserves_composition_root_path_fresh_tail
	            [OF path_full' head[unfolded br_eq]])
      show "?TailQ (Some (brs, u))"
        using map_eq path_tail by simp
    qed
    also have "... \<le> (1 / nnreal size) ^ n"
      by (rule Suc.IH[OF len_bs'])
    finally show
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t \<le> (1 / nnreal size) ^ n" .
  qed
  have "wp_event (ntimes receive_composition_fri_commits (Suc n)) ?Q s
      \<le> wp_event receive_composition_fri_commits ?Head s *
        (1 / nnreal size) ^ n"
    using bind_bound by simp
  also have "... \<le> (1 / nnreal size) * (1 / nnreal size) ^ n"
    by (rule mult_right_mono[OF head_bound]) simp
  also have "... = (1 / nnreal size) ^ Suc n"
    by simp
  finally show ?case .
qed

lemma wp_ntimes_receive_composition_fri_commits_finite_set_actual_fresh_bound:
  assumes finite_B: "finite B"
    and lengths: "\<And>bs. bs \<in> B \<Longrightarrow> length bs = n"
  shows
    "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs \<in> B \<and>
            composition_fri_root_path_fresh_from s (map snd brs) n) s
      \<le> nnreal (card B) / (nnreal size) ^ n"
proof -
  let ?P =
    "\<lambda>bs out. case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow>
          map fst brs = bs \<and>
          composition_fri_root_path_fresh_from s (map snd brs) n"
  have event_mono:
    "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs \<in> B \<and>
            composition_fri_root_path_fresh_from s (map snd brs) n) s
      \<le> wp_event (ntimes receive_composition_fri_commits n)
        (\<lambda>out. \<exists>bs \<in> B. ?P bs out) s"
    by (rule wp_event_mono) (auto split: option.splits prod.splits)
  also have "... \<le> (\<Sum>bs\<in>B. (1 / nnreal size) ^ n)"
    by (rule wp_event_finite_UN_bound[OF finite_B])
      (rule wp_ntimes_receive_composition_fri_commits_exact_challenges_actual_fresh_bound
        [OF lengths])
  also have "... = nnreal (card B) * ((1 / nnreal size) ^ n)"
    using finite_B by simp
  also have "... = nnreal (card B) / (nnreal size) ^ n"
    using size_card by transfer (simp add: power_divide)
  finally show ?thesis .
qed

lemma wp_ntimes_receive_composition_fri_commits_challenge_space_actual_fresh_bound:
  assumes subset: "B \<subseteq> fri_challenge_space n"
  shows
    "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs \<in> B \<and>
            composition_fri_root_path_fresh_from s (map snd brs) n) s
      \<le> nnreal (card B) / nnreal (CARD('f) ^ n)"
proof -
  have finite_B: "finite B"
    by (rule finite_subset[OF subset finite_fri_challenge_space])
  have lengths: "\<And>bs. bs \<in> B \<Longrightarrow> length bs = n"
    using subset unfolding fri_challenge_space_def by auto
  have "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            map fst brs \<in> B \<and>
            composition_fri_root_path_fresh_from s (map snd brs) n) s
      \<le> nnreal (card B) / (nnreal size) ^ n"
    by (rule
        wp_ntimes_receive_composition_fri_commits_finite_set_actual_fresh_bound
        [OF finite_B lengths])
  also have "... = nnreal (card B) / nnreal (CARD('f) ^ n)"
    using size_card by simp
  finally show ?thesis .
qed

lemma composition_fri_challenge_path_fresh_before_composition_iff:
  assumes state:
    "PState s_comp =
      concat
        (foldl concat
          (concat
            (foldl concat (concat (PState s) fr) trace_roots)
            trace_final)
          as)
        dg"
    and counter: "PCompositionFriCounter s_comp = PCompositionFriCounter s"
    and hash: "HashMap s_comp = HashMap s"
  shows
    "composition_fri_challenge_path_fresh s fr trace_roots trace_final as dg
      composition_roots n \<longleftrightarrow>
      composition_fri_root_path_fresh_from s_comp composition_roots n"
  unfolding composition_fri_challenge_path_fresh_def
    composition_fri_root_path_fresh_from_def
  by (simp add: composition_fri_challenge_key_at_def state counter hash)

lemma composition_fri_challenge_path_fresh_from_preservedI:
  assumes state:
    "PState s_comp =
      concat
        (foldl concat
          (concat
            (foldl concat (concat (PState s) fr) trace_roots)
            trace_final)
          as)
        dg"
    and counter: "PCompositionFriCounter s_comp = PCompositionFriCounter s"
    and lookup:
      "\<And>i x. fmlookup (HashMap s_comp) (CompositionFriChallenge i x) =
        fmlookup (HashMap s) (CompositionFriChallenge i x)"
    and fresh:
      "composition_fri_root_path_fresh_from s_comp composition_roots n"
	  shows
	    "composition_fri_challenge_path_fresh s fr trace_roots trace_final as dg
	      composition_roots n"
	  unfolding composition_fri_challenge_path_fresh_def
	    composition_fri_challenge_key_at_def
proof (intro allI impI)
  fix i
  assume i_lt: "i < n"
    and i_len: "i < length composition_roots"
  let ?key =
    "CompositionFriChallenge (PCompositionFriCounter s + i)
      (foldl concat
        (concat
          (foldl concat
            (concat (foldl concat (concat (PState s) fr) trace_roots)
              trace_final)
            as)
          dg)
        (take (Suc i) composition_roots))"
  have "?key =
      CompositionFriChallenge (PCompositionFriCounter s_comp + i)
        (foldl concat (PState s_comp) (take (Suc i) composition_roots))"
    using state counter by simp
  moreover have
    "fmlookup (HashMap s_comp)
      (CompositionFriChallenge (PCompositionFriCounter s_comp + i)
        (foldl concat (PState s_comp) (take (Suc i) composition_roots))) =
      None"
    using fresh i_lt i_len
    unfolding composition_fri_root_path_fresh_from_def by blast
  ultimately show "fmlookup (HashMap s) ?key = None"
    using lookup[of "PCompositionFriCounter s_comp + i"
        "foldl concat (PState s_comp) (take (Suc i) composition_roots)"]
    by simp
qed

lemma receive_trace_fri_commits_preserves_composition_fri_lookup:
  assumes outcome:
    "Some (br, t) \<in> set_dist (execute receive_trace_fri_commits s)"
  shows
    "fmlookup (HashMap t) (CompositionFriChallenge i x) =
      fmlookup (HashMap s) (CompositionFriChallenge i x)"
proof -
  obtain b r where br_eq: "br = (b, r)"
    by (cases br)
  from outcome[unfolded br_eq] obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s_read)"
    unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have neq:
    "CompositionFriChallenge i x \<noteq>
      TraceFriChallenge (PTraceFriCounter s_read) (PState s_read)"
    by simp
  have "fmlookup (HashMap t) (CompositionFriChallenge i x) =
      fmlookup (HashMap s_read) (CompositionFriChallenge i x)"
    by (rule receive_trace_fri_challenge_preserves_other_lookup
        [OF rand_b neq])
  also have "... = fmlookup (HashMap s) (CompositionFriChallenge i x)"
    using read_hash by simp
  finally show ?thesis .
qed

lemma ntimes_receive_trace_fri_commits_preserves_composition_fri_lookup:
  assumes outcome:
    "Some (brs, t) \<in>
      set_dist (execute (ntimes receive_trace_fri_commits n) s)"
  shows
    "fmlookup (HashMap t) (CompositionFriChallenge i x) =
      fmlookup (HashMap s) (CompositionFriChallenge i x)"
  using outcome
proof (induction n arbitrary: s brs t)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems obtain br brs' s1 where
    head: "Some (br, s1) \<in> set_dist (execute receive_trace_fri_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes receive_trace_fri_commits n) s1)"
    by (auto elim!: set_dist_bindE)
  have "fmlookup (HashMap t) (CompositionFriChallenge i x) =
      fmlookup (HashMap s1) (CompositionFriChallenge i x)"
    by (rule Suc.IH[OF tail])
  also have "... = fmlookup (HashMap s) (CompositionFriChallenge i x)"
    by (rule receive_trace_fri_commits_preserves_composition_fri_lookup
        [OF head])
  finally show ?case .
qed

lemma alpha_round_preserves_composition_fri_lookup:
  assumes outcome: "Some (a, t) \<in> set_dist (execute alpha_round s)"
  shows
    "fmlookup (HashMap t) (CompositionFriChallenge i x) =
      fmlookup (HashMap s) (CompositionFriChallenge i x)"
proof -
  from outcome obtain a0 s0 a1 s1 s2 where
    rand: "Some (a0, s0) \<in> set_dist (execute receive_alpha_challenge s)"
    and read_a: "Some (a1, s1) \<in> set_dist (execute read s0)"
    and assert_a: "Some ((), s2) \<in> set_dist (execute (assert (a0 = a1)) s1)"
    and ret_a: "Some (a, t) \<in> set_dist (execute (return a1) s2)"
    unfolding alpha_round_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  have neq:
    "CompositionFriChallenge i x \<noteq>
      AlphaChallenge (PAlphaCounter s) (PState s)"
    by simp
  have "fmlookup (HashMap s0) (CompositionFriChallenge i x) =
      fmlookup (HashMap s) (CompositionFriChallenge i x)"
    by (rule receive_alpha_challenge_preserves_other_lookup[OF rand neq])
  moreover have "HashMap s1 = HashMap s0"
    by (rule read_preserves_hash_map[OF read_a])
  moreover have "s2 = s1"
    using assert_a unfolding assert_def
    by (cases "a0 = a1") (auto simp: throw_no_outcome)
  moreover have "t = s2"
    using ret_a by simp
  ultimately show ?thesis
    by simp
qed

lemma mmap_alpha_round_preserves_composition_fri_lookup:
  assumes outcome:
    "Some (as, t) \<in>
      set_dist (execute (mmap (replicate n alpha_round)) s)"
  shows
    "fmlookup (HashMap t) (CompositionFriChallenge i x) =
      fmlookup (HashMap s) (CompositionFriChallenge i x)"
  using outcome
proof (induction n arbitrary: s as t)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems obtain a as' s1 where
    head: "Some (a, s1) \<in> set_dist (execute alpha_round s)"
    and tail:
      "Some (as', t) \<in>
        set_dist (execute (mmap (replicate n alpha_round)) s1)"
    by (auto elim!: set_dist_bindE)
  have "fmlookup (HashMap t) (CompositionFriChallenge i x) =
      fmlookup (HashMap s1) (CompositionFriChallenge i x)"
    by (rule Suc.IH[OF tail])
  also have "... = fmlookup (HashMap s) (CompositionFriChallenge i x)"
    by (rule alpha_round_preserves_composition_fri_lookup[OF head])
  finally show ?case .
qed

lemma wp_verifier_composition_fri_prefix_challenge_list_actual_fresh_bound:
  fixes C :: prob
  assumes subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verifier_composition_fri_prefix
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((fr, f_fl, f_final, as, dg, fl), _) \<Rightarrow>
            map fst fl \<in> B dg \<and>
            composition_fri_challenge_path_fresh s fr (map snd f_fl)
              f_final as dg (map snd fl) (length (map snd fl))) s
      \<le> C"
proof -
  let ?Q =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl, f_final, as, dg, fl), _) \<Rightarrow>
          map fst fl \<in> B dg \<and>
          composition_fri_challenge_path_fresh s fr (map snd f_fl)
            f_final as dg (map snd fl) (length (map snd fl))"
  show ?thesis
    unfolding verifier_composition_fri_prefix_def
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?Q None"
      by simp
  next
    fix fr s1
    assume read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    from read_outcome[OF read_fr] have st_s1:
      "PState s1 = concat (PState s) fr"
      by blast
    from read_outcome[OF read_fr] have comp_count_s1:
      "PCompositionFriCounter s1 = PCompositionFriCounter s"
      by blast
    have hash_s1: "HashMap s1 = HashMap s"
      by (rule read_preserves_hash_map[OF read_fr])
    show "wp_event
        (ntimes receive_trace_fri_commits (ceil_log clength) \<bind>
          (\<lambda>f_fl. read \<bind>
            (\<lambda>f_final.
              mmap (replicate (length spec) alpha_round) \<bind>
                (\<lambda>as. read \<bind>
                  (\<lambda>dg.
                    assert (to_nat dg \<le> maxDegree) \<bind>
                      (\<lambda>_. ntimes receive_composition_fri_commits
                        (ceil_log (to_nat dg + 1)) \<bind>
                        (\<lambda>fl.
                          return (fr, f_fl, f_final, as, dg, fl))))))))
        ?Q s1 \<le> C"
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?Q None"
        by simp
    next
      fix f_fl s2
      assume trace_fri:
        "Some (f_fl, s2) \<in>
          set_dist
            (execute (ntimes receive_trace_fri_commits (ceil_log clength)) s1)"
      have trace_res:
        "PState s2 = foldl concat (PState s1) (map snd f_fl) \<and>
         PCompositionFriCounter s2 = PCompositionFriCounter s1"
        using ntimes_receive_trace_fri_commits_outcome[OF trace_fri]
        by simp
      have lookup_s2:
        "\<And>i x. fmlookup (HashMap s2) (CompositionFriChallenge i x) =
          fmlookup (HashMap s) (CompositionFriChallenge i x)"
      proof -
        fix i x
        have "fmlookup (HashMap s2) (CompositionFriChallenge i x) =
            fmlookup (HashMap s1) (CompositionFriChallenge i x)"
          by (rule ntimes_receive_trace_fri_commits_preserves_composition_fri_lookup
              [OF trace_fri])
        also have "... = fmlookup (HashMap s) (CompositionFriChallenge i x)"
          using hash_s1 by simp
        finally show
          "fmlookup (HashMap s2) (CompositionFriChallenge i x) =
            fmlookup (HashMap s) (CompositionFriChallenge i x)" .
      qed
      show "wp_event
          (read \<bind>
            (\<lambda>f_final.
              mmap (replicate (length spec) alpha_round) \<bind>
                (\<lambda>as. read \<bind>
                  (\<lambda>dg.
                    assert (to_nat dg \<le> maxDegree) \<bind>
                      (\<lambda>_. ntimes receive_composition_fri_commits
                        (ceil_log (to_nat dg + 1)) \<bind>
                        (\<lambda>fl.
                          return (fr, f_fl, f_final, as, dg, fl)))))))
          ?Q s2 \<le> C"
      proof (rule wp_event_bind_bound_by_cont)
        show "\<not> ?Q None"
          by simp
      next
        fix f_final s3
        assume read_final: "Some (f_final, s3) \<in> set_dist (execute read s2)"
        from read_outcome[OF read_final] have st_s3:
          "PState s3 = concat (PState s2) f_final"
          by blast
        from read_outcome[OF read_final] have comp_count_s3:
          "PCompositionFriCounter s3 = PCompositionFriCounter s2"
          by blast
        have hash_s3: "HashMap s3 = HashMap s2"
          by (rule read_preserves_hash_map[OF read_final])
        have lookup_s3:
          "\<And>i x. fmlookup (HashMap s3) (CompositionFriChallenge i x) =
            fmlookup (HashMap s) (CompositionFriChallenge i x)"
          using hash_s3 lookup_s2 by simp
        show "wp_event
            (mmap (replicate (length spec) alpha_round) \<bind>
              (\<lambda>as. read \<bind>
                (\<lambda>dg.
                  assert (to_nat dg \<le> maxDegree) \<bind>
                    (\<lambda>_. ntimes receive_composition_fri_commits
                      (ceil_log (to_nat dg + 1)) \<bind>
                      (\<lambda>fl.
                        return (fr, f_fl, f_final, as, dg, fl))))))
            ?Q s3 \<le> C"
        proof (rule wp_event_bind_bound_by_cont)
          show "\<not> ?Q None"
            by simp
        next
          fix as s4
          assume alpha:
            "Some (as, s4) \<in>
              set_dist
                (execute (mmap (replicate (length spec) alpha_round)) s3)"
          have alpha_res:
            "PState s4 = foldl concat (PState s3) as \<and>
             PCompositionFriCounter s4 = PCompositionFriCounter s3"
            using mmap_alpha_round_outcome[OF alpha] by simp
          have lookup_s4:
            "\<And>i x. fmlookup (HashMap s4) (CompositionFriChallenge i x) =
              fmlookup (HashMap s) (CompositionFriChallenge i x)"
          proof -
            fix i x
            have "fmlookup (HashMap s4) (CompositionFriChallenge i x) =
                fmlookup (HashMap s3) (CompositionFriChallenge i x)"
              by (rule mmap_alpha_round_preserves_composition_fri_lookup
                  [OF alpha])
            also have "... =
                fmlookup (HashMap s) (CompositionFriChallenge i x)"
              by (rule lookup_s3)
            finally show
              "fmlookup (HashMap s4) (CompositionFriChallenge i x) =
                fmlookup (HashMap s) (CompositionFriChallenge i x)" .
          qed
          show "wp_event
              (read \<bind>
                (\<lambda>dg.
                  assert (to_nat dg \<le> maxDegree) \<bind>
                    (\<lambda>_. ntimes receive_composition_fri_commits
                      (ceil_log (to_nat dg + 1)) \<bind>
                      (\<lambda>fl.
                        return (fr, f_fl, f_final, as, dg, fl)))))
              ?Q s4 \<le> C"
          proof (rule wp_event_bind_bound_by_cont)
            show "\<not> ?Q None"
              by simp
          next
            fix dg s5
            assume read_dg: "Some (dg, s5) \<in> set_dist (execute read s4)"
            from read_outcome[OF read_dg] have st_s5:
              "PState s5 = concat (PState s4) dg"
              by blast
            from read_outcome[OF read_dg] have comp_count_s5:
              "PCompositionFriCounter s5 = PCompositionFriCounter s4"
              by blast
            have hash_s5: "HashMap s5 = HashMap s4"
              by (rule read_preserves_hash_map[OF read_dg])
            have lookup_s5:
              "\<And>i x. fmlookup (HashMap s5) (CompositionFriChallenge i x) =
                fmlookup (HashMap s) (CompositionFriChallenge i x)"
              using hash_s5 lookup_s4 by simp
            show "wp_event
                (assert (to_nat dg \<le> maxDegree) \<bind>
                  (\<lambda>_. ntimes receive_composition_fri_commits
                    (ceil_log (to_nat dg + 1)) \<bind>
                    (\<lambda>fl.
                      return (fr, f_fl, f_final, as, dg, fl))))
                ?Q s5 \<le> C"
            proof (rule wp_event_bind_bound_by_cont)
              show "\<not> ?Q None"
                by simp
            next
              fix u s6
              assume assert_out:
                "Some (u, s6) \<in>
                  set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
              have s6_eq: "s6 = s5"
                using assert_out unfolding assert_def
                by (cases "to_nat dg \<le> maxDegree")
                  (auto simp: throw_no_outcome)
              have state_s6:
                "PState s6 =
                  concat
                    (foldl concat
                      (concat
                        (foldl concat (concat (PState s) fr)
                          (map snd f_fl))
                        f_final)
                      as)
                    dg"
                using st_s1 trace_res st_s3 alpha_res st_s5 s6_eq
                by simp
              have counter_s6:
                "PCompositionFriCounter s6 = PCompositionFriCounter s"
                using comp_count_s1 trace_res comp_count_s3 alpha_res
                  comp_count_s5 s6_eq
                by simp
              have lookup_s6:
                "\<And>i x. fmlookup (HashMap s6)
                    (CompositionFriChallenge i x) =
                  fmlookup (HashMap s) (CompositionFriChallenge i x)"
                using lookup_s5 s6_eq by simp
              let ?Head =
                "\<lambda>out. case out of
                    None \<Rightarrow> False
                  | Some (fl, _) \<Rightarrow>
                      map fst fl \<in> B dg \<and>
                      composition_fri_root_path_fresh_from s6 (map snd fl)
                        (ceil_log (to_nat dg + 1))"
              have comp_bound:
                "wp_event
                  (ntimes receive_composition_fri_commits
                    (ceil_log (to_nat dg + 1)))
                  ?Head s6 \<le>
                  nnreal (card (B dg)) /
                    nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
                by (rule
                    wp_ntimes_receive_composition_fri_commits_challenge_space_actual_fresh_bound
                    [OF subset])
              have comp_bound_C:
                "wp_event
                  (ntimes receive_composition_fri_commits
                    (ceil_log (to_nat dg + 1)))
                  ?Head s6 \<le> C"
                by (rule order_trans[OF comp_bound bound])
              show "wp_event
                  (ntimes receive_composition_fri_commits
                    (ceil_log (to_nat dg + 1)) \<bind>
                    (\<lambda>fl.
                      return (fr, f_fl, f_final, as, dg, fl)))
                  ?Q s6 \<le> C"
              proof (rule wp_event_bind_bound_by_head_event[OF comp_bound_C])
                show "?Q None \<Longrightarrow> ?Head None"
                  by simp
              next
                fix fl t out
                assume comp_out:
                    "Some (fl, t) \<in>
                      set_dist
                        (execute
                          (ntimes receive_composition_fri_commits
                            (ceil_log (to_nat dg + 1))) s6)"
                  and cont:
                    "out \<in>
                      set_dist
                        (execute
                          (return (fr, f_fl, f_final, as, dg, fl)) t)"
                  and hit: "?Q out"
                have out_eq:
                  "out = Some ((fr, f_fl, f_final, as, dg, fl), t)"
                  using cont
                  unfolding set_dist_def return.rep_eq dist_return_def
                    dist_delta_dist delta_map_def
                  by simp
                have len_fl: "length fl = ceil_log (to_nat dg + 1)"
                  using ntimes_receive_composition_fri_commits_outcome
                    [OF comp_out] by simp
	                have path_fresh_len:
	                  "composition_fri_challenge_path_fresh s fr
	                    (map snd f_fl) f_final as dg (map snd fl)
	                    (length fl)"
	                  using hit out_eq by simp
	                have root_fresh_head:
	                  "composition_fri_root_path_fresh_from s6 (map snd fl)
	                    (ceil_log (to_nat dg + 1))"
	                  using path_fresh_len len_fl state_s6 counter_s6 lookup_s6
	                  unfolding composition_fri_challenge_path_fresh_def
	                    composition_fri_root_path_fresh_from_def
	                    composition_fri_challenge_key_at_def
	                  by simp
	                have root_fresh:
	                  "composition_fri_root_path_fresh_from s6 (map snd fl)
	                    (ceil_log (Suc (to_nat dg)))"
	                  using root_fresh_head by simp
                have path_fresh:
                  "composition_fri_challenge_path_fresh s fr (map snd f_fl)
                    f_final as dg (map snd fl) (length (map snd fl))"
                  using composition_fri_challenge_path_fresh_from_preservedI
                    [OF state_s6 counter_s6 lookup_s6 root_fresh]
                    len_fl
                  by simp
	                show "?Head (Some (fl, t))"
	                  using hit out_eq root_fresh_head by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma wp_verify_monad_composition_fri_challenge_list_fresh_hit_actual_bound:
  fixes C :: prob
  assumes subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad (composition_fri_challenge_list_fresh_hit s B) s
      \<le> C"
proof -
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl, f_final, as, dg, fl), _) \<Rightarrow>
          map fst fl \<in> B dg \<and>
          composition_fri_challenge_path_fresh s fr (map snd f_fl)
            f_final as dg (map snd fl) (length (map snd fl))"
  have prefix_bound:
    "wp_event verifier_composition_fri_prefix ?Head s \<le> C"
    by (rule
        wp_verifier_composition_fri_prefix_challenge_list_actual_fresh_bound
        [OF subset bound])
  show ?thesis
    unfolding verify_monad_composition_fri_decomposition
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show "composition_fri_challenge_list_fresh_hit s B None \<Longrightarrow>
      ?Head None"
      unfolding composition_fri_challenge_list_fresh_hit_def
        accepted_fri_challenges_def by blast
  next
    fix header prefix_state out
    assume prefix:
      "Some (header, prefix_state) \<in>
        set_dist (execute verifier_composition_fri_prefix s)"
      and suffix:
        "out \<in>
          set_dist (execute
            (verifier_after_composition_fri header) prefix_state)"
      and hit: "composition_fri_challenge_list_fresh_hit s B out"
    obtain fr f_fl f_final as dg fl where header_eq:
      "header = (fr, f_fl, f_final, as, dg, fl)"
      by (cases header) auto
    from hit obtain trace_bs dg' comp_bs fr' trace_roots' trace_final'
        as' composition_roots' final' rest' where
      challenges_hit: "accepted_fri_challenges s out trace_bs dg' comp_bs"
      and header_hit:
        "verifier_header_transcript s fr' trace_roots' trace_final' as' dg'
          composition_roots' final' rest'"
      and comp_bs_B: "comp_bs \<in> B dg'"
      and fresh_hit:
        "composition_fri_challenge_path_fresh s fr' trace_roots'
          trace_final' as' dg' composition_roots'
          (length composition_roots')"
      unfolding composition_fri_challenge_list_fresh_hit_def by blast
    from challenges_hit obtain result final_state where out_eq:
      "out = Some (result, final_state)"
      unfolding accepted_fri_challenges_def by blast
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
    from suffix' obtain final query_state where
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
      unfolding verifier_after_composition_fri_def
      by (auto elim!: set_dist_bindE)
    have prefix_res:
      "length f_fl = ceil_log clength \<and>
       length as = length spec \<and>
       length fl = ceil_log (to_nat dg + 1) \<and>
       PTranscript s =
         [fr] @ map snd f_fl @ [f_final] @ as @ [dg] @
         map snd fl @ PTranscript prefix_state"
      using verifier_composition_fri_prefix_outcome[OF prefix'] by simp
    from read_outcome[OF read_final] obtain rest_query where
      tr_prefix: "PTranscript prefix_state = final # rest_query"
      and tr_query: "PTranscript query_state = rest_query"
      by blast
    have header_prefix:
      "verifier_header_transcript s fr (map snd f_fl) f_final as dg
        (map snd fl) final (PTranscript query_state)"
      using prefix_res tr_prefix tr_query
      unfolding verifier_header_transcript_def verifier_header_messages_def
      by simp
    have challenges_prefix:
      "accepted_fri_challenges s (Some (result, final_state))
        (map fst f_fl) dg (map fst fl)"
      by (rule verifier_after_composition_fri_accepted_fri_challenges
          [OF prefix' suffix'])
    have eqs:
      "trace_bs = map fst f_fl \<and> dg' = dg \<and> comp_bs = map fst fl"
      using accepted_fri_challenges_unique
        [OF challenges_prefix challenges_hit[unfolded out_eq]]
      by simp
    have header_eqs:
      "fr' = fr \<and>
       trace_roots' = map snd f_fl \<and>
       trace_final' = f_final \<and>
       as' = as \<and>
       composition_roots' = map snd fl"
      using verifier_header_transcript_unique[OF header_prefix header_hit]
        eqs
      by simp
    then have fresh_prefix:
      "composition_fri_challenge_path_fresh s fr (map snd f_fl)
        f_final as dg (map snd fl) (length (map snd fl))"
      using fresh_hit eqs by simp
    show "?Head (Some (header, prefix_state))"
      using comp_bs_B eqs fresh_prefix header_eq by simp
  qed
qed

lemma trace_fri_challenge_list_fresh_hit_imp_set_hit:
  assumes "trace_fri_challenge_list_fresh_hit s B out"
  shows "trace_fri_challenge_list_set_hit s B out"
  using assms
  unfolding trace_fri_challenge_list_fresh_hit_def
    trace_fri_challenge_list_set_hit_def
  by blast

lemma composition_fri_challenge_list_fresh_hit_imp_set_hit:
  assumes "composition_fri_challenge_list_fresh_hit s B out"
  shows "composition_fri_challenge_list_set_hit s B out"
  using assms
  unfolding composition_fri_challenge_list_fresh_hit_def
    composition_fri_challenge_list_set_hit_def
  by blast

lemma wp_trace_fri_challenge_list_fresh_hit_bound_from_future_fresh:
  assumes future: "trace_fri_future_fresh s"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
  shows
    "wp_event verify_monad (trace_fri_challenge_list_fresh_hit s B) s \<le>
      nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
proof -
  have "wp_event verify_monad (trace_fri_challenge_list_fresh_hit s B) s
      \<le> wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule trace_fri_challenge_list_fresh_hit_imp_set_hit)
  also have "... \<le>
      nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verify_monad_trace_fri_challenge_list_set_bound
        [OF future subset])
  finally show ?thesis .
qed

lemma wp_composition_fri_challenge_list_fresh_hit_bound_from_future_fresh:
  assumes future: "composition_fri_future_fresh s"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad (composition_fri_challenge_list_fresh_hit s B) s
      \<le> C"
proof -
  have "wp_event verify_monad (composition_fri_challenge_list_fresh_hit s B) s
      \<le> wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule composition_fri_challenge_list_fresh_hit_imp_set_hit)
  also have "... \<le> C"
    by (rule wp_verify_monad_composition_fri_challenge_list_set_bound
        [OF future subset bound])
  finally show ?thesis .
qed

lemma accepted_fri_challenges_headerE:
  assumes "accepted_fri_challenges s out trace_bs dg comp_bs"
  obtains fr f_fl trace_final alphas fl final rest where
    "verifier_header_transcript s fr (map snd f_fl) trace_final alphas dg
      (map snd fl) final rest"
    "trace_bs = map fst f_fl"
    "comp_bs = map fst fl"
proof -
  from assms obtain result final_state fr f_fl trace_final alphas fl final
      query_state where body:
    "out = Some (result, final_state) \<and>
      verifier_header_transcript s fr (map snd f_fl) trace_final alphas dg
        (map snd fl) final (PTranscript query_state) \<and>
      PState query_state =
        verifier_header_state s fr (map snd f_fl) trace_final alphas dg
          (map snd fl) final \<and>
      Some (result, final_state) \<in>
        set_dist (execute
          (ntimes (verifier_query_round_program fr f_fl trace_final alphas fl final)
            rounds)
          query_state) \<and>
      PQueryCounter query_state = PQueryCounter s \<and>
      trace_bs = map fst f_fl \<and>
      comp_bs = map fst fl \<and>
      (\<forall>i < length f_fl.
        fmlookup (HashMap query_state)
          (TraceFriChallenge (PTraceFriCounter s + i)
            (foldl concat (concat (PState s) fr)
              (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))) \<and>
      (\<forall>i < length fl.
        fmlookup (HashMap query_state)
          (CompositionFriChallenge (PCompositionFriCounter s + i)
            (foldl concat
              (concat
                (foldl concat
                  (concat
                    (foldl concat (concat (PState s) fr) (map snd f_fl))
                    trace_final)
                  alphas)
                dg)
              (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i)))"
    unfolding accepted_fri_challenges_def by blast
  have header:
    "verifier_header_transcript s fr (map snd f_fl) trace_final alphas dg
      (map snd fl) final (PTranscript query_state)"
    using body by simp
  have trace_eq: "trace_bs = map fst f_fl"
    using body by simp
  have comp_eq: "comp_bs = map fst fl"
    using body by simp
  show thesis
    by (rule that[of fr f_fl trace_final alphas fl final
          "PTranscript query_state",
          OF header trace_eq comp_eq])
qed

lemma trace_fri_challenge_path_fresh_or_prequeried:
  "trace_fri_challenge_path_fresh s fr roots n \<or>
    trace_fri_challenge_path_prequeried s fr roots n"
proof (cases "\<exists>i < n. i < length roots \<and>
    fmlookup (HashMap s) (trace_fri_challenge_key_at s fr roots i) \<noteq>
      None")
  case True
  then have "trace_fri_challenge_path_prequeried s fr roots n"
    unfolding trace_fri_challenge_path_prequeried_def .
  then show ?thesis by simp
next
  case False
  then have "trace_fri_challenge_path_fresh s fr roots n"
    unfolding trace_fri_challenge_path_fresh_def
    by auto
  then show ?thesis by simp
qed

lemma composition_fri_challenge_path_fresh_or_prequeried:
  "composition_fri_challenge_path_fresh s fr trace_roots trace_final as dg
      composition_roots n \<or>
    composition_fri_challenge_path_prequeried s fr trace_roots trace_final as
      dg composition_roots n"
proof (cases "\<exists>i < n. i < length composition_roots \<and>
    fmlookup (HashMap s)
      (composition_fri_challenge_key_at s fr trace_roots trace_final as dg
        composition_roots i) \<noteq> None")
  case True
  then have "composition_fri_challenge_path_prequeried s fr trace_roots
      trace_final as dg composition_roots n"
    unfolding composition_fri_challenge_path_prequeried_def .
  then show ?thesis by simp
next
  case False
  then have "composition_fri_challenge_path_fresh s fr trace_roots
      trace_final as dg composition_roots n"
    unfolding composition_fri_challenge_path_fresh_def
    by auto
  then show ?thesis by simp
qed

lemma trace_fri_challenge_list_set_hit_imp_fresh_or_prequery:
  assumes "trace_fri_challenge_list_set_hit s B out"
  shows
    "trace_fri_challenge_list_fresh_hit s B out \<or>
     trace_fri_challenge_list_prequery_hit s B out"
proof -
  from assms obtain trace_bs dg comp_bs where hit:
    "accepted_fri_challenges s out trace_bs dg comp_bs"
    "trace_bs \<in> B"
    unfolding trace_fri_challenge_list_set_hit_def by auto
  from hit(1) obtain fr f_fl trace_final alphas fl final rest where
    header:
      "verifier_header_transcript s fr (map snd f_fl) trace_final alphas dg
      (map snd fl) final rest"
    "trace_bs = map fst f_fl"
    "comp_bs = map fst fl"
    by (rule accepted_fri_challenges_headerE)
  have split: "trace_fri_challenge_path_fresh s fr (map snd f_fl)
      (length (map snd f_fl)) \<or>
    trace_fri_challenge_path_prequeried s fr (map snd f_fl)
      (length (map snd f_fl))"
    by (rule trace_fri_challenge_path_fresh_or_prequeried)
  then show ?thesis
  proof
    assume fresh: "trace_fri_challenge_path_fresh s fr (map snd f_fl)
      (length (map snd f_fl))"
    have "trace_fri_challenge_list_fresh_hit s B out"
      unfolding trace_fri_challenge_list_fresh_hit_def
      by (intro exI conjI; (rule hit(1) | rule header | rule hit(2) |
          rule fresh))
    then show ?thesis by simp
  next
    assume prequeried: "trace_fri_challenge_path_prequeried s fr
      (map snd f_fl) (length (map snd f_fl))"
    have "trace_fri_challenge_list_prequery_hit s B out"
      unfolding trace_fri_challenge_list_prequery_hit_def
      by (intro exI conjI; (rule hit(1) | rule header | rule hit(2) |
          rule prequeried))
    then show ?thesis by simp
  qed
qed

lemma composition_fri_challenge_list_set_hit_imp_fresh_or_prequery:
  assumes "composition_fri_challenge_list_set_hit s B out"
  shows
    "composition_fri_challenge_list_fresh_hit s B out \<or>
     composition_fri_challenge_list_prequery_hit s B out"
proof -
  from assms obtain trace_bs dg comp_bs where hit:
    "accepted_fri_challenges s out trace_bs dg comp_bs"
    "comp_bs \<in> B dg"
    unfolding composition_fri_challenge_list_set_hit_def by auto
  from hit(1) obtain fr f_fl trace_final alphas fl final rest where
    header:
      "verifier_header_transcript s fr (map snd f_fl) trace_final alphas dg
      (map snd fl) final rest"
    "trace_bs = map fst f_fl"
    "comp_bs = map fst fl"
    by (rule accepted_fri_challenges_headerE)
  have split: "composition_fri_challenge_path_fresh s fr (map snd f_fl)
      trace_final alphas dg (map snd fl) (length (map snd fl)) \<or>
    composition_fri_challenge_path_prequeried s fr (map snd f_fl)
      trace_final alphas dg (map snd fl) (length (map snd fl))"
    by (rule composition_fri_challenge_path_fresh_or_prequeried)
  then show ?thesis
  proof
    assume fresh: "composition_fri_challenge_path_fresh s fr (map snd f_fl)
      trace_final alphas dg (map snd fl) (length (map snd fl))"
    have "composition_fri_challenge_list_fresh_hit s B out"
      unfolding composition_fri_challenge_list_fresh_hit_def
      by (intro exI conjI; (rule hit(1) | rule header | rule hit(2) |
          rule fresh))
    then show ?thesis by simp
  next
    assume prequeried: "composition_fri_challenge_path_prequeried s fr
      (map snd f_fl) trace_final alphas dg (map snd fl) (length (map snd fl))"
    have "composition_fri_challenge_list_prequery_hit s B out"
      unfolding composition_fri_challenge_list_prequery_hit_def
      by (intro exI conjI; (rule hit(1) | rule header | rule hit(2) |
          rule prequeried))
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_challenge_list_set_hit_bound_from_fresh_and_prequery:
  assumes fresh_bound:
    "wp_event verify_monad (trace_fri_challenge_list_fresh_hit s B) s \<le> F"
    and prequery_bound:
    "wp_event verify_monad (trace_fri_challenge_list_prequery_hit s B) s
      \<le> P"
  shows "wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s
    \<le> F + P"
proof -
  have "wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s \<le>
      wp_event verify_monad
        (\<lambda>out. trace_fri_challenge_list_fresh_hit s B out \<or>
          trace_fri_challenge_list_prequery_hit s B out) s"
    by (rule wp_event_mono)
      (rule trace_fri_challenge_list_set_hit_imp_fresh_or_prequery)
  also have "... \<le>
      wp_event verify_monad (trace_fri_challenge_list_fresh_hit s B) s +
      wp_event verify_monad (trace_fri_challenge_list_prequery_hit s B) s"
    by (rule wp_event_union_bound)
  also have "... \<le> F + P"
    by (rule add_mono[OF fresh_bound prequery_bound])
  finally show ?thesis .
qed

lemma wp_composition_fri_challenge_list_set_hit_bound_from_fresh_and_prequery:
  assumes fresh_bound:
    "wp_event verify_monad (composition_fri_challenge_list_fresh_hit s B) s
      \<le> F"
    and prequery_bound:
    "wp_event verify_monad (composition_fri_challenge_list_prequery_hit s B) s
      \<le> P"
  shows "wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s
    \<le> F + P"
proof -
  have "wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s
      \<le> wp_event verify_monad
        (\<lambda>out. composition_fri_challenge_list_fresh_hit s B out \<or>
          composition_fri_challenge_list_prequery_hit s B out) s"
    by (rule wp_event_mono)
      (rule composition_fri_challenge_list_set_hit_imp_fresh_or_prequery)
  also have "... \<le>
      wp_event verify_monad (composition_fri_challenge_list_fresh_hit s B) s +
      wp_event verify_monad (composition_fri_challenge_list_prequery_hit s B) s"
    by (rule wp_event_union_bound)
  also have "... \<le> F + P"
    by (rule add_mono[OF fresh_bound prequery_bound])
  finally show ?thesis .
qed

end

context soundness
begin

lemma checked_staged_security_trace_fri_challenge_list_set_hit_bound_from_fresh_and_prequery:
  assumes fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and prequery_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_prequery_hit s B))
      adversary_initial_state \<le> P"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_set_hit s B))
      adversary_initial_state \<le> F + P"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_set_hit s B))
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s out.
            trace_fri_challenge_list_fresh_hit s B out \<or>
            trace_fri_challenge_list_prequery_hit s B out))
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_set_hit s B) out"
    then show
      "staged_security_with_data_state_verifier_event
        (\<lambda>s out.
          trace_fri_challenge_list_fresh_hit s B out \<or>
          trace_fri_challenge_list_prequery_hit s B out) out"
      unfolding staged_security_with_data_state_verifier_event_def
      by (auto dest: trace_fri_challenge_list_set_hit_imp_fresh_or_prequery
          split: option.splits prod.splits)
  qed
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_challenge_list_fresh_hit s B) out \<or>
          staged_security_with_data_state_verifier_event
            (\<lambda>s. trace_fri_challenge_list_prequery_hit s B) out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_prequery_hit s B))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> F + P"
    by (rule add_mono[OF fresh_bound prequery_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_challenge_list_set_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_set_hit s B))
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  by (rule
      checked_staged_security_trace_fri_challenge_list_set_hit_bound_from_fresh_and_prequery)
    (rule fresh_bound,
     rule checked_staged_security_trace_fri_verifier_prequery_hit_bound
      [OF wf controlled finite_B])

lemma checked_staged_security_trace_fri_challenge_list_fresh_hit_actual_bound:
  assumes subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le>
      nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> trace_fri_challenge_list_fresh_hit s B None"
    unfolding trace_fri_challenge_list_fresh_hit_def
      accepted_fri_challenges_def by blast
next
  fix data attacker_state
  assume "Some (data, attacker_state) \<in>
    set_dist
      (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (trace_fri_challenge_list_fresh_hit
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) B)
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verify_monad_trace_fri_challenge_list_fresh_hit_actual_bound
        [OF subset])
qed

lemma checked_staged_security_trace_fri_bad_challenge_list_fresh_hit_bound_from_round_bounds:
  assumes local_bound:
    "\<And>i prefix.
      i < fri_round_count_for_degree_bound (clength - 1) \<Longrightarrow>
      length prefix = i \<Longrightarrow>
      card (bad i prefix) \<le> bd i"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s
          (generic_fri_bad_challenge_lists
            (fri_round_count_for_degree_bound (clength - 1)) bad)))
      adversary_initial_state \<le>
      nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (clength - 1)}.
          CARD('f) ^ i * bd i *
            CARD('f) ^
              (fri_round_count_for_degree_bound (clength - 1) - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound (clength - 1))"
proof -
  let ?n = "fri_round_count_for_degree_bound (clength - 1)"
  let ?B = "generic_fri_bad_challenge_lists ?n bad"
  let ?K =
    "(\<Sum>i \<in> {..<?n}.
      CARD('f) ^ i * bd i * CARD('f) ^ (?n - Suc i))"
	  have subset: "?B \<subseteq> fri_challenge_space (ceil_log clength)"
	    using generic_fri_bad_challenge_lists_subset[of ?n bad]
	    by (simp add: fri_round_count_for_degree_bound_def clength_pos)
  have base:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s ?B))
      adversary_initial_state \<le>
      nnreal (card ?B) / nnreal (CARD('f) ^ ceil_log clength)"
    by (rule checked_staged_security_trace_fri_challenge_list_fresh_hit_actual_bound
        [OF subset])
  have card_bound: "card ?B \<le> ?K"
    by (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds)
      (rule local_bound)
  have ratio_bound:
    "nnreal (card ?B) / nnreal (CARD('f) ^ ceil_log clength)
      \<le> nnreal ?K / nnreal (CARD('f) ^ ?n)"
  proof -
    have "nnreal (card ?B) / nnreal (CARD('f) ^ ceil_log clength)
        \<le> nnreal ?K / nnreal (CARD('f) ^ ceil_log clength)"
      using card_bound by (rule nnreal_nat_divide_right_mono)
	    also have "... = nnreal ?K / nnreal (CARD('f) ^ ?n)"
	      by (simp add: fri_round_count_for_degree_bound_def clength_pos)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule order_trans[OF base ratio_bound])
qed

lemma checked_staged_security_composition_fri_challenge_list_fresh_hit_actual_bound:
  fixes C :: prob
  assumes subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> C"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> composition_fri_challenge_list_fresh_hit s B None"
    unfolding composition_fri_challenge_list_fresh_hit_def
      accepted_fri_challenges_def by blast
next
  fix data attacker_state
  assume "Some (data, attacker_state) \<in>
    set_dist
      (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (composition_fri_challenge_list_fresh_hit
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) B)
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> C"
    by (rule wp_verify_monad_composition_fri_challenge_list_fresh_hit_actual_bound
        [OF subset bound])
qed

lemma checked_staged_security_composition_fri_bad_challenge_list_fresh_hit_bound_from_round_bounds:
  fixes C :: prob
  assumes local_bound:
    "\<And>dg i prefix.
      i < fri_round_count_for_degree_bound (to_nat dg) \<Longrightarrow>
      length prefix = i \<Longrightarrow>
      card (bad dg i prefix) \<le> bd dg i"
    and fraction_bound:
    "\<And>dg.
      nnreal
        (\<Sum>i \<in> {..<fri_round_count_for_degree_bound (to_nat dg)}.
          CARD('f) ^ i * bd dg i *
            CARD('f) ^
              (fri_round_count_for_degree_bound (to_nat dg) - Suc i)) /
      nnreal (CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg)) \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s
          (\<lambda>dg. generic_fri_bad_challenge_lists
            (fri_round_count_for_degree_bound (to_nat dg)) (bad dg))))
      adversary_initial_state \<le> C"
proof -
  let ?B =
    "\<lambda>dg. generic_fri_bad_challenge_lists
      (fri_round_count_for_degree_bound (to_nat dg)) (bad dg)"
	  have subset:
	    "\<And>dg. ?B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
	    using generic_fri_bad_challenge_lists_subset
	    by (simp add: fri_round_count_for_degree_bound_def)
  have ratio_bound:
    "\<And>dg. nnreal (card (?B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  proof -
    fix dg
    let ?n = "fri_round_count_for_degree_bound (to_nat dg)"
    let ?K =
      "(\<Sum>i \<in> {..<?n}.
        CARD('f) ^ i * bd dg i * CARD('f) ^ (?n - Suc i))"
    have card_bound: "card (?B dg) \<le> ?K"
      by (rule generic_fri_bad_challenge_lists_card_bound_from_round_bounds)
        (rule local_bound)
    have "nnreal (card (?B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))
        \<le> nnreal ?K / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
      using card_bound by (rule nnreal_nat_divide_right_mono)
	    also have "... = nnreal ?K / nnreal (CARD('f) ^ ?n)"
	      by (simp add: fri_round_count_for_degree_bound_def)
    also have "... \<le> C"
      by (rule fraction_bound)
    finally show
      "nnreal (card (?B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C" .
  qed
  show ?thesis
    by (rule
        checked_staged_security_composition_fri_challenge_list_fresh_hit_actual_bound
        [OF subset ratio_bound])
qed

lemma checked_staged_security_composition_fri_challenge_list_set_hit_bound_from_fresh_and_prequery:
  assumes fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and prequery_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_prequery_hit s B))
      adversary_initial_state \<le> P"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_set_hit s B))
      adversary_initial_state \<le> F + P"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_set_hit s B))
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s out.
            composition_fri_challenge_list_fresh_hit s B out \<or>
            composition_fri_challenge_list_prequery_hit s B out))
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_set_hit s B) out"
    then show
      "staged_security_with_data_state_verifier_event
        (\<lambda>s out.
          composition_fri_challenge_list_fresh_hit s B out \<or>
          composition_fri_challenge_list_prequery_hit s B out) out"
      unfolding staged_security_with_data_state_verifier_event_def
      by (auto dest:
          composition_fri_challenge_list_set_hit_imp_fresh_or_prequery
          split: option.splits prod.splits)
  qed
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out.
          staged_security_with_data_state_verifier_event
            (\<lambda>s. composition_fri_challenge_list_fresh_hit s B) out \<or>
          staged_security_with_data_state_verifier_event
            (\<lambda>s. composition_fri_challenge_list_prequery_hit s B) out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_challenge_list_prequery_hit s B))
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> F + P"
    by (rule add_mono[OF fresh_bound prequery_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_challenge_list_set_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_set_hit s B))
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  by (rule
      checked_staged_security_composition_fri_challenge_list_set_hit_bound_from_fresh_and_prequery)
    (rule fresh_bound,
     rule checked_staged_security_composition_fri_verifier_prequery_hit_bound
      [OF wf controlled finite_B])

end

end
