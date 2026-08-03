(*  Title:      Stark/Soundness_Execution_Prefix.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Execution_Prefix
  imports Soundness_Execution_Query
begin

text \<open>Verifier alpha/FRI prefix execution and challenge-space bounds.\<close>

context soundness
begin

definition alpha_round
  where
    "alpha_round =
      (do {
        a0 \<leftarrow> receive_alpha_challenge;
        let a0' = a0;
        a1 \<leftarrow> read;
        let a1' = a1;
        assert (a0' = a1');
        return a1'
      })"

definition verifier_alpha_prefix
  :: "('f \<times> ('f \<times> 'f) list \<times> 'f \<times> 'f list,
       ('f, 'a) protocol_channel_scheme) state_monad"
  where
    "verifier_alpha_prefix =
      (do {
        fr \<leftarrow> read;
        f_fl \<leftarrow> ntimes receive_trace_fri_commits (ceil_log clength);
        f_final \<leftarrow> read;
        as \<leftarrow> mmap (replicate (length spec) alpha_round);
        return (fr, f_fl, f_final, as)
      })"

definition verifier_trace_fri_prefix
  :: "('f \<times> ('f \<times> 'f) list,
       ('f, 'a) protocol_channel_scheme) state_monad"
  where
    "verifier_trace_fri_prefix =
      (do {
        fr \<leftarrow> read;
        f_fl \<leftarrow> ntimes receive_trace_fri_commits (ceil_log clength);
        return (fr, f_fl)
      })"

definition verifier_after_trace_fri
  :: "'f \<times> ('f \<times> 'f) list \<Rightarrow>
      (unit list, ('f, 'a) protocol_channel_scheme) state_monad"
  where
    "verifier_after_trace_fri header =
      (case header of (fr, f_fl) \<Rightarrow>
        do {
          f_final \<leftarrow> read;
          as \<leftarrow> mmap (replicate (length spec) alpha_round);
          dg \<leftarrow> read;
          assert (to_nat dg \<le> maxDegree);
          fl \<leftarrow> ntimes receive_composition_fri_commits
            (ceil_log (to_nat dg + 1));
          final \<leftarrow> read;
          ntimes (verifier_query_round_program fr f_fl f_final as fl final)
            rounds
        })"

definition verifier_composition_fri_prefix
  :: "('f \<times> ('f \<times> 'f) list \<times> 'f \<times> 'f list \<times>
        'f \<times> ('f \<times> 'f) list,
       ('f, 'a) protocol_channel_scheme) state_monad"
  where
    "verifier_composition_fri_prefix =
      (do {
        fr \<leftarrow> read;
        f_fl \<leftarrow> ntimes receive_trace_fri_commits (ceil_log clength);
        f_final \<leftarrow> read;
        as \<leftarrow> mmap (replicate (length spec) alpha_round);
        dg \<leftarrow> read;
        assert (to_nat dg \<le> maxDegree);
        fl \<leftarrow> ntimes receive_composition_fri_commits
          (ceil_log (to_nat dg + 1));
        return (fr, f_fl, f_final, as, dg, fl)
      })"

definition verifier_after_composition_fri
  :: "'f \<times> ('f \<times> 'f) list \<times> 'f \<times> 'f list \<times>
        'f \<times> ('f \<times> 'f) list \<Rightarrow>
      (unit list, ('f, 'a) protocol_channel_scheme) state_monad"
  where
    "verifier_after_composition_fri header =
      (case header of (fr, f_fl, f_final, as, dg, fl) \<Rightarrow>
        do {
          final \<leftarrow> read;
          ntimes (verifier_query_round_program fr f_fl f_final as fl final)
            rounds
        })"

definition verifier_after_alpha
  :: "'f \<times> ('f \<times> 'f) list \<times> 'f \<times> 'f list \<Rightarrow>
      (unit list, ('f, 'a) protocol_channel_scheme) state_monad"
  where
    "verifier_after_alpha header =
      (case header of (fr, f_fl, f_final, as) \<Rightarrow>
        do {
          dg \<leftarrow> read;
          assert (to_nat dg \<le> maxDegree);
          fl \<leftarrow> ntimes receive_composition_fri_commits
            (ceil_log (to_nat dg + 1));
          final \<leftarrow> read;
          ntimes (verifier_query_round_program fr f_fl f_final as fl final)
            rounds
        })"

lemma verify_monad_alpha_decomposition:
  "verify_monad = (verifier_alpha_prefix \<bind> verifier_after_alpha)"
  unfolding verify_monad_def verifier_alpha_prefix_def verifier_after_alpha_def
    alpha_round_def verifier_query_round_program_def
  by (simp add: Let_def sm_bind_assoc sm_bind_return_map split: prod.splits)

lemma verify_monad_trace_fri_decomposition:
  "verify_monad = (verifier_trace_fri_prefix \<bind> verifier_after_trace_fri)"
  unfolding verify_monad_def verifier_trace_fri_prefix_def
    verifier_after_trace_fri_def alpha_round_def verifier_query_round_program_def
  by (simp add: Let_def sm_bind_assoc sm_bind_return_map split: prod.splits)

lemma verify_monad_composition_fri_decomposition:
  "verify_monad =
    (verifier_composition_fri_prefix \<bind> verifier_after_composition_fri)"
  unfolding verify_monad_def verifier_composition_fri_prefix_def
    verifier_after_composition_fri_def alpha_round_def
    verifier_query_round_program_def
  by (simp add: Let_def sm_bind_assoc sm_bind_return_map split: prod.splits)

lemma alpha_round_outcome:
  assumes outcome: "Some (a, t) \<in> set_dist (execute alpha_round s)"
  shows
    "\<exists>rest.
      PTranscript s = a # rest \<and>
      PState t = concat (PState s) a \<and>
      PTranscript t = rest \<and>
      s \<le> t \<and>
      PTraceFriCounter t = PTraceFriCounter s \<and>
      PCompositionFriCounter t = PCompositionFriCounter s \<and>
      PAlphaCounter t = Suc (PAlphaCounter s) \<and>
      PQueryCounter t = PQueryCounter s \<and>
      fmlookup (HashMap t) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
proof -
  from outcome obtain a0 s0 a1 s1 s2 where
    rand: "Some (a0, s0) \<in> set_dist (execute receive_alpha_challenge s)"
    and read_a: "Some (a1, s1) \<in> set_dist (execute read s0)"
    and assert_a: "Some ((), s2) \<in> set_dist (execute (assert (a0 = a1)) s1)"
    and ret_a: "Some (a, t) \<in> set_dist (execute (return a1) s2)"
    unfolding alpha_round_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  have rand_res:
    "s \<le> s0 \<and>
     PState s0 = PState s \<and>
     PTranscript s0 = PTranscript s \<and>
     fmlookup (HashMap s0) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a0"
    using receive_alpha_challenge_outcome[OF rand] .
  have rand_counter:
    "PTraceFriCounter s0 = PTraceFriCounter s \<and>
     PCompositionFriCounter s0 = PCompositionFriCounter s \<and>
     PAlphaCounter s0 = Suc (PAlphaCounter s) \<and>
     PQueryCounter s0 = PQueryCounter s"
    using receive_alpha_challenge_counter_outcome[OF rand] by simp
  obtain rest where tr_s0: "PTranscript s0 = a1 # rest"
  proof -
    have "PTranscript s0 \<noteq> []"
      using read_a unfolding read_def protocol_read_def assert_def
      by (cases "PTranscript s0") (auto simp: throw_no_outcome elim!: set_dist_bindE)
    then obtain x xs where xs: "PTranscript s0 = x # xs"
      by (cases "PTranscript s0") auto
    have a1_x: "a1 = x"
      using read_nonempty_outcome[OF read_a xs] by simp
    show ?thesis
      using that xs a1_x by auto
  qed
  have read_res:
    "s1 = s0\<lparr>PState := concat (PState s0) a1, PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF read_a tr_s0] by simp
  have a_eq: "a0 = a1"
    using assert_a unfolding assert_def
    by (cases "a0 = a1") (auto simp: throw_no_outcome)
  have s2_eq: "s2 = s1"
    using assert_a a_eq unfolding assert_def by simp
  have t_eq: "t = s1" and a_ret: "a = a1"
    using ret_a s2_eq by simp_all
  have lookup_t: "fmlookup (HashMap t) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using rand_res read_res t_eq a_ret a_eq
    unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have ext: "s \<le> t"
    using rand_res read_res t_eq a_ret a_eq
    unfolding less_eq_hash_ext_def less_eq_fmap_def by auto
  show ?thesis
    using rand_res rand_counter tr_s0 read_res t_eq a_ret a_eq lookup_t ext
    by auto
qed

lemma alpha_round_preserves_alpha_future_fresh:
  assumes future: "alpha_future_fresh s"
    and outcome: "Some (a, t) \<in> set_dist (execute alpha_round s)"
  shows "alpha_future_fresh t"
proof -
  from outcome obtain a0 s0 a1 s1 s2 where
    rand: "Some (a0, s0) \<in> set_dist (execute receive_alpha_challenge s)"
    and read_a: "Some (a1, s1) \<in> set_dist (execute read s0)"
    and assert_a: "Some ((), s2) \<in> set_dist (execute (assert (a0 = a1)) s1)"
    and ret_a: "Some (a, t) \<in> set_dist (execute (return a1) s2)"
    unfolding alpha_round_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  have counter_t: "PAlphaCounter t = Suc (PAlphaCounter s)"
    using alpha_round_outcome[OF outcome] by blast
  have future_s0:
    "\<And>i x. Suc (PAlphaCounter s) \<le> i \<Longrightarrow>
      fmlookup (HashMap s0) (AlphaChallenge i x) = None"
  proof -
    fix i x
    assume i_ge: "Suc (PAlphaCounter s) \<le> i"
    have neq:
      "AlphaChallenge i x \<noteq>
        AlphaChallenge (PAlphaCounter s) (PState s)"
      using i_ge by auto
    have "fmlookup (HashMap s0) (AlphaChallenge i x) =
        fmlookup (HashMap s) (AlphaChallenge i x)"
      by (rule receive_alpha_challenge_preserves_other_lookup[OF rand neq])
    also have "... = None"
      using future i_ge unfolding alpha_future_fresh_def by auto
    finally show
      "fmlookup (HashMap s0) (AlphaChallenge i x) = None" .
  qed
  have hash_s1: "HashMap s1 = HashMap s0"
    by (rule read_preserves_hash_map[OF read_a])
  have s2_eq: "s2 = s1"
    using assert_a unfolding assert_def
    by (cases "a0 = a1") (auto simp: throw_no_outcome)
  have t_eq: "t = s2"
    using ret_a by simp
  show ?thesis
    unfolding alpha_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume "PAlphaCounter t \<le> i"
    then have "Suc (PAlphaCounter s) \<le> i"
      using counter_t by simp
    then show "fmlookup (HashMap t) (AlphaChallenge i x) = None"
      using future_s0[of i x] hash_s1 unfolding t_eq s2_eq by simp
  qed
qed

lemma alpha_round_preserves_composition_fri_future_fresh:
  assumes future: "composition_fri_future_fresh s"
    and outcome: "Some (a, t) \<in> set_dist (execute alpha_round s)"
  shows "composition_fri_future_fresh t"
proof -
  from outcome obtain a0 s0 a1 s1 s2 where
    rand: "Some (a0, s0) \<in> set_dist (execute receive_alpha_challenge s)"
    and read_a: "Some (a1, s1) \<in> set_dist (execute read s0)"
    and assert_a: "Some ((), s2) \<in> set_dist (execute (assert (a0 = a1)) s1)"
    and ret_a: "Some (a, t) \<in> set_dist (execute (return a1) s2)"
    unfolding alpha_round_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  have counter_s0:
    "PCompositionFriCounter s0 = PCompositionFriCounter s"
    using receive_alpha_challenge_counter_outcome[OF rand] by simp
  have future_s0:
    "composition_fri_future_fresh s0"
    unfolding composition_fri_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge_s0: "PCompositionFriCounter s0 \<le> i"
    have i_ge_s: "PCompositionFriCounter s \<le> i"
      using i_ge_s0 counter_s0 by simp
    have neq:
      "CompositionFriChallenge i x \<noteq>
        AlphaChallenge (PAlphaCounter s) (PState s)"
      by simp
    have "fmlookup (HashMap s0) (CompositionFriChallenge i x) =
        fmlookup (HashMap s) (CompositionFriChallenge i x)"
      by (rule receive_alpha_challenge_preserves_other_lookup[OF rand neq])
    also have "... = None"
      using future i_ge_s
      unfolding composition_fri_future_fresh_def by blast
    finally show
      "fmlookup (HashMap s0) (CompositionFriChallenge i x) = None" .
  qed
  have future_s1:
    "composition_fri_future_fresh s1"
    by (rule read_preserves_composition_fri_future_fresh
        [OF future_s0 read_a])
  have s2_eq: "s2 = s1"
    using assert_a unfolding assert_def
    by (cases "a0 = a1") (auto simp: throw_no_outcome)
  have t_eq: "t = s2"
    using ret_a by simp
  show ?thesis
    using future_s1 unfolding t_eq s2_eq .
qed

lemma alpha_round_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome: "Some (a, t) \<in> set_dist (execute alpha_round s)"
  shows "query_future_fresh t"
proof -
  from outcome obtain a0 s0 a1 s1 s2 where
    rand: "Some (a0, s0) \<in> set_dist (execute receive_alpha_challenge s)"
    and read_a: "Some (a1, s1) \<in> set_dist (execute read s0)"
    and assert_a: "Some ((), s2) \<in> set_dist (execute (assert (a0 = a1)) s1)"
    and ret_a: "Some (a, t) \<in> set_dist (execute (return a1) s2)"
    unfolding alpha_round_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  have counter_s0:
    "PQueryCounter s0 = PQueryCounter s"
    using receive_alpha_challenge_counter_outcome[OF rand] by simp
  have future_s0:
    "query_future_fresh s0"
    unfolding query_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge_s0: "PQueryCounter s0 \<le> i"
    have i_ge_s: "PQueryCounter s \<le> i"
      using i_ge_s0 counter_s0 by simp
    have neq:
      "QueryIndexChallenge i x \<noteq>
        AlphaChallenge (PAlphaCounter s) (PState s)"
      by simp
    have "fmlookup (HashMap s0) (QueryIndexChallenge i x) =
        fmlookup (HashMap s) (QueryIndexChallenge i x)"
      by (rule receive_alpha_challenge_preserves_other_lookup[OF rand neq])
    also have "... = None"
      using future i_ge_s
      unfolding query_future_fresh_def by blast
    finally show
      "fmlookup (HashMap s0) (QueryIndexChallenge i x) = None" .
  qed
  have future_s1:
    "query_future_fresh s1"
    by (rule read_preserves_query_future_fresh[OF future_s0 read_a])
  have s2_eq: "s2 = s1"
    using assert_a unfolding assert_def
    by (cases "a0 = a1") (auto simp: throw_no_outcome)
  have t_eq: "t = s2"
    using ret_a by simp
  show ?thesis
    using future_s1 unfolding t_eq s2_eq .
qed

lemma wp_alpha_round_fresh_set:
  assumes future: "alpha_future_fresh s"
  shows
    "wp_event alpha_round
      (\<lambda>out. case out of None \<Rightarrow> False | Some (a, _) \<Rightarrow> a \<in> B) s
      \<le> nnreal (card B) / nnreal size"
proof -
  let ?P = "\<lambda>out. case out of None \<Rightarrow> False | Some (a, _) \<Rightarrow> a \<in> B"
  let ?k =
    "\<lambda>a0. read \<bind> (\<lambda>a1.
      assert (a0 = a1) \<bind> (\<lambda>_. return a1))"
  have head_bound:
    "wp_event receive_alpha_challenge ?P s \<le>
      nnreal (card B) / nnreal size"
    using wp_receive_alpha_challenge_fresh_set
      [OF alpha_future_fresh_current[OF future], of B]
    by simp
  have round_eq: "alpha_round = (receive_alpha_challenge \<bind> ?k)"
    unfolding alpha_round_def by (simp add: Let_def)
  show ?thesis
    unfolding round_eq
  proof (rule wp_event_bind_bound_by_head_event[OF head_bound])
    show "?P None \<Longrightarrow> ?P None"
      by simp
  next
    fix a0 s0 out
    assume cont: "out \<in> set_dist (execute (?k a0) s0)"
      and hit: "?P out"
    show "?P (Some (a0, s0))"
    proof (cases out)
      case None
      then show ?thesis
        using hit by simp
    next
      case (Some pair)
      obtain a t where pair_eq: "pair = (a, t)"
        by (cases pair)
      from cont[unfolded Some pair_eq]
      obtain a1 s1 s2 where
        read_a: "Some (a1, s1) \<in> set_dist (execute read s0)"
        and assert_a:
          "Some ((), s2) \<in> set_dist (execute (assert (a0 = a1)) s1)"
        and ret_a: "Some (a, t) \<in> set_dist (execute (return a1) s2)"
        by (auto elim!: set_dist_bindE)
      have a0_eq: "a0 = a1"
        using assert_a unfolding assert_def
        by (cases "a0 = a1") (auto simp: throw_no_outcome)
      have a_eq: "a = a1"
        using ret_a by simp
      have "a \<in> B"
        using hit Some pair_eq by simp
      then show ?thesis
        using a0_eq a_eq by simp
    qed
  qed
qed

lemma wp_alpha_round_success_bound:
  assumes future: "alpha_future_fresh s"
  shows
    "wp_event alpha_round
      (\<lambda>out. case out of None \<Rightarrow> False | Some _ \<Rightarrow> True) s
      \<le> 1 / nnreal size"
proof (cases "PTranscript s")
  case Nil
  have no_success:
    "\<And>out. out \<in> set_dist (execute alpha_round s) \<Longrightarrow>
      (case out of None \<Rightarrow> False | Some _ \<Rightarrow> True) \<Longrightarrow> False"
  proof -
    fix out
    assume out: "out \<in> set_dist (execute alpha_round s)"
      and success: "(case out of None \<Rightarrow> False | Some _ \<Rightarrow> True)"
    from success obtain a t where out_eq: "out = Some (a, t)"
      by (cases out) auto
    from alpha_round_outcome[OF out[unfolded out_eq]]
    obtain rest where "PTranscript s = a # rest"
      by blast
    then show False
      using Nil by simp
  qed
  have "wp_event alpha_round
      (\<lambda>out. case out of None \<Rightarrow> False | Some _ \<Rightarrow> True) s
      \<le> wp_event alpha_round
        (\<lambda>_ :: ('f \<times> ('f, 'a) protocol_channel_scheme) option. False) s"
    by (rule wp_event_mono_on_support) (rule no_success)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  also have "... \<le> 1 / nnreal size"
    by simp
  finally show ?thesis .
next
  case (Cons x rest)
  let ?Q = "\<lambda>out. case out of None \<Rightarrow> False | Some _ \<Rightarrow> True"
  let ?P = "\<lambda>out. case out of None \<Rightarrow> False | Some (a, _) \<Rightarrow> a \<in> {x}"
  let ?k =
    "\<lambda>a0. read \<bind> (\<lambda>a1.
      assert (a0 = a1) \<bind> (\<lambda>_. return a1))"
  have head_bound:
    "wp_event receive_alpha_challenge ?P s \<le> 1 / nnreal size"
  proof -
    have "wp_event receive_alpha_challenge ?P s =
        nnreal (card ({x} :: 'f set)) / nnreal size"
      using wp_receive_alpha_challenge_fresh_set
        [OF alpha_future_fresh_current[OF future], of "{x}"]
      by simp
    then show ?thesis
      by simp
  qed
  have round_eq: "alpha_round = (receive_alpha_challenge \<bind> ?k)"
    unfolding alpha_round_def by (simp add: Let_def)
  show ?thesis
    unfolding round_eq
  proof (rule wp_event_bind_bound_by_head_event[OF head_bound])
    show "?Q None \<Longrightarrow> ?P None"
      by simp
  next
    fix a0 s0 out
    assume rand:
        "Some (a0, s0) \<in> set_dist (execute receive_alpha_challenge s)"
      and cont: "out \<in> set_dist (execute (?k a0) s0)"
      and success: "?Q out"
    from success obtain a t where out_eq: "out = Some (a, t)"
      by (cases out) auto
    from cont[unfolded out_eq]
    obtain a1 s1 s2 where
      read_a: "Some (a1, s1) \<in> set_dist (execute read s0)"
      and assert_a:
        "Some ((), s2) \<in> set_dist (execute (assert (a0 = a1)) s1)"
      and ret_a: "Some (a, t) \<in> set_dist (execute (return a1) s2)"
      by (auto elim!: set_dist_bindE)
    have tr_s0: "PTranscript s0 = x # rest"
      using receive_alpha_challenge_outcome[OF rand] Cons by simp
    have a1_eq: "a1 = x"
      using read_nonempty_outcome[OF read_a tr_s0] by simp
    have a0_eq: "a0 = a1"
      using assert_a unfolding assert_def
      by (cases "a0 = a1") (auto simp: throw_no_outcome)
    show "?P (Some (a0, s0))"
      using a0_eq a1_eq by simp
  qed
qed

lemma mmap_alpha_round_outcome:
  assumes outcome:
    "Some (as, t) \<in> set_dist (execute (mmap (replicate n alpha_round)) s)"
  shows
    "length as = n \<and>
     PTranscript s = as @ PTranscript t \<and>
     PState t = foldl concat (PState s) as \<and>
     s \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s + n \<and>
     PQueryCounter t = PQueryCounter s \<and>
     (\<forall>i < n.
        fmlookup (HashMap t)
          (AlphaChallenge (PAlphaCounter s + i)
            (foldl concat (PState s) (take i as))) =
        Some (as ! i))"
  using outcome
proof (induction n arbitrary: s as t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain a as' s1 where
    head: "Some (a, s1) \<in> set_dist (execute alpha_round s)"
    and tail:
      "Some (as', t) \<in> set_dist (execute (mmap (replicate n alpha_round)) s1)"
    and as_eq: "as = a # as'"
    by (auto elim!: set_dist_bindE)
  from alpha_round_outcome[OF head] obtain rest1 where
    tr_s: "PTranscript s = a # rest1"
    and st_s1: "PState s1 = concat (PState s) a"
    and tr_s1: "PTranscript s1 = rest1"
    and ext_head: "s \<le> s1"
    and trace_count_s1: "PTraceFriCounter s1 = PTraceFriCounter s"
    and comp_count_s1: "PCompositionFriCounter s1 = PCompositionFriCounter s"
    and alpha_count_s1: "PAlphaCounter s1 = Suc (PAlphaCounter s)"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    and lookup_head: "fmlookup (HashMap s1) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    by blast
  have tail_res:
    "length as' = n \<and>
     PTranscript s1 = as' @ PTranscript t \<and>
     PState t = foldl concat (PState s1) as' \<and>
     s1 \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s1 \<and>
     PCompositionFriCounter t = PCompositionFriCounter s1 \<and>
     PAlphaCounter t = PAlphaCounter s1 + n \<and>
     PQueryCounter t = PQueryCounter s1 \<and>
     (\<forall>i<n.
        fmlookup (HashMap t)
          (AlphaChallenge (PAlphaCounter s1 + i)
            (foldl concat (PState s1) (take i as'))) =
        Some (as' ! i))"
    using Suc.IH[OF tail] .
  have ext_s1_t: "s1 \<le> t"
    using tail_res by simp
  have lookup_head_t:
    "fmlookup (HashMap t) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using hash_extension_lookup[OF lookup_head ext_s1_t] .
  have ext_combined: "s \<le> t"
    using ext_head ext_s1_t by (meson hash_ext_trans)
  have counters_t:
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s + Suc n \<and>
     PQueryCounter t = PQueryCounter s"
    using tail_res trace_count_s1 comp_count_s1 alpha_count_s1 query_count_s1
    by simp
  have lookups:
    "\<forall>i < Suc n.
      fmlookup (HashMap t)
        (AlphaChallenge (PAlphaCounter s + i)
          (foldl concat (PState s) (take i as))) =
      Some (as ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < Suc n"
    show "fmlookup (HashMap t)
        (AlphaChallenge (PAlphaCounter s + i)
          (foldl concat (PState s) (take i as))) =
      Some (as ! i)"
    proof (cases i)
      case 0
      then show ?thesis
        using lookup_head_t as_eq by simp
    next
      case (Suc j)
      then have j_bound: "j < n"
        using i_bound by simp
      have key_eq:
        "foldl concat (PState s) (take i as) =
          foldl concat (PState s1) (take j as')"
        using Suc as_eq st_s1 by simp
      show ?thesis
        using tail_res j_bound Suc as_eq key_eq alpha_count_s1 by simp
    qed
  qed
  show ?case
    using tail_res tr_s tr_s1 st_s1 ext_combined lookups as_eq
      counters_t
    by simp
qed

lemma mmap_alpha_round_preserves_alpha_future_fresh:
  assumes future: "alpha_future_fresh s"
    and outcome:
      "Some (as, t) \<in>
        set_dist (execute (mmap (replicate n alpha_round)) s)"
  shows "alpha_future_fresh t"
  using outcome future
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
  have future_s1: "alpha_future_fresh s1"
    by (rule alpha_round_preserves_alpha_future_fresh[OF Suc.prems(2) head])
  show ?case
    by (rule Suc.IH[OF tail future_s1])
qed

lemma mmap_alpha_round_preserves_composition_fri_future_fresh:
  assumes future: "composition_fri_future_fresh s"
    and outcome:
      "Some (as, t) \<in>
        set_dist (execute (mmap (replicate n alpha_round)) s)"
  shows "composition_fri_future_fresh t"
  using outcome future
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
  have future_s1: "composition_fri_future_fresh s1"
    by (rule alpha_round_preserves_composition_fri_future_fresh
        [OF Suc.prems(2) head])
  show ?case
    by (rule Suc.IH[OF tail future_s1])
qed

lemma mmap_alpha_round_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some (as, t) \<in>
        set_dist (execute (mmap (replicate n alpha_round)) s)"
  shows "query_future_fresh t"
  using outcome future
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
  have future_s1: "query_future_fresh s1"
    by (rule alpha_round_preserves_query_future_fresh
        [OF Suc.prems(2) head])
  show ?case
    by (rule Suc.IH[OF tail future_s1])
qed

lemma wp_mmap_alpha_round_success_bound:
  assumes future: "alpha_future_fresh s"
  shows
    "wp_event (mmap (replicate n alpha_round))
      (\<lambda>out. case out of None \<Rightarrow> False | Some _ \<Rightarrow> True) s
      \<le> (1 / nnreal size) ^ n"
  using future
proof (induction n arbitrary: s)
  case 0
  then show ?case
    by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  let ?ListSuccess =
    "\<lambda>out :: ('f list \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of None \<Rightarrow> False | Some _ \<Rightarrow> True"
  let ?HeadSuccess =
    "\<lambda>out :: ('f \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of None \<Rightarrow> False | Some _ \<Rightarrow> True"
  let ?tail =
    "(mmap (replicate n alpha_round) ::
      ('f list, ('f, 'a) protocol_channel_scheme) state_monad)"
  let ?D = "(1 / nnreal size) ^ n"
  have bind_bound:
    "wp_event
      (alpha_round \<bind>
        (\<lambda>a :: 'f. ?tail \<bind> (\<lambda>as :: 'f list. return (a # as))))
      ?ListSuccess s
      \<le> wp_event alpha_round ?HeadSuccess s * ?D"
  proof (rule wp_event_bind_bound_by_head_and_cont
      [where P = ?HeadSuccess])
    show "\<not> ?ListSuccess None"
      by simp
  next
    fix a t
    assume "\<not> ?HeadSuccess (Some (a, t))"
    then show
      "wp_event (?tail \<bind> (\<lambda>as :: 'f list. return (a # as)))
        ?ListSuccess t = 0"
      by simp
  next
    fix a t
    assume head: "Some (a, t) \<in> set_dist (execute alpha_round s)"
    have future_t: "alpha_future_fresh t"
      by (rule alpha_round_preserves_alpha_future_fresh[OF Suc.prems head])
    have tail_bound: "wp_event ?tail ?ListSuccess t \<le> ?D"
      by (rule Suc.IH[OF future_t])
    have cont_eq:
      "(\<lambda>out. case out of
          None \<Rightarrow> (0 :: prob)
        | Some (as, u) \<Rightarrow>
            wp (return (a # as))
              (\<lambda>out. if ?ListSuccess out then 1 else 0) u) =
       (\<lambda>out. if ?ListSuccess out then 1 else 0)"
      by (rule ext) (auto simp: wpsimps split: option.splits prod.splits)
    have "wp_event (?tail \<bind> (\<lambda>as :: 'f list. return (a # as)))
        ?ListSuccess t =
        wp_event ?tail ?ListSuccess t"
      unfolding wp_event_def
      by (simp add: wpsimps cont_eq)
    also have "... \<le> ?D"
      by (rule tail_bound)
    finally show
      "wp_event (?tail \<bind> (\<lambda>as :: 'f list. return (a # as)))
        ?ListSuccess t \<le> ?D" .
  qed
  have "wp_event (mmap (replicate (Suc n) alpha_round)) ?ListSuccess s
      \<le> wp_event alpha_round ?HeadSuccess s * ?D"
    using bind_bound by simp
  also have "... \<le> (1 / nnreal size) * ?D"
    by (rule mult_right_mono[OF wp_alpha_round_success_bound[OF Suc.prems]])
      simp
  also have "... = (1 / nnreal size) ^ Suc n"
    by simp
  finally show ?case .
qed

lemma wp_mmap_alpha_round_finite_set_bound:
  assumes future: "alpha_future_fresh s"
    and finite_B: "finite B"
  shows
    "wp_event (mmap (replicate n alpha_round))
      (\<lambda>out. case out of None \<Rightarrow> False | Some (as, _) \<Rightarrow> as \<in> B) s
      \<le> nnreal (card B) / (nnreal size) ^ n"
proof (cases "B = {}")
  case True
  have "wp_event (mmap (replicate n alpha_round))
      (\<lambda>out. case out of None \<Rightarrow> False | Some (as, _) \<Rightarrow> as \<in> B) s
      \<le> wp_event (mmap (replicate n alpha_round))
        (\<lambda>_ :: ('f list \<times> ('f, 'a) protocol_channel_scheme) option. False) s"
    unfolding True
    by (rule wp_event_mono) (auto split: option.splits prod.splits)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis
    unfolding True by simp
next
  case False
  have card_pos: "0 < card B"
    using finite_B False by (simp add: card_gt_0_iff)
  have event_success:
    "wp_event (mmap (replicate n alpha_round))
      (\<lambda>out. case out of None \<Rightarrow> False | Some (as, _) \<Rightarrow> as \<in> B) s
      \<le> wp_event (mmap (replicate n alpha_round))
        (\<lambda>out. case out of None \<Rightarrow> False | Some _ \<Rightarrow> True) s"
    by (rule wp_event_mono) (auto split: option.splits prod.splits)
  also have "... \<le> (1 / nnreal size) ^ n"
    by (rule wp_mmap_alpha_round_success_bound[OF future])
  also have "... = 1 / (nnreal size) ^ n"
    using size_card by transfer (simp add: power_divide)
  also have "... = nnreal (1::nat) / nnreal (size ^ n)"
    by simp
  also have "... \<le> nnreal (card B) / nnreal (size ^ n)"
    by (rule nnreal_nat_divide_right_mono) (use card_pos in simp)
  also have "... \<le> nnreal (card B) / (nnreal size) ^ n"
    by simp
  finally show ?thesis .
qed

lemma wp_mmap_alpha_round_alpha_space_set_bound:
  assumes future: "alpha_future_fresh s"
    and subset: "B \<subseteq> alpha_space"
  shows
    "wp_event (mmap (replicate (length spec) alpha_round))
      (\<lambda>out. case out of None \<Rightarrow> False | Some (as, _) \<Rightarrow> as \<in> B) s
      \<le> nnreal (card B) / nnreal (card alpha_space)"
proof -
  have finite_B: "finite B"
    by (rule finite_subset[OF subset finite_alpha_space])
  have "wp_event (mmap (replicate (length spec) alpha_round))
      (\<lambda>out. case out of None \<Rightarrow> False | Some (as, _) \<Rightarrow> as \<in> B) s
      \<le> nnreal (card B) / (nnreal size) ^ length spec"
    by (rule wp_mmap_alpha_round_finite_set_bound[OF future finite_B])
  also have "... = nnreal (card B) / nnreal (card alpha_space)"
    using size_card by simp
  finally show ?thesis .
qed

lemma receive_fri_commits_with_outcome:
  assumes receiver_outcome:
    "\<And>b s_read t.
      Some (b, t) \<in> set_dist (execute receive_challenge s_read) \<Longrightarrow>
      s_read \<le> t \<and>
      PState t = PState s_read \<and>
      PTranscript t = PTranscript s_read \<and>
      fmlookup (HashMap t) (tag (PState s_read)) = Some b"
    and outcome:
      "Some ((b, r), t) \<in>
        set_dist (execute (receive_fri_commits_with receive_challenge) s)"
  shows
    "\<exists>rest.
      PTranscript s = r # rest \<and>
      PState t = concat (PState s) r \<and>
      PTranscript t = rest \<and>
      s \<le> t \<and>
      fmlookup (HashMap t) (tag (concat (PState s) r)) = Some b"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in> set_dist (execute receive_challenge s_read)"
    unfolding receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  obtain rest where tr_s: "PTranscript s = r # rest"
  proof -
    have "PTranscript s \<noteq> []"
      using read_r unfolding read_def protocol_read_def assert_def
      by (cases "PTranscript s") (auto simp: throw_no_outcome elim!: set_dist_bindE)
    then obtain x xs where xs: "PTranscript s = x # xs"
      by (cases "PTranscript s") auto
    have r_x: "r = x"
      using read_nonempty_outcome[OF read_r xs] by simp
    show ?thesis
      using that xs r_x by auto
  qed
  have read_res:
    "r = r \<and>
     s_read = s\<lparr>PState := concat (PState s) r, PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF read_r tr_s] by simp
  have rand_res:
    "s_read \<le> t \<and>
     PState t = PState s_read \<and>
     PTranscript t = PTranscript s_read \<and>
     fmlookup (HashMap t) (tag (PState s_read)) = Some b"
    using receiver_outcome[OF rand_b] .
  have s_read_ext: "s \<le> s_read"
    using read_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s_t: "s \<le> t"
    using s_read_ext rand_res by (meson hash_ext_trans)
  show ?thesis
    using tr_s read_res rand_res s_t by auto
qed

lemma receive_trace_fri_commits_outcome:
  assumes outcome:
    "Some ((b, r), t) \<in>
      set_dist (execute receive_trace_fri_commits s)"
  shows
    "\<exists>rest.
      PTranscript s = r # rest \<and>
      PState t = concat (PState s) r \<and>
      PTranscript t = rest \<and>
      s \<le> t \<and>
      PTraceFriCounter t = Suc (PTraceFriCounter s) \<and>
      PCompositionFriCounter t = PCompositionFriCounter s \<and>
      PAlphaCounter t = PAlphaCounter s \<and>
      PQueryCounter t = PQueryCounter s \<and>
      fmlookup (HashMap t)
        (TraceFriChallenge (PTraceFriCounter s) (concat (PState s) r)) =
        Some b"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s_read)"
    unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  obtain rest where tr_s: "PTranscript s = r # rest"
  proof -
    have "PTranscript s \<noteq> []"
      using read_r unfolding read_def protocol_read_def assert_def
      by (cases "PTranscript s") (auto simp: throw_no_outcome elim!: set_dist_bindE)
    then obtain x xs where xs: "PTranscript s = x # xs"
      by (cases "PTranscript s") auto
    have r_x: "r = x"
      using read_nonempty_outcome[OF read_r xs] by simp
    show ?thesis
      using that xs r_x by auto
  qed
  have read_res:
    "s_read = s\<lparr>PState := concat (PState s) r, PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF read_r tr_s] by simp
  have rand_res:
    "s_read \<le> t \<and>
     PState t = PState s_read \<and>
     PTranscript t = PTranscript s_read \<and>
     fmlookup (HashMap t)
       (TraceFriChallenge (PTraceFriCounter s_read) (PState s_read)) =
      Some b"
    using receive_trace_fri_challenge_outcome[OF rand_b] .
  have rand_counter:
    "PTraceFriCounter t = Suc (PTraceFriCounter s_read) \<and>
     PCompositionFriCounter t = PCompositionFriCounter s_read \<and>
     PAlphaCounter t = PAlphaCounter s_read \<and>
     PQueryCounter t = PQueryCounter s_read"
    using receive_trace_fri_challenge_counter_outcome[OF rand_b] by simp
  have s_read_ext: "s \<le> s_read"
    using read_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s_t: "s \<le> t"
    using s_read_ext rand_res by (meson hash_ext_trans)
  show ?thesis
    using tr_s read_res rand_res rand_counter s_t by auto
qed

lemma receive_trace_fri_commits_preserves_trace_fri_future_fresh:
  assumes future: "trace_fri_future_fresh s"
    and outcome:
      "Some ((b, r), t) \<in>
        set_dist (execute receive_trace_fri_commits s)"
  shows "trace_fri_future_fresh t"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s_read)"
    unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_r] have read_counts:
    "PTraceFriCounter s_read = PTraceFriCounter s"
    by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have counter_t:
    "PTraceFriCounter t = Suc (PTraceFriCounter s)"
    using receive_trace_fri_challenge_counter_outcome[OF rand_b] read_counts
    by simp
  show ?thesis
    unfolding trace_fri_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge_t: "PTraceFriCounter t \<le> i"
    have i_ge_s: "PTraceFriCounter s \<le> i"
      using i_ge_t counter_t by simp
    have neq:
      "TraceFriChallenge i x \<noteq>
        TraceFriChallenge (PTraceFriCounter s_read) (PState s_read)"
      using i_ge_t counter_t read_counts by auto
    have "fmlookup (HashMap t) (TraceFriChallenge i x) =
        fmlookup (HashMap s_read) (TraceFriChallenge i x)"
      by (rule receive_trace_fri_challenge_preserves_other_lookup
          [OF rand_b neq])
    also have "... = fmlookup (HashMap s) (TraceFriChallenge i x)"
      using read_hash by simp
    also have "... = None"
      using future i_ge_s unfolding trace_fri_future_fresh_def by blast
    finally show "fmlookup (HashMap t) (TraceFriChallenge i x) = None" .
  qed
qed

lemma receive_trace_fri_commits_preserves_alpha_future_fresh:
  assumes future: "alpha_future_fresh s"
    and outcome:
      "Some ((b, r), t) \<in>
        set_dist (execute receive_trace_fri_commits s)"
  shows "alpha_future_fresh t"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s_read)"
    unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_r] have read_counts:
    "PAlphaCounter s_read = PAlphaCounter s"
    by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have counter_t:
    "PAlphaCounter t = PAlphaCounter s"
    using receive_trace_fri_challenge_counter_outcome[OF rand_b]
      read_counts
    by simp
  show ?thesis
    unfolding alpha_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge_t: "PAlphaCounter t \<le> i"
    have i_ge_s: "PAlphaCounter s \<le> i"
      using i_ge_t counter_t by simp
    have neq:
      "AlphaChallenge i x \<noteq>
        TraceFriChallenge (PTraceFriCounter s_read) (PState s_read)"
      by simp
    have "fmlookup (HashMap t) (AlphaChallenge i x) =
        fmlookup (HashMap s_read) (AlphaChallenge i x)"
      by (rule receive_trace_fri_challenge_preserves_other_lookup
          [OF rand_b neq])
    also have "... = fmlookup (HashMap s) (AlphaChallenge i x)"
      using read_hash by simp
    also have "... = None"
      using future i_ge_s unfolding alpha_future_fresh_def by blast
    finally show "fmlookup (HashMap t) (AlphaChallenge i x) = None" .
  qed
qed

lemma receive_trace_fri_commits_preserves_composition_fri_future_fresh:
  assumes future: "composition_fri_future_fresh s"
    and outcome:
      "Some ((b, r), t) \<in>
        set_dist (execute receive_trace_fri_commits s)"
  shows "composition_fri_future_fresh t"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s_read)"
    unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_r] have read_counts:
    "PCompositionFriCounter s_read = PCompositionFriCounter s"
    by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have counter_t:
    "PCompositionFriCounter t = PCompositionFriCounter s"
    using receive_trace_fri_challenge_counter_outcome[OF rand_b]
      read_counts
    by simp
  show ?thesis
    unfolding composition_fri_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge_t: "PCompositionFriCounter t \<le> i"
    have i_ge_s: "PCompositionFriCounter s \<le> i"
      using i_ge_t counter_t by simp
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
    also have "... = None"
      using future i_ge_s
      unfolding composition_fri_future_fresh_def by blast
    finally show
      "fmlookup (HashMap t) (CompositionFriChallenge i x) = None" .
  qed
qed

lemma receive_trace_fri_commits_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some ((b, r), t) \<in>
        set_dist (execute receive_trace_fri_commits s)"
  shows "query_future_fresh t"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s_read)"
    unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_r] have read_counts:
    "PQueryCounter s_read = PQueryCounter s"
    by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have counter_t:
    "PQueryCounter t = PQueryCounter s"
    using receive_trace_fri_challenge_counter_outcome[OF rand_b]
      read_counts
    by simp
  show ?thesis
    unfolding query_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge_t: "PQueryCounter t \<le> i"
    have i_ge_s: "PQueryCounter s \<le> i"
      using i_ge_t counter_t by simp
    have neq:
      "QueryIndexChallenge i x \<noteq>
        TraceFriChallenge (PTraceFriCounter s_read) (PState s_read)"
      by simp
    have "fmlookup (HashMap t) (QueryIndexChallenge i x) =
        fmlookup (HashMap s_read) (QueryIndexChallenge i x)"
      by (rule receive_trace_fri_challenge_preserves_other_lookup
          [OF rand_b neq])
    also have "... = fmlookup (HashMap s) (QueryIndexChallenge i x)"
      using read_hash by simp
    also have "... = None"
      using future i_ge_s unfolding query_future_fresh_def by blast
    finally show "fmlookup (HashMap t) (QueryIndexChallenge i x) = None" .
  qed
qed

lemma wp_receive_trace_fri_commits_fresh_set:
  assumes future: "trace_fri_future_fresh s"
  shows
    "wp_event receive_trace_fri_commits
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((b, r), _) \<Rightarrow> b \<in> B) s
      \<le> nnreal (card B) / nnreal size"
  unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> (case None of
      None \<Rightarrow> False | Some ((b, r), _) \<Rightarrow> b \<in> B)"
    by simp
next
  fix r s_read
  assume read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
  have read_counts:
    "PTraceFriCounter s_read = PTraceFriCounter s"
    using read_outcome[OF read_r] by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have fresh:
    "fmlookup (HashMap s_read)
      (TraceFriChallenge (PTraceFriCounter s_read) (PState s_read)) = None"
    using future read_counts read_hash
    unfolding trace_fri_future_fresh_def by simp
  let ?Q =
    "\<lambda>out :: (('f \<times> 'f) \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of None \<Rightarrow> False | Some ((b, r), _) \<Rightarrow> b \<in> B"
  have cont_eq:
    "(\<lambda>out. case out of
        None \<Rightarrow> (0 :: prob)
      | Some (b, u) \<Rightarrow>
          wp (return (b, r)) (\<lambda>out. if ?Q out then 1 else 0) u) =
     (\<lambda>out :: ('f \<times> ('f, 'a) protocol_channel_scheme) option.
        if (case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B)
        then 1 else 0)"
    by (rule ext) (auto simp: wpsimps split: option.splits prod.splits)
  have "wp_event
      (receive_trace_fri_challenge \<bind> (\<lambda>b :: 'f. return (b, r)))
      ?Q s_read =
      wp_event receive_trace_fri_challenge
        (\<lambda>out. case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B)
        s_read"
    unfolding wp_event_def by (simp add: wpsimps cont_eq)
  also have "... = nnreal (card B) / nnreal size"
    by (rule wp_receive_trace_fri_challenge_fresh_set[OF fresh])
  finally show
    "wp_event
      (receive_trace_fri_challenge \<bind> (\<lambda>b :: 'f. return (b, r)))
      (\<lambda>out. case out of None \<Rightarrow> False | Some ((b, r), _) \<Rightarrow> b \<in> B)
      s_read
      \<le> nnreal (card B) / nnreal size"
    by simp
qed

lemma ntimes_receive_trace_fri_commits_preserves_trace_fri_future_fresh:
  assumes future: "trace_fri_future_fresh s"
    and outcome:
      "Some (brs, t) \<in>
        set_dist (execute (ntimes receive_trace_fri_commits n) s)"
  shows "trace_fri_future_fresh t"
  using outcome future
proof (induction n arbitrary: s brs t)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems obtain br brs' s1 where
    head:
      "Some (br, s1) \<in> set_dist (execute receive_trace_fri_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes receive_trace_fri_commits n) s1)"
    by (auto elim!: set_dist_bindE)
  obtain b r where br_eq: "br = (b, r)"
    by (cases br)
  have future_s1:
    "trace_fri_future_fresh s1"
    by (rule receive_trace_fri_commits_preserves_trace_fri_future_fresh
        [OF Suc.prems(2) head[unfolded br_eq]])
  show ?case
    by (rule Suc.IH[OF tail future_s1])
qed

lemma ntimes_receive_trace_fri_commits_preserves_alpha_future_fresh:
  assumes outcome:
      "Some (brs, t) \<in>
        set_dist (execute (ntimes receive_trace_fri_commits n) s)"
    and future: "alpha_future_fresh s"
  shows "alpha_future_fresh t"
  using outcome future
proof (induction n arbitrary: s brs t)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems(1) obtain br brs' s1 where
    head:
      "Some (br, s1) \<in> set_dist (execute receive_trace_fri_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes receive_trace_fri_commits n) s1)"
    by (auto elim!: set_dist_bindE)
  obtain b r where br_eq: "br = (b, r)"
    by (cases br)
  have future_s1:
    "alpha_future_fresh s1"
    by (rule receive_trace_fri_commits_preserves_alpha_future_fresh
        [OF Suc.prems(2) head[unfolded br_eq]])
  show ?case
    by (rule Suc.IH[OF tail future_s1])
qed

lemma ntimes_receive_trace_fri_commits_preserves_composition_fri_future_fresh:
  assumes outcome:
      "Some (brs, t) \<in>
        set_dist (execute (ntimes receive_trace_fri_commits n) s)"
    and future: "composition_fri_future_fresh s"
  shows "composition_fri_future_fresh t"
  using outcome future
proof (induction n arbitrary: s brs t)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems(1) obtain br brs' s1 where
    head:
      "Some (br, s1) \<in> set_dist (execute receive_trace_fri_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes receive_trace_fri_commits n) s1)"
    by (auto elim!: set_dist_bindE)
  obtain b r where br_eq: "br = (b, r)"
    by (cases br)
  have future_s1:
    "composition_fri_future_fresh s1"
    by (rule receive_trace_fri_commits_preserves_composition_fri_future_fresh
        [OF Suc.prems(2) head[unfolded br_eq]])
  show ?case
    by (rule Suc.IH[OF tail future_s1])
qed

lemma ntimes_receive_trace_fri_commits_preserves_query_future_fresh:
  assumes outcome:
      "Some (brs, t) \<in>
        set_dist (execute (ntimes receive_trace_fri_commits n) s)"
    and future: "query_future_fresh s"
  shows "query_future_fresh t"
  using outcome future
proof (induction n arbitrary: s brs t)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems(1) obtain br brs' s1 where
    head:
      "Some (br, s1) \<in> set_dist (execute receive_trace_fri_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes receive_trace_fri_commits n) s1)"
    by (auto elim!: set_dist_bindE)
  obtain b r where br_eq: "br = (b, r)"
    by (cases br)
  have future_s1:
    "query_future_fresh s1"
    by (rule receive_trace_fri_commits_preserves_query_future_fresh
        [OF Suc.prems(2) head[unfolded br_eq]])
  show ?case
    by (rule Suc.IH[OF tail future_s1])
qed

lemma verifier_alpha_prefix_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some (header, t) \<in> set_dist (execute verifier_alpha_prefix s)"
  shows "query_future_fresh t"
proof -
  from outcome obtain fr s1 f_fl s2 f_final s3 as where
    read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    and trace_fri:
      "Some (f_fl, s2) \<in>
        set_dist (execute (ntimes receive_trace_fri_commits (ceil_log clength)) s1)"
    and read_final: "Some (f_final, s3) \<in> set_dist (execute read s2)"
    and alpha:
      "Some (as, t) \<in>
        set_dist (execute (mmap (replicate (length spec) alpha_round)) s3)"
    unfolding verifier_alpha_prefix_def
    by (auto elim!: set_dist_bindE)
  have future_s1: "query_future_fresh s1"
    by (rule read_preserves_query_future_fresh[OF future read_fr])
  have future_s2: "query_future_fresh s2"
    by (rule ntimes_receive_trace_fri_commits_preserves_query_future_fresh
        [OF trace_fri future_s1])
  have future_s3: "query_future_fresh s3"
    by (rule read_preserves_query_future_fresh[OF future_s2 read_final])
  show ?thesis
    by (rule mmap_alpha_round_preserves_query_future_fresh
        [OF future_s3 alpha])
qed

lemma wp_verifier_alpha_prefix_alpha_space_set_bound:
  assumes future: "alpha_future_fresh s"
    and subset: "B \<subseteq> alpha_space"
  shows
    "wp_event verifier_alpha_prefix
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((_, _, _, as'), _) \<Rightarrow> as' \<in> B) s
      \<le> nnreal (card B) / nnreal (card alpha_space)"
proof -
  let ?Q =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((_, _, _, as'), _) \<Rightarrow> as' \<in> B"
  let ?C = "nnreal (card B) / nnreal (card alpha_space)"
  show ?thesis
    unfolding verifier_alpha_prefix_def
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?Q None"
      by simp
  next
    fix fr s1
    assume read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    have future_s1: "alpha_future_fresh s1"
      by (rule read_preserves_alpha_future_fresh[OF future read_fr])
    show "wp_event
        (ntimes receive_trace_fri_commits (ceil_log clength) \<bind>
          (\<lambda>f_fl. read \<bind>
            (\<lambda>f_final.
              mmap (replicate (length spec) alpha_round) \<bind>
                (\<lambda>as. return (fr, f_fl, f_final, as)))))
        ?Q s1 \<le> ?C"
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?Q None"
        by simp
    next
      fix f_fl s2
      assume trace_fri:
        "Some (f_fl, s2) \<in>
          set_dist
            (execute (ntimes receive_trace_fri_commits (ceil_log clength)) s1)"
      have future_s2: "alpha_future_fresh s2"
        by (rule ntimes_receive_trace_fri_commits_preserves_alpha_future_fresh
            [OF trace_fri future_s1])
      show "wp_event
          (read \<bind>
            (\<lambda>f_final.
              mmap (replicate (length spec) alpha_round) \<bind>
                (\<lambda>as. return (fr, f_fl, f_final, as))))
          ?Q s2 \<le> ?C"
      proof (rule wp_event_bind_bound_by_cont)
        show "\<not> ?Q None"
          by simp
      next
        fix f_final s3
        assume read_final:
          "Some (f_final, s3) \<in> set_dist (execute read s2)"
        have future_s3: "alpha_future_fresh s3"
          by (rule read_preserves_alpha_future_fresh[OF future_s2 read_final])
        let ?A =
          "\<lambda>out. case out of
              None \<Rightarrow> False
            | Some (as, _) \<Rightarrow> as \<in> B"
        have alpha_bound:
          "wp_event (mmap (replicate (length spec) alpha_round)) ?A s3 \<le> ?C"
          by (rule wp_mmap_alpha_round_alpha_space_set_bound
              [OF future_s3 subset])
        show "wp_event
            (mmap (replicate (length spec) alpha_round) \<bind>
              (\<lambda>as. return (fr, f_fl, f_final, as)))
            ?Q s3 \<le> ?C"
        proof (rule wp_event_bind_bound_by_head_event[OF alpha_bound])
          show "?Q None \<Longrightarrow> ?A None"
            by simp
        next
          fix as t out
          assume cont:
              "out \<in>
                set_dist
                  (execute (return (fr, f_fl, f_final, as)) t)"
            and hit: "?Q out"
          have out_eq: "out = Some ((fr, f_fl, f_final, as), t)"
            using cont
            unfolding set_dist_def return.rep_eq dist_return_def
              dist_delta_dist delta_map_def
            by simp
          show "?A (Some (as, t))"
            using hit unfolding out_eq by simp
        qed
      qed
    qed
  qed
qed

lemma wp_verifier_alpha_prefix_dependent_alpha_space_set_bound:
  fixes C :: prob
  assumes future: "alpha_future_fresh s"
    and subset:
      "\<And>fr f_fl f_final. B fr f_fl f_final \<subseteq> alpha_space"
    and bound:
      "\<And>fr f_fl f_final.
        nnreal (card (B fr f_fl f_final)) / nnreal (card alpha_space) \<le> C"
  shows
    "wp_event verifier_alpha_prefix
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((fr, f_fl, f_final, as'), _) \<Rightarrow>
            as' \<in> B fr f_fl f_final) s
      \<le> C"
proof -
  let ?Q =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl, f_final, as'), _) \<Rightarrow>
          as' \<in> B fr f_fl f_final"
  show ?thesis
    unfolding verifier_alpha_prefix_def
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?Q None"
      by simp
  next
    fix fr s1
    assume read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    have future_s1: "alpha_future_fresh s1"
      by (rule read_preserves_alpha_future_fresh[OF future read_fr])
    show "wp_event
        (ntimes receive_trace_fri_commits (ceil_log clength) \<bind>
          (\<lambda>f_fl. read \<bind>
            (\<lambda>f_final.
              mmap (replicate (length spec) alpha_round) \<bind>
                (\<lambda>as. return (fr, f_fl, f_final, as)))))
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
      have future_s2: "alpha_future_fresh s2"
        by (rule ntimes_receive_trace_fri_commits_preserves_alpha_future_fresh
            [OF trace_fri future_s1])
      show "wp_event
          (read \<bind>
            (\<lambda>f_final.
              mmap (replicate (length spec) alpha_round) \<bind>
                (\<lambda>as. return (fr, f_fl, f_final, as))))
          ?Q s2 \<le> C"
      proof (rule wp_event_bind_bound_by_cont)
        show "\<not> ?Q None"
          by simp
      next
        fix f_final s3
        assume read_final:
          "Some (f_final, s3) \<in> set_dist (execute read s2)"
        have future_s3: "alpha_future_fresh s3"
          by (rule read_preserves_alpha_future_fresh[OF future_s2 read_final])
        let ?B = "B fr f_fl f_final"
        let ?A =
          "\<lambda>out. case out of
              None \<Rightarrow> False
            | Some (as, _) \<Rightarrow> as \<in> ?B"
        have alpha_bound:
          "wp_event (mmap (replicate (length spec) alpha_round)) ?A s3 \<le>
            nnreal (card ?B) / nnreal (card alpha_space)"
          by (rule wp_mmap_alpha_round_alpha_space_set_bound
              [OF future_s3 subset[of fr f_fl f_final]])
        have alpha_bound_C:
          "wp_event (mmap (replicate (length spec) alpha_round)) ?A s3 \<le> C"
          by (rule order_trans[OF alpha_bound bound[of fr f_fl f_final]])
        show "wp_event
            (mmap (replicate (length spec) alpha_round) \<bind>
              (\<lambda>as. return (fr, f_fl, f_final, as)))
            ?Q s3 \<le> C"
        proof (rule wp_event_bind_bound_by_head_event[OF alpha_bound_C])
          show "?Q None \<Longrightarrow> ?A None"
            by simp
        next
          fix as t out
          assume cont:
              "out \<in>
                set_dist
                  (execute (return (fr, f_fl, f_final, as)) t)"
            and hit: "?Q out"
          have out_eq: "out = Some ((fr, f_fl, f_final, as), t)"
            using cont
            unfolding set_dist_def return.rep_eq dist_return_def
              dist_delta_dist delta_map_def
            by simp
          show "?A (Some (as, t))"
            using hit unfolding out_eq by simp
        qed
      qed
    qed
  qed
qed

lemma wp_ntimes_receive_trace_fri_commits_exact_challenges_bound:
  assumes future: "trace_fri_future_fresh s"
    and len: "length bs = n"
  shows
    "wp_event (ntimes receive_trace_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs = bs) s
      \<le> (1 / nnreal size) ^ n"
  using len future
proof (induction n arbitrary: s bs)
  case 0
  then have bs_empty: "bs = []"
    by simp
  show ?case
    unfolding bs_empty by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  obtain b bs' where bs_eq: "bs = b # bs'"
    using Suc.prems(1) by (cases bs) auto
  have len_bs': "length bs' = n"
    using Suc.prems(1) bs_eq by simp
  let ?tail =
    "(ntimes receive_trace_fri_commits n ::
      (('f \<times> 'f) list, ('f, 'a) protocol_channel_scheme) state_monad)"
  let ?Q =
    "\<lambda>out :: ((('f \<times> 'f) list) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of None \<Rightarrow> False | Some (brs, _) \<Rightarrow> map fst brs = bs"
  let ?Head =
    "\<lambda>out :: (('f \<times> 'f) \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of None \<Rightarrow> False | Some ((b0, r0), _) \<Rightarrow> b0 \<in> {b}"
  have head_bound:
    "wp_event receive_trace_fri_commits ?Head s \<le> 1 / nnreal size"
  proof -
    have "wp_event receive_trace_fri_commits ?Head s \<le>
        nnreal (card ({b} :: 'f set)) / nnreal size"
      by (rule wp_receive_trace_fri_commits_fresh_set[OF Suc.prems(2)])
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
    have b0_ne: "b0 \<noteq> b"
      using not_head unfolding br_eq by simp
    have cont_false:
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t
       \<le> wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        (\<lambda>_ :: ((('f \<times> 'f) list) \<times>
          ('f, 'a) protocol_channel_scheme) option. False) t"
      by (rule wp_event_mono_on_support)
        (use b0_ne bs_eq br_eq in
          \<open>auto simp: wpsimps elim!: set_dist_bindE split: option.splits prod.splits\<close>)
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
    have future_t: "trace_fri_future_fresh t"
      by (rule receive_trace_fri_commits_preserves_trace_fri_future_fresh
          [OF Suc.prems(2) head[unfolded br_eq]])
    have tail_bound:
      "wp_event ?tail
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some (brs, _) \<Rightarrow> map fst brs = bs') t
        \<le> (1 / nnreal size) ^ n"
      by (rule Suc.IH[OF len_bs' future_t])
    have cont_eq:
      "(\<lambda>out. case out of
          None \<Rightarrow> (0 :: prob)
        | Some (brs, u) \<Rightarrow>
            wp (return (br # brs)) (\<lambda>out. if ?Q out then 1 else 0) u) =
       (\<lambda>out :: ((('f \<times> 'f) list) \<times>
          ('f, 'a) protocol_channel_scheme) option.
          if (case out of None \<Rightarrow> False
            | Some (brs, _) \<Rightarrow> map fst brs = bs')
          then 1 else 0)"
      by (rule ext)
        (auto simp: wpsimps b0_eq bs_eq br_eq
          split: option.splits prod.splits)
    have "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t =
        wp_event ?tail
          (\<lambda>out. case out of None \<Rightarrow> False
            | Some (brs, _) \<Rightarrow> map fst brs = bs') t"
      unfolding wp_event_def by (simp add: wpsimps cont_eq)
    also have "... \<le> (1 / nnreal size) ^ n"
      by (rule tail_bound)
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

lemma wp_ntimes_receive_trace_fri_commits_finite_set_bound:
  assumes future: "trace_fri_future_fresh s"
    and finite_B: "finite B"
    and lengths: "\<And>bs. bs \<in> B \<Longrightarrow> length bs = n"
  shows
    "wp_event (ntimes receive_trace_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs \<in> B) s
      \<le> nnreal (card B) / (nnreal size) ^ n"
proof -
  let ?P =
    "\<lambda>bs out. case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow> map fst brs = bs"
  have event_mono:
    "wp_event (ntimes receive_trace_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs \<in> B) s
      \<le> wp_event (ntimes receive_trace_fri_commits n)
        (\<lambda>out. \<exists>bs \<in> B. ?P bs out) s"
    by (rule wp_event_mono) (auto split: option.splits prod.splits)
  also have "... \<le> (\<Sum>bs\<in>B. (1 / nnreal size) ^ n)"
    by (rule wp_event_finite_UN_bound[OF finite_B])
      (rule wp_ntimes_receive_trace_fri_commits_exact_challenges_bound
        [OF future lengths])
  also have "... = nnreal (card B) * ((1 / nnreal size) ^ n)"
    using finite_B by simp
  also have "... = nnreal (card B) / (nnreal size) ^ n"
    using size_card by transfer (simp add: power_divide)
  finally show ?thesis .
qed

lemma wp_ntimes_receive_trace_fri_commits_challenge_space_set_bound:
  assumes future: "trace_fri_future_fresh s"
    and subset: "B \<subseteq> fri_challenge_space n"
  shows
    "wp_event (ntimes receive_trace_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs \<in> B) s
      \<le> nnreal (card B) / nnreal (CARD('f) ^ n)"
proof -
  have finite_B: "finite B"
    by (rule finite_subset[OF subset finite_fri_challenge_space])
  have lengths: "\<And>bs. bs \<in> B \<Longrightarrow> length bs = n"
    using subset unfolding fri_challenge_space_def by auto
  have "wp_event (ntimes receive_trace_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs \<in> B) s
      \<le> nnreal (card B) / (nnreal size) ^ n"
    by (rule wp_ntimes_receive_trace_fri_commits_finite_set_bound
        [OF future finite_B lengths])
  also have "... = nnreal (card B) / nnreal (CARD('f) ^ n)"
    using size_card by simp
  finally show ?thesis .
qed

lemma wp_verifier_trace_fri_prefix_challenge_space_set_bound:
  assumes future: "trace_fri_future_fresh s"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
  shows
    "wp_event verifier_trace_fri_prefix
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((_, f_fl), _) \<Rightarrow> map fst f_fl \<in> B) s
      \<le> nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
proof -
  let ?Q =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((_, f_fl), _) \<Rightarrow> map fst f_fl \<in> B"
  let ?C = "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength)"
  show ?thesis
    unfolding verifier_trace_fri_prefix_def
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?Q None"
      by simp
  next
    fix fr s1
    assume read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    have future_s1: "trace_fri_future_fresh s1"
      by (rule read_preserves_trace_fri_future_fresh[OF future read_fr])
    let ?Head =
      "\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (f_fl, _) \<Rightarrow> map fst f_fl \<in> B"
    have trace_bound:
      "wp_event (ntimes receive_trace_fri_commits (ceil_log clength))
        ?Head s1 \<le> ?C"
      by (rule wp_ntimes_receive_trace_fri_commits_challenge_space_set_bound
          [OF future_s1 subset])
    show "wp_event
        (ntimes receive_trace_fri_commits (ceil_log clength) \<bind>
          (\<lambda>f_fl. return (fr, f_fl)))
        ?Q s1 \<le> ?C"
    proof (rule wp_event_bind_bound_by_head_event[OF trace_bound])
      show "?Q None \<Longrightarrow> ?Head None"
        by simp
    next
      fix f_fl t out
      assume cont:
          "out \<in> set_dist (execute (return (fr, f_fl)) t)"
        and hit: "?Q out"
      have out_eq: "out = Some ((fr, f_fl), t)"
        using cont
        unfolding set_dist_def return.rep_eq dist_return_def
          dist_delta_dist delta_map_def
        by simp
      show "?Head (Some (f_fl, t))"
        using hit unfolding out_eq by simp
    qed
  qed
qed

lemma wp_verifier_trace_fri_prefix_dependent_challenge_space_set_bound:
  fixes C :: prob
  assumes future: "trace_fri_future_fresh s"
    and subset: "\<And>fr. B fr \<subseteq> fri_challenge_space (ceil_log clength)"
    and bound:
      "\<And>fr. nnreal (card (B fr)) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "wp_event verifier_trace_fri_prefix
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((fr, f_fl), _) \<Rightarrow> map fst f_fl \<in> B fr) s
      \<le> C"
proof -
  let ?Q =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl), _) \<Rightarrow> map fst f_fl \<in> B fr"
  show ?thesis
    unfolding verifier_trace_fri_prefix_def
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?Q None"
      by simp
  next
    fix fr s1
    assume read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    have future_s1: "trace_fri_future_fresh s1"
      by (rule read_preserves_trace_fri_future_fresh[OF future read_fr])
    let ?Head =
      "\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (f_fl, _) \<Rightarrow> map fst f_fl \<in> B fr"
    have trace_bound:
      "wp_event (ntimes receive_trace_fri_commits (ceil_log clength))
        ?Head s1 \<le>
        nnreal (card (B fr)) / nnreal (CARD('f) ^ ceil_log clength)"
      by (rule wp_ntimes_receive_trace_fri_commits_challenge_space_set_bound
          [OF future_s1 subset[of fr]])
    have trace_bound_C:
      "wp_event (ntimes receive_trace_fri_commits (ceil_log clength))
        ?Head s1 \<le> C"
      by (rule order_trans[OF trace_bound bound[of fr]])
    show "wp_event
        (ntimes receive_trace_fri_commits (ceil_log clength) \<bind>
          (\<lambda>f_fl. return (fr, f_fl)))
        ?Q s1 \<le> C"
    proof (rule wp_event_bind_bound_by_head_event[OF trace_bound_C])
      show "?Q None \<Longrightarrow> ?Head None"
        by simp
    next
      fix f_fl t out
      assume cont:
          "out \<in> set_dist (execute (return (fr, f_fl)) t)"
        and hit: "?Q out"
      have out_eq: "out = Some ((fr, f_fl), t)"
        using cont
        unfolding set_dist_def return.rep_eq dist_return_def
          dist_delta_dist delta_map_def
        by simp
      show "?Head (Some (f_fl, t))"
        using hit unfolding out_eq by simp
    qed
  qed
qed

lemma receive_composition_fri_commits_outcome:
  assumes outcome:
    "Some ((b, r), t) \<in>
      set_dist (execute receive_composition_fri_commits s)"
  shows
    "\<exists>rest.
      PTranscript s = r # rest \<and>
      PState t = concat (PState s) r \<and>
      PTranscript t = rest \<and>
      s \<le> t \<and>
      PTraceFriCounter t = PTraceFriCounter s \<and>
      PCompositionFriCounter t = Suc (PCompositionFriCounter s) \<and>
      PAlphaCounter t = PAlphaCounter s \<and>
      PQueryCounter t = PQueryCounter s \<and>
      fmlookup (HashMap t)
        (CompositionFriChallenge (PCompositionFriCounter s)
          (concat (PState s) r)) =
        Some b"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in> set_dist (execute receive_composition_fri_challenge s_read)"
    unfolding receive_composition_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  obtain rest where tr_s: "PTranscript s = r # rest"
  proof -
    have "PTranscript s \<noteq> []"
      using read_r unfolding read_def protocol_read_def assert_def
      by (cases "PTranscript s") (auto simp: throw_no_outcome elim!: set_dist_bindE)
    then obtain x xs where xs: "PTranscript s = x # xs"
      by (cases "PTranscript s") auto
    have r_x: "r = x"
      using read_nonempty_outcome[OF read_r xs] by simp
    show ?thesis
      using that xs r_x by auto
  qed
  have read_res:
    "s_read = s\<lparr>PState := concat (PState s) r, PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF read_r tr_s] by simp
  have rand_res:
    "s_read \<le> t \<and>
     PState t = PState s_read \<and>
     PTranscript t = PTranscript s_read \<and>
     fmlookup (HashMap t)
       (CompositionFriChallenge (PCompositionFriCounter s_read)
         (PState s_read)) =
      Some b"
    using receive_composition_fri_challenge_outcome[OF rand_b] .
  have rand_counter:
    "PTraceFriCounter t = PTraceFriCounter s_read \<and>
     PCompositionFriCounter t = Suc (PCompositionFriCounter s_read) \<and>
     PAlphaCounter t = PAlphaCounter s_read \<and>
     PQueryCounter t = PQueryCounter s_read"
    using receive_composition_fri_challenge_counter_outcome[OF rand_b] by simp
  have s_read_ext: "s \<le> s_read"
    using read_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s_t: "s \<le> t"
    using s_read_ext rand_res by (meson hash_ext_trans)
  show ?thesis
    using tr_s read_res rand_res rand_counter s_t by auto
qed

lemma receive_composition_fri_commits_preserves_composition_fri_future_fresh:
  assumes future: "composition_fri_future_fresh s"
    and outcome:
      "Some ((b, r), t) \<in>
        set_dist (execute receive_composition_fri_commits s)"
  shows "composition_fri_future_fresh t"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in>
        set_dist (execute receive_composition_fri_challenge s_read)"
    unfolding receive_composition_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_r] have read_counts:
    "PCompositionFriCounter s_read = PCompositionFriCounter s"
    by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have counter_t:
    "PCompositionFriCounter t = Suc (PCompositionFriCounter s)"
    using receive_composition_fri_challenge_counter_outcome[OF rand_b]
      read_counts
    by simp
  show ?thesis
    unfolding composition_fri_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge_t: "PCompositionFriCounter t \<le> i"
    have i_ge_s: "PCompositionFriCounter s \<le> i"
      using i_ge_t counter_t by simp
    have neq:
      "CompositionFriChallenge i x \<noteq>
        CompositionFriChallenge
          (PCompositionFriCounter s_read) (PState s_read)"
      using i_ge_t counter_t read_counts by auto
    have "fmlookup (HashMap t) (CompositionFriChallenge i x) =
        fmlookup (HashMap s_read) (CompositionFriChallenge i x)"
      by (rule receive_composition_fri_challenge_preserves_other_lookup
          [OF rand_b neq])
    also have "... = fmlookup (HashMap s) (CompositionFriChallenge i x)"
      using read_hash by simp
    also have "... = None"
      using future i_ge_s unfolding composition_fri_future_fresh_def by blast
    finally show "fmlookup (HashMap t) (CompositionFriChallenge i x) = None" .
  qed
qed

lemma receive_composition_fri_commits_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some ((b, r), t) \<in>
        set_dist (execute receive_composition_fri_commits s)"
  shows "query_future_fresh t"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in>
        set_dist (execute receive_composition_fri_challenge s_read)"
    unfolding receive_composition_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_r] have read_counts:
    "PQueryCounter s_read = PQueryCounter s"
    by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have counter_t:
    "PQueryCounter t = PQueryCounter s"
    using receive_composition_fri_challenge_counter_outcome[OF rand_b]
      read_counts
    by simp
  show ?thesis
    unfolding query_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge_t: "PQueryCounter t \<le> i"
    have i_ge_s: "PQueryCounter s \<le> i"
      using i_ge_t counter_t by simp
    have neq:
      "QueryIndexChallenge i x \<noteq>
        CompositionFriChallenge
          (PCompositionFriCounter s_read) (PState s_read)"
      by simp
    have "fmlookup (HashMap t) (QueryIndexChallenge i x) =
        fmlookup (HashMap s_read) (QueryIndexChallenge i x)"
      by (rule receive_composition_fri_challenge_preserves_other_lookup
          [OF rand_b neq])
    also have "... = fmlookup (HashMap s) (QueryIndexChallenge i x)"
      using read_hash by simp
    also have "... = None"
      using future i_ge_s unfolding query_future_fresh_def by blast
    finally show "fmlookup (HashMap t) (QueryIndexChallenge i x) = None" .
  qed
qed

lemma wp_receive_composition_fri_commits_fresh_set:
  assumes future: "composition_fri_future_fresh s"
  shows
    "wp_event receive_composition_fri_commits
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((b, r), _) \<Rightarrow> b \<in> B) s
      \<le> nnreal (card B) / nnreal size"
  unfolding receive_composition_fri_commits_def receive_fri_commits_with_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> (case None of
      None \<Rightarrow> False | Some ((b, r), _) \<Rightarrow> b \<in> B)"
    by simp
next
  fix r s_read
  assume read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
  have read_counts:
    "PCompositionFriCounter s_read = PCompositionFriCounter s"
    using read_outcome[OF read_r] by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  have fresh:
    "fmlookup (HashMap s_read)
      (CompositionFriChallenge
        (PCompositionFriCounter s_read) (PState s_read)) = None"
    using future read_counts read_hash
    unfolding composition_fri_future_fresh_def by simp
  let ?Q =
    "\<lambda>out :: (('f \<times> 'f) \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of None \<Rightarrow> False | Some ((b, r), _) \<Rightarrow> b \<in> B"
  have cont_eq:
    "(\<lambda>out. case out of
        None \<Rightarrow> (0 :: prob)
      | Some (b, u) \<Rightarrow>
          wp (return (b, r)) (\<lambda>out. if ?Q out then 1 else 0) u) =
     (\<lambda>out :: ('f \<times> ('f, 'a) protocol_channel_scheme) option.
        if (case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B)
        then 1 else 0)"
    by (rule ext) (auto simp: wpsimps split: option.splits prod.splits)
  have "wp_event
      (receive_composition_fri_challenge \<bind> (\<lambda>b :: 'f. return (b, r)))
      ?Q s_read =
      wp_event receive_composition_fri_challenge
        (\<lambda>out. case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B)
        s_read"
    unfolding wp_event_def by (simp add: wpsimps cont_eq)
  also have "... = nnreal (card B) / nnreal size"
    by (rule wp_receive_composition_fri_challenge_fresh_set[OF fresh])
  finally show
    "wp_event
      (receive_composition_fri_challenge \<bind> (\<lambda>b :: 'f. return (b, r)))
      (\<lambda>out. case out of None \<Rightarrow> False | Some ((b, r), _) \<Rightarrow> b \<in> B)
      s_read
      \<le> nnreal (card B) / nnreal size"
    by simp
qed

lemma ntimes_receive_composition_fri_commits_preserves_composition_fri_future_fresh:
  assumes outcome:
      "Some (brs, t) \<in>
        set_dist (execute (ntimes receive_composition_fri_commits n) s)"
    and future: "composition_fri_future_fresh s"
  shows "composition_fri_future_fresh t"
  using outcome future
proof (induction n arbitrary: s brs t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain br brs' s1 where
    head:
      "Some (br, s1) \<in>
        set_dist (execute receive_composition_fri_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes receive_composition_fri_commits n) s1)"
    and brs_eq: "brs = br # brs'"
    by (auto elim!: set_dist_bindE)
  obtain b r where br_eq: "br = (b, r)"
    by (cases br)
  have future_s1:
    "composition_fri_future_fresh s1"
    by (rule receive_composition_fri_commits_preserves_composition_fri_future_fresh
        [OF Suc.prems(2) head[unfolded br_eq]])
  show ?case
    by (rule Suc.IH[OF tail future_s1])
qed

lemma ntimes_receive_composition_fri_commits_preserves_query_future_fresh:
  assumes outcome:
      "Some (brs, t) \<in>
        set_dist (execute (ntimes receive_composition_fri_commits n) s)"
    and future: "query_future_fresh s"
  shows "query_future_fresh t"
  using outcome future
proof (induction n arbitrary: s brs t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain br brs' s1 where
    head:
      "Some (br, s1) \<in>
        set_dist (execute receive_composition_fri_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes receive_composition_fri_commits n) s1)"
    by (auto elim!: set_dist_bindE)
  obtain b r where br_eq: "br = (b, r)"
    by (cases br)
  have future_s1:
    "query_future_fresh s1"
    by (rule receive_composition_fri_commits_preserves_query_future_fresh
        [OF Suc.prems(2) head[unfolded br_eq]])
  show ?case
    by (rule Suc.IH[OF tail future_s1])
qed

lemma wp_ntimes_receive_composition_fri_commits_exact_challenges_bound:
  assumes future: "composition_fri_future_fresh s"
    and len: "length bs = n"
  shows
    "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs = bs) s
      \<le> (1 / nnreal size) ^ n"
  using len future
proof (induction n arbitrary: s bs)
  case 0
  then have bs_empty: "bs = []"
    by simp
  show ?case
    unfolding bs_empty by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  obtain b bs' where bs_eq: "bs = b # bs'"
    using Suc.prems(1) by (cases bs) auto
  have len_bs': "length bs' = n"
    using Suc.prems(1) bs_eq by simp
  let ?tail =
    "(ntimes receive_composition_fri_commits n ::
      (('f \<times> 'f) list, ('f, 'a) protocol_channel_scheme) state_monad)"
  let ?Q =
    "\<lambda>out :: ((('f \<times> 'f) list) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of None \<Rightarrow> False | Some (brs, _) \<Rightarrow> map fst brs = bs"
  let ?Head =
    "\<lambda>out :: (('f \<times> 'f) \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of None \<Rightarrow> False | Some ((b0, r0), _) \<Rightarrow> b0 \<in> {b}"
  have head_bound:
    "wp_event receive_composition_fri_commits ?Head s \<le> 1 / nnreal size"
  proof -
    have "wp_event receive_composition_fri_commits ?Head s \<le>
        nnreal (card ({b} :: 'f set)) / nnreal size"
      by (rule wp_receive_composition_fri_commits_fresh_set[OF Suc.prems(2)])
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
    have b0_ne: "b0 \<noteq> b"
      using not_head unfolding br_eq by simp
    have cont_false:
      "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t
       \<le> wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        (\<lambda>_ :: ((('f \<times> 'f) list) \<times>
          ('f, 'a) protocol_channel_scheme) option. False) t"
      by (rule wp_event_mono_on_support)
        (use b0_ne bs_eq br_eq in
          \<open>auto simp: wpsimps elim!: set_dist_bindE split: option.splits prod.splits\<close>)
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
    have future_t: "composition_fri_future_fresh t"
      by (rule receive_composition_fri_commits_preserves_composition_fri_future_fresh
          [OF Suc.prems(2) head[unfolded br_eq]])
    have tail_bound:
      "wp_event ?tail
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some (brs, _) \<Rightarrow> map fst brs = bs') t
        \<le> (1 / nnreal size) ^ n"
      by (rule Suc.IH[OF len_bs' future_t])
    have cont_eq:
      "(\<lambda>out. case out of
          None \<Rightarrow> (0 :: prob)
        | Some (brs, u) \<Rightarrow>
            wp (return (br # brs)) (\<lambda>out. if ?Q out then 1 else 0) u) =
       (\<lambda>out :: ((('f \<times> 'f) list) \<times>
          ('f, 'a) protocol_channel_scheme) option.
          if (case out of None \<Rightarrow> False
            | Some (brs, _) \<Rightarrow> map fst brs = bs')
          then 1 else 0)"
      by (rule ext)
        (auto simp: wpsimps b0_eq bs_eq br_eq
          split: option.splits prod.splits)
    have "wp_event (?tail \<bind> (\<lambda>brs :: ('f \<times> 'f) list. return (br # brs)))
        ?Q t =
        wp_event ?tail
          (\<lambda>out. case out of None \<Rightarrow> False
            | Some (brs, _) \<Rightarrow> map fst brs = bs') t"
      unfolding wp_event_def by (simp add: wpsimps cont_eq)
    also have "... \<le> (1 / nnreal size) ^ n"
      by (rule tail_bound)
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

lemma wp_ntimes_receive_composition_fri_commits_finite_set_bound:
  assumes future: "composition_fri_future_fresh s"
    and finite_B: "finite B"
    and lengths: "\<And>bs. bs \<in> B \<Longrightarrow> length bs = n"
  shows
    "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs \<in> B) s
      \<le> nnreal (card B) / (nnreal size) ^ n"
proof -
  let ?P =
    "\<lambda>bs out. case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow> map fst brs = bs"
  have event_mono:
    "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs \<in> B) s
      \<le> wp_event (ntimes receive_composition_fri_commits n)
        (\<lambda>out. \<exists>bs \<in> B. ?P bs out) s"
    by (rule wp_event_mono) (auto split: option.splits prod.splits)
  also have "... \<le> (\<Sum>bs\<in>B. (1 / nnreal size) ^ n)"
    by (rule wp_event_finite_UN_bound[OF finite_B])
      (rule wp_ntimes_receive_composition_fri_commits_exact_challenges_bound
        [OF future lengths])
  also have "... = nnreal (card B) * ((1 / nnreal size) ^ n)"
    using finite_B by simp
  also have "... = nnreal (card B) / (nnreal size) ^ n"
    using size_card by transfer (simp add: power_divide)
  finally show ?thesis .
qed

lemma wp_ntimes_receive_composition_fri_commits_challenge_space_set_bound:
  assumes future: "composition_fri_future_fresh s"
    and subset: "B \<subseteq> fri_challenge_space n"
  shows
    "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs \<in> B) s
      \<le> nnreal (card B) / nnreal (CARD('f) ^ n)"
proof -
  have finite_B: "finite B"
    by (rule finite_subset[OF subset finite_fri_challenge_space])
  have lengths: "\<And>bs. bs \<in> B \<Longrightarrow> length bs = n"
    using subset unfolding fri_challenge_space_def by auto
  have "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs \<in> B) s
      \<le> nnreal (card B) / (nnreal size) ^ n"
    by (rule wp_ntimes_receive_composition_fri_commits_finite_set_bound
        [OF future finite_B lengths])
  also have "... = nnreal (card B) / nnreal (CARD('f) ^ n)"
    using size_card by simp
  finally show ?thesis .
qed

lemma wp_verifier_composition_fri_prefix_challenge_space_set_bound:
  assumes future: "composition_fri_future_fresh s"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verifier_composition_fri_prefix
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((_, _, _, _, dg, fl), _) \<Rightarrow> map fst fl \<in> B dg) s
      \<le> C"
proof -
  let ?Q =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((_, _, _, _, dg, fl), _) \<Rightarrow> map fst fl \<in> B dg"
  show ?thesis
    unfolding verifier_composition_fri_prefix_def
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?Q None"
      by simp
  next
    fix fr s1
    assume read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    have future_s1: "composition_fri_future_fresh s1"
      by (rule read_preserves_composition_fri_future_fresh
          [OF future read_fr])
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
      have future_s2: "composition_fri_future_fresh s2"
        by (rule ntimes_receive_trace_fri_commits_preserves_composition_fri_future_fresh
            [OF trace_fri future_s1])
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
        have future_s3: "composition_fri_future_fresh s3"
          by (rule read_preserves_composition_fri_future_fresh
              [OF future_s2 read_final])
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
          have future_s4: "composition_fri_future_fresh s4"
            by (rule mmap_alpha_round_preserves_composition_fri_future_fresh
                [OF future_s3 alpha])
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
            have future_s5: "composition_fri_future_fresh s5"
              by (rule read_preserves_composition_fri_future_fresh
                  [OF future_s4 read_dg])
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
              have future_s6: "composition_fri_future_fresh s6"
                using future_s5 unfolding s6_eq .
              let ?Head =
                "\<lambda>out. case out of
                    None \<Rightarrow> False
                  | Some (fl, _) \<Rightarrow> map fst fl \<in> B dg"
              have comp_bound:
                "wp_event
                  (ntimes receive_composition_fri_commits
                    (ceil_log (to_nat dg + 1)))
                  ?Head s6 \<le>
                  nnreal (card (B dg)) /
                    nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
                by (rule
                    wp_ntimes_receive_composition_fri_commits_challenge_space_set_bound
                    [OF future_s6 subset])
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
                assume cont:
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
                show "?Head (Some (fl, t))"
                  using hit unfolding out_eq by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma ntimes_receive_fri_commits_with_outcome:
  fixes receive_commits :: "('f, 'f \<times> 'f, 'a) protocol_c_monad"
    and counter :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat"
    and preserve1 :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat"
    and preserve2 :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat"
    and preserve3 :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat"
    and tag :: "nat \<Rightarrow> 'f \<Rightarrow> 'f protocol_hash_input"
  assumes step_outcome:
      "\<And>s b r t. Some ((b, r), t) \<in> set_dist (execute receive_commits s) \<Longrightarrow>
        \<exists>rest.
          PTranscript s = r # rest \<and>
          PState t = concat (PState s) r \<and>
          PTranscript t = rest \<and>
          s \<le> t \<and>
          counter t = Suc (counter s) \<and>
          preserve1 t = preserve1 s \<and>
          preserve2 t = preserve2 s \<and>
          preserve3 t = preserve3 s \<and>
          fmlookup (HashMap t) (tag (counter s) (concat (PState s) r)) = Some b"
    and outcome:
      "Some (brs, t) \<in> set_dist (execute (ntimes receive_commits n) s)"
  shows
    "length brs = n \<and>
     PTranscript s = map snd brs @ PTranscript t \<and>
     PState t = foldl concat (PState s) (map snd brs) \<and>
     s \<le> t \<and>
     counter t = counter s + n \<and>
     preserve1 t = preserve1 s \<and>
     preserve2 t = preserve2 s \<and>
     preserve3 t = preserve3 s \<and>
     (\<forall>i < n.
        fmlookup (HashMap t)
          (tag (counter s + i)
            (foldl concat (PState s) (take (Suc i) (map snd brs)))) =
          Some (fst (brs ! i)))"
  using outcome
proof (induction n arbitrary: s brs t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain br brs' s1 where
    head: "Some (br, s1) \<in> set_dist (execute receive_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes receive_commits n) s1)"
    and brs_eq: "brs = br # brs'"
    by (auto elim!: set_dist_bindE)
  obtain b r where br_eq: "br = (b, r)"
    by (cases br)
  from step_outcome[OF head[unfolded br_eq]]
  obtain rest1 where
    tr_s: "PTranscript s = r # rest1"
    and st_s1: "PState s1 = concat (PState s) r"
    and tr_s1: "PTranscript s1 = rest1"
    and ext_head: "s \<le> s1"
    and counter_s1: "counter s1 = Suc (counter s)"
    and preserve1_s1: "preserve1 s1 = preserve1 s"
    and preserve2_s1: "preserve2 s1 = preserve2 s"
    and preserve3_s1: "preserve3 s1 = preserve3 s"
    and lookup_head:
      "fmlookup (HashMap s1) (tag (counter s) (concat (PState s) r)) = Some b"
    by blast
  have tail_res:
    "length brs' = n \<and>
     PTranscript s1 = map snd brs' @ PTranscript t \<and>
     PState t = foldl concat (PState s1) (map snd brs') \<and>
     s1 \<le> t \<and>
     counter t = counter s1 + n \<and>
     preserve1 t = preserve1 s1 \<and>
     preserve2 t = preserve2 s1 \<and>
     preserve3 t = preserve3 s1 \<and>
     (\<forall>i<n.
        fmlookup (HashMap t)
          (tag (counter s1 + i)
            (foldl concat (PState s1) (take (Suc i) (map snd brs')))) =
          Some (fst (brs' ! i)))"
    using Suc.IH[OF tail] .
  have ext_s1_t: "s1 \<le> t"
    using tail_res by simp
  have lookup_head_t:
    "fmlookup (HashMap t) (tag (counter s) (concat (PState s) r)) = Some b"
    using hash_extension_lookup[OF lookup_head ext_s1_t] .
  have ext_combined: "s \<le> t"
    using ext_head ext_s1_t by (meson hash_ext_trans)
  have counter_t: "counter t = counter s + Suc n"
    using tail_res counter_s1 by simp
  have preserves_t:
    "preserve1 t = preserve1 s \<and>
     preserve2 t = preserve2 s \<and>
     preserve3 t = preserve3 s"
    using tail_res preserve1_s1 preserve2_s1 preserve3_s1 by simp
  have lookups:
    "\<forall>i < Suc n.
      fmlookup (HashMap t)
        (tag (counter s + i)
          (foldl concat (PState s) (take (Suc i) (map snd brs)))) =
        Some (fst (brs ! i))"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < Suc n"
    show "fmlookup (HashMap t)
        (tag (counter s + i)
          (foldl concat (PState s) (take (Suc i) (map snd brs)))) =
        Some (fst (brs ! i))"
    proof (cases i)
      case 0
      then show ?thesis
        using brs_eq br_eq lookup_head_t by simp
    next
      case (Suc j)
      have j_bound: "j < n"
        using i_bound Suc by simp
      have state_shift:
        "foldl concat (PState s) (take (Suc (Suc j)) (map snd brs)) =
          foldl concat (PState s1) (take (Suc j) (map snd brs'))"
        using brs_eq br_eq st_s1 by simp
      have brs_nth: "brs ! Suc j = brs' ! j"
        using brs_eq j_bound by simp
      show ?thesis
        using tail_res j_bound Suc state_shift brs_nth counter_s1 by simp
    qed
  qed
  have as_eq:
    "PTranscript s = map snd brs @ PTranscript t \<and>
     PState t = foldl concat (PState s) (map snd brs)"
    using tail_res tr_s tr_s1 st_s1 brs_eq br_eq by simp
  show ?case
    using tail_res tr_s tr_s1 st_s1 ext_combined lookups as_eq brs_eq br_eq
      counter_t preserves_t
    by simp
qed

lemma ntimes_receive_trace_fri_commits_outcome:
  assumes outcome:
    "Some (brs, t) \<in>
      set_dist (execute (ntimes receive_trace_fri_commits n) s)"
  shows
    "length brs = n \<and>
     PTranscript s = map snd brs @ PTranscript t \<and>
     PState t = foldl concat (PState s) (map snd brs) \<and>
     s \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s + n \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s \<and>
     (\<forall>i < n.
        fmlookup (HashMap t)
          (TraceFriChallenge (PTraceFriCounter s + i)
            (foldl concat (PState s) (take (Suc i) (map snd brs)))) =
          Some (fst (brs ! i)))"
proof -
  have res:
    "length brs = n \<and>
     PTranscript s = map snd brs @ PTranscript t \<and>
     PState t = foldl concat (PState s) (map snd brs) \<and>
     s \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s + n \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s \<and>
     (\<forall>i < n.
        fmlookup (HashMap t)
          (TraceFriChallenge (PTraceFriCounter s + i)
            (foldl concat (PState s) (take (Suc i) (map snd brs)))) =
          Some (fst (brs ! i)))"
    by (rule ntimes_receive_fri_commits_with_outcome
        [of receive_trace_fri_commits PTraceFriCounter PCompositionFriCounter
          PAlphaCounter PQueryCounter TraceFriChallenge,
          OF receive_trace_fri_commits_outcome outcome])
  then show ?thesis .
qed

lemma ntimes_receive_composition_fri_commits_outcome:
  assumes outcome:
    "Some (brs, t) \<in>
      set_dist (execute (ntimes receive_composition_fri_commits n) s)"
  shows
    "length brs = n \<and>
     PTranscript s = map snd brs @ PTranscript t \<and>
     PState t = foldl concat (PState s) (map snd brs) \<and>
     s \<le> t \<and>
     PCompositionFriCounter t = PCompositionFriCounter s + n \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s \<and>
     (\<forall>i < n.
        fmlookup (HashMap t)
          (CompositionFriChallenge (PCompositionFriCounter s + i)
            (foldl concat (PState s) (take (Suc i) (map snd brs)))) =
          Some (fst (brs ! i)))"
proof -
  have composition_step_outcome:
    "\<And>s b r t. Some ((b, r), t) \<in>
        set_dist (execute receive_composition_fri_commits s) \<Longrightarrow>
      \<exists>rest.
        PTranscript s = r # rest \<and>
        PState t = concat (PState s) r \<and>
        PTranscript t = rest \<and>
        s \<le> t \<and>
        PCompositionFriCounter t = Suc (PCompositionFriCounter s) \<and>
        PTraceFriCounter t = PTraceFriCounter s \<and>
        PAlphaCounter t = PAlphaCounter s \<and>
        PQueryCounter t = PQueryCounter s \<and>
        fmlookup (HashMap t)
          (CompositionFriChallenge (PCompositionFriCounter s)
            (concat (PState s) r)) =
          Some b"
    using receive_composition_fri_commits_outcome by blast
  have res:
    "length brs = n \<and>
     PTranscript s = map snd brs @ PTranscript t \<and>
     PState t = foldl concat (PState s) (map snd brs) \<and>
     s \<le> t \<and>
     PCompositionFriCounter t = PCompositionFriCounter s + n \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s \<and>
     (\<forall>i < n.
        fmlookup (HashMap t)
          (CompositionFriChallenge (PCompositionFriCounter s + i)
            (foldl concat (PState s) (take (Suc i) (map snd brs)))) =
          Some (fst (brs ! i)))"
    using composition_step_outcome outcome
    by (rule ntimes_receive_fri_commits_with_outcome
        [of receive_composition_fri_commits PCompositionFriCounter
          PTraceFriCounter PAlphaCounter PQueryCounter CompositionFriChallenge])
  then show ?thesis .
qed

lemma ntimes_receive_composition_fri_commits_roots_outcome:
  assumes outcome:
    "Some (brs, t) \<in>
      set_dist (execute (ntimes receive_composition_fri_commits n) s)"
  shows "map snd brs = take n (PTranscript s)"
proof -
  have res:
    "length brs = n \<and> PTranscript s = map snd brs @ PTranscript t"
    using ntimes_receive_composition_fri_commits_outcome[OF outcome] by simp
  have len: "length (map snd brs) = n"
    using res by simp
  have "take n (PTranscript s) = take n (map snd brs @ PTranscript t)"
    using res by simp
  also have "... = map snd brs"
    using len by simp
  finally show ?thesis
    by simp
qed

lemma wp_ntimes_receive_composition_fri_commits_root_dependent_challenge_space_set_bound:
  fixes B :: "'f list \<Rightarrow> 'f list set"
  assumes future: "composition_fri_future_fresh s"
    and subset: "\<And>roots. B roots \<subseteq> fri_challenge_space n"
  shows
    "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs \<in> B (map snd brs)) s
      \<le> nnreal (card (B (take n (PTranscript s)))) /
          nnreal (CARD('f) ^ n)"
proof -
  let ?roots = "take n (PTranscript s)"
  let ?Q =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow> map fst brs \<in> B (map snd brs)"
  let ?Q' =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow> map fst brs \<in> B ?roots"
  have fixed_bound:
    "wp_event (ntimes receive_composition_fri_commits n) ?Q' s
      \<le> nnreal (card (B ?roots)) / nnreal (CARD('f) ^ n)"
    by (rule wp_ntimes_receive_composition_fri_commits_challenge_space_set_bound
        [OF future subset])
  have event_le:
    "wp_event (ntimes receive_composition_fri_commits n) ?Q s
      \<le> wp_event (ntimes receive_composition_fri_commits n) ?Q' s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume out_supp:
      "out \<in> set_dist (execute (ntimes receive_composition_fri_commits n) s)"
      and hit: "?Q out"
    show "?Q' out"
    proof (cases out)
      case None
      then show ?thesis
        using hit by simp
    next
      case (Some pair)
      then obtain brs t where out_eq: "out = Some (brs, t)"
        by (cases pair) auto
      have roots_eq: "map snd brs = ?roots"
        by (rule ntimes_receive_composition_fri_commits_roots_outcome)
          (use out_supp out_eq in simp)
      show ?thesis
        using hit roots_eq out_eq by simp
    qed
  qed
  show ?thesis
    by (rule order_trans[OF event_le fixed_bound])
qed

lemma wp_ntimes_receive_composition_fri_commits_root_dependent_bound:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and subset: "\<And>roots. B roots \<subseteq> fri_challenge_space n"
    and bound:
      "\<And>roots. nnreal (card (B roots)) /
        nnreal (CARD('f) ^ n) \<le> C"
  shows
    "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs \<in> B (map snd brs)) s
      \<le> C"
proof -
  have root_bound:
    "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow> map fst brs \<in> B (map snd brs)) s
      \<le> nnreal (card (B (take n (PTranscript s)))) /
          nnreal (CARD('f) ^ n)"
    by (rule
        wp_ntimes_receive_composition_fri_commits_root_dependent_challenge_space_set_bound
        [OF future subset])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma wp_verifier_composition_fri_prefix_root_dependent_challenge_space_set_bound:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and subset:
      "\<And>fr f_fl f_final as dg roots.
        B fr f_fl f_final as dg roots \<subseteq>
          fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>fr f_fl f_final as dg roots.
        nnreal (card (B fr f_fl f_final as dg roots)) /
          nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verifier_composition_fri_prefix
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((fr, f_fl, f_final, as, dg, fl), _) \<Rightarrow>
            map fst fl \<in> B fr f_fl f_final as dg (map snd fl)) s
      \<le> C"
proof -
  let ?Q =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl, f_final, as, dg, fl), _) \<Rightarrow>
          map fst fl \<in> B fr f_fl f_final as dg (map snd fl)"
  show ?thesis
    unfolding verifier_composition_fri_prefix_def
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?Q None"
      by simp
  next
    fix fr s1
    assume read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    have future_s1: "composition_fri_future_fresh s1"
      by (rule read_preserves_composition_fri_future_fresh
          [OF future read_fr])
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
      have future_s2: "composition_fri_future_fresh s2"
        by (rule ntimes_receive_trace_fri_commits_preserves_composition_fri_future_fresh
            [OF trace_fri future_s1])
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
        have future_s3: "composition_fri_future_fresh s3"
          by (rule read_preserves_composition_fri_future_fresh
              [OF future_s2 read_final])
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
          have future_s4: "composition_fri_future_fresh s4"
            by (rule mmap_alpha_round_preserves_composition_fri_future_fresh
                [OF future_s3 alpha])
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
            have future_s5: "composition_fri_future_fresh s5"
              by (rule read_preserves_composition_fri_future_fresh
                  [OF future_s4 read_dg])
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
              have future_s6: "composition_fri_future_fresh s6"
                using future_s5 unfolding s6_eq .
              let ?Head =
                "\<lambda>out. case out of
                    None \<Rightarrow> False
                  | Some (fl, _) \<Rightarrow>
                      map fst fl \<in> B fr f_fl f_final as dg (map snd fl)"
              have comp_bound_C:
                "wp_event
                  (ntimes receive_composition_fri_commits
                    (ceil_log (to_nat dg + 1)))
                  ?Head s6 \<le> C"
                by (rule
                    wp_ntimes_receive_composition_fri_commits_root_dependent_bound
                    [where B = "B fr f_fl f_final as dg",
                      OF future_s6])
                  (use subset bound in simp_all)
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
                assume cont:
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
                show "?Head (Some (fl, t))"
                  using hit unfolding out_eq by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma verifier_alpha_prefix_outcome:
  assumes outcome:
    "Some ((fr, f_fl, f_final, as), t) \<in>
      set_dist (execute verifier_alpha_prefix s)"
  shows
    "length f_fl = ceil_log clength \<and>
     length as = length spec \<and>
     PTranscript s =
       [fr] @ map snd f_fl @ [f_final] @ as @ PTranscript t \<and>
     PState t =
       foldl concat
        (concat (foldl concat (concat (PState s) fr) (map snd f_fl))
          f_final)
        as \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  from outcome obtain s1 s2 s3 s4 where
    read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    and trace_fri:
      "Some (f_fl, s2) \<in>
        set_dist (execute
          (ntimes receive_trace_fri_commits (ceil_log clength)) s1)"
    and read_final: "Some (f_final, s3) \<in> set_dist (execute read s2)"
    and alpha_out:
      "Some (as, s4) \<in>
        set_dist (execute (mmap (replicate (length spec) alpha_round)) s3)"
    and ret:
      "Some ((fr, f_fl, f_final, as), t) \<in>
        set_dist (execute (return (fr, f_fl, f_final, as)) s4)"
    unfolding verifier_alpha_prefix_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_fr] obtain rest1 where
    tr_s: "PTranscript s = fr # rest1"
    and st_s1: "PState s1 = concat (PState s) fr"
    and tr_s1: "PTranscript s1 = rest1"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  have trace_res:
    "length f_fl = ceil_log clength \<and>
     PTranscript s1 = map snd f_fl @ PTranscript s2 \<and>
     PState s2 = foldl concat (PState s1) (map snd f_fl) \<and>
     PQueryCounter s2 = PQueryCounter s1"
    using ntimes_receive_trace_fri_commits_outcome[OF trace_fri] by simp
  from read_outcome[OF read_final] obtain rest3 where
    tr_s2: "PTranscript s2 = f_final # rest3"
    and st_s3: "PState s3 = concat (PState s2) f_final"
    and tr_s3: "PTranscript s3 = rest3"
    and query_count_s3: "PQueryCounter s3 = PQueryCounter s2"
    by blast
  have alpha_res:
    "length as = length spec \<and>
     PTranscript s3 = as @ PTranscript s4 \<and>
     PState s4 = foldl concat (PState s3) as \<and>
     PQueryCounter s4 = PQueryCounter s3"
    using mmap_alpha_round_outcome[OF alpha_out] by simp
  have t_eq: "t = s4"
    using ret by simp
  show ?thesis
    using tr_s tr_s1 trace_res tr_s2 tr_s3 alpha_res st_s1 st_s3
      query_count_s1 query_count_s3 t_eq
    by simp
qed

lemma verifier_trace_fri_prefix_outcome:
  assumes outcome:
    "Some ((fr, f_fl), t) \<in>
      set_dist (execute verifier_trace_fri_prefix s)"
  shows
    "length f_fl = ceil_log clength \<and>
     PTranscript s = [fr] @ map snd f_fl @ PTranscript t \<and>
     PState t = foldl concat (concat (PState s) fr) (map snd f_fl) \<and>
     s \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s + ceil_log clength \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s \<and>
     (\<forall>i < length f_fl.
        fmlookup (HashMap t)
          (TraceFriChallenge (PTraceFriCounter s + i)
            (foldl concat (concat (PState s) fr)
              (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i)))"
proof -
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
  from read_outcome[OF read_fr] obtain rest1 where
    tr_s: "PTranscript s = fr # rest1"
    and st_s1: "PState s1 = concat (PState s) fr"
    and tr_s1: "PTranscript s1 = rest1"
    and ext_s_s1: "s \<le> s1"
    and trace_count_s1: "PTraceFriCounter s1 = PTraceFriCounter s"
    and comp_count_s1: "PCompositionFriCounter s1 = PCompositionFriCounter s"
    and alpha_count_s1: "PAlphaCounter s1 = PAlphaCounter s"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  have trace_res:
    "length f_fl = ceil_log clength \<and>
     PTranscript s1 = map snd f_fl @ PTranscript s2 \<and>
     PState s2 = foldl concat (PState s1) (map snd f_fl) \<and>
     s1 \<le> s2 \<and>
     PTraceFriCounter s2 = PTraceFriCounter s1 + ceil_log clength \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
     PAlphaCounter s2 = PAlphaCounter s1 \<and>
     PQueryCounter s2 = PQueryCounter s1 \<and>
     (\<forall>i < ceil_log clength.
        fmlookup (HashMap s2)
          (TraceFriChallenge (PTraceFriCounter s1 + i)
            (foldl concat (PState s1) (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i)))"
    using ntimes_receive_trace_fri_commits_outcome[OF trace_fri] by simp
  have t_eq: "t = s2"
    using ret by simp
  have ext_s_t: "s \<le> t"
    using ext_s_s1 trace_res t_eq by (meson hash_ext_trans)
  have lookups:
    "\<forall>i < length f_fl.
      fmlookup (HashMap t)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
    using trace_res st_s1 trace_count_s1 t_eq by simp
  show ?thesis
    using tr_s tr_s1 st_s1 trace_res t_eq ext_s_t trace_count_s1
      comp_count_s1 alpha_count_s1 query_count_s1 lookups
    by simp
qed

lemma verifier_composition_fri_prefix_outcome:
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
proof -
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
  from read_outcome[OF read_fr] obtain rest1 where
    tr_s: "PTranscript s = fr # rest1"
    and st_s1: "PState s1 = concat (PState s) fr"
    and tr_s1: "PTranscript s1 = rest1"
    and ext_s_s1: "s \<le> s1"
    and trace_count_s1: "PTraceFriCounter s1 = PTraceFriCounter s"
    and comp_count_s1: "PCompositionFriCounter s1 = PCompositionFriCounter s"
    and alpha_count_s1: "PAlphaCounter s1 = PAlphaCounter s"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  have trace_res:
    "length f_fl = ceil_log clength \<and>
     PTranscript s1 = map snd f_fl @ PTranscript s2 \<and>
     PState s2 = foldl concat (PState s1) (map snd f_fl) \<and>
     s1 \<le> s2 \<and>
     PTraceFriCounter s2 = PTraceFriCounter s1 + ceil_log clength \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
     PAlphaCounter s2 = PAlphaCounter s1 \<and>
     PQueryCounter s2 = PQueryCounter s1 \<and>
     (\<forall>i < ceil_log clength.
        fmlookup (HashMap s2)
          (TraceFriChallenge (PTraceFriCounter s1 + i)
            (foldl concat (PState s1) (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i)))"
    using ntimes_receive_trace_fri_commits_outcome[OF trace_fri] by simp
  from read_outcome[OF read_f_final] obtain rest3 where
    tr_s2: "PTranscript s2 = f_final # rest3"
    and st_s3: "PState s3 = concat (PState s2) f_final"
    and tr_s3: "PTranscript s3 = rest3"
    and ext_s2_s3: "s2 \<le> s3"
    and comp_count_s3: "PCompositionFriCounter s3 = PCompositionFriCounter s2"
    and query_count_s3: "PQueryCounter s3 = PQueryCounter s2"
    by blast
  have alpha_res:
    "length as = length spec \<and>
     PTranscript s3 = as @ PTranscript s4 \<and>
     PState s4 = foldl concat (PState s3) as \<and>
     s3 \<le> s4 \<and>
     PCompositionFriCounter s4 = PCompositionFriCounter s3 \<and>
     PQueryCounter s4 = PQueryCounter s3"
    using mmap_alpha_round_outcome[OF alpha_out] by simp
  from read_outcome[OF read_dg] obtain rest5 where
    tr_s4: "PTranscript s4 = dg # rest5"
    and st_s5: "PState s5 = concat (PState s4) dg"
    and tr_s5: "PTranscript s5 = rest5"
    and ext_s4_s5: "s4 \<le> s5"
    and comp_count_s5: "PCompositionFriCounter s5 = PCompositionFriCounter s4"
    and query_count_s5: "PQueryCounter s5 = PQueryCounter s4"
    by blast
  have s6_eq: "s6 = s5"
    using degree_assert unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
  have ext_s5_s6: "s5 \<le> s6"
    unfolding s6_eq by (rule hash_ext_refl)
  have comp_res:
    "length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s6 = map snd fl @ PTranscript s7 \<and>
     PState s7 = foldl concat (PState s6) (map snd fl) \<and>
     s6 \<le> s7 \<and>
     PCompositionFriCounter s7 =
        PCompositionFriCounter s6 + ceil_log (to_nat dg + 1) \<and>
     PQueryCounter s7 = PQueryCounter s6 \<and>
     (\<forall>i < ceil_log (to_nat dg + 1).
        fmlookup (HashMap s7)
          (CompositionFriChallenge (PCompositionFriCounter s6 + i)
            (foldl concat (PState s6) (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i)))"
    using ntimes_receive_composition_fri_commits_outcome[OF comp_fri]
    by simp
  have t_eq: "t = s7"
    using ret by simp
  have ext_s_t: "s \<le> t"
    using ext_s_s1 trace_res ext_s2_s3 alpha_res ext_s4_s5 ext_s5_s6
      comp_res t_eq
    by (meson hash_ext_trans)
  have ext_s2_t: "s2 \<le> t"
    using ext_s2_s3 alpha_res ext_s4_s5 ext_s5_s6 comp_res t_eq
    by (meson hash_ext_trans)
  have trace_lookup:
    "\<forall>i < length f_fl.
      fmlookup (HashMap t)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length f_fl"
    have lookup_s2:
      "fmlookup (HashMap s2)
        (TraceFriChallenge (PTraceFriCounter s1 + i)
          (foldl concat (PState s1) (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
      using trace_res i_bound by simp
    show "fmlookup (HashMap t)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
      using hash_extension_lookup[OF lookup_s2 ext_s2_t] st_s1
        trace_count_s1
      by simp
  qed
  have comp_lookup:
    "\<forall>i < length fl.
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
      Some (fst (fl ! i))"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length fl"
    have lookup_s7:
      "fmlookup (HashMap s7)
        (CompositionFriChallenge (PCompositionFriCounter s6 + i)
          (foldl concat (PState s6) (take (Suc i) (map snd fl)))) =
      Some (fst (fl ! i))"
      using comp_res i_bound by simp
    show "fmlookup (HashMap t)
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
      Some (fst (fl ! i))"
      using lookup_s7 t_eq st_s1 trace_res st_s3 alpha_res st_s5 s6_eq
        comp_count_s1 comp_count_s3 comp_count_s5
      by simp
  qed
  have query_count_t: "PQueryCounter t = PQueryCounter s"
    using query_count_s1 trace_res query_count_s3 alpha_res query_count_s5
      s6_eq comp_res t_eq
    by simp
  show ?thesis
    using tr_s tr_s1 trace_res tr_s2 tr_s3 alpha_res tr_s4 tr_s5 s6_eq
      comp_res st_s1 st_s3 st_s5 t_eq ext_s_t query_count_t trace_lookup
      comp_lookup
    by simp
qed

end

end
