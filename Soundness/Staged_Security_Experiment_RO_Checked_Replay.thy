theory Staged_Security_Experiment_RO_Checked_Replay
  imports Staged_Security_Experiment_RO_Checked
begin

primrec ro_absorb_lookup_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> bool"
where
  "ro_absorb_lookup_chain s st [] final \<longleftrightarrow> final = st"
| "ro_absorb_lookup_chain s st (x # xs) final \<longleftrightarrow>
    (\<exists>st'.
      fmlookup (HashMap s) (TranscriptAbsorb st x) = Some st' \<and>
      ro_absorb_lookup_chain s st' xs final)"

lemma ro_absorb_lookup_chain_mono:
  assumes chain: "ro_absorb_lookup_chain s st xs final"
    and ext: "s \<le> t"
  shows "ro_absorb_lookup_chain t st xs final"
  using chain
proof (induction xs arbitrary: st)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then obtain st' where
    lookup_s: "fmlookup (HashMap s) (TranscriptAbsorb st x) = Some st'"
    and tail_s: "ro_absorb_lookup_chain s st' xs final"
    by auto
  have lookup_t:
    "fmlookup (HashMap t) (TranscriptAbsorb st x) = Some st'"
    by (rule protocol_merkle.hash_extension_lookup[OF lookup_s ext])
  have tail_t: "ro_absorb_lookup_chain t st' xs final"
    by (rule Cons.IH[OF tail_s])
  show ?case
    using lookup_t tail_t by auto
qed

lemma ro_absorb_lookup_chain_append:
  assumes first: "ro_absorb_lookup_chain s st xs mid"
    and second: "ro_absorb_lookup_chain s mid ys final"
  shows "ro_absorb_lookup_chain s st (xs @ ys) final"
  using first
proof (induction xs arbitrary: st)
  case Nil
  then show ?case
    using second by simp
next
  case (Cons x xs)
  then obtain st' where
    lookup: "fmlookup (HashMap s) (TranscriptAbsorb st x) = Some st'"
    and tail: "ro_absorb_lookup_chain s st' xs mid"
    by auto
  have tail_append: "ro_absorb_lookup_chain s st' (xs @ ys) final"
    by (rule Cons.IH[OF tail])
  show ?case
    using lookup tail_append by auto
qed

text \<open>RO-checked staged transcript replay facts that do not rely on
  deterministic `foldl concat` transcript-state equations.\<close>

context soundness
begin

lemma controlled_ro_program_hash_extension_preserving:
  assumes controlled: "controlled_ro_program q m"
  shows "hash_extension_preserving m"
  using controlled
proof (induction rule: controlled_ro_program.induct)
  case (Return x)
  then show ?case
    by (rule hash_extension_preserving_return)
next
  case Fail
  then show ?case
    unfolding hash_extension_preserving_def
    by (simp add: throw_no_outcome)
next
  case (Sample d)
  then show ?case
    unfolding hash_extension_preserving_def lift.rep_eq lift_dist_def
    by (auto simp: set_dist_dist_map hash_ext_refl)
next
  case (Query q k x)
  have hash_ext:
    "hash_extension_preserving
      (hash x :: ('f, 'f protocol_channel) state_monad)"
    by (rule hash_extension_preserving_hash)
  have cont_ext: "\<And>y. hash_extension_preserving (k y)"
    using Query.IH by simp
  show ?case
    by (rule hash_extension_preserving_bind[OF hash_ext cont_ext])
next
  case (Bind q m r k)
  have m_ext: "hash_extension_preserving m"
    using Bind.IH(1) .
  have k_ext: "\<And>x. hash_extension_preserving (k x)"
    using Bind.IH(2) by simp
  show ?case
    by (rule hash_extension_preserving_bind[OF m_ext k_ext])
next
  case (Weaken q m r)
  then show ?case
    by simp
qed

lemma protocol_absorb_read_known_nonempty_outcome:
  assumes tr: "PTranscript r = x # xs"
    and lookup:
      "fmlookup (HashMap r) (TranscriptAbsorb (PState r) x) =
        Some absorbed"
    and outcome:
      "Some (y, t) \<in> set_dist (execute protocol_absorb_read r)"
  shows
    "y = x \<and> PState t = absorbed \<and> PTranscript t = xs \<and> r \<le> t"
proof -
  let ?s = "r\<lparr>PTranscript := []\<rparr>"
  have r_eq: "r = ?s\<lparr>PTranscript := x # xs\<rparr>"
    using tr by simp
  from outcome have outcome':
    "Some (y, t) \<in>
      set_dist (execute protocol_absorb_read (?s\<lparr>PTranscript := x # xs\<rparr>))"
    using r_eq by simp
  obtain h' u where
    y_eq: "y = x"
    and hash_out:
      "Some (h', u) \<in>
        set_dist
          (execute (hash (TranscriptAbsorb (PState ?s) x))
            (?s\<lparr>PTranscript := x # xs\<rparr>))"
    and t_eq: "t = u\<lparr>PState := h', PTranscript := xs\<rparr>"
    and ext_start_u: "?s\<lparr>PTranscript := x # xs\<rparr> \<le> u"
  proof (rule protocol_absorb_read_cons_outcome[OF outcome'])
    fix h' u
    assume y_eq': "y = x"
      and hash_out':
        "Some (h', u) \<in>
          set_dist
            (execute (hash (TranscriptAbsorb (PState ?s) x))
              (?s\<lparr>PTranscript := x # xs\<rparr>))"
      and t_eq': "t = u\<lparr>PState := h', PTranscript := xs\<rparr>"
      and "PState u = PState ?s"
      and "PTranscript u = x # xs"
      and ext_start_u': "?s\<lparr>PTranscript := x # xs\<rparr> \<le> u"
    show ?thesis
      by (rule that[OF y_eq' hash_out' t_eq' ext_start_u'])
  qed
  have ext_r_u: "r \<le> u"
    using ext_start_u r_eq by simp
  have lookup_u_old:
    "fmlookup (HashMap u) (TranscriptAbsorb (PState r) x) =
      Some absorbed"
    by (rule hash_extension_lookup[OF lookup ext_r_u])
  have lookup_u_new:
    "fmlookup (HashMap u) (TranscriptAbsorb (PState r) x) = Some h'"
    using protocol_merkle.hash_outcome(2)[OF hash_out] by simp
  have h'_eq: "h' = absorbed"
    using lookup_u_old lookup_u_new by simp
  have ext_u_t: "u \<le> t"
    unfolding t_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have ext_r_t: "r \<le> t"
    by (rule hash_ext_trans[OF ext_r_u ext_u_t])
  show ?thesis
    using y_eq t_eq h'_eq ext_r_t by simp
qed

lemma ro_absorb_lookup_chain_replay_from_extension:
  assumes chain: "ro_absorb_lookup_chain sent start xs final"
    and start_ext: "sent \<le> r"
    and start_state: "PState r = start"
    and start_tr: "PTranscript r = xs @ rest"
    and replay:
      "Some (ys, out) \<in>
        set_dist (execute (ntimes protocol_absorb_read (length xs)) r)"
  shows
    "ys = xs \<and> PState out = final \<and> PTranscript out = rest \<and> sent \<le> out"
  using chain start_ext start_state start_tr replay
proof (induction xs arbitrary: start final r ys out rest)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  from Cons.prems(1) obtain next_state where
    lookup_sent:
      "fmlookup (HashMap sent) (TranscriptAbsorb start x) = Some next_state"
    and tail_chain: "ro_absorb_lookup_chain sent next_state xs final"
    by auto
  from Cons.prems(5) obtain y r1 ys_tail where
    read_head:
      "Some (y, r1) \<in> set_dist (execute protocol_absorb_read r)"
    and replay_tail:
      "Some (ys_tail, out) \<in>
        set_dist (execute (ntimes protocol_absorb_read (length xs)) r1)"
    and ys_eq: "ys = y # ys_tail"
    by (auto elim!: set_dist_bindE)
  have lookup_r_old:
    "fmlookup (HashMap r) (TranscriptAbsorb start x) = Some next_state"
    by (rule hash_extension_lookup[OF lookup_sent Cons.prems(2)])
  have lookup_r:
    "fmlookup (HashMap r) (TranscriptAbsorb (PState r) x) = Some next_state"
    using lookup_r_old Cons.prems(3) by simp
  have tr_r: "PTranscript r = x # (xs @ rest)"
    using Cons.prems(4) by simp
  have read_props:
    "y = x \<and> PState r1 = next_state \<and>
      PTranscript r1 = xs @ rest \<and> r \<le> r1"
    by (rule protocol_absorb_read_known_nonempty_outcome
        [where xs = "xs @ rest", OF tr_r lookup_r read_head])
  have read_ext: "r \<le> r1"
    using read_props by simp
  have ext_sent_r1: "sent \<le> r1"
    by (rule hash_ext_trans[OF Cons.prems(2) read_ext])
  have state_r1: "PState r1 = next_state"
    using read_props by simp
  have tr_r1: "PTranscript r1 = xs @ rest"
    using read_props by simp
  have tail_props:
    "ys_tail = xs \<and> PState out = final \<and> PTranscript out = rest \<and> sent \<le> out"
    by (rule Cons.IH[OF tail_chain ext_sent_r1 state_r1 tr_r1 replay_tail])
  show ?case
    using ys_eq read_props tail_props by simp
qed

lemma protocol_absorb_read_known_nonempty_support:
  assumes tr: "PTranscript r = x # xs"
    and lookup:
      "fmlookup (HashMap r) (TranscriptAbsorb (PState r) x) =
        Some absorbed"
  shows
    "Some (x, r\<lparr>PState := absorbed, PTranscript := xs\<rparr>) \<in>
      set_dist (execute protocol_absorb_read r)"
proof -
  let ?key = "TranscriptAbsorb (PState r) x"
  have fmap_update_eq: "fmupd ?key absorbed (HashMap r) = HashMap r"
  proof (rule fmap_ext)
    fix z
    show "fmlookup (fmupd ?key absorbed (HashMap r)) z =
      fmlookup (HashMap r) z"
      using lookup by (cases "z = ?key") simp_all
  qed
  have state_update_eq:
    "r\<lparr>HashMap := fmupd ?key absorbed (HashMap r)\<rparr> = r"
    using fmap_update_eq by simp
  have apply_support:
    "Some (absorbed, r) \<in> set_dist (execute (apply_hash ?key) r)"
    using lookup
    unfolding apply_hash_def hash_dist_def option_default_dist_def
      lift.rep_eq lift_dist_def
    by (simp add: set_dist_dist_map set_dist_def dist_delta_dist delta_map_def)
  have get_support:
    "Some (r, r) \<in> set_dist (execute get r)"
    unfolding set_dist_def get.rep_eq dist_get_def dist_delta_dist delta_map_def
    by simp
  have put_support:
    "Some ((), r) \<in> set_dist (execute (put r) r)"
    unfolding set_dist_def put.rep_eq dist_put_def dist_delta_dist delta_map_def
    by simp
  have modify_support:
    "Some ((), r) \<in> set_dist (execute (modify_HashMap ?key absorbed) r)"
    unfolding modify_HashMap_def modify_def
    apply (rule set_dist_bindI[OF get_support])
    using put_support state_update_eq
    apply simp
    done
  have hash_support:
    "Some (absorbed, r) \<in> set_dist (execute (hash ?key) r)"
    unfolding hash_def
    apply (rule set_dist_bindI[OF apply_support])
    apply (rule set_dist_bindI[OF modify_support])
    apply simp
    done
  have assert_support:
    "Some ((), r) \<in>
      set_dist (execute (assert (PTranscript r \<noteq> [])) r)"
    using tr unfolding assert_def by simp
  have hash_support_hd:
    "Some (absorbed, r) \<in>
      set_dist
        (execute (hash (TranscriptAbsorb (PState r) (hd (PTranscript r)))) r)"
    using hash_support tr by simp
  have put_absorb_support:
    "Some ((), r\<lparr>PState := absorbed, PTranscript := xs\<rparr>) \<in>
      set_dist
        (execute (put (r\<lparr>PState := absorbed, PTranscript := xs\<rparr>)) r)"
    unfolding set_dist_def put.rep_eq dist_put_def dist_delta_dist delta_map_def
    by simp
  have modify_read_support:
    "Some ((), r\<lparr>PState := absorbed, PTranscript := xs\<rparr>) \<in>
      set_dist
        (execute
          (modify
            (\<lambda>s. s\<lparr>PState := absorbed,
              PTranscript := tl (PTranscript s)\<rparr>)) r)"
    unfolding modify_def
    apply (rule set_dist_bindI[OF get_support])
    using put_absorb_support tr
    apply simp
    done
  have return_read_support:
    "Some (x, r\<lparr>PState := absorbed, PTranscript := xs\<rparr>) \<in>
      set_dist
        (execute (return (hd (PTranscript r)))
          (r\<lparr>PState := absorbed, PTranscript := xs\<rparr>))"
    using tr by simp
  show ?thesis
    unfolding protocol_absorb_read_def
    apply (rule set_dist_bindI[OF get_support])
    apply (rule set_dist_bindI[OF assert_support])
    apply (rule set_dist_bindI[OF hash_support_hd])
    apply (rule set_dist_bindI[OF modify_read_support])
    using return_read_support
    apply simp
    done
qed

lemma ro_absorb_lookup_chain_replay_support_from_extension:
  assumes chain: "ro_absorb_lookup_chain sent start xs final"
    and start_ext: "sent \<le> r"
    and start_state: "PState r = start"
    and start_tr: "PTranscript r = xs @ rest"
  shows
    "Some (xs, r\<lparr>PState := final, PTranscript := rest\<rparr>) \<in>
      set_dist (execute (ntimes protocol_absorb_read (length xs)) r)"
  using chain start_ext start_state start_tr
proof (induction xs arbitrary: start final r rest)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  from Cons.prems(1) obtain next_state where
    lookup_sent:
      "fmlookup (HashMap sent) (TranscriptAbsorb start x) = Some next_state"
    and tail_chain: "ro_absorb_lookup_chain sent next_state xs final"
    by auto
  have lookup_r_old:
    "fmlookup (HashMap r) (TranscriptAbsorb start x) = Some next_state"
    by (rule hash_extension_lookup[OF lookup_sent Cons.prems(2)])
  have lookup_r:
    "fmlookup (HashMap r) (TranscriptAbsorb (PState r) x) = Some next_state"
    using lookup_r_old Cons.prems(3) by simp
  have tr_r: "PTranscript r = x # (xs @ rest)"
    using Cons.prems(4) by simp
  let ?r1 = "r\<lparr>PState := next_state, PTranscript := xs @ rest\<rparr>"
  have head_support:
    "Some (x, ?r1) \<in> set_dist (execute protocol_absorb_read r)"
    by (rule protocol_absorb_read_known_nonempty_support
        [where xs = "xs @ rest", OF tr_r lookup_r])
  have ext_r_r1: "r \<le> ?r1"
    unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have ext_sent_r1: "sent \<le> ?r1"
    by (rule hash_ext_trans[OF Cons.prems(2) ext_r_r1])
  have tail_support:
    "Some (xs, ?r1\<lparr>PState := final, PTranscript := rest\<rparr>) \<in>
      set_dist (execute (ntimes protocol_absorb_read (length xs)) ?r1)"
    by (rule Cons.IH[OF tail_chain ext_sent_r1]) simp_all
  have bind_support:
    "Some (x # xs, ?r1\<lparr>PState := final, PTranscript := rest\<rparr>) \<in>
      set_dist
        (execute
          (protocol_absorb_read \<bind>
            (\<lambda>y. ntimes protocol_absorb_read (length xs) \<bind>
              (\<lambda>ys. return (y # ys)))) r)"
    apply (rule set_dist_bindI[OF head_support])
    apply (rule set_dist_bindI[OF tail_support])
    apply simp
    done
  show ?case
    using bind_support by simp
qed

lemma ro_record_staged_message_absorb_lookup_state:
  assumes outcome:
    "Some ((), t) \<in> set_dist (execute (ro_record_staged_message x) s)"
  shows
    "fmlookup (HashMap t) (TranscriptAbsorb (PState s) x) =
      Some (PState t) \<and> s \<le> t"
proof -
  obtain h u where
    hash_out:
      "Some (h, u) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState s) x)) s)"
    and t_eq: "t = u\<lparr>PState := h, PTranscript := PTranscript u @ [x]\<rparr>"
    and ext_s_u: "s \<le> u"
  proof (rule ro_record_staged_message_outcome[OF outcome])
    fix h u
    assume hash_out':
      "Some (h, u) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState s) x)) s)"
      and t_eq': "t = u\<lparr>PState := h, PTranscript := PTranscript u @ [x]\<rparr>"
      and "PState u = PState s"
      and "PTranscript u = PTranscript s"
      and "PTraceFriCounter u = PTraceFriCounter s"
      and "PCompositionFriCounter u = PCompositionFriCounter s"
      and "PAlphaCounter u = PAlphaCounter s"
      and "PQueryCounter u = PQueryCounter s"
      and ext_s_u': "s \<le> u"
    show ?thesis
      by (rule that[OF hash_out' t_eq' ext_s_u'])
  qed
  have lookup_u:
    "fmlookup (HashMap u) (TranscriptAbsorb (PState s) x) = Some h"
    using protocol_merkle.hash_outcome(2)[OF hash_out] .
  have lookup_t:
    "fmlookup (HashMap t) (TranscriptAbsorb (PState s) x) = Some h"
    using lookup_u t_eq by simp
  have state_t: "PState t = h"
    using t_eq by simp
  have ext_u_t: "u \<le> t"
    unfolding t_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_u ext_u_t])
  show ?thesis
    using lookup_t state_t ext_s_t by simp
qed

lemma ro_record_staged_messages_absorb_lookup_chain:
  assumes outcome:
    "Some ((), t) \<in> set_dist (execute (ro_record_staged_messages xs) s)"
  shows "ro_absorb_lookup_chain t (PState s) xs (PState t) \<and> s \<le> t"
  using outcome
proof (induction xs arbitrary: s t)
  case Nil
  then show ?case
    unfolding ro_record_staged_messages_def
    by (simp add: hash_ext_refl)
next
  case (Cons x xs)
  from Cons.prems obtain s1 where
    head:
      "Some ((), s1) \<in>
        set_dist (execute (ro_record_staged_message x) s)"
    and tail:
      "Some ((), t) \<in>
        set_dist (execute (ro_record_staged_messages xs) s1)"
    unfolding ro_record_staged_messages_def
    by (auto elim!: set_dist_bindE)
  have head_props:
    "fmlookup (HashMap s1) (TranscriptAbsorb (PState s) x) =
      Some (PState s1) \<and> s \<le> s1"
    by (rule ro_record_staged_message_absorb_lookup_state[OF head])
  have tail_props:
    "ro_absorb_lookup_chain t (PState s1) xs (PState t) \<and> s1 \<le> t"
    by (rule Cons.IH[OF tail])
  have lookup_t:
    "fmlookup (HashMap t) (TranscriptAbsorb (PState s) x) =
      Some (PState s1)"
    by (rule hash_extension_lookup[OF conjunct1[OF head_props]
          conjunct2[OF tail_props]])
  have chain_t:
    "ro_absorb_lookup_chain t (PState s) (x # xs) (PState t)"
    using lookup_t tail_props by auto
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF conjunct2[OF head_props]
          conjunct2[OF tail_props]])
  show ?case
    using chain_t ext_s_t by simp
qed

lemma ro_staged_alpha_program_absorb_lookup_chain:
  assumes outcome:
    "Some (as, t) \<in> set_dist (execute (ro_staged_alpha_program n) s)"
  shows "ro_absorb_lookup_chain t (PState s) as (PState t) \<and> s \<le> t"
  using outcome
proof (induction n arbitrary: s as t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain a s1 s2 as_tail where
    challenge_out:
      "Some (a, s1) \<in> set_dist (execute receive_alpha_challenge s)"
    and record_out:
      "Some ((), s2) \<in> set_dist (execute (ro_record_staged_message a) s1)"
    and tail_out:
      "Some (as_tail, t) \<in> set_dist (execute (ro_staged_alpha_program n) s2)"
    and as_eq: "as = a # as_tail"
    by (auto elim!: set_dist_bindE)
  have challenge_props:
    "s \<le> s1 \<and> PState s1 = PState s \<and> PTranscript s1 = PTranscript s \<and>
      fmlookup (HashMap s1)
        (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using receive_alpha_challenge_outcome[OF challenge_out] by simp
  have record_props:
    "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) a) =
      Some (PState s2) \<and> s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF record_out])
  have tail_props:
    "ro_absorb_lookup_chain t (PState s2) as_tail (PState t) \<and> s2 \<le> t"
    by (rule Suc.IH[OF tail_out])
  have lookup_t_old:
    "fmlookup (HashMap t) (TranscriptAbsorb (PState s1) a) =
      Some (PState s2)"
    by (rule hash_extension_lookup[OF conjunct1[OF record_props]
          conjunct2[OF tail_props]])
  have lookup_t:
    "fmlookup (HashMap t) (TranscriptAbsorb (PState s) a) =
      Some (PState s2)"
    using lookup_t_old challenge_props by simp
  have chain_t: "ro_absorb_lookup_chain t (PState s) as (PState t)"
    unfolding as_eq using lookup_t tail_props by auto
  have ext_s_s2: "s \<le> s2"
    by (rule hash_ext_trans[OF conjunct1[OF challenge_props]
          conjunct2[OF record_props]])
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_s2 conjunct2[OF tail_props]])
  show ?case
    using chain_t ext_s_t by simp
qed

lemma ro_staged_trace_fri_program_absorb_lookup_chain:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (trace_fri_budgets budgets)"
    and outcome:
      "Some ((roots, bs'), t) \<in>
        set_dist
          (execute (ro_staged_trace_fri_program A i n bs) s)"
  shows "ro_absorb_lookup_chain t (PState s) roots (PState t) \<and> s \<le> t"
  using bound outcome
proof (induction n arbitrary: i bs s roots bs' t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(2) obtain root s1 s2 b s3 roots_tail bs_tail where
    stage_out:
      "Some (root, s1) \<in>
        set_dist (execute (trace_fri_root_stage A i bs) s)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in>
        set_dist (execute receive_trace_fri_challenge s2)"
    and tail_out:
      "Some ((roots_tail, bs_tail), t) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A (Suc i) n (bs @ [b])) s3)"
    and roots_eq: "roots = root # roots_tail"
    and bs'_eq: "bs' = bs_tail"
    unfolding ro_staged_trace_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  have i_bound: "i < length (trace_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have stage_ext: "s \<le> s1"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have stage_state: "PState s1 = PState s"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have record_props:
    "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) root) =
      Some (PState s2) \<and> s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF record_out])
  have challenge_props:
    "s2 \<le> s3 \<and> PState s3 = PState s2"
    using receive_trace_fri_challenge_outcome[OF challenge_out] by simp
  have tail_bound:
    "Suc i + n \<le> length (trace_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_props:
    "ro_absorb_lookup_chain t (PState s3) roots_tail (PState t) \<and> s3 \<le> t"
    by (rule Suc.IH[OF tail_bound tail_out])
  have ext_s2_t: "s2 \<le> t"
    by (rule hash_ext_trans[OF conjunct1[OF challenge_props]
          conjunct2[OF tail_props]])
  have lookup_t_old:
    "fmlookup (HashMap t) (TranscriptAbsorb (PState s1) root) =
      Some (PState s2)"
    by (rule hash_extension_lookup[OF conjunct1[OF record_props] ext_s2_t])
  have lookup_t:
    "fmlookup (HashMap t) (TranscriptAbsorb (PState s) root) =
      Some (PState s2)"
    using lookup_t_old stage_state by simp
  have tail_chain:
    "ro_absorb_lookup_chain t (PState s2) roots_tail (PState t)"
    using tail_props challenge_props by simp
  have chain_t:
    "ro_absorb_lookup_chain t (PState s) roots (PState t)"
    unfolding roots_eq using lookup_t tail_chain by auto
  have ext_s_s2: "s \<le> s2"
    by (rule hash_ext_trans[OF stage_ext conjunct2[OF record_props]])
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_s2 ext_s2_t])
  show ?case
    using chain_t ext_s_t by simp
qed

lemma ro_staged_composition_fri_program_absorb_lookup_chain:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (composition_fri_budgets budgets)"
    and outcome:
      "Some ((roots, bs'), t) \<in>
        set_dist
          (execute (ro_staged_composition_fri_program A dg i n bs) s)"
  shows "ro_absorb_lookup_chain t (PState s) roots (PState t) \<and> s \<le> t"
  using bound outcome
proof (induction n arbitrary: i bs s roots bs' t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(2) obtain root s1 s2 b s3 roots_tail bs_tail where
    stage_out:
      "Some (root, s1) \<in>
        set_dist (execute (composition_fri_root_stage A dg i bs) s)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message root) s1)"
    and challenge_out:
      "Some (b, s3) \<in>
        set_dist (execute receive_composition_fri_challenge s2)"
    and tail_out:
      "Some ((roots_tail, bs_tail), t) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg (Suc i) n
              (bs @ [b])) s3)"
    and roots_eq: "roots = root # roots_tail"
    and bs'_eq: "bs' = bs_tail"
    unfolding ro_staged_composition_fri_program.simps
    by (auto elim!: set_dist_bindE split: prod.splits)
  have i_bound: "i < length (composition_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have stage_ext: "s \<le> s1"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have stage_state: "PState s1 = PState s"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have record_props:
    "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) root) =
      Some (PState s2) \<and> s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF record_out])
  have challenge_props:
    "s2 \<le> s3 \<and> PState s3 = PState s2"
    using receive_composition_fri_challenge_outcome[OF challenge_out]
    by simp
  have tail_bound:
    "Suc i + n \<le> length (composition_fri_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_props:
    "ro_absorb_lookup_chain t (PState s3) roots_tail (PState t) \<and> s3 \<le> t"
    by (rule Suc.IH[OF tail_bound tail_out])
  have ext_s2_t: "s2 \<le> t"
    by (rule hash_ext_trans[OF conjunct1[OF challenge_props]
          conjunct2[OF tail_props]])
  have lookup_t_old:
    "fmlookup (HashMap t) (TranscriptAbsorb (PState s1) root) =
      Some (PState s2)"
    by (rule hash_extension_lookup[OF conjunct1[OF record_props] ext_s2_t])
  have lookup_t:
    "fmlookup (HashMap t) (TranscriptAbsorb (PState s) root) =
      Some (PState s2)"
    using lookup_t_old stage_state by simp
  have tail_chain:
    "ro_absorb_lookup_chain t (PState s2) roots_tail (PState t)"
    using tail_props challenge_props by simp
  have chain_t:
    "ro_absorb_lookup_chain t (PState s) roots (PState t)"
    unfolding roots_eq using lookup_t tail_chain by auto
  have ext_s_s2: "s \<le> s2"
    by (rule hash_ext_trans[OF stage_ext conjunct2[OF record_props]])
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_s2 ext_s2_t])
  show ?case
    using chain_t ext_s_t by simp
qed

lemma ro_record_staged_message_hash_extends_query_counter:
  assumes outcome:
    "Some ((), t) \<in> set_dist (execute (ro_record_staged_message x) s)"
  shows "s \<le> t \<and> PQueryCounter t = PQueryCounter s"
proof -
  obtain h u where
    t_eq: "t = u\<lparr>PState := h, PTranscript := PTranscript u @ [x]\<rparr>"
    and counter_u: "PQueryCounter u = PQueryCounter s"
    and ext_s_u: "s \<le> u"
  proof (rule ro_record_staged_message_outcome[OF outcome])
    fix h u
    assume "Some (h, u) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState s) x)) s)"
      and t_eq':
        "t = u\<lparr>PState := h, PTranscript := PTranscript u @ [x]\<rparr>"
      and "PState u = PState s"
      and "PTranscript u = PTranscript s"
      and "PTraceFriCounter u = PTraceFriCounter s"
      and "PCompositionFriCounter u = PCompositionFriCounter s"
      and "PAlphaCounter u = PAlphaCounter s"
      and counter_u': "PQueryCounter u = PQueryCounter s"
      and ext_s_u': "s \<le> u"
    show ?thesis
      by (rule that[OF t_eq' counter_u' ext_s_u'])
  qed
  have ext_u_t: "u \<le> t"
    unfolding t_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_u ext_u_t])
  have counter_t: "PQueryCounter t = PQueryCounter s"
    unfolding t_eq using counter_u by simp
  show ?thesis
    using ext_s_t counter_t by simp
qed

lemma ro_record_staged_messages_hash_extends_query_counter:
  assumes outcome:
    "Some ((), t) \<in> set_dist (execute (ro_record_staged_messages xs) s)"
  shows "s \<le> t \<and> PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction xs arbitrary: s t)
  case Nil
  then show ?case
    unfolding ro_record_staged_messages_def
    by (simp add: hash_ext_refl)
next
  case (Cons x xs)
  from Cons.prems obtain u where
    head:
      "Some ((), u) \<in>
        set_dist (execute (ro_record_staged_message x) s)"
    and tail:
      "Some ((), t) \<in>
        set_dist (execute (ro_record_staged_messages xs) u)"
    unfolding ro_record_staged_messages_def
    by (auto elim!: set_dist_bindE)
  have head_props: "s \<le> u \<and> PQueryCounter u = PQueryCounter s"
    by (rule ro_record_staged_message_hash_extends_query_counter[OF head])
  have tail_props: "u \<le> t \<and> PQueryCounter t = PQueryCounter u"
    by (rule Cons.IH[OF tail])
  have "s \<le> t"
    by (rule hash_ext_trans[OF conjunct1[OF head_props]
          conjunct1[OF tail_props]])
  moreover have "PQueryCounter t = PQueryCounter s"
    using head_props tail_props by simp
  ultimately show ?case
    by simp
qed

lemma ro_record_staged_messages_absorb_read_replay_from_extension:
  assumes record_out:
    "Some ((), sent) \<in> set_dist (execute (ro_record_staged_messages xs) s)"
    and start_ext: "sent \<le> r"
    and start_state: "PState r = PState s"
    and start_tr: "PTranscript r = xs @ rest"
    and replay:
      "Some (ys, out) \<in>
        set_dist (execute (ntimes protocol_absorb_read (length xs)) r)"
  shows
    "ys = xs \<and> PState out = PState sent \<and>
      PTranscript out = rest \<and> sent \<le> out"
  using record_out start_ext start_state start_tr replay
proof (induction xs arbitrary: s sent r ys out rest)
  case Nil
  then show ?case
    unfolding ro_record_staged_messages_def
    by simp
next
  case (Cons x xs)
  from Cons.prems(1) obtain s1 where
    head:
      "Some ((), s1) \<in>
        set_dist (execute (ro_record_staged_message x) s)"
    and tail:
      "Some ((), sent) \<in>
        set_dist (execute (ro_record_staged_messages xs) s1)"
    unfolding ro_record_staged_messages_def
    by (auto elim!: set_dist_bindE)
  from Cons.prems(5) obtain y r1 ys_tail where
    read_head:
      "Some (y, r1) \<in> set_dist (execute protocol_absorb_read r)"
    and replay_tail:
      "Some (ys_tail, out) \<in>
        set_dist (execute (ntimes protocol_absorb_read (length xs)) r1)"
    and ys_eq: "ys = y # ys_tail"
    by (auto elim!: set_dist_bindE)
  have head_lookup_props:
    "fmlookup (HashMap s1) (TranscriptAbsorb (PState s) x) =
      Some (PState s1) \<and> s \<le> s1"
    by (rule ro_record_staged_message_absorb_lookup_state[OF head])
  have tail_ext: "s1 \<le> sent"
    using ro_record_staged_messages_hash_extends_query_counter[OF tail]
    by simp
  have lookup_sent:
    "fmlookup (HashMap sent) (TranscriptAbsorb (PState s) x) =
      Some (PState s1)"
    by (rule hash_extension_lookup[OF conjunct1[OF head_lookup_props]
          tail_ext])
  have lookup_r_old:
    "fmlookup (HashMap r) (TranscriptAbsorb (PState s) x) =
      Some (PState s1)"
    by (rule hash_extension_lookup[OF lookup_sent Cons.prems(2)])
  have lookup_r:
    "fmlookup (HashMap r) (TranscriptAbsorb (PState r) x) =
      Some (PState s1)"
    using lookup_r_old Cons.prems(3) by simp
  have tr_r: "PTranscript r = x # (xs @ rest)"
    using Cons.prems(4) by simp
  have read_props:
    "y = x \<and> PState r1 = PState s1 \<and>
      PTranscript r1 = xs @ rest \<and> r \<le> r1"
    by (rule protocol_absorb_read_known_nonempty_outcome
        [where xs = "xs @ rest", OF tr_r lookup_r read_head])
  have read_ext: "r \<le> r1"
    using read_props by simp
  have ext_sent_r1: "sent \<le> r1"
    by (rule hash_ext_trans[OF Cons.prems(2) read_ext])
  have state_r1: "PState r1 = PState s1"
    using read_props by simp
  have tr_r1: "PTranscript r1 = xs @ rest"
    using read_props by simp
  have tail_props:
    "ys_tail = xs \<and> PState out = PState sent \<and>
      PTranscript out = rest \<and> sent \<le> out"
    by (rule Cons.IH[OF tail ext_sent_r1 state_r1 tr_r1 replay_tail])
  show ?case
    using ys_eq read_props tail_props by simp
qed

lemma ro_checked_staged_query_program_Suc_outcomeE:
  assumes outcome:
    "Some (chunks, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots composition_roots
            i (Suc n)) s)"
  obtains raw chunk chunks' s1 s2 s3 where
    "Some (raw, s1) \<in>
      set_dist (execute receive_query_index_challenge s)"
    "Some (chunk, s2) \<in>
      set_dist (execute (query_opening_stage A i raw) s1)"
    "verifier_query_round_chunk (index (to_nat raw))
      trace_roots composition_roots chunk"
    "Some ((), s3) \<in>
      set_dist (execute (ro_record_staged_messages chunk) s2)"
    "Some (chunks', t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots composition_roots
            (Suc i) n) s3)"
    "chunks = chunk # chunks'"
  using outcome
  unfolding ro_checked_staged_query_program.simps assert_def Let_def
  by (auto simp: throw_no_outcome elim!: set_dist_bindE intro: that
      split: if_splits)

lemma ro_checked_staged_query_program_chunks_match_verifier:
  assumes outcome:
    "Some (chunks, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots composition_roots
            i n) s)"
  shows
    "\<exists>raw_idxs query_idxs.
      length raw_idxs = n \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length chunks = n \<and>
      (\<forall>j < n.
        verifier_query_round_chunk (query_idxs ! j)
          trace_roots composition_roots (chunks ! j)) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale)"
  using outcome
proof (induction n arbitrary: i chunks s t)
  case 0
  then show ?case
    by (intro exI[of _ "[]"] exI[of _ "[]"]) simp
next
  case (Suc n)
  obtain raw chunk chunks' s1 s2 s3 where
    chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and rest_out:
      "Some (chunks', t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
  proof (rule ro_checked_staged_query_program_Suc_outcomeE[OF Suc.prems])
    fix raw chunk chunks' s1 s2 s3
    assume shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
      and rest:
        "Some (chunks', t) \<in>
          set_dist
            (execute
              (ro_checked_staged_query_program A trace_roots composition_roots
                (Suc i) n) s3)"
      and chunks: "chunks = chunk # chunks'"
    show ?thesis
      by (rule that[OF shape rest chunks])
  qed
  from Suc.IH[OF rest_out]
  obtain raw_tail idx_tail where
    len_raw_tail: "length raw_tail = n"
    and idx_tail_def:
      "idx_tail = map (\<lambda>raw. index (to_nat raw)) raw_tail"
    and len_chunks_tail: "length chunks' = n"
    and tail_shape:
      "\<forall>j < n.
        verifier_query_round_chunk (idx_tail ! j)
          trace_roots composition_roots (chunks' ! j)"
    and idx_tail_bound:
      "\<forall>idx \<in> set idx_tail. idx < clength * scale"
    by blast
  let ?raws = "raw # raw_tail"
  let ?idxs = "index (to_nat raw) # idx_tail"
  have idxs_def: "?idxs = map (\<lambda>raw. index (to_nat raw)) ?raws"
    using idx_tail_def by simp
  have shape_all:
    "\<forall>j < Suc n.
      verifier_query_round_chunk (?idxs ! j)
        trace_roots composition_roots ((chunk # chunks') ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show "verifier_query_round_chunk (?idxs ! j)
        trace_roots composition_roots ((chunk # chunks') ! j)"
    proof (cases j)
      case 0
      then show ?thesis
        using chunk_shape by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      then show ?thesis
        using tail_shape Suc by simp
    qed
  qed
  have idx_bound_all:
    "\<forall>idx \<in> set ?idxs. idx < clength * scale"
    using idx_tail_bound index_less_domain by auto
  show ?case
    unfolding chunks_eq
    by (intro exI[of _ ?raws] exI[of _ ?idxs] conjI)
      (use len_raw_tail idxs_def len_chunks_tail shape_all idx_bound_all
        in simp_all)
qed

lemma ro_checked_staged_query_program_chunks_match_verifier_lengths:
  assumes outcome:
    "Some (chunks, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots composition_roots
            i rounds) s)"
  shows
    "\<exists>query_idxs.
      staged_query_chunks_match_verifier_lengths
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = chunks\<rparr>
        query_idxs"
proof -
  from ro_checked_staged_query_program_chunks_match_verifier[OF outcome]
  obtain raw_idxs query_idxs where
    len_chunks: "length chunks = rounds"
    and chunk_shape:
      "\<forall>j < rounds.
        verifier_query_round_chunk (query_idxs ! j)
          trace_roots composition_roots (chunks ! j)"
    by blast
  have chunk_lens:
    "\<forall>j < rounds.
      length (chunks ! j) =
        verifier_query_round_transcript_length (query_idxs ! j)
          trace_roots composition_roots"
    using chunk_shape verifier_query_round_chunk_length by blast
  show ?thesis
    by (intro exI[of _ query_idxs])
      (use len_chunks chunk_lens in
        \<open>simp add: staged_query_chunks_match_verifier_lengths_def\<close>)
qed

lemma ro_checked_staged_query_program_outcome_with_raws:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and outcome:
      "Some (chunks, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              i n) s)"
  shows
    "\<exists>raw_idxs query_idxs query_states.
      length raw_idxs = n \<and>
      length query_states = n \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length chunks = n \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s + n \<and>
      (\<forall>j < n.
        query_states ! j \<le> t \<and>
        PQueryCounter (query_states ! j) = PQueryCounter s + j \<and>
        fmlookup (HashMap t)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raw_idxs ! j) \<and>
        verifier_query_round_chunk (query_idxs ! j)
          trace_roots composition_roots (chunks ! j)) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale)"
  using bound outcome
proof (induction n arbitrary: i chunks s t)
  case 0
  then show ?case
    by (intro exI[of _ "[]"] conjI) (simp_all add: hash_ext_refl)
next
  case (Suc n)
  from ro_checked_staged_query_program_Suc_outcomeE[OF Suc.prems(2)]
  obtain raw chunk chunks' s1 s2 s3 where
    challenge_out:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and stage_out:
      "Some (chunk, s2) \<in>
        set_dist (execute (query_opening_stage A i raw) s1)"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and record_out:
      "Some ((), s3) \<in>
        set_dist (execute (ro_record_staged_messages chunk) s2)"
    and rest_out:
      "Some (chunks', t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
    .
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have challenge:
    "s \<le> s1 \<and>
     PState s1 = PState s \<and>
     PTranscript s1 = PTranscript s \<and>
     fmlookup (HashMap s1)
       (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule receive_query_index_challenge_outcome[OF challenge_out])
  have challenge_counter:
    "PQueryCounter s1 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF challenge_out]
    by simp
  have ext_s1_s2: "s1 \<le> s2"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have stage_counter: "PQueryCounter s2 = PQueryCounter s1"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have record_props: "s2 \<le> s3 \<and> PQueryCounter s3 = PQueryCounter s2"
    by (rule ro_record_staged_messages_hash_extends_query_counter[OF record_out])
  have ext_s2_s3: "s2 \<le> s3"
    using record_props by simp
  have counter_s3: "PQueryCounter s3 = Suc (PQueryCounter s)"
    using record_props stage_counter challenge_counter by simp
  have rest_bound:
    "Suc i + n \<le> length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  from Suc.IH[OF rest_bound rest_out]
  obtain raw_tail idx_tail state_tail where
    len_raw_tail: "length raw_tail = n"
    and len_state_tail: "length state_tail = n"
    and idx_tail_def:
      "idx_tail = map (\<lambda>raw. index (to_nat raw)) raw_tail"
    and len_chunks_tail: "length chunks' = n"
    and ext_s3_t: "s3 \<le> t"
    and query_count_tail:
      "PQueryCounter t = PQueryCounter s3 + n"
    and tail_props:
      "\<forall>j < n.
        state_tail ! j \<le> t \<and>
        PQueryCounter (state_tail ! j) = PQueryCounter s3 + j \<and>
        fmlookup (HashMap t)
          (QueryIndexChallenge
            (PQueryCounter (state_tail ! j))
            (PState (state_tail ! j))) =
          Some (raw_tail ! j) \<and>
        verifier_query_round_chunk (idx_tail ! j)
          trace_roots composition_roots (chunks' ! j)"
    and idx_tail_bound:
      "\<forall>idx \<in> set idx_tail. idx < clength * scale"
    by blast
  let ?raws = "raw # raw_tail"
  let ?idxs = "index (to_nat raw) # idx_tail"
  let ?states = "s # state_tail"
  let ?chunks = "chunk # chunks'"
  have idxs_def: "?idxs = map (\<lambda>raw. index (to_nat raw)) ?raws"
    using idx_tail_def by simp
  have ext_s_t: "s \<le> t"
  proof -
    have "s \<le> s1"
      using challenge by simp
    moreover have "s1 \<le> t"
      by (rule hash_ext_trans[OF ext_s1_s2])
        (rule hash_ext_trans[OF ext_s2_s3 ext_s3_t])
    ultimately show ?thesis
      by (rule hash_ext_trans)
  qed
  have ext_s1_t: "s1 \<le> t"
    by (rule hash_ext_trans[OF ext_s1_s2])
      (rule hash_ext_trans[OF ext_s2_s3 ext_s3_t])
  have lookup_head_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup)
      (use challenge ext_s1_t in simp_all)
  have query_count_all:
    "PQueryCounter t = PQueryCounter s + Suc n"
    using query_count_tail counter_s3 by simp
  have query_props_all:
    "\<forall>j < Suc n.
      ?states ! j \<le> t \<and>
      PQueryCounter (?states ! j) = PQueryCounter s + j \<and>
      fmlookup (HashMap t)
        (QueryIndexChallenge
          (PQueryCounter (?states ! j))
          (PState (?states ! j))) =
        Some (?raws ! j) \<and>
      verifier_query_round_chunk (?idxs ! j)
        trace_roots composition_roots (?chunks ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show
      "?states ! j \<le> t \<and>
       PQueryCounter (?states ! j) = PQueryCounter s + j \<and>
       fmlookup (HashMap t)
         (QueryIndexChallenge
           (PQueryCounter (?states ! j))
           (PState (?states ! j))) =
         Some (?raws ! j) \<and>
       verifier_query_round_chunk (?idxs ! j)
         trace_roots composition_roots (?chunks ! j)"
    proof (cases j)
      case 0
      then show ?thesis
        using ext_s_t lookup_head_t chunk_shape by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      have tail_k:
        "state_tail ! k \<le> t \<and>
         PQueryCounter (state_tail ! k) = PQueryCounter s3 + k \<and>
         fmlookup (HashMap t)
           (QueryIndexChallenge
             (PQueryCounter (state_tail ! k))
             (PState (state_tail ! k))) = Some (raw_tail ! k) \<and>
         verifier_query_round_chunk (idx_tail ! k)
           trace_roots composition_roots (chunks' ! k)"
        using tail_props k_bound by blast
      have state_ext_k: "state_tail ! k \<le> t"
        using tail_k by blast
      have counter_k0:
        "PQueryCounter (state_tail ! k) = PQueryCounter s3 + k"
        using tail_k by blast
      have counter_k:
        "PQueryCounter (state_tail ! k) = PQueryCounter s + Suc k"
        using counter_k0 counter_s3 by simp
      have lookup_k:
        "fmlookup (HashMap t)
          (QueryIndexChallenge
            (PQueryCounter (state_tail ! k))
            (PState (state_tail ! k))) = Some (raw_tail ! k)"
        using tail_k by blast
      have lookup_k':
        "fmlookup (HashMap t)
          (QueryIndexChallenge
            (PQueryCounter s + Suc k)
            (PState (state_tail ! k))) = Some (raw_tail ! k)"
        using lookup_k counter_k by simp
      have shape_k:
        "verifier_query_round_chunk (idx_tail ! k)
          trace_roots composition_roots (chunks' ! k)"
        using tail_k by blast
      show ?thesis
        using state_ext_k counter_k lookup_k' shape_k Suc by simp
    qed
  qed
  have idx_bound_all:
    "\<forall>idx \<in> set ?idxs. idx < clength * scale"
    using idx_tail_bound index_less_domain by auto
  show ?case
    unfolding chunks_eq
  proof (intro exI[of _ ?raws] exI[of _ ?idxs]
      exI[of _ ?states] conjI)
    show "length ?raws = Suc n"
      using len_raw_tail by simp
    show "length ?states = Suc n"
      using len_state_tail by simp
    show "?idxs = map (\<lambda>raw. index (to_nat raw)) ?raws"
      by (rule idxs_def)
    show "length ?chunks = Suc n"
      using len_chunks_tail by simp
    show "s \<le> t"
      by (rule ext_s_t)
    show "PQueryCounter t = PQueryCounter s + Suc n"
      by (rule query_count_all)
    show "\<forall>j<Suc n.
      ?states ! j \<le> t \<and>
      PQueryCounter (?states ! j) = PQueryCounter s + j \<and>
      fmlookup (HashMap t)
        (QueryIndexChallenge
          (PQueryCounter (?states ! j))
          (PState (?states ! j))) =
        Some (?raws ! j) \<and>
      verifier_query_round_chunk (?idxs ! j)
        trace_roots composition_roots (?chunks ! j)"
      by (rule query_props_all)
    show "\<forall>idx \<in> set ?idxs. idx < clength * scale"
      by (rule idx_bound_all)
  qed
qed

lemma ro_checked_staged_query_program_absorb_lookup_chain:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and outcome:
      "Some (chunks, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              i n) s)"
  shows
    "ro_absorb_lookup_chain t (PState s) (List.concat chunks)
      (PState t) \<and> s \<le> t"
  using bound outcome
proof (induction n arbitrary: i chunks s t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from ro_checked_staged_query_program_Suc_outcomeE[OF Suc.prems(2)]
  obtain raw chunk chunks' s1 s2 s3 where
    challenge_out:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and stage_out:
      "Some (chunk, s2) \<in>
        set_dist (execute (query_opening_stage A i raw) s1)"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and record_out:
      "Some ((), s3) \<in>
        set_dist (execute (ro_record_staged_messages chunk) s2)"
    and rest_out:
      "Some (chunks', t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
    .
  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have challenge_props:
    "s \<le> s1 \<and> PState s1 = PState s"
    using receive_query_index_challenge_outcome[OF challenge_out] by simp
  have stage_ext: "s1 \<le> s2"
    using controlled_ro_program_extension[OF stage_controlled] stage_out
    unfolding hash_extension_preserving_def by blast
  have stage_state: "PState s2 = PState s1"
    using controlled_stage_outcome_fields[OF stage_controlled stage_out]
    by simp
  have record_props:
    "ro_absorb_lookup_chain s3 (PState s2) chunk (PState s3) \<and>
      s2 \<le> s3"
    by (rule ro_record_staged_messages_absorb_lookup_chain[OF record_out])
  have tail_bound:
    "Suc i + n \<le> length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_props:
    "ro_absorb_lookup_chain t (PState s3) (List.concat chunks')
      (PState t) \<and> s3 \<le> t"
    by (rule Suc.IH[OF tail_bound rest_out])
  have head_chain_t:
    "ro_absorb_lookup_chain t (PState s) chunk (PState s3)"
  proof -
    have chain_from_s2:
      "ro_absorb_lookup_chain t (PState s2) chunk (PState s3)"
      by (rule ro_absorb_lookup_chain_mono[OF conjunct1[OF record_props]
            conjunct2[OF tail_props]])
    then show ?thesis
      using challenge_props stage_state by simp
  qed
  have chain_t:
    "ro_absorb_lookup_chain t (PState s) (List.concat chunks)
      (PState t)"
    unfolding chunks_eq List.concat.simps
    by (rule ro_absorb_lookup_chain_append[OF head_chain_t
          conjunct1[OF tail_props]])
  have ext_s_s3: "s \<le> s3"
  proof -
    have ext_s_s1: "s \<le> s1"
      using challenge_props by simp
    have ext_s_s2: "s \<le> s2"
      by (rule hash_ext_trans[OF ext_s_s1 stage_ext])
    show ?thesis
      by (rule hash_ext_trans[OF ext_s_s2 conjunct2[OF record_props]])
  qed
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_s3 conjunct2[OF tail_props]])
  show ?case
    using chain_t ext_s_t by simp
qed

lemma ro_checked_staged_transcript_program_absorb_lookup_chain:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A) s)"
  shows
    "ro_absorb_lookup_chain t (PState s) (staged_proof_transcript data)
      (PState t) \<and> s \<le> t"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3
      trace_final s4 s5 as s6 dg s7 s8 s9
      composition_roots composition_bs s10 composition_final s11 s12
      query_chunks where
    root_out:
      "Some (fr, s1) \<in> set_dist (execute (trace_root_stage A) s)"
    and root_record_out:
      "Some ((), s2) \<in> set_dist (execute (ro_record_staged_message fr) s1)"
    and trace_out:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and trace_final_out:
      "Some (trace_final, s4) \<in>
        set_dist (execute (trace_final_stage A trace_bs) s3)"
    and trace_final_record_out:
      "Some ((), s5) \<in>
        set_dist (execute (ro_record_staged_message trace_final) s4)"
    and alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (ro_staged_alpha_program (length spec)) s5)"
    and degree_out:
      "Some (dg, s7) \<in> set_dist (execute (degree_stage A as) s6)"
    and degree_record_out:
      "Some ((), s8) \<in> set_dist (execute (ro_record_staged_message dg) s7)"
    and assert_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1))) s8)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s9)"
    and composition_final_out:
      "Some (composition_final, s11) \<in>
        set_dist
          (execute (composition_final_stage A dg composition_bs) s10)"
    and composition_final_record_out:
      "Some ((), s12) \<in>
        set_dist
          (execute (ro_record_staged_message composition_final) s11)"
    and query_out:
      "Some (query_chunks, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              0 rounds) s12)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
    unfolding ro_checked_staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have root_controlled:
    "controlled_ro_program (trace_root_budget budgets) (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have root_stage_ext: "s \<le> s1"
    using controlled_ro_program_extension[OF root_controlled] root_out
    unfolding hash_extension_preserving_def by blast
  have root_stage_state: "PState s1 = PState s"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp
  have root_record_props:
    "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) fr) =
      Some (PState s2) \<and> s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF root_record_out])
  have root_chain_s2:
    "ro_absorb_lookup_chain s2 (PState s) [fr] (PState s2)"
    using root_record_props root_stage_state by auto
  have trace_bound:
    "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have trace_props:
    "ro_absorb_lookup_chain s3 (PState s2) trace_roots (PState s3) \<and>
      s2 \<le> s3"
    by (rule ro_staged_trace_fri_program_absorb_lookup_chain
        [OF controlled trace_bound trace_out])
  have trace_final_controlled:
    "controlled_ro_program (trace_final_budget budgets)
      (trace_final_stage A trace_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have trace_final_stage_ext: "s3 \<le> s4"
    using controlled_ro_program_extension[OF trace_final_controlled]
      trace_final_out
    unfolding hash_extension_preserving_def by blast
  have trace_final_stage_state: "PState s4 = PState s3"
    using controlled_stage_outcome_fields
        [OF trace_final_controlled trace_final_out]
    by simp
  have trace_final_record_props:
    "fmlookup (HashMap s5) (TranscriptAbsorb (PState s4) trace_final) =
      Some (PState s5) \<and> s4 \<le> s5"
    by (rule ro_record_staged_message_absorb_lookup_state
        [OF trace_final_record_out])
  have trace_final_chain_s5:
    "ro_absorb_lookup_chain s5 (PState s3) [trace_final] (PState s5)"
    using trace_final_record_props trace_final_stage_state by auto
  have alpha_props:
    "ro_absorb_lookup_chain s6 (PState s5) as (PState s6) \<and> s5 \<le> s6"
    by (rule ro_staged_alpha_program_absorb_lookup_chain[OF alpha_out])
  have degree_controlled:
    "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have degree_stage_ext: "s6 \<le> s7"
    using controlled_ro_program_extension[OF degree_controlled] degree_out
    unfolding hash_extension_preserving_def by blast
  have degree_stage_state: "PState s7 = PState s6"
    using controlled_stage_outcome_fields[OF degree_controlled degree_out]
    by simp
  have degree_record_props:
    "fmlookup (HashMap s8) (TranscriptAbsorb (PState s7) dg) =
      Some (PState s8) \<and> s7 \<le> s8"
    by (rule ro_record_staged_message_absorb_lookup_state
        [OF degree_record_out])
  have degree_chain_s8:
    "ro_absorb_lookup_chain s8 (PState s6) [dg] (PState s8)"
    using degree_record_props degree_stage_state by auto
  have s9_eq: "s9 = s8"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_round_bound:
    "0 + ceil_log (to_nat dg + 1) \<le>
      length (composition_fri_budgets budgets)"
    using assert_out wf unfolding assert_def staged_budget_wellformed_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_props_s9:
    "ro_absorb_lookup_chain s10 (PState s9) composition_roots
      (PState s10) \<and> s9 \<le> s10"
    by (rule ro_staged_composition_fri_program_absorb_lookup_chain
        [OF controlled composition_round_bound composition_out])
  have composition_props:
    "ro_absorb_lookup_chain s10 (PState s8) composition_roots
      (PState s10) \<and> s8 \<le> s10"
    using composition_props_s9 s9_eq by simp
  have composition_final_controlled:
    "controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg composition_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_stage_ext: "s10 \<le> s11"
    using controlled_ro_program_extension[OF composition_final_controlled]
      composition_final_out
    unfolding hash_extension_preserving_def by blast
  have composition_final_stage_state: "PState s11 = PState s10"
    using controlled_stage_outcome_fields
        [OF composition_final_controlled composition_final_out]
    by simp
  have composition_final_record_props:
    "fmlookup (HashMap s12)
      (TranscriptAbsorb (PState s11) composition_final) =
      Some (PState s12) \<and> s11 \<le> s12"
    by (rule ro_record_staged_message_absorb_lookup_state
        [OF composition_final_record_out])
  have composition_final_chain_s12:
    "ro_absorb_lookup_chain s12 (PState s10) [composition_final]
      (PState s12)"
    using composition_final_record_props composition_final_stage_state by auto
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_props:
    "ro_absorb_lookup_chain t (PState s12) (List.concat query_chunks)
      (PState t) \<and> s12 \<le> t"
    by (rule ro_checked_staged_query_program_absorb_lookup_chain
        [OF controlled query_bound query_out])

  have ext_s_s2: "s \<le> s2"
    by (rule hash_ext_trans[OF root_stage_ext conjunct2[OF root_record_props]])
  have ext_s3_s5: "s3 \<le> s5"
    by (rule hash_ext_trans[OF trace_final_stage_ext
          conjunct2[OF trace_final_record_props]])
  have ext_s6_s8: "s6 \<le> s8"
    by (rule hash_ext_trans[OF degree_stage_ext
          conjunct2[OF degree_record_props]])
  have ext_s10_s12: "s10 \<le> s12"
    by (rule hash_ext_trans[OF composition_final_stage_ext
          conjunct2[OF composition_final_record_props]])
  have ext_s2_s5: "s2 \<le> s5"
    by (rule hash_ext_trans[OF conjunct2[OF trace_props] ext_s3_s5])
  have ext_s2_s6: "s2 \<le> s6"
    by (rule hash_ext_trans[OF ext_s2_s5 conjunct2[OF alpha_props]])
  have ext_s2_s8: "s2 \<le> s8"
    by (rule hash_ext_trans[OF ext_s2_s6 ext_s6_s8])
  have ext_s2_s10: "s2 \<le> s10"
    by (rule hash_ext_trans[OF ext_s2_s8 conjunct2[OF composition_props]])
  have ext_s2_s12: "s2 \<le> s12"
    by (rule hash_ext_trans[OF ext_s2_s10 ext_s10_s12])
  have ext_s2_t: "s2 \<le> t"
    by (rule hash_ext_trans[OF ext_s2_s12 conjunct2[OF query_props]])
  have ext_s3_s6: "s3 \<le> s6"
    by (rule hash_ext_trans[OF ext_s3_s5 conjunct2[OF alpha_props]])
  have ext_s3_s8: "s3 \<le> s8"
    by (rule hash_ext_trans[OF ext_s3_s6 ext_s6_s8])
  have ext_s3_s10: "s3 \<le> s10"
    by (rule hash_ext_trans[OF ext_s3_s8 conjunct2[OF composition_props]])
  have ext_s3_s12: "s3 \<le> s12"
    by (rule hash_ext_trans[OF ext_s3_s10 ext_s10_s12])
  have ext_s3_t: "s3 \<le> t"
    by (rule hash_ext_trans[OF ext_s3_s12 conjunct2[OF query_props]])
  have ext_s5_s8: "s5 \<le> s8"
    by (rule hash_ext_trans[OF conjunct2[OF alpha_props] ext_s6_s8])
  have ext_s5_s10: "s5 \<le> s10"
    by (rule hash_ext_trans[OF ext_s5_s8 conjunct2[OF composition_props]])
  have ext_s5_s12: "s5 \<le> s12"
    by (rule hash_ext_trans[OF ext_s5_s10 ext_s10_s12])
  have ext_s5_t: "s5 \<le> t"
    by (rule hash_ext_trans[OF ext_s5_s12 conjunct2[OF query_props]])
  have ext_s6_s10: "s6 \<le> s10"
    by (rule hash_ext_trans[OF ext_s6_s8 conjunct2[OF composition_props]])
  have ext_s6_s12: "s6 \<le> s12"
    by (rule hash_ext_trans[OF ext_s6_s10 ext_s10_s12])
  have ext_s6_t: "s6 \<le> t"
    by (rule hash_ext_trans[OF ext_s6_s12 conjunct2[OF query_props]])
  have ext_s8_s12: "s8 \<le> s12"
    by (rule hash_ext_trans[OF conjunct2[OF composition_props] ext_s10_s12])
  have ext_s8_t: "s8 \<le> t"
    by (rule hash_ext_trans[OF ext_s8_s12 conjunct2[OF query_props]])
  have ext_s10_t: "s10 \<le> t"
    by (rule hash_ext_trans[OF ext_s10_s12 conjunct2[OF query_props]])

  have root_chain_t:
    "ro_absorb_lookup_chain t (PState s) [fr] (PState s2)"
    by (rule ro_absorb_lookup_chain_mono[OF root_chain_s2 ext_s2_t])
  have trace_chain_t:
    "ro_absorb_lookup_chain t (PState s2) trace_roots (PState s3)"
    by (rule ro_absorb_lookup_chain_mono[OF conjunct1[OF trace_props]
          ext_s3_t])
  have trace_final_chain_t:
    "ro_absorb_lookup_chain t (PState s3) [trace_final] (PState s5)"
    by (rule ro_absorb_lookup_chain_mono
        [OF trace_final_chain_s5 ext_s5_t])
  have alpha_chain_t:
    "ro_absorb_lookup_chain t (PState s5) as (PState s6)"
    by (rule ro_absorb_lookup_chain_mono[OF conjunct1[OF alpha_props]
          ext_s6_t])
  have degree_chain_t:
    "ro_absorb_lookup_chain t (PState s6) [dg] (PState s8)"
    by (rule ro_absorb_lookup_chain_mono[OF degree_chain_s8 ext_s8_t])
  have composition_chain_t:
    "ro_absorb_lookup_chain t (PState s8) composition_roots (PState s10)"
    by (rule ro_absorb_lookup_chain_mono[OF conjunct1[OF composition_props]
          ext_s10_t])
  have composition_final_chain_t:
    "ro_absorb_lookup_chain t (PState s10) [composition_final]
      (PState s12)"
    by (rule ro_absorb_lookup_chain_mono
        [OF composition_final_chain_s12 conjunct2[OF query_props]])
  have query_chain_t:
    "ro_absorb_lookup_chain t (PState s12) (List.concat query_chunks)
      (PState t)"
    using query_props by simp

  have chain_1:
    "ro_absorb_lookup_chain t (PState s) ([fr] @ trace_roots)
      (PState s3)"
    by (rule ro_absorb_lookup_chain_append[OF root_chain_t trace_chain_t])
  have chain_2_raw:
    "ro_absorb_lookup_chain t (PState s)
      (([fr] @ trace_roots) @ [trace_final]) (PState s5)"
    by (rule ro_absorb_lookup_chain_append[OF chain_1 trace_final_chain_t])
  have chain_2:
    "ro_absorb_lookup_chain t (PState s)
      ([fr] @ trace_roots @ [trace_final]) (PState s5)"
    using chain_2_raw by simp
  have chain_3_raw:
    "ro_absorb_lookup_chain t (PState s)
      (([fr] @ trace_roots @ [trace_final]) @ as) (PState s6)"
    by (rule ro_absorb_lookup_chain_append[OF chain_2 alpha_chain_t])
  have chain_3:
    "ro_absorb_lookup_chain t (PState s)
      ([fr] @ trace_roots @ [trace_final] @ as) (PState s6)"
    using chain_3_raw by simp
  have chain_4_raw:
    "ro_absorb_lookup_chain t (PState s)
      (([fr] @ trace_roots @ [trace_final] @ as) @ [dg])
      (PState s8)"
    by (rule ro_absorb_lookup_chain_append[OF chain_3 degree_chain_t])
  have chain_4:
    "ro_absorb_lookup_chain t (PState s)
      ([fr] @ trace_roots @ [trace_final] @ as @ [dg])
      (PState s8)"
    using chain_4_raw by simp
  have chain_5_raw:
    "ro_absorb_lookup_chain t (PState s)
      (([fr] @ trace_roots @ [trace_final] @ as @ [dg]) @
        composition_roots) (PState s10)"
    by (rule ro_absorb_lookup_chain_append[OF chain_4 composition_chain_t])
  have chain_5:
    "ro_absorb_lookup_chain t (PState s)
      ([fr] @ trace_roots @ [trace_final] @ as @ [dg] @
        composition_roots) (PState s10)"
    using chain_5_raw by simp
  have chain_6_raw:
    "ro_absorb_lookup_chain t (PState s)
      (([fr] @ trace_roots @ [trace_final] @ as @ [dg] @
        composition_roots) @ [composition_final]) (PState s12)"
    by (rule ro_absorb_lookup_chain_append
        [OF chain_5 composition_final_chain_t])
  have chain_6:
    "ro_absorb_lookup_chain t (PState s)
      ([fr] @ trace_roots @ [trace_final] @ as @ [dg] @
        composition_roots @ [composition_final]) (PState s12)"
    using chain_6_raw by simp
  have full_chain_raw:
    "ro_absorb_lookup_chain t (PState s)
      (([fr] @ trace_roots @ [trace_final] @ as @ [dg] @
        composition_roots @ [composition_final]) @
        List.concat query_chunks) (PState t)"
    by (rule ro_absorb_lookup_chain_append[OF chain_6 query_chain_t])
  have full_chain:
    "ro_absorb_lookup_chain t (PState s)
      ([fr] @ trace_roots @ [trace_final] @ as @ [dg] @
        composition_roots @ [composition_final] @
        List.concat query_chunks) (PState t)"
    using full_chain_raw by simp
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_s2 ext_s2_t])
  show ?thesis
    unfolding data_eq staged_proof_transcript_def verifier_header_messages_def
    using full_chain ext_s_t by simp
qed

lemma ro_checked_staged_transcript_program_absorb_read_replay_from_extension:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and builder_out:
      "Some (data, sent) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A) s)"
    and start_ext: "sent \<le> r"
    and start_state: "PState r = PState s"
    and start_tr: "PTranscript r = staged_proof_transcript data @ rest"
    and replay:
      "Some (ys, out) \<in>
        set_dist
          (execute
            (ntimes protocol_absorb_read
              (length (staged_proof_transcript data))) r)"
  shows
    "ys = staged_proof_transcript data \<and>
      PState out = PState sent \<and> PTranscript out = rest \<and> sent \<le> out"
proof -
  have chain:
    "ro_absorb_lookup_chain sent (PState s) (staged_proof_transcript data)
      (PState sent) \<and> s \<le> sent"
    by (rule ro_checked_staged_transcript_program_absorb_lookup_chain
        [OF wf controlled builder_out])
  show ?thesis
    by (rule ro_absorb_lookup_chain_replay_from_extension
        [OF conjunct1[OF chain] start_ext start_state start_tr replay])
qed

lemma ro_checked_staged_transcript_program_absorb_read_replay_from_verifier_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and builder_out:
      "Some (data, sent) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    and replay:
      "Some (ys, out) \<in>
        set_dist
          (execute
            (ntimes protocol_absorb_read
              (length (staged_proof_transcript data)))
            (verifier_state_from_adversary sent
              (staged_proof_transcript data @ rest)))"
  shows
    "ys = staged_proof_transcript data \<and>
      PState out = PState sent \<and> PTranscript out = rest \<and> sent \<le> out"
proof -
  have start_ext:
    "sent \<le> verifier_state_from_adversary sent
      (staged_proof_transcript data @ rest)"
    unfolding verifier_state_from_adversary_def less_eq_hash_ext_def
      less_eq_fmap_def
    by simp
  have start_state:
    "PState (verifier_state_from_adversary sent
      (staged_proof_transcript data @ rest)) =
      PState adversary_initial_state"
    by simp
  have start_tr:
    "PTranscript (verifier_state_from_adversary sent
      (staged_proof_transcript data @ rest)) =
      staged_proof_transcript data @ rest"
    by simp
  show ?thesis
    by (rule ro_checked_staged_transcript_program_absorb_read_replay_from_extension
        [OF wf controlled builder_out start_ext start_state start_tr replay])
qed

lemma ro_checked_staged_transcript_program_absorb_read_replay_support_from_extension:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and builder_out:
      "Some (data, sent) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A) s)"
    and start_ext: "sent \<le> r"
    and start_state: "PState r = PState s"
    and start_tr: "PTranscript r = staged_proof_transcript data @ rest"
  shows
    "Some (staged_proof_transcript data,
       r\<lparr>PState := PState sent, PTranscript := rest\<rparr>) \<in>
      set_dist
        (execute
          (ntimes protocol_absorb_read
            (length (staged_proof_transcript data))) r)"
proof -
  have chain:
    "ro_absorb_lookup_chain sent (PState s) (staged_proof_transcript data)
      (PState sent) \<and> s \<le> sent"
    by (rule ro_checked_staged_transcript_program_absorb_lookup_chain
        [OF wf controlled builder_out])
  show ?thesis
    by (rule ro_absorb_lookup_chain_replay_support_from_extension
        [OF conjunct1[OF chain] start_ext start_state start_tr])
qed

lemma ro_checked_staged_transcript_program_absorb_read_replay_support_from_verifier_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and builder_out:
      "Some (data, sent) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
  shows
    "Some (staged_proof_transcript data,
       (verifier_state_from_adversary sent
          (staged_proof_transcript data @ rest))\<lparr>
            PState := PState sent, PTranscript := rest\<rparr>) \<in>
      set_dist
        (execute
          (ntimes protocol_absorb_read
            (length (staged_proof_transcript data)))
          (verifier_state_from_adversary sent
            (staged_proof_transcript data @ rest)))"
proof -
  have start_ext:
    "sent \<le> verifier_state_from_adversary sent
      (staged_proof_transcript data @ rest)"
    unfolding verifier_state_from_adversary_def less_eq_hash_ext_def
      less_eq_fmap_def
    by simp
  have start_state:
    "PState (verifier_state_from_adversary sent
      (staged_proof_transcript data @ rest)) =
      PState adversary_initial_state"
    by simp
  have start_tr:
    "PTranscript (verifier_state_from_adversary sent
      (staged_proof_transcript data @ rest)) =
      staged_proof_transcript data @ rest"
    by simp
  show ?thesis
    by (rule ro_checked_staged_transcript_program_absorb_read_replay_support_from_extension
        [OF wf controlled builder_out start_ext start_state start_tr])
qed

lemma ro_checked_staged_transcript_program_query_witnessesE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A) s)"
  obtains query_start raw_idxs query_idxs query_states where
    "Some (staged_query_chunks data, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data) 0 rounds)
          query_start)"
    "length raw_idxs = rounds"
    "length query_states = rounds"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length (staged_query_chunks data) = rounds"
    "query_start \<le> t"
    "PQueryCounter t = PQueryCounter query_start + rounds"
    "\<forall>j < rounds.
      query_states ! j \<le> t \<and>
      PQueryCounter (query_states ! j) = PQueryCounter query_start + j \<and>
      fmlookup (HashMap t)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raw_idxs ! j) \<and>
      verifier_query_round_chunk (query_idxs ! j)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! j)"
    "\<forall>idx \<in> set query_idxs. idx < clength * scale"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 query_chunks where
    query_out:
      "Some (query_chunks, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              0 rounds)
            s11)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
    unfolding ro_checked_staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  from ro_checked_staged_query_program_outcome_with_raws
      [OF controlled query_bound query_out]
  obtain raw_idxs query_idxs query_states where
    len_raw: "length raw_idxs = rounds"
    and len_states: "length query_states = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and query_start_ext: "s11 \<le> t"
    and query_count:
      "PQueryCounter t = PQueryCounter s11 + rounds"
    and query_props:
      "\<forall>j < rounds.
        query_states ! j \<le> t \<and>
        PQueryCounter (query_states ! j) = PQueryCounter s11 + j \<and>
        fmlookup (HashMap t)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raw_idxs ! j) \<and>
        verifier_query_round_chunk (query_idxs ! j)
          trace_roots composition_roots (query_chunks ! j)"
    and idx_bound:
      "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by blast
  have query_props_data:
    "\<forall>j < rounds.
      query_states ! j \<le> t \<and>
      PQueryCounter (query_states ! j) = PQueryCounter s11 + j \<and>
      fmlookup (HashMap t)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raw_idxs ! j) \<and>
      verifier_query_round_chunk (query_idxs ! j)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < rounds"
    have prop_j:
      "query_states ! j \<le> t \<and>
       PQueryCounter (query_states ! j) = PQueryCounter s11 + j \<and>
       fmlookup (HashMap t)
         (QueryIndexChallenge
           (PQueryCounter (query_states ! j))
           (PState (query_states ! j))) =
         Some (raw_idxs ! j) \<and>
       verifier_query_round_chunk (query_idxs ! j)
         trace_roots composition_roots (query_chunks ! j)"
      using query_props j_bound by blast
    have state_ext_j: "query_states ! j \<le> t"
      using prop_j by blast
    have counter_j:
      "PQueryCounter (query_states ! j) = PQueryCounter s11 + j"
      using prop_j by blast
    have lookup_j:
      "fmlookup (HashMap t)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raw_idxs ! j)"
      using prop_j by blast
    have shape_j:
      "verifier_query_round_chunk (query_idxs ! j)
        trace_roots composition_roots (query_chunks ! j)"
      using prop_j by blast
    show
      "query_states ! j \<le> t \<and>
       PQueryCounter (query_states ! j) = PQueryCounter s11 + j \<and>
       fmlookup (HashMap t)
         (QueryIndexChallenge
           (PQueryCounter (query_states ! j))
           (PState (query_states ! j))) =
         Some (raw_idxs ! j) \<and>
       verifier_query_round_chunk (query_idxs ! j)
         (staged_trace_fri_roots data)
         (staged_composition_fri_roots data)
         (staged_query_chunks data ! j)"
    proof (intro conjI)
      show "query_states ! j \<le> t"
        by (rule state_ext_j)
      show "PQueryCounter (query_states ! j) = PQueryCounter s11 + j"
        by (rule counter_j)
      show "fmlookup (HashMap t)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raw_idxs ! j)"
        by (rule lookup_j)
      show "verifier_query_round_chunk (query_idxs ! j)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! j)"
        using shape_j data_eq by simp
    qed
  qed
  show ?thesis
  proof (rule that[of s11 raw_idxs query_states query_idxs])
    show "Some (staged_query_chunks data, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data) 0 rounds)
          s11)"
      using query_out data_eq by simp
    show "length raw_idxs = rounds"
      by (rule len_raw)
    show "length query_states = rounds"
      by (rule len_states)
    show "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
      by (rule query_idxs_eq)
    show "length (staged_query_chunks data) = rounds"
      using len_chunks data_eq by simp
    show "s11 \<le> t"
      by (rule query_start_ext)
    show "PQueryCounter t = PQueryCounter s11 + rounds"
      by (rule query_count)
    show "\<forall>j<rounds.
      query_states ! j \<le> t \<and>
      PQueryCounter (query_states ! j) = PQueryCounter s11 + j \<and>
      fmlookup (HashMap t)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raw_idxs ! j) \<and>
      verifier_query_round_chunk (query_idxs ! j)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! j)"
      by (rule query_props_data)
    show "\<forall>idx \<in> set query_idxs. idx < clength * scale"
      by (rule idx_bound)
  qed
qed

lemma ro_staged_alpha_program_output_length:
  assumes out:
    "Some (as, t) \<in> set_dist (execute (ro_staged_alpha_program n) s)"
  shows "length as = n"
  using out
proof (induction n arbitrary: s as t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain a s1 s2 as' where
    tail:
      "Some (as', t) \<in> set_dist (execute (ro_staged_alpha_program n) s2)"
    and as_eq: "as = a # as'"
    unfolding ro_staged_alpha_program.simps
    by (auto elim!: set_dist_bindE)
  from Suc.IH[OF tail] as_eq show ?case
    by simp
qed

lemma ro_checked_staged_transcript_program_query_chunks_match_verifier_lengths:
  assumes outcome:
    "Some (data, t) \<in>
      set_dist
        (execute (ro_checked_staged_transcript_program A) s)"
  shows "\<exists>query_idxs.
    staged_query_chunks_match_verifier_lengths data query_idxs"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 s12 query_chunks where
    query_out:
      "Some (query_chunks, s12) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              0 rounds)
            s11)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
    unfolding ro_checked_staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  show ?thesis
    unfolding data_eq
    by (rule ro_checked_staged_query_program_chunks_match_verifier_lengths
        [OF query_out])
qed

lemma ro_checked_staged_security_experiment_with_data_state_query_lengthsE:
  assumes outcome:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_security_experiment_with_data_state A)
          initial_state)"
  obtains query_idxs where
    "staged_query_chunks_match_verifier_lengths data query_idxs"
proof -
  from ro_checked_staged_security_experiment_with_data_state_outcomeE
      [OF outcome]
  have builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (ro_checked_staged_transcript_program A) initial_state)"
    by blast
  from ro_checked_staged_transcript_program_query_chunks_match_verifier_lengths
      [OF builder]
  obtain query_idxs where
    "staged_query_chunks_match_verifier_lengths data query_idxs"
    by blast
  then show ?thesis
    by (rule that)
qed

lemma ro_checked_staged_transcript_program_outcome_shape:
  assumes outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
  shows
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     ceil_log (to_nat (staged_degree data) + 1) \<le>
       ceil_log (maxDegree + 1) \<and>
     length (staged_query_chunks data) = rounds"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 s12 query_chunks where
    trace_out:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (ro_staged_alpha_program (length spec)) s5)"
    and degree_eq: "staged_degree data = dg"
    and assert_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1))) s8)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s9)"
    and query_out:
      "Some (query_chunks, s12) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              0 rounds)
            s11)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
    unfolding ro_checked_staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have trace_len:
    "length trace_roots = ceil_log clength \<and>
     length trace_bs = ceil_log clength"
    using ro_staged_trace_fri_program_output_lengths[OF trace_out] by simp
  have alpha_len: "length as = length spec"
    using ro_staged_alpha_program_output_length[OF alpha_out] by simp
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_len:
    "length composition_roots = ceil_log (to_nat dg + 1) \<and>
     length composition_bs = ceil_log (to_nat dg + 1)"
    using ro_staged_composition_fri_program_output_lengths[OF composition_out]
    by simp
  have query_len: "length query_chunks = rounds"
    using ro_checked_staged_query_program_chunks_match_verifier[OF query_out]
    by blast
  show ?thesis
    unfolding data_eq degree_eq
    using trace_len alpha_len composition_len round_bound query_len by simp
qed

lemma ro_checked_staged_transcript_program_outcome_header_transcript:
  assumes outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
  shows
    "verifier_header_transcript
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
proof -
  have shape:
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     ceil_log (to_nat (staged_degree data) + 1) \<le>
       ceil_log (maxDegree + 1) \<and>
     length (staged_query_chunks data) = rounds"
    by (rule ro_checked_staged_transcript_program_outcome_shape[OF outcome])
  show ?thesis
    by (rule staged_proof_transcript_verifier_header_transcript)
      (use shape in simp_all)
qed

end

end
