(* Title: Stark/FS_Transcript_Prescan.thy
   License: BSD-3-Clause *)

theory FS_Transcript_Prescan
  imports "Stark.FS_Private_Randomness_Normalization"
begin

section \<open>Failure-sensitive transcript pre-scanning\<close>

text \<open>This is a proof-side classification of existing state-monad programs,
  not a new attacker or verifier interface. A successful classified program
  consumes a fixed number of transcript words. Its other oracle operations may
  be adaptive, but their keys must be disjoint from TranscriptAbsorb.

  The invariant averages over the existing lazy random oracle, for every initial
  cache and postcondition. It preserves failures as well as successful final
  states. It is not equality of operational hash-call counts or execution logs.\<close>

context soundness
begin

inductive fs_scan_program :: "nat \<Rightarrow> ('a, 'f protocol_channel) state_monad \<Rightarrow> bool"
where
  Return: "fs_scan_program 0 (return x)"
| Fail: "fs_scan_program n throw"
| Read: "(\<And>x. fs_scan_program n (k x)) \<Longrightarrow>
    fs_scan_program (Suc n) (protocol_absorb_read \<bind> k)"
| Hash: "(\<And>x y. key \<noteq> TranscriptAbsorb x y) \<Longrightarrow>
    (\<And>a. fs_scan_program n (k a)) \<Longrightarrow>
    fs_scan_program n (hash key \<bind> k)"

lemma fs_scan_bind:
  assumes "fs_scan_program n m" "\<And>x. fs_scan_program r (k x)"
  shows "fs_scan_program (n+r) (m \<bind> k)"
  using assms
  apply (induction rule: fs_scan_program.induct)
    apply (auto simp: sm_bind_assoc fs_throw_bind intro: fs_scan_program.intros)
  apply (rule fs_scan_program.Hash)
   apply assumption
  apply assumption
  done

lemma fs_scan_assert:
  "fs_scan_program 0 (assert P)"
  by (cases P) (auto simp: assert_def intro: fs_scan_program.intros)

lemma fs_shadow_const:
  "wp (shadow_absorb xs cursor) (\<lambda>_. c) s=c"
  by (induction xs arbitrary: cursor s) (simp_all add: wp_bind wp_hash wp_return fs_expect_const)

lemma fs_hash_swap:
  fixes x y :: "'f protocol_hash_input"
  assumes "x\<noteq>y"
  shows "wp (hash x \<bind> (\<lambda>a. hash y \<bind> (\<lambda>b. return (a,b)))) F s =
    wp (hash y \<bind> (\<lambda>b. hash x \<bind> (\<lambda>a. return (a,b)))) F s"
proof -
  have updates: "fmupd y b (fmupd x a (HashMap s)) =
    fmupd x a (fmupd y b (HashMap s))" for a b
    using assms by (simp add: fmupd_reorder_neq)
  show ?thesis
    apply (simp add: wpsimps hash_dist_def assms updates eq_commute)
    apply (rule fs_expect_swap)
    done
qed

lemma fs_hash_swap_bind:
  fixes x y :: "'f protocol_hash_input"
    and k :: "'f \<Rightarrow> 'f \<Rightarrow> ('a,'f protocol_channel) state_monad"
  assumes "x\<noteq>y"
  shows "(hash x \<bind> (\<lambda>a. hash y \<bind> (\<lambda>b. k a b))) =
    (hash y \<bind> (\<lambda>b. hash x \<bind> (\<lambda>a. k a b)))"
proof -
  have pair: "(hash x \<bind> (\<lambda>a. hash y \<bind> (\<lambda>b. return (a,b)))) =
    (hash y \<bind> (\<lambda>b. hash x \<bind> (\<lambda>a. return (a,b))))"
    by (rule fs_wp_ext) (rule fs_hash_swap[OF assms])
  show ?thesis
    using arg_cong[OF pair, of "\<lambda>m. m \<bind> (\<lambda>(a,b). k a b)"]
    by (simp add: sm_bind_assoc)
qed

lemma fs_shadow_hash_commute:
  fixes key :: "'f protocol_hash_input"
    and k :: "'f \<Rightarrow> 'f \<Rightarrow> ('a,'f protocol_channel) state_monad"
  assumes key: "\<And>a b. key\<noteq>TranscriptAbsorb a b"
  shows "(hash key \<bind> (\<lambda>x. shadow_absorb xs cursor \<bind> (\<lambda>z. k x z))) =
    (shadow_absorb xs cursor \<bind> (\<lambda>z. hash key \<bind> (\<lambda>x. k x z)))"
  by (induction xs arbitrary: cursor k)
    (simp_all add: sm_bind_assoc fs_hash_swap_bind[OF key])

lemma fs_shadow_transport:
  fixes f :: "'f protocol_channel \<Rightarrow> 'f protocol_channel"
  assumes hm: "\<And>s. HashMap (f s)=HashMap s"
    and upd: "\<And>s k y. f (s\<lparr>HashMap:=fmupd k y (HashMap s)\<rparr>) =
      (f s)\<lparr>HashMap:=fmupd k y (HashMap (f s))\<rparr>"
  shows "wp (shadow_absorb xs cursor) F (f s) =
    wp (shadow_absorb xs cursor)
      (\<lambda>out. case out of None \<Rightarrow> F None | Some (x,t) \<Rightarrow> F (Some(x,f t))) s"
  by (induction xs arbitrary: cursor s F)
    (simp_all add: wp_bind wp_hash wp_return hash_dist_def hm upd[unfolded hm, symmetric])

lemma fs_shadow_outcome:
  fixes s t :: "'f protocol_channel"
  assumes "Some(x,t)\<in>set_dist(execute (shadow_absorb xs cursor) s)"
  shows "s\<le>t" "PState t=PState s" "PTranscript t=PTranscript s"
  using assms
    controlled_ro_program_hash_extension_preserving[OF shadow_absorb_controlled]
    shadow_absorb_preserves_fields
  unfolding hash_extension_preserving_def protocol_fields_preserving_def
  by (auto dest: spec)

lemma fs_absorb_read_known:
  assumes "PTranscript s=x#xs"
    "fmlookup (HashMap s) (TranscriptAbsorb (PState s) x)=Some cursor"
  shows "wp protocol_absorb_read F s=F (Some(x,s\<lparr>PState:=cursor,PTranscript:=xs\<rparr>))"
  unfolding protocol_absorb_read_def
  by (simp add: wp_bind wp_get wp_modify wp_return assert_def assms hash_known_wp)

lemma fs_shadow_read_cached:
  fixes s :: "'f protocol_channel"
  assumes tr: "PTranscript s=x#xs"
    and known: "fmlookup (HashMap s) (TranscriptAbsorb (PState s) x)=Some cursor"
  shows "wp (shadow_absorb ys cursor \<bind> (\<lambda>_. protocol_absorb_read \<bind> k)) F s =
    wp (shadow_absorb ys cursor \<bind> (\<lambda>_. k x)) F (s\<lparr>PState:=cursor,PTranscript:=xs\<rparr>)"
proof -
  let ?f = "\<lambda>t. t\<lparr>PState:=cursor,PTranscript:=xs\<rparr>"
  let ?post = "\<lambda>out. case out of None \<Rightarrow> F None
    | Some (z,t) \<Rightarrow> wp (k x) F (?f t)"
  have move:
    "wp (shadow_absorb ys cursor \<bind> (\<lambda>_. protocol_absorb_read \<bind> k)) F s =
      wp (shadow_absorb ys cursor) ?post s"
  proof (simp only: wp_bind, rule fs_wp_cong_on_support)
    fix out assume out: "out\<in>set_dist(execute (shadow_absorb ys cursor) s)"
    show "(case out of None \<Rightarrow> F None | Some(z,t) \<Rightarrow>
      wp protocol_absorb_read (\<lambda>r. case r of None \<Rightarrow> F None
        | Some(y,u) \<Rightarrow> wp (k y) F u) t) = ?post out"
    proof (cases out)
      case None then show ?thesis by simp
    next
      case (Some zt)
      obtain z t where zt: "zt=(z,t)" by (cases zt) auto
      have outcome: "Some(z,t)\<in>set_dist(execute (shadow_absorb ys cursor) s)"
        using out Some zt by simp
      note props=fs_shadow_outcome[OF outcome]
      have lookup: "fmlookup (HashMap t) (TranscriptAbsorb (PState t) x)=Some cursor"
        using hash_extension_lookup[OF known props(1)] props(2) by simp
      show ?thesis
        using Some zt fs_absorb_read_known[OF _ lookup] tr props(3)
        by simp
    qed
  qed
  have transport: "wp (shadow_absorb ys cursor \<bind> (\<lambda>_. k x)) F (?f s) =
    wp (shadow_absorb ys cursor) ?post s"
    unfolding wp_bind
    using fs_shadow_transport[where f="?f" and xs=ys and cursor=cursor and s=s
      and F="\<lambda>out. case out of None \<Rightarrow> F None | Some(z,t) \<Rightarrow> wp (k x) F t"]
    by (simp split: option.splits)
  show ?thesis using move transport by simp
qed

lemma fs_scan_invariant:
  assumes "fs_scan_program n m"
  shows "wp (shadow_absorb (take n (PTranscript s)) (PState s) \<bind> (\<lambda>_. m)) F s =
    wp m F s"
  using assms
proof (induction arbitrary: s F rule: fs_scan_program.induct)
  case (Return x)
  then show ?case by (simp add: wp_return)
next
  case (Fail n)
  have post: "(\<lambda>r :: ('f \<times> 'f protocol_channel) option.
      case r of None \<Rightarrow> F None | Some(x,t) \<Rightarrow> F None) = (\<lambda>_. F None)"
    by (rule ext) (auto split: option.splits)
  show ?case
    by (simp only: wp_bind wp_throw post fs_shadow_const)
next
  case (Read n k)
  show ?case
  proof (cases "PTranscript s")
    case Nil
    then show ?thesis
      by (simp add: protocol_absorb_read_def wp_bind wp_get wp_throw assert_def)
  next
    case (Cons x xs)
    let ?key = "TranscriptAbsorb (PState s) x"
    let ?t = "\<lambda>a. s\<lparr>HashMap:=fmupd ?key a (HashMap s)\<rparr>"
    have tail:
      "wp (shadow_absorb (take n xs) a \<bind> (\<lambda>_. protocol_absorb_read \<bind> k)) F (?t a) =
       wp (k x) F ((?t a)\<lparr>PState:=a,PTranscript:=xs\<rparr>)" for a
    proof -
      have cached:
        "wp (shadow_absorb (take n xs) a \<bind> (\<lambda>_. protocol_absorb_read \<bind> k)) F (?t a) =
         wp (shadow_absorb (take n xs) a \<bind> (\<lambda>_. k x)) F
           ((?t a)\<lparr>PState:=a,PTranscript:=xs\<rparr>)"
        by (rule fs_shadow_read_cached) (use Cons in simp_all)
      show ?thesis
        using cached Read.IH[of "(?t a)\<lparr>PState:=a,PTranscript:=xs\<rparr>" x F]
        by simp
    qed
    show ?thesis
      using tail
      by (simp add: Cons sm_bind_assoc wp_bind wp_hash protocol_absorb_read_def
        wp_get wp_modify wp_return assert_def)
  qed
next
  case (Hash key n k)
  let ?scan = "shadow_absorb (take n (PTranscript s)) (PState s)"
  have commute: "(?scan \<bind> (\<lambda>_. hash key \<bind> k)) =
    (hash key \<bind> (\<lambda>a. ?scan \<bind> (\<lambda>_. k a)))"
    by (rule fs_shadow_hash_commute[OF Hash.hyps(1), symmetric])
  have tail: "wp (?scan \<bind> (\<lambda>_. k a)) F
      (s\<lparr>HashMap:=fmupd key a (HashMap s)\<rparr>) =
    wp (k a) F (s\<lparr>HashMap:=fmupd key a (HashMap s)\<rparr>)" for a
    using Hash.IH[of "s\<lparr>HashMap:=fmupd key a (HashMap s)\<rparr>" a F] by simp
  show ?case
    unfolding commute
    using tail[unfolded wp_bind]
    by (simp add: wp_bind wp_hash)
qed

lemma fs_scan_read: "fs_scan_program 1 protocol_absorb_read"
  using fs_scan_program.Read[where k="\<lambda>x. return x", OF fs_scan_program.Return] by simp

lemma fs_scan_hash:
  assumes "\<And>x y. key \<noteq> TranscriptAbsorb x y"
  shows "fs_scan_program 0 (hash key)"
  using fs_scan_program.Hash[where k="\<lambda>x. return x", OF assms fs_scan_program.Return] by simp

lemma fs_scan_ntimes:
  assumes "fs_scan_program n m"
  shows "fs_scan_program (r*n) (ntimes m r)"
  by (induction r)
    (auto intro!: fs_scan_bind[OF assms]
      fs_scan_bind[where r=0, simplified] fs_scan_program.Return)

lemma fs_scan_mmap:
  assumes "\<And>x. x\<in>set xs \<Longrightarrow> fs_scan_program n (f x)"
  shows "fs_scan_program (length xs*n) (mmap (map f xs))"
  using assms
  proof (induction xs)
  case Nil then show ?case by (simp add: fs_scan_program.Return)
next
  case (Cons a xs)
  have head: "fs_scan_program n (f a)" by (rule Cons.prems) simp
  have tail: "fs_scan_program (length xs*n) (mmap (map f xs))"
    by (rule Cons.IH) (auto intro: Cons.prems)
  show ?case
    using fs_scan_bind[OF head fs_scan_bind[where r=0, simplified, OF tail fs_scan_program.Return]]
    by simp
qed

end
end
