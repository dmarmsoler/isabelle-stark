(* Title: Stark/FS_Query_Phase_Scan.thy
   License: BSD-3-Clause *)

theory FS_Query_Phase_Scan
  imports FS_Query_Round_Prescan
begin

section \<open>Ordered read and counted-query pre-scanning\<close>

text \<open>A proof-side event schedule records transcript reads as True and counted
  query draws as False. Its hash-only scan carries the absorption cursor and
  query counter explicitly, while preserving the channel fields. Absorptions and
  counted queries remain in chronological order; only other domain-separated
  hash operations commute with them. Cached keys and output collisions are allowed.
  This layer adds no attacker interface, oracle assumption or public premise.\<close>

context soundness
begin

fun fs_phase_scan :: "bool list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> ('f, 'f protocol_channel) state_monad"
where
  "fs_phase_scan [] xs cursor qc = return cursor"
| "fs_phase_scan (True#es) [] cursor qc = fs_phase_scan es [] cursor qc"
| "fs_phase_scan (True#es) (x#xs) cursor qc =
    (hash (TranscriptAbsorb cursor x) \<bind> (\<lambda>a. fs_phase_scan es xs a qc))"
| "fs_phase_scan (False#es) xs cursor qc =
    (hash (QueryIndexChallenge qc cursor) \<bind> (\<lambda>_. fs_phase_scan es xs cursor (Suc qc)))"

text \<open>This classification concerns the existing verifier programs, not the
  adversary. Hash continuations can depend on all earlier answers. Their keys
  must be separated from both tags scanned by this proof-side schedule.\<close>

inductive fs_phase_program :: "bool list \<Rightarrow> ('a,'f protocol_channel) state_monad \<Rightarrow> bool"
where
  Return: "fs_phase_program [] (return x)"
| Fail: "fs_phase_program es throw"
| Read: "(\<And>x. fs_phase_program es (k x)) \<Longrightarrow>
    fs_phase_program (True#es) (protocol_absorb_read \<bind> k)"
| Query: "(\<And>x. fs_phase_program es (k x)) \<Longrightarrow>
    fs_phase_program (False#es) (receive_query_index_challenge \<bind> k)"
| Hash: "(\<And>a b. key \<noteq> TranscriptAbsorb a b) \<Longrightarrow>
    (\<And>i a. key \<noteq> QueryIndexChallenge i a) \<Longrightarrow>
    (\<And>x. fs_phase_program es (k x)) \<Longrightarrow>
    fs_phase_program es (hash key \<bind> k)"

lemma fs_phase_scan_const:
  "wp (fs_phase_scan es xs cursor qc) (\<lambda>_. c) s = c"
  by (induction es xs cursor qc arbitrary: s rule: fs_phase_scan.induct)
    (simp_all add: wp_bind wp_hash wp_return fs_expect_const)

lemma fs_phase_scan_transport:
  fixes f :: "'f protocol_channel \<Rightarrow> 'f protocol_channel"
  assumes hm: "\<And>s. HashMap (f s)=HashMap s"
    and upd: "\<And>s k y. f (s\<lparr>HashMap:=fmupd k y (HashMap s)\<rparr>) =
      (f s)\<lparr>HashMap:=fmupd k y (HashMap (f s))\<rparr>"
  shows "wp (fs_phase_scan es xs cursor qc) F (f s) =
    wp (fs_phase_scan es xs cursor qc)
      (\<lambda>out. case out of None \<Rightarrow> F None | Some(x,t) \<Rightarrow> F (Some(x,f t))) s"
  by (induction es xs cursor qc arbitrary: s F rule: fs_phase_scan.induct)
    (simp_all add: wp_bind wp_hash wp_return hash_dist_def hm upd[unfolded hm, symmetric])

lemma fs_phase_scan_commute:
  fixes key :: "'f protocol_hash_input"
    and k :: "'f \<Rightarrow> 'f \<Rightarrow> ('a,'f protocol_channel) state_monad"
  assumes abs: "\<And>a b. key \<noteq> TranscriptAbsorb a b"
    and qry: "\<And>i a. key \<noteq> QueryIndexChallenge i a"
  shows "(hash key \<bind> (\<lambda>x. fs_phase_scan es xs cursor qc \<bind> (\<lambda>z. k x z))) =
    (fs_phase_scan es xs cursor qc \<bind> (\<lambda>z. hash key \<bind> (\<lambda>x. k x z)))"
  by (induction es xs cursor qc arbitrary: k rule: fs_phase_scan.induct)
    (simp_all add: sm_bind_assoc fs_hash_swap_bind[OF abs] fs_hash_swap_bind[OF qry])

lemma fs_phase_scan_controlled:
  "controlled_ro_program (length es) (fs_phase_scan es xs cursor qc)"
  by (induction es xs cursor qc rule: fs_phase_scan.induct)
    (auto intro: controlled_ro_program.Weaken)

lemma fs_phase_scan_fields:
  "protocol_fields_preserving (fs_phase_scan es xs cursor qc)"
  by (rule controlled_ro_program_preserves_protocol_fields[OF fs_phase_scan_controlled])

lemma fs_phase_scan_outcome:
  fixes s t :: "'f protocol_channel"
  assumes out: "Some(x,t)\<in>set_dist(execute (fs_phase_scan es xs cursor qc) s)"
  shows "s\<le>t" "s\<lparr>HashMap:=HashMap t\<rparr>=t"
proof -
  show "s\<le>t"
    using controlled_ro_program_hash_extension_preserving[OF fs_phase_scan_controlled] out
    unfolding hash_extension_preserving_def by blast
  have fields: "PState t=PState s \<and> PTranscript t=PTranscript s \<and>
    PTraceFriCounter t=PTraceFriCounter s \<and>
    PCompositionFriCounter t=PCompositionFriCounter s \<and>
    PAlphaCounter t=PAlphaCounter s \<and> PQueryCounter t=PQueryCounter s"
    using fs_phase_scan_fields[unfolded protocol_fields_preserving_def,
      rule_format, OF out] .
  show "s\<lparr>HashMap:=HashMap t\<rparr>=t" using fields by (cases s; cases t) simp
qed

lemma fs_phase_read_cached:
  fixes s :: "'f protocol_channel"
  assumes tr: "PTranscript s=x#xs"
    and known: "fmlookup (HashMap s) (TranscriptAbsorb (PState s) x)=Some cursor"
  shows "wp (fs_phase_scan es ys c qc \<bind> (\<lambda>_. protocol_absorb_read \<bind> k)) F s =
    wp (fs_phase_scan es ys c qc \<bind> (\<lambda>_. k x)) F
      (s\<lparr>PState:=cursor,PTranscript:=xs\<rparr>)"
proof -
  let ?scan = "fs_phase_scan es ys c qc"
  let ?f = "\<lambda>t. t\<lparr>PState:=cursor,PTranscript:=xs\<rparr>"
  let ?post = "\<lambda>out. case out of None \<Rightarrow> F None
    | Some(z,t) \<Rightarrow> wp (k x) F (?f t)"
  have move: "wp (?scan \<bind> (\<lambda>_. protocol_absorb_read \<bind> k)) F s = wp ?scan ?post s"
  proof (simp only: wp_bind, rule fs_wp_cong_on_support)
    fix out assume out: "out\<in>set_dist(execute ?scan s)"
    show "(case out of None \<Rightarrow> F None | Some(z,t) \<Rightarrow>
      wp protocol_absorb_read (\<lambda>r. case r of None \<Rightarrow> F None
        | Some(y,u) \<Rightarrow> wp (k y) F u) t) = ?post out"
    proof (cases out)
      case None then show ?thesis by simp
    next
      case (Some zt)
      obtain z t where zt: "zt=(z,t)" by (cases zt) auto
      have outcome: "Some(z,t)\<in>set_dist(execute ?scan s)" using out Some zt by simp
      note props=fs_phase_scan_outcome[OF outcome]
      have fields: "PState t=PState s" "PTranscript t=PTranscript s"
        using arg_cong[OF props(2), of PState] arg_cong[OF props(2), of PTranscript]
        by simp_all
      have lookup: "fmlookup (HashMap t) (TranscriptAbsorb (PState t) x)=Some cursor"
        using hash_extension_lookup[OF known props(1)] fields(1) by simp
      show ?thesis using Some zt fs_absorb_read_known[OF _ lookup] tr fields(2) by simp
    qed
  qed
  have transport: "wp (?scan \<bind> (\<lambda>_. k x)) F (?f s) = wp ?scan ?post s"
    unfolding wp_bind
    using fs_phase_scan_transport[where f="?f" and es=es and xs=ys and cursor=c and qc=qc and s=s
      and F="\<lambda>out. case out of None \<Rightarrow> F None | Some(z,t) \<Rightarrow> wp (k x) F t"]
    by (simp split: option.splits)
  show ?thesis using move transport by simp
qed

lemma fs_phase_query_cached:
  fixes s :: "'f protocol_channel"
  assumes known: "fmlookup (HashMap s)
    (QueryIndexChallenge (PQueryCounter s) (PState s))=Some a"
  shows "wp (fs_phase_scan es xs c qc \<bind> (\<lambda>_. receive_query_index_challenge \<bind> k)) F s =
    wp (fs_phase_scan es xs c qc \<bind> (\<lambda>_. k a)) F
      (s\<lparr>PQueryCounter:=Suc(PQueryCounter s)\<rparr>)"
proof -
  let ?scan = "fs_phase_scan es xs c qc"
  let ?f = "\<lambda>t. t\<lparr>PQueryCounter:=Suc(PQueryCounter t)\<rparr>"
  let ?post = "\<lambda>out. case out of None \<Rightarrow> F None
    | Some(z,t) \<Rightarrow> wp (k a) F (?f t)"
  have move: "wp (?scan \<bind> (\<lambda>_. receive_query_index_challenge \<bind> k)) F s = wp ?scan ?post s"
  proof (simp only: wp_bind, rule fs_wp_cong_on_support)
    fix out assume out: "out\<in>set_dist(execute ?scan s)"
    show "(case out of None \<Rightarrow> F None | Some(z,t) \<Rightarrow>
      wp receive_query_index_challenge (\<lambda>r. case r of None \<Rightarrow> F None
        | Some(y,u) \<Rightarrow> wp (k y) F u) t) = ?post out"
    proof (cases out)
      case None then show ?thesis by simp
    next
      case (Some zt)
      obtain z t where zt: "zt=(z,t)" by (cases zt) auto
      have outcome: "Some(z,t)\<in>set_dist(execute ?scan s)" using out Some zt by simp
      note props=fs_phase_scan_outcome[OF outcome]
      have fields: "PState t=PState s" "PQueryCounter t=PQueryCounter s"
        using arg_cong[OF props(2), of PState] arg_cong[OF props(2), of PQueryCounter]
        by simp_all
      have lookup: "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter t) (PState t))=Some a"
        using hash_extension_lookup[OF known props(1)] fields by simp
      show ?thesis using Some zt fs_query_receive_known[OF lookup] by simp
    qed
  qed
  have transport: "wp (?scan \<bind> (\<lambda>_. k a)) F (?f s) = wp ?scan ?post s"
    unfolding wp_bind
    using fs_phase_scan_transport[where f="?f" and es=es and xs=xs and cursor=c and qc=qc and s=s
      and F="\<lambda>out. case out of None \<Rightarrow> F None | Some(z,t) \<Rightarrow> wp (k a) F t"]
    by (simp split: option.splits)
  show ?thesis using move transport by simp
qed

lemma fs_phase_empty_read:
  fixes s :: "'f protocol_channel"
  assumes nil: "PTranscript s=[]"
  shows "wp (fs_phase_scan es xs c qc \<bind> (\<lambda>_. protocol_absorb_read \<bind> k)) F s = F None"
proof -
  have eq: "wp (fs_phase_scan es xs c qc \<bind> (\<lambda>_. protocol_absorb_read \<bind> k)) F s =
    wp (fs_phase_scan es xs c qc) (\<lambda>_. F None) s"
  proof (simp only: wp_bind, rule fs_wp_cong_on_support)
    fix out assume out: "out\<in>set_dist(execute (fs_phase_scan es xs c qc) s)"
    show "(case out of None \<Rightarrow> F None | Some(z,t) \<Rightarrow>
      wp protocol_absorb_read (\<lambda>r. case r of None \<Rightarrow> F None
        | Some(x,u) \<Rightarrow> wp (k x) F u) t) = F None"
    proof (cases out)
      case None then show ?thesis by simp
    next
      case (Some zt)
      obtain z t where zt: "zt=(z,t)" by (cases zt) auto
      have outcome: "Some(z,t)\<in>set_dist(execute (fs_phase_scan es xs c qc) s)"
        using out Some zt by simp
      have tr: "PTranscript t=[]"
        using arg_cong[OF fs_phase_scan_outcome(2)[OF outcome], of PTranscript] nil by simp
      show ?thesis using Some zt tr
        by (simp add: protocol_absorb_read_def wp_bind wp_get wp_throw assert_def)
    qed
  qed
  show ?thesis using eq by (simp add: fs_phase_scan_const)
qed

subsection \<open>Failure-sensitive schedule invariance\<close>

text \<open>Every successful execution performs the scheduled reads and counted
  query draws. Failed executions may stop earlier. The scanner is total even on
  a short transcript; extra work on a subsequently failing branch is unobserved
  in the original option-valued state monad. No failed probability mass is lost.\<close>

lemma fs_phase_invariant:
  assumes "fs_phase_program es m"
  shows "wp (fs_phase_scan es (PTranscript s) (PState s) (PQueryCounter s) \<bind> (\<lambda>_. m)) F s =
    wp m F s"
  using assms
proof (induction arbitrary: s F rule: fs_phase_program.induct)
  case (Return x)
  then show ?case by (simp add: wp_return)
next
  case (Fail es)
  have post: "(\<lambda>r :: ('f \<times> 'f protocol_channel) option.
    case r of None \<Rightarrow> F None | Some(x,t) \<Rightarrow> F None) = (\<lambda>_. F None)"
    by (rule ext) (auto split: option.splits)
  show ?case by (simp only: wp_bind wp_throw post fs_phase_scan_const)
next
  case (Read es k)
  show ?case
  proof (cases "PTranscript s")
    case Nil
    then show ?thesis
      apply (simp only: Nil fs_phase_scan.simps fs_phase_empty_read[OF Nil])
      by (simp add: protocol_absorb_read_def Nil wp_bind wp_get wp_throw assert_def)
  next
    case (Cons x xs)
    let ?key = "TranscriptAbsorb (PState s) x"
    let ?t = "\<lambda>a. s\<lparr>HashMap:=fmupd ?key a (HashMap s)\<rparr>"
    have tail: "wp (fs_phase_scan es xs a (PQueryCounter s) \<bind>
        (\<lambda>_. protocol_absorb_read \<bind> k)) F (?t a) =
      wp (k x) F ((?t a)\<lparr>PState:=a,PTranscript:=xs\<rparr>)" for a
    proof -
      have cached: "wp (fs_phase_scan es xs a (PQueryCounter s) \<bind>
          (\<lambda>_. protocol_absorb_read \<bind> k)) F (?t a) =
        wp (fs_phase_scan es xs a (PQueryCounter s) \<bind> (\<lambda>_. k x)) F
          ((?t a)\<lparr>PState:=a,PTranscript:=xs\<rparr>)"
        by (rule fs_phase_read_cached) (use Cons in simp_all)
      show ?thesis using cached
        Read.IH[of "(?t a)\<lparr>PState:=a,PTranscript:=xs\<rparr>" x F] by simp
    qed
    show ?thesis using tail
      by (simp add: Cons sm_bind_assoc wp_bind wp_hash protocol_absorb_read_def
        wp_get wp_modify wp_return assert_def)
  qed
next
  case (Query es k)
  let ?key = "QueryIndexChallenge (PQueryCounter s) (PState s)"
  let ?t = "\<lambda>a. s\<lparr>HashMap:=fmupd ?key a (HashMap s)\<rparr>"
  have tail: "wp (fs_phase_scan es (PTranscript s) (PState s) (Suc(PQueryCounter s)) \<bind>
      (\<lambda>_. receive_query_index_challenge \<bind> k)) F (?t a) =
    wp (k a) F ((?t a)\<lparr>PQueryCounter:=Suc(PQueryCounter s)\<rparr>)" for a
  proof -
    have cached: "wp (fs_phase_scan es (PTranscript s) (PState s) (Suc(PQueryCounter s)) \<bind>
        (\<lambda>_. receive_query_index_challenge \<bind> k)) F (?t a) =
      wp (fs_phase_scan es (PTranscript s) (PState s) (Suc(PQueryCounter s)) \<bind>
        (\<lambda>_. k a)) F ((?t a)\<lparr>PQueryCounter:=Suc(PQueryCounter s)\<rparr>)"
      using fs_phase_query_cached[where s="?t a" and a=a and es=es
        and xs="PTranscript s" and c="PState s" and qc="Suc(PQueryCounter s)" and k=k and F=F]
      by simp
    show ?thesis using cached
      Query.IH[of "(?t a)\<lparr>PQueryCounter:=Suc(PQueryCounter s)\<rparr>" a F] by simp
  qed
  show ?case using tail[unfolded receive_query_index_challenge_def
      protocol_receive_counted_tagged_random_field_element_def]
    by (simp add: receive_query_index_challenge_def
      protocol_receive_counted_tagged_random_field_element_def
      sm_bind_assoc wp_bind wp_get wp_hash wp_modify wp_return)
next
  case (Hash key es k)
  let ?scan = "fs_phase_scan es (PTranscript s) (PState s) (PQueryCounter s)"
  have commute: "(?scan \<bind> (\<lambda>_. hash key \<bind> k)) =
    (hash key \<bind> (\<lambda>a. ?scan \<bind> (\<lambda>_. k a)))"
    by (rule fs_phase_scan_commute[OF Hash.hyps(1,2), symmetric])
  have tail: "wp (?scan \<bind> (\<lambda>_. k a)) F
      (s\<lparr>HashMap:=fmupd key a (HashMap s)\<rparr>) =
    wp (k a) F (s\<lparr>HashMap:=fmupd key a (HashMap s)\<rparr>)" for a
    using Hash.IH[of "s\<lparr>HashMap:=fmupd key a (HashMap s)\<rparr>" a F] by simp
  show ?case unfolding commute using tail[unfolded wp_bind]
    by (simp add: wp_bind wp_hash)
qed

subsection \<open>Compositional program classification\<close>

lemma fs_phase_bind:
  assumes "fs_phase_program es m" "\<And>x. fs_phase_program ds (k x)"
  shows "fs_phase_program (es@ds) (m \<bind> k)"
  using assms
  apply (induction rule: fs_phase_program.induct)
      apply (auto simp: sm_bind_assoc fs_throw_bind intro: fs_phase_program.intros)
  apply (rule fs_phase_program.Hash)
    apply assumption
   apply assumption
  apply assumption
  done

definition fs_phase_reads
  where "fs_phase_reads n m \<longleftrightarrow> fs_phase_program (replicate n True) m"

lemma fs_phase_reads_bind:
  assumes "fs_phase_reads n m" "\<And>x. fs_phase_reads r (k x)"
  shows "fs_phase_reads (n+r) (m \<bind> k)"
  using fs_phase_bind[OF assms[unfolded fs_phase_reads_def]]
  by (simp add: fs_phase_reads_def replicate_add)

lemma fs_phase_reads_return: "fs_phase_reads 0 (return x)"
  by (simp add: fs_phase_reads_def fs_phase_program.Return)

lemma fs_phase_reads_step:
  assumes "\<And>x. fs_phase_reads n (k x)"
  shows "fs_phase_reads (Suc n) (protocol_absorb_read \<bind> k)"
  using assms unfolding fs_phase_reads_def replicate_Suc
  by (rule fs_phase_program.Read)

lemma fs_phase_reads_assert:
  "fs_phase_reads 0 (assert P)"
  by (cases P) (auto simp: fs_phase_reads_def assert_def intro: fs_phase_program.intros)

lemma fs_phase_reads_read:
  "fs_phase_reads 1 protocol_absorb_read"
  using fs_phase_reads_step[where k="\<lambda>x. return x", OF fs_phase_reads_return] by simp

lemma fs_phase_reads_hash:
  assumes "\<And>a b. key \<noteq> TranscriptAbsorb a b" "\<And>i a. key \<noteq> QueryIndexChallenge i a"
  shows "fs_phase_reads 0 (hash key)"
  using fs_phase_program.Hash[where k="\<lambda>x. return x", OF assms fs_phase_program.Return]
  by (simp add: fs_phase_reads_def)

lemma fs_phase_reads_ntimes:
  assumes "fs_phase_reads n m"
  shows "fs_phase_reads (r*n) (ntimes m r)"
  by (induction r)
    (auto intro!: fs_phase_reads_bind[OF assms]
      fs_phase_reads_bind[where r=0, simplified] fs_phase_reads_return)

lemma fs_phase_reads_mmap:
  assumes "\<And>x. x\<in>set xs \<Longrightarrow> fs_phase_reads n (f x)"
  shows "fs_phase_reads (length xs*n) (mmap (map f xs))"
  using assms
proof (induction xs)
  case Nil then show ?case by (simp add: fs_phase_reads_return)
next
  case (Cons a xs)
  have head: "fs_phase_reads n (f a)" by (rule Cons.prems) simp
  have tail: "fs_phase_reads (length xs*n) (mmap (map f xs))"
    by (rule Cons.IH) (auto intro: Cons.prems)
  show ?case
    using fs_phase_reads_bind[OF head
      fs_phase_reads_bind[where r=0, simplified, OF tail fs_phase_reads_return]] by simp
qed

end
end
