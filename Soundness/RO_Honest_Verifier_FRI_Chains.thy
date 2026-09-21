(*  Title:      Stark/RO_Honest_Verifier_FRI_Chains.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory RO_Honest_Verifier_FRI_Chains
 imports "Stark.RO_Honest_Verifier_Openings"
begin

section \<open>Failure-Sensitive Recorded FRI Chain Composition\<close>

text \<open>Compose the actual absorbing FRI layer checks over recorded canonical chunks. Local authentication and value-transition conditions are explicit component obligations, not public soundness premises. Empty chains are included; the complete hash map and counters are preserved.\<close>

lemma mfold_indexed_exact_wp:
  assumes steps: "\<And>k F. j \<le> k \<Longrightarrow> k < j+n \<Longrightarrow>
    wp (fs k (vs k)) F (ss k) = F (Some (vs (Suc k), ss (Suc k)))"
  shows "wp (mfold (vs j) (map fs [j..<j+n])) Q (ss j) =
    Q (Some (vs (j+n), ss (j+n)))"
  using steps
proof (induction n arbitrary: j Q)
  case 0
  show ?case by (simp add: wp_return)
next
  case (Suc n)
  have first: "wp (fs j (vs j)) F (ss j) =
    F (Some (vs (Suc j), ss (Suc j)))" for F
    by (rule Suc.prems) simp_all
  have tail: "wp (mfold (vs (Suc j)) (map fs [Suc j..<Suc j+n])) F (ss (Suc j)) =
    F (Some (vs (Suc j+n), ss (Suc j+n)))" for F
    by (rule Suc.IH) (use Suc.prems in auto)
  show ?case
    apply (subst upt_conv_Cons)
    apply simp
    using first tail by (simp add: wp_bind)
qed

context soundness
begin

lemma honest_fri_chunks_index_mod:
  assumes divides: "\<And>xs tree. (xs,tree) \<in> set pairs \<Longrightarrow> length xs dvd len"
  shows "honest_fri_chunks pairs (idx mod len) = honest_fri_chunks pairs idx"
  using divides
proof (induction pairs arbitrary: idx)
  case Nil
  show ?case by simp
next
  case (Cons pair pairs)
  obtain xs tree where pair: "pair=(xs,tree)" by (cases pair) auto
  have dvd: "length xs dvd len" by (rule Cons.prems[of xs tree]) (simp add: pair)
  have mod: "(idx mod len) mod length xs = idx mod length xs"
    by (rule mod_mod_cancel) (rule dvd)
  show ?case by (simp add: pair honest_fri_pair_chunk_def Let_def mod)
qed

lemma ro_absorb_lookup_chunk_cursors:
  assumes whole: "ro_absorb_lookup_chain sent first (List.concat chunks) final"
  obtains cs where "cs 0=first" "cs (length chunks)=final"
    "\<And>k. k<length chunks \<Longrightarrow> ro_absorb_lookup_chain sent (cs k) (chunks!k) (cs (Suc k))"
  using whole
proof (induction chunks arbitrary: first thesis)
  case Nil
  show ?case by (rule Nil.prems(1)[of "\<lambda>_. first"]) (use Nil.prems(2) in auto)
next
  case (Cons chunk chunks)
  obtain mid where head: "ro_absorb_lookup_chain sent first chunk mid"
    and tail: "ro_absorb_lookup_chain sent mid (List.concat chunks) final"
    using Cons.prems(2) by (auto simp: ro_absorb_lookup_chain_append_iff)
  obtain cs where init: "cs 0=mid" and fin: "cs (length chunks)=final"
    and steps: "\<And>k. k<length chunks \<Longrightarrow>
      ro_absorb_lookup_chain sent (cs k) (chunks!k) (cs (Suc k))"
    by (rule Cons.IH[OF _ tail]) blast
  let ?cs = "\<lambda>k. case k of 0 \<Rightarrow> first | Suc j \<Rightarrow> cs j"
  show ?case
    apply (rule Cons.prems(1)[of ?cs])
    using init fin head steps by (auto split: nat.splits)
qed

lemma mfold_recorded_chunks_exact_wp:
  fixes start sent :: "'f protocol_channel"
  assumes len: "length chunks=n"
    and whole: "ro_absorb_lookup_chain sent (PState start) (List.concat chunks) final"
    and ext: "sent\<le>start"
    and tr: "PTranscript start=List.concat chunks@rest"
    and steps: "\<And>k st c suffix F. k<n \<Longrightarrow>
      ro_absorb_lookup_chain sent (PState st) (chunks!k) c \<Longrightarrow> sent\<le>st \<Longrightarrow>
      PTranscript st=chunks!k@suffix \<Longrightarrow>
      wp (fs k (vs k)) F st =
        F (Some (vs (Suc k),st\<lparr>PState:=c,PTranscript:=suffix\<rparr>))"
  shows "wp (mfold (vs 0) (map fs [0..<n])) Q start =
    Q (Some (vs n,start\<lparr>PState:=final,PTranscript:=rest\<rparr>))"
proof -
  obtain cs where init: "cs 0=PState start" and fin: "cs n=final"
    and chain: "\<And>k. k<n \<Longrightarrow>
      ro_absorb_lookup_chain sent (cs k) (chunks!k) (cs (Suc k))"
    using ro_absorb_lookup_chunk_cursors[OF whole] len by blast
  let ?ss = "\<lambda>k. start\<lparr>PState:=cs k,PTranscript:=List.concat (drop k chunks)@rest\<rparr>"
  have initial: "?ss 0=start" using init tr by simp
  have step: "wp (fs k (vs k)) F (?ss k) = F (Some (vs (Suc k),?ss (Suc k)))"
    if k: "0\<le>k" "k<0+n" for k F
  proof -
    have inb: "k<n" using k by simp
    have lookup: "ro_absorb_lookup_chain sent (PState (?ss k)) (chunks!k) (cs (Suc k))"
      using chain[OF inb] by simp
    have ext': "sent\<le>?ss k" using ext by (simp add: less_eq_hash_ext_def)
    have drop: "drop k chunks=chunks!k # drop (Suc k) chunks"
      by (rule Cons_nth_drop_Suc[symmetric]) (use inb len in simp)
    have tr': "PTranscript (?ss k)=chunks!k @ (List.concat (drop (Suc k) chunks)@rest)"
      by (simp add: drop)
    show ?thesis using steps[OF inb lookup ext' tr', of F] by simp
  qed
  have result: "wp (mfold (vs 0) (map fs [0..<0+n])) Q (?ss 0) =
    Q (Some (vs (0+n),?ss (0+n)))"
    by (rule mfold_indexed_exact_wp) (rule step)
  show ?thesis using result[unfolded initial] len fin by simp
qed

lemma honest_fri_chunks_flat:
  assumes divides: "\<And>j k. j<k \<Longrightarrow> k<length pairs \<Longrightarrow>
    length (fst (pairs!k)) dvd length (fst (pairs!j))"
  shows "honest_fri_chunks pairs idx =
    map (\<lambda>(xs,tree). honest_fri_pair_chunk xs tree idx) pairs"
  using divides
proof (induction pairs arbitrary: idx)
  case Nil
  show ?case by simp
next
  case (Cons pair pairs)
  obtain xs tree where pair: "pair=(xs,tree)" by (cases pair) auto
  have divtail: "length (fst (pairs!k)) dvd length (fst (pairs!j))"
    if "j<k" "k<length pairs" for j k
    using Cons.prems[of "Suc j" "Suc k"] that by simp
  have dh: "length ys dvd length xs" if member: "(ys,tr)\<in>set pairs" for ys tr
  proof -
    obtain k where k: "k<length pairs" "pairs!k=(ys,tr)"
      using member by (meson in_set_conv_nth)
    show ?thesis using Cons.prems[of 0 "Suc k"] k by (simp add: pair)
  qed
  have tail: "honest_fri_chunks pairs (idx mod length xs)=honest_fri_chunks pairs idx"
    by (rule honest_fri_chunks_index_mod[OF dh])
  show ?case using Cons.IH[OF divtail, of idx] tail by (simp add: pair)
qed

lemma honest_fri_pair_chunk_mod:
  "honest_fri_pair_chunk xs tree (idx mod length xs)=honest_fri_pair_chunk xs tree idx"
  by (simp add: honest_fri_pair_chunk_def)

lemma ro_fri_chain_indexed_wp:
  fixes sent start :: "'f protocol_channel"
  assumes pairs: "length pairs=n" and bs: "length bs=n"
    and ct: "\<And>j. j<n \<Longrightarrow> protocol_created_tree (fst (pairs!j)) (snd (pairs!j)) sent"
    and pow: "\<And>j. j<n \<Longrightarrow> length (fst (pairs!j))=2^(N-j)"
    and idx: "\<And>j. j<n \<Longrightarrow> ix j < length (fst (pairs!j))"
    and paths: "\<And>j k. j<n \<Longrightarrow>
      length (get_authentication_path (length (fst (pairs!j))) k (snd (pairs!j))) =
        floor_log (length (fst (pairs!j)))"
    and curr: "\<And>j. j<n \<Longrightarrow> vs j=(ix j,fst (pairs!j)!ix j,length (fst (pairs!j)),pw j)"
    and successor: "\<And>j. j<n \<Longrightarrow>
      vs (Suc j) =
        (ix j mod (length (fst (pairs!j)) div 2),
        (fst (pairs!j)!ix j + fst (pairs!j)!((ix j+length (fst (pairs!j)) div 2) mod length (fst (pairs!j)))) div 2 +
          bs!j * ((fst (pairs!j)!ix j - fst (pairs!j)!((ix j+length (fst (pairs!j)) div 2) mod length (fst (pairs!j)))) div
            (2*((h^ix j)*shift)^(pw j))),
        length (fst (pairs!j)) div 2,pw j+pw j)"
    and chunks: "chunks=map (\<lambda>j. honest_fri_pair_chunk (fst (pairs!j)) (snd (pairs!j)) (ix j)) [0..<n]"
    and whole: "ro_absorb_lookup_chain sent (PState start) (List.concat chunks) final"
    and ext: "sent\<le>start"
    and tr: "PTranscript start=List.concat chunks@rest"
  shows "wp (mfold (vs 0) (ro_receive_query_commits (zip bs (map (value \<circ> snd) pairs)))) Q start =
    Q (Some (vs n,start\<lparr>PState:=final,PTranscript:=rest\<rparr>))"
proof -
  let ?fs = "\<lambda>j. ro_fri_layer_opening_step (bs!j,value (snd (pairs!j)))"
  have program: "ro_receive_query_commits (zip bs (map (value \<circ> snd) pairs)) =
    map ?fs [0..<n]"
    using pairs bs by (auto intro!: nth_equalityI simp: ro_receive_query_commits_def)
  have len: "length chunks=n" by (simp add: chunks)
  show ?thesis unfolding program
  proof (rule mfold_recorded_chunks_exact_wp[OF len whole ext tr])
    fix j st c suffix F
    assume j: "j<n"
      and chain: "ro_absorb_lookup_chain sent (PState st) (chunks!j) c"
      and ext': "sent\<le>st" and tr': "PTranscript st=chunks!j@suffix"
    have ch: "chunks!j=honest_fri_pair_chunk (fst (pairs!j)) (snd (pairs!j)) (ix j)"
      using j by (simp add: chunks)
    show "wp (?fs j (vs j)) F st = F (Some (vs (Suc j),st\<lparr>PState:=c,PTranscript:=suffix\<rparr>))"
      using ro_fri_layer_opening_honest_wp[OF ct[OF j] pow[OF j] idx[OF j]
        paths[OF j] chain[unfolded ch] ext' tr'[unfolded ch], of "bs!j" "pw j" F]
      by (simp add: curr[OF j] successor[OF j])
  qed
qed

end

ML \<open>
  val _ = List.app (fn (name, expected, th) =>
    let val oracles = Thm_Deps.all_oracles [th]
    in
      if Thm.nprems_of th = expected andalso null (Thm.hyps_of th) andalso null oracles
      then writeln (name ^ ": checked " ^ string_of_int expected ^ " explicit premises")
      else error ("Unexpected FRI-chain dependency: " ^ name)
    end)
    [("mfold_indexed_exact_wp", 1, @{thm mfold_indexed_exact_wp}),
     ("soundness.honest_fri_chunks_index_mod", 2, @{thm soundness.honest_fri_chunks_index_mod}),
     ("soundness.ro_absorb_lookup_chunk_cursors", 3, @{thm soundness.ro_absorb_lookup_chunk_cursors}),
     ("soundness.mfold_recorded_chunks_exact_wp", 6, @{thm soundness.mfold_recorded_chunks_exact_wp}),
     ("soundness.honest_fri_chunks_flat", 2, @{thm soundness.honest_fri_chunks_flat}),
     ("soundness.honest_fri_pair_chunk_mod", 1, @{thm soundness.honest_fri_pair_chunk_mod}),
     ("soundness.ro_fri_chain_indexed_wp", 13, @{thm soundness.ro_fri_chain_indexed_wp})];
\<close>

end
