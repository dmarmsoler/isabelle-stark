(* Title: Stark/FS_Query_Phase_Prescan.thy
   License: BSD-3-Clause *)

theory FS_Query_Phase_Prescan
  imports FS_Query_Phase_Scan
begin

section \<open>Whole query phase: checked scan, reset, and verify\<close>

text \<open>For arbitrary fixed header data, arbitrary initial oracle cache and any
  number of query rounds, the existing checked staged query driver with a pure
  sliced selector can scan the entire phase before the original verifier.
  The final identity preserves every postcondition, including failure and the
  complete successful final channel. Header reconstruction, general adaptive
  callback compilation and conventional query-budget translation are separate
  obligations; no numerical or public soundness consequence is claimed here.\<close>

context soundness
begin

subsection \<open>Actual Merkle and FRI bodies\<close>

lemma fs_phase_reads_merkle:
  "fs_phase_reads 0 (protocol_merkle.check_authentication_path len idx (MerkleLeaf v) path)"
  by (induction path arbitrary: len idx)
    (auto intro!: fs_phase_reads_bind[where n=0 and r=0, simplified] fs_phase_reads_hash)

lemma fs_phase_reads_authentication:
  "fs_phase_reads 0 (check_authentication_path len idx v path)"
  unfolding check_authentication_path_def protocol_check_authentication_path_def
  by (rule fs_phase_reads_merkle)

lemma fs_phase_reads_decommitment:
  "fs_phase_reads (1+floor_log(scale*clength)) (ro_query_decommitment_step fr i)"
  unfolding ro_query_decommitment_step_def Let_def
  apply (rule fs_phase_reads_bind[OF fs_phase_reads_read])
  apply (rule fs_phase_reads_bind[where n="floor_log(scale*clength)" and r=0, simplified])
   apply (use fs_phase_reads_ntimes[OF fs_phase_reads_read, of "floor_log(scale*clength)"] in simp)
  apply (rule fs_phase_reads_bind[where n=0 and r=0, simplified, OF fs_phase_reads_authentication])
  apply (rule fs_phase_reads_bind[where n=0 and r=0, simplified, OF fs_phase_reads_assert])
  apply (rule fs_phase_reads_return)
  done

lemma fs_phase_reads_fri_finish:
  assumes "\<And>j y pw'. fs_phase_reads r (k (j,y,len div 2,pw'))"
  shows "fs_phase_reads r
    (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path \<bind> k)"
  unfolding fri_layer_opening_finish_def Let_def sm_bind_assoc sm_bind_return_left
  by (intro fs_phase_reads_bind[where n=0, simplified, OF fs_phase_reads_assert]
    fs_phase_reads_bind[where n=0, simplified, OF fs_phase_reads_authentication] assms)

lemma fs_phase_reads_fri_step:
  assumes "\<And>j y pw'. fs_phase_reads r (k (j,y,len div 2,pw'))"
  shows "fs_phase_reads (2+2*floor_log len+r)
    (ro_fri_layer_opening_step (b,f) (i,x,len,pw) \<bind> k)"
proof -
  have reads: "fs_phase_reads (floor_log len)
    (ntimes protocol_absorb_read (floor_log len))"
    using fs_phase_reads_ntimes[OF fs_phase_reads_read, of "floor_log len"] by simp
  have "fs_phase_reads (Suc (floor_log len + Suc (floor_log len + r)))
    (ro_fri_layer_opening_step (b,f) (i,x,len,pw) \<bind> k)"
    unfolding ro_fri_layer_opening_step_def split sm_bind_assoc
      replicate_Suc
    by (intro fs_phase_reads_step fs_phase_reads_bind[OF reads] fs_phase_reads_fri_finish assms)
  then show ?thesis by (simp add: mult_2 add.assoc)
qed


lemma fs_phase_reads_fri_layers:
  "fs_phase_reads (fri_layers_transcript_length (length fl) len)
    (mfold (i,x,len,pw) (ro_receive_query_commits fl))"
proof (induction fl arbitrary: i x len pw)
  case Nil then show ?case
    by (simp add: ro_receive_query_commits_def fs_phase_reads_return)
next
  case (Cons bf fl)
  obtain b f where bf: "bf=(b,f)" by (cases bf) auto
  show ?case
    unfolding bf ro_receive_query_commits_def list.map mfold.simps
      length_Cons fri_layers_transcript_length.simps
    by (rule fs_phase_reads_fri_step) (rule Cons.IH[unfolded ro_receive_query_commits_def])
qed

lemma fs_phase_reads_query_body:
  "fs_phase_reads (verifier_query_round_transcript_length 0 (map snd f_fl) (map snd fl))
    (fs_query_round_body fr f_fl f_final as fl final raw)"
proof -
  let ?idx = "index (to_nat raw)"
  have decommit: "fs_phase_reads (query_decommitment_transcript_length ?idx)
    (mmap (ro_check_decommit_on_query fr ?idx))"
    unfolding query_decommitment_transcript_length_def ro_check_decommit_on_query_def
    by (rule fs_phase_reads_mmap) (rule fs_phase_reads_decommitment[unfolded mult.commute[of scale clength]])
  have body: "fs_phase_reads (verifier_query_round_transcript_length ?idx
      (map snd f_fl) (map snd fl))
    (fs_query_round_body fr f_fl f_final as fl final raw)"
    unfolding fs_query_round_body_def Let_def verifier_query_round_transcript_length_def
      length_map add.assoc
    apply (rule fs_phase_reads_bind[OF decommit])
    apply (rule fs_phase_reads_bind[OF fs_phase_reads_fri_layers])
    apply (simp only: split_paired_all split)
    apply (rule fs_phase_reads_bind[where n=0, simplified, OF fs_phase_reads_assert])
    apply (rule fs_phase_reads_bind[where r=0, simplified, OF fs_phase_reads_fri_layers])
    apply (simp only: split_paired_all split)
    apply (rule fs_phase_reads_assert)
    done
  show ?thesis
    using body verifier_query_round_transcript_length_index_irrelevant[of ?idx "map snd f_fl" "map snd fl" 0]
    by simp
qed



lemma fs_phase_ntimes:
  assumes "fs_phase_program es m"
  shows "fs_phase_program (List.concat (replicate n es)) (ntimes m n)"
  by (induction n)
    (auto intro!: fs_phase_bind[OF assms]
      fs_phase_bind[where ds="[]", simplified] fs_phase_program.Return)

subsection \<open>The actual repeated query program\<close>

text \<open>Each repetition has one counted query draw followed by the existing
  fixed successful word count. A round retains all authentication, both FRI
  chains and both terminal assertions. The count may be zero in the generic
  helpers; no positivity or well-sized-transcript hypothesis is needed.\<close>

definition fs_query_phase_schedule
  where "fs_query_phase_schedule L n = List.concat (replicate n (False#replicate L True))"

lemma fs_actual_query_phase_program:
  "fs_phase_program
    (fs_query_phase_schedule (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)) n)
    (ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n)"
  unfolding fs_query_phase_schedule_def fs_query_round_body_exact
  by (rule fs_phase_ntimes, rule fs_phase_program.Query, rule fs_phase_reads_query_body[unfolded fs_phase_reads_def])

definition fs_query_phase_prescan
  where "fs_query_phase_prescan L n =
    (get \<bind> (\<lambda>s. fs_phase_scan (fs_query_phase_schedule L n)
      (PTranscript s) (PState s) (PQueryCounter s)))"

theorem fs_actual_query_phase_prescan_exact:
  "(fs_query_phase_prescan (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)) n
    \<bind> (\<lambda>_. ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n)) =
   ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n"
proof (rule fs_wp_ext)
  fix F s
  show "wp (fs_query_phase_prescan
      (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)) n
      \<bind> (\<lambda>_. ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n)) F s =
    wp (ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n) F s"
    unfolding fs_query_phase_prescan_def
    using fs_phase_invariant[OF fs_actual_query_phase_program, where F=F and s=s]
    by (simp add: wp_bind wp_get)
qed

subsection \<open>Ordered chunks and protocol-field transport\<close>

lemma fs_phase_scan_reads_prefix:
  "fs_phase_scan (replicate L True @ es) xs cursor qc =
    (shadow_absorb (take L xs) cursor \<bind>
      (\<lambda>c. fs_phase_scan es (drop L xs) c qc))"
  proof (induction L arbitrary: xs cursor)
  case 0 then show ?case by simp
next
  case (Suc L)
  then show ?case by (cases xs) (simp_all add: sm_bind_assoc)
qed

lemma fs_query_phase_scan_zero:
  "fs_phase_scan (fs_query_phase_schedule L 0) xs cursor qc = return cursor"
  by (simp add: fs_query_phase_schedule_def)

lemma fs_query_phase_scan_Suc:
  "fs_phase_scan (fs_query_phase_schedule L (Suc n)) xs cursor qc =
    (hash (QueryIndexChallenge qc cursor) \<bind> (\<lambda>_.
      shadow_absorb (take L xs) cursor \<bind>
        (\<lambda>c. fs_phase_scan (fs_query_phase_schedule L n) (drop L xs) c (Suc qc))))"
  by (simp add: fs_query_phase_schedule_def fs_phase_scan_reads_prefix sm_bind_assoc)

primrec fs_query_chunks :: "nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list list"
where
  "fs_query_chunks L 0 xs = []"
| "fs_query_chunks L (Suc n) xs = take L xs # fs_query_chunks L n (drop L xs)"

definition fs_query_phase_shape
  where "fs_query_phase_shape trs crs L n xs =
    list_all (verifier_query_round_chunk 0 trs crs) (fs_query_chunks L n xs)"

lemma fs_query_phase_shape_zero[simp]:
  "fs_query_phase_shape trs crs L 0 xs"
  by (simp add: fs_query_phase_shape_def)

lemma fs_query_phase_shape_Suc:
  "fs_query_phase_shape trs crs L (Suc n) xs =
    (verifier_query_round_chunk 0 trs crs (take L xs) \<and>
      fs_query_phase_shape trs crs L n (drop L xs))"
  by (simp add: fs_query_phase_shape_def)

lemma fs_phase_scan_reset_transport:
  fixes saved :: "'f protocol_channel"
    and f :: "'f protocol_channel \<Rightarrow> 'f protocol_channel"
  assumes hm: "\<And>s. HashMap (f s)=HashMap s"
    and upd: "\<And>s k y. f (s\<lparr>HashMap:=fmupd k y (HashMap s)\<rparr>) =
      (f s)\<lparr>HashMap:=fmupd k y (HashMap (f s))\<rparr>"
  shows "wp (fs_phase_scan es xs cursor qc \<bind>
      (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))) F (f s) =
    wp (fs_phase_scan es xs cursor qc \<bind>
      (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))) F s"
  using fs_phase_scan_transport[OF hm upd, where es=es and xs=xs and cursor=cursor and qc=qc and s=s
    and F="\<lambda>out. case out of None \<Rightarrow> F None | Some(x,t) \<Rightarrow>
      F (Some((),saved\<lparr>HashMap:=HashMap t\<rparr>))"]
  by (simp add: wp_bind wp_modify hm cong: option.case_cong prod.case_cong)

lemma fs_shadow_reset_transport:
  fixes saved :: "'f protocol_channel"
    and f :: "'f protocol_channel \<Rightarrow> 'f protocol_channel"
  assumes hm: "\<And>s. HashMap (f s)=HashMap s"
    and upd: "\<And>s k y. f (s\<lparr>HashMap:=fmupd k y (HashMap s)\<rparr>) =
      (f s)\<lparr>HashMap:=fmupd k y (HashMap (f s))\<rparr>"
  shows "wp (shadow_absorb xs cursor \<bind>
      (\<lambda>c. fs_phase_scan es ys c qc \<bind>
        (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>)))) F (f s) =
    wp (shadow_absorb xs cursor \<bind>
      (\<lambda>c. fs_phase_scan es ys c qc \<bind>
        (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>)))) F s"
  unfolding wp_bind
  using fs_shadow_transport[OF hm upd, where xs=xs and cursor=cursor and s=s
    and F="\<lambda>out. case out of None \<Rightarrow> F None | Some(c,t) \<Rightarrow>
      wp (fs_phase_scan es ys c qc \<bind> (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))) F t"]
    fs_phase_scan_reset_transport[OF hm upd, where saved=saved]
  by (simp add: wp_bind cong: option.case_cong prod.case_cong)

lemma fs_phase_scan_reset_record_fields:
  fixes saved s :: "'f protocol_channel"
  shows "wp (fs_phase_scan es xs cursor qc \<bind>
      (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))) F
        (s\<lparr>PState:=c,PTranscript:=ts\<rparr>) =
    wp (fs_phase_scan es xs cursor qc \<bind>
      (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))) F s"
  by (rule fs_phase_scan_reset_transport[where f="\<lambda>t. t\<lparr>PState:=c,PTranscript:=ts\<rparr>"])
    simp_all


lemma fs_shadow_counter_post:
  fixes s :: "'f protocol_channel"
  shows "wp (shadow_absorb xs cursor)
    (\<lambda>out. case out of None \<Rightarrow> v | Some(c,t) \<Rightarrow> K c t (PQueryCounter t)) s =
   wp (shadow_absorb xs cursor)
    (\<lambda>out. case out of None \<Rightarrow> v | Some(c,t) \<Rightarrow> K c t (PQueryCounter s)) s"
proof (rule fs_wp_cong_on_support)
  fix out assume out: "out\<in>set_dist(execute (shadow_absorb xs cursor) s)"
  show "(case out of None \<Rightarrow> v | Some(c,t) \<Rightarrow> K c t (PQueryCounter t)) =
    (case out of None \<Rightarrow> v | Some(c,t) \<Rightarrow> K c t (PQueryCounter s))"
  proof (cases out)
    case None then show ?thesis by simp
  next
    case (Some ct)
    obtain c t where ct: "ct=(c,t)" by (cases ct) auto
    have outcome: "Some(c,t)\<in>set_dist(execute (shadow_absorb xs cursor) s)"
      using out Some ct by simp
    have counter: "PQueryCounter t=PQueryCounter s"
      using shadow_absorb_preserves_fields[unfolded protocol_fields_preserving_def,
        rule_format, OF outcome] by simp
    show ?thesis using Some ct counter by simp
  qed
qed

subsection \<open>The existing checked staged driver\<close>

text \<open>The opening callback returns the slice at its actual stage index.
  It is pure and ignores the challenge and current buffer. The driver itself
  still draws challenges, checks the original shape guards and records messages.
  The result below accounts for its full scan before a single reset. It does
  not compile a general adaptive attacker or equate operational query counts.\<close>

lemma fs_query_driver_reset_wp:
  fixes s saved :: "'f protocol_channel"
  shows "wp (ro_checked_staged_query_program
      (A\<lparr>query_opening_stage:=(\<lambda>j _. return (take L (drop (j*L) source)))\<rparr>)
      trs crs i n \<bind> (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))) F s =
    (if fs_query_phase_shape trs crs L n (drop (i*L) source) then
      wp (fs_phase_scan (fs_query_phase_schedule L n) (drop (i*L) source)
        (PState s) (PQueryCounter s) \<bind>
        (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))) F s
     else F None)"
proof (induction n arbitrary: i s)
  case 0
  then show ?case by (simp add: fs_query_phase_scan_zero)
next
  case (Suc n)
  let ?chunk = "take L (drop (i*L) source)"
  let ?rest = "drop (Suc i*L) source"
  let ?shape = "fs_query_phase_shape trs crs L n ?rest"
  let ?driver = "ro_checked_staged_query_program
    (A\<lparr>query_opening_stage:=(\<lambda>j _. return (take L (drop (j*L) source)))\<rparr>) trs crs (Suc i) n"
  let ?reset = "modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>)"
  have recorded: "wp (ro_record_staged_messages ?chunk \<bind> (\<lambda>_. ?driver \<bind> (\<lambda>_. ?reset))) F u =
    (if ?shape then
      wp (shadow_absorb ?chunk (PState u) \<bind>
        (\<lambda>c. fs_phase_scan (fs_query_phase_schedule L n) ?rest c (PQueryCounter u) \<bind>
          (\<lambda>_. ?reset))) F u
     else F None)" for u
    using Suc.IH[of "Suc i", unfolded wp_bind]
      fs_shadow_counter_post[where xs="?chunk" and cursor="PState u" and s=u and v="F None"
        and K="\<lambda>c t qc. wp (fs_phase_scan (fs_query_phase_schedule L n) ?rest c qc \<bind>
          (\<lambda>_. ?reset)) F t", unfolded wp_bind]
    apply (cases ?shape)
     apply (simp_all only: wp_bind fs_record_shadow_wp)
    apply (simp_all add: fs_phase_scan_reset_record_fields[unfolded wp_bind]
      fs_shadow_const cong: option.case_cong prod.case_cong)
    apply (subst fs_wp_cong_on_support[where F'="\<lambda>_. F None"])
     apply (simp split: option.splits)
    apply (rule fs_shadow_const)
    done
  have bumped: "wp (shadow_absorb ?chunk (PState s) \<bind>
      (\<lambda>c. fs_phase_scan (fs_query_phase_schedule L n) ?rest c (Suc(PQueryCounter s)) \<bind>
        (\<lambda>_. ?reset))) F (u\<lparr>PQueryCounter:=Suc(PQueryCounter u)\<rparr>) =
    wp (shadow_absorb ?chunk (PState s) \<bind>
      (\<lambda>c. fs_phase_scan (fs_query_phase_schedule L n) ?rest c (Suc(PQueryCounter s)) \<bind>
        (\<lambda>_. ?reset))) F u" for u
    by (rule fs_shadow_reset_transport[where f="\<lambda>t. t\<lparr>PQueryCounter:=Suc(PQueryCounter t)\<rparr>"])
      simp_all
  have bump_hash: "wp (shadow_absorb ?chunk (PState s) \<bind>
      (\<lambda>c. fs_phase_scan (fs_query_phase_schedule L n) ?rest c (Suc(PQueryCounter s)) \<bind>
        (\<lambda>_. ?reset))) F
      (s\<lparr>HashMap:=fmupd (QueryIndexChallenge (PQueryCounter s) (PState s)) a (HashMap s),
        PQueryCounter:=Suc(PQueryCounter s)\<rparr>) =
    wp (shadow_absorb ?chunk (PState s) \<bind>
      (\<lambda>c. fs_phase_scan (fs_query_phase_schedule L n) ?rest c (Suc(PQueryCounter s)) \<bind>
        (\<lambda>_. ?reset))) F
      (s\<lparr>HashMap:=fmupd (QueryIndexChallenge (PQueryCounter s) (PState s)) a (HashMap s)\<rparr>)" for a
    using bumped[of "s\<lparr>HashMap:=fmupd (QueryIndexChallenge (PQueryCounter s) (PState s)) a (HashMap s)\<rparr>"]
    by simp
  have guard: "verifier_query_round_chunk (index(to_nat raw)) trs crs ?chunk =
    verifier_query_round_chunk 0 trs crs ?chunk" for raw
    by (rule fs_query_chunk_index_irrelevant)
  show ?case
    apply (simp only: ro_checked_staged_query_program.simps staged_adversary.select_convs
      sm_bind_return_left Let_def sm_bind_assoc)
    apply (simp only: fs_query_phase_shape_Suc fs_query_phase_scan_Suc)
    apply (simp add: receive_query_index_challenge_def
      protocol_receive_counted_tagged_random_field_element_def
      wp_bind wp_get wp_hash wp_modify wp_return wp_throw guard assert_def
      recorded[unfolded wp_bind wp_modify] bump_hash[unfolded wp_bind wp_modify, simplified]
      fs_expect_const add.commute
      cong: option.case_cong prod.case_cong)
    done
qed

subsection \<open>Malformed chunks and the full reset identity\<close>

lemma fs_actual_query_suffix:
  assumes outcome: "Some((),t)\<in>set_dist
    (execute (ro_verifier_query_round_program fr ffl tf as cfl cf) s)"
  shows "PTranscript t =
    drop (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)) (PTranscript s)"
proof -
  obtain raw chunk where shape:
    "verifier_query_round_chunk (index(to_nat raw)) (map snd ffl) (map snd cfl) chunk"
    and split: "PTranscript s=chunk@PTranscript t"
    using ro_verifier_query_round_program_outcome_with_lookup_chain[OF outcome] by blast
  have len: "length chunk=verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)"
    using verifier_query_round_chunk_length[OF shape]
      verifier_query_round_transcript_length_index_irrelevant by metis
  show ?thesis using split len by simp
qed

lemma fs_actual_query_phase_success_shape:
  assumes outcome: "Some(results,t)\<in>set_dist
    (execute (ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n) s)"
  shows "fs_query_phase_shape (map snd ffl) (map snd cfl)
    (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)) n (PTranscript s)"
  using outcome
proof (induction n arbitrary: s t results)
  case 0 then show ?case by simp
next
  case (Suc n)
  obtain u tail where head: "Some((),u)\<in>set_dist
      (execute (ro_verifier_query_round_program fr ffl tf as cfl cf) s)"
    and tail: "Some(tail,t)\<in>set_dist
      (execute (ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n) u)"
    using Suc.prems by (auto elim!: set_dist_bindE)
  show ?case
    using fs_actual_query_success_shape[OF head] Suc.IH[OF tail] fs_actual_query_suffix[OF head]
    by (simp add: fs_query_phase_shape_Suc)
qed

lemma fs_actual_query_phase_bad_shape_wp:
  assumes bad: "\<not> fs_query_phase_shape (map snd ffl) (map snd cfl)
    (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)) n (PTranscript s)"
  shows "wp (ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n) F s = F None"
proof -
  have "wp (ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n) F s =
    wp (ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n) (\<lambda>_. F None) s"
  proof (rule fs_wp_cong_on_support)
    fix out assume out: "out\<in>set_dist
      (execute (ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n) s)"
    show "F out=F None"
    proof (cases out)
      case None then show ?thesis by simp
    next
      case (Some pair)
      obtain results t where pair: "pair=(results,t)" by (cases pair) auto
      have outcome: "Some(results,t)\<in>set_dist
        (execute (ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n) s)"
        using out Some pair by simp
      show ?thesis using fs_actual_query_phase_success_shape[OF outcome] bad by blast
    qed
  qed
  then show ?thesis by (simp add: wp_def fs_expect_const)
qed

lemma fs_phase_scan_reset_self:
  fixes s :: "'f protocol_channel"
  shows "wp (fs_phase_scan es xs cursor qc \<bind>
      (\<lambda>_. modify (\<lambda>t. s\<lparr>HashMap:=HashMap t\<rparr>))) F s =
    wp (fs_phase_scan es xs cursor qc \<bind> (\<lambda>_. return ())) F s"
proof (simp only: wp_bind, rule fs_wp_cong_on_support)
  fix out assume out: "out\<in>set_dist(execute (fs_phase_scan es xs cursor qc) s)"
  show "(case out of None \<Rightarrow> F None | Some(x,t) \<Rightarrow>
    wp (modify (\<lambda>t. s\<lparr>HashMap:=HashMap t\<rparr>)) F t) =
    (case out of None \<Rightarrow> F None | Some(x,t) \<Rightarrow> wp (return ()) F t)"
  proof (cases out)
    case None then show ?thesis by simp
  next
    case (Some xt)
    obtain x t where xt: "xt=(x,t)" by (cases xt) auto
    have outcome: "Some(x,t)\<in>set_dist(execute (fs_phase_scan es xs cursor qc) s)"
      using out Some xt by simp
    show ?thesis using Some xt fs_phase_scan_outcome(2)[OF outcome]
      by (simp add: wp_modify wp_return)
  qed
qed

text \<open>The saved channel supplies all slices. Only after the entire checked
  driver finishes are its protocol fields reset, keeping the extended oracle
  map. The original transcript, including trailing words, is restored. This is
  a proof experiment over the unchanged monad, not a new protocol operation.\<close>

definition fs_query_phase_checked_record_reset
  where "fs_query_phase_checked_record_reset A trs crs L n =
    (get \<bind> (\<lambda>saved.
      ro_checked_staged_query_program
        (A\<lparr>query_opening_stage:=(\<lambda>j _. return (take L (drop (j*L) (PTranscript saved))))\<rparr>)
        trs crs 0 n \<bind> (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))))"

lemma fs_query_phase_checked_record_reset_wp:
  "wp (fs_query_phase_checked_record_reset A trs crs L n) F s =
    (if fs_query_phase_shape trs crs L n (PTranscript s) then
      wp (fs_query_phase_prescan L n \<bind> (\<lambda>_. return ())) F s else F None)"
  unfolding fs_query_phase_checked_record_reset_def fs_query_phase_prescan_def
  using fs_query_driver_reset_wp[where A=A and trs=trs and crs=crs and i=0 and n=n
    and L=L and source="PTranscript s" and saved=s and s=s and F=F]
    fs_phase_scan_reset_self[where es="fs_query_phase_schedule L n"
      and xs="PTranscript s" and cursor="PState s" and qc="PQueryCounter s" and s=s and F=F]
  by (simp add: wp_bind wp_get)

lemma fs_query_phase_checked_record_reset_bind_wp:
  "wp (fs_query_phase_checked_record_reset A trs crs L n \<bind> k) F s =
    (if fs_query_phase_shape trs crs L n (PTranscript s) then
      wp (fs_query_phase_prescan L n \<bind> (\<lambda>_. k ())) F s else F None)"
  unfolding wp_bind
  apply (subst fs_query_phase_checked_record_reset_wp)
  apply (simp add: wp_bind wp_return cong: option.case_cong prod.case_cong)
  done

theorem fs_actual_query_phase_checked_record_reset_exact:
  "(fs_query_phase_checked_record_reset A (map snd ffl) (map snd cfl)
      (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)) n
    \<bind> (\<lambda>_. ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n)) =
   ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n"
proof (rule fs_wp_ext)
  fix F s
  show "wp (fs_query_phase_checked_record_reset A (map snd ffl) (map snd cfl)
      (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)) n
      \<bind> (\<lambda>_. ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n)) F s =
    wp (ntimes (ro_verifier_query_round_program fr ffl tf as cfl cf) n) F s"
    by (simp add: fs_query_phase_checked_record_reset_bind_wp
      fs_actual_query_phase_prescan_exact fs_actual_query_phase_bad_shape_wp)
qed

end
ML \<open>
  val phase_checked = @{thms
    soundness.fs_phase_invariant
    soundness.fs_actual_query_phase_program
    soundness.fs_actual_query_phase_prescan_exact
    soundness.fs_query_driver_reset_wp
    soundness.fs_actual_query_phase_success_shape
    soundness.fs_actual_query_phase_bad_shape_wp
    soundness.fs_query_phase_checked_record_reset_wp
    soundness.fs_actual_query_phase_checked_record_reset_exact};
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then () else error "Unexpected whole-query-phase proof dependency") phase_checked;
  writeln ("Whole-query-phase checked conclusions: " ^ Int.toString (length phase_checked));
\<close>
end
