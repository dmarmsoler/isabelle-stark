(* Title: Stark/FS_Query_Round_Prescan.thy
   License: BSD-3-Clause *)

theory FS_Query_Round_Prescan
  imports FS_Transcript_Prescan
begin

section \<open>One actual query round: scan, reset, and verify\<close>

text \<open>The header values are arbitrary fixed parameters. Authentication, both FRI
  chains, the exact modulo query sampler, and both terminal assertions are the
  existing verifier operations. No completed-map, successful-opening, clean-branch
  or collision-freedom premise is added.

  This local bridge is not the full conventional-FS compiler and supplies no
  conventional-query-budget conversion. Its staged selector is a pure fixed
  chunk; adaptive attacker replay and header/multiround composition remain
  separate obligations.\<close>

context soundness
begin

subsection \<open>The unchanged query body has a fixed successful read count\<close>

lemma fs_scan_merkle:
  "fs_scan_program 0 (protocol_merkle.check_authentication_path len idx (MerkleLeaf v) path)"
  by (induction path arbitrary: len idx)
    (auto intro!: fs_scan_bind[where n=0 and r=0, simplified] fs_scan_hash)

lemma fs_scan_authentication:
  "fs_scan_program 0 (check_authentication_path len idx v path)"
  unfolding check_authentication_path_def protocol_check_authentication_path_def
  by (rule fs_scan_merkle)

lemma fs_scan_decommitment:
  "fs_scan_program (1+floor_log(scale*clength)) (ro_query_decommitment_step fr i)"
  unfolding ro_query_decommitment_step_def Let_def
  apply (rule fs_scan_bind[OF fs_scan_read])
  apply (rule fs_scan_bind[where n="floor_log(scale*clength)" and r=0, simplified])
   apply (use fs_scan_ntimes[OF fs_scan_read, of "floor_log(scale*clength)"] in simp)
  apply (rule fs_scan_bind[where n=0 and r=0, simplified, OF fs_scan_authentication])
  apply (rule fs_scan_bind[where n=0 and r=0, simplified, OF fs_scan_assert])
  apply (rule fs_scan_program.Return)
  done

lemma fs_scan_fri_finish:
  assumes "\<And>j y pw'. fs_scan_program r (k (j,y,len div 2,pw'))"
  shows "fs_scan_program r
    (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path \<bind> k)"
  unfolding fri_layer_opening_finish_def Let_def sm_bind_assoc sm_bind_return_left
  by (intro fs_scan_bind[where n=0, simplified, OF fs_scan_assert]
    fs_scan_bind[where n=0, simplified, OF fs_scan_authentication] assms)

lemma fs_scan_fri_step:
  assumes "\<And>j y pw'. fs_scan_program r (k (j,y,len div 2,pw'))"
  shows "fs_scan_program (2+2*floor_log len+r)
    (ro_fri_layer_opening_step (b,f) (i,x,len,pw) \<bind> k)"
proof -
  have reads: "fs_scan_program (floor_log len)
    (ntimes protocol_absorb_read (floor_log len))"
    using fs_scan_ntimes[OF fs_scan_read, of "floor_log len"] by simp
  have "fs_scan_program (Suc (floor_log len + Suc (floor_log len + r)))
    (ro_fri_layer_opening_step (b,f) (i,x,len,pw) \<bind> k)"
    unfolding ro_fri_layer_opening_step_def split sm_bind_assoc
    by (intro fs_scan_program.Read fs_scan_bind[OF reads] fs_scan_fri_finish assms)
  then show ?thesis by (simp add: mult_2 add.assoc)
qed


lemma fs_scan_fri_layers:
  "fs_scan_program (fri_layers_transcript_length (length fl) len)
    (mfold (i,x,len,pw) (ro_receive_query_commits fl))"
proof (induction fl arbitrary: i x len pw)
  case Nil then show ?case
    by (simp add: ro_receive_query_commits_def fs_scan_program.Return)
next
  case (Cons bf fl)
  obtain b f where bf: "bf=(b,f)" by (cases bf) auto
  show ?case
    unfolding bf ro_receive_query_commits_def list.map mfold.simps
      length_Cons fri_layers_transcript_length.simps
    by (rule fs_scan_fri_step) (rule Cons.IH[unfolded ro_receive_query_commits_def])
qed

text \<open>This named body is an exact refactoring for proof purposes only;
  the equality below reconnects it to the production verifier.\<close>

definition fs_query_round_body
  where "fs_query_round_body fr f_fl f_final as fl final raw =
    (let idx = index (to_nat raw) in do {
      fv \<leftarrow> mmap (ro_check_decommit_on_query fr idx);
      (fi,fx,flen,fpow) \<leftarrow> mfold (idx,hd fv,clength*scale,1)
        (ro_receive_query_commits f_fl);
      assert (fx=f_final);
      (i,x,len,pw) \<leftarrow> mfold (idx,cp_eval as fv (h^idx*shift),clength*scale,1)
        (ro_receive_query_commits fl);
      assert (x=final)
    })"

lemma fs_query_round_body_exact:
  "ro_verifier_query_round_program fr f_fl f_final as fl final =
    (receive_query_index_challenge \<bind> fs_query_round_body fr f_fl f_final as fl final)"
  by (simp add: ro_verifier_query_round_program_def fs_query_round_body_def[abs_def])

lemma fs_scan_query_body:
  "fs_scan_program (verifier_query_round_transcript_length 0 (map snd f_fl) (map snd fl))
    (fs_query_round_body fr f_fl f_final as fl final raw)"
proof -
  let ?idx = "index (to_nat raw)"
  have decommit: "fs_scan_program (query_decommitment_transcript_length ?idx)
    (mmap (ro_check_decommit_on_query fr ?idx))"
    unfolding query_decommitment_transcript_length_def ro_check_decommit_on_query_def
    by (rule fs_scan_mmap) (rule fs_scan_decommitment[unfolded mult.commute[of scale clength]])
  have body: "fs_scan_program (verifier_query_round_transcript_length ?idx
      (map snd f_fl) (map snd fl))
    (fs_query_round_body fr f_fl f_final as fl final raw)"
    unfolding fs_query_round_body_def Let_def verifier_query_round_transcript_length_def
      length_map add.assoc
    apply (rule fs_scan_bind[OF decommit])
    apply (rule fs_scan_bind[OF fs_scan_fri_layers])
    apply (simp only: split_paired_all split)
    apply (rule fs_scan_bind[where n=0, simplified, OF fs_scan_assert])
    apply (rule fs_scan_bind[where r=0, simplified, OF fs_scan_fri_layers])
    apply (simp only: split_paired_all split)
    apply (rule fs_scan_assert)
    done
  show ?thesis
    using body verifier_query_round_transcript_length_index_irrelevant[of ?idx "map snd f_fl" "map snd fl" 0]
    by simp
qed


subsection \<open>Cached counted challenges and full query-round equality\<close>

lemma fs_query_receive_known:
  assumes "fmlookup (HashMap s) (QueryIndexChallenge (PQueryCounter s) (PState s))=Some a"
  shows "wp receive_query_index_challenge F s =
    F (Some(a,s\<lparr>PQueryCounter:=Suc(PQueryCounter s)\<rparr>))"
  unfolding receive_query_index_challenge_def protocol_receive_counted_tagged_random_field_element_def
  by (simp add: wp_bind wp_get wp_modify wp_return hash_known_wp[OF assms])

lemma fs_shadow_query_cached:
  fixes s :: "'f protocol_channel"
  assumes known: "fmlookup (HashMap s)
    (QueryIndexChallenge (PQueryCounter s) (PState s))=Some a"
  shows "wp (shadow_absorb ys cursor \<bind> (\<lambda>_. receive_query_index_challenge \<bind> k)) F s =
    wp (shadow_absorb ys cursor \<bind> (\<lambda>_. k a)) F
      (s\<lparr>PQueryCounter:=Suc(PQueryCounter s)\<rparr>)"
proof -
  let ?f = "\<lambda>t. t\<lparr>PQueryCounter:=Suc(PQueryCounter t)\<rparr>"
  let ?post = "\<lambda>out. case out of None \<Rightarrow> F None
    | Some(z,t) \<Rightarrow> wp (k a) F (?f t)"
  have move: "wp (shadow_absorb ys cursor \<bind> (\<lambda>_. receive_query_index_challenge \<bind> k)) F s =
    wp (shadow_absorb ys cursor) ?post s"
  proof (simp only: wp_bind, rule fs_wp_cong_on_support)
    fix out assume out: "out\<in>set_dist(execute (shadow_absorb ys cursor) s)"
    show "(case out of None \<Rightarrow> F None | Some(z,t) \<Rightarrow>
      wp receive_query_index_challenge (\<lambda>r. case r of None \<Rightarrow> F None
        | Some(y,u) \<Rightarrow> wp (k y) F u) t) = ?post out"
    proof (cases out)
      case None then show ?thesis by simp
    next
      case (Some zt)
      obtain z t where zt: "zt=(z,t)" by (cases zt) auto
      have outcome: "Some(z,t)\<in>set_dist(execute (shadow_absorb ys cursor) s)"
        using out Some zt by simp
      note props=fs_shadow_outcome[OF outcome]
      have counter: "PQueryCounter t=PQueryCounter s"
        using shadow_absorb_preserves_fields[of ys cursor] outcome
        unfolding protocol_fields_preserving_def by blast
      have lookup: "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter t) (PState t))=Some a"
        using hash_extension_lookup[OF known props(1)] props(2) counter by simp
      show ?thesis using Some zt fs_query_receive_known[OF lookup] by simp
    qed
  qed
  have transport: "wp (shadow_absorb ys cursor \<bind> (\<lambda>_. k a)) F (?f s) =
    wp (shadow_absorb ys cursor) ?post s"
    unfolding wp_bind
    using fs_shadow_transport[where f="?f" and xs=ys and cursor=cursor and s=s
      and F="\<lambda>out. case out of None \<Rightarrow> F None | Some(z,t) \<Rightarrow> wp (k a) F t"]
    by (simp split: option.splits)
  show ?thesis using move transport by simp
qed

definition fs_query_prescan
  where "fs_query_prescan n = (get \<bind> (\<lambda>s.
    hash (QueryIndexChallenge (PQueryCounter s) (PState s)) \<bind> (\<lambda>_.
      shadow_absorb (take n (PTranscript s)) (PState s))))"

lemma fs_query_prescan_invariant:
  assumes body: "\<And>a. fs_scan_program n (k a)"
  shows "wp (fs_query_prescan n \<bind> (\<lambda>_. receive_query_index_challenge \<bind> k)) F s =
    wp (receive_query_index_challenge \<bind> k) F s"
proof -
  let ?key = "QueryIndexChallenge (PQueryCounter s) (PState s)"
  let ?t = "\<lambda>a. s\<lparr>HashMap:=fmupd ?key a (HashMap s)\<rparr>"
  have tail: "wp (shadow_absorb (take n (PTranscript s)) (PState s) \<bind>
      (\<lambda>_. receive_query_index_challenge \<bind> k)) F (?t a) =
    wp (k a) F ((?t a)\<lparr>PQueryCounter:=Suc(PQueryCounter s)\<rparr>)" for a
  proof -
    have cached: "wp (shadow_absorb (take n (PTranscript s)) (PState s) \<bind>
        (\<lambda>_. receive_query_index_challenge \<bind> k)) F (?t a) =
      wp (shadow_absorb (take n (PTranscript s)) (PState s) \<bind> (\<lambda>_. k a)) F
        ((?t a)\<lparr>PQueryCounter:=Suc(PQueryCounter s)\<rparr>)"
      using fs_shadow_query_cached[where s="?t a" and a=a and
        ys="take n (PTranscript s)" and cursor="PState s" and k=k and F=F]
      by simp
    show ?thesis using cached
      fs_scan_invariant[OF body, where s="(?t a)\<lparr>PQueryCounter:=Suc(PQueryCounter s)\<rparr>"
        and F=F] by simp
  qed
  show ?thesis
    unfolding fs_query_prescan_def receive_query_index_challenge_def
      protocol_receive_counted_tagged_random_field_element_def
    using tail[unfolded receive_query_index_challenge_def
      protocol_receive_counted_tagged_random_field_element_def]
    by (simp add: sm_bind_assoc wp_bind wp_get wp_hash wp_modify wp_return)
qed

theorem fs_actual_query_prescan_wp:
  "wp (fs_query_prescan (verifier_query_round_transcript_length 0 (map snd f_fl) (map snd fl))
    \<bind> (\<lambda>_. ro_verifier_query_round_program fr f_fl f_final as fl final)) F s =
   wp (ro_verifier_query_round_program fr f_fl f_final as fl final) F s"
  unfolding fs_query_round_body_exact
  by (rule fs_query_prescan_invariant) (rule fs_scan_query_body)

theorem fs_actual_query_prescan_exact:
  "(fs_query_prescan (verifier_query_round_transcript_length 0 (map snd f_fl) (map snd fl))
    \<bind> (\<lambda>_. ro_verifier_query_round_program fr f_fl f_final as fl final)) =
   ro_verifier_query_round_program fr f_fl f_final as fl final"
  by (rule fs_wp_ext) (rule fs_actual_query_prescan_wp)


subsection \<open>The actual staged recorder and protocol-field reset\<close>

text \<open>The reset restores the saved protocol fields while retaining every oracle
  entry generated by the scan. It is a proof experiment, not a verifier change.
  The original transcript suffix is restored, so trailing words are preserved.
  Intermediate failed states are not observable in the existing option-valued
  state monad; their complete probability mass is retained.\<close>

lemma fs_record_shadow_wp:
  fixes s :: "'f protocol_channel"
  shows "wp (ro_record_staged_messages xs) F s =
    wp (shadow_absorb xs (PState s))
      (\<lambda>out. case out of None \<Rightarrow> F None | Some(cursor,t) \<Rightarrow>
        F (Some((),t\<lparr>PState:=cursor,PTranscript:=PTranscript s @ xs\<rparr>))) s"
proof (induction xs arbitrary: s F)
  case Nil
  then show ?case
    by (simp add: ro_record_staged_messages_def wp_return)
next
  case (Cons x xs)
  let ?key = "TranscriptAbsorb (PState s) x"
  let ?t = "\<lambda>a. s\<lparr>HashMap:=fmupd ?key a (HashMap s)\<rparr>"
  let ?f = "\<lambda>a t. t\<lparr>PState:=a,PTranscript:=PTranscript t@[x]\<rparr>"
  let ?post = "\<lambda>out. case out of None \<Rightarrow> F None | Some(cursor,t) \<Rightarrow>
      F (Some((),t\<lparr>PState:=cursor,PTranscript:=PTranscript s @ (x#xs)\<rparr>))"
  have step: "wp (ro_record_staged_messages xs) F (?f a (?t a)) =
      wp (shadow_absorb xs a) ?post (?t a)" for a
  proof -
    note transport = fs_shadow_transport[where f="?f a" and xs=xs and cursor=a
      and s="?t a" and F="\<lambda>out. case out of None \<Rightarrow> F None | Some(cursor,t) \<Rightarrow>
        F (Some((),t\<lparr>PState:=cursor,PTranscript:=(PTranscript s@[x])@xs\<rparr>))"]
    show ?thesis
      using Cons.IH[of F "?f a (?t a)"] transport
      by (simp cong: option.case_cong prod.case_cong)
  qed
  show ?case
    using step
    by (simp add: ro_record_staged_messages_def ro_record_staged_message_def
      wp_bind wp_get wp_hash wp_modify)
qed

lemma fs_record_reset_shadow_wp:
  fixes s saved :: "'f protocol_channel"
  shows "wp (ro_record_staged_messages xs \<bind> (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))) F s =
    wp (shadow_absorb xs (PState s) \<bind> (\<lambda>_. modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))) F s"
  unfolding wp_bind
  apply (subst fs_record_shadow_wp)
  apply (rule arg_cong[where f="\<lambda>P. wp (shadow_absorb xs (PState s)) P s"])
  apply (rule ext)
  apply (auto simp: wp_modify split: option.splits)
  done

definition fs_query_record_reset
  where "fs_query_record_reset n = (get \<bind> (\<lambda>saved.
    receive_query_index_challenge \<bind> (\<lambda>_.
    ro_record_staged_messages (take n (PTranscript saved)) \<bind> (\<lambda>_.
    modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>)))))"

lemma fs_query_record_reset_prescan_wp:
  "wp (fs_query_record_reset n) F s = wp (fs_query_prescan n \<bind> (\<lambda>_. return ())) F s"
proof -
  let ?key = "QueryIndexChallenge (PQueryCounter s) (PState s)"
  let ?t = "\<lambda>a. s\<lparr>HashMap:=fmupd ?key a (HashMap s)\<rparr>"
  let ?bump = "\<lambda>t. t\<lparr>PQueryCounter:=Suc(PQueryCounter t)\<rparr>"
  let ?scan = "shadow_absorb (take n (PTranscript s)) (PState s)"
  have transport: "wp ?scan (\<lambda>out. case out of None \<Rightarrow> F None
      | Some(cursor,t) \<Rightarrow> F (Some((),s\<lparr>HashMap:=HashMap t\<rparr>))) (?bump (?t a)) =
    wp ?scan (\<lambda>out. case out of None \<Rightarrow> F None
      | Some(cursor,t) \<Rightarrow> F (Some((),s\<lparr>HashMap:=HashMap t\<rparr>))) (?t a)" for a
    using fs_shadow_transport[where f="?bump" and xs="take n (PTranscript s)"
      and cursor="PState s" and s="?t a"
      and F="\<lambda>out. case out of None \<Rightarrow> F None
        | Some(cursor,t) \<Rightarrow> F (Some((),s\<lparr>HashMap:=HashMap t\<rparr>))"]
    by (simp split: option.splits)
  have reset: "wp ?scan (\<lambda>out. case out of None \<Rightarrow> F None
      | Some(cursor,t) \<Rightarrow> F (Some((),s\<lparr>HashMap:=HashMap t\<rparr>))) (?t a) =
    wp ?scan (\<lambda>out. case out of None \<Rightarrow> F None | Some(cursor,t) \<Rightarrow> F (Some((),t))) (?t a)" for a
  proof (rule fs_wp_cong_on_support)
    fix out assume out: "out\<in>set_dist(execute ?scan (?t a))"
    show "(case out of None \<Rightarrow> F None | Some(cursor,t) \<Rightarrow> F (Some((),s\<lparr>HashMap:=HashMap t\<rparr>))) =
      (case out of None \<Rightarrow> F None | Some(cursor,t) \<Rightarrow> F (Some((),t)))"
    proof (cases out)
      case None then show ?thesis by simp
    next
      case (Some pair)
      obtain cursor t where pair: "pair=(cursor,t)" by (cases pair) auto
      have outcome: "Some(cursor,t)\<in>set_dist(execute ?scan (?t a))"
        using out Some pair by simp
      have fields: "PState t=PState s \<and> PTranscript t=PTranscript s \<and>
        PTraceFriCounter t=PTraceFriCounter s \<and>
        PCompositionFriCounter t=PCompositionFriCounter s \<and>
        PAlphaCounter t=PAlphaCounter s \<and> PQueryCounter t=PQueryCounter s"
        using shadow_absorb_preserves_fields[of "take n (PTranscript s)" "PState s",
          unfolded protocol_fields_preserving_def, rule_format, OF outcome]
        by simp
      have eq: "s\<lparr>HashMap:=HashMap t\<rparr>=t"
        using fields by (cases s; cases t) simp
      show ?thesis using Some pair eq by simp
    qed
  qed
  show ?thesis
    unfolding fs_query_record_reset_def fs_query_prescan_def
      receive_query_index_challenge_def protocol_receive_counted_tagged_random_field_element_def
    using transport reset
    apply (simp only: wp_bind wp_get wp_hash wp_modify wp_return fs_record_shadow_wp)
    apply (simp add: transport reset wp_modify wp_return split: option.splits)
    done
qed


subsection \<open>Structural guards, including malformed transcripts\<close>

lemma fs_query_chunk_index_irrelevant:
  "verifier_query_round_chunk idx trs crs chunk =
    verifier_query_round_chunk idx' trs crs chunk"
  unfolding verifier_query_round_chunk_def query_decommitment_transcript_def powers_scaled_def
  by simp

lemma fs_actual_query_success_shape:
  assumes outcome: "Some((),t)\<in>set_dist
    (execute (ro_verifier_query_round_program fr ffl tf as cfl cf) s)"
  defines "L \<equiv> verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)"
  shows "verifier_query_round_chunk 0 (map snd ffl) (map snd cfl)
    (take L (PTranscript s))"
proof -
  obtain raw chunk where shape:
    "verifier_query_round_chunk (index (to_nat raw)) (map snd ffl) (map snd cfl) chunk"
    and split: "PTranscript s=chunk@PTranscript t"
    using ro_verifier_query_round_program_outcome_with_lookup_chain[OF outcome] by blast
  have len: "length chunk=L"
    using verifier_query_round_chunk_length[OF shape]
      verifier_query_round_transcript_length_index_irrelevant
    unfolding L_def by metis
  show ?thesis
    using shape split len fs_query_chunk_index_irrelevant[of "index(to_nat raw)" "map snd ffl" "map snd cfl" chunk 0]
    by simp
qed

definition fs_query_checked_record_reset
  where "fs_query_checked_record_reset trs crs n = (get \<bind> (\<lambda>saved.
    receive_query_index_challenge \<bind> (\<lambda>raw.
    assert (verifier_query_round_chunk (index(to_nat raw)) trs crs
      (take n (PTranscript saved))) \<bind> (\<lambda>_.
    ro_record_staged_messages (take n (PTranscript saved)) \<bind> (\<lambda>_.
    modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))))))"

lemma fs_query_checked_record_reset_wp:
  "wp (fs_query_checked_record_reset trs crs n \<bind> k) F s =
    (if verifier_query_round_chunk 0 trs crs (take n (PTranscript s)) then
      wp (fs_query_record_reset n \<bind> k) F s else F None)"
proof -
  have guard: "verifier_query_round_chunk (index(to_nat raw)) trs crs chunk =
    verifier_query_round_chunk 0 trs crs chunk" for raw chunk
    by (rule fs_query_chunk_index_irrelevant)
  show ?thesis
    unfolding fs_query_checked_record_reset_def fs_query_record_reset_def
      receive_query_index_challenge_def protocol_receive_counted_tagged_random_field_element_def
    by (cases "verifier_query_round_chunk 0 trs crs (take n (PTranscript s))")
      (simp_all add: wp_bind wp_get wp_hash wp_modify wp_return wp_throw assert_def
        fs_expect_const guard cong: option.case_cong prod.case_cong)
qed

lemma fs_actual_query_bad_shape_wp:
  assumes bad: "\<not>verifier_query_round_chunk 0 (map snd ffl) (map snd cfl)
    (take (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl))
      (PTranscript s))"
  shows "wp (ro_verifier_query_round_program fr ffl tf as cfl cf) F s = F None"
proof -
  have "wp (ro_verifier_query_round_program fr ffl tf as cfl cf) F s =
    wp (ro_verifier_query_round_program fr ffl tf as cfl cf) (\<lambda>_. F None) s"
  proof (rule fs_wp_cong_on_support)
    fix out assume out: "out\<in>set_dist
      (execute (ro_verifier_query_round_program fr ffl tf as cfl cf) s)"
    show "F out=F None"
    proof (cases out)
      case None then show ?thesis by simp
    next
      case (Some pair)
      obtain t where pair: "pair=((),t)" by (cases pair) simp
      have outcome: "Some((),t)\<in>set_dist
        (execute (ro_verifier_query_round_program fr ffl tf as cfl cf) s)"
        using out Some pair by simp
      show ?thesis using fs_actual_query_success_shape[OF outcome] bad by blast
    qed
  qed
  then show ?thesis by (simp add: wp_def fs_expect_const)
qed

theorem fs_actual_query_record_reset_exact:
  "(fs_query_record_reset (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl))
    \<bind> (\<lambda>_. ro_verifier_query_round_program fr ffl tf as cfl cf)) =
    ro_verifier_query_round_program fr ffl tf as cfl cf"
proof -
  have recorded: "fs_query_record_reset n = (fs_query_prescan n \<bind> (\<lambda>_. return ()))" for n
    by (rule fs_wp_ext) (rule fs_query_record_reset_prescan_wp)
  show ?thesis by (simp add: recorded sm_bind_assoc fs_actual_query_prescan_exact)
qed

theorem fs_actual_query_checked_record_reset_exact:
  "(fs_query_checked_record_reset (map snd ffl) (map snd cfl)
      (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl))
    \<bind> (\<lambda>_. ro_verifier_query_round_program fr ffl tf as cfl cf)) =
    ro_verifier_query_round_program fr ffl tf as cfl cf"
proof (rule fs_wp_ext)
  fix F s
  show "wp (fs_query_checked_record_reset (map snd ffl) (map snd cfl)
      (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl))
      \<bind> (\<lambda>_. ro_verifier_query_round_program fr ffl tf as cfl cf)) F s =
    wp (ro_verifier_query_round_program fr ffl tf as cfl cf) F s"
    by (simp add: fs_query_checked_record_reset_wp fs_actual_query_record_reset_exact
      fs_actual_query_bad_shape_wp)
qed


lemma fs_query_checked_record_reset_actual_driver:
  "fs_query_checked_record_reset trs crs n =
    (get \<bind> (\<lambda>saved.
      ro_checked_staged_query_program
        (A\<lparr>query_opening_stage:=(\<lambda>_ _. return (take n (PTranscript saved)))\<rparr>)
        trs crs i 1 \<bind> (\<lambda>_.
      modify (\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))))"
  by (simp add: fs_query_checked_record_reset_def sm_bind_assoc)


end

ML \<open>
  val fs_query_scan_checked = @{thms
    soundness.fs_scan_invariant
    soundness.fs_scan_query_body
    soundness.fs_actual_query_prescan_wp
    soundness.fs_actual_query_prescan_exact
    soundness.fs_record_shadow_wp
    soundness.fs_query_record_reset_prescan_wp
    soundness.fs_actual_query_success_shape
    soundness.fs_actual_query_bad_shape_wp
    soundness.fs_actual_query_record_reset_exact
    soundness.fs_actual_query_checked_record_reset_exact
    soundness.fs_query_checked_record_reset_actual_driver};
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then ()
    else error "Unexpected query scan proof dependency") fs_query_scan_checked;
  writeln ("Query scan checked conclusions: " ^
    Int.toString (length fs_query_scan_checked));
\<close>

end
