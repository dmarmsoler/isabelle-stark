(* Title: Stark/FS_Full_Reconstruction_Primitives.thy
   License: BSD-3-Clause *)

theory FS_Full_Reconstruction_Primitives
  imports FS_Guarded_Header_Reconstruction RO_Honest_Verifier_Header
    RO_Honest_Verifier_Query_Replay
begin

section \<open>Guarded replay and unused transcript suffixes\<close>

text \<open>Supported header replay needs protocol-field preservation, not unconditional
  success of the degree callback. The local extension below derives that
  preservation from the existing controlled oracle syntax. Other header callbacks
  retain the existing hash-only interface.

  The suffix lemmas classify the actual verifier reads and counted query draws.
  They preserve failure and every postcondition that ignores only the final
  transcript field. This is needed because the existing staged serialization
  omits unused trailing words. No empty-transcript guard, freshness condition,
  oracle restriction or public soundness premise is introduced.\<close>

context soundness
begin

lemma fs_replay_controlled_fields:
  assumes prog: "controlled_ro_program q m"
    and out: "Some(x,t)\<in>set_dist(execute m s)"
  shows "ro_replay_state base t xs=ro_replay_state base s xs"
  using controlled_ro_program_preserves_protocol_fields[OF prog,
    unfolded protocol_fields_preserving_def, rule_format, OF out]
  by (cases s; cases t) (simp add: ro_replay_state_def)

lemma fs_controlled_degree_header_replay:
  assumes root: "hash_only_ro qr (trace_root_stage A)"
    and roots: "\<And>i bs. hash_only_ro qt (trace_fri_root_stage A i bs)"
    and tfinal: "\<And>bs. hash_only_ro qtf (trace_final_stage A bs)"
    and degree: "\<And>as. controlled_ro_program qd (degree_stage A as)"
    and croots: "\<And>dg i bs. hash_only_ro qc (composition_fri_root_stage A dg i bs)"
    and cfinal: "\<And>dg bs. hash_only_ro qcf (composition_final_stage A dg bs)"
    and out: "Some(((fr,rs,bs,tf,as),dg,crs,cbs,cv),t)\<in>set_dist
      (execute (ro_commitment_prefix A) s)"
    and guard: "to_nat dg\<le>maxDegree"
    and ext: "t\<le>base"
  shows "wp (protocol_absorb_read \<bind> (\<lambda>fr.
    ntimes ro_receive_trace_fri_commits (ceil_log clength) \<bind> (\<lambda>fl.
    protocol_absorb_read \<bind> (\<lambda>tf.
    mmap (replicate (length spec) ro_alpha_round) \<bind> (\<lambda>as.
    protocol_absorb_read \<bind> (\<lambda>dg.
    assert(to_nat dg\<le>maxDegree) \<bind> (\<lambda>_.
    ntimes ro_receive_composition_fri_commits (ceil_log(to_nat dg+1)) \<bind> (\<lambda>cfl.
    protocol_absorb_read \<bind> (\<lambda>cv. K fr fl tf as dg cfl cv)))))))))
    Q (ro_replay_state base s ((fr#rs@[tf]@as@[dg]@crs@[cv])@rest)) =
    wp (K fr (zip bs rs) tf as dg (zip cbs crs) cv) Q (ro_replay_state base t rest)"
proof -
  obtain h d dr c f where
    header: "Some((fr,rs,bs,tf,as),h)\<in>set_dist(execute (ro_header_prefix A) s)"
    and dout: "Some(dg,d)\<in>set_dist(execute (degree_stage A as) h)"
    and drec: "Some((),dr)\<in>set_dist(execute (ro_record_staged_message dg) d)"
    and chain: "Some((crs,cbs),c)\<in>set_dist
      (execute (ro_staged_composition_fri_program A dg 0 (ceil_log(to_nat dg+1)) []) dr)"
    and fout: "Some(cv,f)\<in>set_dist(execute (composition_final_stage A dg cbs) c)"
    and frec: "Some((),t)\<in>set_dist(execute (ro_record_staged_message cv) f)"
    using out unfolding ro_commitment_prefix_def
    by (auto simp: assert_def throw_no_outcome elim!: set_dist_bindE split: prod.splits if_splits)
  have fb: "f\<le>base"
    using ro_record_staged_message_absorb_lookup_state[OF frec] ext by (meson hash_ext_trans)
  have cf: "c\<le>f" using hash_only_ro_extends[OF cfinal] fout
    unfolding hash_extension_preserving_def by blast
  have cb: "c\<le>base" by (rule hash_ext_trans[OF cf fb])
  have drb: "dr\<le>base"
    using composition_prefix_properties[OF croots chain] cb by (meson hash_ext_trans)
  have db: "d\<le>base"
    using ro_record_staged_message_absorb_lookup_state[OF drec] drb by (meson hash_ext_trans)
  have hd: "h\<le>d" using controlled_ro_program_hash_extension_preserving[OF degree] dout
    unfolding hash_extension_preserving_def by blast
  have hb: "h\<le>base" by (rule hash_ext_trans[OF hd db])
  have df: "ro_replay_state base d xs=ro_replay_state base h xs" for xs
    by (rule fs_replay_controlled_fields[OF degree dout])
  have ff: "ro_replay_state base f xs=ro_replay_state base c xs" for xs
    by (rule ro_replay_hash_only_fields[OF cfinal fout])
  have dw: "wp protocol_absorb_read F (ro_replay_state base h (dg#xs)) =
    F (Some(dg,ro_replay_state base dr xs))" for F xs
    using ro_recorded_scalar_replay[OF drec drb] df by simp
  have fw: "wp protocol_absorb_read F (ro_replay_state base c (cv#xs)) =
    F (Some(cv,ro_replay_state base t xs))" for F xs
    using ro_recorded_scalar_replay[OF frec ext] ff by simp
  show ?thesis
    apply (simp only: append_assoc append_Cons append_Nil)
    apply (subst ro_trace_header_replay[OF root roots tfinal header hb,
      where rest="(dg#crs@[cv])@rest", simplified append_assoc append_Cons append_Nil])
    by (simp add: wp_bind wp_return assert_def guard dw
      ro_composition_commitments_replay[OF croots chain cb, simplified] fw)
qed

definition fs_ignores_transcript where
  "fs_ignores_transcript F \<longleftrightarrow>
    (\<forall>x s xs. F (Some(x,s\<lparr>PTranscript:=xs\<rparr>)) = F (Some(x,s)))"

lemma fs_transcript_updates:
  "s\<lparr>PTranscript:=xs,HashMap:=hm\<rparr> = s\<lparr>HashMap:=hm,PTranscript:=xs\<rparr>"
  "s\<lparr>PTranscript:=xs,PQueryCounter:=qc\<rparr> = s\<lparr>PQueryCounter:=qc,PTranscript:=xs\<rparr>"
  "s\<lparr>PTranscript:=xs,PState:=cursor\<rparr> = s\<lparr>PState:=cursor,PTranscript:=xs\<rparr>"
  by (cases s; simp)+

lemma fs_phase_suffix_wp:
  assumes prog: "fs_phase_program es m"
    and len: "length (filter (\<lambda>b. b) es) \<le> length xs"
    and obs: "fs_ignores_transcript F"
  shows "wp m F (s\<lparr>PTranscript:=xs@rest\<rparr>) = wp m F (s\<lparr>PTranscript:=xs\<rparr>)"
  using prog len
proof (induction arbitrary: s xs rule: fs_phase_program.induct)
  case (Return x)
  then show ?case using obs
    by (simp add: wp_return fs_ignores_transcript_def)
next
  case (Fail es)
  then show ?case by (simp add: wp_throw)
next
  case (Read es k)
  then obtain x tail where xs: "xs=x#tail" by (cases xs) auto
  have small: "length(filter (\<lambda>b. b) es)\<le>length tail" using Read.prems xs by simp
  show ?case
    using Read.IH[OF small]
    by (simp add: xs protocol_absorb_read_def wp_bind wp_get wp_hash
      wp_modify wp_return wp_throw assert_def hash_dist_def fs_transcript_updates
      cong: option.case_cong prod.case_cong)
next
  case (Query es k)
  then show ?case
    by (simp add: receive_query_index_challenge_def
      protocol_receive_counted_tagged_random_field_element_def
      wp_bind wp_get wp_hash wp_modify wp_return hash_dist_def fs_transcript_updates
      cong: option.case_cong prod.case_cong)
next
  case (Hash key es k)
  then show ?case
    by (simp add: wp_bind wp_hash hash_dist_def fs_transcript_updates
      cong: option.case_cong prod.case_cong)
qed

lemma fs_query_chunks_concat:
  "List.concat (fs_query_chunks L n xs) = take (n*L) xs"
  by (induction n arbitrary: xs)
    (simp_all add: take_add)

lemma fs_query_schedule_read_count:
  "length(filter (\<lambda>b. b) (fs_query_phase_schedule L n))=n*L"
  by (induction n) (simp_all add: fs_query_phase_schedule_def filter_replicate)

lemma fs_actual_query_suffix_irrelevant:
  assumes obs: "fs_ignores_transcript F"
    and enough: "n*verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl) \<le> length xs"
  shows "wp (ntimes(ro_verifier_query_round_program fr ffl tf as cfl cf) n) F
    (s\<lparr>PTranscript:=xs@rest\<rparr>) =
    wp (ntimes(ro_verifier_query_round_program fr ffl tf as cfl cf) n) F
    (s\<lparr>PTranscript:=xs\<rparr>)"
  by (rule fs_phase_suffix_wp[OF fs_actual_query_phase_program _ obs])
    (simp add: fs_query_schedule_read_count enough)

lemma fs_sliced_query_chunks:
  assumes out: "Some(chunks,t)\<in>set_dist(execute (ro_checked_staged_query_program
    (A\<lparr>query_opening_stage:=\<lambda>j _. return(take L(drop(j*L) source))\<rparr>)
    trs crs i n) s)"
  shows "chunks=fs_query_chunks L n (drop(i*L) source)"
  using out
proof (induction n arbitrary: i chunks s)
  case 0 then show ?case by simp
next
  case (Suc n)
  obtain cs w where
    tail: "Some(cs,t)\<in>set_dist(execute (ro_checked_staged_query_program
      (A\<lparr>query_opening_stage:=\<lambda>j _. return(take L(drop(j*L) source))\<rparr>)
      trs crs (Suc i) n) w)"
    and chunks: "chunks=take L(drop(i*L)source)#cs"
    by (rule ro_checked_staged_query_program_Suc_outcomeE[OF Suc.prems])
      (auto intro: that)
  show ?case using Suc.IH[OF tail] chunks
    by (simp add: add.commute)
qed

lemma fs_guarded_prefix_expansion:
  assumes lens: "length rs=ceil_log clength" "length supplied=length spec"
    "length crs=ceil_log(to_nat dg+1)"
  shows "ro_commitment_prefix(fs_header_callbacks A fr rs tf supplied dg crs cf) =
    (ro_record_staged_message fr \<bind> (\<lambda>_.
     fs_header_write_fri receive_trace_fri_challenge rs \<bind> (\<lambda>bs.
     ro_record_staged_message tf \<bind> (\<lambda>_.
     fs_header_guarded_alphas supplied \<bind> (\<lambda>as.
     ro_record_staged_message dg \<bind> (\<lambda>_.
     assert(to_nat dg\<le>maxDegree) \<bind> (\<lambda>_.
     fs_header_write_fri receive_composition_fri_challenge crs \<bind> (\<lambda>cbs.
     ro_record_staged_message cf \<bind> (\<lambda>_.
     return((fr,rs,bs,tf,as),dg,crs,cbs,cf))))))))))"
proof -
  let ?A = "fs_header_callbacks A fr rs tf supplied dg crs cf"
  have tr: "ro_staged_trace_fri_program ?A 0 (ceil_log clength) [] =
    (fs_header_write_fri receive_trace_fri_challenge rs \<bind> (\<lambda>bs. return(rs,bs)))"
    using fs_header_staged_trace_slice[where A="?A" and roots=rs and i=0
      and n="ceil_log clength" and bs="[]"]
    by (simp add: fs_header_callbacks_def lens)
  have co: "ro_staged_composition_fri_program ?A dg 0 (ceil_log(to_nat dg+1)) [] =
    (fs_header_write_fri receive_composition_fri_challenge crs \<bind> (\<lambda>bs. return(crs,bs)))"
    using fs_header_staged_composition_slice[where A="?A" and roots=crs and i=0
      and n="ceil_log(to_nat dg+1)" and bs="[]"]
    by (simp add: fs_header_callbacks_def lens)
  have depth: "to_nat dg\<le>maxDegree \<Longrightarrow> ceil_log(to_nat dg+1)\<le>ceil_log(maxDegree+1)"
    by (rule ceil_log_mono) simp
  have sel:
    "trace_root_stage ?A=return fr"
    "trace_final_stage ?A bs=return tf"
    "degree_stage ?A as=(assert(as=supplied \<and> to_nat dg\<le>maxDegree) \<bind> (\<lambda>_. return dg))"
    "composition_final_stage ?A d cs=return cf" for bs as d cs
    by (simp_all add: fs_header_callbacks_def)
  show ?thesis
    unfolding ro_commitment_prefix_def ro_header_prefix_def
      fs_header_guarded_alphas_def
    by (cases "to_nat dg\<le>maxDegree")
      (simp_all add: tr co[simplified] sel lens assert_def depth[simplified]
        sm_bind_assoc fs_throw_bind fs_throw_after)
qed
lemma fs_write_fri_length:
  assumes out: "Some(bs,t)\<in>set_dist(execute(fs_header_write_fri recv rs) s)"
  shows "length bs=length rs"
  using out
  by (induction rs arbitrary: s bs) (auto elim!: set_dist_bindE)

lemma fs_guarded_prefix_outcome:
  assumes lens: "length rs=ceil_log clength" "length supplied=length spec"
    "length crs=ceil_log(to_nat dg+1)"
    and out: "Some(prefix,t)\<in>set_dist(execute
      (ro_commitment_prefix(fs_header_callbacks A fr rs tf supplied dg crs cf)) s)"
  obtains bs cbs where
    "prefix=((fr,rs,bs,tf,supplied),dg,crs,cbs,cf)"
    "length bs=length rs" "length cbs=length crs" "to_nat dg\<le>maxDegree"
proof -
  obtain bs cbs s1 s2 s3 s4 where
    tr: "Some(bs,s2)\<in>set_dist(execute(fs_header_write_fri receive_trace_fri_challenge rs) s1)"
    and co: "Some(cbs,s4)\<in>set_dist(execute(fs_header_write_fri receive_composition_fri_challenge crs) s3)"
    and eq: "prefix=((fr,rs,bs,tf,supplied),dg,crs,cbs,cf)"
    and guard: "to_nat dg\<le>maxDegree"
    using out unfolding fs_guarded_prefix_expansion[OF lens] fs_header_guarded_alphas_def
    by (auto simp: assert_def throw_no_outcome elim!: set_dist_bindE split: if_splits)
  show thesis by (rule that[OF eq fs_write_fri_length[OF tr] fs_write_fri_length[OF co] guard])
qed

lemma fs_checked_query_word_count:
  assumes out: "Some(chunks,t)\<in>set_dist(execute
    (ro_checked_staged_query_program A trs crs i n) s)"
  shows "length(List.concat chunks)=n*verifier_query_round_transcript_length 0 trs crs"
  using out
proof (induction n arbitrary: i chunks s)
  case 0 then show ?case by simp
next
  case (Suc n)
  obtain raw chunk cs w where
    guard: "verifier_query_round_chunk (index(to_nat raw)) trs crs chunk"
    and tail: "Some(cs,t)\<in>set_dist(execute
      (ro_checked_staged_query_program A trs crs (Suc i) n) w)"
    and chunks: "chunks=chunk#cs"
    by (rule ro_checked_staged_query_program_Suc_outcomeE[OF Suc.prems])
      (rule that; assumption)
  have shape: "verifier_query_round_chunk 0 trs crs chunk"
    using guard fs_query_chunk_index_irrelevant[of "index(to_nat raw)" trs crs chunk] by simp
  show ?case using verifier_query_round_chunk_length[OF shape] Suc.IH[OF tail] chunks by simp
qed

lemma fs_sliced_query_reset_transcript:
  "wp (ro_checked_staged_query_program
    (A\<lparr>query_opening_stage:=\<lambda>j _. return(take L(drop(j*L)source))\<rparr>)
    trs crs i n \<bind> (\<lambda>_. modify(\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))) F
      (s\<lparr>PTranscript:=xs\<rparr>) =
   wp (ro_checked_staged_query_program
    (A\<lparr>query_opening_stage:=\<lambda>j _. return(take L(drop(j*L)source))\<rparr>)
    trs crs i n \<bind> (\<lambda>_. modify(\<lambda>t. saved\<lparr>HashMap:=HashMap t\<rparr>))) F s"
  using fs_phase_scan_reset_transport[where f="\<lambda>t. t\<lparr>PTranscript:=xs\<rparr>"
    and saved=saved and es="fs_query_phase_schedule L n" and xs="drop(i*L)source"
    and cursor="PState s" and qc="PQueryCounter s" and F=F and s=s]
  by (simp add: fs_query_driver_reset_wp)

lemma fs_sliced_query_replay_suffix:
  assumes out: "Some(chunks,t)\<in>set_dist(execute (ro_checked_staged_query_program
    (A\<lparr>query_opening_stage:=\<lambda>j _. return(take
      (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl))
      (drop(j*verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl))source))\<rparr>)
    (map snd ffl) (map snd cfl) 0 n) s)"
    and obs: "fs_ignores_transcript F"
  shows "wp(ntimes(ro_verifier_query_round_program fr ffl tf as cfl cf)n) F
      (base\<lparr>PTranscript:=List.concat chunks\<rparr>) =
    wp(ntimes(ro_verifier_query_round_program fr ffl tf as cfl cf)n) F
      (base\<lparr>PTranscript:=source\<rparr>)"
proof -
  let ?L = "verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)"
  have concat: "List.concat chunks=take(n*?L)source"
    using fs_sliced_query_chunks[OF out] by (simp add: fs_query_chunks_concat)
  have len: "length(List.concat chunks)=n*?L"
    by (rule fs_checked_query_word_count[OF out])
  have enough: "n*?L\<le>length(List.concat chunks)" using len by simp
  show ?thesis
    using fs_actual_query_suffix_irrelevant[OF obs enough,
      where rest="drop(n*?L)source" and s=base and fr=fr and tf=tf and as=as and cf=cf]
    by (simp add: concat)
qed


end
end
