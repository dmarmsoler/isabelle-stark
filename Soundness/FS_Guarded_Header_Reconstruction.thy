(* Title: Stark/FS_Guarded_Header_Reconstruction.thy
   License: BSD-3-Clause *)

theory FS_Guarded_Header_Reconstruction
  imports FS_Header_Coupling RO_Honest_Composition_Reconstruction
begin

section \<open>Guarded header reconstruction and the query boundary\<close>

text \<open>The header writer below invokes the existing commitment-prefix driver
  with pure transcript selectors. Its degree callback checks both the generated
  alpha echoes and the actual decoded-degree bound. The parser's layout guard
  checks only serialization; verifier success is not built into that guard.

  The final theorem is equality of complete probabilistic programs, including
  malformed input and failure. The hybrid reconstructs the header, restores the
  unread suffix, and uses the settled query scan and reset result. It is not yet
  the full staged experiment followed by a reset and complete verifier replay.
  General adaptive callback compilation and total-query allowance translation
  remain separate obligations; no public security bound changes here.\<close>

context soundness
begin

definition fs_header_reader where
  "fs_header_reader =
    (protocol_absorb_read \<bind> (\<lambda>fr.
     ntimes ro_receive_trace_fri_commits (ceil_log clength) \<bind> (\<lambda>ffl.
     protocol_absorb_read \<bind> (\<lambda>tf.
     mmap(replicate(length spec)ro_alpha_round) \<bind> (\<lambda>as.
     protocol_absorb_read \<bind> (\<lambda>dg.
     assert(to_nat dg\<le>maxDegree) \<bind> (\<lambda>_.
     ntimes ro_receive_composition_fri_commits (ceil_log(to_nat dg+1)) \<bind> (\<lambda>cfl.
     protocol_absorb_read \<bind> (\<lambda>cf.
     return(fr,ffl,tf,as,dg,cfl,cf))))))))))"

lemma fs_header_reader_verify:
  "ro_verify_monad = (fs_header_reader \<bind> (\<lambda>(fr,ffl,tf,as,dg,cfl,cf).
    ntimes(ro_verifier_query_round_program fr ffl tf as cfl cf) rounds))"
  by (simp add: fs_header_reader_def ro_verify_monad_def sm_bind_assoc Let_def)

definition fs_header_callbacks where
  "fs_header_callbacks A fr rs tf supplied dg crs cf =
    A\<lparr>trace_root_stage:=return fr,
      trace_fri_root_stage:=\<lambda>j bs. return(rs!j),
      trace_final_stage:=\<lambda>bs. return tf,
      degree_stage:=\<lambda>as. assert(as=supplied \<and> to_nat dg\<le>maxDegree) \<bind> (\<lambda>_. return dg),
      composition_fri_root_stage:=\<lambda>d j bs. return(crs!j),
      composition_final_stage:=\<lambda>d bs. return cf\<rparr>"

definition fs_header_writer where
  "fs_header_writer A fr rs tf supplied dg crs cf =
    (ro_commitment_prefix(fs_header_callbacks A fr rs tf supplied dg crs cf)
      \<bind> (\<lambda>((fr,rs,bs,tf,as),dg,crs,cbs,cf).
        return(fr,zip bs rs,tf,as,dg,zip cbs crs,cf)))"


lemma fs_header_writer_expansion:
  assumes lens: "length rs=ceil_log clength" "length supplied=length spec"
    "length crs=ceil_log(to_nat dg+1)"
  shows "fs_header_writer A fr rs tf supplied dg crs cf =
    (ro_record_staged_message fr \<bind> (\<lambda>_.
     fs_header_write_fri receive_trace_fri_challenge rs \<bind> (\<lambda>bs.
     ro_record_staged_message tf \<bind> (\<lambda>_.
     fs_header_guarded_alphas supplied \<bind> (\<lambda>as.
     ro_record_staged_message dg \<bind> (\<lambda>_.
     assert(to_nat dg\<le>maxDegree) \<bind> (\<lambda>_.
     fs_header_write_fri receive_composition_fri_challenge crs \<bind> (\<lambda>cbs.
     ro_record_staged_message cf \<bind> (\<lambda>_.
     return(fr,zip bs rs,tf,as,dg,zip cbs crs,cf))))))))))"
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
    unfolding fs_header_writer_def ro_commitment_prefix_def ro_header_prefix_def
      fs_header_guarded_alphas_def
    by (cases "to_nat dg\<le>maxDegree")
      (simp_all add: tr co[simplified] sel lens assert_def depth[simplified]
        sm_bind_assoc fs_throw_bind fs_throw_after)
qed


theorem fs_guarded_header_coupling:
  assumes lens: "length rs=ceil_log clength" "length supplied=length spec"
    "length crs=ceil_log(to_nat dg+1)"
  shows "fs_header_coupling (fr#rs@[tf]@supplied@[dg]@crs@[cf])
    fs_header_reader (fs_header_writer A fr rs tf supplied dg crs cf)"
proof -
  note tr = fs_header_coupling_fri[OF fs_header_coupling_trace_challenge, of rs]
  note co = fs_header_coupling_fri[OF fs_header_coupling_composition_challenge, of crs]
  show ?thesis
    unfolding fs_header_reader_def fs_header_writer_expansion[OF lens]
      ro_receive_trace_fri_commits_def ro_receive_composition_fri_commits_def
    apply (simp only: append_Cons append_Nil append_assoc)
    apply (rule fs_header_coupling_read_bind)
    apply (subst lens(1)[symmetric])
    apply (rule fs_header_coupling_bind_mapped[OF tr])
    apply (rule fs_header_coupling_read_bind)
    apply (subst lens(2)[symmetric])
    apply (rule fs_header_coupling_bind[OF fs_header_coupling_alphas])
    apply (rule fs_header_coupling_read_bind)
    apply (rule fs_header_coupling_bind[where xs="[]", simplified,
      OF fs_header_coupling_assert])
    apply (subst lens(3)[symmetric])
    apply (rule fs_header_coupling_bind_mapped[OF co])
    apply (rule fs_header_coupling_read_bind)
    apply (rule fs_header_coupling_return)
    done
qed


lemma fs_header_coupling_follow_wp:
  assumes coupling: "fs_header_coupling xs reader writer"
  shows "wp(reader \<bind> k) F (s\<lparr>PTranscript:=xs@rest\<rparr>) =
    wp(writer \<bind> (\<lambda>x. modify(\<lambda>t. t\<lparr>PTranscript:=rest\<rparr>) \<bind> (\<lambda>_. k x))) F s"
  using coupling
  by (simp add: fs_header_coupling_def wp_bind wp_modify
    cong: option.case_cong prod.case_cong)

theorem fs_guarded_header_queries_exact_wp:
  assumes lens: "length rs=ceil_log clength" "length supplied=length spec"
    "length crs=ceil_log(to_nat dg+1)"
  shows "wp ro_verify_monad F
    (s\<lparr>PTranscript:=(fr#rs@[tf]@supplied@[dg]@crs@[cf])@rest\<rparr>) =
    wp(fs_header_writer A fr rs tf supplied dg crs cf \<bind>
      (\<lambda>(fr,ffl,tf,as,dg,cfl,cf).
       modify(\<lambda>t. t\<lparr>PTranscript:=rest\<rparr>) \<bind> (\<lambda>_.
       fs_query_phase_checked_record_reset A (map snd ffl) (map snd cfl)
         (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)) rounds
       \<bind> (\<lambda>_. ntimes(ro_verifier_query_round_program fr ffl tf as cfl cf) rounds)))) F s"
  unfolding fs_header_reader_verify
  using fs_header_coupling_follow_wp[OF fs_guarded_header_coupling[OF lens],
    where F=F and s=s and rest=rest and
    k="\<lambda>(fr,ffl,tf,as,dg,cfl,cf).
      ntimes(ro_verifier_query_round_program fr ffl tf as cfl cf) rounds"]
  by (simp add: split_def fs_actual_query_phase_checked_record_reset_exact)

subsection \<open>Malformed sources and deterministic parsing\<close>

lemma fs_header_read_suffix:
  assumes out: "Some(x,t)\<in>set_dist(execute protocol_absorb_read s)"
  shows "PTranscript s=x#PTranscript t"
proof -
  obtain cursor u where nonempty: "PTranscript s\<noteq>[]"
    and x: "x=hd(PTranscript s)"
    and hashed: "Some(cursor,u)\<in>set_dist
      (execute(hash(TranscriptAbsorb(PState s)(hd(PTranscript s))))s)"
    and final: "t=u\<lparr>PState:=cursor,PTranscript:=tl(PTranscript u)\<rparr>"
    using out unfolding protocol_absorb_read_def
    by (auto simp: assert_def throw_no_outcome modify_def
      elim!: set_dist_bindE split: if_splits)
  have "PTranscript u=PTranscript s"
    by (rule protocol_hash_channel_preserves(2)[OF hashed])
  with nonempty x final show ?thesis by simp
qed

lemma fs_header_fri_suffix:
  assumes receive: "\<And>b u v. Some(b,v)\<in>set_dist(execute recv u) \<Longrightarrow>
    PTranscript v=PTranscript u"
    and out: "Some(pairs,t)\<in>set_dist
      (execute(ntimes(ro_receive_fri_commits_with recv)n)s)"
  shows "length pairs=n \<and> PTranscript s=map snd pairs@PTranscript t"
  using out
proof (induction n arbitrary: s pairs t)
  case 0 then show ?case by simp
next
  case (Suc n)
  obtain r u b v tail where read: "Some(r,u)\<in>set_dist(execute protocol_absorb_read s)"
    and draw: "Some(b,v)\<in>set_dist(execute recv u)"
    and rest: "Some(tail,t)\<in>set_dist(execute(ntimes(ro_receive_fri_commits_with recv)n)v)"
    and pairs: "pairs=(b,r)#tail"
    using Suc.prems unfolding ntimes.simps ro_receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  show ?case using fs_header_read_suffix[OF read] receive[OF draw]
    Suc.IH[OF rest] pairs by simp
qed

lemma fs_header_alphas_suffix:
  assumes out: "Some(as,t)\<in>set_dist(execute(mmap(replicate n ro_alpha_round))s)"
  shows "length as=n \<and> PTranscript s=as@PTranscript t"
  using out
proof (induction n arbitrary: s as t)
  case 0 then show ?case by simp
next
  case (Suc n)
  obtain a u x v tail where draw: "Some(a,u)\<in>set_dist(execute receive_alpha_challenge s)"
    and read: "Some(x,v)\<in>set_dist(execute protocol_absorb_read u)"
    and rest: "Some(tail,t)\<in>set_dist(execute(mmap(replicate n ro_alpha_round))v)"
    and alphas: "as=x#tail"
    using Suc.prems unfolding replicate_Suc mmap.simps ro_alpha_round_def Let_def
    by (auto simp: assert_def throw_no_outcome elim!: set_dist_bindE split: if_splits)
  have "PTranscript u=PTranscript s"
    using receive_alpha_challenge_outcome[OF draw] by simp
  with fs_header_read_suffix[OF read] Suc.IH[OF rest] alphas show ?case by simp
qed

definition fs_header_layout where
  "fs_header_layout source \<longleftrightarrow> (\<exists>fr rs tf supplied dg crs cf rest.
    length rs=ceil_log clength \<and> length supplied=length spec \<and>
    length crs=ceil_log(to_nat dg+1) \<and>
    source=(fr#rs@[tf]@supplied@[dg]@crs@[cf])@rest)"


theorem fs_verifier_success_header_layout:
  assumes out: "Some(result,t)\<in>set_dist(execute ro_verify_monad s)"
  shows "fs_header_layout(PTranscript s)"
proof -
  obtain fr tp tf supplied dg cp cf s1 s2 s3 s4 s5 s6 s7 s8 where
    rfr: "Some(fr,s1)\<in>set_dist(execute protocol_absorb_read s)"
    and tr: "Some(tp,s2)\<in>set_dist(execute
      (ntimes ro_receive_trace_fri_commits(ceil_log clength))s1)"
    and rtf: "Some(tf,s3)\<in>set_dist(execute protocol_absorb_read s2)"
    and al: "Some(supplied,s4)\<in>set_dist(execute
      (mmap(replicate(length spec)ro_alpha_round))s3)"
    and rdg: "Some(dg,s5)\<in>set_dist(execute protocol_absorb_read s4)"
    and guard: "Some((),s6)\<in>set_dist(execute(assert(to_nat dg\<le>maxDegree))s5)"
    and co: "Some(cp,s7)\<in>set_dist(execute
      (ntimes ro_receive_composition_fri_commits(ceil_log(to_nat dg+1)))s6)"
    and rcf: "Some(cf,s8)\<in>set_dist(execute protocol_absorb_read s7)"
    by (rule ro_verify_monad_outcomeE[OF out]) (rule that; assumption)
  have trace: "length tp=ceil_log clength \<and> PTranscript s1=map snd tp@PTranscript s2"
    by (rule fs_header_fri_suffix[OF _ tr[unfolded ro_receive_trace_fri_commits_def]])
      (use receive_trace_fri_challenge_outcome in auto)
  have composition: "length cp=ceil_log(to_nat dg+1) \<and> PTranscript s6=map snd cp@PTranscript s7"
    by (rule fs_header_fri_suffix[OF _ co[unfolded ro_receive_composition_fri_commits_def]])
      (use receive_composition_fri_challenge_outcome in auto)
  have same: "s6=s5" by (rule assert_unit_outcomeD(2)[OF guard])
  have source: "PTranscript s=(fr#map snd tp@[tf]@supplied@[dg]@map snd cp@[cf])@PTranscript s8"
    using fs_header_read_suffix[OF rfr] fs_header_read_suffix[OF rtf]
      fs_header_read_suffix[OF rdg] fs_header_read_suffix[OF rcf]
      fs_header_alphas_suffix[OF al] trace composition same
    by simp
  show ?thesis
    unfolding fs_header_layout_def
    apply (rule exI[where x=fr], rule exI[where x="map snd tp"], rule exI[where x=tf],
      rule exI[where x=supplied], rule exI[where x=dg], rule exI[where x="map snd cp"],
      rule exI[where x=cf], rule exI[where x="PTranscript s8"])
    using trace composition fs_header_alphas_suffix[OF al] source by simp
qed

theorem fs_verifier_malformed_header_wp:
  assumes bad: "\<not>fs_header_layout(PTranscript s)"
  shows "wp ro_verify_monad F s=F None"
proof -
  have "wp ro_verify_monad F s=wp ro_verify_monad (\<lambda>_. F None) s"
  proof (rule fs_wp_cong_on_support)
    fix out assume member: "out\<in>set_dist(execute ro_verify_monad s)"
    show "F out=F None"
      using member bad fs_verifier_success_header_layout
      by (cases out) (auto split: prod.splits)
  qed
  then show ?thesis by (simp add: fs_wp_const)
qed


definition fs_header_parse where
  "fs_header_parse source =
   (let tr=ceil_log clength;
        alpha_count=length spec;
        tail=drop(Suc tr)source;
        degree_tail=drop(Suc alpha_count)tail;
        dg=hd degree_tail;
        co=ceil_log(to_nat dg+1);
        comp_tail=tl degree_tail
    in (hd source,take tr(tl source),hd tail,take alpha_count(tl tail),dg,
        take co comp_tail,hd(drop co comp_tail),drop(Suc co)comp_tail))"

lemma fs_header_parse_encoded:
  assumes lens: "length rs=ceil_log clength" "length supplied=length spec"
    "length crs=ceil_log(to_nat dg+1)"
  shows "fs_header_parse ((fr#rs@[tf]@supplied@[dg]@crs@[cf])@rest)=
    (fr,rs,tf,supplied,dg,crs,cf,rest)"
  using lens by (simp add: fs_header_parse_def Let_def)

lemma fs_header_layout_parse:
  assumes layout: "fs_header_layout source"
    and parsed: "fs_header_parse source=(fr,rs,tf,supplied,dg,crs,cf,rest)"
  shows "length rs=ceil_log clength" "length supplied=length spec"
    "length crs=ceil_log(to_nat dg+1)"
    "source=(fr#rs@[tf]@supplied@[dg]@crs@[cf])@rest"
proof -
  obtain fr' rs' tf' supplied' dg' crs' cf' rest' where
    lens: "length rs'=ceil_log clength" "length supplied'=length spec"
      "length crs'=ceil_log(to_nat dg'+1)"
    and source: "source=(fr'#rs'@[tf']@supplied'@[dg']@crs'@[cf'])@rest'"
    using layout unfolding fs_header_layout_def by blast
  have eq: "(fr,rs,tf,supplied,dg,crs,cf,rest)=
    (fr',rs',tf',supplied',dg',crs',cf',rest')"
    using parsed fs_header_parse_encoded[OF lens, of fr' tf' cf' rest'] source by simp
  show "length rs=ceil_log clength" "length supplied=length spec"
    "length crs=ceil_log(to_nat dg+1)"
    "source=(fr#rs@[tf]@supplied@[dg]@crs@[cf])@rest"
    using eq lens source by auto
qed

definition fs_guarded_header_then_queries where
  "fs_guarded_header_then_queries A =
    (get \<bind> (\<lambda>saved.
     if fs_header_layout(PTranscript saved) then
       (case fs_header_parse(PTranscript saved) of (fr,rs,tf,supplied,dg,crs,cf,rest) \<Rightarrow>
        fs_header_writer A fr rs tf supplied dg crs cf \<bind>
        (\<lambda>(fr,ffl,tf,as,dg,cfl,cf).
          modify(\<lambda>t. t\<lparr>PTranscript:=rest\<rparr>) \<bind> (\<lambda>_.
          fs_query_phase_checked_record_reset A (map snd ffl) (map snd cfl)
            (verifier_query_round_transcript_length 0 (map snd ffl) (map snd cfl)) rounds
          \<bind> (\<lambda>_. ntimes(ro_verifier_query_round_program fr ffl tf as cfl cf) rounds))))
     else throw))"

theorem fs_guarded_header_then_queries_exact:
  "fs_guarded_header_then_queries A=ro_verify_monad"
proof (rule fs_wp_ext)
  fix F s
  show "wp(fs_guarded_header_then_queries A) F s=wp ro_verify_monad F s"
  proof (cases "fs_header_layout(PTranscript s)")
    case False
    then show ?thesis
      by (simp add: fs_guarded_header_then_queries_def wp_bind wp_get wp_throw
        fs_verifier_malformed_header_wp)
  next
    case True
    obtain fr rs tf supplied dg crs cf rest where
      parsed: "fs_header_parse(PTranscript s)=(fr,rs,tf,supplied,dg,crs,cf,rest)"
      by (cases "fs_header_parse(PTranscript s)") auto
    note layout=fs_header_layout_parse[OF True parsed]
    have updated: "s\<lparr>PTranscript:=(fr#rs@[tf]@supplied@[dg]@crs@[cf])@rest\<rparr>=s"
      using layout(4) by simp
    show ?thesis
      using fs_guarded_header_queries_exact_wp[OF layout(1-3),
        where F=F and s=s and fr=fr and tf=tf and cf=cf and rest=rest and A=A]
      by (simp add: fs_guarded_header_then_queries_def wp_bind wp_get True parsed updated[simplified])
  qed
qed

lemma fs_header_callbacks_controlled:
  "controlled_ro_program 0 (trace_root_stage(fs_header_callbacks A fr rs tf supplied dg crs cf))"
  "controlled_ro_program 0 (trace_fri_root_stage(fs_header_callbacks A fr rs tf supplied dg crs cf) j bs)"
  "controlled_ro_program 0 (trace_final_stage(fs_header_callbacks A fr rs tf supplied dg crs cf) bs)"
  "controlled_ro_program 0 (degree_stage(fs_header_callbacks A fr rs tf supplied dg crs cf) as)"
  "controlled_ro_program 0 (composition_fri_root_stage(fs_header_callbacks A fr rs tf supplied dg crs cf) d j bs)"
  "controlled_ro_program 0 (composition_final_stage(fs_header_callbacks A fr rs tf supplied dg crs cf) d bs)"
  by (auto simp: fs_header_callbacks_def assert_def fs_throw_bind split: if_splits)

end
ML \<open>
  val checked = @{thms
    soundness.fs_header_coupling_alphas
    soundness.fs_header_writer_expansion
    soundness.fs_guarded_header_coupling
    soundness.fs_guarded_header_queries_exact_wp
    soundness.fs_verifier_success_header_layout
    soundness.fs_verifier_malformed_header_wp
    soundness.fs_header_layout_parse
    soundness.fs_guarded_header_then_queries_exact
    soundness.fs_header_callbacks_controlled};
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then () else error "Unexpected guarded header proof dependency") checked;
  writeln ("Guarded header checked conclusions: " ^ Int.toString (length checked));
\<close>
end
