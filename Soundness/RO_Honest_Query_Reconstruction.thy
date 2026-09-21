(*  Title:      Stark/RO_Honest_Query_Reconstruction.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory RO_Honest_Query_Reconstruction
 imports "Stark.RO_Honest_Composition_Reconstruction"
begin

section \<open>Commitment Replay and Checked Query Completion\<close>

text \<open>Hash-only reconstruction of the completed commitment prefix, with unchanged query-callback updates and a format-only checked-query no-failure rule. Generic helper premises are discharged by the concrete honest producer; none are public soundness premises.\<close>
context soundness
begin

definition shadow_header_cursor
  :: "'f staged_adversary \<Rightarrow> 'f \<Rightarrow>
    (('f \<times> 'f list \<times> 'f list \<times> 'f \<times> 'f list) \<times> 'f, 'f protocol_channel) state_monad"
where
  "shadow_header_cursor A cursor =
    (trace_root_stage A \<bind> (\<lambda>fr.
     hash (TranscriptAbsorb cursor fr) \<bind> (\<lambda>c.
     shadow_trace A 0 (ceil_log clength) [] c \<bind> (\<lambda>(rs,bs,c').
     trace_final_stage A bs \<bind> (\<lambda>final.
     hash (TranscriptAbsorb c' final) \<bind> (\<lambda>c''.
     shadow_alphas 0 (length spec) c'' \<bind> (\<lambda>(as,last_cursor).
     return ((fr,rs,bs,final,as),last_cursor))))))))"

lemma shadow_header_cursor_hash_only:
  assumes root: "hash_only_ro qr (trace_root_stage A)"
    and roots: "\<And>i bs. hash_only_ro qt (trace_fri_root_stage A i bs)"
    and final: "\<And>bs. hash_only_ro qf (trace_final_stage A bs)"
  shows "hash_only_ro (qr+1+((qt+2)*ceil_log clength)+qf+1+2*length spec)
    (shadow_header_cursor A cursor)"
proof -
  have step: "hash_only_ro (qr + Suc (((qt+2)*ceil_log clength) + (qf + Suc (2*length spec))))
      (shadow_header_cursor A cursor)"
    unfolding shadow_header_cursor_def
    apply (rule hash_only_ro_bind[OF root])
    apply (rule hash_only_ro.Ask)
    apply (rule hash_only_ro_bind[OF shadow_trace_hash_only[OF roots]])
    apply (simp only: case_prod_unfold)
    apply (rule hash_only_ro_bind[OF final])
    apply (rule hash_only_ro.Ask)
    apply (rule hash_only_ro_map)
    apply (rule shadow_alphas_hash_only)
    done
  show ?thesis using step by (simp add: algebra_simps)
qed

lemma shadow_header_cursor_replay:
  assumes root: "hash_only_ro qr (trace_root_stage A)"
    and roots: "\<And>i bs. hash_only_ro qt (trace_fri_root_stage A i bs)"
    and final: "\<And>bs. hash_only_ro qf (trace_final_stage A bs)"
    and out: "Some (data,t) \<in> set_dist (execute (ro_header_prefix A) s)"
    and counters: "PTraceFriCounter s=0" "PAlphaCounter s=0"
    and ext: "t \<le> u"
  shows "wp (shadow_header_cursor A (PState s)) Q u = Q (Some ((data,PState t),u))"
proof -
  obtain fr s1 s2 rs bs s3 ffinal s4 s5 as where
    root_out: "Some (fr,s1) \<in> set_dist (execute (trace_root_stage A) s)"
    and root_rec: "Some ((),s2) \<in> set_dist (execute (ro_record_staged_message fr) s1)"
    and trace_out: "Some ((rs,bs),s3) \<in> set_dist
      (execute (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and final_out: "Some (ffinal,s4) \<in> set_dist (execute (trace_final_stage A bs) s3)"
    and final_rec: "Some ((),s5) \<in> set_dist (execute (ro_record_staged_message ffinal) s4)"
    and alphas: "Some (as,t) \<in> set_dist (execute (ro_staged_alpha_program (length spec)) s5)"
    and data: "data=(fr,rs,bs,ffinal,as)"
    using out unfolding ro_header_prefix_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  note rfields = hash_only_ro_fields[OF root root_out]
  note rr = ro_record_staged_message_absorb_lookup_state[OF root_rec]
  note rrc = ro_record_staged_message_counter_preserves[OF root_rec]
  note tp = trace_prefix_properties[OF roots trace_out]
  note ffields = hash_only_ro_fields[OF final final_out]
  note frp = ro_record_staged_message_absorb_lookup_state[OF final_rec]
  note frc = ro_record_staged_message_counter_preserves[OF final_rec]
  have s3s4: "s3 \<le> s4" using hash_only_ro_extends[OF final] final_out
    unfolding hash_extension_preserving_def by blast
  have s5t: "s5 \<le> t" using ro_staged_alpha_program_absorb_lookup_chain[OF alphas] by simp
  have s5u: "s5 \<le> u" by (rule hash_ext_trans[OF s5t ext])
  have s4u: "s4 \<le> u" using frp s5u by (meson hash_ext_trans)
  have s3u: "s3 \<le> u" by (rule hash_ext_trans[OF s3s4 s4u])
  have s2u: "s2 \<le> u" using tp s3u by (meson hash_ext_trans)
  have s1u: "s1 \<le> u" using rr s2u by (meson hash_ext_trans)
  have rw: "wp (trace_root_stage A) F u=F (Some (fr,u))" for F
    using hash_only_ro_replayable[OF root] root_out s1u unfolding replayable_ro_def by blast
  have rk: "fmlookup (HashMap u) (TranscriptAbsorb (PState s) fr)=Some (PState s2)"
    using hash_extension_lookup[OF conjunct1[OF rr] s2u] rfields by simp
  have trctr: "PTraceFriCounter s2=0" using counters rfields rrc by simp
  have tw: "wp (shadow_trace A 0 (ceil_log clength) [] (PState s2)) F u =
      F (Some ((rs,bs,PState s3),u))" for F
    by (rule shadow_trace_replay[OF roots trace_out trctr s3u])
  have fw: "wp (trace_final_stage A bs) F u=F (Some (ffinal,u))" for F
    using hash_only_ro_replayable[OF final] final_out s4u unfolding replayable_ro_def by blast
  have fk: "fmlookup (HashMap u) (TranscriptAbsorb (PState s3) ffinal)=Some (PState s5)"
    using hash_extension_lookup[OF conjunct1[OF frp] s5u] ffields by simp
  have actr: "PAlphaCounter s5=0" using counters rfields rrc tp ffields frc by simp
  have aw: "wp (shadow_alphas 0 (length spec) (PState s5)) F u =
      F (Some ((as,PState t),u))" for F
    using shadow_alphas_replay[OF alphas ext, of F] actr by simp
  show ?thesis unfolding shadow_header_cursor_def
    by (simp add: wp_bind wp_return rw hash_known_wp[OF rk] tw fw hash_known_wp[OF fk] aw data)
qed


lemma trace_prefix_untouched_counters:
  assumes roots: "\<And>j bs. hash_only_ro q (trace_fri_root_stage A j bs)"
    and out: "Some ((rs,bs'),t) \<in> set_dist (execute (ro_staged_trace_fri_program A i n bs) s)"
  shows "PCompositionFriCounter t=PCompositionFriCounter s \<and> PQueryCounter t=PQueryCounter s"
  using out
proof (induction n arbitrary: i bs s rs bs' t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain r s1 s2 b s3 rest where
    rout: "Some (r,s1) \<in> set_dist (execute (trace_fri_root_stage A i bs) s)"
    and rec: "Some ((),s2) \<in> set_dist (execute (ro_record_staged_message r) s1)"
    and recv: "Some (b,s3) \<in> set_dist (execute receive_trace_fri_challenge s2)"
    and tail: "Some ((rest,bs'),t) \<in> set_dist
      (execute (ro_staged_trace_fri_program A (Suc i) n (bs@[b])) s3)"
    using Suc.prems by (auto elim!: set_dist_bindE split: prod.splits)
  show ?case using Suc.IH[OF tail] hash_only_ro_fields[OF roots rout]
    ro_record_staged_message_counter_preserves[OF rec]
    receive_trace_fri_challenge_counter_outcome[OF recv] by simp
qed

lemma ro_header_untouched_counters:
  assumes root: "hash_only_ro qr (trace_root_stage A)"
    and roots: "\<And>i bs. hash_only_ro qt (trace_fri_root_stage A i bs)"
    and final: "\<And>bs. hash_only_ro qf (trace_final_stage A bs)"
    and out: "Some (data,t) \<in> set_dist (execute (ro_header_prefix A) s)"
  shows "PCompositionFriCounter t=PCompositionFriCounter s \<and> PQueryCounter t=PQueryCounter s"
proof -
  obtain fr s1 s2 rs bs s3 tf s4 s5 as where
    rout: "Some (fr,s1) \<in> set_dist (execute (trace_root_stage A) s)"
    and rrec: "Some ((),s2) \<in> set_dist (execute (ro_record_staged_message fr) s1)"
    and tr: "Some ((rs,bs),s3) \<in> set_dist
      (execute (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and fout: "Some (tf,s4) \<in> set_dist (execute (trace_final_stage A bs) s3)"
    and frec: "Some ((),s5) \<in> set_dist (execute (ro_record_staged_message tf) s4)"
    and alphas: "Some (as,t) \<in> set_dist (execute (ro_staged_alpha_program (length spec)) s5)"
    using out unfolding ro_header_prefix_def by (auto elim!: set_dist_bindE split: prod.splits)
  show ?thesis using hash_only_ro_fields[OF root rout]
    ro_record_staged_message_counter_preserves[OF rrec]
    trace_prefix_untouched_counters[OF roots tr]
    hash_only_ro_fields[OF final fout]
    ro_record_staged_message_counter_preserves[OF frec]
    ro_staged_alpha_program_counters[OF alphas] by simp
qed

definition shadow_commitment_prefix where
  "shadow_commitment_prefix A cursor =
    (shadow_header_cursor A cursor \<bind> (\<lambda>(data,c).
     case data of (fr,rs,bs,tf,as) \<Rightarrow>
     degree_stage A as \<bind> (\<lambda>dg.
     hash (TranscriptAbsorb c dg) \<bind> (\<lambda>c'.
     shadow_composition A dg 0 (ceil_log (to_nat dg+1)) [] c' \<bind> (\<lambda>(crs,cbs,c'').
     composition_final_stage A dg cbs \<bind> (\<lambda>cv.
     hash (TranscriptAbsorb c'' cv) \<bind> (\<lambda>_.
     return (data,dg,crs,cbs,cv))))))))"


lemma shadow_commitment_prefix_replay:
  assumes root: "hash_only_ro qr (trace_root_stage A)"
    and roots: "\<And>i bs. hash_only_ro qt (trace_fri_root_stage A i bs)"
    and tfinal: "\<And>bs. hash_only_ro qtf (trace_final_stage A bs)"
    and degree_cb: "\<And>as. hash_only_ro qd (degree_stage A as)"
    and croots: "\<And>dg i bs. hash_only_ro qc (composition_fri_root_stage A dg i bs)"
    and cfinal: "\<And>dg bs. hash_only_ro qcf (composition_final_stage A dg bs)"
    and out: "Some (((fr,rs,bs,tf,as),dg,crs,cbs,cv),sent) \<in> set_dist
      (execute (ro_commitment_prefix A) s)"
    and ctr: "PTraceFriCounter s=0" "PAlphaCounter s=0" "PCompositionFriCounter s=0"
    and ext: "sent \<le> u"
  shows "wp (shadow_commitment_prefix A (PState s)) Q u =
    Q (Some (((fr,rs,bs,tf,as),dg,crs,cbs,cv),u))"
proof -
  obtain h d w c f where
    header: "Some ((fr,rs,bs,tf,as),h) \<in> set_dist (execute (ro_header_prefix A) s)"
    and deg: "Some (dg,d) \<in> set_dist (execute (degree_stage A as) h)"
    and drec: "Some ((),w) \<in> set_dist (execute (ro_record_staged_message dg) d)"
    and comp: "Some ((crs,cbs),c) \<in> set_dist
      (execute (ro_staged_composition_fri_program A dg 0 (ceil_log (to_nat dg+1)) []) w)"
    and fin: "Some (cv,f) \<in> set_dist (execute (composition_final_stage A dg cbs) c)"
    and frec: "Some ((),sent) \<in> set_dist (execute (ro_record_staged_message cv) f)"
    using out unfolding ro_commitment_prefix_def
    by (auto simp: assert_def throw_no_outcome elim!: set_dist_bindE split: prod.splits if_splits)
  note df = hash_only_ro_fields[OF degree_cb deg]
  note dr = ro_record_staged_message_absorb_lookup_state[OF drec]
  note dc = ro_record_staged_message_counter_preserves[OF drec]
  note cp = composition_prefix_properties[OF croots comp]
  note ff = hash_only_ro_fields[OF cfinal fin]
  note fre = ro_record_staged_message_absorb_lookup_state[OF frec]
  have cf: "c \<le> f" using hash_only_ro_extends[OF cfinal] fin
    unfolding hash_extension_preserving_def by blast
  have fu: "f \<le> u" using fre ext by (meson hash_ext_trans)
  have cu: "c \<le> u" by (rule hash_ext_trans[OF cf fu])
  have wu: "w \<le> u" using cp cu by (meson hash_ext_trans)
  have du: "d \<le> u" using dr wu by (meson hash_ext_trans)
  have hd: "h \<le> d" using hash_only_ro_extends[OF degree_cb] deg
    unfolding hash_extension_preserving_def by blast
  have hu: "h \<le> u" by (rule hash_ext_trans[OF hd du])
  have hw: "wp (shadow_header_cursor A (PState s)) F u =
    F (Some (((fr,rs,bs,tf,as),PState h),u))" for F
    by (rule shadow_header_cursor_replay[OF root roots tfinal header ctr(1,2) hu])
  have dw: "wp (degree_stage A as) F u = F (Some (dg,u))" for F
    using hash_only_ro_replayable[OF degree_cb] deg du unfolding replayable_ro_def by blast
  have dk: "fmlookup (HashMap u) (TranscriptAbsorb (PState h) dg)=Some (PState w)"
    using hash_extension_lookup[OF conjunct1[OF dr] wu] df by simp
  have cc: "PCompositionFriCounter w=0"
    using ro_header_untouched_counters[OF root roots tfinal header] df dc ctr(3) by simp
  have cw: "wp (shadow_composition A dg 0 (ceil_log (to_nat dg+1)) [] (PState w)) F u =
    F (Some ((crs,cbs,PState c),u))" for F
    by (rule shadow_composition_replay[OF croots comp cc cu])
  have fw: "wp (composition_final_stage A dg cbs) F u = F (Some (cv,u))" for F
    using hash_only_ro_replayable[OF cfinal] fin fu unfolding replayable_ro_def by blast
  have fk: "fmlookup (HashMap u) (TranscriptAbsorb (PState c) cv)=Some (PState sent)"
    using hash_extension_lookup[OF conjunct1[OF fre] ext] ff by simp
  show ?thesis unfolding shadow_commitment_prefix_def
    by (simp only: wp_bind wp_return hw dw hash_known_wp[OF dk] cw fw hash_known_wp[OF fk] prod.case option.case)
qed


lemma ro_commitment_prefix_query_update:
  "ro_commitment_prefix (A\<lparr>query_opening_stage:=opening\<rparr>)=ro_commitment_prefix A"
proof -
  have header: "ro_header_prefix (A\<lparr>query_opening_stage:=opening\<rparr>)=ro_header_prefix A"
    by (rule ro_header_prefix_cong) simp_all
  have comp: "ro_staged_composition_fri_program (A\<lparr>query_opening_stage:=opening\<rparr>) dg i n bs =
    ro_staged_composition_fri_program A dg i n bs" for dg i n bs
    by (induction n arbitrary: i bs) simp_all
  show ?thesis by (simp add: ro_commitment_prefix_def header comp)
qed

lemma ro_records_no_failure:
  "None\<notin>dom (dist (execute (ro_record_staged_messages xs) s))"
  by (induction xs arbitrary: s)
    (simp_all add: ro_record_staged_messages_def no_failure_bindI ro_record_no_failure)

lemma ro_checked_queries_no_failure:
  assumes opening_nf: "\<And>i raw s. None\<notin>dom (dist (execute (query_opening_stage A i raw) s))"
    and opening_format: "\<And>i raw s chunk t. initial\<le>s \<Longrightarrow>
      Some (chunk,t)\<in>set_dist (execute (query_opening_stage A i raw) s) \<Longrightarrow>
      verifier_query_round_chunk (index (to_nat raw)) trs crs chunk \<and> s\<le>t"
    and ext: "initial\<le>u"
  shows "None\<notin>dom (dist (execute (ro_checked_staged_query_program A trs crs i n) u))"
  using ext
proof (induction n arbitrary: i u)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
    unfolding ro_checked_staged_query_program.simps Let_def
  proof (rule no_failure_bindI[OF receive_query_index_challenge_no_failure])
    fix raw s1
    assume recv: "Some (raw,s1)\<in>set_dist (execute receive_query_index_challenge u)"
    have us1: "u\<le>s1" using receive_query_index_challenge_outcome[OF recv] by simp
    have is1: "initial\<le>s1" by (rule hash_ext_trans[OF Suc.prems us1])
    show "None\<notin>dom (dist (execute
      (query_opening_stage A i raw \<bind> (\<lambda>chunk.
        assert (verifier_query_round_chunk (index (to_nat raw)) trs crs chunk) \<bind> (\<lambda>_.
        ro_record_staged_messages chunk \<bind> (\<lambda>_.
        ro_checked_staged_query_program A trs crs (Suc i) n \<bind> (\<lambda>chunks.
        return (chunk#chunks)))))) s1))"
    proof (rule no_failure_bindI[OF opening_nf])
      fix chunk s2
      assume op: "Some (chunk,s2)\<in>set_dist (execute (query_opening_stage A i raw) s1)"
      have format: "verifier_query_round_chunk (index (to_nat raw)) trs crs chunk"
        and s1s2: "s1\<le>s2" using opening_format[OF is1 op] by auto
      have is2: "initial\<le>s2" by (rule hash_ext_trans[OF is1 s1s2])
      have guard: "assert (verifier_query_round_chunk (index (to_nat raw)) trs crs chunk) =
        (return () :: (unit, 'f protocol_channel) state_monad)"
        using format by (simp add: assert_def)
      show "None\<notin>dom (dist (execute
        (assert (verifier_query_round_chunk (index (to_nat raw)) trs crs chunk) \<bind> (\<lambda>_.
         ro_record_staged_messages chunk \<bind> (\<lambda>_.
         ro_checked_staged_query_program A trs crs (Suc i) n \<bind> (\<lambda>chunks.
         return (chunk#chunks))))) s2))"
        unfolding guard sm_bind_return_left
      proof (rule no_failure_bindI[OF ro_records_no_failure])
        fix unit s3
        assume rec: "Some (unit,s3)\<in>set_dist (execute (ro_record_staged_messages chunk) s2)"
        have s2s3: "s2\<le>s3"
          using ro_record_staged_messages_absorb_lookup_chain[of s3 chunk s2] rec by (cases unit) auto
        have is3: "initial\<le>s3" by (rule hash_ext_trans[OF is2 s2s3])
        show "None\<notin>dom (dist (execute
          (ro_checked_staged_query_program A trs crs (Suc i) n \<bind> (\<lambda>chunks. return (chunk#chunks))) s3))"
          by (rule no_failure_bindI[OF Suc.IH[OF is3]]) simp
      qed
    qed
  qed
qed

end
end
