(*  License: BSD-3-Clause *)
theory RO_Honest_Header_Reconstruction
  imports RO_Honest_Trace_Reconstruction
begin

section \<open>Honest header replay and the first composition frontier\<close>

text \<open>The prefix and frontier below are factorizations of the existing checked
  transcript builder, not replacement experiments. The frontier ends after
  recording the first composition root and before its challenge, or after the
  direct terminal message when the actual composition depth is zero.
  Generic callback hypotheses are discharged by the concrete producer.\<close>

context soundness
begin

definition ro_header_prefix
  :: "'f staged_adversary \<Rightarrow>
    ('f \<times> 'f list \<times> 'f list \<times> 'f \<times> 'f list, 'f protocol_channel) state_monad"
where
  "ro_header_prefix A =
    (trace_root_stage A \<bind> (\<lambda>fr.
     ro_record_staged_message fr \<bind> (\<lambda>_.
     ro_staged_trace_fri_program A 0 (ceil_log clength) [] \<bind> (\<lambda>(rs,bs).
     trace_final_stage A bs \<bind> (\<lambda>final.
     ro_record_staged_message final \<bind> (\<lambda>_.
     ro_staged_alpha_program (length spec) \<bind> (\<lambda>as.
     return (fr,rs,bs,final,as))))))))"

definition shadow_header
  :: "'f staged_adversary \<Rightarrow> 'f \<Rightarrow>
    ('f \<times> 'f list \<times> 'f list \<times> 'f \<times> 'f list, 'f protocol_channel) state_monad"
where
  "shadow_header A cursor =
    (trace_root_stage A \<bind> (\<lambda>fr.
     hash (TranscriptAbsorb cursor fr) \<bind> (\<lambda>c.
     shadow_trace A 0 (ceil_log clength) [] c \<bind> (\<lambda>(rs,bs,c').
     trace_final_stage A bs \<bind> (\<lambda>final.
     hash (TranscriptAbsorb c' final) \<bind> (\<lambda>c''.
     shadow_alphas 0 (length spec) c'' \<bind> (\<lambda>(as,_).
     return (fr,rs,bs,final,as))))))))"

lemma shadow_header_hash_only:
  assumes root: "hash_only_ro qr (trace_root_stage A)"
    and roots: "\<And>i bs. hash_only_ro qt (trace_fri_root_stage A i bs)"
    and final: "\<And>bs. hash_only_ro qf (trace_final_stage A bs)"
  shows "hash_only_ro (qr+1+((qt+2)*ceil_log clength)+qf+1+2*length spec)
    (shadow_header A cursor)"
proof -
  have step: "hash_only_ro (qr + Suc (((qt+2)*ceil_log clength) + (qf + Suc (2*length spec))))
      (shadow_header A cursor)"
    unfolding shadow_header_def
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

lemma shadow_header_replay:
  assumes root: "hash_only_ro qr (trace_root_stage A)"
    and roots: "\<And>i bs. hash_only_ro qt (trace_fri_root_stage A i bs)"
    and final: "\<And>bs. hash_only_ro qf (trace_final_stage A bs)"
    and out: "Some (data,t) \<in> set_dist (execute (ro_header_prefix A) s)"
    and counters: "PTraceFriCounter s=0" "PAlphaCounter s=0"
    and ext: "t \<le> u"
  shows "wp (shadow_header A (PState s)) Q u = Q (Some (data,u))"
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
  show ?thesis unfolding shadow_header_def
    by (simp add: wp_bind wp_return rw hash_known_wp[OF rk] tw fw hash_known_wp[OF fk] aw data)
qed

lemma ro_record_no_failure:
  "None \<notin> dom (dist (execute (ro_record_staged_message x) s))"
  unfolding ro_record_staged_message_def
  by (simp add: no_failure_bindI protocol_hash_no_failure)

lemma ro_alphas_no_failure:
  "None \<notin> dom (dist (execute (ro_staged_alpha_program n) s))"
  by (induction n arbitrary: s)
    (simp_all add: no_failure_bindI receive_alpha_challenge_no_failure ro_record_no_failure)

lemma ro_trace_no_failure:
  assumes roots: "\<And>i bs. hash_only_ro q (trace_fri_root_stage A i bs)"
  shows "None \<notin> dom (dist (execute (ro_staged_trace_fri_program A i n bs) s))"
  by (induction n arbitrary: i bs s)
    (simp_all add: no_failure_bindI hash_only_ro_no_failure[OF roots]
      receive_trace_fri_challenge_no_failure ro_record_no_failure split: prod.splits)

lemma ro_header_no_failure:
  assumes root: "hash_only_ro qr (trace_root_stage A)"
    and roots: "\<And>i bs. hash_only_ro qt (trace_fri_root_stage A i bs)"
    and final: "\<And>bs. hash_only_ro qf (trace_final_stage A bs)"
  shows "None \<notin> dom (dist (execute (ro_header_prefix A) s))"
  unfolding ro_header_prefix_def
  by (simp add: no_failure_bindI hash_only_ro_no_failure[OF root]
    hash_only_ro_no_failure[OF final] ro_trace_no_failure[OF roots]
    ro_record_no_failure ro_alphas_no_failure split: prod.splits)

definition ro_after_header
where
  "ro_after_header A data =
    (case data of (fr,rs,bs,ffinal,as) \<Rightarrow>
     degree_stage A as \<bind> (\<lambda>dg.
     ro_record_staged_message dg \<bind> (\<lambda>_.
     assert (ceil_log (to_nat dg+1) \<le> ceil_log (maxDegree+1)) \<bind> (\<lambda>_.
     ro_staged_composition_fri_program A dg 0 (ceil_log (to_nat dg+1)) [] \<bind> (\<lambda>(crs,cbs).
     composition_final_stage A dg cbs \<bind> (\<lambda>cfinal.
     ro_record_staged_message cfinal \<bind> (\<lambda>_.
     ro_checked_staged_query_program A rs crs 0 rounds \<bind> (\<lambda>chunks.
     return \<lparr>staged_trace_root=fr,staged_trace_fri_roots=rs,
       staged_trace_fri_challenges=bs,staged_trace_final=ffinal,
       staged_alphas=as,staged_degree=dg,staged_composition_fri_roots=crs,
       staged_composition_fri_challenges=cbs,staged_composition_final=cfinal,
       staged_query_chunks=chunks\<rparr>))))))))"

lemma ro_checked_program_header_decomposition:
  "ro_checked_staged_transcript_program A = ro_header_prefix A \<bind> ro_after_header A"
  unfolding ro_checked_staged_transcript_program_def ro_header_prefix_def ro_after_header_def
  by (simp add: sm_bind_assoc case_prod_unfold Let_def)

lemma ro_header_prefix_cong:
  assumes "trace_root_stage A=trace_root_stage B"
    "trace_fri_root_stage A=trace_fri_root_stage B"
    "trace_final_stage A=trace_final_stage B"
  shows "ro_header_prefix A=ro_header_prefix B"
proof -
  have trace: "ro_staged_trace_fri_program A i n bs=ro_staged_trace_fri_program B i n bs"
    for i n bs using assms(2) by (induction n arbitrary: i bs) simp_all
  show ?thesis unfolding ro_header_prefix_def using assms trace by simp
qed

definition ro_composition_frontier
where
  "ro_composition_frontier A =
    (ro_header_prefix A \<bind> (\<lambda>data.
     case data of (fr,rs,bs,ffinal,as) \<Rightarrow>
     degree_stage A as \<bind> (\<lambda>dg.
     ro_record_staged_message dg \<bind> (\<lambda>_.
     assert (ceil_log (to_nat dg+1) \<le> ceil_log (maxDegree+1)) \<bind> (\<lambda>_.
     (if ceil_log (to_nat dg+1)=0
      then composition_final_stage A dg []
      else composition_fri_root_stage A dg 0 []) \<bind> (\<lambda>v.
     ro_record_staged_message v \<bind> (\<lambda>_.
     return (data,dg,v))))))))"

definition ro_finish_composition_frontier
where
  "ro_finish_composition_frontier A frontier =
    (case frontier of ((fr,rs,bs,ffinal,as),dg,v) \<Rightarrow>
     (if ceil_log (to_nat dg+1)=0
      then return ([],[],v)
      else receive_composition_fri_challenge \<bind> (\<lambda>b.
       ro_staged_composition_fri_program A dg 1 (ceil_log (to_nat dg+1)-1) [b] \<bind> (\<lambda>(crs,cbs).
       composition_final_stage A dg cbs \<bind> (\<lambda>cv.
       ro_record_staged_message cv \<bind> (\<lambda>_.
       return (v#crs,cbs,cv)))))) \<bind> (\<lambda>(crs,cbs,cv).
     ro_checked_staged_query_program A rs crs 0 rounds \<bind> (\<lambda>chunks.
     return \<lparr>staged_trace_root=fr,staged_trace_fri_roots=rs,
       staged_trace_fri_challenges=bs,staged_trace_final=ffinal,
       staged_alphas=as,staged_degree=dg,staged_composition_fri_roots=crs,
       staged_composition_fri_challenges=cbs,staged_composition_final=cv,
       staged_query_chunks=chunks\<rparr>)))"

lemma ro_bind_cont_cong:
  fixes m :: "('a, 'f protocol_channel) state_monad"
    and k1 k2 :: "'a \<Rightarrow> ('b, 'f protocol_channel) state_monad"
  assumes "\<And>x. k1 x=k2 x"
  shows "(m \<bind> k1)=(m \<bind> k2)"
  by (rule arg_cong[where f="\<lambda>k. m \<bind> k"]) (rule ext, rule assms)

lemma ro_composition_frontier_decomposition:
  "ro_checked_staged_transcript_program A =
    ro_composition_frontier A \<bind> ro_finish_composition_frontier A"
proof -
  have after: "ro_after_header A data =
     ((case data of (fr,rs,bs,ffinal,as) \<Rightarrow>
     degree_stage A as \<bind> (\<lambda>dg.
     ro_record_staged_message dg \<bind> (\<lambda>_.
     assert (ceil_log (to_nat dg+1) \<le> ceil_log (maxDegree+1)) \<bind> (\<lambda>_.
     (if ceil_log (to_nat dg+1)=0 then composition_final_stage A dg []
       else composition_fri_root_stage A dg 0 []) \<bind> (\<lambda>v.
     ro_record_staged_message v \<bind> (\<lambda>_.
     return (data,dg,v))))))) \<bind> ro_finish_composition_frontier A)" for data
    unfolding ro_after_header_def ro_finish_composition_frontier_def
    apply (simp add: sm_bind_assoc case_prod_unfold Let_def)
    apply (rule ro_bind_cont_cong)
    subgoal for dg
      by (cases "ceil_log (to_nat dg+1)")
        (simp_all add: sm_bind_assoc case_prod_unfold)
    done
  show ?thesis
    unfolding ro_checked_program_header_decomposition ro_composition_frontier_def sm_bind_assoc
    by (rule ro_bind_cont_cong, rule after)
qed

lemma ro_header_output_lengths:
  assumes roots: "\<And>i bs. hash_only_ro qt (trace_fri_root_stage A i bs)"
    and out: "Some ((fr,rs,bs,ffinal,as),t) \<in> set_dist (execute (ro_header_prefix A) s)"
  shows "length bs=ceil_log clength \<and> length as=length spec"
proof -
  obtain s2 s3 s5 where
    trace: "Some ((rs,bs),s3) \<in> set_dist
      (execute (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and alpha: "Some (as,t) \<in> set_dist (execute (ro_staged_alpha_program (length spec)) s5)"
    using out unfolding ro_header_prefix_def by (auto elim!: set_dist_bindE)
  show ?thesis using trace_prefix_properties[OF roots trace]
    ro_staged_alpha_program_output_length[OF alpha] by simp
qed

end

end
