(*  License: BSD-3-Clause *)
theory RO_Honest_Composition_Reconstruction
  imports RO_Honest_Header_Reconstruction
begin

section \<open>Variable-depth composition reconstruction\<close>

text \<open>The supplied degree and challenge history are those of the existing staged
  program. Replaying cached roots, absorptions and challenges changes no
  protocol-local fields. The commitment prefix is an exact factorization of
  the checked builder before query openings, not a new experiment. Generic
  hash-only hypotheses are discharged by the concrete honest callbacks.\<close>

context soundness
begin

primrec shadow_composition
  :: "'f staged_adversary \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
     ('f list \<times> 'f list \<times> 'f, 'f protocol_channel) state_monad"
where
  "shadow_composition A dg i 0 bs cursor = return ([],bs,cursor)"
| "shadow_composition A dg i (Suc n) bs cursor =
    (composition_fri_root_stage A dg i bs \<bind> (\<lambda>r.
     hash (TranscriptAbsorb cursor r) \<bind> (\<lambda>c.
     hash (CompositionFriChallenge i c) \<bind> (\<lambda>b.
     shadow_composition A dg (Suc i) n (bs@[b]) c \<bind> (\<lambda>(rs,bs',final).
     return (r#rs,bs',final))))))"

lemma composition_prefix_properties:
  assumes roots: "\<And>i bs. hash_only_ro q (composition_fri_root_stage A dg i bs)"
    and out: "Some ((rs,bs'),t) \<in> set_dist (execute (ro_staged_composition_fri_program A dg i n bs) s)"
  shows "s \<le> t \<and> PCompositionFriCounter t = PCompositionFriCounter s+n \<and>
    PTraceFriCounter t = PTraceFriCounter s \<and> length bs' = length bs+n"
  using out
proof (induction n arbitrary: i bs s rs bs' t)
  case 0
  then show ?case by (simp add: hash_ext_refl)
next
  case (Suc n)
  obtain r s1 s2 b s3 tail where
    rout: "Some (r,s1) \<in> set_dist (execute (composition_fri_root_stage A dg i bs) s)"
    and rec: "Some ((),s2) \<in> set_dist (execute (ro_record_staged_message r) s1)"
    and recv: "Some (b,s3) \<in> set_dist (execute receive_composition_fri_challenge s2)"
    and tout: "Some ((tail,bs'),t) \<in> set_dist
      (execute (ro_staged_composition_fri_program A dg (Suc i) n (bs@[b])) s3)"
    using Suc.prems by (auto elim!: set_dist_bindE split: prod.splits)
  have root_ext: "s \<le> s1" using hash_only_ro_extends[OF roots] rout
    unfolding hash_extension_preserving_def by blast
  note root_fields = hash_only_ro_fields[OF roots rout]
  have rec_ext: "s1 \<le> s2"
    using ro_record_staged_message_absorb_lookup_state[OF rec] by simp
  note rec_fields = ro_record_staged_message_counter_preserves[OF rec]
  have recv_ext: "s2 \<le> s3" using receive_composition_fri_challenge_outcome[OF recv] by simp
  note recv_fields = receive_composition_fri_challenge_counter_outcome[OF recv]
  note rest = Suc.IH[OF tout]
  have "s \<le> t"
    using root_ext rec_ext recv_ext rest by (meson hash_ext_trans)
  then show ?case using root_fields rec_fields recv_fields rest by simp
qed

lemma shadow_composition_hash_only:
  assumes roots: "\<And>j bs. hash_only_ro q (composition_fri_root_stage A dg j bs)"
  shows "hash_only_ro ((q+2)*n) (shadow_composition A dg i n bs cursor)"
proof (induction n arbitrary: i bs cursor)
  case 0
  show ?case by auto
next
  case (Suc n)
  have step: "hash_only_ro (q + Suc (Suc ((q+2)*n)))
      (shadow_composition A dg i (Suc n) bs cursor)"
    unfolding shadow_composition.simps
    apply (rule hash_only_ro_bind[OF roots])
    apply (intro hash_only_ro.Ask)
    apply (simp only: case_prod_unfold)
    apply (rule hash_only_ro_map)
    using Suc.IH by (simp add: algebra_simps)
  show ?case using step by (simp add: algebra_simps)
qed

lemma shadow_composition_replay:
  assumes roots: "\<And>j bs. hash_only_ro q (composition_fri_root_stage A dg j bs)"
    and out: "Some ((rs,bs'),t) \<in> set_dist (execute (ro_staged_composition_fri_program A dg i n bs) s)"
    and ctr: "PCompositionFriCounter s=i"
    and ext: "t \<le> u"
  shows "wp (shadow_composition A dg i n bs (PState s)) Q u =
    Q (Some ((rs,bs',PState t),u))"
  using out ctr ext
proof (induction n arbitrary: i bs s rs bs' t u Q)
  case 0
  then show ?case by (simp add: wp_return)
next
  case (Suc n)
  obtain r s1 s2 b s3 tail where
    rout: "Some (r,s1) \<in> set_dist (execute (composition_fri_root_stage A dg i bs) s)"
    and rec: "Some ((),s2) \<in> set_dist (execute (ro_record_staged_message r) s1)"
    and recv: "Some (b,s3) \<in> set_dist (execute receive_composition_fri_challenge s2)"
    and tout: "Some ((tail,bs'),t) \<in> set_dist
      (execute (ro_staged_composition_fri_program A dg (Suc i) n (bs@[b])) s3)"
    and rs: "rs=r#tail"
    using Suc.prems(1) by (auto elim!: set_dist_bindE split: prod.splits)
  note root_fields = hash_only_ro_fields[OF roots rout]
  note rec_props = ro_record_staged_message_absorb_lookup_state[OF rec]
  note rec_fields = ro_record_staged_message_counter_preserves[OF rec]
  note recv_props = receive_composition_fri_challenge_outcome[OF recv]
  note recv_fields = receive_composition_fri_challenge_counter_outcome[OF recv]
  have s3t: "s3 \<le> t" using composition_prefix_properties[OF roots tout] by simp
  have s3u: "s3 \<le> u" by (rule hash_ext_trans[OF s3t Suc.prems(3)])
  have s2u: "s2 \<le> u" using recv_props s3u by (meson hash_ext_trans)
  have s1u: "s1 \<le> u" using rec_props s2u by (meson hash_ext_trans)
  have root_wp: "wp (composition_fri_root_stage A dg i bs) F u = F (Some (r,u))" for F
    using hash_only_ro_replayable[OF roots] rout s1u
    unfolding replayable_ro_def by blast
  have absorb: "fmlookup (HashMap u) (TranscriptAbsorb (PState s) r) = Some (PState s2)"
    using hash_extension_lookup[OF conjunct1[OF rec_props] s2u] root_fields by simp
  have challenge: "fmlookup (HashMap u) (CompositionFriChallenge i (PState s2)) = Some b"
    using hash_extension_lookup[OF conjunct2[OF conjunct2[OF conjunct2[OF recv_props]]] s3u]
      root_fields rec_fields Suc.prems(2) by simp
  have next_ctr: "PCompositionFriCounter s3=Suc i"
    using root_fields rec_fields recv_fields Suc.prems(2) by simp
  have next_cursor: "PState s3=PState s2" using recv_props by simp
  have rest_wp:
    "wp (shadow_composition A dg (Suc i) n (bs@[b]) (PState s2)) F u =
       F (Some ((tail,bs',PState t),u))" for F
    using Suc.IH[OF tout next_ctr Suc.prems(3), of F] next_cursor by simp
  show ?case
    by (simp add: wp_bind wp_return root_wp hash_known_wp[OF absorb]
      hash_known_wp[OF challenge] rest_wp rs)
qed


lemma ro_composition_no_failure:
  assumes roots: "\<And>i bs. hash_only_ro q (composition_fri_root_stage A dg i bs)"
  shows "None \<notin> dom (dist (execute (ro_staged_composition_fri_program A dg i n bs) s))"
  by (induction n arbitrary: i bs s)
    (simp_all add: no_failure_bindI hash_only_ro_no_failure[OF roots]
      receive_composition_fri_challenge_no_failure ro_record_no_failure split: prod.splits)

lemma wp_equality_support:
  fixes m n :: "('x, 'f protocol_channel) state_monad"
  assumes eq: "\<And>Q. wp m Q s=wp n Q s"
    and out: "out \<in> set_dist (execute m s)"
  shows "out \<in> set_dist (execute n s)"
proof -
  have pos: "0 < wp_event m (\<lambda>x. x=out) s"
    by (rule wp_event_pos_of_support[OF out]) simp
  have "0 < wp_event n (\<lambda>x. x=out) s"
    using pos eq unfolding wp_event_def by simp
  then obtain x where "x \<in> set_dist (execute n s)" "x=out"
    by (rule wp_event_pos_imp_exists_support)
  then show ?thesis by simp
qed

definition ro_commitment_prefix where
  "ro_commitment_prefix A =
    (ro_header_prefix A \<bind> (\<lambda>data.
     case data of (fr,rs,bs,ffinal,as) \<Rightarrow>
     degree_stage A as \<bind> (\<lambda>dg.
     ro_record_staged_message dg \<bind> (\<lambda>_.
     assert (ceil_log (to_nat dg+1) \<le> ceil_log (maxDegree+1)) \<bind> (\<lambda>_.
     ro_staged_composition_fri_program A dg 0 (ceil_log (to_nat dg+1)) [] \<bind> (\<lambda>(crs,cbs).
     composition_final_stage A dg cbs \<bind> (\<lambda>cv.
     ro_record_staged_message cv \<bind> (\<lambda>_.
     return (data,dg,crs,cbs,cv)))))))))"

definition ro_after_commitment_prefix where
  "ro_after_commitment_prefix A prefix =
    (case prefix of ((fr,rs,bs,ffinal,as),dg,crs,cbs,cv) \<Rightarrow>
     ro_checked_staged_query_program A rs crs 0 rounds \<bind> (\<lambda>chunks.
     return \<lparr>staged_trace_root=fr,staged_trace_fri_roots=rs,
       staged_trace_fri_challenges=bs,staged_trace_final=ffinal,
       staged_alphas=as,staged_degree=dg,staged_composition_fri_roots=crs,
       staged_composition_fri_challenges=cbs,staged_composition_final=cv,
       staged_query_chunks=chunks\<rparr>))"

lemma ro_commitment_prefix_decomposition:
  "ro_checked_staged_transcript_program A =
    ro_commitment_prefix A \<bind> ro_after_commitment_prefix A"
  unfolding ro_checked_program_header_decomposition ro_after_header_def
    ro_commitment_prefix_def ro_after_commitment_prefix_def
  by (simp add: sm_bind_assoc case_prod_unfold)


end
end
