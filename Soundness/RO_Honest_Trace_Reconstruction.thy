(*  License: BSD-3-Clause *)
theory RO_Honest_Trace_Reconstruction
  imports RO_Honest_Replay_Primitives
begin

section \<open>Reconstructing actual trace and alpha prefixes\<close>

text \<open>Local cursors and counters reconstruct the previously recorded prefix
  using ordinary hash queries. They are not reads or writes of protocol-local
  channel fields. Actual receive and record outcomes supply the lookup facts.\<close>

context soundness
begin

primrec shadow_alphas
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow> ('f list \<times> 'f, 'f protocol_channel) state_monad"
where
  "shadow_alphas i 0 cursor = return ([],cursor)"
| "shadow_alphas i (Suc n) cursor =
    (shadow_alpha i cursor \<bind> (\<lambda>(a,c).
      shadow_alphas (Suc i) n c \<bind> (\<lambda>(as,final).
        return (a#as,final))))"

lemma shadow_alphas_hash_only:
  "hash_only_ro (2*n) (shadow_alphas i n cursor)"
proof (induction n arbitrary: i cursor)
  case 0
  show ?case by auto
next
  case (Suc n)
  have "hash_only_ro (2+2*n) (shadow_alphas i (Suc n) cursor)"
    unfolding shadow_alphas.simps
    apply (rule hash_only_ro_bind[OF hash_only_ro_shadow_alpha])
    apply (clarsimp split: prod.splits)
    by (auto simp: case_prod_unfold intro: hash_only_ro_map Suc.IH)
  then show ?case by simp
qed

lemma shadow_alphas_replay:
  assumes out: "Some (as,t) \<in> set_dist (execute (ro_staged_alpha_program n) s)"
    and ext: "t \<le> u"
  shows "wp (shadow_alphas (PAlphaCounter s) n (PState s)) Q u =
    Q (Some ((as,PState t),u))"
  using out ext
proof (induction n arbitrary: s as t u Q)
  case 0
  then show ?case by (simp add: wp_return)
next
  case (Suc n)
  obtain a s1 s2 rest where
    recv: "Some (a,s1) \<in> set_dist (execute receive_alpha_challenge s)"
    and rec: "Some ((),s2) \<in> set_dist (execute (ro_record_staged_message a) s1)"
    and tail: "Some (rest,t) \<in> set_dist (execute (ro_staged_alpha_program n) s2)"
    and as: "as=a#rest"
    using Suc.prems(1) by (auto elim!: set_dist_bindE)
  have s2t: "s2 \<le> t"
    using ro_staged_alpha_program_absorb_lookup_chain[OF tail] by simp
  have s2u: "s2 \<le> u" by (rule hash_ext_trans[OF s2t Suc.prems(2)])
  have ctr: "PAlphaCounter s2 = Suc (PAlphaCounter s)"
    using receive_alpha_challenge_counter_outcome[OF recv]
      ro_record_staged_message_counter_preserves[OF rec] by simp
  have first: "wp (shadow_alpha (PAlphaCounter s) (PState s)) F u =
      F (Some ((a,PState s2),u))" for F
    by (rule shadow_alpha_replays_actual_round[OF recv rec s2u])
  have tail_wp: "wp (shadow_alphas (Suc (PAlphaCounter s)) n (PState s2)) F u =
      F (Some ((rest,PState t),u))" for F
    using Suc.IH[OF tail Suc.prems(2), of F] ctr by simp
  show ?case by (simp add: wp_bind wp_return first tail_wp as)
qed


lemma hash_only_ro_extends:
  assumes "hash_only_ro q m"
  shows "hash_extension_preserving m"
  by (rule controlled_ro_program_extension[OF hash_only_ro_controlled[OF assms]])

lemma hash_only_ro_replayable:
  assumes "hash_only_ro q m"
  shows "replayable_ro m"
  using assms
  by (induction rule: hash_only_ro.induct)
    (auto intro!: replayable_ro_return replayable_ro_bind replayable_ro_hash
      intro: hash_only_ro_extends)

lemma hash_only_ro_fields:
  assumes prog: "hash_only_ro q m"
    and out: "Some (x,t) \<in> set_dist (execute m s)"
  shows "PState t=PState s \<and> PTranscript t=PTranscript s \<and>
    PTraceFriCounter t=PTraceFriCounter s \<and>
    PCompositionFriCounter t=PCompositionFriCounter s \<and>
    PAlphaCounter t=PAlphaCounter s \<and> PQueryCounter t=PQueryCounter s"
  using controlled_stage_outcome_fields[OF hash_only_ro_controlled[OF prog] out] by auto

lemma hash_only_ro_no_failure:
  assumes "hash_only_ro q m"
  shows "None \<notin> dom (dist (execute m s))"
  using assms
proof (induction arbitrary: s rule: hash_only_ro.induct)
  case (Pure x)
  show ?case by simp
next
  case (Ask q k x)
  show ?case by (rule no_failure_bindI[OF protocol_hash_no_failure]) (rule Ask.IH)
next
  case (Bound q m r)
  show ?case by (rule Bound.IH)
qed

primrec shadow_trace
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
     ('f list \<times> 'f list \<times> 'f, 'f protocol_channel) state_monad"
where
  "shadow_trace A i 0 bs cursor = return ([],bs,cursor)"
| "shadow_trace A i (Suc n) bs cursor =
    (trace_fri_root_stage A i bs \<bind> (\<lambda>r.
     hash (TranscriptAbsorb cursor r) \<bind> (\<lambda>c.
     hash (TraceFriChallenge i c) \<bind> (\<lambda>b.
     shadow_trace A (Suc i) n (bs@[b]) c \<bind> (\<lambda>(rs,bs',final).
     return (r#rs,bs',final))))))"

lemma trace_prefix_properties:
  assumes roots: "\<And>i bs. hash_only_ro q (trace_fri_root_stage A i bs)"
    and out: "Some ((rs,bs'),t) \<in> set_dist (execute (ro_staged_trace_fri_program A i n bs) s)"
  shows "s \<le> t \<and> PTraceFriCounter t = PTraceFriCounter s+n \<and>
    PAlphaCounter t = PAlphaCounter s \<and> length bs' = length bs+n"
  using out
proof (induction n arbitrary: i bs s rs bs' t)
  case 0
  then show ?case by (simp add: hash_ext_refl)
next
  case (Suc n)
  obtain r s1 s2 b s3 tail where
    rout: "Some (r,s1) \<in> set_dist (execute (trace_fri_root_stage A i bs) s)"
    and rec: "Some ((),s2) \<in> set_dist (execute (ro_record_staged_message r) s1)"
    and recv: "Some (b,s3) \<in> set_dist (execute receive_trace_fri_challenge s2)"
    and tout: "Some ((tail,bs'),t) \<in> set_dist
      (execute (ro_staged_trace_fri_program A (Suc i) n (bs@[b])) s3)"
    using Suc.prems by (auto elim!: set_dist_bindE split: prod.splits)
  have root_ext: "s \<le> s1" using hash_only_ro_extends[OF roots] rout
    unfolding hash_extension_preserving_def by blast
  note root_fields = hash_only_ro_fields[OF roots rout]
  have rec_ext: "s1 \<le> s2"
    using ro_record_staged_message_absorb_lookup_state[OF rec] by simp
  note rec_fields = ro_record_staged_message_counter_preserves[OF rec]
  have recv_ext: "s2 \<le> s3" using receive_trace_fri_challenge_outcome[OF recv] by simp
  note recv_fields = receive_trace_fri_challenge_counter_outcome[OF recv]
  note rest = Suc.IH[OF tout]
  have "s \<le> t"
    using root_ext rec_ext recv_ext rest by (meson hash_ext_trans)
  then show ?case using root_fields rec_fields recv_fields rest by simp
qed

lemma shadow_trace_hash_only:
  assumes roots: "\<And>j bs. hash_only_ro q (trace_fri_root_stage A j bs)"
  shows "hash_only_ro ((q+2)*n) (shadow_trace A i n bs cursor)"
proof (induction n arbitrary: i bs cursor)
  case 0
  show ?case by auto
next
  case (Suc n)
  have step: "hash_only_ro (q + Suc (Suc ((q+2)*n)))
      (shadow_trace A i (Suc n) bs cursor)"
    unfolding shadow_trace.simps
    apply (rule hash_only_ro_bind[OF roots])
    apply (intro hash_only_ro.Ask)
    apply (simp only: case_prod_unfold)
    apply (rule hash_only_ro_map)
    using Suc.IH by (simp add: algebra_simps)
  show ?case using step by (simp add: algebra_simps)
qed

lemma shadow_trace_replay:
  assumes roots: "\<And>j bs. hash_only_ro q (trace_fri_root_stage A j bs)"
    and out: "Some ((rs,bs'),t) \<in> set_dist (execute (ro_staged_trace_fri_program A i n bs) s)"
    and ctr: "PTraceFriCounter s=i"
    and ext: "t \<le> u"
  shows "wp (shadow_trace A i n bs (PState s)) Q u =
    Q (Some ((rs,bs',PState t),u))"
  using out ctr ext
proof (induction n arbitrary: i bs s rs bs' t u Q)
  case 0
  then show ?case by (simp add: wp_return)
next
  case (Suc n)
  obtain r s1 s2 b s3 tail where
    rout: "Some (r,s1) \<in> set_dist (execute (trace_fri_root_stage A i bs) s)"
    and rec: "Some ((),s2) \<in> set_dist (execute (ro_record_staged_message r) s1)"
    and recv: "Some (b,s3) \<in> set_dist (execute receive_trace_fri_challenge s2)"
    and tout: "Some ((tail,bs'),t) \<in> set_dist
      (execute (ro_staged_trace_fri_program A (Suc i) n (bs@[b])) s3)"
    and rs: "rs=r#tail"
    using Suc.prems(1) by (auto elim!: set_dist_bindE split: prod.splits)
  note root_fields = hash_only_ro_fields[OF roots rout]
  note rec_props = ro_record_staged_message_absorb_lookup_state[OF rec]
  note rec_fields = ro_record_staged_message_counter_preserves[OF rec]
  note recv_props = receive_trace_fri_challenge_outcome[OF recv]
  note recv_fields = receive_trace_fri_challenge_counter_outcome[OF recv]
  have s3t: "s3 \<le> t" using trace_prefix_properties[OF roots tout] by simp
  have s3u: "s3 \<le> u" by (rule hash_ext_trans[OF s3t Suc.prems(3)])
  have s2u: "s2 \<le> u" using recv_props s3u by (meson hash_ext_trans)
  have s1u: "s1 \<le> u" using rec_props s2u by (meson hash_ext_trans)
  have root_wp: "wp (trace_fri_root_stage A i bs) F u = F (Some (r,u))" for F
    using hash_only_ro_replayable[OF roots] rout s1u
    unfolding replayable_ro_def by blast
  have absorb: "fmlookup (HashMap u) (TranscriptAbsorb (PState s) r) = Some (PState s2)"
    using hash_extension_lookup[OF conjunct1[OF rec_props] s2u] root_fields by simp
  have challenge: "fmlookup (HashMap u) (TraceFriChallenge i (PState s2)) = Some b"
    using hash_extension_lookup[OF conjunct2[OF conjunct2[OF conjunct2[OF recv_props]]] s3u]
      root_fields rec_fields Suc.prems(2) by simp
  have next_ctr: "PTraceFriCounter s3=Suc i"
    using root_fields rec_fields recv_fields Suc.prems(2) by simp
  have next_cursor: "PState s3=PState s2" using recv_props by simp
  have rest_wp:
    "wp (shadow_trace A (Suc i) n (bs@[b]) (PState s2)) F u =
       F (Some ((tail,bs',PState t),u))" for F
    using Suc.IH[OF tout next_ctr Suc.prems(3), of F] next_cursor by simp
  show ?case
    by (simp add: wp_bind wp_return root_wp hash_known_wp[OF absorb]
      hash_known_wp[OF challenge] rest_wp rs)
qed


end

end
