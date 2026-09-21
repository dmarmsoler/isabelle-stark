(*  License: BSD-3-Clause *)
theory RO_Honest_Verifier_Header_Primitives
  imports "Stark.RO_Honest_Verifier_Replay" "Stark.RO_Honest_Composition_Reconstruction"
begin

section \<open>Exact Replay of Honest Header Operations\<close>

text \<open>Replay actual recorded scalar and counted challenge outcomes in a fixed extended oracle map. The state overlay is proof notation: it copies the producer's cursor and counters and installs the specified remaining transcript. Trace and composition commitments and alpha rounds are replayed without freshness or collision-freedom assumptions.\<close>

definition ro_replay_state :: "'f protocol_channel \<Rightarrow> 'f protocol_channel \<Rightarrow> 'f list \<Rightarrow> 'f protocol_channel"
where "ro_replay_state base producer xs = producer\<lparr>HashMap := HashMap base, PTranscript := xs\<rparr>"

lemma ro_replay_state_fields [simp]:
  "HashMap (ro_replay_state base s xs)=HashMap base"
  "PState (ro_replay_state base s xs)=PState s"
  "PTranscript (ro_replay_state base s xs)=xs"
  "PTraceFriCounter (ro_replay_state base s xs)=PTraceFriCounter s"
  "PCompositionFriCounter (ro_replay_state base s xs)=PCompositionFriCounter s"
  "PAlphaCounter (ro_replay_state base s xs)=PAlphaCounter s"
  "PQueryCounter (ro_replay_state base s xs)=PQueryCounter s"
  by (simp_all add: ro_replay_state_def)

context soundness
begin

lemma ro_replay_hash_only_fields:
  assumes prog: "hash_only_ro q m"
    and out: "Some(x,t)\<in>set_dist(execute m s)"
  shows "ro_replay_state base t xs=ro_replay_state base s xs"
  using hash_only_ro_fields[OF prog out]
  by (cases s; cases t) (simp add: ro_replay_state_def)

lemma ro_recorded_scalar_replay:
  assumes out: "Some((),t)\<in>set_dist(execute (ro_record_staged_message x) s)"
    and ext: "t\<le>base"
  shows "wp protocol_absorb_read Q (ro_replay_state base s (x#rest)) =
    Q (Some(x,ro_replay_state base t rest))"
proof -
  note p=ro_record_staged_message_absorb_lookup_state[OF out]
  note c=ro_record_staged_message_counter_preserves[OF out]
  have key: "fmlookup (HashMap (ro_replay_state base s (x#rest)))
    (TranscriptAbsorb (PState (ro_replay_state base s (x#rest))) x)=Some(PState t)"
    using hash_extension_lookup[OF conjunct1[OF p] ext] by simp
  have eq: "(ro_replay_state base s (x#rest))\<lparr>PState:=PState t,PTranscript:=rest\<rparr> =
    ro_replay_state base t rest"
    using c by (cases s; cases t) (simp add: ro_replay_state_def)
  show ?thesis using protocol_absorb_read_known_wp[OF _ key, where Q=Q] eq by simp
qed

lemma ro_trace_fri_challenge_replay:
  assumes out: "Some(b,t)\<in>set_dist(execute receive_trace_fri_challenge s)"
    and ext: "t\<le>base"
  shows "wp receive_trace_fri_challenge Q (ro_replay_state base s xs) =
    Q (Some(b,ro_replay_state base t xs))"
proof -
  note p=receive_trace_fri_challenge_outcome[OF out]
  note c=receive_trace_fri_challenge_counter_outcome[OF out]
  have key: "fmlookup (HashMap (ro_replay_state base s xs))
    (TraceFriChallenge (PTraceFriCounter (ro_replay_state base s xs))
      (PState (ro_replay_state base s xs)))=Some b"
    using hash_extension_lookup[OF conjunct2[OF conjunct2[OF conjunct2[OF p]]] ext] by simp
  have eq: "(ro_replay_state base s xs)\<lparr>PTraceFriCounter:=Suc(PTraceFriCounter s)\<rparr> =
    ro_replay_state base t xs"
    using p c by (cases s; cases t) (simp add: ro_replay_state_def)
  show ?thesis using receive_trace_fri_challenge_known_wp[OF key, where Q=Q] eq by simp
qed

lemma ro_composition_fri_challenge_replay:
  assumes out: "Some(b,t)\<in>set_dist(execute receive_composition_fri_challenge s)"
    and ext: "t\<le>base"
  shows "wp receive_composition_fri_challenge Q (ro_replay_state base s xs) =
    Q (Some(b,ro_replay_state base t xs))"
proof -
  note p=receive_composition_fri_challenge_outcome[OF out]
  note c=receive_composition_fri_challenge_counter_outcome[OF out]
  have key: "fmlookup (HashMap (ro_replay_state base s xs))
    (CompositionFriChallenge (PCompositionFriCounter (ro_replay_state base s xs))
      (PState (ro_replay_state base s xs)))=Some b"
    using hash_extension_lookup[OF conjunct2[OF conjunct2[OF conjunct2[OF p]]] ext] by simp
  have eq: "(ro_replay_state base s xs)\<lparr>PCompositionFriCounter:=Suc(PCompositionFriCounter s)\<rparr> =
    ro_replay_state base t xs"
    using p c by (cases s; cases t) (simp add: ro_replay_state_def)
  show ?thesis using receive_composition_fri_challenge_known_wp[OF key, where Q=Q] eq by simp
qed

lemma ro_alpha_challenge_replay:
  assumes out: "Some(b,t)\<in>set_dist(execute receive_alpha_challenge s)"
    and ext: "t\<le>base"
  shows "wp receive_alpha_challenge Q (ro_replay_state base s xs) =
    Q (Some(b,ro_replay_state base t xs))"
proof -
  note p=receive_alpha_challenge_outcome[OF out]
  note c=receive_alpha_challenge_counter_outcome[OF out]
  have key: "fmlookup (HashMap (ro_replay_state base s xs))
    (AlphaChallenge (PAlphaCounter (ro_replay_state base s xs))
      (PState (ro_replay_state base s xs)))=Some b"
    using hash_extension_lookup[OF conjunct2[OF conjunct2[OF conjunct2[OF p]]] ext] by simp
  have eq: "(ro_replay_state base s xs)\<lparr>PAlphaCounter:=Suc(PAlphaCounter s)\<rparr> =
    ro_replay_state base t xs"
    using p c by (cases s; cases t) (simp add: ro_replay_state_def)
  show ?thesis using receive_alpha_challenge_known_wp[OF key, where Q=Q] eq by simp
qed

lemma ro_trace_challenge_history:
  assumes out: "Some((rs,bs'),t)\<in>set_dist(execute (ro_staged_trace_fri_program A i n bs) s)"
  shows "bs'=bs @ drop (length bs) bs'"
  using out
proof (induction n arbitrary: i bs s rs bs' t)
  case 0 then show ?case by simp
next
  case (Suc n)
  then obtain b s3 tail where
    tail: "Some((tail,bs'),t)\<in>set_dist
      (execute (ro_staged_trace_fri_program A (Suc i) n (bs@[b])) s3)"
    by (auto elim!: set_dist_bindE split: prod.splits)
  from Suc.IH[OF tail] show ?case by (metis append_assoc append_eq_conv_conj)
qed

lemma ro_trace_commitments_replay:
  assumes roots: "\<And>j bs. hash_only_ro q (trace_fri_root_stage A j bs)"
    and out: "Some((rs,bs'),t)\<in>set_dist(execute (ro_staged_trace_fri_program A i n bs) s)"
    and ext: "t\<le>base"
  shows "wp (ntimes ro_receive_trace_fri_commits n) Q (ro_replay_state base s (rs@rest)) =
    Q (Some(zip (drop (length bs) bs') rs,ro_replay_state base t rest))"
  using out ext
proof (induction n arbitrary: i bs s rs bs' t base rest Q)
  case 0 then show ?case by (simp add: wp_return)
next
  case (Suc n)
  obtain r s1 s2 b s3 tail where
    rout: "Some(r,s1)\<in>set_dist(execute (trace_fri_root_stage A i bs) s)"
    and rec: "Some((),s2)\<in>set_dist(execute (ro_record_staged_message r) s1)"
    and recv: "Some(b,s3)\<in>set_dist(execute receive_trace_fri_challenge s2)"
    and tail: "Some((tail,bs'),t)\<in>set_dist
      (execute (ro_staged_trace_fri_program A (Suc i) n (bs@[b])) s3)"
    and rs: "rs=r#tail"
    using Suc.prems(1) by (auto elim!: set_dist_bindE split: prod.splits)
  have s3base: "s3\<le>base"
    using trace_prefix_properties[OF roots tail] Suc.prems(2) by (meson hash_ext_trans)
  have s2base: "s2\<le>base"
    using receive_trace_fri_challenge_outcome[OF recv] s3base by (meson hash_ext_trans)
  have fields: "ro_replay_state base s1 xs=ro_replay_state base s xs" for xs
    by (rule ro_replay_hash_only_fields[OF roots rout])
  have step: "wp ro_receive_trace_fri_commits F (ro_replay_state base s (r#xs)) =
    F (Some((b,r),ro_replay_state base s3 xs))" for F xs
    unfolding ro_receive_trace_fri_commits_def ro_receive_fri_commits_with_def
    using ro_recorded_scalar_replay[OF rec s2base] fields
    by (simp add: wp_bind wp_return ro_trace_fri_challenge_replay[OF recv s3base])
  have history: "bs'=(bs@[b])@drop (length (bs@[b])) bs'"
    by (rule ro_trace_challenge_history[OF tail])
  have drop: "drop (length bs) bs'=b#drop (length (bs@[b])) bs'"
    using arg_cong[OF history, of "drop (length bs)"] by simp
  show ?case
    by (simp add: wp_bind wp_return step Suc.IH[OF tail Suc.prems(2)] rs drop)
qed

lemma ro_composition_challenge_history:
  assumes out: "Some((rs,bs'),t)\<in>set_dist(execute (ro_staged_composition_fri_program A dg i n bs) s)"
  shows "bs'=bs @ drop (length bs) bs'"
  using out
proof (induction n arbitrary: i bs s rs bs' t)
  case 0 then show ?case by simp
next
  case (Suc n)
  then obtain b s3 tail where
    tail: "Some((tail,bs'),t)\<in>set_dist
      (execute (ro_staged_composition_fri_program A dg (Suc i) n (bs@[b])) s3)"
    by (auto elim!: set_dist_bindE split: prod.splits)
  from Suc.IH[OF tail] show ?case by (metis append_assoc append_eq_conv_conj)
qed

lemma ro_composition_commitments_replay:
  assumes roots: "\<And>j bs. hash_only_ro q (composition_fri_root_stage A dg j bs)"
    and out: "Some((rs,bs'),t)\<in>set_dist(execute (ro_staged_composition_fri_program A dg i n bs) s)"
    and ext: "t\<le>base"
  shows "wp (ntimes ro_receive_composition_fri_commits n) Q (ro_replay_state base s (rs@rest)) =
    Q (Some(zip (drop (length bs) bs') rs,ro_replay_state base t rest))"
  using out ext
proof (induction n arbitrary: i bs s rs bs' t base rest Q)
  case 0 then show ?case by (simp add: wp_return)
next
  case (Suc n)
  obtain r s1 s2 b s3 tail where
    rout: "Some(r,s1)\<in>set_dist(execute (composition_fri_root_stage A dg i bs) s)"
    and rec: "Some((),s2)\<in>set_dist(execute (ro_record_staged_message r) s1)"
    and recv: "Some(b,s3)\<in>set_dist(execute receive_composition_fri_challenge s2)"
    and tail: "Some((tail,bs'),t)\<in>set_dist
      (execute (ro_staged_composition_fri_program A dg (Suc i) n (bs@[b])) s3)"
    and rs: "rs=r#tail"
    using Suc.prems(1) by (auto elim!: set_dist_bindE split: prod.splits)
  have s3base: "s3\<le>base"
    using composition_prefix_properties[OF roots tail] Suc.prems(2) by (meson hash_ext_trans)
  have s2base: "s2\<le>base"
    using receive_composition_fri_challenge_outcome[OF recv] s3base by (meson hash_ext_trans)
  have fields: "ro_replay_state base s1 xs=ro_replay_state base s xs" for xs
    by (rule ro_replay_hash_only_fields[OF roots rout])
  have step: "wp ro_receive_composition_fri_commits F (ro_replay_state base s (r#xs)) =
    F (Some((b,r),ro_replay_state base s3 xs))" for F xs
    unfolding ro_receive_composition_fri_commits_def ro_receive_fri_commits_with_def
    using ro_recorded_scalar_replay[OF rec s2base] fields
    by (simp add: wp_bind wp_return ro_composition_fri_challenge_replay[OF recv s3base])
  have history: "bs'=(bs@[b])@drop (length (bs@[b])) bs'"
    by (rule ro_composition_challenge_history[OF tail])
  have drop: "drop (length bs) bs'=b#drop (length (bs@[b])) bs'"
    using arg_cong[OF history, of "drop (length bs)"] by simp
  show ?case
    by (simp add: wp_bind wp_return step Suc.IH[OF tail Suc.prems(2)] rs drop)
qed

lemma ro_alphas_replay:
  assumes out: "Some(as,t)\<in>set_dist(execute (ro_staged_alpha_program n) s)"
    and ext: "t\<le>base"
  shows "wp (mmap (replicate n ro_alpha_round)) Q (ro_replay_state base s (as@rest)) =
    Q (Some(as,ro_replay_state base t rest))"
  using out ext
proof (induction n arbitrary: s as t base rest Q)
  case 0 then show ?case by (simp add: wp_return)
next
  case (Suc n)
  obtain a s1 s2 tail where
    recv: "Some(a,s1)\<in>set_dist(execute receive_alpha_challenge s)"
    and rec: "Some((),s2)\<in>set_dist(execute (ro_record_staged_message a) s1)"
    and tail: "Some(tail,t)\<in>set_dist(execute (ro_staged_alpha_program n) s2)"
    and as: "as=a#tail"
    using Suc.prems(1) by (auto elim!: set_dist_bindE)
  have s2base: "s2\<le>base"
    using ro_staged_alpha_program_absorb_lookup_chain[OF tail] Suc.prems(2)
    by (meson hash_ext_trans)
  have s1base: "s1\<le>base"
    using ro_record_staged_message_absorb_lookup_state[OF rec] s2base
    by (meson hash_ext_trans)
  have step: "wp ro_alpha_round F (ro_replay_state base s (a#xs)) =
    F (Some(a,ro_replay_state base s2 xs))" for F xs
    unfolding ro_alpha_round_def
    by (simp add: wp_bind wp_return Let_def assert_def
      ro_alpha_challenge_replay[OF recv s1base] ro_recorded_scalar_replay[OF rec s2base])
  show ?case
    by (simp add: wp_bind wp_return step Suc.IH[OF tail Suc.prems(2)] as)
qed

lemma ro_recorded_messages_counter_fields:
  assumes out: "Some((),t)\<in>set_dist(execute (ro_record_staged_messages xs) s)"
  shows "PTraceFriCounter t=PTraceFriCounter s \<and>
    PCompositionFriCounter t=PCompositionFriCounter s \<and>
    PAlphaCounter t=PAlphaCounter s \<and> PQueryCounter t=PQueryCounter s"
  using out unfolding ro_record_staged_messages_def
proof (induction xs arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then obtain u where
    rec: "Some((),u)\<in>set_dist(execute (ro_record_staged_message x) s)"
    and tail: "Some((),t)\<in>set_dist(execute (mfold2 ro_record_staged_message xs) u)"
    by (auto elim!: set_dist_bindE)
  show ?case using Cons.IH[OF tail] ro_record_staged_message_counter_preserves[OF rec] by simp
qed

end

ML \<open>
  val _ = List.app (fn (name, expected, th) =>
    if Thm.nprems_of th = expected andalso null (Thm.hyps_of th)
      andalso null (Thm_Deps.all_oracles [th])
    then writeln (name ^ ": checked " ^ string_of_int expected ^ " explicit premises")
    else error ("Unexpected header-replay dependency: " ^ name))
    [("ro_replay_state_fields(1)", 0, @{thm ro_replay_state_fields(1)}),
     ("ro_replay_state_fields(2)", 0, @{thm ro_replay_state_fields(2)}),
     ("ro_replay_state_fields(3)", 0, @{thm ro_replay_state_fields(3)}),
     ("ro_replay_state_fields(4)", 0, @{thm ro_replay_state_fields(4)}),
     ("ro_replay_state_fields(5)", 0, @{thm ro_replay_state_fields(5)}),
     ("ro_replay_state_fields(6)", 0, @{thm ro_replay_state_fields(6)}),
     ("ro_replay_state_fields(7)", 0, @{thm ro_replay_state_fields(7)}),
     ("soundness.ro_replay_hash_only_fields", 3, @{thm soundness.ro_replay_hash_only_fields}),
     ("soundness.ro_recorded_scalar_replay", 3, @{thm soundness.ro_recorded_scalar_replay}),
     ("soundness.ro_trace_fri_challenge_replay", 3, @{thm soundness.ro_trace_fri_challenge_replay}),
     ("soundness.ro_composition_fri_challenge_replay", 3, @{thm soundness.ro_composition_fri_challenge_replay}),
     ("soundness.ro_alpha_challenge_replay", 3, @{thm soundness.ro_alpha_challenge_replay}),
     ("soundness.ro_trace_challenge_history", 2, @{thm soundness.ro_trace_challenge_history}),
     ("soundness.ro_trace_commitments_replay", 4, @{thm soundness.ro_trace_commitments_replay}),
     ("soundness.ro_composition_challenge_history", 2, @{thm soundness.ro_composition_challenge_history}),
     ("soundness.ro_composition_commitments_replay", 4, @{thm soundness.ro_composition_commitments_replay}),
     ("soundness.ro_alphas_replay", 3, @{thm soundness.ro_alphas_replay}),
     ("soundness.ro_recorded_messages_counter_fields", 2, @{thm soundness.ro_recorded_messages_counter_fields})];
\<close>

end
