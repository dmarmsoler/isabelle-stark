(*  License: BSD-3-Clause *)
theory RO_Honest_Verifier_Query_Replay
  imports "Stark.RO_Honest_Verifier_Header_Primitives"
begin

section \<open>Chronological Replay of Checked Query Sequences\<close>

text \<open>Replay the original counted query, honest hash-only opening and recorded messages in chronological order. The generic induction retains every result and local state field, including an arbitrary remaining transcript suffix. Its one-query premise is a proof interface discharged by the concrete verifier theorem, not an added public soundness premise.\<close>

context soundness
begin

lemma ro_honest_checked_queries_extend:
  assumes open_cb: "\<And>i raw. hash_only_ro q (query_opening_stage A i raw)"
    and out: "Some(chunks,t)\<in>set_dist
      (execute (ro_checked_staged_query_program A trs crs i n) before)"
  shows "before\<le>t"
  using out
proof (induction n arbitrary: i before chunks)
  case 0
  then show ?case by (simp add: hash_ext_refl)
next
  case (Suc n)
  obtain raw chunk chunks' u v w where
    query: "Some(raw,u)\<in>set_dist(execute receive_query_index_challenge before)"
    and opened: "Some(chunk,v)\<in>set_dist(execute (query_opening_stage A i raw) u)"
    and recorded: "Some((),w)\<in>set_dist(execute (ro_record_staged_messages chunk) v)"
    and tail: "Some(chunks',t)\<in>set_dist
      (execute (ro_checked_staged_query_program A trs crs (Suc i) n) w)"
    by (rule ro_checked_staged_query_program_Suc_outcomeE[OF Suc.prems]) blast
  have bu: "before\<le>u" using receive_query_index_challenge_outcome[OF query] by simp
  have uv: "u\<le>v" using hash_only_ro_extends[OF open_cb] opened
    unfolding hash_extension_preserving_def by blast
  have vw: "v\<le>w" using ro_record_staged_messages_absorb_lookup_chain[OF recorded] by simp
  have wt: "w\<le>t" by (rule Suc.IH[OF tail])
  show ?case using bu uv vw wt by (meson hash_ext_trans)
qed

lemma ro_honest_query_replay_state:
  assumes open_cb: "hash_only_ro q m"
    and query: "Some(raw,u)\<in>set_dist(execute receive_query_index_challenge before)"
    and opened: "Some(chunk,t)\<in>set_dist(execute m u)"
    and recorded: "Some((),v)\<in>set_dist(execute (ro_record_staged_messages chunk) t)"
  shows "(ro_replay_state base before xs)\<lparr>PState:=PState v,PTranscript:=rest,
      PQueryCounter:=Suc(PQueryCounter before)\<rparr> = ro_replay_state base v rest"
  using receive_query_index_challenge_outcome[OF query]
    receive_query_index_challenge_counter_outcome[OF query]
    hash_only_ro_fields[OF open_cb opened] ro_recorded_messages_counter_fields[OF recorded]
  by (cases before; cases u; cases t; cases v) (simp add: ro_replay_state_def)

lemma ro_honest_checked_queries_replay_wp:
  fixes m :: "(unit, 'f protocol_channel) state_monad"
  assumes open_cb: "\<And>i raw. hash_only_ro q (query_opening_stage A i raw)"
    and step: "\<And>i raw before u chunk t v base rest Q.
      initial\<le>before \<Longrightarrow>
      Some(raw,u)\<in>set_dist(execute receive_query_index_challenge before) \<Longrightarrow>
      Some(chunk,t)\<in>set_dist(execute (query_opening_stage A i raw) u) \<Longrightarrow>
      Some((),v)\<in>set_dist(execute (ro_record_staged_messages chunk) t) \<Longrightarrow>
      v\<le>base \<Longrightarrow>
      wp m Q (ro_replay_state base before (chunk@rest)) =
        Q (Some((),ro_replay_state base v rest))"
    and out: "Some(chunks,t)\<in>set_dist
      (execute (ro_checked_staged_query_program A trs crs i n) before)"
    and prior: "initial\<le>before"
    and ext: "t\<le>base"
  shows "wp (ntimes m n) Q (ro_replay_state base before (List.concat chunks@rest)) =
    Q (Some(replicate n (),ro_replay_state base t rest))"
  using out prior ext
proof (induction n arbitrary: i before chunks Q)
  case 0
  then show ?case by (simp add: wp_return)
next
  case (Suc n)
  obtain raw chunk chunks' u v w where
    query: "Some(raw,u)\<in>set_dist(execute receive_query_index_challenge before)"
    and opened: "Some(chunk,v)\<in>set_dist(execute (query_opening_stage A i raw) u)"
    and recorded: "Some((),w)\<in>set_dist(execute (ro_record_staged_messages chunk) v)"
    and tail: "Some(chunks',t)\<in>set_dist
      (execute (ro_checked_staged_query_program A trs crs (Suc i) n) w)"
    and chunks: "chunks=chunk#chunks'"
    by (rule ro_checked_staged_query_program_Suc_outcomeE[OF Suc.prems(1)]) blast
  have bu: "before\<le>u" using receive_query_index_challenge_outcome[OF query] by simp
  have uv: "u\<le>v" using hash_only_ro_extends[OF open_cb] opened
    unfolding hash_extension_preserving_def by blast
  have vw: "v\<le>w" using ro_record_staged_messages_absorb_lookup_chain[OF recorded] by simp
  have iw: "initial\<le>w" using Suc.prems(2) bu uv vw by (meson hash_ext_trans)
  have wt: "w\<le>t" by (rule ro_honest_checked_queries_extend[OF open_cb tail])
  have wb: "w\<le>base" by (rule hash_ext_trans[OF wt Suc.prems(3)])
  have first: "wp m F (ro_replay_state base before (chunk@(List.concat chunks'@rest))) =
    F (Some((),ro_replay_state base w (List.concat chunks'@rest)))" for F
    by (rule step[OF Suc.prems(2) query opened recorded wb])
  have remaining: "wp (ntimes m n) F (ro_replay_state base w (List.concat chunks'@rest)) =
    F (Some(replicate n (),ro_replay_state base t rest))" for F
    by (rule Suc.IH[OF tail iw Suc.prems(3)])
  show ?case
    by (simp only: chunks concat.simps append_assoc ntimes.simps wp_bind first
      option.case prod.case remaining wp_return replicate.simps)
qed

lemma ro_replay_wp_no_failure:
  assumes replay: "\<And>Q. wp m Q s=Q (Some(x,t))"
  shows "None\<notin>dom (dist (execute m s))"
proof -
  have zero: "wp_event m (\<lambda>out. out=None) s=0"
    unfolding wp_event_def by (simp add: replay)
  show ?thesis
  proof
    assume bad: "None\<in>dom (dist (execute m s))"
    have pos: "0<wp_event m (\<lambda>out. out=None) s"
      by (rule wp_event_pos_of_support) (use bad in \<open>simp_all add: set_dist_def\<close>)
    show False using zero pos by simp
  qed
qed

end
ML \<open>
  val _ = List.app (fn (name, expected, th) =>
    if Thm.nprems_of th = expected andalso null (Thm.hyps_of th)
      andalso null (Thm_Deps.all_oracles [th])
    then writeln (name ^ ": checked " ^ string_of_int expected ^ " explicit premises")
    else error ("Unexpected all-query replay dependency: " ^ name))
    [("soundness.ro_honest_checked_queries_extend", 3, @{thm soundness.ro_honest_checked_queries_extend}),
     ("soundness.ro_honest_query_replay_state", 5, @{thm soundness.ro_honest_query_replay_state}),
     ("soundness.ro_honest_checked_queries_replay_wp", 6, @{thm soundness.ro_honest_checked_queries_replay_wp}),
     ("soundness.ro_replay_wp_no_failure", 2, @{thm soundness.ro_replay_wp_no_failure})];
\<close>

end
