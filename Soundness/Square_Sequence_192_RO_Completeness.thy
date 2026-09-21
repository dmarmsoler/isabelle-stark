(*  License: BSD-3-Clause *)
theory Square_Sequence_192_RO_Completeness
  imports "Stark.Square_Sequence_192_RO_Verifier_Header" "Stark.RO_Honest_Verifier_Query_Replay"
begin

section \<open>Full Honest Acceptance in the Absorbing RO Experiment\<close>

text \<open>The existing square endpoint equation suffices for honest acceptance by the original absorbing verifier after all 640 queries. The proof composes actual supported builder outcomes with exact chronological replay and the independently proved builder no-failure theorem. No verifier-success premise, fresh-challenge condition or budget-fit assertion is used. Honest resource fit and the public soundness bound remain separate.\<close>

context
  fixes a z :: field_192
    and combine :: "field_192 \<Rightarrow> field_192 \<Rightarrow> field_192"
begin

interpretation s: soundness combine field_generator_192 field_generator_192 64 1024 2
  stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
  "square_workload_spec 1024 a z" 640 "square_workload_spec2 1024 a z" 0 0 0
  by (rule square_192_soundness) simp

lemma square_ro_query_round_replay_wp:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some(((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and prior: "sent\<le>before"
    and query: "Some(raw,u)\<in>set_dist(execute s.receive_query_index_challenge before)"
    and opened: "Some(chunk,t)\<in>set_dist(execute (square_ro_query_opening a z raw) u)"
    and recorded: "Some((),v)\<in>set_dist(execute (s.ro_record_staged_messages chunk) t)"
    and ext: "v\<le>base"
  shows "wp (s.ro_verifier_query_round_program fr (zip tbs trs) tf as (zip cbs crs) cv)
    Q (ro_replay_state base before (chunk@rest)) =
      Q (Some((),ro_replay_state base v rest))"
proof -
  let ?start="ro_replay_state base before (chunk@rest)"
  have vs: "v\<le>?start" using ext by (simp add: less_eq_hash_ext_def)
  have fields: "?start\<lparr>PState:=PState v,PTranscript:=rest,
    PQueryCounter:=Suc(PQueryCounter ?start)\<rparr>=ro_replay_state base v rest"
    using s.ro_honest_query_replay_state[OF square_ro_query_opening_hash_only[OF endpoint]
      query opened recorded, where base=base and xs="chunk@rest" and rest=rest] by simp
  show ?thesis
    using square_ro_actual_query_round_wp[OF endpoint prefix prior query opened recorded vs,
      where Q=Q and rest=rest] fields by simp
qed

lemma square_ro_all_queries_replay_wp:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some(((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and queries: "Some(chunks,t)\<in>set_dist
      (execute (s.ro_checked_staged_query_program (square_ro_honest_callbacks a z) trs crs i n) before)"
    and prior: "sent\<le>before"
    and ext: "t\<le>base"
  shows "wp (ntimes (s.ro_verifier_query_round_program fr (zip tbs trs) tf as (zip cbs crs) cv) n)
    Q (ro_replay_state base before (concat chunks@rest)) =
      Q (Some(replicate n (),ro_replay_state base t rest))"
proof (rule s.ro_honest_checked_queries_replay_wp[OF _ _ queries prior ext])
  show "s.hash_only_ro 21364931 (query_opening_stage (square_ro_honest_callbacks a z) j raw)"
    for j raw
    by (simp add: square_ro_honest_callbacks_def square_ro_query_opening_hash_only[OF endpoint])
next
  fix j raw before u chunk t v base rest Q
  assume sb: "sent\<le>before"
    and query: "Some(raw,u)\<in>set_dist(execute s.receive_query_index_challenge before)"
    and opened: "Some(chunk,t)\<in>set_dist
      (execute (query_opening_stage (square_ro_honest_callbacks a z) j raw) u)"
    and recorded: "Some((),v)\<in>set_dist(execute (s.ro_record_staged_messages chunk) t)"
    and vb: "v\<le>base"
  have op: "Some(chunk,t)\<in>set_dist(execute (square_ro_query_opening a z raw) u)"
    using opened by (simp add: square_ro_honest_callbacks_def)
  show "wp (s.ro_verifier_query_round_program fr (zip tbs trs) tf as (zip cbs crs) cv)
    Q (ro_replay_state base before (chunk@rest)) =
      Q (Some((),ro_replay_state base v rest))"
    by (rule square_ro_query_round_replay_wp[OF endpoint prefix sb query op recorded vb])
qed

lemma square_ro_honest_builder_components:
  assumes build: "Some(data,t)\<in>set_dist
    (execute (s.ro_checked_staged_transcript_program (square_ro_honest_callbacks a z))
      s.adversary_initial_state)"
  obtains sent where
    "Some(((staged_trace_root data,staged_trace_fri_roots data,
      staged_trace_fri_challenges data,staged_trace_final data,staged_alphas data),
      staged_degree data,staged_composition_fri_roots data,
      staged_composition_fri_challenges data,staged_composition_final data),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    "Some(staged_query_chunks data,t)\<in>set_dist
      (execute (s.ro_checked_staged_query_program (square_ro_honest_callbacks a z)
        (staged_trace_fri_roots data) (staged_composition_fri_roots data) 0 640) sent)"
  using build
  unfolding s.ro_commitment_prefix_decomposition square_ro_honest_commitment_unchanged
    s.ro_after_commitment_prefix_def
  by (auto elim!: s.set_dist_bindE intro: that split: prod.splits)

lemma square_ro_honest_built_verifier_wp:
  assumes endpoint: "z=a^(2^1023)"
    and build: "Some(data,t)\<in>set_dist
      (execute (s.ro_checked_staged_transcript_program (square_ro_honest_callbacks a z))
        s.adversary_initial_state)"
    and ext: "t\<le>base"
  shows "wp s.ro_verify_monad Q
    (s.verifier_state_from_adversary base (s.staged_proof_transcript data)) =
      Q (Some(replicate 640 (),ro_replay_state base t []))"
proof -
  obtain sent where
    prefix: "Some(((staged_trace_root data,staged_trace_fri_roots data,
      staged_trace_fri_challenges data,staged_trace_final data,staged_alphas data),
      staged_degree data,staged_composition_fri_roots data,
      staged_composition_fri_challenges data,staged_composition_final data),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and queries: "Some(staged_query_chunks data,t)\<in>set_dist
      (execute (s.ro_checked_staged_query_program (square_ro_honest_callbacks a z)
        (staged_trace_fri_roots data) (staged_composition_fri_roots data) 0 640) sent)"
    by (rule square_ro_honest_builder_components[OF build])
  have cb: "s.hash_only_ro 21364931
    (query_opening_stage (square_ro_honest_callbacks a z) j raw)" for j raw
    by (simp add: square_ro_honest_callbacks_def square_ro_query_opening_hash_only[OF endpoint])
  have st: "sent\<le>t" by (rule s.ro_honest_checked_queries_extend[OF cb queries])
  have sb: "sent\<le>base" by (rule s.hash_ext_trans[OF st ext])
  show ?thesis
    apply (subst square_ro_actual_serialized_header_wp[OF endpoint prefix sb])
    using square_ro_all_queries_replay_wp[OF endpoint prefix queries s.hash_ext_refl ext,
      where Q=Q and rest="[]"] by simp
qed


lemma square_ro_honest_built_verifier_no_failure:
  assumes endpoint: "z=a^(2^1023)"
    and build: "Some(data,t)\<in>set_dist
      (execute (s.ro_checked_staged_transcript_program (square_ro_honest_callbacks a z))
        s.adversary_initial_state)"
  shows "None\<notin>dom(dist(execute s.ro_verify_monad
    (s.verifier_state_from_adversary t (s.staged_proof_transcript data))))"
  by (rule s.ro_replay_wp_no_failure)
    (rule square_ro_honest_built_verifier_wp[OF endpoint build s.hash_ext_refl])

lemma square_ro_honest_experiment_no_failure:
  assumes endpoint: "z=a^(2^1023)"
  shows "None\<notin>dom(dist(execute
    (s.ro_absorb_checked_staged_security_experiment (square_ro_honest_callbacks a z))
      s.adversary_initial_state))"
  unfolding s.ro_absorb_checked_staged_security_experiment_def
proof (rule no_failure_bindI[OF square_ro_honest_checked_builder_no_failure[OF endpoint]])
  fix data t
  assume build: "Some(data,t)\<in>set_dist
    (execute (s.ro_checked_staged_transcript_program (square_ro_honest_callbacks a z))
      s.adversary_initial_state)"
  let ?next="get \<bind> (\<lambda>s. put (s.verifier_state_from_adversary s
    (s.staged_proof_transcript data)) \<bind> (\<lambda>_. s.ro_verify_monad))"
  have replay: "wp ?next Q t=Q (Some(replicate 640 (),ro_replay_state t t []))" for Q
    by (simp only: wp_bind wp_get wp_put option.case prod.case
      square_ro_honest_built_verifier_wp[OF endpoint build s.hash_ext_refl])
  show "None\<notin>dom(dist(execute ?next t))"
    by (rule s.ro_replay_wp_no_failure[OF replay])
qed

lemma square_ro_honest_experiment_acceptance_one:
  assumes endpoint: "z=a^(2^1023)"
  shows "wp_event
    (s.ro_absorb_checked_staged_security_experiment (square_ro_honest_callbacks a z))
    (\<lambda>out. \<not>Option.is_none out) s.adversary_initial_state=1"
proof -
  have nf: "None\<notin>dom(dist(execute
    (s.ro_absorb_checked_staged_security_experiment (square_ro_honest_callbacks a z))
    s.adversary_initial_state))"
    by (rule square_ro_honest_experiment_no_failure[OF endpoint])
  show ?thesis unfolding wp_event_def wp_def
    by (rule dist_expect_eq_1) (use nf in \<open>metis Option.is_none_def\<close>)
qed

end
ML \<open>
  val _ = List.app (fn (name, expected, th) =>
    if Thm.nprems_of th = expected andalso null (Thm.hyps_of th)
      andalso null (Thm_Deps.all_oracles [th])
    then writeln (name ^ ": checked " ^ string_of_int expected ^ " explicit premises")
    else error ("Unexpected all-query replay dependency: " ^ name))
    [("square_ro_query_round_replay_wp", 7, @{thm square_ro_query_round_replay_wp}),
     ("square_ro_all_queries_replay_wp", 5, @{thm square_ro_all_queries_replay_wp}),
     ("square_ro_honest_builder_components", 2, @{thm square_ro_honest_builder_components}),
     ("square_ro_honest_built_verifier_wp", 3, @{thm square_ro_honest_built_verifier_wp}),
     ("square_ro_honest_built_verifier_no_failure", 2, @{thm square_ro_honest_built_verifier_no_failure}),
     ("square_ro_honest_experiment_no_failure", 1, @{thm square_ro_honest_experiment_no_failure}),
     ("square_ro_honest_experiment_acceptance_one", 1, @{thm square_ro_honest_experiment_acceptance_one})];
\<close>

end
