(*  License: BSD-3-Clause *)
theory Square_Sequence_192_RO_Verifier_Header
 imports "Stark.RO_Honest_Verifier_Header" "Stark.Square_Sequence_192_RO_Query_Verifier"
begin

section \<open>Actual Honest Header and First Query Replay\<close>

text \<open>The existing absorbing verifier starts from its original verifier-state transfer and receives the actual honest commitment data. The proved honest algebra discharges its decoded-degree guard. Header replay leaves the original 640-query continuation; a supported first honest query leaves the original 639-query continuation. Endpoint-only full-experiment acceptance and honest resource fit remain separate.\<close>

context
  fixes a z :: field_192
    and combine :: "field_192 \<Rightarrow> field_192 \<Rightarrow> field_192"
begin

interpretation s: soundness combine field_generator_192 field_generator_192 64 1024 2
  stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
  "square_workload_spec 1024 a z" 640 "square_workload_spec2 1024 a z" 0 0 0
  by (rule square_192_soundness) simp

interpretation p: prover combine field_generator_192 field_generator_192 64 1024 2
  stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
  "square_workload_spec 1024 a z" 640 "square_trace_values 1024 a"
  by unfold_locales simp

interpretation honest: verification combine field_generator_192 field_generator_192 64 1024 2
  stark_mod_ring_encode stark_mod_ring_decode field_cardinality_192
  "square_workload_spec 1024 a z" 640 "square_workload_spec2 1024 a z"
  "square_trace_values 1024 a"
proof unfold_locales
  fix c roots d
  assume entry: "(c,roots,d) \<in> set (square_workload_spec 1024 a z)"
  show "degree (c p.f_powers) \<le> d*(1024-1)"
    using square_workload_constraint_degree[OF p.honest_interpolant_degree entry]
    by (simp add: p.f_powers_def)
qed

lemma square_ro_actual_verifier_degree_guard:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some(((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
  shows "stark_mod_ring_decode dg\<le>s.maxDegree"
  using square_ro_commitment_prefix_outcome[OF endpoint prefix]
    honest.honest_degree_message_assert_hol[OF square_192_honest_trace_valid[OF endpoint], of as]
  by simp

lemma square_ro_actual_header_wp:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some(((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and ext: "sent\<le>base"
  shows "wp s.ro_verify_monad Q
    (s.verifier_state_from_adversary base ((fr#trs@[tf]@as@[dg]@crs@[cv])@rest)) =
    wp (ntimes (s.ro_verifier_query_round_program fr (zip tbs trs) tf as (zip cbs crs) cv) 640)
      Q (ro_replay_state base sent rest)"
  unfolding s.ro_verify_monad_def
  by (rule s.ro_complete_header_replay[OF
    square_ro_commitment_hash_only(1) square_ro_commitment_hash_only(2)
    square_ro_commitment_hash_only(3) square_ro_commitment_hash_only(4)
    square_ro_commitment_hash_only(5) square_ro_commitment_hash_only(6)
    prefix square_ro_actual_verifier_degree_guard[OF endpoint prefix] ext,
      unfolded s.ro_replay_initial_state])

lemma square_ro_actual_serialized_header_wp:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some(((staged_trace_root data,staged_trace_fri_roots data,
      staged_trace_fri_challenges data,staged_trace_final data,staged_alphas data),
      staged_degree data,staged_composition_fri_roots data,
      staged_composition_fri_challenges data,staged_composition_final data),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and ext: "sent\<le>base"
  shows "wp s.ro_verify_monad Q (s.verifier_state_from_adversary base (s.staged_proof_transcript data)) =
    wp (ntimes (s.ro_verifier_query_round_program (staged_trace_root data)
      (zip (staged_trace_fri_challenges data) (staged_trace_fri_roots data))
      (staged_trace_final data) (staged_alphas data)
      (zip (staged_composition_fri_challenges data) (staged_composition_fri_roots data))
      (staged_composition_final data)) 640) Q
      (ro_replay_state base sent (concat (staged_query_chunks data)))"
  using square_ro_actual_header_wp[OF endpoint prefix ext, where Q=Q
    and rest="concat (staged_query_chunks data)"]
  by (simp add: s.staged_proof_transcript_def s.verifier_header_messages_def)

lemma square_ro_actual_header_first_query_wp:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some(((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and query: "Some(raw,u)\<in>set_dist(execute s.receive_query_index_challenge sent)"
    and opened: "Some(chunk,t)\<in>set_dist(execute (square_ro_query_opening a z raw) u)"
    and recorded: "Some((),v)\<in>set_dist(execute (s.ro_record_staged_messages chunk) t)"
    and ext: "v\<le>base"
  shows "wp s.ro_verify_monad Q
    (s.verifier_state_from_adversary base
      ((fr#trs@[tf]@as@[dg]@crs@[cv])@chunk@rest)) =
    wp (ntimes (s.ro_verifier_query_round_program fr (zip tbs trs) tf as (zip cbs crs) cv) 639
      \<bind> (\<lambda>ys. return (()#ys))) Q (ro_replay_state base v rest)"
proof -
  let ?m="s.ro_verifier_query_round_program fr (zip tbs trs) tf as (zip cbs crs) cv"
  let ?start="ro_replay_state base sent (chunk@rest)"
  note qp=s.receive_query_index_challenge_outcome[OF query]
  note qc=s.receive_query_index_challenge_counter_outcome[OF query]
  note ofields=s.hash_only_ro_fields[OF square_ro_query_opening_hash_only[OF endpoint] opened]
  note rc=s.ro_recorded_messages_counter_fields[OF recorded]
  have su: "sent\<le>u" using qp by simp
  have ut: "u\<le>t"
    using s.hash_only_ro_extends[OF square_ro_query_opening_hash_only[OF endpoint]] opened
    unfolding s.hash_extension_preserving_def by blast
  have tv: "t\<le>v" using s.ro_record_staged_messages_absorb_lookup_chain[OF recorded] by simp
  have sb: "sent\<le>base" using su ut tv ext by (meson s.hash_ext_trans)
  have vs: "v\<le>?start" using ext by (simp add: less_eq_hash_ext_def)
  have eq: "?start\<lparr>PState:=PState v,PTranscript:=rest,
    PQueryCounter:=Suc(PQueryCounter ?start)\<rparr> = ro_replay_state base v rest"
    using qp qc ofields rc
    by (cases sent; cases u; cases t; cases v) (simp add: ro_replay_state_def)
  have qw: "wp ?m F ?start=F (Some((),ro_replay_state base v rest))" for F
    using square_ro_actual_query_round_wp[OF endpoint prefix s.hash_ext_refl
      query opened recorded vs, where Q=F and rest=rest] eq by simp
  have count: "(640::nat)=Suc 639" by simp
  show ?thesis
    apply (subst square_ro_actual_header_wp[OF endpoint prefix sb])
    by (simp only: count ntimes.simps wp_bind qw option.case prod.case)
qed

end

ML \<open>
  val _ = List.app (fn (name, expected, th) =>
    if Thm.nprems_of th = expected andalso null (Thm.hyps_of th)
      andalso null (Thm_Deps.all_oracles [th])
    then writeln (name ^ ": checked " ^ string_of_int expected ^ " explicit premises")
    else error ("Unexpected header-replay dependency: " ^ name))
    [("square_ro_actual_verifier_degree_guard", 2, @{thm square_ro_actual_verifier_degree_guard}),
     ("square_ro_actual_header_wp", 3, @{thm square_ro_actual_header_wp}),
     ("square_ro_actual_serialized_header_wp", 3, @{thm square_ro_actual_serialized_header_wp}),
     ("square_ro_actual_header_first_query_wp", 6, @{thm square_ro_actual_header_first_query_wp})];
\<close>

end
