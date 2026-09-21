(*  Title:      Stark/Square_Sequence_192_RO_Query_Verifier.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Square_Sequence_192_RO_Query_Verifier
 imports "Stark.Square_Sequence_192_RO_FRI_Verifier"
   "Stark.Square_Sequence_192_RO_Query_Values"
   "Stark.Square_Sequence_192_RO_Query_Witnesses"
begin

section \<open>Complete Actual Honest RO Query Round\<close>

text \<open>The original query-round program consumes the supported honest chunk and cannot fail at an aligned replay state. Its query lookup is derived from an actual challenge execution, and its counter is incremented exactly once. The ten explicit endpoint, support and replay conditions are local; whole-header replay, all repetitions and honest resource fit remain separate.\<close>
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

lemma square_ro_actual_query_checks_wp:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some (((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and ext: "sent\<le>u"
    and opened: "Some (chunk,t)\<in>set_dist (execute (square_ro_query_opening a z raw) u)"
    and recorded: "Some ((),v)\<in>set_dist (execute (s.ro_record_staged_messages chunk) t)"
    and extension: "v\<le>start"
    and cursor: "PState start=PState t"
    and transcript: "PTranscript start=chunk@rest"
  shows "wp (mmap (s.ro_check_decommit_on_query fr (s.index (stark_mod_ring_decode raw))) \<bind> (\<lambda>fv.
    (mfold (s.index (stark_mod_ring_decode raw),hd fv,65536,1)
      (s.ro_receive_query_commits (zip tbs trs)) \<bind>
        (\<lambda>(i,x,len,pw). assert (x=tf))) \<bind> (\<lambda>_.
    mfold (s.index (stark_mod_ring_decode raw),
      s.cp_eval as fv (s.h^s.index (stark_mod_ring_decode raw)*field_generator_192),65536,1)
      (s.ro_receive_query_commits (zip cbs crs)) \<bind>
        (\<lambda>(i,x,len,pw). assert (x=cv))))) Q start =
    Q (Some ((),start\<lparr>PState:=PState v,PTranscript:=rest\<rparr>))"
proof -
  let ?idx = "s.index (stark_mod_ring_decode raw)"
  let ?xs = "square_ro_trace_layer a []"
  let ?fv = "map (\<lambda>i. ?xs!i) (s.powers_scaled ?idx)"
  obtain tree tp cps where ut: "u\<le>t"
    and base: "protocol_created_tree ?xs tree t"
    and root: "value tree=fr"
    and paths: "\<And>j. length (get_authentication_path 65536 j tree)=16"
    and tw: "map fst tp=square_ro_opening_trace_words a tbs"
    and tr: "map (value \<circ> snd) tp=trs"
    and cw: "map fst cps=square_ro_opening_composition_words a z as cbs"
    and cr: "map (value \<circ> snd) cps=crs"
    and built: "\<And>xs tree. (xs,tree)\<in>set tp \<union> set cps \<Longrightarrow> protocol_created_tree xs tree t"
    and layers: "\<And>xs tree j. (xs,tree)\<in>set tp \<union> set cps \<Longrightarrow>
      length (get_authentication_path (length xs) j tree)=floor_log (length xs)"
    and chunk: "chunk=s.honest_query_chunk ?xs tree ?idx @
      List.concat (s.honest_fri_chunks tp ?idx) @ List.concat (s.honest_fri_chunks cps ?idx)"
    by (rule square_ro_actual_opening_witnesses[OF endpoint prefix ext opened]) blast
  have tb: "length tbs=10" and cb: "length cbs=ceil_log (stark_mod_ring_decode
      (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)"
    and tf: "tf=hd (square_ro_trace_layer a tbs)"
    and cv: "cv=hd (square_ro_composition_layer a z as cbs)"
    using square_ro_query_round_commitment_data[OF endpoint prefix] by auto
  have tv: "t\<le>v" and whole: "ro_absorb_lookup_chain v (PState start) chunk (PState v)"
    using s.ro_record_staged_messages_absorb_lookup_chain[OF recorded] cursor by auto
  have basev: "protocol_created_tree ?xs tree v"
    by (rule protocol_created_tree_mono[OF base tv])
  have builtv: "protocol_created_tree xs tree v" if "(xs,tree)\<in>set tp \<union> set cps" for xs tree
    by (rule protocol_created_tree_mono[OF built[OF that] tv])
  let ?dq = "s.honest_query_chunk ?xs tree ?idx"
  let ?tq = "List.concat (s.honest_fri_chunks tp ?idx)"
  let ?cq = "List.concat (s.honest_fri_chunks cps ?idx)"
  obtain c1 c2 where dq: "ro_absorb_lookup_chain v (PState start) ?dq c1"
    and tq: "ro_absorb_lookup_chain v c1 ?tq c2"
    and cq: "ro_absorb_lookup_chain v c2 ?cq (PState v)"
    using whole by (auto simp: chunk ro_absorb_lookup_chain_append_iff)
  let ?s1 = "start\<lparr>PState:=c1,PTranscript:=?tq@?cq@rest\<rparr>"
  let ?s2 = "start\<lparr>PState:=c2,PTranscript:=?cq@rest\<rparr>"
  have e1: "v\<le>?s1" and e2: "v\<le>?s2"
    using extension by (simp_all add: less_eq_hash_ext_def)
  have len: "length ?xs=65536"
    by (simp add: square_ro_trace_layer_def square_ro_fold_domain_def s.eval_domain_def s.H_def)
  have il: "?idx<65536" using square_ro_sampled_positions(1)[of raw] by arith
  have inds: "i<length ?xs" if "i\<in>set (s.powers_scaled ?idx)" for i
    using square_ro_sampled_positions(2)[OF that] len by simp
  have paths': "length (get_authentication_path (length ?xs) j tree)=floor_log (length ?xs)" for j
    using paths by (simp add: len floor_log_rec)
  have dtr: "PTranscript start=?dq @ (?tq@?cq@rest)"
    using transcript chunk by simp
  have init: "wp (mmap (s.ro_check_decommit_on_query fr ?idx)) F start =
    F (Some (?fv,?s1))" for F
    using s.ro_check_decommit_on_query_honest_wp[OF basev _ _ inds paths' dq extension dtr, where Q=F and n=16]
      len root by simp
  have twords: "map fst tp=map (\<lambda>j. square_ro_trace_layer a (take j tbs)) [0..<10]"
    using tw by (simp add: square_ro_opening_trace_words_def)
  have cwords: "map fst cps=map (\<lambda>j. square_ro_composition_layer a z as (take j cbs)) [0..<length cbs]"
    using cw cb by (simp add: square_ro_opening_composition_words_def)
  have trace: "wp (mfold (?idx,?xs!?idx,65536,1)
      (s.ro_receive_query_commits (zip tbs trs)) \<bind>
        (\<lambda>(i,x,len,pw). assert (x=tf))) F ?s1 =
      F (Some ((),?s2))" for F
    using square_ro_trace_fri_terminal_wp[OF tb twords _ _ il _ e1, where Q=F]
      builtv layers tq tr tf by auto
  have comp: "wp (mfold (?idx,square_ro_composition_layer a z as []!?idx,65536,1)
      (s.ro_receive_query_commits (zip cbs crs)) \<bind>
        (\<lambda>(i,x,len,pw). assert (x=cv))) F ?s2 =
      F (Some ((),start\<lparr>PState:=PState v,PTranscript:=rest\<rparr>))" for F
    using square_ro_composition_fri_terminal_wp[OF endpoint cb cwords _ _ il _ e2, where Q=F]
      builtv layers cq cr cv by auto
  show ?thesis
    apply (subst wp_bind)
    apply (subst init)
    apply (simp only: option.case prod.case square_ro_initial_trace_value
      square_ro_initial_composition_value[OF endpoint])
    apply (subst wp_bind)
    apply (subst trace)
    by (simp only: option.case prod.case comp)
qed


lemma square_ro_actual_query_round_wp:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some (((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and ext: "sent\<le>before"
    and query: "Some (raw,u)\<in>set_dist (execute s.receive_query_index_challenge before)"
    and opened: "Some (chunk,t)\<in>set_dist (execute (square_ro_query_opening a z raw) u)"
    and recorded: "Some ((),v)\<in>set_dist (execute (s.ro_record_staged_messages chunk) t)"
    and extension: "v\<le>start"
    and cursor: "PState start=PState before"
    and counter: "PQueryCounter start=PQueryCounter before"
    and transcript: "PTranscript start=chunk@rest"
  shows "wp (s.ro_verifier_query_round_program fr (zip tbs trs) tf as (zip cbs crs) cv) Q start =
    Q (Some ((),start\<lparr>PState:=PState v,PTranscript:=rest,
      PQueryCounter:=Suc (PQueryCounter start)\<rparr>))"
proof -
  note qp = s.receive_query_index_challenge_outcome[OF query]
  have su: "sent\<le>u" using ext qp by (meson s.hash_ext_trans)
  have ut: "u\<le>t"
    using square_ro_query_opening_authenticated_trees[OF endpoint prefix su opened] by blast
  have tv: "t\<le>v" using s.ro_record_staged_messages_absorb_lookup_chain[OF recorded] by simp
  have uv: "u\<le>v" by (rule s.hash_ext_trans[OF ut tv])
  have us: "u\<le>start" by (rule s.hash_ext_trans[OF uv extension])
  have key: "fmlookup (HashMap u) (QueryIndexChallenge (PQueryCounter before) (PState before))=Some raw"
    using qp by simp
  have known: "fmlookup (HashMap start) (QueryIndexChallenge (PQueryCounter start) (PState start))=Some raw"
    using protocol_merkle.hash_extension_lookup[OF key us] cursor counter by simp
  have fields: "PState t=PState u"
    using s.hash_only_ro_fields[OF square_ro_query_opening_hash_only[OF endpoint] opened] by simp
  let ?next = "start\<lparr>PQueryCounter:=Suc (PQueryCounter start)\<rparr>"
  have extension': "v\<le>?next" using extension by (simp add: less_eq_hash_ext_def)
  have cursor': "PState ?next=PState t" using cursor fields qp by simp
  have transcript': "PTranscript ?next=chunk@rest" using transcript by simp
  note checks = square_ro_actual_query_checks_wp[OF endpoint prefix su opened recorded
    extension' cursor' transcript', where Q=Q]
  show ?thesis
    unfolding s.ro_verifier_query_round_program_def
    apply (subst wp_bind)
    apply (subst s.receive_query_index_challenge_known_wp[OF known])
    using checks
    by (cases start) (simp add: Let_def sm_bind_assoc case_prod_unfold)
qed



lemma square_ro_actual_query_round_no_failure:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some (((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and ext: "sent\<le>before"
    and query: "Some (raw,u)\<in>set_dist (execute s.receive_query_index_challenge before)"
    and opened: "Some (chunk,t)\<in>set_dist (execute (square_ro_query_opening a z raw) u)"
    and recorded: "Some ((),v)\<in>set_dist (execute (s.ro_record_staged_messages chunk) t)"
    and extension: "v\<le>start"
    and cursor: "PState start=PState before"
    and counter: "PQueryCounter start=PQueryCounter before"
    and transcript: "PTranscript start=chunk@rest"
  shows "None\<notin>dom (dist (execute
    (s.ro_verifier_query_round_program fr (zip tbs trs) tf as (zip cbs crs) cv) start))"
proof -
  let ?m = "s.ro_verifier_query_round_program fr (zip tbs trs) tf as (zip cbs crs) cv"
  have zero: "wp_event ?m (\<lambda>out. out=None) start=0"
    unfolding wp_event_def by (simp add: square_ro_actual_query_round_wp[OF assms])
  show ?thesis
  proof
    assume bad: "None\<in>dom (dist (execute ?m start))"
    have pos: "0<wp_event ?m (\<lambda>out. out=None) start"
      by (rule s.wp_event_pos_of_support) (use bad in \<open>simp_all add: set_dist_def\<close>)
    show False using zero pos by simp
  qed
qed


end

ML \<open>
  val _ = List.app (fn (name, expected, th) =>
    if Thm.nprems_of th = expected andalso null (Thm.hyps_of th)
       andalso null (Thm_Deps.all_oracles [th])
    then writeln (name ^ ": checked " ^ string_of_int expected ^ " explicit premises")
    else error ("Unexpected query-round dependency: " ^ name))
    [("square_ro_actual_query_checks_wp", 8, @{thm square_ro_actual_query_checks_wp}),
     ("square_ro_actual_query_round_wp", 10, @{thm square_ro_actual_query_round_wp}),
     ("square_ro_actual_query_round_no_failure", 10, @{thm square_ro_actual_query_round_no_failure})];
\<close>

end
