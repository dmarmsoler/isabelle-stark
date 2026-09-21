(* Title: Stark/FS_Full_Transcript_Reconstruction.thy
   License: BSD-3-Clause *)

theory FS_Full_Transcript_Reconstruction
  imports FS_Full_Reconstruction_Primitives
begin

section \<open>Complete staged reconstruction of a fixed transcript\<close>

text \<open>Pure selectors drive the existing complete staged transcript builder.
  Alpha echoes and decoded degree remain explicit failure guards. After producing
  the actual staged proof record, the existing security experiment resets the
  cursor and counters and runs the whole original verifier.

  The final acceptance identity covers every fixed supplied transcript and every
  initial oracle cache. The stronger weakest-precondition identity ignores only
  the final transcript field: serialization discards unused suffixes. Initial
  protocol fields are those of the actual reset experiment, not arbitrary
  counters. This does not compile an adaptive transcript-producing attacker,
  equate operational oracle-call counts, translate conventional query budgets,
  or change a public soundness bound.\<close>

context soundness
begin

definition fs_sliced_callbacks where
  "fs_sliced_callbacks A fr rs tf supplied dg crs cf source =
    fs_header_callbacks
      (A\<lparr>query_opening_stage:=\<lambda>j _. return(take
        (verifier_query_round_transcript_length 0 rs crs)
        (drop(j*verifier_query_round_transcript_length 0 rs crs)source))\<rparr>)
      fr rs tf supplied dg crs cf"

lemma fs_sliced_callback_fields:
  "hash_only_ro 0 (trace_root_stage(fs_sliced_callbacks A fr rs tf supplied dg crs cf source))"
  "hash_only_ro 0 (trace_fri_root_stage(fs_sliced_callbacks A fr rs tf supplied dg crs cf source) j bs)"
  "hash_only_ro 0 (trace_final_stage(fs_sliced_callbacks A fr rs tf supplied dg crs cf source) bs)"
  "controlled_ro_program 0 (degree_stage(fs_sliced_callbacks A fr rs tf supplied dg crs cf source) as)"
  "hash_only_ro 0 (composition_fri_root_stage(fs_sliced_callbacks A fr rs tf supplied dg crs cf source) d j bs)"
  "hash_only_ro 0 (composition_final_stage(fs_sliced_callbacks A fr rs tf supplied dg crs cf source) d bs)"
  "hash_only_ro 0 (query_opening_stage(fs_sliced_callbacks A fr rs tf supplied dg crs cf source) j raw)"
  by (auto simp: fs_sliced_callbacks_def fs_header_callbacks_def assert_def fs_throw_bind
    split: if_splits)

lemma fs_sliced_callback_query_update:
  "(fs_sliced_callbacks A fr rs tf supplied dg crs cf source)
    \<lparr>query_opening_stage:=\<lambda>j _. return(take
      (verifier_query_round_transcript_length 0 rs crs)
      (drop(j*verifier_query_round_transcript_length 0 rs crs)source))\<rparr> =
    fs_sliced_callbacks A fr rs tf supplied dg crs cf source"
  by (simp add: fs_sliced_callbacks_def fs_header_callbacks_def)

lemma fs_replay_initial_cache:
  "ro_replay_state final (verifier_state_from_adversary base []) xs =
    verifier_state_from_adversary final xs"
  by (simp add: ro_replay_state_def verifier_state_from_adversary_def)

lemma fs_sliced_header_replay:
  assumes out: "Some(((fr,rs,bs,tf,supplied),dg,crs,cbs,cf),hdr)\<in>set_dist
    (execute(ro_commitment_prefix(fs_sliced_callbacks A fr rs tf supplied dg crs cf source))
      (verifier_state_from_adversary base []))"
    and guard: "to_nat dg\<le>maxDegree"
    and ext: "hdr\<le>final"
  shows "wp ro_verify_monad F
    (verifier_state_from_adversary final ((fr#rs@[tf]@supplied@[dg]@crs@[cf])@rest)) =
    wp(ntimes(ro_verifier_query_round_program fr (zip bs rs) tf supplied (zip cbs crs) cf)rounds)
      F (ro_replay_state final hdr rest)"
  using fs_controlled_degree_header_replay[OF fs_sliced_callback_fields(1)
    fs_sliced_callback_fields(2) fs_sliced_callback_fields(3)
    fs_sliced_callback_fields(4) fs_sliced_callback_fields(5)
    fs_sliced_callback_fields(6) out guard ext,
    where K="\<lambda>fr ffl tf as dg cfl cf. ntimes(ro_verifier_query_round_program fr ffl tf as cfl cf)rounds"
      and Q=F and rest=rest]
  by (simp add: ro_verify_monad_def Let_def fs_replay_initial_cache)

lemma fs_sliced_after_prefix_replay:
  fixes A fr rs tf supplied dg crs cf source bs cbs
  defines "B \<equiv> fs_sliced_callbacks A fr rs tf supplied dg crs cf source"
    and "prefix \<equiv> ((fr,rs,bs,tf,supplied),dg,crs,cbs,cf)"
    and "L \<equiv> verifier_query_round_transcript_length 0 rs crs"
    and "query \<equiv> ntimes(ro_verifier_query_round_program fr (zip bs rs) tf supplied (zip cbs crs) cf)rounds"
  assumes header: "Some(prefix,hdr)\<in>set_dist(execute(ro_commitment_prefix B)
      (verifier_state_from_adversary base []))"
    and lens: "length bs=length rs" "length cbs=length crs"
    and guard: "to_nat dg\<le>maxDegree"
    and obs: "fs_ignores_transcript F"
  shows "wp(ro_after_commitment_prefix B prefix \<bind> (\<lambda>data.
      get \<bind> (\<lambda>final. put(verifier_state_from_adversary final (staged_proof_transcript data))
        \<bind> (\<lambda>_. ro_verify_monad)))) F hdr =
    wp(fs_query_phase_checked_record_reset B rs crs L rounds \<bind> (\<lambda>_. query)) F
      (hdr\<lparr>PTranscript:=source\<rparr>)"
proof -
  let ?driver = "ro_checked_staged_query_program B rs crs 0 rounds"
  let ?saved = "hdr\<lparr>PTranscript:=source\<rparr>"
  let ?reset = "modify(\<lambda>t. ?saved\<lparr>HashMap:=HashMap t\<rparr>)"
  let ?data = "\<lambda>chunks. \<lparr>staged_trace_root=fr,staged_trace_fri_roots=rs,
    staged_trace_fri_challenges=bs,staged_trace_final=tf,staged_alphas=supplied,
    staged_degree=dg,staged_composition_fri_roots=crs,staged_composition_fri_challenges=cbs,
    staged_composition_final=cf,staged_query_chunks=chunks\<rparr>"
  have upd: "B\<lparr>query_opening_stage:=\<lambda>j _. return(take L(drop(j*L)source))\<rparr>=B"
    unfolding B_def L_def by (rule fs_sliced_callback_query_update)
  have maps: "map snd(zip bs rs)=rs" "map snd(zip cbs crs)=crs"
    using lens by simp_all
  have replay: "wp ro_verify_monad F
      (verifier_state_from_adversary final (staged_proof_transcript(?data chunks))) =
    wp query F (?saved\<lparr>HashMap:=HashMap final\<rparr>)"
    if out: "Some(chunks,final)\<in>set_dist(execute ?driver hdr)" for chunks final
  proof -
    have cb: "\<And>j raw. hash_only_ro 0 (query_opening_stage B j raw)"
      unfolding B_def by (rule fs_sliced_callback_fields(7))
    have ext: "hdr\<le>final"
      by (rule ro_honest_checked_queries_extend[OF cb out])
    have head: "wp ro_verify_monad F
        (verifier_state_from_adversary final (staged_proof_transcript(?data chunks))) =
      wp query F (ro_replay_state final hdr (List.concat chunks))"
      using fs_sliced_header_replay[OF header[unfolded B_def prefix_def] guard ext,
        where F=F and rest="List.concat chunks"]
      by (simp add: query_def staged_proof_transcript_def verifier_header_messages_def)
    have suffix: "wp query F (ro_replay_state final hdr (List.concat chunks)) =
      wp query F (ro_replay_state final hdr source)"
      using fs_sliced_query_replay_suffix[where A=B and ffl="zip bs rs" and cfl="zip cbs crs"
        and n=rounds and source=source and s=hdr and chunks=chunks and t=final and F=F
        and base="hdr\<lparr>HashMap:=HashMap final\<rparr>" and fr=fr and tf=tf and as=supplied and cf=cf]
        out obs
      by (simp add: maps upd[unfolded L_def] query_def ro_replay_state_def)
    show ?thesis using head suffix
      by (simp add: ro_replay_state_def fs_transcript_updates)
  qed
  have avg: "wp(?driver \<bind> (\<lambda>chunks. get \<bind> (\<lambda>final.
      put(verifier_state_from_adversary final (staged_proof_transcript(?data chunks)))
        \<bind> (\<lambda>_. ro_verify_monad)))) F hdr =
    wp(?driver \<bind> (\<lambda>_. ?reset \<bind> (\<lambda>_. query))) F hdr"
  proof (simp only: wp_bind wp_get wp_put wp_modify option.case prod.case, rule fs_wp_cong_on_support)
    fix out assume out: "out\<in>set_dist(execute ?driver hdr)"
    show "(case out of None \<Rightarrow> F None | Some(chunks,final) \<Rightarrow>
      wp ro_verify_monad F (verifier_state_from_adversary final (staged_proof_transcript(?data chunks)))) =
      (case out of None \<Rightarrow> F None | Some(x,final) \<Rightarrow> wp query F (?saved\<lparr>HashMap:=HashMap final\<rparr>))"
      using out by (cases out) (auto simp: replay split: prod.splits)
  qed
  have transport: "wp(?driver \<bind> (\<lambda>_. ?reset \<bind> (\<lambda>_. query))) F ?saved =
    wp(?driver \<bind> (\<lambda>_. ?reset \<bind> (\<lambda>_. query))) F hdr"
    using fs_sliced_query_reset_transcript[where A=B and source=source and L=L
      and trs=rs and crs=crs and i=0 and n=rounds and saved="?saved" and s=hdr and xs=source
      and F="\<lambda>out. case out of None \<Rightarrow> F None | Some(x,t) \<Rightarrow> wp query F t"]
    by (simp add: upd wp_bind cong: option.case_cong prod.case_cong)
  show ?thesis
    using avg transport
    by (simp add: prefix_def ro_after_commitment_prefix_def fs_query_phase_checked_record_reset_def
      sm_bind_assoc wp_bind wp_get wp_return upd cong: option.case_cong prod.case_cong)
qed

theorem fs_sliced_full_experiment_wp:
  assumes lens: "length rs=ceil_log clength" "length supplied=length spec"
    "length crs=ceil_log(to_nat dg+1)"
    and obs: "fs_ignores_transcript F"
  shows "wp(ro_absorb_checked_staged_security_experiment
      (fs_sliced_callbacks A fr rs tf supplied dg crs cf source)) F
      (verifier_state_from_adversary base []) =
    wp ro_verify_monad F
      (verifier_state_from_adversary base ((fr#rs@[tf]@supplied@[dg]@crs@[cf])@source))"
proof -
  let ?L = "verifier_query_round_transcript_length 0 rs crs"
  let ?A = "A\<lparr>query_opening_stage:=\<lambda>j _. return(take ?L(drop(j*?L)source))\<rparr>"
  let ?B = "fs_sliced_callbacks A fr rs tf supplied dg crs cf source"
  let ?initial = "verifier_state_from_adversary base []"
  let ?follow = "\<lambda>((fr,rs,bs,tf,as),dg,crs,cbs,cf).
    modify(\<lambda>t. t\<lparr>PTranscript:=source\<rparr>) \<bind> (\<lambda>_.
      ntimes(ro_verifier_query_round_program fr (zip bs rs) tf as (zip cbs crs) cf) rounds)"
  have bridge: "wp ro_verify_monad F
      (verifier_state_from_adversary base ((fr#rs@[tf]@supplied@[dg]@crs@[cf])@source)) =
    wp(ro_commitment_prefix ?B \<bind> ?follow) F ?initial"
    using fs_header_coupling_follow_wp[OF fs_guarded_header_coupling[OF lens, where A="?A"],
      where F=F and s="?initial" and rest=source and
      k="\<lambda>(fr,ffl,tf,as,dg,cfl,cf). ntimes(ro_verifier_query_round_program fr ffl tf as cfl cf)rounds"]
    by (simp add: fs_header_reader_verify fs_header_writer_def fs_sliced_callbacks_def
      sm_bind_assoc split_def verifier_state_from_adversary_def)

  have continuation: "wp(ro_after_commitment_prefix ?B prefix \<bind> (\<lambda>data.
      get \<bind> (\<lambda>final. put(verifier_state_from_adversary final(staged_proof_transcript data))
        \<bind> (\<lambda>_. ro_verify_monad)))) F hdr = wp(?follow prefix) F hdr"
    if pout: "Some(prefix,hdr)\<in>set_dist(execute(ro_commitment_prefix ?B) ?initial)"
    for prefix hdr
  proof -
    obtain bs cbs where prefix: "prefix=((fr,rs,bs,tf,supplied),dg,crs,cbs,cf)"
      and sizes: "length bs=length rs" "length cbs=length crs"
      and guard: "to_nat dg\<le>maxDegree"
      by (rule fs_guarded_prefix_outcome[OF lens pout[unfolded fs_sliced_callbacks_def]])
        (rule that; assumption)
    note replay = fs_sliced_after_prefix_replay[OF pout[unfolded prefix] sizes guard obs]
    have exact: "(fs_query_phase_checked_record_reset ?B rs crs ?L rounds \<bind> (\<lambda>_.
        ntimes(ro_verifier_query_round_program fr (zip bs rs) tf supplied (zip cbs crs) cf)rounds)) =
      ntimes(ro_verifier_query_round_program fr (zip bs rs) tf supplied (zip cbs crs) cf)rounds"
      using fs_actual_query_phase_checked_record_reset_exact[where A="?B"
        and ffl="zip bs rs" and cfl="zip cbs crs" and fr=fr and tf=tf and as=supplied
        and cf=cf and n=rounds] sizes by simp
    show ?thesis using replay exact
      by (simp add: prefix wp_bind wp_modify cong: option.case_cong prod.case_cong)
  qed
  have joint: "wp(ro_absorb_checked_staged_security_experiment ?B) F ?initial =
    wp(ro_commitment_prefix ?B \<bind> ?follow) F ?initial"
    unfolding ro_absorb_checked_staged_security_experiment_def
      ro_commitment_prefix_decomposition sm_bind_assoc
    apply (simp only: wp_bind)
    apply (rule fs_wp_cong_on_support)
    using continuation[unfolded wp_bind]
    by (auto split: option.splits prod.splits)

  show ?thesis using joint bridge by simp
qed

definition fs_fixed_transcript_staged_adversary where
  "fs_fixed_transcript_staged_adversary A source =
    (case fs_header_parse source of (fr,rs,tf,supplied,dg,crs,cf,rest) \<Rightarrow>
      let B=fs_sliced_callbacks A fr rs tf supplied dg crs cf rest
      in if fs_header_layout source then B else B\<lparr>trace_root_stage:=throw\<rparr>)"

lemma fs_staged_failed_root:
  assumes root: "trace_root_stage A=throw"
  shows "ro_absorb_checked_staged_security_experiment A=throw"
  by (simp add: ro_absorb_checked_staged_security_experiment_def
    ro_commitment_prefix_decomposition ro_commitment_prefix_def
    ro_header_prefix_def root fs_throw_bind)

theorem fs_fixed_transcript_full_reconstruction_wp:
  assumes obs: "fs_ignores_transcript F"
  shows "wp(ro_absorb_checked_staged_security_experiment
      (fs_fixed_transcript_staged_adversary A source)) F
      (verifier_state_from_adversary base []) =
    wp ro_verify_monad F (verifier_state_from_adversary base source)"
proof -
  obtain fr rs tf supplied dg crs cf rest where
    parsed: "fs_header_parse source=(fr,rs,tf,supplied,dg,crs,cf,rest)"
    by (cases "fs_header_parse source") auto
  show ?thesis
  proof (cases "fs_header_layout source")
    case False
    have fail: "ro_absorb_checked_staged_security_experiment
      (fs_fixed_transcript_staged_adversary A source)=throw"
      by (rule fs_staged_failed_root)
        (simp add: fs_fixed_transcript_staged_adversary_def parsed False Let_def)
    show ?thesis
      using fs_verifier_malformed_header_wp[where s="verifier_state_from_adversary base source"
        and F=F] False
      by (simp add: fail wp_throw)
  next
    case True
    note layout=fs_header_layout_parse[OF True parsed]
    have actor: "fs_fixed_transcript_staged_adversary A source =
      fs_sliced_callbacks A fr rs tf supplied dg crs cf rest"
      by (simp add: fs_fixed_transcript_staged_adversary_def parsed True Let_def)
    show ?thesis
      using fs_sliced_full_experiment_wp[OF layout(1-3) obs,
        where A=A and base=base and fr=fr and tf=tf and cf=cf and source=rest]
      by (simp only: actor) (simp add: layout(4))
  qed
qed

corollary fs_fixed_transcript_full_reconstruction_acceptance:
  "wp_event(ro_absorb_checked_staged_security_experiment
      (fs_fixed_transcript_staged_adversary A source)) accepted
      (verifier_state_from_adversary base []) =
    wp_event ro_verify_monad accepted (verifier_state_from_adversary base source)"
  unfolding wp_event_def
  by (rule fs_fixed_transcript_full_reconstruction_wp)
    (simp add: fs_ignores_transcript_def accepted_def)

lemma fs_fixed_transcript_callbacks_controlled:
  "controlled_ro_program 0 (trace_root_stage(fs_fixed_transcript_staged_adversary A source))"
  "controlled_ro_program 0 (trace_fri_root_stage(fs_fixed_transcript_staged_adversary A source) j bs)"
  "controlled_ro_program 0 (trace_final_stage(fs_fixed_transcript_staged_adversary A source) bs)"
  "controlled_ro_program 0 (degree_stage(fs_fixed_transcript_staged_adversary A source) as)"
  "controlled_ro_program 0 (composition_fri_root_stage(fs_fixed_transcript_staged_adversary A source) d j bs)"
  "controlled_ro_program 0 (composition_final_stage(fs_fixed_transcript_staged_adversary A source) d bs)"
  "controlled_ro_program 0 (query_opening_stage(fs_fixed_transcript_staged_adversary A source) j raw)"
  by (auto simp: fs_fixed_transcript_staged_adversary_def fs_sliced_callbacks_def
    fs_header_callbacks_def Let_def assert_def fs_throw_bind split: prod.splits if_splits)

end
ML \<open>
  val checked = @{thms
    soundness.fs_replay_controlled_fields
    soundness.fs_controlled_degree_header_replay
    soundness.fs_phase_suffix_wp
    soundness.fs_actual_query_suffix_irrelevant
    soundness.fs_sliced_query_chunks
    soundness.fs_guarded_prefix_outcome
    soundness.fs_checked_query_word_count
    soundness.fs_sliced_query_reset_transcript
    soundness.fs_sliced_query_replay_suffix
    soundness.fs_sliced_header_replay
    soundness.fs_sliced_after_prefix_replay
    soundness.fs_sliced_full_experiment_wp
    soundness.fs_fixed_transcript_full_reconstruction_wp
    soundness.fs_fixed_transcript_full_reconstruction_acceptance
    soundness.fs_fixed_transcript_callbacks_controlled};
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then () else error "Unexpected full reconstruction proof dependency") checked;
  val _ = if Thm.nprems_of @{thm soundness.fs_fixed_transcript_full_reconstruction_acceptance} = 1
    andalso Thm.nprems_of @{thm soundness.fs_fixed_transcript_full_reconstruction_wp} = 2
    then () else error "Unexpected final reconstruction premise count";
  writeln ("Full reconstruction checked conclusions: " ^ Int.toString (length checked));
\<close>
end
