(*  License: BSD-3-Clause *)
theory RO_Honest_Verifier_Header
  imports "Stark.RO_Honest_Verifier_Header_Primitives"
begin

section \<open>Complete Failure-Sensitive Verifier Header Replay\<close>

text \<open>Compose the original header operations in their chronological order. The decoded-degree guard is explicit in the generic lemma and is discharged for the honest concrete producer. The arbitrary continuation retains failures, outputs and the complete remaining state; no successful-verifier outcome is assumed.\<close>
context soundness
begin

lemma ro_replay_initial_state:
  "ro_replay_state base adversary_initial_state xs = verifier_state_from_adversary base xs"
  by (simp add: ro_replay_state_def adversary_initial_state_def verifier_state_from_adversary_def)

lemma ro_trace_header_replay:
  assumes root: "hash_only_ro qr (trace_root_stage A)"
    and roots: "\<And>i bs. hash_only_ro qt (trace_fri_root_stage A i bs)"
    and final: "\<And>bs. hash_only_ro qf (trace_final_stage A bs)"
    and out: "Some((fr,rs,bs,tf,as),t)\<in>set_dist(execute (ro_header_prefix A) s)"
    and ext: "t\<le>base"
  shows "wp (protocol_absorb_read \<bind> (\<lambda>fr.
    ntimes ro_receive_trace_fri_commits (ceil_log clength) \<bind> (\<lambda>fl.
    protocol_absorb_read \<bind> (\<lambda>tf.
    mmap (replicate (length spec) ro_alpha_round) \<bind> (\<lambda>as. K fr fl tf as)))))
      Q (ro_replay_state base s ((fr#rs@[tf]@as)@rest)) =
    wp (K fr (zip bs rs) tf as) Q (ro_replay_state base t rest)"
proof -
  obtain s1 s2 s3 s4 s5 where
    rout: "Some(fr,s1)\<in>set_dist(execute (trace_root_stage A) s)"
    and rrec: "Some((),s2)\<in>set_dist(execute (ro_record_staged_message fr) s1)"
    and tr: "Some((rs,bs),s3)\<in>set_dist
      (execute (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and fout: "Some(tf,s4)\<in>set_dist(execute (trace_final_stage A bs) s3)"
    and frec: "Some((),s5)\<in>set_dist(execute (ro_record_staged_message tf) s4)"
    and alphas: "Some(as,t)\<in>set_dist(execute (ro_staged_alpha_program (length spec)) s5)"
    using out unfolding ro_header_prefix_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have s5b: "s5\<le>base"
    using ro_staged_alpha_program_absorb_lookup_chain[OF alphas] ext by (meson hash_ext_trans)
  have s4b: "s4\<le>base"
    using ro_record_staged_message_absorb_lookup_state[OF frec] s5b by (meson hash_ext_trans)
  have s3s4: "s3\<le>s4" using hash_only_ro_extends[OF final] fout
    unfolding hash_extension_preserving_def by blast
  have s3b: "s3\<le>base" by (rule hash_ext_trans[OF s3s4 s4b])
  have s2b: "s2\<le>base"
    using trace_prefix_properties[OF roots tr] s3b by (meson hash_ext_trans)
  have rf: "ro_replay_state base s1 xs=ro_replay_state base s xs" for xs
    by (rule ro_replay_hash_only_fields[OF root rout])
  have ff: "ro_replay_state base s4 xs=ro_replay_state base s3 xs" for xs
    by (rule ro_replay_hash_only_fields[OF final fout])
  have rw: "wp protocol_absorb_read F (ro_replay_state base s (fr#xs)) =
    F (Some(fr,ro_replay_state base s2 xs))" for F xs
    using ro_recorded_scalar_replay[OF rrec s2b] rf by simp
  have fw: "wp protocol_absorb_read F (ro_replay_state base s3 (tf#xs)) =
    F (Some(tf,ro_replay_state base s5 xs))" for F xs
    using ro_recorded_scalar_replay[OF frec s5b] ff by simp
  show ?thesis
    by (simp add: wp_bind rw ro_trace_commitments_replay[OF roots tr s3b]
      fw ro_alphas_replay[OF alphas ext])
qed

lemma ro_complete_header_replay:
  assumes root: "hash_only_ro qr (trace_root_stage A)"
    and roots: "\<And>i bs. hash_only_ro qt (trace_fri_root_stage A i bs)"
    and tfinal: "\<And>bs. hash_only_ro qtf (trace_final_stage A bs)"
    and degree: "\<And>as. hash_only_ro qd (degree_stage A as)"
    and croots: "\<And>dg i bs. hash_only_ro qc (composition_fri_root_stage A dg i bs)"
    and cfinal: "\<And>dg bs. hash_only_ro qcf (composition_final_stage A dg bs)"
    and out: "Some(((fr,rs,bs,tf,as),dg,crs,cbs,cv),t)\<in>set_dist
      (execute (ro_commitment_prefix A) s)"
    and guard: "to_nat dg\<le>maxDegree"
    and ext: "t\<le>base"
  shows "wp (protocol_absorb_read \<bind> (\<lambda>fr.
    ntimes ro_receive_trace_fri_commits (ceil_log clength) \<bind> (\<lambda>fl.
    protocol_absorb_read \<bind> (\<lambda>tf.
    mmap (replicate (length spec) ro_alpha_round) \<bind> (\<lambda>as.
    protocol_absorb_read \<bind> (\<lambda>dg.
    assert(to_nat dg\<le>maxDegree) \<bind> (\<lambda>_.
    ntimes ro_receive_composition_fri_commits (ceil_log(to_nat dg+1)) \<bind> (\<lambda>cfl.
    protocol_absorb_read \<bind> (\<lambda>cv. K fr fl tf as dg cfl cv)))))))))
    Q (ro_replay_state base s ((fr#rs@[tf]@as@[dg]@crs@[cv])@rest)) =
    wp (K fr (zip bs rs) tf as dg (zip cbs crs) cv) Q (ro_replay_state base t rest)"
proof -
  obtain h d dr c f where
    header: "Some((fr,rs,bs,tf,as),h)\<in>set_dist(execute (ro_header_prefix A) s)"
    and dout: "Some(dg,d)\<in>set_dist(execute (degree_stage A as) h)"
    and drec: "Some((),dr)\<in>set_dist(execute (ro_record_staged_message dg) d)"
    and chain: "Some((crs,cbs),c)\<in>set_dist
      (execute (ro_staged_composition_fri_program A dg 0 (ceil_log(to_nat dg+1)) []) dr)"
    and fout: "Some(cv,f)\<in>set_dist(execute (composition_final_stage A dg cbs) c)"
    and frec: "Some((),t)\<in>set_dist(execute (ro_record_staged_message cv) f)"
    using out unfolding ro_commitment_prefix_def
    by (auto simp: assert_def throw_no_outcome elim!: set_dist_bindE split: prod.splits if_splits)
  have fb: "f\<le>base"
    using ro_record_staged_message_absorb_lookup_state[OF frec] ext by (meson hash_ext_trans)
  have cf: "c\<le>f" using hash_only_ro_extends[OF cfinal] fout
    unfolding hash_extension_preserving_def by blast
  have cb: "c\<le>base" by (rule hash_ext_trans[OF cf fb])
  have drb: "dr\<le>base"
    using composition_prefix_properties[OF croots chain] cb by (meson hash_ext_trans)
  have db: "d\<le>base"
    using ro_record_staged_message_absorb_lookup_state[OF drec] drb by (meson hash_ext_trans)
  have hd: "h\<le>d" using hash_only_ro_extends[OF degree] dout
    unfolding hash_extension_preserving_def by blast
  have hb: "h\<le>base" by (rule hash_ext_trans[OF hd db])
  have df: "ro_replay_state base d xs=ro_replay_state base h xs" for xs
    by (rule ro_replay_hash_only_fields[OF degree dout])
  have ff: "ro_replay_state base f xs=ro_replay_state base c xs" for xs
    by (rule ro_replay_hash_only_fields[OF cfinal fout])
  have dw: "wp protocol_absorb_read F (ro_replay_state base h (dg#xs)) =
    F (Some(dg,ro_replay_state base dr xs))" for F xs
    using ro_recorded_scalar_replay[OF drec drb] df by simp
  have fw: "wp protocol_absorb_read F (ro_replay_state base c (cv#xs)) =
    F (Some(cv,ro_replay_state base t xs))" for F xs
    using ro_recorded_scalar_replay[OF frec ext] ff by simp
  show ?thesis
    apply (simp only: append_assoc append_Cons append_Nil)
    apply (subst ro_trace_header_replay[OF root roots tfinal header hb,
      where rest="(dg#crs@[cv])@rest", simplified append_assoc append_Cons append_Nil])
    by (simp add: wp_bind wp_return assert_def guard dw
      ro_composition_commitments_replay[OF croots chain cb, simplified] fw)
qed

end

ML \<open>
  val _ = List.app (fn (name, expected, th) =>
    if Thm.nprems_of th = expected andalso null (Thm.hyps_of th)
      andalso null (Thm_Deps.all_oracles [th])
    then writeln (name ^ ": checked " ^ string_of_int expected ^ " explicit premises")
    else error ("Unexpected header-replay dependency: " ^ name))
    [("soundness.ro_replay_initial_state", 1, @{thm soundness.ro_replay_initial_state}),
     ("soundness.ro_trace_header_replay", 6, @{thm soundness.ro_trace_header_replay}),
     ("soundness.ro_complete_header_replay", 10, @{thm soundness.ro_complete_header_replay})];
\<close>

end
