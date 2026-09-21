(*  Title:      Stark/Square_Sequence_192_RO_Query_Witnesses.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Square_Sequence_192_RO_Query_Witnesses
 imports "Stark.Square_Sequence_192_RO_Openings"
begin

section \<open>Actual Honest Query-Round Witness Alignment\<close>

text \<open>Align the actual commitment data with simultaneous authentication, path-length and serialization witnesses from an honest opening. Tree uniqueness needs no collision-freedom premise; zero-depth composition remains included.\<close>

lemma protocol_created_pairs_unique:
  assumes words: "map fst xs=map fst ys"
    and left: "\<And>w t. (w,t)\<in>set xs \<Longrightarrow> protocol_created_tree w t s"
    and right: "\<And>w t. (w,t)\<in>set ys \<Longrightarrow> protocol_created_tree w t s"
  shows "xs=ys"
proof (rule nth_equalityI)
  show len: "length xs=length ys"
    using arg_cong[OF words, of length] by simp
  fix i assume ix: "i<length xs"
  have iy: "i<length ys" using ix len by simp
  obtain w t where x: "xs!i=(w,t)" by (cases "xs!i") auto
  obtain v r where y: "ys!i=(v,r)" by (cases "ys!i") auto
  have wv: "w=v" using arg_cong[OF words, of "\<lambda>zs. zs!i"] ix iy
    by (simp add: x y)
  have ct: "protocol_created_tree w t s"
    by (rule left) (use ix x in \<open>metis nth_mem\<close>)
  have cr: "protocol_created_tree w r s"
    by (rule right) (use iy y wv in \<open>metis nth_mem\<close>)
  show "xs!i=ys!i"
    using protocol_created_tree_unique[OF ct cr] by (simp add: x y wv)
qed
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

lemma square_ro_header_terminal_value:
  assumes prefix: "Some ((fr,trs,tbs,tf,as),h)\<in>set_dist
    (execute (s.ro_header_prefix (square_ro_commitment_callbacks a z)) u)"
  shows "tf=hd (square_ro_trace_layer a tbs)"
  using prefix unfolding s.ro_header_prefix_def
  by (auto simp: square_ro_commitment_callbacks_def square_ro_header_callbacks_def
    simp del: s.ro_staged_trace_fri_program.simps
    elim!: s.set_dist_bindE split: prod.splits)

lemma square_ro_query_round_commitment_data:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some (((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
  shows "length tbs=10 \<and>
    length cbs=ceil_log (stark_mod_ring_decode
      (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1) \<and>
    tf=hd (square_ro_trace_layer a tbs) \<and>
    cv=hd (square_ro_composition_layer a z as cbs)"
proof -
  obtain h where header: "Some ((fr,trs,tbs,tf,as),h)\<in>set_dist
    (execute (s.ro_header_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    using square_ro_commitment_header_embedding[OF prefix] by blast
  show ?thesis
    using square_ro_header_authenticated[OF header]
      square_ro_header_terminal_value[OF header]
      square_ro_commitment_prefix_outcome[OF endpoint prefix]
    by auto
qed

lemma square_ro_actual_opening_witnesses:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some (((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and ext: "sent\<le>u"
    and out: "Some (chunk,t)\<in>set_dist (execute (square_ro_query_opening a z raw) u)"
  obtains tree tp cps where
    "u\<le>t"
    "protocol_created_tree (square_ro_trace_layer a []) tree t"
    "value tree=fr"
    "\<And>j. length (get_authentication_path 65536 j tree)=16"
    "map fst tp=square_ro_opening_trace_words a tbs"
    "map (value \<circ> snd) tp=trs"
    "map fst cps=square_ro_opening_composition_words a z as cbs"
    "map (value \<circ> snd) cps=crs"
    "\<And>xs tr. (xs,tr)\<in>set tp \<union> set cps \<Longrightarrow> protocol_created_tree xs tr t"
    "\<And>xs tr j. (xs,tr)\<in>set tp \<union> set cps \<Longrightarrow>
      length (get_authentication_path (length xs) j tr)=floor_log (length xs)"
    "chunk=s.honest_query_chunk (square_ro_trace_layer a []) tree (s.index (stark_mod_ring_decode raw)) @
      List.concat (s.honest_fri_chunks tp (s.index (stark_mod_ring_decode raw))) @
      List.concat (s.honest_fri_chunks cps (s.index (stark_mod_ring_decode raw)))"
proof -
  have bout: "Some (chunk,t)\<in>set_dist (execute (square_ro_opening_body a z tbs as cbs raw) u)"
    by (rule s.wp_equality_support[OF square_ro_query_opening_reconstruction[OF prefix ext] out])
  obtain tree tp cps where ut: "u\<le>t"
    and base: "protocol_created_tree (square_ro_trace_layer a []) tree t"
    and bpaths: "\<forall>j. length (get_authentication_path 65536 j tree)=16"
    and tw: "map fst tp=square_ro_opening_trace_words a tbs"
    and cw: "map fst cps=square_ro_opening_composition_words a z as cbs"
    and built: "\<forall>xs tr. (xs,tr)\<in>set tp \<union> set cps \<longrightarrow> protocol_created_tree xs tr t \<and>
      (xs\<noteq>[] \<longrightarrow> (\<forall>j. length (get_authentication_path (length xs) j tr)=floor_log (length xs)))"
    and chunk: "chunk=s.honest_query_chunk (square_ro_trace_layer a []) tree (s.index (stark_mod_ring_decode raw)) @
      List.concat (s.honest_fri_chunks tp (s.index (stark_mod_ring_decode raw))) @
      List.concat (s.honest_fri_chunks cps (s.index (stark_mod_ring_decode raw)))"
    using square_ro_opening_body_outcome[OF bout] by blast
  obtain tree' tp' cps' where base': "protocol_created_tree (square_ro_trace_layer a []) tree' t"
    and root': "value tree'=fr"
    and tw': "map fst tp'=square_ro_opening_trace_words a tbs"
    and cw': "map fst cps'=square_ro_opening_composition_words a z as cbs"
    and tr': "map (value \<circ> snd) tp'=trs"
    and cr': "map (value \<circ> snd) cps'=crs"
    and built': "\<forall>xs tr. (xs,tr)\<in>set tp' \<union> set cps' \<longrightarrow> protocol_created_tree xs tr t"
    using square_ro_query_opening_authenticated_trees[OF endpoint prefix ext out] by blast
  have tp: "tp=tp'"
    by (rule protocol_created_pairs_unique[OF trans[OF tw tw'[symmetric]]])
      (use built built' in auto)
  have cps: "cps=cps'"
    by (rule protocol_created_pairs_unique[OF trans[OF cw cw'[symmetric]]])
      (use built built' in auto)
  have root: "value tree=fr"
    using protocol_created_tree_unique[OF base base'] root' by simp
  have tb: "length tbs=10" and cb: "length cbs=ceil_log (stark_mod_ring_decode
      (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)"
    using square_ro_query_round_commitment_data[OF endpoint prefix] by auto
  have ne: "xs\<noteq>[]" if mem: "(xs,tr)\<in>set tp \<union> set cps" for xs tr
    using square_ro_opening_word_nonempty[OF endpoint tb cb] tw cw mem
    by (metis Un_iff fst_conv image_eqI list.set_map)
  show thesis
    by (rule that[OF ut base root])
      (use bpaths tw cw tr' cr' tp cps built ne chunk in auto)
qed

end

ML \<open>
  val _ = List.app (fn (name, expected, th) =>
    if Thm.nprems_of th = expected andalso null (Thm.hyps_of th)
       andalso null (Thm_Deps.all_oracles [th])
    then writeln (name ^ ": checked " ^ string_of_int expected ^ " explicit premises")
    else error ("Unexpected query-round dependency: " ^ name))
    [("protocol_created_pairs_unique", 3, @{thm protocol_created_pairs_unique}),
     ("square_ro_header_terminal_value", 1, @{thm square_ro_header_terminal_value}),
     ("square_ro_query_round_commitment_data", 2, @{thm square_ro_query_round_commitment_data}),
     ("square_ro_actual_opening_witnesses", 5, @{thm square_ro_actual_opening_witnesses})];
\<close>

end
