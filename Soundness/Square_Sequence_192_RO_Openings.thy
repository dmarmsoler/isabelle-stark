(*  Title:      Stark/Square_Sequence_192_RO_Openings.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Square_Sequence_192_RO_Openings
 imports "Stark.RO_Honest_Query_Reconstruction"
   "Stark.RO_Honest_Opening_Chunks" "Stark.Square_Sequence_192_RO_Composition"
begin

section \<open>Honest Square-Workload RO Query Openings\<close>

text \<open>The honest opening callback reconstructs actual commitment data using only tagged hash queries, re-creates the intended trees, and emits the original query/FRI chunk layout. The complete checked builder cannot fail at the correct endpoint. This is not full RO-verifier acceptance or a fit to the concrete security allowance.\<close>
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



definition square_ro_committed_data where
  "square_ro_committed_data =
    s.shadow_commitment_prefix (square_ro_commitment_callbacks a z) 0"

lemma square_ro_commitment_hash_only:
  "s.hash_only_ro 131071 (trace_root_stage (square_ro_commitment_callbacks a z))"
  "s.hash_only_ro 131071 (trace_fri_root_stage (square_ro_commitment_callbacks a z) i bs)"
  "s.hash_only_ro 0 (trace_final_stage (square_ro_commitment_callbacks a z) bs)"
  "s.hash_only_ro 0 (degree_stage (square_ro_commitment_callbacks a z) as)"
  "s.hash_only_ro 1572880 (composition_fri_root_stage (square_ro_commitment_callbacks a z) dg i bs)"
  "s.hash_only_ro 1441809 (composition_final_stage (square_ro_commitment_callbacks a z) dg bs)"
  by (simp_all add: square_ro_commitment_callbacks_def square_ro_header_callbacks_def
    square_ro_trace_root_hash_only square_ro_composition_root_hash_only
    square_ro_composition_final_hash_only s.hash_only_ro.Pure)

lemma square_ro_committed_data_reconstruction:
  assumes out: "Some (((fr,rs,bs,tf,as),dg,crs,cbs,cv),sent) \<in> set_dist
    (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and ext: "sent \<le> u"
  shows "wp square_ro_committed_data Q u =
    Q (Some (((fr,rs,bs,tf,as),dg,crs,cbs,cv),u))"
  unfolding square_ro_committed_data_def
  using s.shadow_commitment_prefix_replay[OF
    square_ro_commitment_hash_only(1) square_ro_commitment_hash_only(2)
    square_ro_commitment_hash_only(3) square_ro_commitment_hash_only(4)
    square_ro_commitment_hash_only(5) square_ro_commitment_hash_only(6)
    out _ _ _ ext, of Q]
  by (simp add: s.adversary_initial_state_def)

lemma square_ro_committed_data_hash_only:
  assumes endpoint: "z=a^(2^1023)"
  shows "s.hash_only_ro 18612440 square_ro_committed_data"
proof -
  have header: "s.hash_only_ro 1441809
    (s.shadow_header_cursor (square_ro_commitment_callbacks a z) 0)"
    using s.shadow_header_cursor_hash_only[OF square_ro_commitment_hash_only(1)
      square_ro_commitment_hash_only(2) square_ro_commitment_hash_only(3), of 0]
    by (simp add: ceil_log_def floor_log_rec)
  have comp: "s.hash_only_ro 15728820
    (s.shadow_composition (square_ro_commitment_callbacks a z)
      (stark_mod_ring_encode (degree (s.cp as p.f_powers))) 0
      (ceil_log (stark_mod_ring_decode
        (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)) [] cursor)" for as cursor
  proof -
    have h: "s.hash_only_ro ((1572880+2) *
      ceil_log (stark_mod_ring_decode
        (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1))
      (s.shadow_composition (square_ro_commitment_callbacks a z)
        (stark_mod_ring_encode (degree (s.cp as p.f_powers))) 0
        (ceil_log (stark_mod_ring_decode
          (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)) [] cursor)"
      by (rule s.shadow_composition_hash_only)
        (simp add: square_ro_commitment_callbacks_def square_ro_composition_root_hash_only)
    have bound: "(1572880+2) * ceil_log (stark_mod_ring_decode
      (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)
      \<le> (1572880+2)*10"
      by (rule mult_le_mono2) (rule square_ro_composition_depth_bound[OF endpoint])
    show ?thesis by (rule s.hash_only_ro.Bound[OF h]) (use bound in simp)
  qed
  have degree_cb: "degree_stage (square_ro_commitment_callbacks a z) as =
    return (stark_mod_ring_encode (degree (s.cp as p.f_powers)))" for as
    by (simp add: square_ro_commitment_callbacks_def square_ro_header_callbacks_def)
  have final_cb: "composition_final_stage (square_ro_commitment_callbacks a z) dg bs =
    square_ro_composition_final a z bs" for dg bs
    by (simp add: square_ro_commitment_callbacks_def)
  have h: "s.hash_only_ro (1441809 + Suc (15728820 + (1441809+1))) square_ro_committed_data"
    unfolding square_ro_committed_data_def s.shadow_commitment_prefix_def
    apply (rule s.hash_only_ro_bind[OF header])
    apply (simp only: case_prod_unfold)
    apply (simp only: degree_cb final_cb sm_bind_return_left)
    apply (rule s.hash_only_ro.Ask)
    apply (rule s.hash_only_ro_bind[OF comp])
    apply (rule s.hash_only_ro_bind[OF square_ro_composition_final_hash_only])
    by auto
  show ?thesis using h by simp
qed

definition square_ro_opening_trace_words where
  "square_ro_opening_trace_words bs =
    map (\<lambda>j. square_ro_trace_layer a (take j bs)) [0..<10]"

definition square_ro_opening_composition_words where
  "square_ro_opening_composition_words as bs =
    map (\<lambda>j. square_ro_composition_layer a z as (take j bs))
      [0..<ceil_log (stark_mod_ring_decode
        (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)]"

definition square_ro_opening_body where
  "square_ro_opening_body tbs as cbs raw =
    (protocol_create (square_ro_trace_layer a []) \<bind> (\<lambda>tree.
     s.honest_create_trees (square_ro_opening_trace_words tbs) \<bind> (\<lambda>tp.
     s.honest_create_trees (square_ro_opening_composition_words as cbs) \<bind> (\<lambda>cps.
     return (s.honest_query_chunk (square_ro_trace_layer a []) tree (s.index (stark_mod_ring_decode raw)) @
       List.concat (s.honest_fri_chunks tp (s.index (stark_mod_ring_decode raw))) @
       List.concat (s.honest_fri_chunks cps (s.index (stark_mod_ring_decode raw))))))))"

definition square_ro_query_opening where
  "square_ro_query_opening raw =
    (square_ro_committed_data \<bind> (\<lambda>((fr,trs,tbs,tf,as),dg,crs,cbs,cv).
     square_ro_opening_body tbs as cbs raw))"

lemma square_ro_tree_list_bound:
  assumes words: "\<And>xs. xs\<in>set xss \<Longrightarrow> length xs\<le>65536"
    and count: "length xss\<le>n"
  shows "s.hash_only_ro (131071*n) (s.honest_create_trees xss)"
proof -
  have sum: "sum_list (map (\<lambda>xs. 2*length xs-1) xss) \<le> 131071*length xss"
    using words
  proof (induction xss)
    case Nil
    show ?case by simp
  next
    case (Cons xs xss)
    have head: "length xs\<le>65536" by (rule Cons.prems) simp
    have tail: "sum_list (map (\<lambda>xs. 2*length xs-1) xss) \<le> 131071*length xss"
      by (rule Cons.IH) (use Cons.prems in auto)
    show ?case using head tail by simp
  qed
  show ?thesis
    by (rule s.hash_only_ro.Bound[OF s.honest_create_trees_hash_only])
      (use sum count in arith)
qed

lemma square_ro_opening_body_hash_only:
  assumes endpoint: "z=a^(2^1023)"
  shows "s.hash_only_ro 2752491 (square_ro_opening_body tbs as cbs raw)"
proof -
  have base: "s.hash_only_ro 131071 (protocol_create (square_ro_trace_layer a []))"
    using s.hash_only_ro_protocol_create[of "square_ro_trace_layer a []"]
    by (simp add: square_ro_trace_layer_def square_ro_fold_domain_def s.eval_domain_def s.H_def)
  have traces: "s.hash_only_ro (131071*10)
    (s.honest_create_trees (square_ro_opening_trace_words tbs))"
    by (rule square_ro_tree_list_bound)
      (auto simp: square_ro_opening_trace_words_def intro: square_ro_trace_layer_length)
  have comps: "s.hash_only_ro (131071*10)
    (s.honest_create_trees (square_ro_opening_composition_words as cbs))"
    apply (rule square_ro_tree_list_bound)
     apply (auto simp: square_ro_opening_composition_words_def
       intro: square_ro_composition_layer_length)[1]
    using square_ro_composition_depth_bound[OF endpoint, of as]
    by (simp add: square_ro_opening_composition_words_def)
  have "s.hash_only_ro (131071+(131071*10+131071*10))
    (square_ro_opening_body tbs as cbs raw)"
    unfolding square_ro_opening_body_def
    by (rule s.hash_only_ro_bind[OF base])
      (rule s.hash_only_ro_bind[OF traces s.hash_only_ro_map[OF comps]])
  then show ?thesis by simp
qed

lemma square_ro_query_opening_hash_only:
  assumes endpoint: "z=a^(2^1023)"
  shows "s.hash_only_ro 21364931 (square_ro_query_opening raw)"
proof -
  have "s.hash_only_ro (18612440+2752491) (square_ro_query_opening raw)"
    unfolding square_ro_query_opening_def
    apply (rule s.hash_only_ro_bind[OF square_ro_committed_data_hash_only[OF endpoint]])
    by (auto simp: case_prod_unfold intro: square_ro_opening_body_hash_only[OF endpoint])
  then show ?thesis by simp
qed

lemma square_ro_query_opening_controlled:
  assumes "z=a^(2^1023)"
  shows "s.controlled_ro_program 21364931 (square_ro_query_opening raw)"
  by (rule s.hash_only_ro_controlled[OF square_ro_query_opening_hash_only[OF assms]])

lemma square_ro_query_opening_no_failure:
  assumes "z=a^(2^1023)"
  shows "None\<notin>dom (dist (execute (square_ro_query_opening raw) u))"
  by (rule s.hash_only_ro_no_failure[OF square_ro_query_opening_hash_only[OF assms]])

lemma square_ro_query_opening_reconstruction:
  assumes out: "Some (((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
    (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and ext: "sent\<le>u"
  shows "wp (square_ro_query_opening raw) Q u = wp (square_ro_opening_body tbs as cbs raw) Q u"
  unfolding square_ro_query_opening_def
  by (simp only: wp_bind square_ro_committed_data_reconstruction[OF out ext] prod.case option.case)

lemma square_ro_opening_word_lengths:
  assumes tb: "length tbs=10"
    and cb: "length cbs=ceil_log (stark_mod_ring_decode
      (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)"
  shows "map length (square_ro_opening_trace_words tbs)=s.fri_layer_lengths 10 65536"
    "map length (square_ro_opening_composition_words as cbs)=s.fri_layer_lengths (length cbs) 65536"
  using tb cb
  by (auto intro!: nth_equalityI
    simp: square_ro_opening_trace_words_def square_ro_opening_composition_words_def
      square_ro_trace_layer_def square_ro_composition_layer_def
      square_ro_fold_domain_exact_length s.eval_domain_def s.H_def
      s.fri_layer_lengths_nth_div)

lemma square_ro_opening_word_nonempty:
  assumes endpoint: "z=a^(2^1023)"
    and tb: "length tbs=10"
    and cb: "length cbs=ceil_log (stark_mod_ring_decode
      (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)"
  shows "[]\<notin>set (square_ro_opening_trace_words tbs)"
    "[]\<notin>set (square_ro_opening_composition_words as cbs)"
proof -
  have positive: "0<(65536::nat) div 2^j" if "j\<le>10" for j
  proof -
    have pow: "(2::nat)^j\<le>1024"
      using power_increasing[OF that, of "2::nat"] by simp
    have "(2::nat)^j\<le>65536" using pow by arith
    then show ?thesis by (simp add: div_greater_zero_iff)
  qed
  show "[]\<notin>set (square_ro_opening_trace_words tbs)"
    using positive tb
    by (auto simp: square_ro_opening_trace_words_def square_ro_trace_layer_def
      square_ro_fold_domain_exact_length s.eval_domain_def s.H_def
      dest!: arg_cong[where f=length]) (metis positive less_imp_le not_less_zero)
  show "[]\<notin>set (square_ro_opening_composition_words as cbs)"
    using positive cb square_ro_composition_depth_bound[OF endpoint, of as]
    by (auto simp: square_ro_opening_composition_words_def square_ro_composition_layer_def
      square_ro_fold_domain_exact_length s.eval_domain_def s.H_def
      dest!: arg_cong[where f=length]) (metis positive le_trans less_imp_le not_less_zero)
qed

lemma square_ro_trace_chain_authenticated:
  assumes out: "Some ((rs,bs'),v)\<in>set_dist
    (execute (s.ro_staged_trace_fri_program (square_ro_commitment_callbacks a z) i n bs) u)"
  shows "u\<le>v \<and> (\<exists>cs. bs'=bs@cs \<and> length cs=n \<and> length rs=n \<and>
    (\<forall>j<n. \<exists>tree. protocol_created_tree (square_ro_trace_layer a (bs@take j cs)) tree v
      \<and> value tree=rs!j))"
  using out
proof (induction n arbitrary: i bs u rs bs' v)
  case 0
  then show ?case by (simp add: s.hash_ext_refl)
next
  case (Suc n)
  obtain tree s1 s2 b s3 rest where
    rout: "Some (tree,s1)\<in>set_dist (execute (protocol_create (square_ro_trace_layer a bs)) u)"
    and rec: "Some ((),s2)\<in>set_dist (execute (s.ro_record_staged_message (value tree)) s1)"
    and recv: "Some (b,s3)\<in>set_dist (execute s.receive_trace_fri_challenge s2)"
    and tail: "Some ((rest,bs'),v)\<in>set_dist
      (execute (s.ro_staged_trace_fri_program (square_ro_commitment_callbacks a z)
        (Suc i) n (bs@[b])) s3)"
    and rs: "rs=value tree#rest"
    using Suc.prems
    by (auto simp: square_ro_commitment_callbacks_def square_ro_header_callbacks_def
      square_ro_trace_root_def elim!: s.set_dist_bindE split: prod.splits)
  note root=protocol_create_outcome[OF rout]
  note rec_props=s.ro_record_staged_message_absorb_lookup_state[OF rec]
  note recv_props=s.receive_trace_fri_challenge_outcome[OF recv]
  obtain cs where rest_ext: "s3\<le>v" and bs': "bs'=(bs@[b])@cs"
    and lengths: "length cs=n" "length rest=n"
    and auth: "\<forall>j<n. \<exists>tree. protocol_created_tree
      (square_ro_trace_layer a ((bs@[b])@take j cs)) tree v \<and> value tree=rest!j"
    using Suc.IH[OF tail] by blast
  have s1v: "s1\<le>v" using rec_props recv_props rest_ext by (meson s.hash_ext_trans)
  have first: "protocol_created_tree (square_ro_trace_layer a bs) tree v"
    using root protocol_created_tree_mono[OF _ s1v] by blast
  have all: "\<forall>j<Suc n. \<exists>tree. protocol_created_tree
    (square_ro_trace_layer a (bs@take j (b#cs))) tree v \<and> value tree=rs!j"
  proof (intro allI impI)
    fix j assume j: "j<Suc n"
    show "\<exists>tree. protocol_created_tree
      (square_ro_trace_layer a (bs@take j (b#cs))) tree v \<and> value tree=rs!j"
      using j first auth by (cases j) (auto simp: rs)
  qed
  have uv: "u\<le>v" using root s1v by (meson s.hash_ext_trans)
  show ?case
    apply (intro conjI[OF uv] exI[of _ "b#cs"])
    using bs' lengths rs all by simp
qed

lemma square_ro_header_authenticated:
  assumes out: "Some ((fr,trs,tbs,tf,as),v)\<in>set_dist
    (execute (s.ro_header_prefix (square_ro_commitment_callbacks a z)) u)"
  shows "u\<le>v \<and> length trs=10 \<and> length tbs=10 \<and>
    (\<exists>tree. protocol_created_tree (square_ro_trace_layer a []) tree v \<and> value tree=fr) \<and>
    (\<forall>j<10. \<exists>tree. protocol_created_tree (square_ro_trace_layer a (take j tbs)) tree v
      \<and> value tree=trs!j)"
proof -
  have depth: "ceil_log (1024::nat)=10" by (simp add: ceil_log_def floor_log_rec)
  obtain tree s1 s2 s3 s4 where
    base: "Some (tree,s1)\<in>set_dist (execute (protocol_create (square_ro_trace_layer a [])) u)"
    and rec: "Some ((),s2)\<in>set_dist (execute (s.ro_record_staged_message fr) s1)"
    and trace: "Some ((trs,tbs),s3)\<in>set_dist
      (execute (s.ro_staged_trace_fri_program (square_ro_commitment_callbacks a z) 0 10 []) s2)"
    and frec: "Some ((),s4)\<in>set_dist (execute (s.ro_record_staged_message tf) s3)"
    and alphas: "Some (as,v)\<in>set_dist (execute (s.ro_staged_alpha_program 3) s4)"
    and fr: "fr=value tree"
    using out unfolding s.ro_header_prefix_def
    by (auto simp: square_ro_commitment_callbacks_def square_ro_header_callbacks_def
      square_ro_trace_root_def depth
      simp del: s.ro_staged_trace_fri_program.simps
      elim!: s.set_dist_bindE split: prod.splits)
  note base_props=protocol_create_outcome[OF base]
  note rec_props=s.ro_record_staged_message_absorb_lookup_state[OF rec]
  note trace_props=square_ro_trace_chain_authenticated[OF trace]
  note frec_props=s.ro_record_staged_message_absorb_lookup_state[OF frec]
  have s4v: "s4\<le>v"
    using s.ro_staged_alpha_program_absorb_lookup_chain[OF alphas] by simp
  have s3v: "s3\<le>v" using frec_props s4v by (meson s.hash_ext_trans)
  have s1v: "s1\<le>v" using rec_props trace_props s3v by (meson s.hash_ext_trans)
  have uv: "u\<le>v" using base_props s1v by (meson s.hash_ext_trans)
  show ?thesis using uv fr base_props trace_props
    protocol_created_tree_mono[OF _ s1v] protocol_created_tree_mono[OF _ s3v]
    by (auto; blast)
qed

lemma square_ro_commitment_header_embedding:
  assumes out: "Some ((data,dg,crs,cbs,cv),v)\<in>set_dist
    (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) u)"
  shows "\<exists>h. Some (data,h)\<in>set_dist
    (execute (s.ro_header_prefix (square_ro_commitment_callbacks a z)) u) \<and> h\<le>v"
proof -
  obtain h d s1 s2 s3 where
    header: "Some (data,h)\<in>set_dist
      (execute (s.ro_header_prefix (square_ro_commitment_callbacks a z)) u)"
    and degree: "Some (dg,d)\<in>set_dist
      (execute (degree_stage (square_ro_commitment_callbacks a z) (square_ro_header_alphas data)) h)"
    and rec: "Some ((),s1)\<in>set_dist (execute (s.ro_record_staged_message dg) d)"
    and chain: "Some ((crs,cbs),s2)\<in>set_dist (execute
      (s.ro_staged_composition_fri_program (square_ro_commitment_callbacks a z) dg 0
        (ceil_log (stark_mod_ring_decode dg+1)) []) s1)"
    and final: "Some (cv,s3)\<in>set_dist
      (execute (composition_final_stage (square_ro_commitment_callbacks a z) dg cbs) s2)"
    and frec: "Some ((),v)\<in>set_dist (execute (s.ro_record_staged_message cv) s3)"
    using out unfolding s.ro_commitment_prefix_def
    by (auto simp: assert_def s.throw_no_outcome elim!: s.set_dist_bindE
      split: prod.splits if_splits)
  have hd: "h\<le>d" using s.hash_only_ro_extends[OF square_ro_commitment_hash_only(4)] degree
    unfolding s.hash_extension_preserving_def by blast
  have ds1: "d\<le>s1" using s.ro_record_staged_message_absorb_lookup_state[OF rec] by simp
  have s1s2: "s1\<le>s2"
    using s.composition_prefix_properties[OF square_ro_commitment_hash_only(5) chain] by simp
  have s2s3: "s2\<le>s3" using s.hash_only_ro_extends[OF square_ro_commitment_hash_only(6)] final
    unfolding s.hash_extension_preserving_def by blast
  have s3v: "s3\<le>v" using s.ro_record_staged_message_absorb_lookup_state[OF frec] by simp
  have "h\<le>v" using hd ds1 s1s2 s2s3 s3v by (meson s.hash_ext_trans)
  then show ?thesis using header by blast
qed

lemma square_ro_opening_body_outcome:
  assumes out: "Some (chunk,t)\<in>set_dist (execute (square_ro_opening_body tbs as cbs raw) u)"
  shows "u\<le>t \<and> (\<exists>tree tp cps.
    protocol_created_tree (square_ro_trace_layer a []) tree t \<and>
    (\<forall>j. length (get_authentication_path 65536 j tree)=16) \<and>
    map fst tp=square_ro_opening_trace_words tbs \<and>
    map fst cps=square_ro_opening_composition_words as cbs \<and>
    (\<forall>xs tr. (xs,tr)\<in>set tp \<union> set cps \<longrightarrow> protocol_created_tree xs tr t \<and>
      (xs\<noteq>[] \<longrightarrow> (\<forall>j. length (get_authentication_path (length xs) j tr)=floor_log (length xs)))) \<and>
    chunk=s.honest_query_chunk (square_ro_trace_layer a []) tree (s.index (stark_mod_ring_decode raw)) @
      List.concat (s.honest_fri_chunks tp (s.index (stark_mod_ring_decode raw))) @
      List.concat (s.honest_fri_chunks cps (s.index (stark_mod_ring_decode raw))))"
proof -
  obtain tree s1 tp s2 cps where
    base: "Some (tree,s1)\<in>set_dist (execute (protocol_create (square_ro_trace_layer a [])) u)"
    and trace: "Some (tp,s2)\<in>set_dist (execute
      (s.honest_create_trees (square_ro_opening_trace_words tbs)) s1)"
    and comp: "Some (cps,t)\<in>set_dist (execute
      (s.honest_create_trees (square_ro_opening_composition_words as cbs)) s2)"
    and chunk: "chunk=s.honest_query_chunk (square_ro_trace_layer a []) tree (s.index (stark_mod_ring_decode raw)) @
      List.concat (s.honest_fri_chunks tp (s.index (stark_mod_ring_decode raw))) @
      List.concat (s.honest_fri_chunks cps (s.index (stark_mod_ring_decode raw)))"
    using out unfolding square_ro_opening_body_def
    by (auto elim!: s.set_dist_bindE split: prod.splits)
  note b=protocol_create_outcome[OF base]
  note tp=s.honest_create_trees_outcome[OF trace]
  note cps=s.honest_create_trees_outcome[OF comp]
  have s1t: "s1\<le>t" using tp cps by (meson s.hash_ext_trans)
  have ut: "u\<le>t" using b s1t by (meson s.hash_ext_trans)
  have base_len: "length (square_ro_trace_layer a [])=65536"
    by (simp add: square_ro_trace_layer_def square_ro_fold_domain_def s.eval_domain_def s.H_def)
  have ne: "square_ro_trace_layer a []\<noteq>[]" using base_len by auto
  have paths: "length (get_authentication_path 65536 j tree)=16" for j
    using s.protocol_created_path_length[OF base ne, of j]
    by (simp add: base_len floor_log_rec)
  have bct: "protocol_created_tree (square_ro_trace_layer a []) tree t"
    using b protocol_created_tree_mono[OF _ s1t] by blast
  have tct: "protocol_created_tree xs tr t" if "(xs,tr)\<in>set tp" for xs tr
    using tp cps that protocol_created_tree_mono by blast
  show ?thesis
    apply (rule conjI[OF ut])
    apply (rule exI[of _ tree])
    apply (rule exI[of _ tp])
    apply (rule exI[of _ cps])
    using bct paths tp cps tct chunk by auto
qed

lemma square_ro_query_opening_format:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some (((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and ext: "sent\<le>u"
    and out: "Some (chunk,t)\<in>set_dist (execute (square_ro_query_opening raw) u)"
  shows "s.verifier_query_round_chunk (s.index (stark_mod_ring_decode raw)) trs crs chunk"
proof -
  have bout: "Some (chunk,t)\<in>set_dist (execute (square_ro_opening_body tbs as cbs raw) u)"
    by (rule s.wp_equality_support[OF square_ro_query_opening_reconstruction[OF prefix ext] out])
  obtain h where header: "Some ((fr,trs,tbs,tf,as),h)\<in>set_dist
    (execute (s.ro_header_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and hs: "h\<le>sent" using square_ro_commitment_header_embedding[OF prefix] by blast
  note hp=square_ro_header_authenticated[OF header]
  note cp=square_ro_commitment_prefix_outcome[OF endpoint prefix]
  have tb: "length tbs=10" and tr: "length trs=10" using hp by auto
  have cb: "length cbs=ceil_log (stark_mod_ring_decode
    (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)"
    and cr: "length crs=length cbs" using cp by auto
  obtain tree tp cps where
    base: "\<forall>j. length (get_authentication_path 65536 j tree)=16"
    and tw: "map fst tp=square_ro_opening_trace_words tbs"
    and cw: "map fst cps=square_ro_opening_composition_words as cbs"
    and paths: "\<forall>xs tr. (xs,tr)\<in>set tp \<union> set cps \<longrightarrow>
      protocol_created_tree xs tr t \<and> (xs\<noteq>[] \<longrightarrow>
        (\<forall>j. length (get_authentication_path (length xs) j tr)=floor_log (length xs)))"
    and chunk: "chunk=s.honest_query_chunk (square_ro_trace_layer a []) tree (s.index (stark_mod_ring_decode raw)) @
      List.concat (s.honest_fri_chunks tp (s.index (stark_mod_ring_decode raw))) @
      List.concat (s.honest_fri_chunks cps (s.index (stark_mod_ring_decode raw)))"
    using square_ro_opening_body_outcome[OF bout] by blast
  have len: "length (square_ro_trace_layer a [])=1024*64"
    by (simp add: square_ro_trace_layer_def square_ro_fold_domain_def s.eval_domain_def s.H_def)
  have bp: "length (get_authentication_path (length (square_ro_trace_layer a [])) j tree)=
    floor_log (length (square_ro_trace_layer a []))" for j
    using base by (simp add: len floor_log_rec)
  have tl: "map (length \<circ> fst) tp=s.fri_layer_lengths (length trs) (1024*64)"
    using square_ro_opening_word_lengths(1)[OF tb cb] tw tr by (simp flip: list.map_comp)
  have cl: "map (length \<circ> fst) cps=s.fri_layer_lengths (length crs) (1024*64)"
    using square_ro_opening_word_lengths(2)[OF tb cb] cw cr by (simp flip: list.map_comp)
  have tne: "xs\<noteq>[]" if "(xs,tr)\<in>set tp" for xs tr
    using square_ro_opening_word_nonempty(1)[OF endpoint tb cb] tw that by (metis fst_conv image_eqI list.set_map)
  have cne: "xs\<noteq>[]" if "(xs,tr)\<in>set cps" for xs tr
    using square_ro_opening_word_nonempty(2)[OF endpoint tb cb] cw that by (metis fst_conv image_eqI list.set_map)
  show ?thesis unfolding chunk
    by (rule s.honest_round_chunk_format[OF len bp tl cl])
      (use paths tne cne in auto)
qed

lemma square_ro_query_opening_authenticated_trees:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some (((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and ext: "sent\<le>u"
    and out: "Some (chunk,t)\<in>set_dist (execute (square_ro_query_opening raw) u)"
  shows "u\<le>t \<and> (\<exists>tree tp cps.
    protocol_created_tree (square_ro_trace_layer a []) tree t \<and> value tree=fr \<and>
    map fst tp=square_ro_opening_trace_words tbs \<and> map (value \<circ> snd) tp=trs \<and>
    map fst cps=square_ro_opening_composition_words as cbs \<and> map (value \<circ> snd) cps=crs \<and>
    (\<forall>xs tr. (xs,tr)\<in>set tp \<union> set cps \<longrightarrow> protocol_created_tree xs tr t) \<and>
    chunk=s.honest_query_chunk (square_ro_trace_layer a []) tree (s.index (stark_mod_ring_decode raw)) @
      List.concat (s.honest_fri_chunks tp (s.index (stark_mod_ring_decode raw))) @
      List.concat (s.honest_fri_chunks cps (s.index (stark_mod_ring_decode raw))))"
proof -
  have bout: "Some (chunk,t)\<in>set_dist (execute (square_ro_opening_body tbs as cbs raw) u)"
    by (rule s.wp_equality_support[OF square_ro_query_opening_reconstruction[OF prefix ext] out])
  obtain tree tp cps where ut: "u\<le>t"
    and base: "protocol_created_tree (square_ro_trace_layer a []) tree t"
    and tw: "map fst tp=square_ro_opening_trace_words tbs"
    and cw: "map fst cps=square_ro_opening_composition_words as cbs"
    and built: "\<forall>xs tr. (xs,tr)\<in>set tp \<union> set cps \<longrightarrow> protocol_created_tree xs tr t"
    and chunk: "chunk=s.honest_query_chunk (square_ro_trace_layer a []) tree (s.index (stark_mod_ring_decode raw)) @
      List.concat (s.honest_fri_chunks tp (s.index (stark_mod_ring_decode raw))) @
      List.concat (s.honest_fri_chunks cps (s.index (stark_mod_ring_decode raw)))"
    using square_ro_opening_body_outcome[OF bout] by blast
  have st: "sent\<le>t" by (rule s.hash_ext_trans[OF ext ut])
  obtain h where header: "Some ((fr,trs,tbs,tf,as),h)\<in>set_dist
    (execute (s.ro_header_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and hs: "h\<le>sent" using square_ro_commitment_header_embedding[OF prefix] by blast
  have ht: "h\<le>t" by (rule s.hash_ext_trans[OF hs st])
  note hp=square_ro_header_authenticated[OF header]
  note cp=square_ro_commitment_prefix_outcome[OF endpoint prefix]
  obtain original where oct: "protocol_created_tree (square_ro_trace_layer a []) original h"
    and root: "value original=fr" using hp by blast
  have oct': "protocol_created_tree (square_ro_trace_layer a []) original t"
    by (rule protocol_created_tree_mono[OF oct ht])
  have fr: "value tree=fr" using protocol_created_tree_unique[OF base oct'] root by simp
  have tl: "length trs=length (square_ro_opening_trace_words tbs)"
    using hp by (simp add: square_ro_opening_trace_words_def)
  have cl: "length crs=length (square_ro_opening_composition_words as cbs)"
    using cp by (simp add: square_ro_opening_composition_words_def)
  have tcommitted: "\<exists>tr. protocol_created_tree (square_ro_opening_trace_words tbs!j) tr t \<and>
    value tr=trs!j" if j: "j<length trs" for j
  proof -
    have j10: "j<10" using hp j by simp
    obtain tr where ct: "protocol_created_tree (square_ro_trace_layer a (take j tbs)) tr h"
      and r: "value tr=trs!j" using hp j10 by blast
    show ?thesis using protocol_created_tree_mono[OF ct ht] r j10
      by (auto simp: square_ro_opening_trace_words_def)
  qed
  have ccommitted: "\<exists>tr. protocol_created_tree (square_ro_opening_composition_words as cbs!j) tr t \<and>
    value tr=crs!j" if j: "j<length crs" for j
  proof -
    obtain tr where ct: "protocol_created_tree (square_ro_composition_layer a z as (take j cbs)) tr sent"
      and r: "value tr=crs!j" using cp j by blast
    have jn: "j<ceil_log (stark_mod_ring_decode
      (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)" using cp j by simp
    show ?thesis using protocol_created_tree_mono[OF ct st] r jn
      by (auto simp: square_ro_opening_composition_words_def)
  qed
  have tr: "map (value \<circ> snd) tp=trs"
    by (rule s.honest_trees_match_roots[OF tw tl tcommitted]) (use built in auto)
  have cr: "map (value \<circ> snd) cps=crs"
    by (rule s.honest_trees_match_roots[OF cw cl ccommitted]) (use built in auto)
  show ?thesis
    apply (rule conjI[OF ut])
    apply (rule exI[of _ tree])
    apply (rule exI[of _ tp])
    apply (rule exI[of _ cps])
    using base fr tw cw built chunk tr cr by blast
qed

definition square_ro_honest_callbacks :: "field_192 staged_adversary" where
  "square_ro_honest_callbacks = (square_ro_commitment_callbacks a z)\<lparr>
    query_opening_stage := (\<lambda>i raw. square_ro_query_opening raw)\<rparr>"

lemma square_ro_honest_commitment_unchanged:
  "s.ro_commitment_prefix square_ro_honest_callbacks =
    s.ro_commitment_prefix (square_ro_commitment_callbacks a z)"
  by (simp add: square_ro_honest_callbacks_def s.ro_commitment_prefix_query_update)

lemma square_ro_honest_queries_no_failure:
  assumes endpoint: "z=a^(2^1023)"
    and prefix: "Some (((fr,trs,tbs,tf,as),dg,crs,cbs,cv),sent)\<in>set_dist
      (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
    and ext: "sent\<le>u"
  shows "None\<notin>dom (dist (execute
    (s.ro_checked_staged_query_program square_ro_honest_callbacks trs crs i n) u))"
proof (rule s.ro_checked_queries_no_failure[OF _ _ ext])
  fix i raw s1
  show "None\<notin>dom (dist (execute (query_opening_stage square_ro_honest_callbacks i raw) s1))"
    by (simp add: square_ro_honest_callbacks_def square_ro_query_opening_no_failure[OF endpoint])
next
  fix i raw s1 chunk s2
  assume ext1: "sent\<le>s1"
    and op: "Some (chunk,s2)\<in>set_dist (execute (query_opening_stage square_ro_honest_callbacks i raw) s1)"
  have op': "Some (chunk,s2)\<in>set_dist (execute (square_ro_query_opening raw) s1)"
    using op by (simp add: square_ro_honest_callbacks_def)
  have form: "s.verifier_query_round_chunk (s.index (stark_mod_ring_decode raw)) trs crs chunk"
    by (rule square_ro_query_opening_format[OF endpoint prefix ext1 op'])
  have extension: "s1\<le>s2"
    using s.hash_only_ro_extends[OF square_ro_query_opening_hash_only[OF endpoint]] op'
    unfolding s.hash_extension_preserving_def by blast
  show "s.verifier_query_round_chunk (s.index (stark_mod_ring_decode raw)) trs crs chunk \<and> s1\<le>s2"
    using form extension by simp
qed

lemma square_ro_honest_checked_builder_no_failure:
  assumes endpoint: "z=a^(2^1023)"
  shows "None\<notin>dom (dist (execute
    (s.ro_checked_staged_transcript_program square_ro_honest_callbacks) s.adversary_initial_state))"
  unfolding s.ro_commitment_prefix_decomposition square_ro_honest_commitment_unchanged
proof (rule no_failure_bindI[OF square_ro_commitment_no_failure[OF endpoint]])
  fix data sent
  assume prefix: "Some (data,sent)\<in>set_dist
    (execute (s.ro_commitment_prefix (square_ro_commitment_callbacks a z)) s.adversary_initial_state)"
  obtain fr trs tbs tf as dg crs cbs cv where data: "data=((fr,trs,tbs,tf,as),dg,crs,cbs,cv)"
    by (cases data) auto
  show "None\<notin>dom (dist (execute (s.ro_after_commitment_prefix square_ro_honest_callbacks data) sent))"
    unfolding data s.ro_after_commitment_prefix_def prod.case
    by (rule no_failure_bindI[OF square_ro_honest_queries_no_failure[OF
      endpoint prefix[unfolded data] s.hash_ext_refl]]) simp
qed

lemma square_ro_sampled_positions:
  "s.index (stark_mod_ring_decode raw)<65472"
  "i\<in>set (s.powers_scaled (s.index (stark_mod_ring_decode raw))) \<Longrightarrow> i<65536"
proof -
  have max: "Max (set [0..<2])=(1::nat)" by (simp add: numeral_2_eq_2)
  show "s.index (stark_mod_ring_decode raw)<65472"
    using s.index_less_query_sample_space[of "stark_mod_ring_decode raw"]
    by (simp only: s.query_sample_space_size_def max)
  have mem: "s.index (stark_mod_ring_decode raw)\<in>s.query_sample_space"
    using s.index_less_query_sample_space[of "stark_mod_ring_decode raw"]
    by (simp add: s.query_sample_space_def)
  show "i\<in>set (s.powers_scaled (s.index (stark_mod_ring_decode raw))) \<Longrightarrow> i<65536"
    using s.query_sample_space_powers_scaled_bound[OF mem, of i] by simp
qed

lemma square_ro_opening_layer_power_lengths:
  assumes tb: "length tbs=10" and tj: "j<10"
  shows "length (square_ro_trace_layer a (take j tbs))=(2::nat)^(16-j)"
  using power_diff[of "2::nat" j 16] tb tj
  by (simp add: square_ro_trace_layer_def square_ro_fold_domain_exact_length
    s.eval_domain_def s.H_def)

lemma square_ro_opening_composition_power_lengths:
  assumes endpoint: "z=a^(2^1023)"
    and cb: "length cbs=ceil_log (stark_mod_ring_decode
      (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)"
    and j: "j<length cbs"
  shows "length (square_ro_composition_layer a z as (take j cbs))=(2::nat)^(16-j)"
proof -
  have j16: "j\<le>16" using j cb square_ro_composition_depth_bound[OF endpoint, of as] by arith
  show ?thesis using power_diff[of "2::nat" j 16] j j16
    by (simp add: square_ro_composition_layer_def square_ro_fold_domain_exact_length
      s.eval_domain_def s.H_def)
qed

end

ML \<open>
  fun check_square_openings n th =
    if null (Thm.hyps_of th) andalso Thm.nprems_of th = n
       andalso null (Thm_Deps.all_oracles [th])
    then writeln (Thm.string_of_thm_global @{theory} th)
    else error "Unexpected honest opening dependency";
  val _ = List.app (check_square_openings 0)
    @{thms square_ro_commitment_hash_only square_ro_honest_commitment_unchanged
      square_ro_sampled_positions(1)};
  val _ = List.app (check_square_openings 1)
    @{thms square_ro_committed_data_hash_only square_ro_opening_body_hash_only
      square_ro_query_opening_hash_only square_ro_query_opening_controlled
      square_ro_query_opening_no_failure square_ro_trace_chain_authenticated
      square_ro_header_authenticated square_ro_commitment_header_embedding
      square_ro_opening_body_outcome square_ro_honest_checked_builder_no_failure
      square_ro_sampled_positions(2)};
  val _ = List.app (check_square_openings 2)
    @{thms square_ro_committed_data_reconstruction square_ro_query_opening_reconstruction
      square_ro_opening_word_lengths square_ro_opening_layer_power_lengths};
  val _ = List.app (check_square_openings 3)
    @{thms square_ro_opening_word_nonempty square_ro_honest_queries_no_failure
      square_ro_opening_composition_power_lengths};
  val _ = List.app (check_square_openings 4)
    @{thms square_ro_query_opening_format square_ro_query_opening_authenticated_trees};
\<close>

end
