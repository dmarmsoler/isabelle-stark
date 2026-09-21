(*  License: BSD-3-Clause *)
theory Square_Sequence_192_RO_Composition
  imports RO_Honest_Composition_Reconstruction Square_Sequence_192_RO_Header
begin

section \<open>Honest composition commitments through the terminal layer\<close>

text \<open>Extend the header producer with every actual composition root and the
  terminal scalar. The callbacks recover alphas by hash-only header replay
  and fold using only the supplied preceding challenges. Actual encoded
  degree determines the depth, including zero; no challenges are excluded.
  Query openings remain the explicit failure callback. The conclusions are
  commitment-prefix completeness and authentication, not full RO acceptance
  or fit to the concrete adversarial allowance.\<close>

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


definition square_ro_composition_layer where
  "square_ro_composition_layer as bs =
    map (poly (square_ro_fold_poly (s.cp as p.f_powers) bs))
      (square_ro_fold_domain s.eval_domain bs)"

lemma square_ro_composition_layer_base:
  "square_ro_composition_layer as [] = p.cp_eval as"
  by (simp add: square_ro_composition_layer_def square_ro_fold_poly_def
    square_ro_fold_domain_def p.cp_eval_def)

lemma square_ro_composition_layer_step:
  "p.next_fri_layer (square_ro_fold_poly (s.cp as p.f_powers) bs)
      (square_ro_fold_domain s.eval_domain bs) b =
    (square_ro_fold_poly (s.cp as p.f_powers) (bs@[b]),
     square_ro_fold_domain s.eval_domain (bs@[b]), square_ro_composition_layer as (bs@[b]))"
  by (simp add: p.next_fri_layer_def square_ro_fold_poly_def
    square_ro_fold_domain_def square_ro_composition_layer_def Let_def)

lemma square_ro_composition_layer_length:
  "length (square_ro_composition_layer as bs) \<le> 65536"
  using square_ro_fold_domain_length[of "s.eval_domain" bs]
  by (simp add: square_ro_composition_layer_def s.eval_domain_def s.H_def)

definition square_ro_composition_root where
  "square_ro_composition_root bs =
    (s.shadow_header (square_ro_header_callbacks a z) 0 \<bind> (\<lambda>data.
     protocol_create (square_ro_composition_layer (square_ro_header_alphas data) bs) \<bind> (\<lambda>tree.
     return (value tree))))"

definition square_ro_composition_final where
  "square_ro_composition_final bs =
    (s.shadow_header (square_ro_header_callbacks a z) 0 \<bind> (\<lambda>data.
     return (hd (square_ro_composition_layer (square_ro_header_alphas data) bs))))"

definition square_ro_commitment_callbacks :: "field_192 staged_adversary"
where
  "square_ro_commitment_callbacks = (square_ro_header_callbacks a z)\<lparr>
    composition_fri_root_stage := (\<lambda>dg i bs. square_ro_composition_root bs),
    composition_final_stage := (\<lambda>dg bs. square_ro_composition_final bs)\<rparr>"

lemma square_ro_commitment_header:
  "s.ro_header_prefix square_ro_commitment_callbacks =
    s.ro_header_prefix (square_ro_header_callbacks a z)"
  by (rule s.ro_header_prefix_cong)
    (simp_all add: square_ro_commitment_callbacks_def)

lemma square_ro_composition_root_hash_only:
  "s.hash_only_ro 1572880 (square_ro_composition_root bs)"
proof -
  have tree: "s.hash_only_ro 131071
    (protocol_create (square_ro_composition_layer as bs) \<bind> (\<lambda>tree. return (value tree)))" for as
  proof -
    have h: "s.hash_only_ro (2*length (square_ro_composition_layer as bs)-1)
      (protocol_create (square_ro_composition_layer as bs) \<bind> (\<lambda>tree. return (value tree)))"
      by (rule s.hash_only_ro_map[OF s.hash_only_ro_protocol_create])
    show ?thesis by (rule s.hash_only_ro.Bound[OF h])
      (use square_ro_composition_layer_length[of as bs] in arith)
  qed
  show ?thesis
    using s.hash_only_ro_bind[OF square_ro_header_hash_only tree]
    unfolding square_ro_composition_root_def by simp
qed

lemma square_ro_composition_final_hash_only:
  "s.hash_only_ro 1441809 (square_ro_composition_final bs)"
  unfolding square_ro_composition_final_def
  by (rule s.hash_only_ro_map[OF square_ro_header_hash_only])

lemma square_ro_fold_domain_exact_length:
  "length (square_ro_fold_domain D bs) = length D div 2^length bs"
  unfolding square_ro_fold_domain_def
proof (induction bs arbitrary: D)
  case Nil
  show ?case by simp
next
  case (Cons b bs)
  show ?case
    using Cons.IH[of "p.next_fri_domain D"]
      div_mult2_eq'[of "length D" 2 "2^length bs"]
    by (simp add: p.next_fri_domain_def)
qed

lemma square_ro_composition_terminal_degree:
  assumes endpoint: "z=a^(2^1023)"
    and depth: "length bs=ceil_log
      (stark_mod_ring_decode (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)"
  shows "degree (square_ro_fold_poly (s.cp as p.f_powers) bs)=0"
  using square_ro_fold_degree[of "s.cp as p.f_powers" bs]
    honest.div_power_two_ceil_log_Suc[of "degree (s.cp as p.f_powers)"]
    depth square_ro_degree_decodes[OF endpoint, of as]
  by simp

lemma square_ro_composition_root_reconstruction:
  assumes prefix: "Some ((fr,rs,tbs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_commitment_callbacks) s.adversary_initial_state)"
    and ext: "t \<le> u"
  shows "wp (square_ro_composition_root bs) Q u =
    wp (protocol_create (square_ro_composition_layer as bs) \<bind> (\<lambda>tree. return (value tree))) Q u"
  unfolding square_ro_composition_root_def
  using square_ro_header_reconstruction[of "(fr,rs,tbs,ffinal,as)" t a z u,
    OF _ ext] prefix
  by (simp add: wp_bind wp_return square_ro_commitment_header)

lemma square_ro_composition_final_reconstruction:
  assumes prefix: "Some ((fr,rs,tbs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_commitment_callbacks) s.adversary_initial_state)"
    and ext: "t \<le> u"
  shows "wp (square_ro_composition_final bs) Q u =
    Q (Some (hd (square_ro_composition_layer as bs),u))"
  unfolding square_ro_composition_final_def
  using square_ro_header_reconstruction[of "(fr,rs,tbs,ffinal,as)" t a z u,
    OF _ ext] prefix
  by (simp add: wp_bind wp_return square_ro_commitment_header)

lemma square_ro_composition_root_outcome:
  assumes prefix: "Some ((fr,rs,tbs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_commitment_callbacks) s.adversary_initial_state)"
    and ext: "t \<le> u"
    and out: "Some (r,v) \<in> set_dist (execute (square_ro_composition_root bs) u)"
  shows "u \<le> v \<and> (\<exists>tree. protocol_created_tree (square_ro_composition_layer as bs) tree v \<and> value tree=r)"
proof -
  have mapped: "Some (r,v) \<in> set_dist (execute
    (protocol_create (square_ro_composition_layer as bs) \<bind> (\<lambda>tree. return (value tree))) u)"
    by (rule s.wp_equality_support[OF square_ro_composition_root_reconstruction[OF prefix ext] out])
  obtain tree where root: "value tree=r" and
    tree: "Some (tree,v) \<in> set_dist (execute (protocol_create (square_ro_composition_layer as bs)) u)"
    using mapped by (auto elim!: s.set_dist_bindE)
  show ?thesis using protocol_create_outcome[OF tree] root by blast
qed

lemma square_ro_composition_final_outcome:
  assumes prefix: "Some ((fr,rs,tbs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_commitment_callbacks) s.adversary_initial_state)"
    and ext: "t \<le> u"
    and out: "Some (cv,v) \<in> set_dist (execute (square_ro_composition_final bs) u)"
  shows "cv=hd (square_ro_composition_layer as bs) \<and> v=u"
proof -
  have eq: "wp (square_ro_composition_final bs) Q u =
    wp (return (hd (square_ro_composition_layer as bs))) Q u" for Q
    using square_ro_composition_final_reconstruction[OF prefix ext, of bs Q]
    by (simp add: wp_return)
  show ?thesis using s.wp_equality_support[OF eq out] by simp
qed


lemma square_ro_composition_depth_bound:
  assumes endpoint: "z=a^(2^1023)"
  shows "ceil_log
    (stark_mod_ring_decode (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1) \<le> 10"
  using square_ro_degree_guard[OF endpoint, of as]
  by (simp add: s.maxDegree_def square_workload_max_degree ceil_log_def floor_log_rec)

lemma square_ro_composition_terminal_domain:
  assumes endpoint: "z=a^(2^1023)"
    and depth: "length bs=ceil_log
      (stark_mod_ring_decode (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)"
  shows "64 \<le> length (square_ro_composition_layer as bs)"
proof -
  have len: "length bs \<le> 10" using depth square_ro_composition_depth_bound[OF endpoint, of as] by simp
  have pow: "(2::nat)^length bs \<le> 1024"
    using power_increasing[OF len, of "2::nat"] by simp
  have "64 \<le> 65536 div (2::nat)^length bs"
    using div_le_mono2[of "(2::nat)^length bs" 1024 65536] pow by simp
  then show ?thesis
    by (simp add: square_ro_composition_layer_def square_ro_fold_domain_exact_length
      s.eval_domain_def s.H_def)
qed

lemma square_ro_composition_terminal_constant:
  assumes endpoint: "z=a^(2^1023)"
    and depth: "length bs=ceil_log
      (stark_mod_ring_decode (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)"
    and index: "i<length (square_ro_composition_layer as bs)"
  shows "square_ro_composition_layer as bs ! i =
    hd (square_ro_composition_layer as bs)"
proof -
  have deg: "degree (square_ro_fold_poly (s.cp as p.f_powers) bs)=0"
    by (rule square_ro_composition_terminal_degree[OF endpoint depth])
  have ne: "square_ro_fold_domain s.eval_domain bs \<noteq> []"
    using square_ro_composition_terminal_domain[OF endpoint depth]
    by (auto simp: square_ro_composition_layer_def)
  show ?thesis using index
    by (simp add: square_ro_composition_layer_def hd_map[OF ne]
      honest.poly_degree_zero_const[OF deg])
qed

lemma square_ro_commitment_no_failure:
  assumes endpoint: "z=a^(2^1023)"
  shows "None \<notin> dom (dist (execute
    (s.ro_commitment_prefix square_ro_commitment_callbacks) s.adversary_initial_state))"
proof -
  have roots: "s.hash_only_ro 1572880
    (composition_fri_root_stage square_ro_commitment_callbacks dg i bs)" for dg i bs
    by (simp add: square_ro_commitment_callbacks_def square_ro_composition_root_hash_only)
  have finals: "None \<notin> dom (dist (execute
    (composition_final_stage square_ro_commitment_callbacks dg bs) u))" for dg bs u
    by (simp add: square_ro_commitment_callbacks_def
      s.hash_only_ro_no_failure[OF square_ro_composition_final_hash_only])
  have dg_stage: "degree_stage square_ro_commitment_callbacks as =
    return (stark_mod_ring_encode (degree (s.cp as p.f_powers)))" for as
    by (simp add: square_ro_commitment_callbacks_def square_ro_header_callbacks_def)
  show ?thesis
    unfolding s.ro_commitment_prefix_def
    apply (rule no_failure_bindI)
     apply (simp add: square_ro_commitment_header square_ro_header_no_failure)
    apply (simp only: case_prod_unfold dg_stage sm_bind_return_left)
    apply (rule no_failure_bindI[OF s.ro_record_no_failure])
    apply (simp only: square_ro_degree_guard[OF endpoint])
    apply (rule no_failure_bindI)
     apply (simp add: assert_def)
    apply (rule no_failure_bindI[OF s.ro_composition_no_failure[OF roots]])
    apply (rule no_failure_bindI[OF finals])
    apply (rule no_failure_bindI[OF s.ro_record_no_failure])
    by simp
qed

text \<open>Uniform all-argument bounds count cached queries as queries. In particular,
  the zero-budget opening entry is the unimplemented failure callback, not
  an honest zero-budget opening algorithm.\<close>

lemma square_ro_commitment_callback_budgets:
  "s.controlled_ro_program 131071 (trace_root_stage square_ro_commitment_callbacks)"
  "s.controlled_ro_program 131071 (trace_fri_root_stage square_ro_commitment_callbacks i bs)"
  "s.controlled_ro_program 0 (trace_final_stage square_ro_commitment_callbacks bs)"
  "s.controlled_ro_program 0 (degree_stage square_ro_commitment_callbacks as)"
  "s.controlled_ro_program 1572880 (composition_fri_root_stage square_ro_commitment_callbacks dg i bs)"
  "s.controlled_ro_program 1441809 (composition_final_stage square_ro_commitment_callbacks dg bs)"
  "s.controlled_ro_program 0 (query_opening_stage square_ro_commitment_callbacks i raw)"
  using s.hash_only_ro_controlled[OF square_ro_trace_root_hash_only]
    s.hash_only_ro_controlled[OF square_ro_composition_root_hash_only]
    s.hash_only_ro_controlled[OF square_ro_composition_final_hash_only]
  by (auto simp: square_ro_commitment_callbacks_def square_ro_header_callbacks_def)


lemma square_ro_composition_chain_authenticated:
  assumes prefix: "Some ((fr,trs,tbs,tf,as),h) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_commitment_callbacks) s.adversary_initial_state)"
    and ext: "h \<le> u"
    and out: "Some ((rs,bs'),v) \<in> set_dist
      (execute (s.ro_staged_composition_fri_program square_ro_commitment_callbacks dg i n bs) u)"
  shows "u \<le> v \<and> (\<exists>cs. bs'=bs@cs \<and> length cs=n \<and> length rs=n \<and>
    (\<forall>j<n. \<exists>tree. protocol_created_tree (square_ro_composition_layer as (bs@take j cs)) tree v
      \<and> value tree=rs!j))"
  using ext out
proof (induction n arbitrary: i bs u rs bs' v)
  case 0
  then show ?case by (simp add: s.hash_ext_refl)
next
  case (Suc n)
  obtain r s1 s2 b s3 rest where
    rout: "Some (r,s1) \<in> set_dist (execute (square_ro_composition_root bs) u)"
    and rec: "Some ((),s2) \<in> set_dist (execute (s.ro_record_staged_message r) s1)"
    and recv: "Some (b,s3) \<in> set_dist (execute s.receive_composition_fri_challenge s2)"
    and tail: "Some ((rest,bs'),v) \<in> set_dist
      (execute (s.ro_staged_composition_fri_program square_ro_commitment_callbacks dg (Suc i) n (bs@[b])) s3)"
    and rs: "rs=r#rest"
    using Suc.prems(2)
    by (auto simp: square_ro_commitment_callbacks_def elim!: s.set_dist_bindE split: prod.splits)
  note root = square_ro_composition_root_outcome[OF prefix Suc.prems(1) rout]
  note rec_props = s.ro_record_staged_message_absorb_lookup_state[OF rec]
  note recv_props = s.receive_composition_fri_challenge_outcome[OF recv]
  have hs3: "h \<le> s3" using Suc.prems(1) root rec_props recv_props
    by (meson s.hash_ext_trans)
  obtain cs where rest_ext: "s3 \<le> v" and bs': "bs'=(bs@[b])@cs"
    and lengths: "length cs=n" "length rest=n"
    and auth: "\<forall>j<n. \<exists>tree. protocol_created_tree
      (square_ro_composition_layer as ((bs@[b])@take j cs)) tree v \<and> value tree=rest!j"
    using Suc.IH[OF hs3 tail] by blast
  have s1v: "s1 \<le> v" using rec_props recv_props rest_ext by (meson s.hash_ext_trans)
  have first: "\<exists>tree. protocol_created_tree (square_ro_composition_layer as bs) tree v \<and> value tree=r"
    using root protocol_created_tree_mono[OF _ s1v] by blast
  have all: "\<forall>j<Suc n. \<exists>tree. protocol_created_tree
    (square_ro_composition_layer as (bs@take j (b#cs))) tree v \<and> value tree=rs!j"
  proof (intro allI impI)
    fix j assume j: "j<Suc n"
    show "\<exists>tree. protocol_created_tree
      (square_ro_composition_layer as (bs@take j (b#cs))) tree v \<and> value tree=rs!j"
      using j first auth by (cases j) (auto simp: rs)
  qed
  have uv: "u \<le> v" using root s1v by (meson s.hash_ext_trans)
  show ?case
    apply (intro conjI[OF uv] exI[of _ "b#cs"])
    using bs' lengths rs all by simp
qed


lemma square_ro_commitment_prefix_outcome:
  assumes endpoint: "z=a^(2^1023)"
    and out: "Some (((fr,trs,tbs,tf,as),dg,rs,bs,cv),v) \<in> set_dist
      (execute (s.ro_commitment_prefix square_ro_commitment_callbacks) s.adversary_initial_state)"
  shows "dg=stark_mod_ring_encode (degree (s.cp as p.f_powers)) \<and>
    length rs=ceil_log (stark_mod_ring_decode dg+1) \<and>
    length bs=ceil_log (stark_mod_ring_decode dg+1) \<and>
    (\<forall>j<length rs. \<exists>tree.
      protocol_created_tree (square_ro_composition_layer as (take j bs)) tree v \<and> value tree=rs!j) \<and>
    64 \<le> length (square_ro_composition_layer as bs) \<and>
    degree (square_ro_fold_poly (s.cp as p.f_powers) bs)=0 \<and>
    cv=hd (square_ro_composition_layer as bs) \<and>
    (\<forall>j<length (square_ro_composition_layer as bs). square_ro_composition_layer as bs ! j=cv)"
proof -
  have degree_cb: "degree_stage square_ro_commitment_callbacks as =
    return (stark_mod_ring_encode (degree (s.cp as p.f_powers)))" for as
    by (simp add: square_ro_commitment_callbacks_def square_ro_header_callbacks_def)
  have final_cb: "composition_final_stage square_ro_commitment_callbacks dg bs =
    square_ro_composition_final bs" for dg bs
    by (simp add: square_ro_commitment_callbacks_def)
  obtain h u w w' where
    prefix: "Some ((fr,trs,tbs,tf,as),h) \<in> set_dist
      (execute (s.ro_header_prefix square_ro_commitment_callbacks) s.adversary_initial_state)"
    and drec: "Some ((),u) \<in> set_dist (execute (s.ro_record_staged_message dg) h)"
    and chain: "Some ((rs,bs),w) \<in> set_dist (execute
      (s.ro_staged_composition_fri_program square_ro_commitment_callbacks dg 0
        (ceil_log (stark_mod_ring_decode dg+1)) []) u)"
    and final: "Some (cv,w') \<in> set_dist (execute (square_ro_composition_final bs) w)"
    and frec: "Some ((),v) \<in> set_dist (execute (s.ro_record_staged_message cv) w')"
    and dg: "dg=stark_mod_ring_encode (degree (s.cp as p.f_powers))"
    using out unfolding s.ro_commitment_prefix_def
    by (auto simp: degree_cb final_cb assert_def elim!: s.set_dist_bindE split: prod.splits if_splits)
  have hu: "h \<le> u" using s.ro_record_staged_message_absorb_lookup_state[OF drec] by simp
  have chain_props: "u \<le> w \<and> length bs=ceil_log (stark_mod_ring_decode dg+1) \<and>
      length rs=ceil_log (stark_mod_ring_decode dg+1) \<and>
      (\<forall>j<length rs. \<exists>tree. protocol_created_tree
        (square_ro_composition_layer as (take j bs)) tree w \<and> value tree=rs!j)"
    using square_ro_composition_chain_authenticated[OF prefix hu chain] by auto
  have hw: "h \<le> w" using hu chain_props by (meson s.hash_ext_trans)
  have fin: "cv=hd (square_ro_composition_layer as bs) \<and> w'=w"
    by (rule square_ro_composition_final_outcome[OF prefix hw final])
  have wv: "w \<le> v"
    using s.ro_record_staged_message_absorb_lookup_state[OF frec] fin by simp
  have auth: "\<forall>j<length rs. \<exists>tree. protocol_created_tree
      (square_ro_composition_layer as (take j bs)) tree v \<and> value tree=rs!j"
    using chain_props protocol_created_tree_mono[OF _ wv] by blast
  have depth: "length bs=ceil_log
      (stark_mod_ring_decode (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)"
    using chain_props dg by simp
  show ?thesis using dg chain_props auth fin
    square_ro_composition_terminal_domain[OF endpoint depth]
    square_ro_composition_terminal_degree[OF endpoint depth]
    square_ro_composition_terminal_constant[OF endpoint depth] by auto
qed


end

ML \<open>
  fun check_square_composition n th =
    if null (Thm.hyps_of th) andalso Thm.nprems_of th = n
       andalso null (Thm_Deps.all_oracles [th])
    then writeln (Thm.string_of_thm_global @{theory} th)
    else error "Unexpected composition reconstruction dependency";
  val _ = List.app (check_square_composition 0)
    @{thms square_ro_composition_layer_base square_ro_composition_layer_step
      square_ro_composition_layer_length square_ro_commitment_header
      square_ro_composition_root_hash_only square_ro_composition_final_hash_only
      square_ro_fold_domain_exact_length square_ro_commitment_callback_budgets};
  val _ = List.app (check_square_composition 1)
    @{thms square_ro_composition_depth_bound square_ro_commitment_no_failure};
  val _ = List.app (check_square_composition 2)
    @{thms square_ro_composition_terminal_degree square_ro_composition_terminal_domain
      square_ro_composition_root_reconstruction square_ro_composition_final_reconstruction
      square_ro_commitment_prefix_outcome};
  val _ = List.app (check_square_composition 3)
    @{thms square_ro_composition_root_outcome square_ro_composition_final_outcome
      square_ro_composition_terminal_constant square_ro_composition_chain_authenticated};
\<close>
end
