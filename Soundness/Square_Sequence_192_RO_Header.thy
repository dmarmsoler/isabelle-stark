(*  License: BSD-3-Clause *)
theory Square_Sequence_192_RO_Header
  imports RO_Honest_Header_Reconstruction Square_Sequence_192_Core_Completeness
begin

section \<open>Concrete honest header in the RO-absorbing experiment\<close>

text \<open>Use the actual square interpolant, domains, folds and variable composition
  degree. All field inputs and challenge values are allowed, including zero
  and colliding hash outputs. The endpoint equation is required only for the
  honest composition degree and no-failure conclusions.
  This partial producer stops at the first composition frontier; later
  composition and opening callbacks deliberately fail. No full RO-verifier
  acceptance or fit to the concrete adversarial budget is claimed.\<close>

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


definition square_ro_fold_poly where
  "square_ro_fold_poly q bs = foldl p.next_fri_polynomial q bs"

definition square_ro_fold_domain where
  "square_ro_fold_domain D bs = foldl (\<lambda>d _. p.next_fri_domain d) D bs"

definition square_ro_trace_layer where
  "square_ro_trace_layer bs =
    map (poly (square_ro_fold_poly p.f bs)) (square_ro_fold_domain s.eval_domain bs)"

lemma square_ro_trace_layer_base:
  "square_ro_trace_layer [] = p.f_eval"
  by (simp add: square_ro_trace_layer_def square_ro_fold_poly_def
    square_ro_fold_domain_def p.f_eval_def)

lemma square_ro_trace_layer_step:
  "p.next_fri_layer (square_ro_fold_poly p.f bs)
      (square_ro_fold_domain s.eval_domain bs) b =
    (square_ro_fold_poly p.f (bs@[b]),
     square_ro_fold_domain s.eval_domain (bs@[b]), square_ro_trace_layer (bs@[b]))"
  by (simp add: p.next_fri_layer_def square_ro_fold_poly_def
    square_ro_fold_domain_def square_ro_trace_layer_def Let_def)

lemma square_ro_fold_domain_length:
  "length (square_ro_fold_domain D bs) \<le> length D"
  unfolding square_ro_fold_domain_def
proof (induction bs arbitrary: D)
  case Nil
  show ?case by simp
next
  case (Cons b bs)
  have "length (foldl (\<lambda>d _. p.next_fri_domain d) (p.next_fri_domain D) bs)
    \<le> length (p.next_fri_domain D)" by (rule Cons.IH)
  also have "... \<le> length D" by (simp add: p.next_fri_domain_def)
  finally show ?case by simp
qed

lemma square_ro_trace_layer_length:
  "length (square_ro_trace_layer bs) \<le> 65536"
  using square_ro_fold_domain_length[of "s.eval_domain" bs]
  by (simp add: square_ro_trace_layer_def s.eval_domain_def s.H_def)

definition square_ro_trace_root where
  "square_ro_trace_root bs = protocol_create (square_ro_trace_layer bs) \<bind> (\<lambda>t. return (value t))"

lemma square_ro_trace_root_hash_only:
  "s.hash_only_ro 131071 (square_ro_trace_root bs)"
proof -
  have h: "s.hash_only_ro (2*length (square_ro_trace_layer bs)-1) (square_ro_trace_root bs)"
    unfolding square_ro_trace_root_def
    by (rule s.hash_only_ro_map[OF s.hash_only_ro_protocol_create])
  show ?thesis
    by (rule s.hash_only_ro.Bound[OF h]) (use square_ro_trace_layer_length[of bs] in arith)
qed

definition square_ro_header_callbacks :: "field_192 staged_adversary"
where
  "square_ro_header_callbacks =
    \<lparr>trace_root_stage = square_ro_trace_root [],
     trace_fri_root_stage = (\<lambda>i bs. square_ro_trace_root bs),
     trace_final_stage = (\<lambda>bs. return (hd (square_ro_trace_layer bs))),
     degree_stage = (\<lambda>as. return (stark_mod_ring_encode (degree (s.cp as p.f_powers)))),
     composition_fri_root_stage = (\<lambda>dg i bs. throw),
     composition_final_stage = (\<lambda>dg bs. throw),
     query_opening_stage = (\<lambda>i raw. throw)\<rparr>"

lemma square_ro_header_controlled:
  "s.hash_only_ro 131071 (trace_root_stage square_ro_header_callbacks)"
  "s.hash_only_ro 131071 (trace_fri_root_stage square_ro_header_callbacks i bs)"
  "s.hash_only_ro 0 (trace_final_stage square_ro_header_callbacks bs)"
  by (simp_all add: square_ro_header_callbacks_def square_ro_trace_root_hash_only s.hash_only_ro.Pure)

lemma square_ro_header_reconstruction:
  assumes out: "Some (data,t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_header_callbacks) s.adversary_initial_state)"
    and ext: "t \<le> u"
  shows "wp (s.shadow_header square_ro_header_callbacks 0) Q u = Q (Some (data,u))"
  using s.shadow_header_replay[OF square_ro_header_controlled(1)
    square_ro_header_controlled(2) square_ro_header_controlled(3) out _ _ ext, of Q]
  by (simp add: s.adversary_initial_state_def)

lemma square_ro_header_no_failure:
  "None \<notin> dom (dist (execute (s.ro_header_prefix square_ro_header_callbacks) s.adversary_initial_state))"
  by (rule s.ro_header_no_failure[OF square_ro_header_controlled(1)
    square_ro_header_controlled(2) square_ro_header_controlled(3)])

lemma square_ro_fold_degree:
  "degree (square_ro_fold_poly q bs) \<le> degree q div 2^length bs"
  unfolding square_ro_fold_poly_def
proof (induction bs arbitrary: q)
  case Nil
  show ?case by simp
next
  case (Cons b bs)
  have "degree (foldl p.next_fri_polynomial (p.next_fri_polynomial q b) bs)
       \<le> degree (p.next_fri_polynomial q b) div 2^length bs" by (rule Cons.IH)
  also have "... \<le> (degree q div 2) div 2^length bs"
    by (rule div_le_mono) (rule honest.fri_degree_halves_polynomial)
  also have "... = degree q div 2^length (b#bs)"
    using div_mult2_eq'[of "degree q" 2 "2^length bs"] by simp
  finally show ?case by simp
qed

lemma square_ro_trace_terminal_degree:
  assumes "length bs=10"
  shows "degree (square_ro_fold_poly p.f bs)=0"
  using square_ro_fold_degree[of p.f bs] p.honest_interpolant_degree assms by simp

lemma square_ro_header_reconstruction_budget:
  "s.controlled_ro_program 1441809 (s.shadow_header square_ro_header_callbacks 0)"
  using s.hash_only_ro_controlled[OF s.shadow_header_hash_only[OF
    square_ro_header_controlled(1) square_ro_header_controlled(2) square_ro_header_controlled(3)], of 0]
  by (simp add: ceil_log_def floor_log_rec)

abbreviation square_ro_header_alphas where
  "square_ro_header_alphas data \<equiv> snd (snd (snd (snd data)))"

definition square_ro_first_composition_root where
  "square_ro_first_composition_root =
    (s.shadow_header square_ro_header_callbacks 0 \<bind> (\<lambda>data.
     protocol_create (p.cp_eval (square_ro_header_alphas data)) \<bind> (\<lambda>tree.
     return (value tree))))"

definition square_ro_zero_composition_final where
  "square_ro_zero_composition_final =
    (s.shadow_header square_ro_header_callbacks 0 \<bind> (\<lambda>data.
     return (hd (p.cp_eval (square_ro_header_alphas data)))))"

definition square_ro_frontier_callbacks :: "field_192 staged_adversary"
where
  "square_ro_frontier_callbacks = square_ro_header_callbacks\<lparr>
    composition_fri_root_stage := (\<lambda>dg i bs.
      if i=0 \<and> bs=[] then square_ro_first_composition_root else throw),
    composition_final_stage := (\<lambda>dg bs.
      if stark_mod_ring_decode dg=0 \<and> bs=[] then square_ro_zero_composition_final else throw)\<rparr>"

lemma square_ro_frontier_header:
  "s.ro_header_prefix square_ro_frontier_callbacks = s.ro_header_prefix square_ro_header_callbacks"
  by (rule s.ro_header_prefix_cong)
    (simp_all add: square_ro_frontier_callbacks_def)

lemma square_ro_first_composition_reconstruction:
  assumes prefix: "Some ((fr,rs,bs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_frontier_callbacks) s.adversary_initial_state)"
    and ext: "t \<le> u"
  shows "wp square_ro_first_composition_root Q u =
    wp (protocol_create (p.cp_eval as) \<bind> (\<lambda>tree. return (value tree))) Q u"
proof -
  have p: "Some ((fr,rs,bs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_header_callbacks) s.adversary_initial_state)"
    using prefix square_ro_frontier_header by simp
  have h: "wp (s.shadow_header square_ro_header_callbacks 0) F u =
    F (Some ((fr,rs,bs,ffinal,as),u))" for F
    by (rule square_ro_header_reconstruction[OF p ext])
  show ?thesis unfolding square_ro_first_composition_root_def by (simp add: wp_bind h)
qed

lemma square_ro_zero_composition_reconstruction:
  assumes prefix: "Some ((fr,rs,bs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_frontier_callbacks) s.adversary_initial_state)"
    and ext: "t \<le> u"
  shows "wp square_ro_zero_composition_final Q u =
    Q (Some (hd (p.cp_eval as),u))"
proof -
  have p: "Some ((fr,rs,bs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_header_callbacks) s.adversary_initial_state)"
    using prefix square_ro_frontier_header by simp
  have h: "wp (s.shadow_header square_ro_header_callbacks 0) F u =
    F (Some ((fr,rs,bs,ffinal,as),u))" for F
    by (rule square_ro_header_reconstruction[OF p ext])
  show ?thesis unfolding square_ro_zero_composition_final_def by (simp add: wp_bind wp_return h)
qed


lemma square_ro_header_hash_only:
  "s.hash_only_ro 1441809 (s.shadow_header square_ro_header_callbacks 0)"
  using s.shadow_header_hash_only[OF square_ro_header_controlled(1)
    square_ro_header_controlled(2) square_ro_header_controlled(3), of 0]
  by (simp add: ceil_log_def floor_log_rec)

lemma square_ro_cp_eval_length:
  "length (p.cp_eval as)=65536"
  by (simp add: p.cp_eval_def s.eval_domain_def s.H_def)

lemma square_ro_first_composition_hash_only:
  "s.hash_only_ro 1572880 square_ro_first_composition_root"
proof -
  have tree: "s.hash_only_ro 131071
    (protocol_create (p.cp_eval as) \<bind> (\<lambda>tree. return (value tree)))" for as
    using s.hash_only_ro_map[OF s.hash_only_ro_protocol_create[of "p.cp_eval as"], of "value"]
    by (simp add: square_ro_cp_eval_length)
  show ?thesis
    using s.hash_only_ro_bind[OF square_ro_header_hash_only tree]
    unfolding square_ro_first_composition_root_def by simp
qed

lemma square_ro_zero_composition_hash_only:
  "s.hash_only_ro 1441809 square_ro_zero_composition_final"
  unfolding square_ro_zero_composition_final_def
  by (rule s.hash_only_ro_map[OF square_ro_header_hash_only])

lemma square_ro_degree_decodes:
  assumes "z=a^(2^1023)"
  shows "stark_mod_ring_decode (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192) =
    degree (s.cp as p.f_powers)"
  using honest.degree_message_decodes[OF
    honest.composition_degree_from_honest_trace_valid[OF square_192_honest_trace_valid[OF assms]]]
  by blast

lemma square_ro_degree_guard:
  assumes "z=a^(2^1023)"
  shows "ceil_log (stark_mod_ring_decode (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)
    \<le> ceil_log (s.maxDegree+1)"
  by (rule s.ceil_log_to_nat_degree_bound[OF
    honest.honest_degree_message_assert_hol[OF square_192_honest_trace_valid[OF assms]]])

lemma square_ro_zero_depth_iff:
  "ceil_log (stark_mod_ring_decode dg+1)=0 \<longleftrightarrow> stark_mod_ring_decode dg=0"
  by (simp add: ceil_log_def floor_log_rec)

lemma square_ro_zero_final_constant:
  assumes endpoint: "z=a^(2^1023)"
    and depth: "ceil_log (stark_mod_ring_decode (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)=0"
    and bound: "i<65536"
  shows "p.cp_eval as ! i = hd (p.cp_eval as)"
proof -
  have deg: "degree (s.cp as p.f_powers)=0"
    using depth by (auto simp: square_ro_degree_decodes[OF endpoint] ceil_log_def floor_log_rec split: if_splits)
  have ne: "s.eval_domain\<noteq>[]" by (simp add: s.eval_domain_def s.H_def)
  show ?thesis
    unfolding p.cp_eval_def
    using bound square_ro_cp_eval_length[of as]
    by (simp add: p.cp_eval_def hd_map[OF ne] honest.poly_degree_zero_const[OF deg])
qed

lemma square_ro_frontier_no_failure:
  assumes endpoint: "z=a^(2^1023)"
  shows "None \<notin> dom (dist (execute
    (s.ro_composition_frontier square_ro_frontier_callbacks) s.adversary_initial_state))"
proof -
  have branch: "None \<notin> dom (dist (execute
    (if ceil_log (stark_mod_ring_decode dg+1)=0
     then composition_final_stage square_ro_frontier_callbacks dg []
     else composition_fri_root_stage square_ro_frontier_callbacks dg 0 []) u))" for dg u
    by (cases "stark_mod_ring_decode dg=0")
      (simp_all add: square_ro_frontier_callbacks_def ceil_log_def
        s.hash_only_ro_no_failure[OF square_ro_first_composition_hash_only]
        s.hash_only_ro_no_failure[OF square_ro_zero_composition_hash_only])
  have dg_stage: "degree_stage square_ro_frontier_callbacks as =
    return (stark_mod_ring_encode (degree (s.cp as p.f_powers)))" for as
    by (simp add: square_ro_frontier_callbacks_def square_ro_header_callbacks_def)
  show ?thesis
    unfolding s.ro_composition_frontier_def
    apply (rule no_failure_bindI)
     apply (simp add: square_ro_frontier_header square_ro_header_no_failure)
    apply (simp only: case_prod_unfold dg_stage sm_bind_return_left)
    apply (rule no_failure_bindI[OF s.ro_record_no_failure])
    apply (simp only: square_ro_degree_guard[OF endpoint])
    apply (rule no_failure_bindI)
     apply (simp add: assert_def)
    apply (rule no_failure_bindI[OF branch])
    apply (rule no_failure_bindI[OF s.ro_record_no_failure])
    by simp
qed

text \<open>These deliberately coarse budgets count cached queries too, and hold
  for all callback arguments. The zero-budget opening callback is the explicit
  unimplemented failure branch, not an honest zero-budget opening procedure.\<close>

lemma square_ro_frontier_callback_budgets:
  "s.controlled_ro_program 131071 (trace_root_stage square_ro_frontier_callbacks)"
  "s.controlled_ro_program 131071 (trace_fri_root_stage square_ro_frontier_callbacks i bs)"
  "s.controlled_ro_program 0 (trace_final_stage square_ro_frontier_callbacks bs)"
  "s.controlled_ro_program 0 (degree_stage square_ro_frontier_callbacks as)"
  "s.controlled_ro_program 1572880 (composition_fri_root_stage square_ro_frontier_callbacks dg i bs)"
  "s.controlled_ro_program 1441809 (composition_final_stage square_ro_frontier_callbacks dg bs)"
  "s.controlled_ro_program 0 (query_opening_stage square_ro_frontier_callbacks i raw)"
  using s.hash_only_ro_controlled[OF square_ro_trace_root_hash_only]
    s.hash_only_ro_controlled[OF square_ro_first_composition_hash_only]
    s.hash_only_ro_controlled[OF square_ro_zero_composition_hash_only]
  by (auto simp: square_ro_frontier_callbacks_def square_ro_header_callbacks_def
    intro: s.controlled_ro_program.Weaken)


lemma square_ro_actual_header_lengths:
  assumes prefix: "Some ((fr,rs,bs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_frontier_callbacks) s.adversary_initial_state)"
  shows "length bs=10 \<and> length as=3 \<and> degree (square_ro_fold_poly p.f bs)=0"
proof -
  have h: "Some ((fr,rs,bs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_header_callbacks) s.adversary_initial_state)"
    using prefix square_ro_frontier_header by simp
  have lengths: "length bs=10 \<and> length as=3"
    using s.ro_header_output_lengths[OF square_ro_header_controlled(2) h]
    by (simp add: ceil_log_def floor_log_rec)
  show ?thesis using lengths square_ro_trace_terminal_degree by blast
qed

lemma square_ro_first_composition_after_degree:
  assumes prefix: "Some ((fr,rs,bs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_frontier_callbacks) s.adversary_initial_state)"
    and rec: "Some ((),u) \<in> set_dist (execute (s.ro_record_staged_message dg) t)"
  shows "wp (composition_fri_root_stage square_ro_frontier_callbacks dg 0 []) Q u =
    wp (protocol_create (p.cp_eval as) \<bind> (\<lambda>tree. return (value tree))) Q u"
  using square_ro_first_composition_reconstruction[OF prefix, of u Q]
    s.ro_record_staged_message_absorb_lookup_state[OF rec]
  by (simp add: square_ro_frontier_callbacks_def)

lemma square_ro_first_composition_authenticated:
  assumes prefix: "Some ((fr,rs,bs,ffinal,as),t) \<in> set_dist
    (execute (s.ro_header_prefix square_ro_frontier_callbacks) s.adversary_initial_state)"
    and ext: "t \<le> u"
  shows "wp_event square_ro_first_composition_root
    (\<lambda>out. case out of None \<Rightarrow> False | Some (r,v) \<Rightarrow>
      u \<le> v \<and> (\<exists>tree. protocol_created_tree (p.cp_eval as) tree v \<and> value tree=r)) u = 1"
proof -
  have nf: "None \<notin> dom (dist (execute (protocol_create (p.cp_eval as)) u))"
    by (rule s.hash_only_ro_no_failure[OF s.hash_only_ro_protocol_create])
  show ?thesis
    unfolding wp_event_def
    apply (subst square_ro_first_composition_reconstruction[OF prefix ext])
    apply (simp only: wp_bind wp_return)
    unfolding wp_def
    apply (rule dist_expect_eq_1)
    subgoal for out
    proof -
      assume member: "out \<in> dom (dist (execute (protocol_create (p.cp_eval as)) u))"
      obtain tree v where out: "out=Some (tree,v)"
        using member nf by (cases out) auto
      have support: "Some (tree,v) \<in> set_dist (execute (protocol_create (p.cp_eval as)) u)"
        using member out by (simp add: set_dist_def)
      have good: "u \<le> v \<and> protocol_created_tree (p.cp_eval as) tree v"
        by (rule protocol_create_outcome[OF support])
      show ?thesis using out good by auto
    qed
    done
qed


end

ML \<open>
  fun check_square_header n th =
    if null (Thm.hyps_of th) andalso Thm.nprems_of th = n
       andalso null (Thm_Deps.all_oracles [th])
    then writeln (Thm.string_of_thm_global @{theory} th)
    else error "Unexpected honest header dependency";
  val _ = List.app (check_square_header 0)
    @{thms square_ro_header_no_failure square_ro_header_reconstruction_budget
      square_ro_frontier_callback_budgets};
  val _ = List.app (check_square_header 1)
    @{thms square_ro_frontier_no_failure square_ro_actual_header_lengths
      square_ro_degree_decodes square_ro_degree_guard};
  val _ = List.app (check_square_header 2)
    @{thms square_ro_header_reconstruction square_ro_first_composition_reconstruction
      square_ro_zero_composition_reconstruction square_ro_first_composition_after_degree
      square_ro_first_composition_authenticated};
  val _ = check_square_header 3 @{thm square_ro_zero_final_constant};
\<close>

end
