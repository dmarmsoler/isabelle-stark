(* Title: Stark/Soundness_FRI_Weighted_Challenge_Portfolio.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Challenge_Portfolio
  imports
    "Soundness_FRI_Weighted_Challenge_Completion"
begin

section \<open>Challenge Portfolio for weighted MCA soundness\<close>

text \<open>Recover completed challenge vectors, transport canonical headers and sum adaptive trace/composition family scores with one shared connection count.\<close>

subsection \<open>Challenge Vector Recovery\<close>

lemma cvr_avg_resolved:
 "map C ks=map Some bs \<Longrightarrow> lca_avg ks C f=f bs"
proof (induction ks arbitrary: bs f)
 case Nil then show ?case by simp
next
 case (Cons k ks)
 then obtain b cs where bs: "bs=b#cs" and head: "C k=Some b"
   and tail: "map C ks=map Some cs" by (cases bs) auto
 show ?case by (simp only: bs lca_avg.simps head option.case Cons.IH[OF tail])
qed

context soundness
begin

definition cvr_evidence where
 "cvr_evidence M data \<longleftrightarrow>
   ro_conditioned_trace_challenge_evidence M (staged_trace_root data)
     (staged_trace_fri_roots data) (staged_trace_fri_challenges data) \<and>
   ro_conditioned_composition_challenge_evidence M (staged_trace_root data)
     (staged_trace_fri_roots data) (staged_trace_final data) (staged_alphas data)
     (staged_degree data) (staged_composition_fri_roots data)
     (staged_composition_fri_challenges data)"

lemma cvr_trace_lookup:
 assumes ev: "ro_conditioned_trace_challenge_evidence M (staged_trace_root data)
     (staged_trace_fri_roots data) (staged_trace_fri_challenges data)"
 shows "map (fmlookup M) (lck_trace_keys M data)=map Some (staged_trace_fri_challenges data)"
proof (rule nth_equalityI)
 show "length (map (fmlookup M) (lck_trace_keys M data))=
   length (map Some (staged_trace_fri_challenges data))"
   using ev by (simp add: lck_trace_keys_def ro_conditioned_trace_challenge_evidence_def)
 fix i assume i: "i<length (map (fmlookup M) (lck_trace_keys M data))"
 have bound: "i<length(staged_trace_fri_roots data)" using i by (simp add: lck_trace_keys_def)
 obtain v where chain: "ro_absorb_lookup_chain (channel_for_hash_map M)
    (PState adversary_initial_state)
    (staged_trace_root data#take(Suc i)(staged_trace_fri_roots data)) v"
   and lookup: "fmlookup M (TraceFriChallenge i v)=Some(staged_trace_fri_challenges data!i)"
   using ev bound unfolding ro_conditioned_trace_challenge_evidence_def by blast
 show "map (fmlookup M) (lck_trace_keys M data)!i=map Some(staged_trace_fri_challenges data)!i"
   using ev bound lookup lck_endpoint_eq[OF chain]
   by (simp add: lck_trace_keys_def ro_conditioned_trace_challenge_evidence_def)
qed

lemma cvr_composition_lookup:
 assumes ev: "ro_conditioned_composition_challenge_evidence M (staged_trace_root data)
     (staged_trace_fri_roots data) (staged_trace_final data) (staged_alphas data)
     (staged_degree data) (staged_composition_fri_roots data)
     (staged_composition_fri_challenges data)"
 shows "map (fmlookup M) (lck_composition_keys M data)=map Some(staged_composition_fri_challenges data)"
proof (rule nth_equalityI)
 show "length (map (fmlookup M) (lck_composition_keys M data))=
   length (map Some (staged_composition_fri_challenges data))"
   using ev by (simp add: lck_composition_keys_def ro_conditioned_composition_challenge_evidence_def)
 fix i assume i: "i<length (map (fmlookup M) (lck_composition_keys M data))"
 have bound: "i<length(staged_composition_fri_roots data)" using i by (simp add: lck_composition_keys_def)
 obtain v where chain: "ro_absorb_lookup_chain (channel_for_hash_map M)
    (PState adversary_initial_state) (composition_fri_challenge_prefix_messages
      (staged_trace_root data) (staged_trace_fri_roots data) (staged_trace_final data)
      (staged_alphas data) (staged_degree data) (staged_composition_fri_roots data) i) v"
   and lookup: "fmlookup M (CompositionFriChallenge i v)=Some(staged_composition_fri_challenges data!i)"
   using ev bound unfolding ro_conditioned_composition_challenge_evidence_def by blast
 show "map (fmlookup M) (lck_composition_keys M data)!i=map Some(staged_composition_fri_challenges data)!i"
   using ev bound lookup lck_endpoint_eq[OF chain]
   by (simp add: lck_composition_keys_def ro_conditioned_composition_challenge_evidence_def)
qed

lemma cvr_lookup:
 "cvr_evidence M data \<Longrightarrow>
   map (fmlookup M) (lck_keys M data)=
     map Some(staged_trace_fri_challenges data@staged_composition_fri_challenges data)"
 unfolding cvr_evidence_def lck_keys_def
 by (simp add: cvr_trace_lookup cvr_composition_lookup)

lemma cvr_complete_score:
 assumes ev: "cvr_evidence U data"
 shows "lcs_score (lck_keys U data) (lcf_raw N r b prefix prefix_state M data)
    (ro_mca_weighted_fri_base r b) rt ffs cfs n j v U =
   lpd_score (query_index_raw_preimage
     (fri_mca_residual_query_indices N r b prefix prefix_state data (channel_for_hash_map M)))
       (ro_mca_weighted_fri_base r b) rt ffs cfs n j v U"
proof -
 have len: "length(staged_trace_fri_challenges data)=length(staged_trace_fri_roots data)"
   using ev by (simp add: cvr_evidence_def ro_conditioned_trace_challenge_evidence_def)
 show ?thesis unfolding lcs_score_def
   by (simp only: cvr_avg_resolved[OF cvr_lookup[OF ev]] lcf_raw_def lcf_data_actual[OF len])
qed

end

subsection \<open>Challenge Canonical Header\<close>

context soundness
begin

definition cch_fields where
 "cch_fields data=(staged_trace_root data, staged_trace_fri_roots data,
   staged_trace_final data, staged_alphas data, staged_degree data,
   staged_composition_fri_roots data, staged_composition_final data)"

lemma cch_canonical_fields:
 assumes clean: "\<not>hash_map_output_collision (channel_for_hash_map M)"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values(channel_for_hash_map M)"
   and header: "as_header M start data"
 shows "cch_fields (as_data M start)=cch_fields data"
proof -
 have chosen: "as_header M start (as_data M start)"
   by (rule as_data_header) (use header in blast)
 obtain ar br where ashape: "weighted_semantic_header_shape data"
   and bshape: "weighted_semantic_header_shape(as_data M start)"
   and a: "ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
     (weighted_semantic_header data@ar) start"
   and b: "ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
     (weighted_semantic_header(as_data M start)@br) start"
   using header chosen unfolding as_header_def by blast
 show ?thesis using ea_header_fields_at_prefix_unique[OF clean initial ashape bshape a b]
   by (simp add: cch_fields_def)
qed

lemma cch_keys_cong:
 "cch_fields a=cch_fields b \<Longrightarrow> lck_keys M a=lck_keys M b"
 unfolding cch_fields_def lck_keys_def lck_trace_keys_def lck_composition_keys_def
 by simp

lemma cch_raw_cong:
 "cch_fields a=cch_fields b \<Longrightarrow>
   lcf_raw N r is_trace prefix prefix_state M a bs =
   lcf_raw N r is_trace prefix prefix_state M b bs"
 unfolding cch_fields_def lcf_raw_def lcf_data_def fri_mca_residual_query_indices_def
 by simp

lemma cch_complete_score:
 assumes fields: "cch_fields a=cch_fields data" and ev: "cvr_evidence U data"
 shows "lcs_score (lck_keys U a) (lcf_raw N r b prefix prefix_state M a)
    (ro_mca_weighted_fri_base r b) rt ffs cfs n j v U =
   lpd_score (query_index_raw_preimage
     (fri_mca_residual_query_indices N r b prefix prefix_state data (channel_for_hash_map M)))
       (ro_mca_weighted_fri_base r b) rt ffs cfs n j v U"
proof -
 have sets: "lcf_raw N r b prefix prefix_state M a=lcf_raw N r b prefix prefix_state M data"
   by (rule ext, rule cch_raw_cong[OF fields])
 show ?thesis by (simp only: cch_keys_cong[OF fields] sets cvr_complete_score[OF ev])
qed

end

subsection \<open>Challenge Adaptive Record\<close>

context soundness
begin

definition car_family where
 "car_family N r b n j M start U =
   (let data=as_data M start in
    lcs_score (lck_keys M data)
      (lcf_raw N r b (0,[],0) (channel_for_hash_map fmempty) M data) (ro_mca_weighted_fri_base r b)
      (staged_trace_root data)
      (map (\<lambda>root. ((0::'f),root)) (staged_trace_fri_roots data))
      (map (\<lambda>root. ((0::'f),root)) (staged_composition_fri_roots data))
      n j start U)"

definition car_record where
 "car_record N r b n j e U =
   (case e of (M,key,start) \<Rightarrow>
     if as_birth 0 0 j e=None then 0
     else car_family N r b n j (fmupd key start M) start U)"

lemma car_birth_header:
 assumes born: "as_birth 0 0 j (M,key,start)\<noteq>None"
 shows "as_header (fmupd key start M) start (as_data (fmupd key start M) start)"
proof (rule as_data_header)
 show "\<exists>data. as_header (fmupd key start M) start data"
   using born unfolding as_birth_def
   by (auto simp: Let_def split: protocol_hash_input.splits if_splits)
qed

lemma car_birth_cap:
 assumes good: "\<not>fc_bad_record {} (M,key,start)"
 shows "car_record N r b n j (M,key,start) (fmupd key start M)\<le>(ro_mca_weighted_fri_base r b)^n"
proof (cases "as_birth 0 0 j (M,key,start)=None")
 case True then show ?thesis by (simp add: car_record_def)
next
 case False
 have fresh: "fmlookup M key=None" and nonquery: "\<And>k w. key\<noteq>QueryIndexChallenge k w"
   using False unfolding as_birth_def
   by (auto simp: Let_def split: protocol_hash_input.splits if_splits)
 have nohit: "start\<notin>weighted_semantic_interval_targets M"
   using good fresh by (simp add: fc_bad_record_def fc_target_def)
 let ?U="fmupd key start M"
 let ?data="as_data ?U start"
 have point: "\<And>bs. lpd_score
    (lcf_raw N r b (0,[],0) (channel_for_hash_map fmempty) ?U ?data bs)
    (ro_mca_weighted_fri_base r b) rt ffs cfs n j start ?U \<le>(ro_mca_weighted_fri_base r b)^n" for rt ffs cfs
   by (rule lpl_score_at_birth[OF lcf_mass fresh nonquery nohit])
 have cap: "car_family N r b n j ?U start ?U\<le>(ro_mca_weighted_fri_base r b)^n"
   unfolding car_family_def Let_def lcs_score_def
   by (subst lca_avg_const[symmetric, where ks="lck_keys ?U ?data" and C="fmlookup ?U"])
      (rule lca_avg_mono, rule point)
 show ?thesis by (simp only: car_record_def prod.case False if_False cap)
qed

lemma car_record_probe:
 assumes hist: "fc_history M0 hist (HashMap s)" and member: "e\<in>set hist"
 shows "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(en,t) \<Rightarrow>
    if \<not>fc_bad_record {} en \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
    then car_record N r b n j e (HashMap t) else 0) s
    \<le>car_record N r b n j e (HashMap s)"
proof (cases "as_birth 0 0 j e=None")
 case True
 show ?thesis by (rule wp_le_const_on_support)
   (use True in \<open>auto simp: car_record_def split: option.splits prod.splits\<close>)
next
 case False
 obtain M k start where e: "e=(M,k,start)" by (cases e) auto
 let ?B="fmupd k start M"
 let ?data="as_data ?B start"
 have header: "as_header ?B start ?data" by (rule car_birth_header) (use False e in simp)
 have ext: "channel_for_hash_map ?B\<le>channel_for_hash_map (HashMap s)"
   using fc_history_member[OF hist member] by (auto simp: e)
 have roots0: "causal_route_roots (staged_trace_root ?data)
      (map (\<lambda>root. ((0::'f),root)) (staged_trace_fri_roots ?data))
      (map (\<lambda>root. ((0::'f),root)) (staged_composition_fri_roots ?data))
       \<subseteq>weighted_semantic_interval_targets ?B"
   by (rule as_header_roots_targets[OF header])
 have mono: "weighted_semantic_interval_targets ?B\<subseteq>weighted_semantic_interval_targets (HashMap s)"
   using fc_target_mono[OF ext, where R="{}"] by (simp add: fc_target_def)
 have roots: "causal_route_roots (staged_trace_root ?data)
      (map (\<lambda>root. ((0::'f),root)) (staged_trace_fri_roots ?data))
      (map (\<lambda>root. ((0::'f),root)) (staged_composition_fri_roots ?data))
       \<subseteq>weighted_semantic_interval_targets (HashMap s)" using roots0 mono by blast
 show ?thesis unfolding car_record_def e prod.case
   using False[unfolded e]
   apply (simp only: if_False car_family_def Let_def)
   apply (rule lcd_stopped_probe)
      apply (rule lck_distinct)
     apply (erule lck_only_fri)
    apply (rule lcf_mass)
   by (rule roots)
qed

end

subsection \<open>Challenge Adaptive Portfolio\<close>

context soundness
begin

definition cap_cost where
 "cap_cost rT rC n=(ro_mca_weighted_fri_base rT True)^n+(ro_mca_weighted_fri_base rC False)^n"

definition cap_record_score where
 "cap_record_score N rT rC n j e U=
    car_record N rT True n j e U+car_record N rC False n j e U"

definition cap_total where
 "cap_total N rT rC n j hist U=
   sum_list(map (\<lambda>e. cap_record_score N rT rC n j e U) hist)"

lemma cap_total_append [simp]:
 "cap_total N rT rC n j (xs@ys) U=
   cap_total N rT rC n j xs U+cap_total N rT rC n j ys U"
 by (simp add: cap_total_def)

lemma cap_total_nil [simp]: "cap_total N rT rC n j [] U=0"
 by (simp add: cap_total_def)

lemma cap_total_singleton [simp]:
 "cap_total N rT rC n j [e] U=cap_record_score N rT rC n j e U"
 by (simp add: cap_total_def)

lemma cap_record_birth:
 "\<not>fc_bad_record {} (M,key,start) \<Longrightarrow>
   cap_record_score N rT rC n j (M,key,start) (fmupd key start M)\<le>cap_cost rT rC n"
 unfolding cap_record_score_def cap_cost_def by (intro add_mono car_birth_cap)

lemma cap_record_probe:
 assumes hist: "fc_history M0 hist (HashMap s)" and member: "e\<in>set hist"
 shows "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(en,t) \<Rightarrow>
    if \<not>fc_bad_record {} en \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
    then cap_record_score N rT rC n j e (HashMap t) else 0) s
    \<le>cap_record_score N rT rC n j e (HashMap s)"
proof -
 let ?P="\<lambda>r b out. case out of None \<Rightarrow> 0 | Some(en,t) \<Rightarrow>
    if \<not>fc_bad_record {} en \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
    then car_record N r b n j e (HashMap t) else 0"
 have eq: "(\<lambda>out. case out of None \<Rightarrow> 0 | Some(en,t) \<Rightarrow>
    if \<not>fc_bad_record {} en \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
    then cap_record_score N rT rC n j e (HashMap t) else 0)=
    (\<lambda>out. ?P rT True out+?P rC False out)"
   by (rule ext) (auto simp: cap_record_score_def split: option.splits prod.splits)
 show ?thesis
   apply (subst eq)
   unfolding causal_wp_add cap_record_score_def
   by (intro add_mono car_record_probe[OF hist member])
qed

lemma cap_total_probe:
  assumes hist: "fc_history M0 hist (HashMap s)"
  shows "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(en,t) \<Rightarrow>
    if \<not>fc_bad_record {} en \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
    then cap_total N rT rC n j hist (HashMap t) else 0) s
    \<le>cap_total N rT rC n j hist (HashMap s)"
proof -
  have bound: "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(en,t) \<Rightarrow>
      if \<not>fc_bad_record {} en \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
      then cap_total N rT rC n j xs (HashMap t) else 0) s
      \<le>cap_total N rT rC n j xs (HashMap s)"
    if sub: "set xs\<subseteq>set hist" for xs
    using sub
  proof (induction xs)
    case Nil
    show ?case by (rule wp_le_const_on_support)
      (auto split: option.splits prod.splits)
  next
    case (Cons e es)
    let ?P = "\<lambda>xs out. case out of None \<Rightarrow> 0 | Some(en,t) \<Rightarrow>
      if \<not>fc_bad_record {} en \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
      then cap_total N rT rC n j xs (HashMap t) else 0"
    have eq: "?P (e#es)=(\<lambda>out. ?P [e] out+?P es out)"
      by (rule ext) (auto simp: cap_total_def split: option.splits prod.splits)
    have "wp (pair_probe key) (?P (e#es)) s =
      wp (pair_probe key) (?P [e]) s+wp (pair_probe key) (?P es) s"
      unfolding eq by (rule causal_wp_add)
    also have "...\<le>cap_total N rT rC n j [e] (HashMap s)+cap_total N rT rC n j es (HashMap s)"
      unfolding cap_total_singleton
      by (rule add_mono)
        (use cap_record_probe[OF hist, of e key N rT rC n j] Cons.prems Cons.IH in auto)
    finally show ?case by (simp add: cap_total_def)
  qed
  show ?thesis by (rule bound) simp
qed


end

subsection \<open>Challenge Adaptive Logging\<close>

context soundness
begin

definition cap_live_total where
  "cap_live_total N rT rC n j M0 hist M =
    (if lpl_alive M0 hist M then cap_total N rT rC n j hist M else 0)"

lemma cap_live_probe:
  "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
      cap_live_total N rT rC n j M0 (hist@[e]) (HashMap t)) s
    \<le> cap_live_total N rT rC n j M0 hist (HashMap s)+cap_cost rT rC n"
proof -
  let ?V = "cap_live_total N rT rC n j M0"
  let ?p = "cap_cost rT rC n"
  let ?old = "\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
    if \<not>fc_bad_record {} e \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
    then cap_total N rT rC n j hist (HashMap t) else 0"
  show ?thesis
  proof (cases "lpl_alive M0 hist (HashMap s)")
    case True
    have hist: "fc_history M0 hist (HashMap s)" using True by (simp add: lpl_alive_def)
    have point: "(case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> ?V (hist@[e]) (HashMap t))
        \<le>?old out+?p"
      if mem: "out\<in>set_dist (execute (pair_probe key) s)" for out
    proof (cases out)
      case None
      then show ?thesis by simp
    next
      case (Some et)
      obtain e t where et: "et=(e,t)" by (cases et) simp
      obtain raw where e: "e=(HashMap s,key,raw)"
        and maps: "HashMap t=fmupd key raw (HashMap s)"
        using mem Some et by (auto elim: lpd_probe_state)
      show ?thesis
      proof (cases "lpl_alive M0 (hist@[e]) (HashMap t)")
        case False
        then show ?thesis by (simp add: Some et cap_live_total_def)
      next
        case alive: True
        have good: "\<not>fc_bad_record {} e"
          and clean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap t))"
          using alive by (auto simp: lpl_alive_def fc_no_bad_def)
        have birthcap: "cap_record_score N rT rC n j e (HashMap t)\<le>?p"
          using cap_record_birth[OF good[unfolded e], where N=N and rT=rT and rC=rC and n=n and j=j]
          by (simp only: e maps)
        show ?thesis using birthcap
          by (simp add: Some et cap_live_total_def alive good clean)
      qed
    qed
    have "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
        ?V (hist@[e]) (HashMap t)) s \<le>wp (pair_probe key) (\<lambda>out. ?old out+?p) s"
      by (rule wp_mono_on_support) (rule point)
    also have "...=wp (pair_probe key) ?old s+?p"
      by (simp only: causal_wp_add causal_wp_const)
    also have "...\<le>cap_total N rT rC n j hist (HashMap s)+?p"
      by (rule add_right_mono[OF cap_total_probe[OF hist]])
    finally show ?thesis by (simp add: cap_live_total_def True)
  next
    case False
    have "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
        ?V (hist@[e]) (HashMap t)) s\<le>0"
    proof (rule wp_le_const_on_support)
      fix out assume mem: "out\<in>set_dist (execute (pair_probe key) s)"
      show "(case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> ?V (hist@[e]) (HashMap t))\<le>0"
      proof (cases out)
        case None then show ?thesis by simp
      next
        case (Some et)
        obtain e t where et: "et=(e,t)" by (cases et) simp
        obtain raw where e: "e=(HashMap s,key,raw)"
          and maps: "HashMap t=fmupd key raw (HashMap s)"
          using mem Some et by (auto elim: lpd_probe_state)
        have dead: "\<not>lpl_alive M0 (hist@[e]) (HashMap t)"
          using False lpl_alive_previous[of M0 hist "HashMap s" key raw]
          by (auto simp: e maps)
        show ?thesis by (simp add: Some et cap_live_total_def dead)
      qed
    qed
    then show ?thesis by (rule order_trans) simp
  qed
qed

lemma cap_potential:
  "lp_potential (\<lambda>fuel hist M. cap_live_total N rT rC n j M0 hist M+
    nnreal fuel*cap_cost rT rC n)"
proof -
  let ?V = "cap_live_total N rT rC n j M0"
  let ?p = "cap_cost rT rC n"
  have mono: "\<And>a b hist M. a\<le>b \<Longrightarrow> ?V hist M+nnreal a*?p\<le>?V hist M+nnreal b*?p"
    by (intro add_left_mono mult_right_mono) auto
  have one: "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
      ?V (hist@[e]) (HashMap t)+nnreal fuel*?p) s
      \<le>?V hist (HashMap s)+nnreal (Suc fuel)*?p"
    for key hist s fuel
  proof -
    let ?W = "\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> ?V (hist@[e]) (HashMap t)"
    have "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
        ?V (hist@[e]) (HashMap t)+nnreal fuel*?p) s
        \<le>wp (pair_probe key) (\<lambda>out. ?W out+nnreal fuel*?p) s"
      by (rule wp_mono_on_support) (auto split: option.splits prod.splits)
    also have "...=wp (pair_probe key) ?W s+nnreal fuel*?p"
      by (simp only: causal_wp_add causal_wp_const)
    also have "...\<le>(?V hist (HashMap s)+?p)+nnreal fuel*?p"
      by (rule add_right_mono[OF cap_live_probe])
    also have "...=?V hist (HashMap s)+nnreal (Suc fuel)*?p"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis unfolding lp_potential_def using mono one by blast
qed

lemma cap_logged_total:
  assumes logged: "lp_rule q m L"
  shows "wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow>
    cap_live_total N rT rC n j (HashMap s) es (HashMap t)) s
    \<le>nnreal q*cap_cost rT rC n"
proof -
  have pot: "lp_potential (\<lambda>fuel hist M. cap_live_total N rT rC n j (HashMap s) hist M+
      nnreal fuel*cap_cost rT rC n)" by (rule cap_potential)
  note bound=lp_ruleD[OF logged pot, where n=0 and hist="[]" and s=s]
  show ?thesis using bound
    by (simp add: cap_live_total_def cong: if_cong option.case_cong prod.case_cong)
qed

end

subsection \<open>Challenge Final Family\<close>

context soundness
begin

definition cff_raw where
 "cff_raw N r b data U=query_index_raw_preimage
   (fri_mca_residual_query_indices N r b (0,[],0) (channel_for_hash_map fmempty)
      data (channel_for_hash_map U))"

definition cff_accept where
 "cff_accept N r b n j data U start =
   lpw_accept (cff_raw N r b data U)
      (lpa_route (staged_trace_root data)
        (map (\<lambda>root. ((0::'f),root)) (staged_trace_fri_roots data))
        (map (\<lambda>root. ((0::'f),root)) (staged_composition_fri_roots data)) U)
      (lpa_samples U) n j start"

lemma cff_raw_frozen:
 assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
   and nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
     (channel_for_hash_map M) (channel_for_hash_map U)"
   and header: "as_header M start data"
 shows "cff_raw N r b data U=cff_raw N r b data M"
proof -
 obtain rest where chain: "ro_absorb_lookup_chain (channel_for_hash_map M)
   (PState adversary_initial_state) (weighted_semantic_header data@rest) start"
   using header unfolding as_header_def by blast
 have messages: "set(weighted_semantic_header data)\<subseteq>transcript_absorb_message_values M"
   using ro_absorb_lookup_chain_messages_subset[OF chain] by auto
 have sub: "fri_checked_builder_merkle_targets data (channel_for_hash_map M)
   \<subseteq>weighted_semantic_interval_targets M"
   using messages unfolding fri_checked_builder_merkle_targets_def
     merkle_prefix_path_targets_def weighted_semantic_interval_targets_def
     weighted_semantic_header_def verifier_header_messages_def by auto
 have no: "\<not>hash_map_new_output_hit
     (merkle_prefix_path_targets (set(staged_trace_fri_roots data)\<union>set(staged_composition_fri_roots data))
       (channel_for_hash_map M)) (channel_for_hash_map M) (channel_for_hash_map U)"
   using hash_map_new_output_hit_subset[OF sub] nt
   unfolding fri_checked_builder_merkle_targets_def by blast
 have tn: "\<not>hash_map_new_output_hit
     (merkle_prefix_path_targets (set(staged_trace_fri_roots data)) (channel_for_hash_map M))
       (channel_for_hash_map M) (channel_for_hash_map U)"
   by (rule fri_mca_no_target_subset[OF _ no]) auto
 have cn: "\<not>hash_map_new_output_hit
     (merkle_prefix_path_targets (set(staged_composition_fri_roots data)) (channel_for_hash_map M))
       (channel_for_hash_map M) (channel_for_hash_map U)"
   by (rule fri_mca_no_target_subset[OF _ no]) auto
 show ?thesis unfolding cff_raw_def fri_mca_residual_query_indices_def
   by (simp only: fri_mca_guarded_stable[OF ext tn] fri_mca_guarded_stable[OF ext cn])
qed

lemma cff_birth_family_one:
 assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
   and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map U)"
   and nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
     (channel_for_hash_map M) (channel_for_hash_map U)"
   and header: "as_header M start data"
   and ev: "cvr_evidence U data"
   and acc: "cff_accept N r b n j data U start"
 shows "car_family N r b n j M start U=1"
proof -
 note base=as_clean_prefix[OF ext clean initial]
 have fields: "cch_fields (as_data M start)=cch_fields data"
   by (rule cch_canonical_fields[OF base header])
 have chosen: "as_header M start (as_data M start)"
   by (rule as_data_header) (use header in blast)
 have keys: "lck_keys M (as_data M start)=lck_keys U (as_data M start)"
   by (rule sym, rule lck_keys_extension[OF ext chosen])
 have frozen: "cff_raw N r b data M=cff_raw N r b data U"
   by (rule sym, rule cff_raw_frozen[OF ext nt header])
 have one: "lpd_score (cff_raw N r b data U) (ro_mca_weighted_fri_base r b) (staged_trace_root data)
        (map (\<lambda>root. ((0::'f),root)) (staged_trace_fri_roots data))
        (map (\<lambda>root. ((0::'f),root)) (staged_composition_fri_roots data)) n j start U=1"
   using acc unfolding cff_accept_def lpd_score_def by (rule lpw_accept_score)
 show ?thesis
   unfolding car_family_def Let_def keys
   apply (subst cch_complete_score[OF fields ev])
   using fields one
   by (simp add: cch_fields_def cff_raw_def[symmetric] frozen)
qed

end

subsection \<open>Challenge Unmarked Event\<close>

context soundness
begin

definition cau_event where
 "cau_event N rT rC n j out \<longleftrightarrow>
   (case out of None \<Rightarrow> False | Some(x,t) \<Rightarrow>
    \<not>hash_map_output_collision (channel_for_hash_map (HashMap t)) \<and>
    PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map (HashMap t)) \<and>
    (\<exists>start data. as_header (HashMap t) start data \<and> cvr_evidence (HashMap t) data \<and>
      (cff_accept N rT True n j data (HashMap t) start \<or>
       cff_accept N rC False n j data (HashMap t) start)))"

lemma cau_history_score:
 assumes hist: "fc_history fmempty es (HashMap t)"
   and nob: "fc_no_bad {} es"
   and event: "cau_event N rT rC n j (Some(x,t))"
 shows "1\<le>cap_total N rT rC n j es (HashMap t)"
proof -
 let ?U="HashMap t"
 obtain start data where
   clean: "\<not>hash_map_output_collision (channel_for_hash_map ?U)"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map ?U)"
   and header: "as_header ?U start data" and ev: "cvr_evidence ?U data"
   and either: "cff_accept N rT True n j data ?U start \<or> cff_accept N rC False n j data ?U start"
   using event unfolding cau_event_def by auto
 obtain pre M pred msg post where split: "es=pre@(M,TranscriptAbsorb pred msg,start)#post"
   and oldheader: "as_header (fmupd (TranscriptAbsorb pred msg) start M) start data"
   and born: "as_birth 0 0 j (M,TranscriptAbsorb pred msg,start)=
     Some(as_family 0 0 (fmupd (TranscriptAbsorb pred msg) start M) start j)"
   by (rule vc_birth_witness[OF hist nob clean initial header]) blast
 let ?e="(M,TranscriptAbsorb pred msg,start)"
 let ?B="fmupd (TranscriptAbsorb pred msg) start M"
 have suffix: "fc_history ?B post ?U" using hist by (auto simp: split fc_history_append)
 have ext: "channel_for_hash_map ?B\<le>channel_for_hash_map ?U"
   by (rule fc_history_extension[OF suffix])
 have nobp: "fc_no_bad {} post" using nob by (auto simp: split fc_no_bad_def)
 have nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets ?B)
     (channel_for_hash_map ?B) (channel_for_hash_map ?U)"
   using fc_history_no_target_hit[OF suffix nobp] by (simp add: fc_target_def)
 have one: "car_family N rT True n j ?B start ?U=1 \<or>car_family N rC False n j ?B start ?U=1"
   using either cff_birth_family_one[OF ext clean initial nt oldheader ev] by blast
 have score: "1\<le>cap_record_score N rT rC n j ?e ?U"
   using one by (auto simp: cap_record_score_def car_record_def born)
 have "1\<le>cap_record_score N rT rC n j ?e ?U+cap_total N rT rC n j post ?U"
   by (rule order_trans[OF score]) simp
 also have "... \<le>cap_total N rT rC n j pre ?U+
     (cap_record_score N rT rC n j ?e ?U+cap_total N rT rC n j post ?U)" by simp
 finally show ?thesis by (simp add: split cap_total_def)
qed

end

subsection \<open>Challenge Probability Bound\<close>

context soundness
begin

lemma cau_logged_bound:
  assumes logged: "lp_rule q m L" and empty: "HashMap s=fmempty"
  shows "wp_event m (cau_event N rT rC n j) s\<le>nnreal q*cap_cost rT rC n+
    fc_charge ({}::'f set) q 0"
proof -
  let ?E="cau_event N rT rC n j"
  let ?I="\<lambda>out. case out of None \<Rightarrow> (0::prob) | Some((x,es),t) \<Rightarrow> if ?E(Some(x,t)) then 1 else 0"
  let ?V="\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow>
    cap_live_total N rT rC n j (HashMap s) es (HashMap t)"
  let ?B="\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow> fc_bad_count ({}::'f set) es"
  have trace: "lg_trace q m L" using logged by (simp add: lp_rule_def)
  have erase: "wp_event m ?E s=wp L ?I s"
    unfolding wp_event_def using lg_wp_erase[OF trace, where P="\<lambda>out. if ?E out then 1 else 0" and s=s]
    by (simp only: cau_event_def option.simps if_False)
  have point: "?I out\<le>?V out+?B out"
    if mem: "out\<in>set_dist (execute L s)" for out
  proof (cases out)
    case None then show ?thesis by simp
  next
    case (Some a)
    obtain x es t where out: "out=Some((x,es),t)" using Some by (cases a) auto
    show ?thesis
    proof (cases "?E(Some(x,t))")
      case False then show ?thesis by (simp add: out)
    next
      case True
      have hist: "fc_history fmempty es (HashMap t)"
        using trace mem empty unfolding lg_trace_def
        apply (simp only: out)
        by fastforce
      have bound: "1\<le>?V out+?B out"
      proof (cases "fc_no_bad {} es")
        case good: True
        have clean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap t))"
          using True by (simp add: cau_event_def)
        have alive: "lpl_alive (HashMap s) es (HashMap t)"
          by (simp add: lpl_alive_def empty hist good clean)
        have score: "1\<le>cap_total N rT rC n j es (HashMap t)"
          by (rule cau_history_score[OF hist good True])
        have "1\<le>cap_total N rT rC n j es (HashMap t)+fc_bad_count ({}::'f set) es"
          by (rule order_trans[OF score]) simp
        then show ?thesis by (simp add: out cap_live_total_def alive)
      next
        case False
        have bad: "1\<le>fc_bad_count ({}::'f set) es" by (rule fc_bad_count_detects[OF False])
        have dead: "\<not>lpl_alive (HashMap s) es (HashMap t)" using False by (simp add: lpl_alive_def)
        show ?thesis using bad by (simp add: out cap_live_total_def dead)
      qed
      show ?thesis using bound True by (simp add: out)
    qed
  qed
  have cap: "card(fmdom' (HashMap s))\<le>0" by (simp add: empty)
  have "wp_event m ?E s\<le>wp L (\<lambda>out. ?V out+?B out) s"
    unfolding erase by (rule wp_mono_on_support) (rule point)
  also have "...=wp L ?V s+wp L ?B s" by (rule causal_wp_add)
  also have "...\<le>nnreal q*cap_cost rT rC n+fc_charge ({}::'f set) q 0"
    by (rule add_mono[OF cap_logged_total[OF logged] ll_logged_bad_count[OF logged cap]])
  finally show ?thesis .
qed

lemma cau_program_bound:
  assumes program: "lc_program q m" and empty: "HashMap s=fmempty"
  shows "wp_event m (cau_event N rT rC n j) s\<le>nnreal q*cap_cost rT rC n+
    fc_charge ({}::'f set) q 0"
  using program unfolding lc_program_def by (blast intro: cau_logged_bound[OF _ empty])

lemma cau_saved_experiment_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
      (cau_event N rT rC n j) adversary_initial_state\<le>
    nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*cap_cost rT rC n+
    fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
  by (rule cau_program_bound[OF
    lc_program_ro_absorb_checked_staged_security_experiment_with_data_state[OF wf controlled]])
    (simp add: adversary_initial_state_def)


end

end
