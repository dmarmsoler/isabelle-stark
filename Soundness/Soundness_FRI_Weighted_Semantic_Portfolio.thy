(* Title: Stark/Soundness_FRI_Weighted_Semantic_Portfolio.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Semantic_Portfolio
  imports
    "Soundness_FRI_Weighted_Long_Paths"
begin

section \<open>Semantic Portfolio for weighted MCA soundness\<close>

text \<open>Sum arbitrary-length scores over adaptively born semantic families, stop them on charged bad histories, and recover an unmarked final-map path event.\<close>

subsection \<open>Long Path Adaptive Portfolio\<close>

context soundness
begin

definition lpp_record_score where
  "lpp_record_score rT rC n j e U =
    (case as_birth rT rC j e of None \<Rightarrow> 0 | Some f \<Rightarrow> lpl_family_score rT rC n f U)"

definition lpp_total where
  "lpp_total rT rC n j hist U = sum_list (map (\<lambda>e. lpp_record_score rT rC n j e U) hist)"

lemma lpp_total_append [simp]:
  "lpp_total rT rC n j (xs@ys) U = lpp_total rT rC n j xs U + lpp_total rT rC n j ys U"
  by (simp add: lpp_total_def)

lemma lpp_total_nil [simp]: "lpp_total rT rC n j [] U=0"
  by (simp add: lpp_total_def)

lemma lpp_total_singleton [simp]:
  "lpp_total rT rC n j [e] U=lpp_record_score rT rC n j e U"
  by (simp add: lpp_total_def)

lemma lpp_birth_mass:
  "as_birth rT rC j e=Some (AP_Family S rt ffs cfs v k) \<Longrightarrow> lpw_mass S\<le>ro_mca_weighted_semantic_base rT rC"
  using as_birth_valid
  by (metis ap_valid.simps lpl_mass_eq)

lemma lpp_birth_roots_in_history:
  assumes hist: "fc_history M0 hist U" and member: "e\<in>set hist"
    and birth: "as_birth rT rC j e=Some (AP_Family S rt ffs cfs v k)"
  shows "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets U"
proof -
  obtain Me key raw where e: "e=(Me,key,raw)"
    and ext: "channel_for_hash_map (fmupd key raw Me)\<le>channel_for_hash_map U"
    by (rule fc_history_member[OF hist member])
  have roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets (fmupd key raw Me)"
    by (rule lpl_canonical_birth_roots[OF birth[unfolded e]])
  have mono: "weighted_semantic_interval_targets (fmupd key raw Me)\<subseteq>weighted_semantic_interval_targets U"
    using fc_target_mono[OF ext, where R="{}"] by (simp add: fc_target_def)
  show ?thesis using roots mono by blast
qed

lemma lpp_record_probe:
  assumes hist: "fc_history M0 hist (HashMap s)" and member: "e\<in>set hist"
  shows "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(en,t) \<Rightarrow>
    if \<not>fc_bad_record {} en \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
    then lpp_record_score rT rC n j e (HashMap t) else 0) s
    \<le>lpp_record_score rT rC n j e (HashMap s)"
proof (cases "as_birth rT rC j e")
  case None
  show ?thesis
    by (rule wp_le_const_on_support)
      (use None in \<open>auto simp: lpp_record_score_def split: option.splits prod.splits\<close>)
next
  case (Some f)
  obtain S rt ffs cfs v k where f: "f=AP_Family S rt ffs cfs v k"
    by (cases f) auto
  have birth: "as_birth rT rC j e=Some (AP_Family S rt ffs cfs v k)" using Some f by simp
  have mass: "lpw_mass S\<le>ro_mca_weighted_semantic_base rT rC" by (rule lpp_birth_mass[OF birth])
  have roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets (HashMap s)"
    by (rule lpp_birth_roots_in_history[OF hist member birth])
  show ?thesis unfolding lpp_record_score_def Some f option.case lpl_family_score.simps
    by (rule lpd_stopped_probe[OF mass roots])
qed

lemma lpp_total_probe:
  assumes hist: "fc_history M0 hist (HashMap s)"
  shows "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(en,t) \<Rightarrow>
    if \<not>fc_bad_record {} en \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
    then lpp_total rT rC n j hist (HashMap t) else 0) s
    \<le>lpp_total rT rC n j hist (HashMap s)"
proof -
  have bound: "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(en,t) \<Rightarrow>
      if \<not>fc_bad_record {} en \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
      then lpp_total rT rC n j xs (HashMap t) else 0) s
      \<le>lpp_total rT rC n j xs (HashMap s)"
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
      then lpp_total rT rC n j xs (HashMap t) else 0"
    have eq: "?P (e#es)=(\<lambda>out. ?P [e] out+?P es out)"
      by (rule ext) (auto simp: lpp_total_def split: option.splits prod.splits)
    have "wp (pair_probe key) (?P (e#es)) s =
      wp (pair_probe key) (?P [e]) s+wp (pair_probe key) (?P es) s"
      unfolding eq by (rule causal_wp_add)
    also have "...\<le>lpp_total rT rC n j [e] (HashMap s)+lpp_total rT rC n j es (HashMap s)"
      unfolding lpp_total_singleton
      by (rule add_mono)
        (use lpp_record_probe[OF hist, of e key rT rC n j] Cons.prems Cons.IH in auto)
    finally show ?case by (simp add: lpp_total_def)
  qed
  show ?thesis by (rule bound) simp
qed

end

subsection \<open>Long Path Adaptive Logging\<close>

context soundness
begin

definition lpp_live_total where
  "lpp_live_total rT rC n j M0 hist M =
    (if lpl_alive M0 hist M then lpp_total rT rC n j hist M else 0)"

lemma lpp_live_probe:
  "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
      lpp_live_total rT rC n j M0 (hist@[e]) (HashMap t)) s
    \<le> lpp_live_total rT rC n j M0 hist (HashMap s)+(ro_mca_weighted_semantic_base rT rC)^n"
proof -
  let ?V = "lpp_live_total rT rC n j M0"
  let ?p = "(ro_mca_weighted_semantic_base rT rC)^n"
  let ?old = "\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
    if \<not>fc_bad_record {} e \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
    then lpp_total rT rC n j hist (HashMap t) else 0"
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
        then show ?thesis by (simp add: Some et lpp_live_total_def)
      next
        case alive: True
        have good: "\<not>fc_bad_record {} e"
          and clean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap t))"
          using alive by (auto simp: lpl_alive_def fc_no_bad_def)
        have birthcap: "lpp_record_score rT rC n j e (HashMap t)\<le>?p"
        proof (cases "as_birth rT rC j e")
          case None
          then show ?thesis by (simp add: lpp_record_score_def)
        next
          case (Some f)
          have cap: "lpl_family_score rT rC n f (fmupd key raw (HashMap s))\<le>?p"
            by (rule lpl_canonical_birth_score[OF Some[unfolded e] good[unfolded e]])
          show ?thesis using cap by (simp add: lpp_record_score_def Some maps)
        qed
        show ?thesis using birthcap
          by (simp add: Some et lpp_live_total_def alive good clean)
      qed
    qed
    have "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
        ?V (hist@[e]) (HashMap t)) s \<le>wp (pair_probe key) (\<lambda>out. ?old out+?p) s"
      by (rule wp_mono_on_support) (rule point)
    also have "...=wp (pair_probe key) ?old s+?p"
      by (simp only: causal_wp_add causal_wp_const)
    also have "...\<le>lpp_total rT rC n j hist (HashMap s)+?p"
      by (rule add_right_mono[OF lpp_total_probe[OF hist]])
    finally show ?thesis by (simp add: lpp_live_total_def True)
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
        show ?thesis by (simp add: Some et lpp_live_total_def dead)
      qed
    qed
    then show ?thesis by (rule order_trans) simp
  qed
qed

lemma lpp_potential:
  "lp_potential (\<lambda>fuel hist M. lpp_live_total rT rC n j M0 hist M+
    nnreal fuel*(ro_mca_weighted_semantic_base rT rC)^n)"
proof -
  let ?V = "lpp_live_total rT rC n j M0"
  let ?p = "(ro_mca_weighted_semantic_base rT rC)^n"
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
      by (rule add_right_mono[OF lpp_live_probe])
    also have "...=?V hist (HashMap s)+nnreal (Suc fuel)*?p"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis unfolding lp_potential_def using mono one by blast
qed

lemma lpp_logged_total:
  assumes logged: "lp_rule q m L"
  shows "wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow>
    lpp_live_total rT rC n j (HashMap s) es (HashMap t)) s
    \<le>nnreal q*(ro_mca_weighted_semantic_base rT rC)^n"
proof -
  have pot: "lp_potential (\<lambda>fuel hist M. lpp_live_total rT rC n j (HashMap s) hist M+
      nnreal fuel*(ro_mca_weighted_semantic_base rT rC)^n)" by (rule lpp_potential)
  note bound=lp_ruleD[OF logged pot, where n=0 and hist="[]" and s=s]
  show ?thesis using bound
    by (simp add: lpp_live_total_def cong: if_cong option.case_cong prod.case_cong)
qed

end

subsection \<open>Long Path Adaptive Event\<close>

context soundness
begin

fun lpp_family_accept where
  "lpp_family_accept n (AP_Family S rt ffs cfs v j) M =
    lpw_accept S (lpa_route rt ffs cfs M) (lpa_samples M) n j v"

lemma lpp_family_accept_score:
  "lpp_family_accept n f M \<Longrightarrow> lpl_family_score rT rC n f M=1"
  by (cases f) (auto simp: lpd_score_def intro: lpw_accept_score)

lemma lpp_member_score:
  assumes member: "e\<in>set hist" and birth: "as_birth rT rC j e=Some f"
    and acc: "lpp_family_accept n f M"
  shows "1\<le>lpp_total rT rC n j hist M"
proof -
  have one: "lpp_record_score rT rC n j e M=1"
    using lpp_family_accept_score[OF acc] by (simp add: lpp_record_score_def birth)
  obtain pre post where hist: "hist=pre@e#post" using split_list[OF member] by blast
  have "(1::prob)\<le>1+lpp_total rT rC n j post M" by simp
  also have "...\<le>lpp_total rT rC n j pre M+(1+lpp_total rT rC n j post M)" by simp
  finally show ?thesis by (simp add: hist lpp_total_def one)
qed

definition lpp_selected_event where
  "lpp_selected_event rT rC n j out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some((x,hist),t) \<Rightarrow>
      \<not>hash_map_output_collision (channel_for_hash_map (HashMap t)) \<and>
      (\<exists>e\<in>set hist. \<exists>f. as_birth rT rC j e=Some f \<and> lpp_family_accept n f (HashMap t)))"

lemma lpp_selected_bound:
  assumes logged: "lp_rule q m L" and cap: "card(fmdom' (HashMap s))\<le>hcap"
  shows "wp_event L (lpp_selected_event rT rC n j) s\<le>
    nnreal q*(ro_mca_weighted_semantic_base rT rC)^n+fc_charge ({}::'f set) q hcap"
proof -
  let ?V = "\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow>
    lpp_live_total rT rC n j (HashMap s) es (HashMap t)"
  let ?B = "\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow> fc_bad_count ({}::'f set) es"
  have point: "(if lpp_selected_event rT rC n j out then 1 else 0)\<le>?V out+?B out"
    if mem: "out\<in>set_dist (execute L s)" for out
  proof (cases "lpp_selected_event rT rC n j out")
    case False then show ?thesis by simp
  next
    case True
    obtain x es t e f where out: "out=Some((x,es),t)"
      and clean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap t))"
      and member: "e\<in>set es" and birth: "as_birth rT rC j e=Some f"
      and acc: "lpp_family_accept n f (HashMap t)"
      using True unfolding lpp_selected_event_def by (auto split: option.splits prod.splits)
    have hist: "fc_history (HashMap s) es (HashMap t)"
      using logged mem unfolding lp_rule_def lg_trace_def by (auto simp: out)
    have bound: "1\<le>?V out+?B out"
    proof (cases "fc_no_bad {} es")
      case True
      have alive: "lpl_alive (HashMap s) es (HashMap t)"
        by (simp add: lpl_alive_def hist True clean)
      have score: "1\<le>lpp_total rT rC n j es (HashMap t)"
        by (rule lpp_member_score[OF member birth acc])
      have "1\<le>lpp_total rT rC n j es (HashMap t)+fc_bad_count ({}::'f set) es"
        by (rule order_trans[OF score]) simp
      then show ?thesis by (simp add: out lpp_live_total_def alive)
    next
      case False
      have bad: "1\<le>fc_bad_count ({}::'f set) es" by (rule fc_bad_count_detects[OF False])
      have dead: "\<not>lpl_alive (HashMap s) es (HashMap t)" using False by (simp add: lpl_alive_def)
      show ?thesis using bad by (simp add: out lpp_live_total_def dead)
    qed
    show ?thesis using bound True by simp
  qed
  have "wp_event L (lpp_selected_event rT rC n j) s\<le>wp L (\<lambda>out. ?V out+?B out) s"
    unfolding wp_event_def by (rule wp_mono_on_support) (rule point)
  also have "...=wp L ?V s+wp L ?B s" by (rule causal_wp_add)
  also have "...\<le>nnreal q*(ro_mca_weighted_semantic_base rT rC)^n+fc_charge ({}::'f set) q hcap"
    by (rule add_mono[OF lpp_logged_total[OF logged] ll_logged_bad_count[OF logged cap]])
  finally show ?thesis .
qed

lemma lpp_original_event_bound:
  assumes logged: "lp_rule q m L"
    and cap: "card(fmdom' (HashMap s))\<le>hcap"
    and none: "\<not>E None"
    and coverage: "\<And>x es t. Some((x,es),t)\<in>set_dist (execute L s) \<Longrightarrow>
      E(Some(x,t)) \<Longrightarrow> lpp_selected_event rT rC n j (Some((x,es),t))"
  shows "wp_event m E s\<le>nnreal q*(ro_mca_weighted_semantic_base rT rC)^n+fc_charge ({}::'f set) q hcap"
proof -
  have trace: "lg_trace q m L" using logged by (simp add: lp_rule_def)
  let ?I = "\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow> if E(Some(x,t)) then 1 else 0"
  have erase: "wp_event m E s=wp L ?I s"
    unfolding wp_event_def using lg_wp_erase[OF trace, where P="\<lambda>out. if E out then 1 else 0" and s=s]
    by (simp only: none if_False)
  have "wp L ?I s\<le>wp_event L (lpp_selected_event rT rC n j) s"
    unfolding wp_event_def
    by (rule wp_mono_on_support) (use coverage in \<open>auto split: option.splits prod.splits\<close>)
  also have "...\<le>nnreal q*(ro_mca_weighted_semantic_base rT rC)^n+fc_charge ({}::'f set) q hcap"
    by (rule lpp_selected_bound[OF logged cap])
  finally show ?thesis by (simp only: erase)
qed

end

subsection \<open>Long Path Semantic Freeze\<close>

context soundness
begin

lemma lps_header_indices_stable:
  assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    and nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
      (channel_for_hash_map M) (channel_for_hash_map U)"
    and header: "as_header M start data"
  shows "weighted_semantic_indices rT rC M data=weighted_semantic_indices rT rC U data"
proof -
  obtain rest where active: "staged_trace_fri_roots data\<noteq>[]"
    and chain: "ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
      (weighted_semantic_header data@rest) start"
    using header unfolding as_header_def by blast
  have messages: "set(weighted_semantic_header data)\<subseteq>transcript_absorb_message_values M"
    using ro_absorb_lookup_chain_messages_subset[OF chain] by auto
  have tables: "conceptual_table (channel_for_hash_map M) rt (scale*clength)=
      conceptual_table (channel_for_hash_map U) rt (scale*clength)"
    if rt: "rt\<in>set(weighted_semantic_header data)" for rt
  proof -
    have sub: "merkle_prefix_path_targets {rt} (channel_for_hash_map M)\<subseteq>weighted_semantic_interval_targets M"
      using messages rt unfolding merkle_prefix_path_targets_def weighted_semantic_interval_targets_def by blast
    have nt': "\<not>hash_map_new_output_hit (merkle_prefix_path_targets {rt} (channel_for_hash_map M))
      (channel_for_hash_map M) (channel_for_hash_map U)"
      using hash_map_new_output_hit_subset[OF sub] nt by blast
    show ?thesis using conceptual_table_prefix_stable_if_no_target[OF ext nt'] by simp
  qed
  show ?thesis by (rule weighted_semantic_map_cong[OF active tables])
qed

lemma lps_header_ready:
  "as_header M start data \<Longrightarrow>
    weighted_semantic_ready rT rC M start (weighted_semantic_indices rT rC M data)"
  unfolding as_header_def weighted_semantic_ready_def by blast

lemma lps_descendant_hit_frozen:
  assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
    and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map U)"
    and nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
      (channel_for_hash_map M) (channel_for_hash_map U)"
    and header: "as_header M start data"
    and route: "ro_absorb_lookup_chain (channel_for_hash_map U) start xs v"
    and hit: "weighted_semantic_hit rT rC U v raw"
  shows "weighted_semantic_hit rT rC M start raw"
proof -
  obtain rest where shape: "weighted_semantic_header_shape data"
    and active: "staged_trace_fri_roots data\<noteq>[]"
    and oldchain: "ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
      (weighted_semantic_header data@rest) start"
    using header unfolding as_header_def by blast
  have chain: "ro_absorb_lookup_chain (channel_for_hash_map U) (PState adversary_initial_state)
      (weighted_semantic_header data@(rest@xs)) v"
    using ro_absorb_lookup_chain_append[OF ro_absorb_lookup_chain_mono[OF oldchain ext] route] by simp
  have ready: "weighted_semantic_ready rT rC U v (weighted_semantic_indices rT rC U data)"
    unfolding weighted_semantic_ready_def using shape active chain by blast
  obtain I where ready': "weighted_semantic_ready rT rC U v I"
    and raw: "raw\<in>query_index_raw_preimage I"
    using hit unfolding weighted_semantic_hit_def by blast
  have eq: "I=weighted_semantic_indices rT rC U data"
    by (rule weighted_semantic_ready_unique[OF clean initial ready' ready])
  have oldready: "weighted_semantic_ready rT rC M start (weighted_semantic_indices rT rC M data)"
    by (rule lps_header_ready[OF header])
  have eq': "weighted_semantic_indices rT rC M data=weighted_semantic_indices rT rC U data"
    by (rule lps_header_indices_stable[OF ext nt header])
  show ?thesis unfolding weighted_semantic_hit_def
    apply (rule exI[of _ "weighted_semantic_indices rT rC M data"], intro conjI)
     apply (rule oldready)
    using raw by (simp only: eq eq')
qed

lemma lps_routes_roots_cong:
  assumes roots: "map snd ffs=map snd ffs'" "map snd cfs=map snd cfs'"
  shows "lpa_route rt ffs cfs M=lpa_route rt ffs' cfs' M"
proof -
  have eq: "pair_route_fiber UNIV rt ffs cfs v (channel_for_hash_map M)=
      pair_route_fiber UNIV rt ffs' cfs' v (channel_for_hash_map M)" for v
    by (rule ext, rule ea_route_roots_cong[OF roots])
  show ?thesis unfolding lpa_route_def by (simp only: eq)
qed

fun lps_semantic_path where
  "lps_semantic_path rT rC rt ffs cfs U 0 i v=True"
| "lps_semantic_path rT rC rt ffs cfs U (Suc n) i v =
    (\<exists>raw. lpa_samples U (i,v)=Some raw \<and> weighted_semantic_hit rT rC U v raw \<and>
      (n=0 \<or> (\<exists>w. lpa_route rt ffs cfs U (i,v) raw=Some w \<and>
        lps_semantic_path rT rC rt ffs cfs U n (Suc i) w)))"

lemma lps_path_freeze:
  assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
    and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map U)"
    and nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
      (channel_for_hash_map M) (channel_for_hash_map U)"
    and header: "as_header M start data"
    and route: "ro_absorb_lookup_chain (channel_for_hash_map U) start xs v"
    and path: "lps_semantic_path rT rC rt ffs cfs U n i v"
  shows "lpw_accept {raw. weighted_semantic_hit rT rC M start raw}
    (lpa_route rt ffs cfs U) (lpa_samples U) n i v"
  using route path
proof (induction n arbitrary: xs v i)
  case 0 then show ?case by simp
next
  case (Suc n)
  obtain raw where sample: "lpa_samples U (i,v)=Some raw"
    and hit: "weighted_semantic_hit rT rC U v raw"
    and tail: "n=0 \<or> (\<exists>w. lpa_route rt ffs cfs U (i,v) raw=Some w \<and>
      lps_semantic_path rT rC rt ffs cfs U n (Suc i) w)"
    using Suc.prems by auto
  have frozen: "weighted_semantic_hit rT rC M start raw"
    by (rule lps_descendant_hit_frozen[OF ext clean initial nt header Suc.prems(1) hit])
  have rest: "n=0 \<or> (\<exists>w. lpa_route rt ffs cfs U (i,v) raw=Some w \<and>
    lpw_accept {raw. weighted_semantic_hit rT rC M start raw}
      (lpa_route rt ffs cfs U) (lpa_samples U) n (Suc i) w)"
  proof (cases "n=0")
    case True then show ?thesis by simp
  next
    case False
    obtain w where edge: "lpa_route rt ffs cfs U (i,v) raw=Some w"
      and path': "lps_semantic_path rT rC rt ffs cfs U n (Suc i) w"
      using tail False by blast
    obtain ys where chain: "ro_absorb_lookup_chain (channel_for_hash_map U) v ys w"
      using lpa_route_chain[OF edge] by auto
    have total: "ro_absorb_lookup_chain (channel_for_hash_map U) start (xs@ys) w"
      by (rule ro_absorb_lookup_chain_append[OF Suc.prems(1) chain])
    have acc: "lpw_accept {raw. weighted_semantic_hit rT rC M start raw}
      (lpa_route rt ffs cfs U) (lpa_samples U) n (Suc i) w"
      by (rule Suc.IH[OF total path'])
    show ?thesis using edge acc by blast
  qed
  show ?case using sample frozen rest by auto
qed

end

subsection \<open>Long Path Unmarked Event\<close>

context soundness
begin

definition lpu_event where
  "lpu_event rT rC n j out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some(x,t) \<Rightarrow>
      \<not>hash_map_output_collision (channel_for_hash_map (HashMap t)) \<and>
      PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map (HashMap t)) \<and>
      (\<exists>start data rt ffs cfs.
        as_header (HashMap t) start data \<and> rt=staged_trace_root data \<and>
        map snd ffs=staged_trace_fri_roots data \<and>
        map snd cfs=staged_composition_fri_roots data \<and>
        lps_semantic_path rT rC rt ffs cfs (HashMap t) n j start))"

lemma lpu_history_selected:
  assumes hist: "fc_history fmempty es (HashMap t)"
    and nob: "fc_no_bad {} es"
    and event: "lpu_event rT rC n j (Some(x,t))"
  shows "lpp_selected_event rT rC n j (Some((x,es),t))"
proof -
  let ?U="HashMap t"
  obtain start data rt ffs cfs where
    clean: "\<not>hash_map_output_collision (channel_for_hash_map ?U)"
    and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map ?U)"
    and header: "as_header ?U start data"
    and rt: "rt=staged_trace_root data"
    and ff: "map snd ffs=staged_trace_fri_roots data"
    and cf: "map snd cfs=staged_composition_fri_roots data"
    and path: "lps_semantic_path rT rC rt ffs cfs ?U n j start"
    using event unfolding lpu_event_def by auto
  obtain pre M pred msg post where split: "es=pre@(M,TranscriptAbsorb pred msg,start)#post"
    and oldheader: "as_header (fmupd (TranscriptAbsorb pred msg) start M) start data"
    and born: "as_birth rT rC j (M,TranscriptAbsorb pred msg,start)=
      Some(as_family rT rC (fmupd (TranscriptAbsorb pred msg) start M) start j)"
    by (rule vc_birth_witness[OF hist nob clean initial header]) blast
  let ?V="fmupd (TranscriptAbsorb pred msg) start M"
  let ?D="as_data ?V start"
  let ?S="{raw. weighted_semantic_hit rT rC ?V start raw}"
  let ?F="map (\<lambda>r.((0::'f),r)) (staged_trace_fri_roots ?D)"
  let ?G="map (\<lambda>r.((0::'f),r)) (staged_composition_fri_roots ?D)"
  have suffix: "fc_history ?V post ?U"
    using hist by (auto simp: split fc_history_append)
  have ext: "channel_for_hash_map ?V\<le>channel_for_hash_map ?U"
    by (rule fc_history_extension[OF suffix])
  have nobp: "fc_no_bad {} post" using nob by (auto simp: split fc_no_bad_def)
  have nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets ?V)
    (channel_for_hash_map ?V) (channel_for_hash_map ?U)"
    using fc_history_no_target_hit[OF suffix nobp] by (simp add: fc_target_def)
  have frozen: "lpw_accept ?S (lpa_route rt ffs cfs ?U) (lpa_samples ?U) n j start"
    by (rule lps_path_freeze[OF ext clean initial nt oldheader, where xs="[]"]) (simp, rule path)
  note base=as_clean_prefix[OF ext clean initial]
  note fields=as_canonical_root_fields[OF base oldheader]
  have rt': "rt=staged_trace_root ?D" using rt fields(1) by simp
  have roots: "map snd ffs=map snd ?F" "map snd cfs=map snd ?G"
    using ff cf fields by (simp_all add: comp_def)
  have routes: "lpa_route rt ffs cfs ?U=lpa_route rt ?F ?G ?U"
    by (rule lps_routes_roots_cong[OF roots])
  have acc: "lpp_family_accept n (as_family rT rC ?V start j) ?U"
    using frozen[unfolded routes] unfolding as_family_def lpp_family_accept.simps
    by (simp only: rt')
  have member: "(M,TranscriptAbsorb pred msg,start)\<in>set es" by (simp add: split)
  show ?thesis unfolding lpp_selected_event_def
    apply (simp only: option.simps prod.case)
    apply (intro conjI clean)
    apply (rule bexI[of _ "(M,TranscriptAbsorb pred msg,start)"])
     apply (rule exI[of _ "as_family rT rC ?V start j"])
    using born acc member by simp_all
qed

lemma lpu_logged_bound:
  assumes logged: "lp_rule q m L" and empty: "HashMap s=fmempty"
  shows "wp_event m (lpu_event rT rC n j) s\<le>nnreal q*(ro_mca_weighted_semantic_base rT rC)^n+
    fc_charge ({}::'f set) q 0"
proof -
  let ?E="lpu_event rT rC n j"
  let ?I="\<lambda>out. case out of None \<Rightarrow> (0::prob) | Some((x,es),t) \<Rightarrow> if ?E(Some(x,t)) then 1 else 0"
  let ?V="\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow>
    lpp_live_total rT rC n j (HashMap s) es (HashMap t)"
  let ?B="\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow> fc_bad_count ({}::'f set) es"
  have trace: "lg_trace q m L" using logged by (simp add: lp_rule_def)
  have erase: "wp_event m ?E s=wp L ?I s"
    unfolding wp_event_def using lg_wp_erase[OF trace, where P="\<lambda>out. if ?E out then 1 else 0" and s=s]
    by (simp only: lpu_event_def option.simps if_False)
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
        have selected: "lpp_selected_event rT rC n j (Some((x,es),t))"
          by (rule lpu_history_selected[OF hist good True])
        obtain e f where clean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap t))"
          and member: "e\<in>set es" and birth: "as_birth rT rC j e=Some f"
          and acc: "lpp_family_accept n f (HashMap t)"
          using selected unfolding lpp_selected_event_def by auto
        have alive: "lpl_alive (HashMap s) es (HashMap t)"
          by (simp add: lpl_alive_def empty hist good clean)
        have score: "1\<le>lpp_total rT rC n j es (HashMap t)"
          by (rule lpp_member_score[OF member birth acc])
        have "1\<le>lpp_total rT rC n j es (HashMap t)+fc_bad_count ({}::'f set) es"
          by (rule order_trans[OF score]) simp
        then show ?thesis by (simp add: out lpp_live_total_def alive)
      next
        case False
        have bad: "1\<le>fc_bad_count ({}::'f set) es" by (rule fc_bad_count_detects[OF False])
        have dead: "\<not>lpl_alive (HashMap s) es (HashMap t)" using False by (simp add: lpl_alive_def)
        show ?thesis using bad by (simp add: out lpp_live_total_def dead)
      qed
      show ?thesis using bound True by (simp add: out)
    qed
  qed
  have cap: "card(fmdom' (HashMap s))\<le>0" by (simp add: empty)
  have "wp_event m ?E s\<le>wp L (\<lambda>out. ?V out+?B out) s"
    unfolding erase by (rule wp_mono_on_support) (rule point)
  also have "...=wp L ?V s+wp L ?B s" by (rule causal_wp_add)
  also have "...\<le>nnreal q*(ro_mca_weighted_semantic_base rT rC)^n+fc_charge ({}::'f set) q 0"
    by (rule add_mono[OF lpp_logged_total[OF logged] ll_logged_bad_count[OF logged cap]])
  finally show ?thesis .
qed

lemma lpu_program_bound:
  assumes program: "lc_program q m" and empty: "HashMap s=fmempty"
  shows "wp_event m (lpu_event rT rC n j) s\<le>nnreal q*(ro_mca_weighted_semantic_base rT rC)^n+
    fc_charge ({}::'f set) q 0"
  using program unfolding lc_program_def by (blast intro: lpu_logged_bound[OF _ empty])

lemma lpu_saved_experiment_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
      (lpu_event rT rC n j) adversary_initial_state\<le>
    nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*(ro_mca_weighted_semantic_base rT rC)^n+
    fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
  by (rule lpu_program_bound[OF
    lc_program_ro_absorb_checked_staged_security_experiment_with_data_state[OF wf controlled]])
    (simp add: adversary_initial_state_def)

end

end
