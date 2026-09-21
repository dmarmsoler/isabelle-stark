(* Title: Stark/Soundness_FRI_Weighted_Execution_Replay.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Execution_Replay
  imports
    "Soundness_FRI_Weighted_Staged_Logging"
    "Soundness_FRI_Weighted_Verifier_Logging"
begin

section \<open>Execution Replay for weighted MCA soundness\<close>

text \<open>Recover selected query paths from supported executions and their insertion histories. These local replay and header facts are reused by the all-repetition semantic and FRI endpoints.\<close>

subsection \<open>Logged History Coverage\<close>

context soundness
begin

lemma vc_first_insertion:
 assumes history: "fc_history M es U"
   and absent: "fmlookup M k=None"
   and final: "fmlookup U k=Some z"
 shows "\<exists>pre V post. es=pre@(V,k,z)#post \<and> fc_history M pre V \<and>
   fmlookup V k=None \<and> fc_history (fmupd k z V) post U"
 using history absent final
proof (induction es arbitrary: M)
 case Nil
 then show ?case by simp
next
 case (Cons e es)
 obtain Me ke x where e: "e=(Me,ke,x)" by (cases e) auto
 have Me: "Me=M" and tail: "fc_history (fmupd ke x M) es U"
   and old: "fmlookup M ke=None \<or> fmlookup M ke=Some x"
   using Cons.prems by (auto simp: e)
 show ?case
 proof (cases "ke=k")
  case True
  have ext: "channel_for_hash_map (fmupd ke x M)\<le>channel_for_hash_map U"
    by (rule fc_history_extension[OF tail])
  have inserted: "fmlookup (HashMap (channel_for_hash_map (fmupd ke x M))) ke=Some x"
    by (simp add: channel_for_hash_map_def)
  have persisted: "fmlookup (HashMap (channel_for_hash_map U)) ke=Some x"
    by (rule hash_extension_lookup[OF inserted ext])
  have xz: "x=z"
    using persisted Cons.prems(3) True by (simp add: channel_for_hash_map_def)
  show ?thesis
    by (intro exI[of _ "[]"] exI[of _ M] exI[of _ es])
      (use Cons.prems tail True xz Me in \<open>auto simp: e\<close>)
 next
  case False
  have absent': "fmlookup (fmupd ke x M) k=None"
    using False Cons.prems(2) by simp
  obtain pre V post where ih:
    "es=pre@(V,k,z)#post" "fc_history (fmupd ke x M) pre V"
    "fmlookup V k=None" "fc_history (fmupd k z V) post U"
    using Cons.IH[OF tail absent' Cons.prems(3)] by blast
  show ?thesis
    by (intro exI[of _ "e#pre"] exI[of _ V] exI[of _ post])
      (use ih Me old in \<open>auto simp: e\<close>)
 qed
qed

lemma vc_two_members:
 assumes a: "a\<in>set es" and b: "b\<in>set es" and different: "a\<noteq>b"
 shows "\<exists>pre mid post forward. es=pre@(if forward then a#mid@[b] else b#mid@[a])@post"
proof -
 obtain pre post where es: "es=pre@a#post" using split_list[OF a] by blast
 show ?thesis
 proof (cases "b\<in>set pre")
  case True
  obtain p q where pre: "pre=p@b#q" using split_list[OF True] by blast
  show ?thesis
   by (intro exI[of _ p] exI[of _ q] exI[of _ post] exI[of _ False])
    (simp add: es pre)
 next
  case False
  have member: "b\<in>set post" using b different False by (auto simp: es)
  obtain p q where post: "post=p@b#q" using split_list[OF member] by blast
  show ?thesis
   by (intro exI[of _ pre] exI[of _ p] exI[of _ q] exI[of _ True])
    (simp add: es post)
 qed
qed

lemma vc_header_last:
 assumes header: "as_header U start data"
 shows "\<exists>pred msg. fmlookup U (TranscriptAbsorb pred msg)=Some start"
proof -
 obtain rest where chain: "ro_absorb_lookup_chain (channel_for_hash_map U)
   (PState adversary_initial_state) (weighted_semantic_header data@rest) start"
   using header unfolding as_header_def by blast
 have nonempty: "weighted_semantic_header data@rest\<noteq>[]"
   by (simp add: weighted_semantic_header_def verifier_header_messages_def)
 obtain xs x where xs: "weighted_semantic_header data@rest=xs@[x]"
   using nonempty by (cases "weighted_semantic_header data@rest" rule: rev_cases) auto
 obtain mid where "fmlookup (HashMap (channel_for_hash_map U)) (TranscriptAbsorb mid x)=Some start"
   using ro_absorb_lookup_chain_snoc[OF chain[unfolded xs]] by blast
 then show ?thesis by (auto simp: channel_for_hash_map_def)
qed

lemma vc_birth_witness:
 assumes history: "fc_history fmempty hist U"
   and nob: "fc_no_bad {} hist"
   and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map U)"
   and header: "as_header U start data"
 obtains pre M pred msg post where
   "hist=pre@(M,TranscriptAbsorb pred msg,start)#post"
   "fmlookup M (TranscriptAbsorb pred msg)=None"
   "fc_history M ((M,TranscriptAbsorb pred msg,start)#post) U"
   "fc_no_bad {} ((M,TranscriptAbsorb pred msg,start)#post)"
   "as_header (fmupd (TranscriptAbsorb pred msg) start M) start data"
   "as_birth rT rC j (M,TranscriptAbsorb pred msg,start)=
     Some (as_family rT rC (fmupd (TranscriptAbsorb pred msg) start M) start j)"
proof -
 obtain pred msg where stored: "fmlookup U (TranscriptAbsorb pred msg)=Some start"
   using vc_header_last[OF header] by blast
 obtain pre M post where split: "hist=pre@(M,TranscriptAbsorb pred msg,start)#post"
   and fresh: "fmlookup M (TranscriptAbsorb pred msg)=None"
   and tail: "fc_history (fmupd (TranscriptAbsorb pred msg) start M) post U"
   using vc_first_insertion[OF history _ stored] by auto
 have history': "fc_history M ((M,TranscriptAbsorb pred msg,start)#post) U"
   using fresh tail by simp
 have nob': "fc_no_bad {} ((M,TranscriptAbsorb pred msg,start)#post)"
   using nob by (simp add: split fc_no_bad_def)
 note birth=as_birth_from_final_header[OF history' nob' fresh clean initial header]
 show ?thesis by (rule that[OF split fresh history' nob' birth])
qed

lemma vc_selected_from_lookups:
 assumes history: "fc_history V es (HashMap u)"
  and absentp: "fmlookup V (QueryIndexChallenge j start)=None"
  and absentc: "fmlookup V (QueryIndexChallenge (Suc j) v)=None"
  and lookp: "fmlookup (HashMap u) (QueryIndexChallenge j start)=Some z"
  and lookc: "fmlookup (HashMap u) (QueryIndexChallenge (Suc j) v)=Some x"
  and clean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap u))"
  and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map (HashMap u))"
  and hitp: "weighted_semantic_hit rT rC (HashMap u) start z"
  and hitc: "weighted_semantic_hit rT rC (HashMap u) v x"
  and counter: "PQueryCounter qs=j" and start: "PState qs=start"
  and successor: "PState qt=v" and ext: "qt\<le>u"
  and actual: "Some ((),qt)\<in>set_dist
   (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) qs)"
 shows "fc_selected_event rT rC rt ffs fv alphas cfs cv start j (Some (((),es),u))"
proof -
 obtain pr Mr sr where parent: "es=pr@(Mr,QueryIndexChallenge j start,z)#sr"
  and freshp: "fmlookup Mr (QueryIndexChallenge j start)=None"
  using vc_first_insertion[OF history absentp lookp] by blast
 obtain pc Mc sc where child: "es=pc@(Mc,QueryIndexChallenge (Suc j) v,x)#sc"
  and freshc: "fmlookup Mc (QueryIndexChallenge (Suc j) v)=None"
  using vc_first_insertion[OF history absentc lookc] by blast
 let ?re="(Mr,QueryIndexChallenge j start,z)"
 let ?ce="(Mc,QueryIndexChallenge (Suc j) v,x)"
 have pm: "?re\<in>set es" by (simp add: parent)
 have cm: "?ce\<in>set es" by (simp add: child)
 have distinct: "?re\<noteq>?ce" by auto
 obtain pre mid post forward where split:
   "es=pre@(if forward then ?re#mid@[?ce] else ?ce#mid@[?re])@post"
   using vc_two_members[OF pm cm distinct] by blast
 have preext: "channel_for_hash_map Mc\<le>channel_for_hash_map (HashMap u)"
   by (rule fc_history_member[OF history cm]) auto
 have postext: "channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x Mc)
    \<le>channel_for_hash_map (HashMap u)"
   by (rule fc_history_member[OF history cm]) auto
 have base: "pair_base_ok Mc"
   using as_clean_prefix[OF preext clean initial] by (simp add: pair_base_ok_def)
 have ready: "pair_eventual_ready rT rC (HashMap u) ?ce"
   using freshc base postext hitc by (auto simp: pair_eventual_ready_def)
 show ?thesis unfolding fc_selected_event_def
   apply (simp only: option.simps prod.case)
   apply (rule exI[of _ pre], rule exI[of _ mid], rule exI[of _ post],
      rule exI[of _ forward], rule exI[of _ Mc], rule exI[of _ v], rule exI[of _ x],
      rule exI[of _ Mr], rule exI[of _ z], rule exI[of _ qs], rule exI[of _ qt])
   using split freshc freshp clean hitp ready counter start successor ext actual
   by (simp add: Let_def)
qed

lemma vc_unmarked_history_selected:
 assumes history: "fc_history fmempty hist (HashMap u)"
  and nob: "fc_no_bad {} hist"
  and clean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap u))"
  and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map (HashMap u))"
  and header: "as_header (HashMap u) start data"
  and rt: "rt=staged_trace_root data"
  and ffs: "map snd ffs=staged_trace_fri_roots data"
  and cfs: "map snd cfs=staged_composition_fri_roots data"
  and lenf: "length ffs\<le>N" and lenc: "length cfs\<le>N"
  and lookp: "fmlookup (HashMap u) (QueryIndexChallenge j start)=Some z"
  and lookc: "fmlookup (HashMap u) (QueryIndexChallenge (Suc j) v)=Some x"
  and hitp: "weighted_semantic_hit rT rC (HashMap u) start z"
  and hitc: "weighted_semantic_hit rT rC (HashMap u) v x"
  and counter: "PQueryCounter qs=j" and start: "PState qs=start"
  and successor: "PState qt=v" and ext: "qt\<le>u"
  and actual: "Some ((),qt)\<in>set_dist
    (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) qs)"
 shows "ar_selected_event rT rC j N (Some ((acc,hist),u))"
proof -
 obtain pre M pred msg post where split: "hist=pre@(M,TranscriptAbsorb pred msg,start)#post"
  and fresh: "fmlookup M (TranscriptAbsorb pred msg)=None"
  and tail: "fc_history M ((M,TranscriptAbsorb pred msg,start)#post) (HashMap u)"
  and nobtail: "fc_no_bad {} ((M,TranscriptAbsorb pred msg,start)#post)"
  and oldheader: "as_header (fmupd (TranscriptAbsorb pred msg) start M) start data"
  and birth: "as_birth rT rC j (M,TranscriptAbsorb pred msg,start)=
    Some (as_family rT rC (fmupd (TranscriptAbsorb pred msg) start M) start j)"
  by (rule vc_birth_witness[OF history nob clean initial header]) blast
 let ?V="fmupd (TranscriptAbsorb pred msg) start M"
 have suffix: "fc_history ?V post (HashMap u)" using tail by simp
 obtain chunk where chain: "ro_absorb_lookup_chain qt (PState qs) chunk (PState qt)"
  by (rule ro_verifier_query_round_program_outcome_with_lookup_chain[OF actual]) blast
 have ext': "qt\<le>channel_for_hash_map (HashMap u)"
  using ext by (simp add: less_eq_hash_ext_def channel_for_hash_map_def)
 have route: "ro_absorb_lookup_chain (channel_for_hash_map (HashMap u)) start chunk v"
  using ro_absorb_lookup_chain_mono[OF chain ext'] by (simp add: start successor)
 note absent=ab_birth_excludes_old_queries[OF tail nobtail fresh route]
 have selected: "fc_selected_event rT rC rt ffs fv alphas cfs cv start j (Some (((),post),u))"
  by (rule vc_selected_from_lookups[OF suffix absent(1) absent(2) lookp lookc
      clean initial hitp hitc counter start successor ext actual])
 have prefix: "channel_for_hash_map ?V\<le>channel_for_hash_map (HashMap u)"
  by (rule fc_history_extension[OF suffix])
 note base=as_clean_prefix[OF prefix clean initial]
 note fields=as_canonical_root_fields[OF base oldheader]
 have matches: "ar_matches ?V start rt ffs cfs"
  using fields rt ffs cfs by (simp add: ar_matches_def)
 show ?thesis unfolding ar_selected_event_def
  apply (simp only: option.simps prod.case)
  apply (rule exI[of _ pre], rule exI[of _ M], rule exI[of _ pred], rule exI[of _ msg],
    rule exI[of _ start], rule exI[of _ post], rule exI[of _ rt], rule exI[of _ ffs],
    rule exI[of _ fv], rule exI[of _ alphas], rule exI[of _ cfs], rule exI[of _ cv])
  using split birth matches lenf lenc selected by (simp add: Let_def)
qed

end

subsection \<open>Actual Unmarked Pair Bound\<close>

context soundness
begin

text \<open>This final-state overapproximation has no log, birth or freshness witness.
Its two stored query keys are connected by an actual supported verifier round.
The event includes the clean-map and initial-value-avoidance branch guards.
It is not false acceptance and does not assert an all-round sampling theorem.\<close>

definition vu_pair_event where
 "vu_pair_event rT rC j N out \<longleftrightarrow>
  (case out of None\<Rightarrow>False | Some (result,u)\<Rightarrow>
   \<not>hash_map_output_collision (channel_for_hash_map (HashMap u)) \<and>
   PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map (HashMap u)) \<and>
   (\<exists>start data rt ffs fv alphas cfs cv v z x qs qt.
    as_header (HashMap u) start data \<and>
    rt=staged_trace_root data \<and> map snd ffs=staged_trace_fri_roots data \<and>
    map snd cfs=staged_composition_fri_roots data \<and> length ffs\<le>N \<and> length cfs\<le>N \<and>
    fmlookup (HashMap u) (QueryIndexChallenge j start)=Some z \<and>
    fmlookup (HashMap u) (QueryIndexChallenge (Suc j) v)=Some x \<and>
    weighted_semantic_hit rT rC (HashMap u) start z \<and>
    weighted_semantic_hit rT rC (HashMap u) v x \<and>
    PQueryCounter qs=j \<and> PState qs=start \<and> PState qt=v \<and> qt\<le>u \<and>
    Some ((),qt)\<in>set_dist
      (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) qs)))"

lemma vu_pair_history_selected:
 assumes history: "fc_history fmempty hist (HashMap u)"
   and nob: "fc_no_bad {} hist"
   and event: "vu_pair_event rT rC j N (Some (result,u))"
 shows "ar_selected_event rT rC j N (Some ((result,hist),u))"
 using event unfolding vu_pair_event_def
 by (auto intro: vc_unmarked_history_selected[OF history nob])

lemma vu_logged_bound:
 fixes m :: "('a, 'f protocol_channel) state_monad"
 assumes logged: "lp_rule q m L"
   and power: "clength*scale=2^N"
   and empty: "HashMap s=fmempty"
 shows "wp_event m (vu_pair_event rT rC j N) s \<le>
   nnreal q*(ro_mca_weighted_semantic_base rT rC)^2+fc_charge ({}::'f set) q 0"
proof -
 let ?step="ap_step rT rC (as_birth rT rC j)"
 let ?E="vu_pair_event rT rC j N"
 let ?I="\<lambda>out. case out of None\<Rightarrow>(0::prob) | Some ((x,es),t)\<Rightarrow>
   if ?E (Some (x,t)) then 1 else 0"
 let ?V="\<lambda>out. case out of None\<Rightarrow>0 | Some ((x,es),t)\<Rightarrow>ap_score rT rC (foldl ?step [] es)"
 let ?B="\<lambda>out. case out of None\<Rightarrow>0 | Some ((x,es),t)\<Rightarrow>fc_bad_count ({}::'f set) es"
 have trace: "lg_trace q m L" using logged unfolding lp_rule_def by blast
 have erased: "wp_event m ?E s=wp L ?I s"
   unfolding wp_event_def using lg_wp_erase[OF trace, of "\<lambda>out. if ?E out then 1 else 0" s]
   by (simp add: vu_pair_event_def split: option.splits prod.splits)
 have point: "?I out\<le>?V out+?B out"
   if supported: "out\<in>set_dist (execute L s)" for out
 proof (cases out)
  case None
  then show ?thesis by simp
 next
  case (Some a)
  obtain x es t where out: "out=Some ((x,es),t)" using Some by (cases a) auto
  show ?thesis
  proof (cases "?E (Some (x,t))")
   case False
   then show ?thesis by (simp add: out)
  next
   case True
   have hist: "fc_history fmempty es (HashMap t)"
     using trace supported empty unfolding lg_trace_def
     apply (simp only: out)
     by fastforce
   show ?thesis
   proof (cases "fc_no_bad {} es")
    case True
    have event: "ar_selected_event rT rC j N (Some ((x,es),t))"
      by (rule vu_pair_history_selected[OF hist True \<open>?E (Some (x,t))\<close>])
    obtain f where won: "(f,FC_Won)\<in>set (foldl ?step [] es)"
      using ar_selected_history_wins[OF power hist event True] by blast
    have score: "1\<le>ap_score rT rC (foldl ?step [] es)"
      by (rule ap_won_member_score[OF won])
    have total: "1\<le>ap_score rT rC (foldl ?step [] es)+fc_bad_count ({}::'f set) es"
      by (rule order_trans[OF score]) simp
    show ?thesis using total by (simp add: out)
   next
    case False
    have count: "1\<le>fc_bad_count ({}::'f set) es"
      by (rule fc_bad_count_detects[OF False])
    have total: "1\<le>ap_score rT rC (foldl ?step [] es)+fc_bad_count ({}::'f set) es"
      by (rule order_trans[OF count]) simp
    show ?thesis using total by (simp add: out)
   qed
  qed
 qed
 have cap: "card (fmdom' (HashMap s))\<le>0" by (simp add: empty)
 have "wp_event m ?E s\<le>wp L (\<lambda>out. ?V out+?B out) s"
   unfolding erased by (rule wp_mono_on_support) (rule point)
 also have "...=wp L ?V s+wp L ?B s" by (rule causal_wp_add)
 also have "...\<le>nnreal q*(ro_mca_weighted_semantic_base rT rC)^2+fc_charge ({}::'f set) q 0"
   by (rule add_mono[OF lr_canonical_score[OF logged] ll_logged_bad_count[OF logged cap]])
 finally show ?thesis .
qed

lemma vu_program_bound:
 fixes m :: "('a, 'f protocol_channel) state_monad"
 assumes program: "lc_program q m" and power: "clength*scale=2^N"
   and empty: "HashMap s=fmempty"
 shows "wp_event m (vu_pair_event rT rC j N) s\<le>
   nnreal q*(ro_mca_weighted_semantic_base rT rC)^2+fc_charge ({}::'f set) q 0"
 using program unfolding lc_program_def by (blast intro: vu_logged_bound[OF _ power empty])

lemma vu_original_experiment_bound:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and power: "clength*scale=2^N"
 shows "wp_event (ro_absorb_checked_staged_security_experiment A)
    (vu_pair_event rT rC j N) adversary_initial_state \<le>
   nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*(ro_mca_weighted_semantic_base rT rC)^2+
   fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
 by (rule vu_program_bound[OF lc_program_ro_absorb_checked_staged_security_experiment[OF wf controlled] power])
   (simp add: adversary_initial_state_def)

lemma vu_saved_experiment_bound:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and power: "clength*scale=2^N"
 shows "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
    (vu_pair_event rT rC j N) adversary_initial_state \<le>
   nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*(ro_mca_weighted_semantic_base rT rC)^2+
   fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
 by (rule vu_program_bound[OF lc_program_ro_absorb_checked_staged_security_experiment_with_data_state[OF wf controlled] power])
   (simp add: adversary_initial_state_def)

lemma vu_decoded_pairI:
 assumes clean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap u))"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map (HashMap u))"
   and header: "as_header (HashMap u) (PState qs) data"
   and rt: "rt=staged_trace_root data"
   and ffs: "map snd ffs=staged_trace_fri_roots data"
   and cfs: "map snd cfs=staged_composition_fri_roots data"
   and lenf: "length ffs\<le>N" and lenc: "length cfs\<le>N"
   and counter: "PQueryCounter qs=j"
   and actual: "Some ((),qt)\<in>set_dist
     (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) qs)"
   and ext: "qt\<le>u"
   and lookp: "fmlookup (HashMap u) (QueryIndexChallenge j (PState qs))=Some z"
   and lookc: "fmlookup (HashMap u) (QueryIndexChallenge (Suc j) (PState qt))=Some x"
   and memberp: "index (to_nat z)\<in>weighted_semantic_indices rT rC (HashMap u) data"
   and memberc: "index (to_nat x)\<in>weighted_semantic_indices rT rC (HashMap u) data"
 shows "vu_pair_event rT rC j N (Some (result,u))"
proof -
 let ?U="HashMap u"
 let ?I="weighted_semantic_indices rT rC ?U data"
 obtain rest where shape: "weighted_semantic_header_shape data"
   and active: "staged_trace_fri_roots data\<noteq>[]"
   and before: "ro_absorb_lookup_chain (channel_for_hash_map ?U)
      (PState adversary_initial_state) (weighted_semantic_header data@rest) (PState qs)"
   using header unfolding as_header_def by blast
 obtain chunk where chain: "ro_absorb_lookup_chain qt (PState qs) chunk (PState qt)"
   by (rule ro_verifier_query_round_program_outcome_with_lookup_chain[OF actual]) blast
 have ext': "qt\<le>channel_for_hash_map ?U"
   using ext by (simp add: less_eq_hash_ext_def channel_for_hash_map_def)
 have route: "ro_absorb_lookup_chain (channel_for_hash_map ?U) (PState qs) chunk (PState qt)"
   by (rule ro_absorb_lookup_chain_mono[OF chain ext'])
 have after: "ro_absorb_lookup_chain (channel_for_hash_map ?U)
      (PState adversary_initial_state) (weighted_semantic_header data@(rest@chunk)) (PState qt)"
   using ro_absorb_lookup_chain_append[OF before route] by simp
 have readyp: "weighted_semantic_ready rT rC ?U (PState qs) ?I"
   using shape active before unfolding weighted_semantic_ready_def by blast
 have readyc: "weighted_semantic_ready rT rC ?U (PState qt) ?I"
   using shape active after unfolding weighted_semantic_ready_def by blast
 have hitp: "weighted_semantic_hit rT rC ?U (PState qs) z"
   using readyp memberp by (auto simp: weighted_semantic_hit_def query_index_raw_preimage_def)
 have hitc: "weighted_semantic_hit rT rC ?U (PState qt) x"
   using readyc memberc by (auto simp: weighted_semantic_hit_def query_index_raw_preimage_def)
 show ?thesis unfolding vu_pair_event_def
   apply (simp only: option.simps prod.case)
   apply (intro conjI clean initial)
   apply (rule exI[of _ "PState qs"], rule exI[of _ data], rule exI[of _ rt],
     rule exI[of _ ffs], rule exI[of _ fv], rule exI[of _ alphas],
     rule exI[of _ cfs], rule exI[of _ cv], rule exI[of _ "PState qt"],
     rule exI[of _ z], rule exI[of _ x], rule exI[of _ qs], rule exI[of _ qt])
   using header rt ffs cfs lenf lenc lookp lookc hitp hitc counter ext actual by simp
qed

definition vu_decoded_pair_event where
 "vu_decoded_pair_event rT rC j N out \<longleftrightarrow>
  (case out of None\<Rightarrow>False | Some (result,u)\<Rightarrow>
   \<not>hash_map_output_collision (channel_for_hash_map (HashMap u)) \<and>
   PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map (HashMap u)) \<and>
   (\<exists>data rt ffs fv alphas cfs cv z x qs qt.
    as_header (HashMap u) (PState qs) data \<and>
    rt=staged_trace_root data \<and> map snd ffs=staged_trace_fri_roots data \<and>
    map snd cfs=staged_composition_fri_roots data \<and> length ffs\<le>N \<and> length cfs\<le>N \<and>
    PQueryCounter qs=j \<and> qt\<le>u \<and>
    Some ((),qt)\<in>set_dist
      (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) qs) \<and>
    fmlookup (HashMap u) (QueryIndexChallenge j (PState qs))=Some z \<and>
    fmlookup (HashMap u) (QueryIndexChallenge (Suc j) (PState qt))=Some x \<and>
    index (to_nat z)\<in>weighted_semantic_indices rT rC (HashMap u) data \<and>
    index (to_nat x)\<in>weighted_semantic_indices rT rC (HashMap u) data))"

lemma vu_decoded_pair_subset:
 "vu_decoded_pair_event rT rC j N out \<Longrightarrow> vu_pair_event rT rC j N out"
 unfolding vu_decoded_pair_event_def
 by (auto intro: vu_decoded_pairI split: option.splits prod.splits)

lemma vu_original_decoded_pair_bound:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and power: "clength*scale=2^N"
 shows "wp_event (ro_absorb_checked_staged_security_experiment A)
    (vu_decoded_pair_event rT rC j N) adversary_initial_state \<le>
   nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*(ro_mca_weighted_semantic_base rT rC)^2+
   fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
proof -
 have "wp_event (ro_absorb_checked_staged_security_experiment A)
    (vu_decoded_pair_event rT rC j N) adversary_initial_state \<le>
   wp_event (ro_absorb_checked_staged_security_experiment A)
    (vu_pair_event rT rC j N) adversary_initial_state"
   unfolding wp_event_def by (rule wp_mono_on_support) (use vu_decoded_pair_subset in auto)
 also have "...\<le>nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*(ro_mca_weighted_semantic_base rT rC)^2+
   fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
   by (rule vu_original_experiment_bound[OF wf controlled power])
 finally show ?thesis .
qed

end

subsection \<open>Actual Initial Pair Replay\<close>

context soundness
begin

lemma vr_ntimes_extends:
 assumes out: "Some (results,t)\<in>set_dist
   (execute (ntimes (ro_verifier_query_round_program rt ffs fv alphas cfs cv) n) s)"
 shows "s\<le>t"
 using out
proof (induction n arbitrary: s results)
 case 0
 then show ?case by (simp add: hash_ext_refl)
next
 case (Suc n)
 obtain mid rest where first: "Some ((),mid)\<in>set_dist
    (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) s)"
   and tail: "Some (rest,t)\<in>set_dist
    (execute (ntimes (ro_verifier_query_round_program rt ffs fv alphas cfs cv) n) mid)"
   using Suc.prems by (auto elim!: set_dist_bindE)
 have first_ext: "s\<le>mid"
   using ro_verifier_query_round_program_outcome_extends_counter[OF first] by simp
 show ?case by (rule hash_ext_trans[OF first_ext Suc.IH[OF tail]])
qed

lemma vr_initial_decoded_pair:
 fixes final_state :: "'f protocol_channel"
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength"
   and builder_out: "Some (((prefix,prefix_state),data,query_start,raws,query_states),attacker_state)
     \<in>set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and verifier_out: "Some (results,final_state)\<in>set_dist (execute ro_verify_monad
     (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
   and clean: "\<not>hash_map_output_collision final_state"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values final_state"
   and two: "2\<le>rounds"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log (maxDegree+1)\<le>N"
   and memberp: "index (to_nat (raws!0))\<in>weighted_semantic_indices rT rC (HashMap final_state) data"
   and memberc: "index (to_nat (raws!1))\<in>weighted_semantic_indices rT rC (HashMap final_state) data"
 shows "vu_pair_event rT rC 0 N (Some (result,final_state))"
proof -
  from ro_checked_staged_transcript_program_with_first_root_outcomeE[
      OF builder_out]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              prefix)
            prefix_final)"
    and query_out:
      "Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots head_data)
              (staged_composition_fri_roots head_data)
              query_start 0 rounds)
            query_start)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    by blast

  obtain fr prefix_trace_bs first_root where
    prefix_eq: "prefix = (fr, prefix_trace_bs, first_root)"
    by (cases prefix) auto
  have prefix_props:
      "prefix_trace_bs = [] \<and>
       prefix_state = prefix_final \<and>
       adversary_initial_state \<le> prefix_final \<and>
       ro_absorb_lookup_chain prefix_final
         (PState adversary_initial_state) [fr, first_root]
         (PState prefix_final) \<and>
       PQueryCounter prefix_final = PQueryCounter adversary_initial_state"
    by (rule ro_staged_first_trace_fri_root_prefix_program_chain[
          OF wf controlled nonempty])
      (use prefix_out prefix_eq in simp)
  have after_fields:
      "staged_trace_root head_data = fr \<and>
       (\<exists>roots. staged_trace_fri_roots head_data = first_root # roots)"
    by (rule
        ro_checked_staged_after_first_trace_fri_root_prefix_program_fields[
          OF nonempty])
      (use after_out prefix_eq in simp)

  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
        ro_checked_staged_transcript_program_with_first_root_projection_outcome[
          OF nonempty builder_out])
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength \<and>
       length (staged_alphas data) = length spec \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       length (staged_composition_fri_challenges data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       ceil_log (to_nat (staged_degree data) + 1) \<le>
         ceil_log (maxDegree + 1) \<and>
       length (staged_query_chunks data) = rounds"
    by (rule ro_checked_staged_transcript_program_outcome_shape[
          OF original_out])
  have query_bound:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_props:
      "length raws = rounds \<and>
       length query_states = rounds \<and>
       length query_chunks = rounds \<and>
       query_start \<le> attacker_state \<and>
       PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
       (\<forall>j < rounds.
         query_states ! j \<le> attacker_state \<and>
         PQueryCounter (query_states ! j) =
           PQueryCounter query_start + j \<and>
         fmlookup (HashMap attacker_state)
           (QueryIndexChallenge
             (PQueryCounter (query_states ! j))
             (PState (query_states ! j))) =
           Some (raws ! j) \<and>
         verifier_query_round_chunk (index (to_nat (raws ! j)))
           (staged_trace_fri_roots head_data)
           (staged_composition_fri_roots head_data)
           (query_chunks ! j)) \<and>
       (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
    by (rule ro_checked_staged_query_program_with_witnesses_outcome[
          OF controlled query_bound query_out])

  have boundary_trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    using shape by simp
  have boundary_composition_len:
      "length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1)"
    using shape by simp
  have boundary_alphas_len:
      "length (staged_alphas data) = length spec"
    using shape by simp
  have boundary_query_idxs_len:
      "length (map (\<lambda>raw. index (to_nat raw)) raws) = rounds"
    using query_props by simp
  have boundary_chunks_len:
      "length (staged_query_chunks data) = rounds"
    using shape by simp
  have boundary_chunk_shapes:
      "\<forall>j < rounds.
        verifier_query_round_chunk
          (map (\<lambda>raw. index (to_nat raw)) raws ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)"
    using query_props data_eq by simp

  from ro_verify_monad_actual_query_boundaryE[
      OF nonempty boundary_trace_len boundary_composition_len
        boundary_alphas_len boundary_query_idxs_len boundary_chunks_len
        boundary_chunk_shapes verifier_out]
  obtain f_fl fl verifier_query_state verifier_fr f_final alphas final where
    verifier_fr_eq: "verifier_fr = staged_trace_root data"
    and trace_roots_eq:
      "map snd f_fl = staged_trace_fri_roots data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and f_fl_nonempty: "f_fl \<noteq> []"
    and verifier_query_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program verifier_fr f_fl f_final
                alphas fl final)
              rounds)
            verifier_query_state)"
    and verifier_transcript:
      "PTranscript verifier_query_state =
        List.concat (staged_query_chunks data)"
    and attacker_verifier_ext:
      "attacker_state \<le> verifier_query_state"
    and verifier_counter:

      "PQueryCounter verifier_query_state = 0"
    and verifier_chain:
      "ro_absorb_lookup_chain final_state (PState verifier_query_state)
        (List.concat (staged_query_chunks data)) (PState final_state)"
    and verifier_ext: "verifier_query_state \<le> final_state"
    .

  have attacker_final_ext: "attacker_state \<le> final_state"
    by (rule hash_ext_trans[OF attacker_verifier_ext verifier_ext])
  have builder_chain_attacker:
      "ro_absorb_lookup_chain attacker_state (PState query_start)
        (List.concat query_chunks) (PState attacker_state)"
    using ro_checked_staged_query_program_with_witnesses_absorb_lookup_chain[
      OF controlled query_bound query_out]
    by blast
  have builder_chain_final:
      "ro_absorb_lookup_chain final_state (PState query_start)
        (List.concat query_chunks) (PState attacker_state)"
    by (rule ro_absorb_lookup_chain_mono[
          OF builder_chain_attacker attacker_final_ext])

  have sync:
      "PState final_state = PState attacker_state \<and>
       PTranscript final_state = [] \<and>
       verifier_state_from_adversary attacker_state
         (staged_proof_transcript data) \<le> final_state \<and>
       PQueryCounter final_state = rounds"
    by (rule ro_checked_staged_transcript_program_ro_verify_monad_sync[
          OF wf controlled original_out verifier_out])
  have builder_chain_final':
      "ro_absorb_lookup_chain final_state (PState query_start)
        (List.concat (staged_query_chunks data)) (PState final_state)"
    using builder_chain_final sync data_eq by simp
  have verifier_builder_state:
      "PState verifier_query_state = PState query_start"
    by (rule ro_absorb_lookup_chain_start_functional_if_clean[
          OF clean verifier_chain builder_chain_final'])

  have good_fields:
      "prefix_state \<le> attacker_state \<and> PQueryCounter query_start = 0"
    by (rule
        ro_checked_staged_transcript_program_with_first_root_good_fields[
          OF wf controlled nonempty builder_out])

  have j0: "0<rounds" and j1: "1<rounds" using two by auto
  have clean_sent: "\<not>hash_map_output_collision attacker_state"
    using hash_map_output_collision_mono[OF _ attacker_final_ext] clean by blast
  note chain0=ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
    OF wf controlled nonempty builder_out clean_sent j0]
  note chain1=ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
    OF wf controlled nonempty builder_out clean_sent j1]
  have header_sent: "ro_absorb_lookup_chain attacker_state (PState adversary_initial_state)
      (weighted_semantic_header data) (PState query_start)"
    using chain0 by (simp add: weighted_semantic_header_def)
  have header_final: "ro_absorb_lookup_chain final_state (PState adversary_initial_state)
      (weighted_semantic_header data) (PState query_start)"
    by (rule ro_absorb_lookup_chain_mono[OF header_sent attacker_final_ext])
  have header_map: "ro_absorb_lookup_chain (channel_for_hash_map (HashMap final_state))
      (PState adversary_initial_state) (weighted_semantic_header data) (PState verifier_query_state)"
  proof -
    have maps: "HashMap (channel_for_hash_map (HashMap final_state))=HashMap final_state"
      by (simp add: channel_for_hash_map_def)
    show ?thesis
      using header_final by (simp only: ro_absorb_lookup_chain_cong_hash_map[OF maps] verifier_builder_state)
  qed
  have header: "as_header (HashMap final_state) (PState verifier_query_state) data"
    unfolding as_header_def
    using shape nonempty header_map
    by (auto simp: weighted_semantic_header_shape_def intro!: exI[of _ "[]"])
  obtain n where R: "rounds=Suc n" using j0 by (cases rounds) auto
  obtain mid rest_results where first: "Some ((),mid)\<in>set_dist
      (execute (ro_verifier_query_round_program verifier_fr f_fl f_final alphas fl final) verifier_query_state)"
    and rest_out: "Some (rest_results,final_state)\<in>set_dist
      (execute (ntimes (ro_verifier_query_round_program verifier_fr f_fl f_final alphas fl final) n) mid)"
    using verifier_query_out unfolding R by (auto elim!: set_dist_bindE)
  have mid_ext: "mid\<le>final_state" by (rule vr_ntimes_extends[OF rest_out])
  have chunk0: "verifier_query_round_chunk (index (to_nat (raws!0)))
      (staged_trace_fri_roots data) (staged_composition_fri_roots data)
      (staged_query_chunks data!0)"
    using boundary_chunk_shapes query_props j0 by simp
  have chunks_nonempty: "staged_query_chunks data\<noteq>[]" using shape j0 by auto
  have chunks_cons: "staged_query_chunks data=
      (staged_query_chunks data!0)#tl (staged_query_chunks data)"
    using chunks_nonempty by (cases "staged_query_chunks data") auto
  have first_tr: "PTranscript verifier_query_state=
      (staged_query_chunks data!0)@List.concat (tl (staged_query_chunks data))"
    using verifier_transcript by (subst (asm) chunks_cons) simp
  have aligned: "ro_absorb_lookup_chain mid (PState verifier_query_state)
      (staged_query_chunks data!0) (PState mid)"
    using ro_verifier_query_round_program_aligns_expected_chunk[
      OF chunk0 first_tr trace_roots_eq[symmetric] composition_roots_eq[symmetric] first] by blast
  have aligned_final: "ro_absorb_lookup_chain final_state (PState query_start)
      (staged_query_chunks data!0) (PState mid)"
    using ro_absorb_lookup_chain_mono[OF aligned mid_ext] verifier_builder_state by simp
  have child_sent: "ro_absorb_lookup_chain attacker_state (PState query_start)
      (staged_query_chunks data!0) (PState (query_states!1))"
    using chain1 by (subst (asm) chunks_cons) simp
  have child_final: "ro_absorb_lookup_chain final_state (PState query_start)
      (staged_query_chunks data!0) (PState (query_states!1))"
    by (rule ro_absorb_lookup_chain_mono[OF child_sent attacker_final_ext])
  have child_state: "PState mid=PState (query_states!1)"
    by (rule ro_absorb_lookup_chain_functional[OF aligned_final child_final])
  have parent_state: "PState (query_states!0)=PState query_start"
    using chain0 by simp
  have parent_sent: "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge 0 (PState verifier_query_state))=Some (raws!0)"
    using query_props good_fields j0 parent_state verifier_builder_state
    apply simp
    by metis
  have child_sent_lookup: "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge 1 (PState mid))=Some (raws!1)"
    using query_props good_fields j1 child_state
    apply simp
    by metis
  have parent_lookup: "fmlookup (HashMap final_state)
      (QueryIndexChallenge 0 (PState verifier_query_state))=Some (raws!0)"
    by (rule hash_extension_lookup[OF parent_sent attacker_final_ext])
  have child_lookup: "fmlookup (HashMap final_state)
      (QueryIndexChallenge (Suc 0) (PState mid))=Some (raws!1)"
    using hash_extension_lookup[OF child_sent_lookup attacker_final_ext] by simp
  have lenff: "length f_fl\<le>N" using trace_roots_eq shape lenf by (metis length_map)
  have lenfl: "length fl\<le>N" using composition_roots_eq shape lenc by (metis length_map order_trans)
  have mapclean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap final_state))"
    using clean by (simp add: hash_map_output_collision_def channel_for_hash_map_def)
  have mapinitial: "PState adversary_initial_state\<notin>hash_map_output_values
      (channel_for_hash_map (HashMap final_state))"
    using initial by (simp add: hash_map_output_values_def channel_for_hash_map_def)
  show ?thesis
    by (rule vu_decoded_pairI[OF mapclean mapinitial header verifier_fr_eq trace_roots_eq
        composition_roots_eq lenff lenfl verifier_counter first mid_ext parent_lookup
        child_lookup memberp memberc])
qed

lemma vr_original_semantic_list_pair:
 fixes final_state :: "'f protocol_channel"
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength"
   and builder_out: "Some (((prefix,prefix_state),data,query_start,raws,query_states),attacker_state)
     \<in>set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and verifier_out: "Some (results,final_state)\<in>set_dist (execute ro_verify_monad
     (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
   and clean: "\<not>hash_map_output_collision final_state"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values final_state"
   and two: "2\<le>rounds"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log (maxDegree+1)\<le>N"

   and no_trace: "\<not>hash_map_new_output_hit
     (first_trace_fri_root_prefix_merkle_targets prefix prefix_state) prefix_state final_state"
   and no_comp: "\<not>hash_map_new_output_hit
     (ro_actual_query_composition_prefix_targets data query_start) query_start final_state"
   and list_hit: "map (\<lambda>raw. index (to_nat raw)) raws\<in>
     ro_mca_decoded_semantic_query_lists rT rC prefix prefix_state data query_start"
 shows "vu_pair_event rT rC 0 N (Some (result,final_state))"
proof -
 have original_out: "Some (data,attacker_state)\<in>set_dist
     (execute (ro_checked_staged_transcript_program A) adversary_initial_state)"
   by (rule ro_checked_staged_transcript_program_with_first_root_projection_outcome[OF nonempty builder_out])
 have transfer: "attacker_state\<le>verifier_state_from_adversary attacker_state (staged_proof_transcript data)"
   by (rule hash_extends_verifier_state_from_adversary_right) (rule hash_ext_refl)
 have replay: "verifier_state_from_adversary attacker_state (staged_proof_transcript data)\<le>final_state"
   using ro_checked_staged_transcript_program_ro_verify_monad_sync[OF wf controlled original_out verifier_out] by blast
 have af: "attacker_state\<le>final_state" by (rule hash_ext_trans[OF transfer replay])
 have ac: "\<not>hash_map_output_collision attacker_state"
   using hash_map_output_collision_mono[OF _ af] clean by blast
 have pa: "prefix_state\<le>attacker_state"
   using ro_checked_staged_transcript_program_with_first_root_good_fields[OF wf controlled nonempty builder_out] by blast
 have qa: "query_start\<le>attacker_state"
   using ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[OF wf controlled builder_out] by blast
 have j0: "0<rounds" using two by simp
 have pref: "prefix=(staged_trace_root data,[],hd (staged_trace_fri_roots data))"
   using ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
     OF wf controlled nonempty builder_out ac j0] by blast
 note facts=af ac pa qa pref
 have su: "prefix_state\<le>final_state" by (rule hash_ext_trans[OF facts(3) facts(1)])
 have qu: "query_start\<le>final_state" by (rule hash_ext_trans[OF facts(4) facts(1)])
 have prefix_clean: "\<not>hash_map_output_collision prefix_state"
   using hash_map_output_collision_mono[OF _ su] clean by blast
 have transport: "ro_mca_decoded_semantic_query_indices rT rC prefix prefix_state data query_start=
     weighted_semantic_indices rT rC (HashMap final_state) data"
   by (rule weighted_semantic_transport[OF facts(5) su qu prefix_clean no_trace no_comp])
 have len: "length raws=rounds" and members:
   "\<forall>raw\<in>set raws. index (to_nat raw)\<in>ro_mca_decoded_semantic_query_indices rT rC prefix prefix_state data query_start"
   using list_hit unfolding ro_mca_decoded_semantic_query_lists_def fri_conditioned_query_lists_def by auto
 have mem0: "raws!0\<in>set raws" and mem1: "raws!1\<in>set raws"
   using len two by (auto intro: nth_mem)
 have p: "index (to_nat (raws!0))\<in>weighted_semantic_indices rT rC (HashMap final_state) data"
   using members mem0 transport by blast
 have c: "index (to_nat (raws!1))\<in>weighted_semantic_indices rT rC (HashMap final_state) data"
   using members mem1 transport by blast
 show ?thesis
   by (rule vr_initial_decoded_pair[OF wf controlled nonempty builder_out verifier_out clean initial
       two lenf lenc p c])
qed

lemma vr_pair_map:
 fixes m :: "('a, 'f protocol_channel) state_monad"
 shows "wp_event (m \<bind> (\<lambda>x. return (f x))) (vu_pair_event rT rC j N) s=
   wp_event m (vu_pair_event rT rC j N) s"
proof -
 have pair: "vu_pair_event rT rC j N (Some (f x,t))=vu_pair_event rT rC j N (Some (x,t))" for x t
   by (simp only: vu_pair_event_def option.simps prod.case)
 have none: "\<not>vu_pair_event rT rC j N None"
   by (simp add: vu_pair_event_def)
 show ?thesis unfolding wp_event_def wp_bind_return_map
   apply (rule arg_cong[where f="\<lambda>P. wp m P s"], rule ext)
   subgoal for out
     by (cases out) (auto simp only: option.simps prod.case pair none split: prod.splits)
   done
qed

lemma vr_witness_pair_probability:
 "wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (vu_pair_event rT rC j N) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
    (vu_pair_event rT rC j N) s"
proof -
 have a: "wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
    (vu_pair_event rT rC j N) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (vu_pair_event rT rC j N) s"
   using vr_pair_map[where m="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
     and f="\<lambda>(((prefix_with_state,data,query_start,raws,query_states),attacker_state),result).
       (((data,query_start,raws,query_states),attacker_state),result)"
     and rT=rT and rC=rC and j=j and N=N and s=s]
   by (simp only: split_def ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection_all_rounds[unfolded split_def])
 have b: "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
    (vu_pair_event rT rC j N) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
    (vu_pair_event rT rC j N) s"
   using vr_pair_map[where m="ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
     and f="\<lambda>(((data,query_start,raws,query_states),attacker_state),result).
       ((data,attacker_state),result)"
     and rT=rT and rC=rC and j=j and N=N and s=s]
   by (simp only: split_def ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection[unfolded split_def])
 show ?thesis using a b by simp
qed

definition vr_clean_semantic_event where
 "vr_clean_semantic_event rT rC out \<longleftrightarrow>
  (case out of None\<Rightarrow>False |
   Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)\<Rightarrow>
    \<not>hash_map_output_collision u \<and>
    PState adversary_initial_state\<notin>hash_map_output_values u \<and>
    \<not>hash_map_new_output_hit
      (first_trace_fri_root_prefix_merkle_targets prefix prefix_state) prefix_state u \<and>
    \<not>hash_map_new_output_hit
      (ro_actual_query_composition_prefix_targets data query_start) query_start u \<and>
    map (\<lambda>raw. index (to_nat raw)) raws\<in>
      ro_mca_decoded_semantic_query_lists rT rC prefix prefix_state data query_start)"

lemma vr_clean_semantic_on_support:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength"
   and two: "2\<le>rounds"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log (maxDegree+1)\<le>N"
   and supported: "out\<in>set_dist (execute
     (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and event: "vr_clean_semantic_event rT rC out"
 shows "vu_pair_event rT rC 0 N out"
proof -
 obtain prefix prefix_state data query_start raws query_states attacker_state results u where
   out: "out=Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)"
   and clean: "\<not>hash_map_output_collision u"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values u"
   and no_trace: "\<not>hash_map_new_output_hit
      (first_trace_fri_root_prefix_merkle_targets prefix prefix_state) prefix_state u"
   and no_comp: "\<not>hash_map_new_output_hit
      (ro_actual_query_composition_prefix_targets data query_start) query_start u"
   and hit: "map (\<lambda>raw. index (to_nat raw)) raws\<in>
      ro_mca_decoded_semantic_query_lists rT rC prefix prefix_state data query_start"
   using event unfolding vr_clean_semantic_event_def by (auto split: option.splits prod.splits)
 have support': "Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)
   \<in>set_dist (execute
     (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
       adversary_initial_state)" using supported out by simp
 have pair: "vu_pair_event rT rC 0 N
     (Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u))"
 proof (rule ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_outcomeE[OF support'])
  assume builder: "Some (((prefix,prefix_state),data,query_start,raws,query_states),attacker_state)
     \<in>set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and verifier: "Some (results,u)\<in>set_dist (execute ro_verify_monad
     (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
  show ?thesis
    by (rule vr_original_semantic_list_pair[OF wf controlled nonempty builder verifier clean initial two
        lenf lenc no_trace no_comp hit])
 qed
 show ?thesis using pair out by simp
qed

lemma vr_clean_semantic_bound:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength"
   and two: "2\<le>rounds"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log (maxDegree+1)\<le>N"
   and power: "clength*scale=2^N"
 shows "wp_event
    (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (vr_clean_semantic_event rT rC) adversary_initial_state \<le>
   nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*(ro_mca_weighted_semantic_base rT rC)^2+
   fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
proof -
 let ?run="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
 have "wp_event ?run (vr_clean_semantic_event rT rC) adversary_initial_state\<le>
     wp_event ?run (vu_pair_event rT rC 0 N) adversary_initial_state"
   unfolding wp_event_def
   by (rule wp_mono_on_support)
     (use vr_clean_semantic_on_support[OF wf controlled nonempty two lenf lenc] in auto)
 also have "...=wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
     (vu_pair_event rT rC 0 N) adversary_initial_state" by (rule vr_witness_pair_probability)
 also have "...\<le>nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*(ro_mca_weighted_semantic_base rT rC)^2+
   fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
   by (rule vu_saved_experiment_bound[OF wf controlled power])
 finally show ?thesis .
qed

lemma vr_head_data_lists:
 "ro_mca_decoded_semantic_query_lists rT rC prefix prefix_state (ro_query_head_data data) query_start=
  ro_mca_decoded_semantic_query_lists rT rC prefix prefix_state data query_start"
proof -
 have candidate: "ro_actual_query_composition_candidate (ro_query_head_data data) query_start=
     ro_actual_query_composition_candidate data query_start"
   by (simp add: ro_query_head_data_def ro_actual_query_composition_candidate_def)
 have degree: "to_nat (staged_degree (ro_query_head_data data))=to_nat (staged_degree data)"
   by (simp add: ro_query_head_data_def)
 have alphas: "staged_alphas (ro_query_head_data data)=staged_alphas data"
   by (simp add: ro_query_head_data_def)
 have indices: "ro_actual_query_trace_composition_accepted_indices prefix prefix_state (ro_query_head_data data) query_start=
     ro_actual_query_trace_composition_accepted_indices prefix prefix_state data query_start"
   by (simp add: ro_actual_query_trace_composition_accepted_indices_def
      ro_query_head_data_def ro_actual_query_composition_candidate_def)
 show ?thesis unfolding ro_mca_decoded_semantic_query_lists_def ro_mca_decoded_semantic_query_indices_def
   by (simp only: candidate degree alphas indices)
qed

lemma vr_original_event_guarded_iff:
 "vr_clean_semantic_event rT rC
    (Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)) \<longleftrightarrow>
  \<not>hash_map_output_collision u \<and>
  PState adversary_initial_state\<notin>hash_map_output_values u \<and>
  \<not>hash_map_new_output_hit
    (first_trace_fri_root_prefix_merkle_targets prefix prefix_state) prefix_state u \<and>
  \<not>hash_map_new_output_hit
    (ro_actual_query_composition_prefix_targets data query_start) query_start u \<and>
  ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
    (ro_mca_decoded_semantic_query_lists rT rC)
    (Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u))"
 unfolding vr_clean_semantic_event_def
   ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
   ro_query_head_dependent_actual_query_index_list_hit_def
 by (simp only: option.simps prod.case vr_head_data_lists)

end

end
