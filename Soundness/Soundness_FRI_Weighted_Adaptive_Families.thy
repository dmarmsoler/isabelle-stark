(* Title: Stark/Soundness_FRI_Weighted_Adaptive_Families.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Adaptive_Families
  imports
    "Soundness_FRI_Weighted_Finite_Candidates"
begin

section \<open>Adaptive Families for weighted MCA soundness\<close>

text \<open>Canonical families can be selected adaptively at authenticated header births. Their initial score is charged per possible birth; no fixed-header or challenge-before-query restriction is imposed on the adversary.\<close>

subsection \<open>Actual Experiment Applicability\<close>

context soundness
begin

text \<open>A two-call admissible stage can precompute the next absorbed prefix
and its query key. This is an interface test, not an accepting execution.\<close>

definition ea_precompute ::
  "'f \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> ('f, 'f protocol_channel) state_monad" where
  "ea_precompute st msg j = do {
    v \<leftarrow> hash (TranscriptAbsorb st msg);
    x \<leftarrow> hash (QueryIndexChallenge j v);
    return msg}"

lemma ea_precompute_controlled:
  "controlled_ro_program 2 (ea_precompute st msg j)"
  unfolding ea_precompute_def
  using controlled_ro_program.Query controlled_ro_program.Return
  by (auto simp: numeral_2_eq_2)

lemma ea_precompute_outcome:
  assumes out: "Some (result,t)\<in>set_dist (execute (ea_precompute st msg j) s)"
  obtains v x where "result=msg" "PState t=PState s" "PQueryCounter t=PQueryCounter s"
    "fmlookup (HashMap t) (TranscriptAbsorb st msg)=Some v"
    "fmlookup (HashMap t) (QueryIndexChallenge j v)=Some x"
proof -
  obtain v u x w where
    first: "Some (v,u)\<in>set_dist (execute (hash (TranscriptAbsorb st msg)) s)"
    and second: "Some (x,w)\<in>set_dist (execute (hash (QueryIndexChallenge j v)) u)"
    and ret: "result=msg" "t=w"
    using out unfolding ea_precompute_def by (auto elim!: set_dist_bindE)
  have stored: "fmlookup (HashMap t) (TranscriptAbsorb st msg)=Some v"
    using hash_extension_lookup[OF hash_outcome(2)[OF first] hash_outcome(1)[OF second]]
    by (simp add: ret)
  show ?thesis
    by (rule that[OF ret(1) _ _ stored])
      (use hash_channel_preserves[OF first] hash_channel_preserves[OF second]
        hash_outcome(2)[OF second] ret in auto)
qed

lemma ea_record_known:
  assumes key: "fmlookup (HashMap s) (TranscriptAbsorb (PState s) msg)=Some v"
    and out: "Some ((),t)\<in>set_dist (execute (ro_record_staged_message msg) s)"
  shows "PState t=v" "PQueryCounter t=PQueryCounter s"
    "s\<le>t"
proof -
  obtain a u where hashed:
    "Some (a,u)\<in>set_dist (execute (hash (TranscriptAbsorb (PState s) msg)) s)"
    and t: "t=u\<lparr>PState:=a,PTranscript:=PTranscript u@[msg]\<rparr>"
    and counter: "PQueryCounter u=PQueryCounter s"
    by (rule ro_record_staged_message_outcome[OF out]) auto
  have ext: "s\<le>u" by (rule hash_outcome(1)[OF hashed])
  have "a=v" using hash_extension_lookup[OF key ext] hash_outcome(2)[OF hashed] by simp
  then show "PState t=v" by (simp add: t)
  show "PQueryCounter t=PQueryCounter s" by (simp add: t counter)
  show "s\<le>t" using ext by (simp add: t less_eq_hash_ext_def)
qed

lemma ea_precompute_then_record_cached:
  assumes st: "PState s=st" and count: "PQueryCounter s=j"
    and out: "Some ((),t)\<in>set_dist
      (execute (ea_precompute st msg j \<bind> ro_record_staged_message) s)"
  shows "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter t) (PState t)) \<noteq> None"
proof -
  obtain result u where first:
    "Some (result,u)\<in>set_dist (execute (ea_precompute st msg j) s)"
    and recorded: "Some ((),t)\<in>set_dist (execute (ro_record_staged_message result) u)"
    using out by (auto elim!: set_dist_bindE)
  obtain v x where result: "result=msg"
    and fields: "PState u=PState s" "PQueryCounter u=PQueryCounter s"
    and absorb: "fmlookup (HashMap u) (TranscriptAbsorb st msg)=Some v"
    and query: "fmlookup (HashMap u) (QueryIndexChallenge j v)=Some x"
    by (rule ea_precompute_outcome[OF first])
  have key: "fmlookup (HashMap u) (TranscriptAbsorb (PState u) msg)=Some v"
    using absorb by (simp add: fields st)
  note props=ea_record_known[OF key recorded[unfolded result]]
  show ?thesis using hash_extension_lookup[OF query props(3)] props(1,2) fields count by simp
qed

lemma ea_precompute_support:
  assumes empty: "HashMap s=fmempty"
  shows "Some (msg,s\<lparr>HashMap:=fmupd (QueryIndexChallenge j v) x
    (fmupd (TranscriptAbsorb st msg) v fmempty)\<rparr>)
    \<in>set_dist (execute (ea_precompute st msg j) s)"
proof -
  let ?u="s\<lparr>HashMap:=fmupd (TranscriptAbsorb st msg) v fmempty\<rparr>"
  have first: "Some (v,?u)\<in>set_dist (execute (hash (TranscriptAbsorb st msg)) s)"
    using hash_fresh_outcome[of s "TranscriptAbsorb st msg" v] empty by simp
  have second: "Some (x,?u\<lparr>HashMap:=fmupd (QueryIndexChallenge j v) x (HashMap ?u)\<rparr>)
    \<in>set_dist (execute (hash (QueryIndexChallenge j v)) ?u)"
    by (rule hash_fresh_outcome) simp
  show ?thesis unfolding ea_precompute_def
    by (rule set_dist_bindI[OF first], rule set_dist_bindI[OF second]) simp
qed

lemma ea_two_entry_clean:
  assumes distinct: "v\<noteq>x"
  shows "\<not>hash_map_output_collision
    (s\<lparr>HashMap:=fmupd (QueryIndexChallenge j v) x
      (fmupd (TranscriptAbsorb st msg) v fmempty)\<rparr>)"
  using distinct unfolding hash_map_output_collision_def
  by (auto split: if_splits)

lemma ea_old_parent_not_selected:
  assumes history: "fc_history M hist (HashMap u)"
    and old: "fmlookup M (QueryIndexChallenge j start)=Some raw"
  shows "\<not> fc_selected_event rT rC rt ffs fv alphas cfs cv start j
    (Some ((acc,hist),u))"
proof
  assume selected: "fc_selected_event rT rC rt ffs fv alphas cfs cv start j
    (Some ((acc,hist),u))"
  obtain pre mid post parent_first Mc v x Mr z where
    hist: "hist=pre@(if parent_first then [(Mr,QueryIndexChallenge j start,z)]@mid@[(Mc,QueryIndexChallenge (Suc j) v,x)]
      else [(Mc,QueryIndexChallenge (Suc j) v,x)]@mid@[(Mr,QueryIndexChallenge j start,z)])@post"
    and fresh: "fmlookup Mr (QueryIndexChallenge j start)=None"
    using selected unfolding fc_selected_event_def by (auto simp: Let_def)
  have member: "(Mr,QueryIndexChallenge j start,z)\<in>set hist"
    by (simp add: hist split: if_splits)
  have "\<not>ep_fresh (QueryIndexChallenge j start) (Mr,QueryIndexChallenge j start,z)"
    by (rule fc_history_old_not_fresh[OF history old member])
  then show False using fresh by (simp add: ep_fresh_def)
qed

text \<open>A target chosen to equal a just-returned hash answer is not a
predictable singleton target. This diagnostic is not a residual estimate.\<close>

lemma ea_retrospective_singleton_target:
  assumes fresh: "fmlookup (HashMap s) k=None"
  shows "wp_event (hash k)
    (\<lambda>out. case out of None \<Rightarrow> False | Some (x,t) \<Rightarrow> hash_map_new_output_hit {x} s t) s = 1"
proof -
  have hit: "\<And>x. hash_map_new_output_hit {x} s
    (s\<lparr>HashMap:=fmupd k x (HashMap s)\<rparr>)"
    using fresh unfolding hash_map_new_output_hit_def
    by (intro exI[where x=k]) auto
  have total: "dist_expect (hash_dist k s) (\<lambda>x. (1::prob))=1"
    unfolding dist_expect_def by (simp add: sum_map_def[symmetric])
  show ?thesis by (simp add: wp_event_def wp_hash hit total)
qed

lemma ea_header_fields_at_prefix_unique:
  assumes clean: "\<not>hash_map_output_collision (channel_for_hash_map M)"
    and initial: "PState adversary_initial_state \<notin> hash_map_output_values (channel_for_hash_map M)"
    and shape: "weighted_semantic_header_shape a" "weighted_semantic_header_shape b"
    and chains:
      "ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
        (weighted_semantic_header a @ ar) st"
      "ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
        (weighted_semantic_header b @ br) st"
  shows "staged_trace_root b=staged_trace_root a \<and>
    staged_trace_fri_roots b=staged_trace_fri_roots a \<and>
    staged_trace_final b=staged_trace_final a \<and>
    staged_alphas b=staged_alphas a \<and> staged_degree b=staged_degree a \<and>
    staged_composition_fri_roots b=staged_composition_fri_roots a \<and>
    staged_composition_final b=staged_composition_final a \<and> br=ar"
proof -
  have eq: "weighted_semantic_header a @ ar=weighted_semantic_header b @ br"
    by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[OF clean initial chains])
  show ?thesis by (rule weighted_semantic_header_parse[OF shape eq])
qed
lemma ea_route_roots_cong:
  assumes roots: "map snd ffs=map snd ffs'" "map snd cfs=map snd cfs'"
  shows "pair_route_fiber S rt ffs cfs start u v =
    pair_route_fiber S rt ffs' cfs' start u v"
  unfolding pair_route_fiber_def
  by (simp only: serial_round_roots_cong[OF roots])

lemma ea_fiber_roots_cong:
  assumes roots: "map snd ffs=map snd ffs'" "map snd cfs=map snd cfs'"
  shows "fc_fiber S rt ffs cfs start j e = fc_fiber S rt ffs' cfs' start j e"
  unfolding fc_fiber_def by (simp only: ea_route_roots_cong[OF roots])

lemma ea_account_roots_cong:
  assumes roots: "map snd ffs=map snd ffs'" "map snd cfs=map snd cfs'"
  shows "fc_step rT rC S rt ffs cfs start j acc e =
    fc_step rT rC S rt ffs' cfs' start j acc e"
  by (cases acc) (simp_all only: fc_step.simps ea_fiber_roots_cong[OF roots])

lemma ea_precompute_and_record_no_failure:
  "None\<notin>dom (dist (execute
    (ea_precompute st msg j \<bind> ro_record_staged_message) s))"
  unfolding ea_precompute_def ro_record_staged_message_def
  by (intro no_failure_bindI) (simp_all add: hash_no_failure)

end

subsection \<open>Adaptive Family Birth\<close>

context soundness
begin

lemma ab_old_query_target:
  assumes "fmlookup M (QueryIndexChallenge j v)=Some x"
  shows "v\<in>weighted_semantic_interval_targets M"
  using assms unfolding weighted_semantic_interval_targets_def query_index_state_values_def by blast

lemma ab_chain_start_target:
  assumes "ro_absorb_lookup_chain (channel_for_hash_map M) start xs v"
    and "v\<in>weighted_semantic_interval_targets M"
  shows "start\<in>weighted_semantic_interval_targets M"
  using assms
  by (cases xs) (auto simp: channel_for_hash_map_def
    weighted_semantic_interval_targets_def transcript_absorb_input_values_def)

lemma ab_no_old_child_connection:
  assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    and nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
      (channel_for_hash_map M) (channel_for_hash_map U)"
    and new: "start\<notin>weighted_semantic_interval_targets M"
    and route: "ro_absorb_lookup_chain (channel_for_hash_map U) start xs v"
  shows "fmlookup M (QueryIndexChallenge j v)=None"
proof (rule ccontr)
  assume "fmlookup M (QueryIndexChallenge j v)\<noteq>None"
  then obtain x where cached: "fmlookup M (QueryIndexChallenge j v)=Some x" by auto
  have target: "v\<in>weighted_semantic_interval_targets M" by (rule ab_old_query_target[OF cached])
  have inputs: "transcript_absorb_input_values (HashMap (channel_for_hash_map M))
    \<subseteq>weighted_semantic_interval_targets M"
    unfolding weighted_semantic_interval_targets_def channel_for_hash_map_def by auto
  have old: "ro_absorb_lookup_chain (channel_for_hash_map M) start xs v"
    by (rule weighted_semantic_absorb_interval_pullback[OF ext inputs nt route target])
  show False using ab_chain_start_target[OF old target] new by contradiction
qed

lemma ab_no_old_parent:
  assumes "start\<notin>weighted_semantic_interval_targets M"
  shows "fmlookup M (QueryIndexChallenge j start)=None"
  using assms ab_old_query_target by (metis option.exhaust)

lemma ab_stored_endpoint_chain_recovery:
  assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
    and stored: "fmlookup M k=Some start"
    and nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
      (channel_for_hash_map M) (channel_for_hash_map U)"
    and chain: "ro_absorb_lookup_chain (channel_for_hash_map U) initial xs start"
  shows "ro_absorb_lookup_chain (channel_for_hash_map M) initial xs start"
proof (cases xs rule: rev_cases)
  case Nil
  then show ?thesis using chain by simp
next
  case (snoc ys msg)
  obtain mid where before: "ro_absorb_lookup_chain (channel_for_hash_map U) initial ys mid"
    and last: "fmlookup U (TranscriptAbsorb mid msg)=Some start"
    using ro_absorb_lookup_chain_snoc[OF chain[unfolded snoc]]
    by (auto simp: channel_for_hash_map_def)
  have oldlookup: "fmlookup (HashMap (channel_for_hash_map M)) k=Some start"
    using stored by (simp add: channel_for_hash_map_def)
  have keep: "fmlookup U k=Some start"
    using hash_extension_lookup[OF oldlookup ext] by (simp add: channel_for_hash_map_def)
  have key: "k=TranscriptAbsorb mid msg"
    using clean keep last unfolding hash_map_output_collision_def channel_for_hash_map_def
    by auto
  have oldlast: "fmlookup M (TranscriptAbsorb mid msg)=Some start" using stored key by simp
  have target: "mid\<in>weighted_semantic_interval_targets M"
    using oldlast unfolding weighted_semantic_interval_targets_def transcript_absorb_input_values_def by blast
  have inputs: "transcript_absorb_input_values (HashMap (channel_for_hash_map M))
    \<subseteq>weighted_semantic_interval_targets M"
    unfolding weighted_semantic_interval_targets_def channel_for_hash_map_def by auto
  have oldbefore: "ro_absorb_lookup_chain (channel_for_hash_map M) initial ys mid"
    by (rule weighted_semantic_absorb_interval_pullback[OF ext inputs nt before target])
  show ?thesis unfolding snoc
    using ro_absorb_lookup_chain_append[OF oldbefore, of "[msg]" start] oldlast
    by (simp add: channel_for_hash_map_def)
qed

lemma ab_semantic_ready_at_stored_endpoint:
  assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
    and stored: "fmlookup M k=Some start"
    and nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
      (channel_for_hash_map M) (channel_for_hash_map U)"
    and ready: "weighted_semantic_ready rT rC U start I"
  shows "weighted_semantic_ready rT rC M start I"
proof -
  obtain data rest where shape: "weighted_semantic_header_shape data"
    and active: "staged_trace_fri_roots data\<noteq>[]"
    and chain: "ro_absorb_lookup_chain (channel_for_hash_map U)
      (PState adversary_initial_state) (weighted_semantic_header data@rest) start"
    and I: "I=weighted_semantic_indices rT rC U data"
    using ready unfolding weighted_semantic_ready_def by blast
  have old: "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state) (weighted_semantic_header data@rest) start"
    by (rule ab_stored_endpoint_chain_recovery[OF ext clean stored nt chain])
  have header: "set (weighted_semantic_header data)\<subseteq>transcript_absorb_message_values M"
    using ro_absorb_lookup_chain_messages_subset[OF old] by auto
  have tables: "\<And>rt. rt\<in>set (weighted_semantic_header data) \<Longrightarrow>
    conceptual_table (channel_for_hash_map M) rt (scale*clength)=
    conceptual_table (channel_for_hash_map U) rt (scale*clength)"
  proof -
    fix rt
    assume rt: "rt\<in>set (weighted_semantic_header data)"
    have sub: "merkle_prefix_path_targets {rt} (channel_for_hash_map M)\<subseteq>weighted_semantic_interval_targets M"
      using header rt unfolding merkle_prefix_path_targets_def weighted_semantic_interval_targets_def by blast
    have nt': "\<not>hash_map_new_output_hit (merkle_prefix_path_targets {rt} (channel_for_hash_map M))
      (channel_for_hash_map M) (channel_for_hash_map U)"
      using hash_map_new_output_hit_subset[OF sub] nt by blast
    show "conceptual_table (channel_for_hash_map M) rt (scale*clength)=
      conceptual_table (channel_for_hash_map U) rt (scale*clength)"
      using conceptual_table_prefix_stable_if_no_target[OF ext nt'] by simp
  qed
  have indices: "I=weighted_semantic_indices rT rC M data"
    using I weighted_semantic_map_cong[OF active tables] by simp
  show ?thesis unfolding weighted_semantic_ready_def using shape active old indices by blast
qed

lemma ab_birth_excludes_old_queries:
  assumes history: "fc_history M ((M,TranscriptAbsorb pred msg,start)#es) U"
    and nob: "fc_no_bad {} ((M,TranscriptAbsorb pred msg,start)#es)"
    and fresh: "fmlookup M (TranscriptAbsorb pred msg)=None"
    and route: "ro_absorb_lookup_chain (channel_for_hash_map U) start xs v"
  shows "fmlookup (fmupd (TranscriptAbsorb pred msg) start M) (QueryIndexChallenge j start)=None"
    "fmlookup (fmupd (TranscriptAbsorb pred msg) start M) (QueryIndexChallenge i v)=None"
proof -
  have new: "start\<notin>weighted_semantic_interval_targets M"
    using nob fresh by (simp add: fc_no_bad_def fc_bad_record_def fc_target_def)
  have ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    by (rule fc_history_extension[OF history])
  have nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
      (channel_for_hash_map M) (channel_for_hash_map U)"
    using fc_history_no_target_hit[OF history nob] by (simp add: fc_target_def)
  show "fmlookup (fmupd (TranscriptAbsorb pred msg) start M) (QueryIndexChallenge j start)=None"
    using ab_no_old_parent[OF new] by simp
  show "fmlookup (fmupd (TranscriptAbsorb pred msg) start M) (QueryIndexChallenge i v)=None"
    using ab_no_old_child_connection[OF ext nt new route] by simp
qed

lemma ab_no_bad_stored_targets:
  assumes history: "fc_history M es U"
    and nob: "fc_no_bad {} es"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
    and stored: "fmlookup M k=Some start"
    and roots: "R\<subseteq>weighted_semantic_interval_targets M\<union>{start}"
  shows "fc_no_bad R es"
proof (unfold fc_no_bad_def, intro ballI)
  fix e
  assume member: "e\<in>set es"
  obtain Me q x where e: "e=(Me,q,x)" by (cases e) auto
  have props: "channel_for_hash_map M\<le>channel_for_hash_map Me"
    "fmlookup U q=Some x"
    using fc_history_member[OF history member] by (auto simp: e)
  have ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    by (rule fc_history_extension[OF history])
  have old: "fmlookup (HashMap (channel_for_hash_map M)) k=Some start"
    using stored by (simp add: channel_for_hash_map_def)
  have keep: "fmlookup U k=Some start"
    using hash_extension_lookup[OF old ext] by (simp add: channel_for_hash_map_def)
  have kt: "fmlookup Me k=Some start"
    using hash_extension_lookup[OF old props(1)] by (simp add: channel_for_hash_map_def)
  have mono: "weighted_semantic_interval_targets M\<subseteq>weighted_semantic_interval_targets Me"
    using fc_target_mono[OF props(1), where R="{}"] by (simp add: fc_target_def)
  have noT: "\<not>fc_bad_record {} e" using nob member by (auto simp: fc_no_bad_def)
  show "\<not>fc_bad_record R e"
  proof
    assume bad: "fc_bad_record R e"
    have fresh: "fmlookup Me q=None" and hit: "x\<in>R"
      using bad noT by (auto simp: e fc_bad_record_def fc_target_def)
    have eq: "x=start" using roots hit mono noT fresh
      by (auto simp: e fc_bad_record_def fc_target_def)
    have qk: "q=k"
      using clean props(2) keep eq
      unfolding hash_map_output_collision_def channel_for_hash_map_def by auto
    show False using fresh kt qk by simp
  qed
qed

end

subsection \<open>Adaptive Family Portfolio\<close>

datatype 'a ap_family = AP_Family "'a set" 'a "('a\<times>'a) list" "('a\<times>'a) list" 'a nat

context soundness
begin

fun ap_valid where
  "ap_valid rT rC (AP_Family S rt ffs cfs start j,acc) =
    (ep_mass S\<le>ro_mca_weighted_semantic_base rT rC \<and> fc_valid S acc)"

fun ap_value where
  "ap_value rT rC (AP_Family S rt ffs cfs start j,acc) = fc_potential rT rC S acc"

fun ap_advance where
  "ap_advance rT rC e (AP_Family S rt ffs cfs start j,acc) =
    (AP_Family S rt ffs cfs start j,fc_step rT rC S rt ffs cfs start j acc e)"

definition ap_score where
  "ap_score rT rC tickets = sum_list (map (ap_value rT rC) tickets)"

definition ap_invariant where
  "ap_invariant rT rC tickets \<longleftrightarrow> (\<forall>ticket\<in>set tickets. ap_valid rT rC ticket)"

definition ap_step where
  "ap_step rT rC birth tickets e =
    map (ap_advance rT rC e) tickets @
      (case birth e of None \<Rightarrow> [] | Some f \<Rightarrow> [(f,FC_Pre {} {})])"

lemma ap_advance_valid:
  "ap_valid rT rC ticket \<Longrightarrow> ap_valid rT rC (ap_advance rT rC e ticket)"
  by (cases ticket; cases "fst ticket")
    (auto simp: fc_valid_step)

lemma ap_advance_bound:
  assumes valid: "ap_valid rT rC ticket"
  shows "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow>
    ap_value rT rC (ap_advance rT rC e ticket)) s \<le> ap_value rT rC ticket"
  using valid
  by (cases ticket; cases "fst ticket") (auto intro: fc_step_potential_bound)

lemma ap_birth_value:
  assumes valid: "ap_valid rT rC (f,FC_Pre {} {})"
  shows "ap_value rT rC (f,FC_Pre {} {})\<le>(ro_mca_weighted_semantic_base rT rC)^2"
proof (cases f)
  case (AP_Family S rt ffs cfs start j)
  have mass: "ep_mass S\<le>ro_mca_weighted_semantic_base rT rC" using valid by (simp add: AP_Family)
  show ?thesis using mult_left_mono[OF mass, of "ro_mca_weighted_semantic_base rT rC"]
    by (simp add: AP_Family ep_mass_def power2_eq_square)
qed

lemma ap_list_advance_bound:
  assumes valid: "ap_invariant rT rC tickets"
  shows "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow>
    ap_score rT rC (map (ap_advance rT rC e) tickets)) s \<le> ap_score rT rC tickets"
  using valid
proof (induction tickets)
  case Nil
  show ?case
    by (rule wp_le_const_on_support) (auto simp: ap_score_def split: option.splits prod.splits)
next
  case (Cons ticket tickets)
  have v: "ap_valid rT rC ticket" and vs: "ap_invariant rT rC tickets"
    using Cons.prems by (auto simp: ap_invariant_def)
  have split: "\<And>out. (case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow>
      ap_score rT rC (map (ap_advance rT rC e) (ticket#tickets))) =
    (case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow> ap_value rT rC (ap_advance rT rC e ticket)) +
    (case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow> ap_score rT rC (map (ap_advance rT rC e) tickets))"
    by (auto simp: ap_score_def split: option.splits prod.splits)
  show ?case
    unfolding split causal_wp_add
    using add_mono[OF ap_advance_bound[OF v] Cons.IH[OF vs]]
    by (simp add: ap_score_def)
qed

lemma ap_step_valid:
  assumes old: "ap_invariant rT rC tickets"
    and births: "\<And>e f. birth e=Some f \<Longrightarrow> ap_valid rT rC (f,FC_Pre {} {})"
  shows "ap_invariant rT rC (ap_step rT rC birth tickets e)"
  using old births ap_advance_valid
  unfolding ap_invariant_def ap_step_def
  by (cases e) (auto intro: ap_advance_valid split: option.splits prod.splits)

lemma ap_step_bound:
  assumes old: "ap_invariant rT rC tickets"
    and births: "\<And>e f. birth e=Some f \<Longrightarrow> ap_valid rT rC (f,FC_Pre {} {})"
  shows "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow>
    ap_score rT rC (ap_step rT rC birth tickets e)) s \<le>
    ap_score rT rC tickets + (ro_mca_weighted_semantic_base rT rC)^2"
proof -
  have point: "\<And>e. ap_score rT rC (ap_step rT rC birth tickets e) \<le>
    ap_score rT rC (map (ap_advance rT rC e) tickets) + (ro_mca_weighted_semantic_base rT rC)^2"
    using ap_birth_value[OF births]
    by (auto simp: ap_step_def ap_score_def split: option.splits)
  have "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow>
      ap_score rT rC (ap_step rT rC birth tickets e)) s \<le>
    wp (pair_probe k) (\<lambda>out. (case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow>
      ap_score rT rC (map (ap_advance rT rC e) tickets)) + (ro_mca_weighted_semantic_base rT rC)^2) s"
    by (rule wp_mono_on_support) (use point in \<open>auto split: option.splits prod.splits\<close>)
  also have "... = wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow>
      ap_score rT rC (map (ap_advance rT rC e) tickets)) s + (ro_mca_weighted_semantic_base rT rC)^2"
    by (simp only: causal_wp_add causal_wp_const)
  also have "... \<le> ap_score rT rC tickets + (ro_mca_weighted_semantic_base rT rC)^2"
    by (rule add_right_mono[OF ap_list_advance_bound[OF old]])
  finally show ?thesis .
qed

lemma ap_walk_score:
  assumes old: "ap_invariant rT rC tickets"
    and births: "\<And>e f. birth e=Some f \<Longrightarrow> ap_valid rT rC (f,FC_Pre {} {})"
  shows "wp (fc_walk n C (ap_step rT rC birth) priv hist tickets)
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((tickets,hist),u) \<Rightarrow> ap_score rT rC tickets) s \<le>
    ap_score rT rC tickets + nnreal n*(ro_mca_weighted_semantic_base rT rC)^2"
  using old
proof (induction n arbitrary: priv hist tickets s)
  case 0
  then show ?case by (simp add: wpsimps)
next
  case (Suc n)
  let ?c="(ro_mca_weighted_semantic_base rT rC)^2"
  let ?V="\<lambda>out. case out of None \<Rightarrow> 0 | Some ((tickets,hist),u) \<Rightarrow> ap_score rT rC tickets"
  have num: "nnreal (Suc n)*?c = ?c+nnreal n*?c"
    by (simp add: algebra_simps)
  show ?case unfolding fc_walk.simps wp_bind num
  proof (rule wp_le_const_on_support)
    fix out
    assume mem: "out\<in>set_dist (execute (C priv hist) s)"
    show "(case out of None \<Rightarrow> ?V None | Some (choice,t) \<Rightarrow>
      wp (case choice of None \<Rightarrow> return (tickets,hist) | Some k \<Rightarrow>
        pair_probe (fst k) \<bind> (\<lambda>e. fc_walk n C (ap_step rT rC birth)
          (snd k) (hist@[e]) (ap_step rT rC birth tickets e))) ?V t)
      \<le> ap_score rT rC tickets + (?c+nnreal n*?c)"
    proof (cases out)
      case None
      then show ?thesis by simp
    next
      case (Some ct)
      obtain choice t where ct: "ct=(choice,t)" by (cases ct) simp
      have bound: "wp (case choice of None \<Rightarrow> return (tickets,hist) | Some k \<Rightarrow>
        pair_probe (fst k) \<bind> (\<lambda>e. fc_walk n C (ap_step rT rC birth)
          (snd k) (hist@[e]) (ap_step rT rC birth tickets e))) ?V t
        \<le> ap_score rT rC tickets + (?c+nnreal n*?c)"
      proof (cases choice)
        case None
        then show ?thesis by (simp add: wpsimps)
      next
        case (Some k)
        have "wp (pair_probe (fst k) \<bind> (\<lambda>e. fc_walk n C (ap_step rT rC birth)
            (snd k) (hist@[e]) (ap_step rT rC birth tickets e))) ?V t \<le>
          wp (pair_probe (fst k)) (\<lambda>out.
            (case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow> ap_score rT rC (ap_step rT rC birth tickets e))
              +nnreal n*?c) t"
          unfolding wp_bind
          by (rule wp_mono_on_support)
            (use Suc.IH[OF ap_step_valid[OF Suc.prems births]] in
              \<open>auto split: option.splits prod.splits\<close>)
        also have "... = wp (pair_probe (fst k))
          (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow> ap_score rT rC (ap_step rT rC birth tickets e)) t
            +nnreal n*?c"
          by (simp only: causal_wp_add causal_wp_const)
        also have "... \<le> (ap_score rT rC tickets+?c)+nnreal n*?c"
          by (rule add_right_mono[OF ap_step_bound[OF Suc.prems births]])
        finally show ?thesis by (simp add: Some add.assoc)
      qed
      then show ?thesis by (simp add: Some ct)
    qed
  qed
qed

definition ap_won where
  "ap_won out \<longleftrightarrow> (case out of None \<Rightarrow> False | Some ((tickets,hist),u) \<Rightarrow>
    (\<exists>f. (f,FC_Won)\<in>set tickets))"

lemma ap_score_member:
  "ticket\<in>set tickets \<Longrightarrow> ap_value rT rC ticket\<le>ap_score rT rC tickets"
  apply (induction tickets)
   apply (auto simp: ap_score_def)
  by (erule order_trans) simp

lemma ap_value_won[simp]: "ap_value rT rC (f,FC_Won)=1"
  by (cases f) simp

lemma ap_won_member_score:
  assumes member: "(f,FC_Won)\<in>set tickets"
  shows "1\<le>ap_score rT rC tickets"
  using ap_score_member[OF member, of rT rC] by simp

lemma ap_won_bound:
  assumes births: "\<And>e f. birth e=Some f \<Longrightarrow> ap_valid rT rC (f,FC_Pre {} {})"
  shows "wp_event (fc_walk n C (ap_step rT rC birth) priv hist []) ap_won s
    \<le>nnreal n*(ro_mca_weighted_semantic_base rT rC)^2"
proof -
  have detects: "\<And>out. (if ap_won out then 1 else 0)\<le>
    (case out of None \<Rightarrow> 0 | Some ((tickets,hist),u) \<Rightarrow> ap_score rT rC tickets)"
    by (auto simp: ap_won_def intro: ap_won_member_score split: option.splits prod.splits)
  have "wp_event (fc_walk n C (ap_step rT rC birth) priv hist []) ap_won s \<le>
    wp (fc_walk n C (ap_step rT rC birth) priv hist [])
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((tickets,hist),u) \<Rightarrow> ap_score rT rC tickets) s"
    unfolding wp_event_def by (rule wp_mono_on_support) (rule detects)
  also have "...\<le>ap_score rT rC []+nnreal n*(ro_mca_weighted_semantic_base rT rC)^2"
    by (rule ap_walk_score[OF _ births]) (simp add: ap_invariant_def)
  finally show ?thesis by (simp add: ap_score_def)
qed

lemma ap_fold_member:
  assumes member: "(AP_Family S rt ffs cfs start j,acc)\<in>set tickets"
  shows "(AP_Family S rt ffs cfs start j,
    foldl (fc_step rT rC S rt ffs cfs start j) acc es)\<in>
    set (foldl (ap_step rT rC birth) tickets es)"
  using member
proof (induction es arbitrary: tickets acc)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  have successor: "(AP_Family S rt ffs cfs start j,
      fc_step rT rC S rt ffs cfs start j acc e)\<in>set (ap_step rT rC birth tickets e)"
    using imageI[OF Cons.prems, of "ap_advance rT rC e"]
    by (simp add: ap_step_def)
  show ?case using Cons.IH[OF successor] by simp
qed

lemma ap_born_member:
  assumes born: "birth e=Some (AP_Family S rt ffs cfs start j)"
  shows "(AP_Family S rt ffs cfs start j,
    foldl (fc_step rT rC S rt ffs cfs start j) (FC_Pre {} {}) post) \<in>
    set (foldl (ap_step rT rC birth) tickets (pre@e#post))"
proof -
  have member: "(AP_Family S rt ffs cfs start j,FC_Pre {} {})\<in>
    set (ap_step rT rC birth (foldl (ap_step rT rC birth) tickets pre) e)"
    by (simp add: ap_step_def born)
  show ?thesis using ap_fold_member[OF member, where es=post] by simp
qed

definition ap_best where
  "ap_best rT rC tickets = Max (insert 0 (ap_value rT rC ` set tickets))"

lemma ap_best_le_score:
  "ap_best rT rC tickets\<le>ap_score rT rC tickets"
  unfolding ap_best_def
  by (auto intro: ap_score_member)

lemma ap_inherited_selection_bound:
  assumes births: "\<And>e f. birth e=Some f \<Longrightarrow> ap_valid rT rC (f,FC_Pre {} {})"
  shows "wp (fc_walk n C (ap_step rT rC birth) priv hist [])
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((tickets,hist),u) \<Rightarrow> ap_best rT rC tickets) s \<le>
    nnreal n*(ro_mca_weighted_semantic_base rT rC)^2"
proof -
  have "wp (fc_walk n C (ap_step rT rC birth) priv hist [])
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((tickets,hist),u) \<Rightarrow> ap_best rT rC tickets) s \<le>
    wp (fc_walk n C (ap_step rT rC birth) priv hist [])
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((tickets,hist),u) \<Rightarrow> ap_score rT rC tickets) s"
    by (rule wp_mono_on_support)
      (auto intro: ap_best_le_score split: option.splits prod.splits)
  also have "...\<le>ap_score rT rC []+nnreal n*(ro_mca_weighted_semantic_base rT rC)^2"
    by (rule ap_walk_score[OF _ births]) (simp add: ap_invariant_def)
  finally show ?thesis by (simp add: ap_score_def)
qed

end

subsection \<open>Adaptive Family Selection\<close>

context soundness
begin

definition as_header where
  "as_header M start data \<longleftrightarrow> weighted_semantic_header_shape data \<and> staged_trace_fri_roots data\<noteq>[] \<and>
    (\<exists>rest. ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
      (weighted_semantic_header data@rest) start)"

definition as_data where
  "as_data M start = (SOME data. as_header M start data)"

lemma as_data_header:
  "(\<exists>data. as_header M start data) \<Longrightarrow> as_header M start (as_data M start)"
  unfolding as_data_def by (rule someI_ex)

definition as_family where
  "as_family rT rC M start j =
    AP_Family {raw. weighted_semantic_hit rT rC M start raw}
      (staged_trace_root (as_data M start))
      (map (\<lambda>root. ((0::'f),root)) (staged_trace_fri_roots (as_data M start)))
      (map (\<lambda>root. ((0::'f),root)) (staged_composition_fri_roots (as_data M start))) start j"

definition as_birth where
  "as_birth rT rC j e = (case e of (M,k,start) \<Rightarrow> (case k of TranscriptAbsorb pred msg \<Rightarrow>
    let V=fmupd k start M in
    if fmlookup M k=None \<and> \<not>hash_map_output_collision (channel_for_hash_map V) \<and>
      PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map V) \<and>
      (\<exists>data. as_header V start data)
    then Some (as_family rT rC V start j) else None
    | _ \<Rightarrow> None))"

lemma as_family_valid:
  assumes clean: "\<not>hash_map_output_collision (channel_for_hash_map M)"
    and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map M)"
  shows "ap_valid rT rC (as_family rT rC M start j,FC_Pre {} {})"
proof -
  have mass: "ep_mass {raw. weighted_semantic_hit rT rC M start raw}\<le>ro_mca_weighted_semantic_base rT rC"
    unfolding ep_mass_def by (rule nnreal_nat_divide_right_mono[OF weighted_semantic_hit_fiber[OF clean initial]])
  show ?thesis using mass by (simp add: as_family_def fc_valid_def)
qed

lemma as_birth_valid:
  "as_birth rT rC j e=Some f \<Longrightarrow> ap_valid rT rC (f,FC_Pre {} {})"
  unfolding as_birth_def using as_family_valid
  by (auto simp: Let_def split: prod.splits protocol_hash_input.splits if_splits)

lemma as_adaptive_family_won_bound:
  "wp_event (fc_walk n C (ap_step rT rC (as_birth rT rC j)) priv hist []) ap_won s
    \<le>nnreal n*(ro_mca_weighted_semantic_base rT rC)^2"
  by (rule ap_won_bound) (rule as_birth_valid)

lemma as_header_recovery:
  assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
    and stored: "fmlookup M k=Some start"
    and nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
      (channel_for_hash_map M) (channel_for_hash_map U)"
    and header: "as_header U start data"
  shows "as_header M start data"
  using header ab_stored_endpoint_chain_recovery[OF ext clean stored nt]
  unfolding as_header_def by blast

lemma as_header_roots_targets:
  assumes header: "as_header M start data"
  shows "causal_route_roots (staged_trace_root data)
    (map (\<lambda>root. ((0::'f),root)) (staged_trace_fri_roots data))
    (map (\<lambda>root. ((0::'f),root)) (staged_composition_fri_roots data)) \<subseteq>weighted_semantic_interval_targets M"
proof -
  obtain rest where chain: "ro_absorb_lookup_chain (channel_for_hash_map M)
    (PState adversary_initial_state) (weighted_semantic_header data@rest) start"
    using header unfolding as_header_def by blast
  have messages: "set (weighted_semantic_header data)\<subseteq>transcript_absorb_message_values M"
    using ro_absorb_lookup_chain_messages_subset[OF chain] by auto
  show ?thesis using messages
    unfolding causal_route_roots_def weighted_semantic_header_def verifier_header_messages_def
      weighted_semantic_interval_targets_def by auto
qed

lemma as_clean_prefix:
  assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
    and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map U)"
  shows "\<not>hash_map_output_collision (channel_for_hash_map M)"
    "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map M)"
proof -
  have keep: "\<And>k x. fmlookup M k=Some x \<Longrightarrow> fmlookup U k=Some x"
  proof -
    fix k x
    assume lookup: "fmlookup M k=Some x"
    have old: "fmlookup (HashMap (channel_for_hash_map M)) k=Some x"
      using lookup by (simp add: channel_for_hash_map_def)
    show "fmlookup U k=Some x" using hash_extension_lookup[OF old ext]
      by (simp add: channel_for_hash_map_def)
  qed
  show "\<not>hash_map_output_collision (channel_for_hash_map M)"
    using clean keep unfolding hash_map_output_collision_def channel_for_hash_map_def by (auto; blast)
  show "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map M)"
    using initial keep unfolding hash_map_output_values_def channel_for_hash_map_def by (auto; blast)
qed

lemma as_birth_from_final_header:
  assumes history: "fc_history M ((M,TranscriptAbsorb pred msg,start)#es) U"
    and nob: "fc_no_bad {} ((M,TranscriptAbsorb pred msg,start)#es)"
    and fresh: "fmlookup M (TranscriptAbsorb pred msg)=None"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
    and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map U)"
    and header: "as_header U start data"
  shows "as_header (fmupd (TranscriptAbsorb pred msg) start M) start data"
    "as_birth rT rC j (M,TranscriptAbsorb pred msg,start)=
      Some (as_family rT rC (fmupd (TranscriptAbsorb pred msg) start M) start j)"
proof -
  let ?V="fmupd (TranscriptAbsorb pred msg) start M"
  have suffix: "fc_history ?V es U" using history by simp
  have ext: "channel_for_hash_map ?V\<le>channel_for_hash_map U"
    by (rule fc_history_extension[OF suffix])
  have cleanV: "\<not>hash_map_output_collision (channel_for_hash_map ?V)"
    and initialV: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map ?V)"
    by (rule as_clean_prefix[OF ext clean initial])+
  have nobp: "fc_no_bad {} es" using nob by (simp add: fc_no_bad_def)
  have nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets ?V)
      (channel_for_hash_map ?V) (channel_for_hash_map U)"
    using fc_history_no_target_hit[OF suffix nobp] by (simp add: fc_target_def)
  have stored: "fmlookup ?V (TranscriptAbsorb pred msg)=Some start" by simp
  show oldheader: "as_header ?V start data"
    by (rule as_header_recovery[OF ext clean stored nt header])
  show "as_birth rT rC j (M,TranscriptAbsorb pred msg,start)=Some (as_family rT rC ?V start j)"
    using fresh cleanV initialV oldheader by (auto simp: as_birth_def Let_def)
qed

lemma as_canonical_root_fields:
  assumes clean: "\<not>hash_map_output_collision (channel_for_hash_map M)"
    and initial: "PState adversary_initial_state\<notin>hash_map_output_values (channel_for_hash_map M)"
    and header: "as_header M start data"
  shows "staged_trace_root (as_data M start)=staged_trace_root data"
    "staged_trace_fri_roots (as_data M start)=staged_trace_fri_roots data"
    "staged_composition_fri_roots (as_data M start)=staged_composition_fri_roots data"
proof -
  have exists: "\<exists>data. as_header M start data" using header by blast
  have chosen: "as_header M start (as_data M start)" by (rule as_data_header[OF exists])
  obtain ar br where ashape: "weighted_semantic_header_shape data"
    and bshape: "weighted_semantic_header_shape (as_data M start)"
    and a: "ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
      (weighted_semantic_header data@ar) start"
    and b: "ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state)
      (weighted_semantic_header (as_data M start)@br) start"
    using header chosen unfolding as_header_def by blast
  note fields=ea_header_fields_at_prefix_unique[OF clean initial ashape bshape a b]
  show "staged_trace_root (as_data M start)=staged_trace_root data"
    "staged_trace_fri_roots (as_data M start)=staged_trace_fri_roots data"
    "staged_composition_fri_roots (as_data M start)=staged_composition_fri_roots data"
    using fields by auto
qed

end

subsection \<open>Adaptive Family Result\<close>

context soundness
begin

definition ar_matches where
  "ar_matches M start rt ffs cfs \<longleftrightarrow>
    rt=staged_trace_root (as_data M start) \<and>
    map snd ffs=staged_trace_fri_roots (as_data M start) \<and>
    map snd cfs=staged_composition_fri_roots (as_data M start)"

definition ar_selected_event where
  "ar_selected_event rT rC j N out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some ((tickets,hist),u) \<Rightarrow>
      \<exists>pre M pred msg start post rt ffs fv alphas cfs cv.
        let e=(M,TranscriptAbsorb pred msg,start);
            V=fmupd (TranscriptAbsorb pred msg) start M
        in hist=pre@e#post \<and> as_birth rT rC j e=Some (as_family rT rC V start j) \<and>
          ar_matches V start rt ffs cfs \<and> length ffs\<le>N \<and> length cfs\<le>N \<and>
          fc_selected_event rT rC rt ffs fv alphas cfs cv start j (Some (((),post),u)))"

lemma ar_selected_history_wins:
  assumes power: "clength*scale=2^N"
    and history: "fc_history M0 hist (HashMap u)"
    and event: "ar_selected_event rT rC j N (Some ((tickets,hist),u))"
    and nob: "fc_no_bad {} hist"
  shows "\<exists>f. (f,FC_Won)\<in>set (foldl (ap_step rT rC (as_birth rT rC j)) [] hist)"
proof -
  obtain pre M pred msg start post rt ffs fv alphas cfs cv where
    hist: "hist=pre@(M,TranscriptAbsorb pred msg,start)#post"
    and born: "as_birth rT rC j (M,TranscriptAbsorb pred msg,start)=
      Some (as_family rT rC (fmupd (TranscriptAbsorb pred msg) start M) start j)"
    and matches: "ar_matches (fmupd (TranscriptAbsorb pred msg) start M) start rt ffs cfs"
    and traces: "length ffs\<le>N" and comps: "length cfs\<le>N"
    and selected: "fc_selected_event rT rC rt ffs fv alphas cfs cv start j (Some (((),post),u))"
    using event unfolding ar_selected_event_def by (auto simp: Let_def)
  let ?V="fmupd (TranscriptAbsorb pred msg) start M"
  let ?D="as_data ?V start"
  let ?F="map (\<lambda>root. ((0::'f),root)) (staged_trace_fri_roots ?D)"
  let ?G="map (\<lambda>root. ((0::'f),root)) (staged_composition_fri_roots ?D)"
  let ?S="{raw. weighted_semantic_hit rT rC ?V start raw}"
  let ?family="AP_Family ?S rt ?F ?G start j"
  let ?R="causal_route_roots rt ffs cfs \<union> {start}"
  have suffix: "fc_history ?V post (HashMap u)"
    using history by (auto simp: hist fc_history_append)
  have nobp: "fc_no_bad {} post" using nob by (auto simp: hist fc_no_bad_def)
  have clean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap u))"
    using selected unfolding fc_selected_event_def by (auto simp: Let_def)
  have exists: "\<exists>data. as_header ?V start data"
    using born by (auto simp: as_birth_def Let_def split: if_splits)
  have header: "as_header ?V start ?D" by (rule as_data_header[OF exists])
  have rt: "rt=staged_trace_root ?D" and roots:
    "map snd ffs=map snd ?F" "map snd cfs=map snd ?G"
    using matches
    by (auto simp: ar_matches_def comp_def)
  have route_roots: "causal_route_roots rt ffs cfs=causal_route_roots rt ?F ?G"
    unfolding causal_route_roots_def by (simp only: roots)
  have R: "?R\<subseteq>weighted_semantic_interval_targets ?V\<union>{start}"
    apply (subst route_roots)
    using as_header_roots_targets[OF header] by (simp only: rt; blast)
  have stored: "fmlookup ?V (TranscriptAbsorb pred msg)=Some start" by simp
  have noR: "fc_no_bad ?R post"
    by (rule ab_no_bad_stored_targets[OF suffix nobp clean stored R])
  have wins: "foldl (fc_step rT rC ?S rt ffs cfs start j) (FC_Pre {} {}) post=FC_Won"
    by (rule fc_selected_history_wins[OF power traces comps suffix selected noR])
  have step: "fc_step rT rC ?S rt ffs cfs start j=fc_step rT rC ?S rt ?F ?G start j"
    by (rule ext, rule ext, rule ea_account_roots_cong[OF roots])
  have canonical: "foldl (fc_step rT rC ?S rt ?F ?G start j) (FC_Pre {} {}) post=FC_Won"
    using wins by (simp only: step)
  have born': "as_birth rT rC j (M,TranscriptAbsorb pred msg,start)=Some ?family"
    using born by (simp add: as_family_def rt)
  have member: "(?family,FC_Won)\<in>set (foldl (ap_step rT rC (as_birth rT rC j)) [] hist)"
    using ap_born_member[where birth="as_birth rT rC j" and e="(M,TranscriptAbsorb pred msg,start)"
      and rT=rT and rC=rC and pre=pre and post=post and tickets="[]", OF born']
    by (simp only: hist canonical)
  show ?thesis using member by blast
qed

lemma ar_selected_event_bound:
  assumes power: "clength*scale=2^N"
    and selectors: "\<And>priv h. hash_map_preserving (C priv h)"
    and cap: "card (fmdom' (HashMap s))\<le>hcap"
  shows "wp_event (fc_walk n C (ap_step rT rC (as_birth rT rC j)) priv [] [])
    (ar_selected_event rT rC j N) s \<le>
    nnreal n*(ro_mca_weighted_semantic_base rT rC)^2 + fc_charge ({}::'f set) n hcap"
proof -
  let ?run="fc_walk n C (ap_step rT rC (as_birth rT rC j)) priv [] []"
  let ?E="ar_selected_event rT rC j N"
  let ?B="\<lambda>out. case out of None \<Rightarrow> False | Some ((tickets,hist),u) \<Rightarrow> \<not>fc_no_bad {} hist"
  have split: "\<And>out. out\<in>set_dist (execute ?run s) \<Longrightarrow> ?E out \<Longrightarrow> ap_won out \<or> ?B out"
  proof -
    fix out
    assume mem: "out\<in>set_dist (execute ?run s)" and event: "?E out"
    obtain tickets hist u where out: "out=Some ((tickets,hist),u)"
      using event unfolding ar_selected_event_def by (auto split: option.splits prod.splits)
    have supported: "Some ((tickets,hist),u)\<in>set_dist (execute ?run s)" using mem out by simp
    obtain es where hist: "hist=es"
      and account: "tickets=foldl (ap_step rT rC (as_birth rT rC j)) [] es"
      and history: "fc_history (HashMap s) es (HashMap u)"
      using fc_walk_log[OF selectors supported] by auto
    show "ap_won out \<or> ?B out"
    proof (cases "fc_no_bad {} hist")
      case True
      have wins: "\<exists>f. (f,FC_Won)\<in>set tickets"
        using ar_selected_history_wins[OF power history, where tickets=tickets]
          event True by (simp add: out hist account)
      then show ?thesis by (simp add: out ap_won_def)
    next
      case False
      then show ?thesis by (simp add: out)
    qed
  qed
  have "wp_event ?run ?E s \<le>
    wp ?run (\<lambda>out. (if ap_won out then 1 else 0)+(if ?B out then 1 else 0)) s"
    unfolding wp_event_def by (rule wp_mono_on_support) (use split in auto)
  also have "...=wp_event ?run ap_won s+wp_event ?run ?B s"
    unfolding wp_event_def by (rule causal_wp_add)
  also have "...\<le>nnreal n*(ro_mca_weighted_semantic_base rT rC)^2+fc_charge ({}::'f set) n hcap"
    by (rule add_mono[OF as_adaptive_family_won_bound fc_walk_bad_event_bound[OF selectors cap]])
  finally show ?thesis .
qed

end

end
