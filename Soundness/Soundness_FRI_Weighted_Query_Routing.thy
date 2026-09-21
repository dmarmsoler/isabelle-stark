(* Title: Stark/Soundness_FRI_Weighted_Query_Routing.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Query_Routing
  imports
    "Stark.Soundness_FRI_First_Root_RO_State_Relation"
    "Stark.Soundness_FRI_RO_Actual_Query_Accepted_Evidence"
    "Soundness_FRI_Weighted_Semantic_Recovery"
begin

section \<open>Query Routing for weighted MCA soundness\<close>

text \<open>Authenticated openings determine query successors. First-insertion recovery and routing weights handle cached calls and child-before-parent oracle order without assuming independent overlapping paths.\<close>

subsection \<open>Cached Draw Causality\<close>

lemma length_cons_decompose:
  assumes "length (x # xs) = length ys"
  obtains y zs where "ys = y # zs" "length xs = length zs"
  using assms by (cases ys) auto

lemma cached_audit_expect_swap:
  "dist_expect d (\<lambda>a. dist_expect e (\<lambda>b. f a b)) =
   dist_expect e (\<lambda>b. dist_expect d (\<lambda>a. f a b))"
proof -
  have "dist_expect d (\<lambda>a. dist_expect e (\<lambda>b. f a b)) =
    (\<Sum>a\<in>dom (dist d). \<Sum>b\<in>dom (dist e).
      the (dist d a) * (the (dist e b) * f a b))"
    by (simp only: dist_expect_def sum_distrib_left)
  also have "... = (\<Sum>b\<in>dom (dist e). \<Sum>a\<in>dom (dist d).
      the (dist d a) * (the (dist e b) * f a b))"
    by (rule sum.swap)
  also have "... = dist_expect e (\<lambda>b. dist_expect d (\<lambda>a. f a b))"
    by (simp only: dist_expect_def sum_distrib_left mult.left_commute)
  finally show ?thesis .
qed

context soundness
begin

text \<open>Auxiliary clean-branch facts, not new public assumptions.\<close>

lemma query_insertion_cannot_select_absorbed_history:
  assumes clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial: "start \<notin> hash_map_output_values (channel_for_hash_map M)"
    and left: "ro_absorb_lookup_chain
      (channel_for_hash_map (fmupd (QueryIndexChallenge j st) y M)) start xs final"
    and right: "ro_absorb_lookup_chain
      (channel_for_hash_map (fmupd (QueryIndexChallenge j st) z M)) start ys final"
  shows "xs = ys"
proof -
  have l: "ro_absorb_lookup_chain (channel_for_hash_map M) start xs final"
    using left by simp
  have r: "ro_absorb_lookup_chain (channel_for_hash_map M) start ys final"
    using right by simp
  show ?thesis
    by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
      OF clean no_initial l r])
qed

lemma clean_merkle_path_unique:
  assumes clean: "\<not> hash_map_output_collision s"
    and first: "merkle_path_bound rt len idx v path s"
    and second: "merkle_path_bound rt len idx v' path' s"
    and same_length: "length path = length path'"
  shows "path = path'"
  using first second same_length
proof (induction path arbitrary: path' rt len idx)
  case Nil
  then show ?case by simp
next
  case (Cons sibling path)
  obtain sibling' rest where path': "path' = sibling' # rest"
    and lengths: "length path = length rest"
    by (rule length_cons_decompose[OF Cons.prems(3)])
  show ?case
  proof (cases "idx < len div 2")
    case True
    obtain child child' where
      a: "merkle_path_bound child (len div 2) idx v path s"
      and b: "merkle_path_bound child' (len div 2) idx v' rest s"
      and l: "fmlookup (HashMap s) (MerkleNode child sibling) = Some rt"
      and r: "fmlookup (HashMap s) (MerkleNode child' sibling') = Some rt"
      using Cons.prems(1,2) True path' by auto
    have nodes: "MerkleNode child sibling = MerkleNode child' sibling'"
      by (rule hash_map_lookup_key_unique_if_no_output_collision[OF clean l r])
    have paths: "path = rest"
      by (rule Cons.IH[OF a _ lengths]) (use b nodes in simp)
    show ?thesis using nodes paths path' by simp
  next
    case False
    obtain child child' where
      a: "merkle_path_bound child (len div 2) (idx-len div 2) v path s"
      and b: "merkle_path_bound child' (len div 2) (idx-len div 2) v' rest s"
      and l: "fmlookup (HashMap s) (MerkleNode sibling child) = Some rt"
      and r: "fmlookup (HashMap s) (MerkleNode sibling' child') = Some rt"
      using Cons.prems(1,2) False path' by auto
    have nodes: "MerkleNode sibling child = MerkleNode sibling' child'"
      by (rule hash_map_lookup_key_unique_if_no_output_collision[OF clean l r])
    have paths: "path = rest"
      by (rule Cons.IH[OF a _ lengths]) (use b nodes in simp)
    show ?thesis using nodes paths path' by simp
  qed
qed

lemma clean_authenticated_opening_unique:
  assumes clean: "\<not> hash_map_output_collision s"
    and a: "authenticated_opening_in s u"
    and b: "authenticated_opening_in s v"
    and roots: "opening_root u = opening_root v"
    and lens: "opening_length u = opening_length v"
    and idx: "opening_index u = opening_index v"
  shows "u = v"
proof -
  have left: "merkle_path_bound (opening_root u) (opening_length u)
    (opening_index u) (opening_value u) (opening_path u) s"
    using a unfolding authenticated_opening_in_def by simp
  have right: "merkle_path_bound (opening_root u) (opening_length u)
    (opening_index u) (opening_value v) (opening_path v) s"
    using b roots lens idx unfolding authenticated_opening_in_def by simp
  have lengths: "length (opening_path u) = length (opening_path v)"
    using a b lens unfolding authenticated_opening_in_def by simp
  have value_eq: "opening_value u = opening_value v"
    by (rule merkle_path_bound_unique_value_if_clean[OF clean left right lengths])
  have paths: "opening_path u = opening_path v"
    by (rule clean_merkle_path_unique[OF clean left right lengths])
  show ?thesis using roots lens idx value_eq paths
    by (cases u; cases v) simp
qed

lemma cached_prefix_late_connection_requires_target:
  assumes fresh: "fmlookup M x = None"
    and cached: "fmlookup M (QueryIndexChallenge j st) = Some raw"
    and new: "ro_absorb_lookup_chain (channel_for_hash_map (fmupd x y M))
      start messages st"
    and old: "\<not> ro_absorb_lookup_chain (channel_for_hash_map M) start messages st"
  shows "y \<in> first_root_relation_drift_targets M x"
proof (rule ccontr)
  assume none: "y \<notin> first_root_relation_drift_targets M x"
  have target: "st \<in> query_index_state_values M"
    using cached unfolding query_index_state_values_def by blast
  have "ro_absorb_lookup_chain (channel_for_hash_map M) start messages st"
    by (rule ro_absorb_lookup_chain_fresh_update_pullback[OF fresh new target none])
  then show False using old by contradiction
qed

lemma clean_fri_layer_chunk_unique:
  assumes clean: "\<not> hash_map_output_collision s"
    and a: "fri_layer_chunk_authenticated rt len idx chunk s"
    and b: "fri_layer_chunk_authenticated rt len idx chunk' s"
  shows "chunk = chunk'"
proof -
  obtain xp pp xn pn yp qp yn qn where
    ca: "fri_layer_opening_chunk len xp pp xn pn chunk"
    and cb: "fri_layer_opening_chunk len yp qp yn qn chunk'"
    and ap: "authenticated_opening_in s
      \<lparr>opening_root=rt, opening_length=len, opening_index=idx,
        opening_value=xp, opening_path=pp\<rparr>"
    and bp: "authenticated_opening_in s
      \<lparr>opening_root=rt, opening_length=len, opening_index=idx,
        opening_value=yp, opening_path=qp\<rparr>"
    and an: "authenticated_opening_in s
      \<lparr>opening_root=rt, opening_length=len, opening_index=fri_sibling_index len idx,
        opening_value=xn, opening_path=pn\<rparr>"
    and bn: "authenticated_opening_in s
      \<lparr>opening_root=rt, opening_length=len, opening_index=fri_sibling_index len idx,
        opening_value=yn, opening_path=qn\<rparr>"
    using a b unfolding fri_layer_chunk_authenticated_def by blast
  have pos: "xp=yp \<and> pp=qp"
    using clean_authenticated_opening_unique[OF clean ap bp] by simp
  have neg: "xn=yn \<and> pn=qn"
    using clean_authenticated_opening_unique[OF clean an bn] by simp
  show ?thesis using ca cb pos neg unfolding fri_layer_opening_chunk_def by simp
qed

lemma clean_fri_chunks_unique:
  assumes clean: "\<not> hash_map_output_collision s"
    and a: "fri_mfold_chunks_authenticated bfs len idx chunks s"
    and b: "fri_mfold_chunks_authenticated bfs len idx chunks' s"
  shows "chunks = chunks'"
proof (rule nth_equalityI)
  show "length chunks = length chunks'"
    using a b unfolding fri_mfold_chunks_authenticated_def by simp
next
  fix i
  assume i: "i < length chunks"
  show "chunks ! i = chunks' ! i"
    by (rule clean_fri_layer_chunk_unique[OF clean])
      (use a b i in \<open>auto simp: fri_mfold_chunks_authenticated_def\<close>)
qed

lemma late_absorb_connection_clean_map_example:
  fixes j :: nat and st raw start msg :: 'f
    and M U :: "('f protocol_hash_input, 'f) fmap"
  assumes distinct: "st \<noteq> raw" "start \<noteq> st" "start \<noteq> raw"
  defines "M \<equiv> fmupd (QueryIndexChallenge j st) raw fmempty"
    and "U \<equiv> fmupd (TranscriptAbsorb start msg) st M"
  shows "fmlookup M (QueryIndexChallenge j st) = Some raw"
    and "\<not> ro_absorb_lookup_chain (channel_for_hash_map M) start [msg] st"
    and "ro_absorb_lookup_chain (channel_for_hash_map U) start [msg] st"
    and "\<not> hash_map_output_collision (channel_for_hash_map U)"
    and "start \<notin> hash_map_output_values (channel_for_hash_map U)"
    and "st \<in> first_root_relation_drift_targets M (TranscriptAbsorb start msg)"
  using distinct
  unfolding M_def U_def channel_for_hash_map_def hash_map_output_collision_def
    hash_map_output_values_def first_root_relation_drift_targets_def
    query_index_state_values_def
  by auto

lemma clean_ordered_partial_openings_unique:
  assumes clean: "\<not> hash_map_output_collision s"
    and a: "partial_authenticated_table rt len us s"
    and b: "partial_authenticated_table rt len vs s"
    and indices: "map opening_index us = map opening_index vs"
  shows "us = vs"
proof (rule nth_equalityI)
  show lengths: "length us = length vs"
    using arg_cong[OF indices, of length] by simp
next
  fix i
  assume i: "i < length us"
  have lengths: "length us = length vs"
    using arg_cong[OF indices, of length] by simp
  have ui: "us!i \<in> set us" and vi: "vs!i \<in> set vs"
    using i lengths by auto
  have au: "authenticated_opening_in s (us!i)"
    and av: "authenticated_opening_in s (vs!i)"
    and roots: "opening_root (us!i) = opening_root (vs!i)"
    and lens: "opening_length (us!i) = opening_length (vs!i)"
    using a b ui vi unfolding partial_authenticated_table_def by auto
  have index: "opening_index (us!i) = opening_index (vs!i)"
    using arg_cong[OF indices, of "\<lambda>xs. xs!i"] i lengths by simp
  show "us!i = vs!i"
    by (rule clean_authenticated_opening_unique[OF clean au av roots lens index])
qed

lemma fixed_distinct_hash_draws_commute:
  fixes x y :: "'f protocol_hash_input"
    and s :: "'f protocol_channel"
  assumes neq: "x \<noteq> y"
  shows "wp_event (do {a \<leftarrow> hash x; b \<leftarrow> hash y; return (a,b)}) P s =
    wp_event (do {b \<leftarrow> hash y; a \<leftarrow> hash x; return (a,b)}) P s"
proof -
  have x_dist: "\<And>b. hash_dist x (s\<lparr>HashMap:=fmupd y b (HashMap s)\<rparr>) = hash_dist x s"
    using neq by (simp add: hash_dist_def)
  have y_dist: "\<And>a. hash_dist y (s\<lparr>HashMap:=fmupd x a (HashMap s)\<rparr>) = hash_dist y s"
    using neq by (simp add: hash_dist_def)
  have updates: "\<And>a b. fmupd y b (fmupd x a (HashMap s)) =
    fmupd x a (fmupd y b (HashMap s))"
    using neq by (simp add: fmupd_reorder_neq)
  show ?thesis
    unfolding wp_event_def
    apply (simp add: wpsimps hash_dist_def neq updates eq_commute)
    apply (rule cached_audit_expect_swap)
    done
qed

lemma fixed_absorbed_history_query_fiber:
  assumes clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial: "start \<notin> hash_map_output_values (channel_for_hash_map M)"
    and subsets: "\<And>xs. ro_absorb_lookup_chain (channel_for_hash_map M) start xs st
      \<Longrightarrow> I xs \<subseteq> query_sample_space"
    and caps: "\<And>xs. ro_absorb_lookup_chain (channel_for_hash_map M) start xs st
      \<Longrightarrow> card (I xs) \<le> B"
  shows "card {y. \<exists>xs.
    ro_absorb_lookup_chain (channel_for_hash_map (fmupd (QueryIndexChallenge j st) y M))
      start xs st \<and> y \<in> query_index_raw_preimage (I xs)}
    \<le> query_raw_preimage_card_envelope B"
proof (cases "\<exists>xs. ro_absorb_lookup_chain (channel_for_hash_map M) start xs st")
  case False
  then have empty: "{y. \<exists>xs.
    ro_absorb_lookup_chain (channel_for_hash_map (fmupd (QueryIndexChallenge j st) y M))
      start xs st \<and> y \<in> query_index_raw_preimage (I xs)} = {}"
    by auto
  show ?thesis unfolding empty by simp
next
  case True
  then obtain xs0 where chain:
    "ro_absorb_lookup_chain (channel_for_hash_map M) start xs0 st" by blast
  have sub: "{y. \<exists>xs.
    ro_absorb_lookup_chain (channel_for_hash_map (fmupd (QueryIndexChallenge j st) y M))
      start xs st \<and> y \<in> query_index_raw_preimage (I xs)}
    \<subseteq> query_index_raw_preimage (I xs0)"
  proof
    fix y
    assume "y \<in> {y. \<exists>xs.
      ro_absorb_lookup_chain (channel_for_hash_map (fmupd (QueryIndexChallenge j st) y M))
        start xs st \<and> y \<in> query_index_raw_preimage (I xs)}"
    then obtain xs where other:
      "ro_absorb_lookup_chain (channel_for_hash_map M) start xs st"
      and hit: "y \<in> query_index_raw_preimage (I xs)" by auto
    have "xs = xs0"
      by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
        OF clean no_initial other chain])
    then show "y \<in> query_index_raw_preimage (I xs0)" using hit by simp
  qed
  have "card {y. \<exists>xs.
    ro_absorb_lookup_chain (channel_for_hash_map (fmupd (QueryIndexChallenge j st) y M))
      start xs st \<and> y \<in> query_index_raw_preimage (I xs)}
    \<le> card (query_index_raw_preimage (I xs0))"
    by (rule card_mono[OF _ sub]) simp
  also have "... \<le> query_raw_preimage_card_envelope (card (I xs0))"
    by (rule card_query_index_raw_preimage_le_query_envelope[OF subsets[OF chain]])
  also have "... \<le> query_raw_preimage_card_envelope B"
    by (rule query_raw_preimage_card_envelope_mono[OF caps[OF chain]])
  finally show ?thesis .
qed

lemma wp_fixed_absorbed_history_query_draw:
  assumes fresh: "fmlookup M (QueryIndexChallenge j st) = None"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial: "start \<notin> hash_map_output_values (channel_for_hash_map M)"
    and subsets: "\<And>xs. ro_absorb_lookup_chain (channel_for_hash_map M) start xs st
      \<Longrightarrow> I xs \<subseteq> query_sample_space"
    and caps: "\<And>xs. ro_absorb_lookup_chain (channel_for_hash_map M) start xs st
      \<Longrightarrow> card (I xs) \<le> B"
  shows "wp_event (hash (QueryIndexChallenge j st))
    (\<lambda>out. case out of None \<Rightarrow> False | Some (y,t) \<Rightarrow>
      (\<exists>xs. ro_absorb_lookup_chain t start xs st \<and> y \<in> query_index_raw_preimage (I xs)))
    (channel_for_hash_map M)
    \<le> nnreal (query_raw_preimage_card_envelope B) / nnreal size"
proof -
  let ?S = "{y. \<exists>xs.
    ro_absorb_lookup_chain (channel_for_hash_map (fmupd (QueryIndexChallenge j st) y M))
      start xs st \<and> y \<in> query_index_raw_preimage (I xs)}"
  have fresh': "fmlookup (HashMap (channel_for_hash_map M)) (QueryIndexChallenge j st) = None"
    using fresh unfolding channel_for_hash_map_def by simp
  have exact: "wp_event (hash (QueryIndexChallenge j st))
    (\<lambda>out. case out of None \<Rightarrow> False | Some (y,t) \<Rightarrow>
      (\<exists>xs. ro_absorb_lookup_chain t start xs st \<and> y \<in> query_index_raw_preimage (I xs)))
    (channel_for_hash_map M) = nnreal (card ?S) / nnreal size"
    unfolding wp_event_def
    using dist_expect_hash_dist_fresh_indicator[OF fresh', of "?S"]
    by (simp add: wp_hash channel_for_hash_map_def)
  have card: "card ?S \<le> query_raw_preimage_card_envelope B"
    by (rule fixed_absorbed_history_query_fiber[OF clean no_initial subsets caps])
  show ?thesis unfolding exact by (rule nnreal_nat_divide_right_mono[OF card])
qed

end

subsection \<open>Query Serialization\<close>

context soundness
begin

text \<open>These proof-only lemmas recover exact consumed messages from the actual
absorbing verifier. Authentication is a necessary consequence of success here,
not a new validity condition assumed in the public theorem.\<close>

lemma serial_ro_opening:
  fixes s t :: "'f protocol_channel"
  assumes idx: "i < scale * clength"
    and outcome: "Some (v,t) \<in> set_dist (execute (ro_query_decommitment_step rt i) s)"
  obtains path where
    "PTranscript s = (v # path) @ PTranscript t"
    "authenticated_opening_in t
      \<lparr>opening_root=rt, opening_length=scale*clength, opening_index=i,
        opening_value=v, opening_path=path\<rparr>"
proof -
  from outcome obtain s1 path s2 ap s3 s4 where
    rv: "Some (v,s1) \<in> set_dist (execute protocol_absorb_read s)"
    and rp: "Some (path,s2) \<in> set_dist (execute (ntimes protocol_absorb_read (floor_log (scale*clength))) s1)"
    and check: "Some (ap,s3) \<in> set_dist (execute (check_authentication_path (scale*clength) i v path) s2)"
    and assertion: "Some ((),s4) \<in> set_dist (execute (assert (ap=rt)) s3)"
    and ret: "Some (v,t) \<in> set_dist (execute (return v) s4)"
    unfolding ro_query_decommitment_step_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  have ap: "ap=rt" using assertion unfolding assert_def
    by (cases "ap=rt") (auto simp: throw_no_outcome)
  have t: "t=s3" using assertion ret ap unfolding assert_def by simp
  have head: "PTranscript s = v # PTranscript s1"
    using protocol_absorb_read_outcome_with_lookup_chain[OF rv] by blast
  have tail: "PTranscript s1 = path @ PTranscript s2"
    and len: "length path = floor_log (scale*clength)"
    using ntimes_protocol_absorb_read_outcome_with_lookup_chain[OF rp] by blast+
  have tr: "PTranscript s = (v # path) @ PTranscript t"
    using head tail check_authentication_path_preserves_channel(2)[OF check] t by simp
  have bound: "merkle_path_bound rt (scale*clength) i v path t"
    using check_authentication_path_outcome_bound[OF check] ap t by simp
  have auth: "authenticated_opening_in t
      \<lparr>opening_root=rt, opening_length=scale*clength, opening_index=i,
        opening_value=v, opening_path=path\<rparr>"
    unfolding authenticated_opening_in_def using idx len bound by simp
  show ?thesis by (rule that[OF tr auth])
qed

definition serial_openings :: "'f authenticated_opening list \<Rightarrow> 'f list" where
  "serial_openings ops = List.concat (map (\<lambda>op. opening_value op # opening_path op) ops)"

lemma serial_ro_openings:
  fixes s t :: "'f protocol_channel"
  assumes outcome: "Some (vs,t) \<in> set_dist (execute (mmap (map (ro_query_decommitment_step rt) idxs)) s)"
    and bounds: "\<And>i. i \<in> set idxs \<Longrightarrow> i < scale*clength"
  shows "\<exists>ops. map opening_value ops = vs \<and> map opening_index ops = idxs \<and>
    partial_authenticated_table rt (scale*clength) ops t \<and>
    PTranscript s = serial_openings ops @ PTranscript t"
  using outcome bounds
proof (induction idxs arbitrary: s t vs)
  case Nil
  then show ?case by (auto simp: serial_openings_def partial_authenticated_table_def)
next
  case (Cons i idxs)
  obtain v vs' s1 where head: "Some (v,s1) \<in> set_dist (execute (ro_query_decommitment_step rt i) s)"
    and tail: "Some (vs',t) \<in> set_dist (execute (mmap (map (ro_query_decommitment_step rt) idxs)) s1)"
    and vs: "vs=v#vs'"
    using Cons.prems by (auto elim!: set_dist_bindE)
  have i: "i<scale*clength" using Cons.prems(2) by simp
  obtain path where tr: "PTranscript s = (v#path) @ PTranscript s1"
    and auth: "authenticated_opening_in s1
      \<lparr>opening_root=rt, opening_length=scale*clength, opening_index=i,
        opening_value=v, opening_path=path\<rparr>"
    by (rule serial_ro_opening[OF i head])
  obtain ops where vals: "map opening_value ops = vs'"
    and inds: "map opening_index ops = idxs"
    and table: "partial_authenticated_table rt (scale*clength) ops t"
    and tr_tail: "PTranscript s1 = serial_openings ops @ PTranscript t"
    using Cons.IH[OF tail] Cons.prems(2) by auto
  have ext: "s1\<le>t"
    using mmap_ro_query_decommitment_steps_outcome_with_lookup_chain[OF tail] by blast
  have auth_t: "authenticated_opening_in t
      \<lparr>opening_root=rt, opening_length=scale*clength, opening_index=i,
        opening_value=v, opening_path=path\<rparr>"
    by (rule authenticated_opening_in_mono[OF auth ext])
  let ?op = "\<lparr>opening_root=rt, opening_length=scale*clength, opening_index=i,
        opening_value=v, opening_path=path\<rparr>"
  show ?case
    by (rule exI[of _ "?op#ops"])
      (use vals inds table tr tr_tail auth_t vs in
        \<open>auto simp: partial_authenticated_table_def serial_openings_def\<close>)
qed

lemma serial_openings_shape:
  assumes inds: "map opening_index ops = powers_scaled idx"
    and auth: "partial_authenticated_table rt (scale*clength) ops s"
  shows "query_decommitment_transcript idx (map opening_value ops)
    (map opening_path ops) (serial_openings ops)"
  using auth arg_cong[OF inds, of length]
  unfolding query_decommitment_transcript_def serial_openings_def
    partial_authenticated_table_def authenticated_opening_in_def
  by (auto simp: zip_map_map zip_same_conv_map mult.commute o_def)

text \<open>This relation records authentication and serialization only. It does not
encode the folding equations or imply verifier acceptance.\<close>

definition serial_round_authenticated ::
  "'f \<Rightarrow> nat \<Rightarrow> ('f\<times>'f) list \<Rightarrow> ('f\<times>'f) list \<Rightarrow> 'f list \<Rightarrow> 'f protocol_channel \<Rightarrow> bool" where
  "serial_round_authenticated rt idx ffs cfs chunk s \<longleftrightarrow>
    (\<exists>ops ts cs. map opening_index ops = powers_scaled idx \<and>
      partial_authenticated_table rt (scale*clength) ops s \<and>
      fri_mfold_chunks_authenticated ffs (clength*scale) idx ts s \<and>
      fri_mfold_chunks_authenticated cfs (clength*scale) idx cs s \<and>
      chunk = serial_openings ops @ List.concat ts @ List.concat cs)"

lemma serial_round_authenticated_mono:
  assumes auth: "serial_round_authenticated rt idx ffs cfs chunk s" and ext: "s\<le>t"
  shows "serial_round_authenticated rt idx ffs cfs chunk t"
  using auth partial_authenticated_table_mono[OF _ ext]
    fri_mfold_chunks_authenticated_mono[OF _ ext]
  unfolding serial_round_authenticated_def by blast

lemma serial_round_authenticated_unique:
  assumes clean: "\<not> hash_map_output_collision s"
    and a: "serial_round_authenticated rt idx ffs cfs a s"
    and b: "serial_round_authenticated rt idx ffs cfs b s"
  shows "a=b"
proof -
  obtain ops ts cs ops' ts' cs' where
    inds: "map opening_index ops = map opening_index ops'"
    and pa: "partial_authenticated_table rt (scale*clength) ops s"
    and pb: "partial_authenticated_table rt (scale*clength) ops' s"
    and ta: "fri_mfold_chunks_authenticated ffs (clength*scale) idx ts s"
    and tb: "fri_mfold_chunks_authenticated ffs (clength*scale) idx ts' s"
    and ca: "fri_mfold_chunks_authenticated cfs (clength*scale) idx cs s"
    and cb: "fri_mfold_chunks_authenticated cfs (clength*scale) idx cs' s"
    and aa: "a = serial_openings ops @ List.concat ts @ List.concat cs"
    and bb: "b = serial_openings ops' @ List.concat ts' @ List.concat cs'"
    using a b unfolding serial_round_authenticated_def by metis
  have "ops=ops'" by (rule clean_ordered_partial_openings_unique[OF clean pa pb inds])
  moreover have "ts=ts'" by (rule clean_fri_chunks_unique[OF clean ta tb])
  moreover have "cs=cs'" by (rule clean_fri_chunks_unique[OF clean ca cb])
  ultimately show ?thesis using aa bb by simp
qed

lemma serial_round_ro_successor_unique:
  assumes clean: "\<not> hash_map_output_collision u"
    and a: "serial_round_authenticated rt idx ffs cfs a u"
    and b: "serial_round_authenticated rt idx ffs cfs b u"
    and ca: "ro_absorb_lookup_chain u start a next"
    and cb: "ro_absorb_lookup_chain u start b next'"
  shows "a=b" and "next=next'"
proof -
  show eq: "a=b" by (rule serial_round_authenticated_unique[OF clean a b])
  show "next=next'"
    using ro_absorb_lookup_chain_functional[OF ca] cb eq by simp
qed

lemma serial_ro_round:
  fixes s t :: "'f protocol_channel"
  assumes power: "clength*scale=2^N"
    and traces: "length ffs\<le>N" and comps: "length cfs\<le>N"
    and outcome: "Some ((),t) \<in> set_dist
      (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) s)"
  obtains raw chunk where
    "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    "serial_round_authenticated rt (index (to_nat raw)) ffs cfs chunk t"
    "PTranscript s = chunk @ PTranscript t"
    "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    "s\<le>t"
    "PQueryCounter t = Suc (PQueryCounter s)"
proof -
  obtain raw idx vs s0 s1 qc ts tc cs cc fi fn fp s2 ci cn cp where
    raw: "Some (raw,s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and idx: "idx=index(to_nat raw)"
    and lookup: "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    and query: "Some (vs,s1) \<in> set_dist (execute (mmap (ro_check_decommit_on_query rt idx)) s0)"
    and tshape: "fri_layers_transcript (length ffs) (clength*scale) ts tc"
    and ttr: "PTranscript s1 = tc @ PTranscript s2"
    and cshape: "fri_layers_transcript (length cfs) (clength*scale) cs cc"
    and ctr: "PTranscript s2 = cc @ PTranscript t"
    and fulltr: "PTranscript s = (qc @ tc @ cc) @ PTranscript t"
    and tlen: "length ts = length ffs"
    and ta: "\<forall>j<length ffs. fri_layer_chunk_authenticated (snd (ffs!j))
      (fri_layer_lengths (length ffs) (clength*scale)!j)
      (fri_layer_indices (length ffs) idx (clength*scale)!j) (ts!j) t"
    and clen: "length cs = length cfs"
    and ca: "\<forall>j<length cfs. fri_layer_chunk_authenticated (snd (cfs!j))
      (fri_layer_lengths (length cfs) (clength*scale)!j)
      (fri_layer_indices (length cfs) idx (clength*scale)!j) (cs!j) t"
    and trun: "Some ((fi,fv,fn,fp),s2) \<in> set_dist
      (execute (mfold (idx,hd vs,clength*scale,1) (ro_receive_query_commits ffs)) s1)"
    and crun: "Some ((ci,cv,cn,cp),t) \<in> set_dist
      (execute (mfold (idx,cp_eval alphas vs (h^idx*shift),clength*scale,1)
        (ro_receive_query_commits cfs)) s2)"
    by (rule ro_verifier_query_round_program_authenticated_consumed_fri_chunks[OF power traces comps outcome]) blast
  have idxin: "idx\<in>query_sample_space"
    using index_less_query_sample_space idx unfolding query_sample_space_def by simp
  have bounds: "\<And>i. i\<in>set(powers_scaled idx) \<Longrightarrow> i<scale*clength"
    using query_sample_space_powers_scaled_bound[OF idxin] by (simp add: mult.commute)
  obtain ops where vals: "map opening_value ops=vs"
    and inds: "map opening_index ops=powers_scaled idx"
    and auth: "partial_authenticated_table rt (scale*clength) ops s1"
    and qtr: "PTranscript s0=serial_openings ops @ PTranscript s1"
    using serial_ro_openings[OF query[unfolded ro_check_decommit_on_query_def] bounds] by blast
  have s12: "s1\<le>s2"
    using mfold_ro_fri_layer_opening_steps_outcome_extends_counter[
      OF trun[unfolded ro_receive_query_commits_def]] by simp
  have s2t: "s2\<le>t"
    using mfold_ro_fri_layer_opening_steps_outcome_extends_counter[
      OF crun[unfolded ro_receive_query_commits_def]] by simp
  have autht: "partial_authenticated_table rt (scale*clength) ops t"
    by (rule partial_authenticated_table_mono[OF auth hash_ext_trans[OF s12 s2t]])
  have rawtr: "PTranscript s0=PTranscript s"
    using receive_query_index_challenge_outcome[OF raw] by simp
  have qc: "qc=serial_openings ops" using fulltr qtr ttr ctr rawtr by simp
  have tc: "tc=List.concat ts" and cc: "cc=List.concat cs"
    using tshape cshape unfolding fri_layers_transcript_def by auto
  let ?chunk = "qc@tc@cc"
  have whole: "serial_round_authenticated rt (index(to_nat raw)) ffs cfs ?chunk t"
    unfolding serial_round_authenticated_def
    by (rule exI[of _ ops], rule exI[of _ ts], rule exI[of _ cs])
      (use inds autht ta ca tlen clen in
        \<open>simp add: fri_mfold_chunks_authenticated_def idx qc tc cc\<close>)
  obtain chunk' where tr': "PTranscript s=chunk'@PTranscript t"
    and chain': "ro_absorb_lookup_chain t (PState s) chunk' (PState t)"
    and ext: "s\<le>t" and counter: "PQueryCounter t=Suc(PQueryCounter s)"
    using ro_verifier_query_round_program_outcome_with_lookup_chain[OF outcome] by blast
  have same: "?chunk=chunk'" using fulltr tr' by simp
  have chain: "ro_absorb_lookup_chain t (PState s) ?chunk (PState t)"
    using chain' same by simp
  show ?thesis by (rule that[OF lookup whole fulltr chain ext counter])
qed

lemma serial_fri_roots_cong:
  assumes roots: "map snd ffs = map snd ffs'"
  shows "fri_mfold_chunks_authenticated ffs len idx chunks s =
    fri_mfold_chunks_authenticated ffs' len idx chunks s"
proof -
  have lengths: "length ffs = length ffs'"
    using arg_cong[OF roots, of length] by simp
  have nths: "\<And>j. j<length ffs \<Longrightarrow> snd(ffs!j)=snd(ffs'!j)"
    using arg_cong[OF roots, of "\<lambda>xs. xs!_"] lengths by (metis nth_map)
  show ?thesis unfolding fri_mfold_chunks_authenticated_def using lengths nths by auto
qed

lemma serial_round_roots_cong:
  assumes "map snd ffs = map snd ffs'" "map snd cfs = map snd cfs'"
  shows "serial_round_authenticated rt idx ffs cfs chunk s =
    serial_round_authenticated rt idx ffs' cfs' chunk s"
proof -
  note T = serial_fri_roots_cong[OF assms(1)]
  note C = serial_fri_roots_cong[OF assms(2)]
  show ?thesis unfolding serial_round_authenticated_def by (simp add: T C)
qed

lemma serial_ro_successful_successor:
  fixes s t s' t' u :: "'f protocol_channel"
  assumes power: "clength*scale=2^N"
    and traces: "length ffs\<le>N" and comps: "length cfs\<le>N"
    and rootsT: "map snd ffs = map snd ffs'"
    and rootsC: "map snd cfs = map snd cfs'"
    and left: "Some ((),t) \<in> set_dist
      (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) s)"
    and right: "Some ((),t') \<in> set_dist
      (execute (ro_verifier_query_round_program rt ffs' fv' alphas' cfs' cv') s')"
    and ext: "t\<le>u" and ext': "t'\<le>u"
    and clean: "\<not> hash_map_output_collision u"
    and prefix: "PState s = PState s'"
    and counter: "PQueryCounter s = PQueryCounter s'"
  shows "PState t = PState t'" and "PQueryCounter t = PQueryCounter t'"
    and "\<exists>chunk. PTranscript s = chunk @ PTranscript t \<and>
      PTranscript s' = chunk @ PTranscript t'"
proof -
  have traces': "length ffs'\<le>N" and comps': "length cfs'\<le>N"
    using traces comps arg_cong[OF rootsT, of length] arg_cong[OF rootsC, of length] by simp_all
  obtain raw a where la: "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    and aa: "serial_round_authenticated rt (index(to_nat raw)) ffs cfs a t"
    and tra: "PTranscript s = a @ PTranscript t"
    and ca: "ro_absorb_lookup_chain t (PState s) a (PState t)"
    and counta: "PQueryCounter t = Suc(PQueryCounter s)"
    by (rule serial_ro_round[OF power traces comps left]) blast
  obtain raw' b where lb: "fmlookup (HashMap t')
      (QueryIndexChallenge (PQueryCounter s') (PState s')) = Some raw'"
    and ab: "serial_round_authenticated rt (index(to_nat raw')) ffs' cfs' b t'"
    and trb: "PTranscript s' = b @ PTranscript t'"
    and cb: "ro_absorb_lookup_chain t' (PState s') b (PState t')"
    and countb: "PQueryCounter t' = Suc(PQueryCounter s')"
    by (rule serial_ro_round[OF power traces' comps' right]) blast
  have laU: "fmlookup (HashMap u)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF la ext])
  have lbU: "fmlookup (HashMap u)
      (QueryIndexChallenge (PQueryCounter s') (PState s')) = Some raw'"
    by (rule hash_extension_lookup[OF lb ext'])
  have raws: "raw=raw'" using laU lbU prefix counter by simp
  have aU: "serial_round_authenticated rt (index(to_nat raw)) ffs cfs a u"
    by (rule serial_round_authenticated_mono[OF aa ext])
  have bU': "serial_round_authenticated rt (index(to_nat raw')) ffs' cfs' b u"
    by (rule serial_round_authenticated_mono[OF ab ext'])
  have bU: "serial_round_authenticated rt (index(to_nat raw)) ffs cfs b u"
    using bU' serial_round_roots_cong[OF rootsT rootsC] raws by simp
  have eq: "a=b" by (rule serial_round_authenticated_unique[OF clean aU bU])
  have caU: "ro_absorb_lookup_chain u (PState s) a (PState t)"
    by (rule ro_absorb_lookup_chain_mono[OF ca ext])
  have cbU: "ro_absorb_lookup_chain u (PState s) a (PState t')"
    using ro_absorb_lookup_chain_mono[OF cb ext'] prefix eq by simp
  show "PState t=PState t'"
    by (rule ro_absorb_lookup_chain_functional[OF caU cbU])
  show "PQueryCounter t=PQueryCounter t'" using counta countb counter by simp
  show "\<exists>chunk. PTranscript s=chunk@PTranscript t \<and> PTranscript s'=chunk@PTranscript t'"
    using tra trb eq by blast
qed

end

subsection \<open>Two Query Path Fibers\<close>

context soundness
begin

text \<open>A final-map partition is available from actual authenticated
serialization. It is not an insertion-time measurable partition theorem.\<close>

definition pair_route_fiber where
  "pair_route_fiber S rt ffs cfs start u next =
    {raw\<in>S. \<exists>chunk. serial_round_authenticated rt (index (to_nat raw)) ffs cfs chunk u \<and>
      ro_absorb_lookup_chain u start chunk next}"

lemma pair_route_fibers_disjoint:
  assumes clean: "\<not> hash_map_output_collision u" and distinct: "v\<noteq>w"
  shows "pair_route_fiber S rt ffs cfs start u v \<inter>
    pair_route_fiber S rt ffs cfs start u w = {}"
  using serial_round_ro_successor_unique(2)[OF clean] distinct
  unfolding pair_route_fiber_def by blast

lemma pair_route_fiber_total:
  assumes clean: "\<not> hash_map_output_collision u"
    and fin: "finite S" "finite V"
  shows "(\<Sum>v\<in>V. card (pair_route_fiber S rt ffs cfs start u v)) \<le> card S"
proof -
  let ?F = "pair_route_fiber S rt ffs cfs start u"
  have finiteF: "\<And>v. finite (?F v)"
    using fin(1) unfolding pair_route_fiber_def by simp
  have disjoint: "\<And>v w. v\<in>V \<Longrightarrow> w\<in>V \<Longrightarrow> v\<noteq>w \<Longrightarrow> ?F v \<inter> ?F w = {}"
    by (rule pair_route_fibers_disjoint[OF clean])
  have eq: "card (\<Union>v\<in>V. ?F v) = (\<Sum>v\<in>V. card (?F v))"
    using fin(2) finiteF disjoint
    by (blast intro: card_UN_disjoint)
  have sub: "(\<Union>v\<in>V. ?F v) \<subseteq> S" unfolding pair_route_fiber_def by blast
  show ?thesis using card_mono[OF fin(1) sub] eq by simp
qed

lemma pair_route_from_success:
  fixes s t :: "'f protocol_channel"
  assumes power: "clength*scale=2^N"
    and traces: "length ffs\<le>N" and comps: "length cfs\<le>N"
    and out: "Some ((),t) \<in> set_dist
      (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) s)"
  obtains raw where
    "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    "raw \<in> pair_route_fiber UNIV rt ffs cfs (PState s) t (PState t)"
    "PQueryCounter t = Suc (PQueryCounter s)"
  by (rule serial_ro_round[OF power traces comps out])
    (auto simp: pair_route_fiber_def intro: that)

end

subsection \<open>Causal Route Weights\<close>

context soundness
begin

text \<open>Local proof relations only. Fixed roots in a lemma are not a new public
adversary restriction. No final-map partition is assumed to be predictable.\<close>

definition causal_route_roots where
  "causal_route_roots rt ffs cfs = insert rt (set (map snd ffs) \<union> set (map snd cfs))"

definition causal_route_targets where
  "causal_route_targets rt ffs cfs M v =
    weighted_semantic_interval_targets M \<union> causal_route_roots rt ffs cfs \<union> {v}"

lemma causal_opening_pullback:
  assumes ext: "s \<le> u" and auth: "authenticated_opening_in u op"
    and nt: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {opening_root op} s) s u"
  shows "authenticated_opening_in s op"
  using auth merkle_path_bound_pullback_or_prefix_target_hit[OF ext] nt
  unfolding authenticated_opening_in_def by blast

lemma causal_partial_pullback:
  assumes ext: "s \<le> u" and auth: "partial_authenticated_table rt len ops u"
    and nt: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {rt} s) s u"
  shows "partial_authenticated_table rt len ops s"
  using auth causal_opening_pullback[OF ext] nt
  unfolding partial_authenticated_table_def
  by fast

lemma causal_layer_pullback:
  assumes ext: "s \<le> u" and auth: "fri_layer_chunk_authenticated rt len idx chunk u"
    and nt: "\<not> hash_map_new_output_hit (merkle_prefix_path_targets {rt} s) s u"
  shows "fri_layer_chunk_authenticated rt len idx chunk s"
  using auth causal_opening_pullback[OF ext] nt
  unfolding fri_layer_chunk_authenticated_def
  by force

lemma causal_layers_pullback:
  assumes ext: "s \<le> u" and auth: "fri_mfold_chunks_authenticated bfs len idx chunks u"
    and nt: "\<And>rt. rt \<in> set (map snd bfs) \<Longrightarrow>
      \<not> hash_map_new_output_hit (merkle_prefix_path_targets {rt} s) s u"
  shows "fri_mfold_chunks_authenticated bfs len idx chunks s"
  using auth causal_layer_pullback[OF ext] nt
  unfolding fri_mfold_chunks_authenticated_def by auto

lemma causal_serial_pullback:
  assumes ext: "s \<le> u" and auth: "serial_round_authenticated rt idx ffs cfs chunk u"
    and nt: "\<And>root. root \<in> causal_route_roots rt ffs cfs \<Longrightarrow>
      \<not> hash_map_new_output_hit (merkle_prefix_path_targets {root} s) s u"
  shows "serial_round_authenticated rt idx ffs cfs chunk s"
  using auth causal_partial_pullback[OF ext] causal_layers_pullback[OF ext] nt
  unfolding serial_round_authenticated_def causal_route_roots_def by blast

lemma causal_route_query_update:
  "pair_route_fiber S rt ffs cfs start
     (channel_for_hash_map (fmupd (QueryIndexChallenge j v) raw M)) next =
   pair_route_fiber S rt ffs cfs start (channel_for_hash_map M) next"
  unfolding pair_route_fiber_def serial_round_authenticated_def
    partial_authenticated_table_def fri_mfold_chunks_authenticated_def
    fri_layer_chunk_authenticated_def by simp

lemma causal_route_mono:
  assumes ext: "s \<le> u"
  shows "pair_route_fiber S rt ffs cfs start s v \<subseteq>
    pair_route_fiber S rt ffs cfs start u v"
  using serial_round_authenticated_mono[OF _ ext]
    ro_absorb_lookup_chain_mono[OF _ ext]
  unfolding pair_route_fiber_def by blast

lemma causal_route_interval_pullback:
  assumes ext: "channel_for_hash_map M \<le> u"
    and nt: "\<not> hash_map_new_output_hit (causal_route_targets rt ffs cfs M v)
      (channel_for_hash_map M) u"
  shows "pair_route_fiber S rt ffs cfs start u v =
    pair_route_fiber S rt ffs cfs start (channel_for_hash_map M) v"
proof (rule subset_antisym)
  let ?s = "channel_for_hash_map M"
  let ?T = "causal_route_targets rt ffs cfs M v"
  have inputs: "transcript_absorb_input_values (HashMap ?s) \<subseteq> ?T"
    unfolding causal_route_targets_def weighted_semantic_interval_targets_def channel_for_hash_map_def by auto
  have target: "v \<in> ?T" unfolding causal_route_targets_def by simp
  have roots: "\<And>root. root \<in> causal_route_roots rt ffs cfs \<Longrightarrow>
    \<not> hash_map_new_output_hit (merkle_prefix_path_targets {root} ?s) ?s u"
    using nt unfolding causal_route_targets_def weighted_semantic_interval_targets_def
      merkle_prefix_path_targets_def hash_map_new_output_hit_def by blast
  show "pair_route_fiber S rt ffs cfs start u v \<subseteq> pair_route_fiber S rt ffs cfs start ?s v"
    using causal_serial_pullback[OF ext _ roots]
      weighted_semantic_absorb_interval_pullback[OF ext inputs nt _ target]
    unfolding pair_route_fiber_def by blast
  show "pair_route_fiber S rt ffs cfs start ?s v \<subseteq> pair_route_fiber S rt ffs cfs start u v"
    by (rule causal_route_mono[OF ext])
qed

lemma causal_targets_query_update:
  "causal_route_targets rt ffs cfs (fmupd (QueryIndexChallenge j v) raw M) v =
    causal_route_targets rt ffs cfs M v"
  unfolding causal_route_targets_def weighted_semantic_interval_targets_query_update by auto

lemma causal_route_first_insertion_recovery:
  assumes ext: "channel_for_hash_map (fmupd (QueryIndexChallenge j v) raw M) \<le> u"
    and nt: "\<not> hash_map_new_output_hit (causal_route_targets rt ffs cfs M v)
      (channel_for_hash_map (fmupd (QueryIndexChallenge j v) raw M)) u"
  shows "pair_route_fiber S rt ffs cfs start u v =
    pair_route_fiber S rt ffs cfs start (channel_for_hash_map M) v"
proof -
  have nohit: "\<not> hash_map_new_output_hit
    (causal_route_targets rt ffs cfs (fmupd (QueryIndexChallenge j v) raw M) v)
    (channel_for_hash_map (fmupd (QueryIndexChallenge j v) raw M)) u"
    using nt
    by (simp add: causal_targets_query_update)
  show ?thesis
    using causal_route_interval_pullback[OF ext nohit]
    by (simp only: causal_route_query_update)
qed

lemma causal_route_mixed_time_total:
  assumes clean: "\<not> hash_map_output_collision u"
    and fin: "finite S" "finite V"
    and ext: "\<And>v. v\<in>V \<Longrightarrow> M v \<le> u"
  shows "(\<Sum>v\<in>V. card (pair_route_fiber S rt ffs cfs start (M v) v)) \<le> card S"
proof -
  have point: "\<And>v. v\<in>V \<Longrightarrow> card (pair_route_fiber S rt ffs cfs start (M v) v) \<le>
    card (pair_route_fiber S rt ffs cfs start u v)"
    by (rule card_mono)
      (use fin causal_route_mono[OF ext] in \<open>auto simp: pair_route_fiber_def\<close>)
  have "(\<Sum>v\<in>V. card (pair_route_fiber S rt ffs cfs start (M v) v)) \<le>
    (\<Sum>v\<in>V. card (pair_route_fiber S rt ffs cfs start u v))"
    by (rule sum_mono) (use point in blast)
  also have "... \<le> card S" by (rule pair_route_fiber_total[OF clean fin])
  finally show ?thesis .
qed

lemma causal_targets_header_reduction:
  assumes roots: "causal_route_roots rt ffs cfs \<subseteq> transcript_absorb_message_values M"
  shows "causal_route_targets rt ffs cfs M v = weighted_semantic_interval_targets M \<union> {v}"
  using roots unfolding causal_route_targets_def weighted_semantic_interval_targets_def by blast

lemma causal_targets_card:
  "card (causal_route_targets rt ffs cfs M v) \<le>
    5 * card (fmdom' M) + 2 + length ffs + length cfs"
proof -
  have roots: "card (causal_route_roots rt ffs cfs) \<le> 1 + length ffs + length cfs"
    using card_length[of "rt # map snd ffs @ map snd cfs"]
    unfolding causal_route_roots_def by simp
  show ?thesis
    using card_Un_le[of "weighted_semantic_interval_targets M" "causal_route_roots rt ffs cfs"]
      card_Un_le[of "weighted_semantic_interval_targets M \<union> causal_route_roots rt ffs cfs" "{v}"]
      weighted_semantic_interval_targets_card[of M] roots
    unfolding causal_route_targets_def by simp
qed

lemma causal_targets_finite[simp]:
  "finite (causal_route_targets rt ffs cfs M v)"
  unfolding causal_route_targets_def causal_route_roots_def by simp

lemma causal_route_late_charge:
  assumes budget: "hash_target_program (causal_route_targets rt ffs cfs M v) q K"
  shows "wp_event K (hash_new_output_hit_event (causal_route_targets rt ffs cfs M v) t) t \<le>
    nnreal (q * (5 * card (fmdom' M) + 2 + length ffs + length cfs)) / nnreal size"
proof -
  have "wp_event K (hash_new_output_hit_event (causal_route_targets rt ffs cfs M v) t) t \<le>
    hash_target_budget_value (causal_route_targets rt ffs cfs M v) q"
    using budget unfolding hash_target_program_def hash_target_budget_def by blast
  also have "... \<le> nnreal (q * (5 * card (fmdom' M) + 2 + length ffs + length cfs)) / nnreal size"
    unfolding hash_target_budget_value_def
    by (rule nnreal_nat_divide_right_mono) (rule mult_left_mono[OF causal_targets_card], simp)
  finally show ?thesis .
qed

lemma causal_route_success_at_child_insertion:
  assumes power: "clength*scale=2^N"
    and traces: "length ffs\<le>N" and comps: "length cfs\<le>N"
    and out: "Some ((),t) \<in> set_dist
      (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) s)"
    and t_ext: "t \<le> u"
    and first_ext: "channel_for_hash_map
      (fmupd (QueryIndexChallenge (Suc (PQueryCounter s)) (PState t)) child M) \<le> u"
    and nt: "\<not> hash_map_new_output_hit (causal_route_targets rt ffs cfs M (PState t))
      (channel_for_hash_map
        (fmupd (QueryIndexChallenge (Suc (PQueryCounter s)) (PState t)) child M)) u"
  obtains raw where
    "fmlookup (HashMap u) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    "raw \<in> pair_route_fiber UNIV rt ffs cfs (PState s) (channel_for_hash_map M) (PState t)"
    "PQueryCounter t = Suc (PQueryCounter s)"
proof -
  obtain raw where lookup: "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    and fiber: "raw \<in> pair_route_fiber UNIV rt ffs cfs (PState s) t (PState t)"
    and count: "PQueryCounter t = Suc (PQueryCounter s)"
    by (rule pair_route_from_success[OF power traces comps out]) blast
  have lu: "fmlookup (HashMap u) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF lookup t_ext])
  have fu: "raw \<in> pair_route_fiber UNIV rt ffs cfs (PState s) u (PState t)"
    using fiber causal_route_mono[OF t_ext] by blast
  have old: "raw \<in> pair_route_fiber UNIV rt ffs cfs (PState s) (channel_for_hash_map M) (PState t)"
    using fu causal_route_first_insertion_recovery[OF first_ext nt] by simp
  show thesis by (rule that[OF lu old count])
qed

lemma causal_route_history_interval_pullback:
  assumes ext: "channel_for_hash_map M \<le> u"
    and nt: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets M \<union> {v}) (channel_for_hash_map M) u"
    and roots: "causal_route_roots rt ffs cfs \<subseteq> set header"
    and history: "ro_absorb_lookup_chain u init (header @ rest) start"
  shows "pair_route_fiber S rt ffs cfs start u v =
    pair_route_fiber S rt ffs cfs start (channel_for_hash_map M) v"
proof (rule subset_antisym)
  let ?s = "channel_for_hash_map M"
  show "pair_route_fiber S rt ffs cfs start u v \<subseteq> pair_route_fiber S rt ffs cfs start ?s v"
  proof
    fix raw assume member: "raw \<in> pair_route_fiber S rt ffs cfs start u v"
    then obtain chunk where serial: "serial_round_authenticated rt (index (to_nat raw)) ffs cfs chunk u"
      and chain: "ro_absorb_lookup_chain u start chunk v"
      unfolding pair_route_fiber_def by blast
    have full: "ro_absorb_lookup_chain u init ((header @ rest) @ chunk) v"
      by (rule ro_absorb_lookup_chain_append[OF history chain])
    have inputs: "transcript_absorb_input_values (HashMap ?s) \<subseteq> weighted_semantic_interval_targets M \<union> {v}"
      unfolding weighted_semantic_interval_targets_def channel_for_hash_map_def by auto
    have old: "ro_absorb_lookup_chain ?s init ((header @ rest) @ chunk) v"
      by (rule weighted_semantic_absorb_interval_pullback[OF ext inputs nt full]) simp
    have roots_old: "causal_route_roots rt ffs cfs \<subseteq> transcript_absorb_message_values M"
      using roots ro_absorb_lookup_chain_messages_subset[OF old] by auto
    have target_eq: "causal_route_targets rt ffs cfs M v = weighted_semantic_interval_targets M \<union> {v}"
      by (rule causal_targets_header_reduction[OF roots_old])
    have nohit: "\<not> hash_map_new_output_hit (causal_route_targets rt ffs cfs M v) ?s u"
      using nt by (simp add: target_eq)
    show "raw \<in> pair_route_fiber S rt ffs cfs start ?s v"
      using member causal_route_interval_pullback[OF ext nohit] by simp
  qed
  show "pair_route_fiber S rt ffs cfs start ?s v \<subseteq> pair_route_fiber S rt ffs cfs start u v"
    by (rule causal_route_mono[OF ext])
qed

lemma causal_route_history_first_insertion:
  assumes ext: "channel_for_hash_map (fmupd (QueryIndexChallenge j v) raw M) \<le> u"
    and nt: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets M \<union> {v})
      (channel_for_hash_map (fmupd (QueryIndexChallenge j v) raw M)) u"
    and roots: "causal_route_roots rt ffs cfs \<subseteq> set header"
    and history: "ro_absorb_lookup_chain u init (header @ rest) start"
  shows "pair_route_fiber S rt ffs cfs start u v =
    pair_route_fiber S rt ffs cfs start (channel_for_hash_map M) v"
proof -
  have nohit: "\<not> hash_map_new_output_hit
    (weighted_semantic_interval_targets (fmupd (QueryIndexChallenge j v) raw M) \<union> {v})
    (channel_for_hash_map (fmupd (QueryIndexChallenge j v) raw M)) u"
    using nt by (simp add: weighted_semantic_interval_targets_query_update Un_assoc)
  show ?thesis
    using causal_route_history_interval_pullback[OF ext nohit roots history]
    by (simp only: causal_route_query_update)
qed

lemma causal_routing_minimum_retained:
  fixes v w :: "'f"
  assumes clean: "\<not> hash_map_output_collision u"
    and ext1: "s \<le> u" and ext2: "t \<le> u"
    and distinct: "v \<noteq> w" and fin: "finite S"
  shows "card (pair_route_fiber S rt ffs cfs start s v) +
      card (pair_route_fiber S rt ffs cfs start t w) \<le> card S"
proof -
  let ?M = "\<lambda>x. if x=v then s else t"
  have maps: "\<And>x. x\<in>{v,w} \<Longrightarrow> ?M x \<le> u" using ext1 ext2 by auto
  have total: "(\<Sum>x\<in>{v,w}. card (pair_route_fiber S rt ffs cfs start (?M x) x)) \<le> card S"
    by (rule causal_route_mixed_time_total[OF clean fin _ maps]) simp
  show ?thesis using total distinct by simp
qed

end

subsection \<open>Predictable Two Child Weights\<close>

context soundness
begin

text \<open>These expectation helpers permit the second weight and test to depend
on the first outcome. They are not an embedding of the complete STARK run.\<close>

lemma causal_wp_add:
  "wp m (\<lambda>out. X out + Y out) s = wp m X s + wp m Y s"
  unfolding wp_def dist_expect_def by (simp add: algebra_simps sum.distrib)

lemma causal_wp_scale:
  "wp m (\<lambda>out. c * X out) s = c * wp m X s"
  unfolding wp_def dist_expect_def by (simp add: algebra_simps sum_distrib_left)

lemma causal_wp_const:
  "wp m (\<lambda>_. c) s = c"
  unfolding wp_def dist_expect_def
  by (simp add: sum_distrib_right[symmetric] sum_map_def[symmetric])

lemma causal_wp_indicator:
  "wp m (\<lambda>out. if P out then c else 0) s = c * wp_event m P s"
proof -
  have eq: "(\<lambda>out. if P out then c else 0) = (\<lambda>out. c * (if P out then 1 else 0))"
    by (rule ext) simp
  show ?thesis unfolding eq wp_event_def by (rule causal_wp_scale)
qed

lemma causal_predictable_two_weight_bound:
  fixes p W a :: prob
  assumes first: "wp_event m A s \<le> p"
    and second: "\<And>out. wp_event (K out) (B out) (t out) \<le> p"
    and cap: "\<And>out. a + b out \<le> W"
  shows "wp m (\<lambda>out.
      (if A out then a else 0) +
      wp (K out) (\<lambda>next. if B out next then b out else 0) (t out)) s \<le> p * W"
proof -
  have point: "\<And>out.
    (if A out then a else 0) +
    wp (K out) (\<lambda>next. if B out next then b out else 0) (t out) \<le>
    (if A out then a else 0) + p * (W - a)"
  proof -
    fix out
    have capr: "nn2real a + nn2real (b out) \<le> nn2real W"
      using cap[of out] by (metis nn2real_add nn2real_le_iff)
    have b: "b out \<le> W - a"
      using capr by (subst nn2real_le_iff[symmetric]) (simp only: nn2real_minus; linarith)
    have "wp (K out) (\<lambda>next. if B out next then b out else 0) (t out)
      = b out * wp_event (K out) (B out) (t out)"
      by (rule causal_wp_indicator)
    also have "... \<le> b out * p" by (rule mult_left_mono[OF second]) simp
    also have "... \<le> p * (W - a)" using mult_left_mono[OF b, of p]
      by (simp add: mult.commute)
    finally show "(if A out then a else 0) +
      wp (K out) (\<lambda>next. if B out next then b out else 0) (t out) \<le>
      (if A out then a else 0) + p * (W - a)"
      by (rule add_left_mono)
  qed
  have "wp m (\<lambda>out. (if A out then a else 0) +
      wp (K out) (\<lambda>next. if B out next then b out else 0) (t out)) s \<le>
      wp m (\<lambda>out. (if A out then a else 0) + p * (W - a)) s"
    by (rule wp_mono_on_support) (rule point)
  also have "... = a * wp_event m A s + p * (W - a)"
    by (simp only: causal_wp_add causal_wp_indicator causal_wp_const)
  also have "... \<le> a * p + p * (W - a)"
    by (rule add_right_mono) (rule mult_left_mono[OF first], simp)
  also have "... = p * W"
  proof -
    have capr: "nn2real a + nn2real (b None) \<le> nn2real W"
      using cap[of None] by (metis nn2real_add nn2real_le_iff)
    have a: "nn2real a \<le> nn2real W" using capr nn2real_nonneg[of "b None"] by linarith
    have delta: "0 \<le> nn2real W - nn2real a" using a by linarith
    show ?thesis
      by (subst nn2real_eq_iff[symmetric])
        (simp only: nn2real_add nn2real_mult nn2real_minus max.absorb2[OF delta]; simp add: algebra_simps)
  qed
  finally show ?thesis .
qed

lemma causal_clip_weight_cap:
  fixes a b W :: prob
  assumes "a \<le> W"
  shows "a + min b (W-a) \<le> W"
  using assms unfolding min_def by transfer (auto simp: max_def)

lemma causal_clip_weight_exact:
  fixes a b W :: prob
  assumes "a + b \<le> W"
  shows "min a W = a" and "min b (W-a) = b"
  using assms by (transfer; auto simp: min_def max_def)+

lemma causal_clipped_two_weight_bound:
  fixes p W a :: prob
  assumes first: "wp_event m A s \<le> p"
    and second: "\<And>out. wp_event (K out) (B out) (t out) \<le> p"
  shows "wp m (\<lambda>out.
      (if A out then min a W else 0) +
      wp (K out) (\<lambda>next. if B out next then min (b out) (W-min a W) else 0) (t out)) s \<le> p * W"
  by (rule causal_predictable_two_weight_bound[OF first second])
    (rule causal_clip_weight_cap, simp)

lemma causal_semantic_probe_weight:
  fixes s :: "'f protocol_channel"
  shows "wp (pair_probe k)
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
      if pair_insert_good rT rC e then w else 0) s \<le>
    w * (nnreal (query_raw_preimage_card_envelope
      (mca_decoded_semantic_query_index_bound rT rC)) / nnreal size)"
proof -
  have eq: "(\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
      if pair_insert_good rT rC e then w else 0) =
    (\<lambda>out. if (case out of None \<Rightarrow> False | Some (e,t) \<Rightarrow> pair_insert_good rT rC e) then w else 0)"
    by (rule ext) (simp split: option.splits prod.splits)
  show ?thesis unfolding eq causal_wp_indicator
    by (rule mult_left_mono[OF wp_pair_probe]) simp
qed

lemma causal_two_child_semantic_score_bound:
  fixes s :: "'f protocol_channel" and rT rC :: nat
  defines "p \<equiv> nnreal (query_raw_preimage_card_envelope
    (mca_decoded_semantic_query_index_bound rT rC)) / nnreal size"
    and "good \<equiv> \<lambda>out. case out of None \<Rightarrow> False | Some (e,t) \<Rightarrow> pair_insert_good rT rC e"
  shows "wp (pair_probe k)
    (\<lambda>out. (if good out then min a p else 0) +
      wp (pair_probe (next_key out))
        (\<lambda>next. if good next then min (b out) (p-min a p) else 0) (next_state out)) s \<le> p^2"
proof -
  have first: "wp_event (pair_probe k) good s \<le> p"
    unfolding good_def p_def by (rule wp_pair_probe)
  have second: "\<And>out. wp_event (pair_probe (next_key out)) good (next_state out) \<le> p"
    unfolding good_def p_def by (rule wp_pair_probe)
  show ?thesis using causal_clipped_two_weight_bound[OF first second, where W=p and a=a and b=b]
    by (simp add: power2_eq_square)
qed

end

end
