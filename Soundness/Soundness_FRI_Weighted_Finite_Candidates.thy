(* Title: Stark/Soundness_FRI_Weighted_Finite_Candidates.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Finite_Candidates
  imports
    "Soundness_FRI_Weighted_Query_Routing"
begin

section \<open>Finite Candidates for weighted MCA soundness\<close>

text \<open>Finite-map insertion logs, candidate potentials and a single bad-connection ledger. Intermediate two-query accounting is retained as a proved foundation for adaptive and arbitrary-length arguments.\<close>

subsection \<open>Fixed Parent Event Score\<close>

context soundness
begin

text \<open>One marked child before a fixed parent, one after it. Intervening
programs retain private context and all their oracle work. This is a bounded
marked experiment, not a new protocol or a full-run insertion log.\<close>

definition ep_raw where
  "ep_raw e = snd (snd e)"

definition ep_fresh where
  "ep_fresh k e \<longleftrightarrow> (case e of (M,key,raw) \<Rightarrow> key=k \<and> fmlookup M key=None)"

definition ep_partition_event where
  "ep_partition_event rT rC S A k out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some ((c,r,d),u) \<Rightarrow>
      ep_fresh k r \<and>
      ((ep_raw r\<in>A \<and> pair_insert_good rT rC c) \<or>
       (ep_raw r\<in>S-A \<and> pair_insert_good rT rC d)))"

definition ep_finish where
  "ep_finish K c z r y d = do {K c z r y d; return (c,r,d)}"

definition ep_after where
  "ep_after C K c z r = do {
    w \<leftarrow> C c z r;
    d \<leftarrow> pair_probe (fst w);
    ep_finish K c z r (snd w) d}"

definition ep_middle where
  "ep_middle C K k c z = do {r \<leftarrow> pair_probe k; ep_after C K c z r}"

definition ep_after_first where
  "ep_after_first D C K k c = do {z \<leftarrow> D c; ep_middle C K k c z}"

definition ep_experiment where
  "ep_experiment D C K child parent = do {
    c \<leftarrow> pair_probe child; ep_after_first D C K parent c}"

lemma ep_after_output:
  assumes "out \<in> set_dist (execute (ep_after C K c z r) s)"
    and "out=Some ((c',r',d),u)"
  shows "c'=c \<and> r'=r"
  using assms unfolding ep_after_def ep_finish_def
  by (auto elim!: set_dist_bindE)

lemma ep_after_zero:
  assumes bad: "\<not> ep_fresh k r \<or>
    (\<not> (ep_raw r\<in>A \<and> pair_insert_good rT rC c) \<and> ep_raw r\<notin>S-A)"
  shows "wp_event (ep_after C K c z r) (ep_partition_event rT rC S A k) s = 0"
proof -
  have no: "\<And>out. out \<in> set_dist (execute (ep_after C K c z r) s) \<Longrightarrow>
    \<not> ep_partition_event rT rC S A k out"
  proof -
    fix out
    assume mem: "out \<in> set_dist (execute (ep_after C K c z r) s)"
    show "\<not> ep_partition_event rT rC S A k out"
      using mem bad unfolding ep_after_def ep_finish_def ep_partition_event_def
      by (cases out) (auto elim!: set_dist_bindE split: prod.splits)
  qed
  have "\<not> 0 < wp_event (ep_after C K c z r) (ep_partition_event rT rC S A k) s"
  proof
    assume pos: "0 < wp_event (ep_after C K c z r) (ep_partition_event rT rC S A k) s"
    show False by (rule wp_event_pos_imp_exists_support[OF pos]) (use no in blast)
  qed
  then show ?thesis by simp
qed

abbreviation ro_mca_weighted_semantic_base where
  "ro_mca_weighted_semantic_base rT rC \<equiv> nnreal (query_raw_preimage_card_envelope
    (mca_decoded_semantic_query_index_bound rT rC)) / nnreal size"

definition ep_mass :: "'f set \<Rightarrow> prob" where
  "ep_mass A = nnreal (card A) / nnreal size"

lemma ep_after_later_bound:
  assumes no_early: "\<not> (ep_raw r\<in>A \<and> pair_insert_good rT rC c)"
  shows "wp_event (ep_after C K c z r) (ep_partition_event rT rC S A k) s \<le> ro_mca_weighted_semantic_base rT rC"
  unfolding ep_after_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> ep_partition_event rT rC S A k None"
    by (simp add: ep_partition_event_def)
next
  fix w t
  assume "Some (w,t) \<in> set_dist (execute (C c z r) s)"
  show "wp_event (pair_probe (fst w) \<bind> ep_finish K c z r (snd w))
    (ep_partition_event rT rC S A k) t \<le> ro_mca_weighted_semantic_base rT rC"
  proof (rule wp_event_bind_bound_by_head_event[OF wp_pair_probe])
    show "ep_partition_event rT rC S A k None \<Longrightarrow>
      (case None of None \<Rightarrow> False | Some (e,t) \<Rightarrow> pair_insert_good rT rC e)"
      by (simp add: ep_partition_event_def)
  next
    fix d u out
    assume "Some (d,u) \<in> set_dist (execute (pair_probe (fst w)) t)"
      and tail: "out \<in> set_dist (execute (ep_finish K c z r (snd w) d) u)"
      and ev: "ep_partition_event rT rC S A k out"
    show "case Some (d,u) of None \<Rightarrow> False | Some (e,t) \<Rightarrow> pair_insert_good rT rC e"
      using tail ev no_early unfolding ep_finish_def ep_partition_event_def
      by (cases out) (auto elim!: set_dist_bindE split: prod.splits)
  qed
qed

lemma ep_after_partition_bound:
  "wp_event (ep_after C K c z r) (ep_partition_event rT rC S A k) s \<le>
    (if ep_fresh k r then
      (if ep_raw r\<in>A \<and> pair_insert_good rT rC c then 1 else 0) +
      (if ep_raw r\<in>S-A then ro_mca_weighted_semantic_base rT rC else 0)
     else 0)"
  using ep_after_later_bound[where C=C and K=K and c=c and z=z and r=r and rT=rT and rC=rC and S=S and A=A and k=k and s=s]
    ep_after_zero[where C=C and K=K and c=c and z=z and r=r and rT=rT and rC=rC and S=S and A=A and k=k and s=s]
    wp_event_le_1[of "ep_after C K c z r" "ep_partition_event rT rC S A k" s]
  by fastforce

lemma ep_probe_raw_weight:
  fixes s :: "'f protocol_channel"
  assumes fresh: "fmlookup (HashMap s) k = None"
  shows "wp (pair_probe k)
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some (r,t) \<Rightarrow>
      if ep_raw r\<in>A then w else 0) s = ep_mass A * w"
proof -
  have indicator: "wp_event (pair_probe k)
    (\<lambda>out. case out of None \<Rightarrow> False | Some (r,t) \<Rightarrow> ep_raw r\<in>A) s = ep_mass A"
    unfolding pair_probe_def ep_raw_def wp_event_def ep_mass_def
    using dist_expect_hash_dist_fresh_indicator[OF fresh, of A]
    by (simp add: wpsimps)
  have eq: "(\<lambda>out. case out of None \<Rightarrow> 0 | Some (r,t) \<Rightarrow> if ep_raw r\<in>A then w else 0) =
    (\<lambda>out. if (case out of None \<Rightarrow> False | Some (r,t) \<Rightarrow> ep_raw r\<in>A) then w else 0)"
    by (rule ext) (simp split: option.splits prod.splits)
  show ?thesis unfolding eq causal_wp_indicator indicator by (simp add: mult.commute)
qed

lemma ep_probe_guarded_weight:
  fixes s :: "'f protocol_channel"
  shows "wp (pair_probe k)
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some (r,t) \<Rightarrow>
      if ep_fresh k r \<and> ep_raw r\<in>A then w else 0) s \<le> ep_mass A * w"
proof (cases "fmlookup (HashMap s) k = None")
  case True
  have eq: "wp (pair_probe k)
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some (r,t) \<Rightarrow> if ep_fresh k r \<and> ep_raw r\<in>A then w else 0) s =
    wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (r,t) \<Rightarrow> if ep_raw r\<in>A then w else 0) s"
    unfolding pair_probe_def ep_fresh_def ep_raw_def using True by (simp add: wpsimps)
  show ?thesis by (simp only: eq ep_probe_raw_weight[OF True] order_refl)
next
  case False
  have eq: "wp (pair_probe k)
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some (r,t) \<Rightarrow> if ep_fresh k r \<and> ep_raw r\<in>A then w else 0) s = 0"
    unfolding pair_probe_def ep_fresh_def ep_raw_def using False
    by (force simp: wpsimps)
  show ?thesis by (simp add: eq)
qed

lemma ep_middle_bound:
  "wp_event (ep_middle C K k c z) (ep_partition_event rT rC S A k) s \<le>
    ep_mass A * (if pair_insert_good rT rC c then 1 else 0) +
    ep_mass (S-A) * ro_mca_weighted_semantic_base rT rC"
proof -
  let ?P = "ep_partition_event rT rC S A k"
  let ?X = "\<lambda>out. case out of None \<Rightarrow> 0 | Some (r,t) \<Rightarrow>
    if ep_fresh k r \<and> ep_raw r\<in>A then (if pair_insert_good rT rC c then 1 else 0) else 0"
  let ?Y = "\<lambda>out. case out of None \<Rightarrow> 0 | Some (r,t) \<Rightarrow>
    if ep_fresh k r \<and> ep_raw r\<in>S-A then ro_mca_weighted_semantic_base rT rC else 0"
  have "wp_event (ep_middle C K k c z) ?P s \<le> wp (pair_probe k) (\<lambda>out. ?X out + ?Y out) s"
    unfolding ep_middle_def wp_event_def wp_bind
  proof (rule wp_mono_on_support)
    fix out
    assume "out \<in> set_dist (execute (pair_probe k) s)"
    show "(case out of None \<Rightarrow> if ?P None then 1 else 0 | Some (r,t) \<Rightarrow>
      wp (ep_after C K c z r) (\<lambda>out. if ?P out then 1 else 0) t) \<le> ?X out + ?Y out"
    proof (cases out)
      case None
      then show ?thesis by (simp add: ep_partition_event_def)
    next
      case (Some a)
      obtain r t where a: "a=(r,t)" by (cases a) simp
      have bound: "wp_event (ep_after C K c z r) ?P t \<le>
        (if ep_fresh k r then
          (if ep_raw r\<in>A \<and> pair_insert_good rT rC c then 1 else 0) +
          (if ep_raw r\<in>S-A then ro_mca_weighted_semantic_base rT rC else 0) else 0)"
        by (rule ep_after_partition_bound)
      show ?thesis using bound unfolding wp_event_def
        by (cases "ep_fresh k r"; cases "ep_raw r\<in>A";
            cases "pair_insert_good rT rC c"; cases "ep_raw r\<in>S-A")
          (simp_all add: Some a)
    qed
  qed
  also have "... = wp (pair_probe k) ?X s + wp (pair_probe k) ?Y s"
    by (rule causal_wp_add)
  also have "... \<le> ep_mass A * (if pair_insert_good rT rC c then 1 else 0) +
    ep_mass (S-A) * ro_mca_weighted_semantic_base rT rC"
    by (rule add_mono; rule ep_probe_guarded_weight)
  finally show ?thesis .
qed

lemma ep_after_first_bound:
  "wp_event (ep_after_first D C K k c) (ep_partition_event rT rC S A k) s \<le>
    ep_mass A * (if pair_insert_good rT rC c then 1 else 0) +
    ep_mass (S-A) * ro_mca_weighted_semantic_base rT rC"
  unfolding ep_after_first_def
  by (rule wp_event_bind_bound_by_cont)
    (simp add: ep_partition_event_def, rule ep_middle_bound)

lemma ep_mass_partition:
  assumes "A \<subseteq> S"
  shows "ep_mass A + ep_mass (S-A) = ep_mass S"
proof -
  have union: "A \<union> (S-A) = S" using assms by blast
  have cards: "card A + card (S-A) = card S"
    using card_Un_disjoint[of A "S-A"] union by auto
  have realcards: "real (card A) + real (card (S-A)) = real (card S)"
    using cards by simp
  show ?thesis
    apply (subst nn2real_eq_iff[symmetric])
    unfolding ep_mass_def
    apply (simp only: nn2real_add nn2real_divide nn2real_nnreal)
    using realcards by (simp add: add_divide_distrib[symmetric])
qed

lemma ep_experiment_partition_bound:
  assumes subset: "A \<subseteq> S"
  shows "wp_event (ep_experiment D C K child parent)
    (ep_partition_event rT rC S A parent) s \<le> ro_mca_weighted_semantic_base rT rC * ep_mass S"
proof -
  let ?P = "ep_partition_event rT rC S A parent"
  let ?E = "\<lambda>out. case out of None \<Rightarrow> False | Some (c,t) \<Rightarrow> pair_insert_good rT rC c"
  have "wp_event (ep_experiment D C K child parent) ?P s \<le>
    wp (pair_probe child) (\<lambda>out. (if ?E out then ep_mass A else 0) + ep_mass (S-A) * ro_mca_weighted_semantic_base rT rC) s"
    unfolding ep_experiment_def wp_event_def wp_bind
  proof (rule wp_mono_on_support)
    fix out
    assume "out \<in> set_dist (execute (pair_probe child) s)"
    show "(case out of None \<Rightarrow> if ?P None then 1 else 0 | Some (c,t) \<Rightarrow>
        wp (ep_after_first D C K parent c) (\<lambda>out. if ?P out then 1 else 0) t) \<le>
      (if ?E out then ep_mass A else 0) + ep_mass (S-A) * ro_mca_weighted_semantic_base rT rC"
    proof (cases out)
      case None
      then show ?thesis by (simp add: ep_partition_event_def)
    next
      case (Some a)
      obtain c t where a: "a=(c,t)" by (cases a) simp
      have bound: "wp_event (ep_after_first D C K parent c) ?P t \<le>
        ep_mass A * (if pair_insert_good rT rC c then 1 else 0) +
        ep_mass (S-A) * ro_mca_weighted_semantic_base rT rC"
        by (rule ep_after_first_bound)
      show ?thesis using bound unfolding wp_event_def
        by (fastforce simp: Some a)
    qed
  qed
  also have "... = ep_mass A * wp_event (pair_probe child) ?E s + ep_mass (S-A) * ro_mca_weighted_semantic_base rT rC"
    by (simp only: causal_wp_add causal_wp_indicator causal_wp_const)
  also have "... \<le> ep_mass A * ro_mca_weighted_semantic_base rT rC + ep_mass (S-A) * ro_mca_weighted_semantic_base rT rC"
    by (rule add_right_mono, rule mult_left_mono[OF wp_pair_probe]) simp
  also have "... = ro_mca_weighted_semantic_base rT rC * ep_mass S"
    by (subst ep_mass_partition[OF subset, symmetric]) (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma ep_experiment_semantic_partition:
  assumes clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and initial: "PState adversary_initial_state \<notin> hash_map_output_values (channel_for_hash_map M)"
    and subset: "A \<subseteq> {raw. weighted_semantic_hit rT rC M start raw}"
  shows "wp_event (ep_experiment D C K child parent)
    (ep_partition_event rT rC {raw. weighted_semantic_hit rT rC M start raw} A parent) s \<le>
    (ro_mca_weighted_semantic_base rT rC)^2"
proof -
  have mass: "ep_mass {raw. weighted_semantic_hit rT rC M start raw} \<le> ro_mca_weighted_semantic_base rT rC"
    unfolding ep_mass_def
    by (rule nnreal_nat_divide_right_mono[OF weighted_semantic_hit_fiber[OF clean initial]])
  have "wp_event (ep_experiment D C K child parent)
      (ep_partition_event rT rC {raw. weighted_semantic_hit rT rC M start raw} A parent) s \<le>
      ro_mca_weighted_semantic_base rT rC * ep_mass {raw. weighted_semantic_hit rT rC M start raw}"
    by (rule ep_experiment_partition_bound[OF subset])
  also have "... \<le> ro_mca_weighted_semantic_base rT rC * ro_mca_weighted_semantic_base rT rC"
    by (rule mult_left_mono[OF mass]) simp
  finally show ?thesis by (simp add: power2_eq_square)
qed

end

subsection \<open>Fixed Parent Authenticated Bridge\<close>

context soundness
begin

text \<open>This is an augmented clean routing event, not a definition of verifier
success. Successful verifier execution supplies authentication separately.
The first two logs are child then parent; the third is a later child.\<close>

definition ep_clean_selected where
  "ep_clean_selected rT rC S rt ffs cfs start j v M out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some ((c,r,d),u) \<Rightarrow>
      \<exists>x Md w y.
        c=(M,QueryIndexChallenge (Suc j) v,x) \<and>
        d=(Md,QueryIndexChallenge (Suc j) w,y) \<and>
        ep_fresh (QueryIndexChallenge j start) r \<and> ep_raw r\<in>S \<and>
        channel_for_hash_map M \<le> u \<and>
        channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M) \<le> u \<and>
        channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M) \<le> channel_for_hash_map Md \<and>
        \<not> hash_map_output_collision u \<and>
        \<not> hash_map_new_output_hit (causal_route_targets rt ffs cfs M v)
          (channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M)) u \<and>
        ((pair_insert_good rT rC c \<and>
          ep_raw r \<in> pair_route_fiber S rt ffs cfs start u v) \<or>
         (pair_insert_good rT rC d \<and>
          ep_raw r \<in> pair_route_fiber S rt ffs cfs start u w)))"

lemma ep_later_fresh_different:
  assumes ext: "channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M) \<le> channel_for_hash_map Md"
    and good: "pair_insert_good rT rC (Md,QueryIndexChallenge (Suc j) w,y)"
  shows "w \<noteq> v"
proof
  assume eq: "w=v"
  have fresh: "fmlookup Md (QueryIndexChallenge (Suc j) w) = None"
    using good unfolding pair_insert_good_def by simp
  have lookup: "fmlookup (HashMap (channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M)))
    (QueryIndexChallenge (Suc j) v) = Some x"
    by (simp add: channel_for_hash_map_def)
  have old: "fmlookup Md (QueryIndexChallenge (Suc j) v) = Some x"
    using hash_extension_lookup[OF lookup ext] by (simp add: channel_for_hash_map_def)
  show False using old fresh eq by simp
qed

lemma ep_clean_selected_partition:
  assumes event: "ep_clean_selected rT rC S rt ffs cfs start j v M out"
  shows "ep_partition_event rT rC S
    (pair_route_fiber S rt ffs cfs start (channel_for_hash_map M) v)
    (QueryIndexChallenge j start) out"
proof -
  obtain c r d u x Md w y where out: "out=Some ((c,r,d),u)"
    and c: "c=(M,QueryIndexChallenge (Suc j) v,x)"
    and d: "d=(Md,QueryIndexChallenge (Suc j) w,y)"
    and fresh: "ep_fresh (QueryIndexChallenge j start) r" and raw: "ep_raw r\<in>S"
    and ext: "channel_for_hash_map M \<le> u"
    and extc: "channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M) \<le> u"
    and extd: "channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M) \<le> channel_for_hash_map Md"
    and clean: "\<not> hash_map_output_collision u"
    and nt: "\<not> hash_map_new_output_hit (causal_route_targets rt ffs cfs M v)
      (channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M)) u"
    and cases: "(pair_insert_good rT rC c \<and> ep_raw r \<in> pair_route_fiber S rt ffs cfs start u v) \<or>
      (pair_insert_good rT rC d \<and> ep_raw r \<in> pair_route_fiber S rt ffs cfs start u w)"
    using event unfolding ep_clean_selected_def by (auto split: option.splits prod.splits)
  let ?A = "pair_route_fiber S rt ffs cfs start (channel_for_hash_map M) v"
  have split: "(ep_raw r\<in>?A \<and> pair_insert_good rT rC c) \<or>
    (ep_raw r\<in>S-?A \<and> pair_insert_good rT rC d)"
  using cases
  proof
    assume early: "pair_insert_good rT rC c \<and> ep_raw r \<in> pair_route_fiber S rt ffs cfs start u v"
    have "pair_route_fiber S rt ffs cfs start u v = ?A"
      by (rule causal_route_first_insertion_recovery[OF extc nt])
    then show ?thesis using early by blast
  next
    assume later: "pair_insert_good rT rC d \<and> ep_raw r \<in> pair_route_fiber S rt ffs cfs start u w"
    have different: "w\<noteq>v" by (rule ep_later_fresh_different[OF extd, where rT=rT and rC=rC and y=y]) (use later d in simp)
    have disjoint: "pair_route_fiber S rt ffs cfs start u v \<inter> pair_route_fiber S rt ffs cfs start u w = {}"
      by (rule pair_route_fibers_disjoint[OF clean]) (use different in auto)
    have notA: "ep_raw r\<notin>?A"
      using later disjoint causal_route_mono[OF ext, of S rt ffs cfs start v] by blast
    show ?thesis using later raw notA by blast
  qed
  show ?thesis using out fresh split unfolding ep_partition_event_def by simp
qed

lemma ep_clean_selected_probability:
  fixes rT rC :: nat and start :: 'f
  assumes clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and initial: "PState adversary_initial_state \<notin> hash_map_output_values (channel_for_hash_map M)"
  defines "S \<equiv> {raw. weighted_semantic_hit rT rC M start raw}"
  shows "wp_event (ep_experiment D C K (QueryIndexChallenge (Suc j) v) (QueryIndexChallenge j start))
    (ep_clean_selected rT rC S rt ffs cfs start j v M) s \<le> (ro_mca_weighted_semantic_base rT rC)^2"
proof -
  let ?A = "pair_route_fiber S rt ffs cfs start (channel_for_hash_map M) v"
  have subset: "?A \<subseteq> S" unfolding pair_route_fiber_def by blast
  have "wp_event (ep_experiment D C K (QueryIndexChallenge (Suc j) v) (QueryIndexChallenge j start))
      (ep_clean_selected rT rC S rt ffs cfs start j v M) s \<le>
    wp_event (ep_experiment D C K (QueryIndexChallenge (Suc j) v) (QueryIndexChallenge j start))
      (ep_partition_event rT rC S ?A (QueryIndexChallenge j start)) s"
    by (rule wp_event_mono) (rule ep_clean_selected_partition)
  also have "... \<le> (ro_mca_weighted_semantic_base rT rC)^2"
    unfolding S_def by (rule ep_experiment_semantic_partition[OF clean initial])
      (use subset in \<open>simp add: S_def\<close>)
  finally show ?thesis .
qed

end

subsection \<open>Fixed Parent Execution Connection\<close>

context soundness
begin

text \<open>Deterministic connection to a successful original verifier round.
Semantic residual membership and late exceptions remain explicit: acceptance
alone is not asserted to imply an MCA residual event.\<close>

lemma ep_update_submap:
  assumes ext: "channel_for_hash_map M \<le> u"
    and lookup: "fmlookup (HashMap u) k = Some raw"
  shows "channel_for_hash_map (fmupd k raw M) \<le> u"
  using assms unfolding channel_for_hash_map_def less_eq_hash_ext_def less_eq_fmap_def
  by auto

lemma ep_extend_update:
  assumes fresh: "fmlookup M k=None"
  shows "channel_for_hash_map M \<le> channel_for_hash_map (fmupd k raw M)"
  using fresh unfolding channel_for_hash_map_def less_eq_hash_ext_def less_eq_fmap_def
  by auto

lemma ep_semantic_before_parent:
  assumes ext: "channel_for_hash_map M \<le> u"
    and fresh: "fmlookup M (QueryIndexChallenge j start)=None"
    and lookup: "fmlookup (HashMap u) (QueryIndexChallenge j start)=Some raw"
    and nt: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets M \<union> {start})
      (channel_for_hash_map M) u"
    and hit: "weighted_semantic_hit rT rC (HashMap u) start raw"
  shows "weighted_semantic_hit rT rC M start raw"
proof -
  let ?A = "channel_for_hash_map (fmupd (QueryIndexChallenge j start) raw M)"
  have MA: "channel_for_hash_map M \<le> ?A" by (rule ep_extend_update[OF fresh])
  have AU: "?A \<le> channel_for_hash_map (HashMap u)"
    using ep_update_submap[OF ext lookup]
    by (simp add: channel_for_hash_map_def less_eq_hash_ext_def)
  have ntA: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets M \<union> {start})
      ?A (channel_for_hash_map (HashMap u))"
    using hash_map_new_output_hit_extend_initial[OF MA] nt
    by (auto simp: hash_map_new_output_hit_def channel_for_hash_map_def)
  obtain I where ready: "weighted_semantic_ready rT rC (HashMap u) start I"
    and raw: "raw\<in>query_index_raw_preimage I"
    using hit unfolding weighted_semantic_hit_def by blast
  have "weighted_semantic_ready rT rC M start I"
    by (rule weighted_semantic_first_insertion_recovery[OF AU ntA ready])
  then show ?thesis using raw unfolding weighted_semantic_hit_def by blast
qed

lemma ep_success_route_with_log:
  fixes qs qt u :: "'f protocol_channel"
  assumes power: "clength*scale=2^N"
    and traces: "length ffs\<le>N" and comps: "length cfs\<le>N"
    and out: "Some ((),qt) \<in> set_dist
      (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) qs)"
    and ext: "qt\<le>u"
    and lookup: "fmlookup (HashMap u) (QueryIndexChallenge (PQueryCounter qs) (PState qs))=Some raw"
    and raw: "raw\<in>S"
  shows "raw\<in>pair_route_fiber S rt ffs cfs (PState qs) u (PState qt)"
proof -
  obtain x where x:
    "fmlookup (HashMap qt) (QueryIndexChallenge (PQueryCounter qs) (PState qs))=Some x"
    "x\<in>pair_route_fiber UNIV rt ffs cfs (PState qs) qt (PState qt)"
    by (rule pair_route_from_success[OF power traces comps out]) blast
  have eq: "x=raw" using hash_extension_lookup[OF x(1) ext] lookup by simp
  have "x\<in>pair_route_fiber UNIV rt ffs cfs (PState qs) u (PState qt)"
    using causal_route_mono[OF ext] x(2) by blast
  then show ?thesis using raw eq unfolding pair_route_fiber_def by blast
qed

definition ep_actual_selected where
  "ep_actual_selected rT rC rt ffs fv alphas cfs cv start j v M out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some ((c,r,d),u) \<Rightarrow>
      \<exists>x Mr z Md w y qs qt.
        c=(M,QueryIndexChallenge (Suc j) v,x) \<and>
        r=(Mr,QueryIndexChallenge j start,z) \<and>
        d=(Md,QueryIndexChallenge (Suc j) w,y) \<and>
        fmlookup Mr (QueryIndexChallenge j start)=None \<and>
        channel_for_hash_map M \<le> channel_for_hash_map Mr \<and>
        fmlookup (HashMap u) (QueryIndexChallenge j start)=Some z \<and>
        channel_for_hash_map M \<le> u \<and>
        channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M) \<le> u \<and>
        channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M) \<le> channel_for_hash_map Md \<and>
        \<not> hash_map_output_collision u \<and>
        \<not> hash_map_new_output_hit (causal_route_targets rt ffs cfs M v)
          (channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M)) u \<and>
        \<not> hash_map_new_output_hit (weighted_semantic_interval_targets M \<union> {start})
          (channel_for_hash_map M) u \<and>
        weighted_semantic_hit rT rC (HashMap u) start z \<and>
        PQueryCounter qs=j \<and> PState qs=start \<and> qt\<le>u \<and>
        Some ((),qt) \<in> set_dist
          (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) qs) \<and>
        ((PState qt=v \<and> pair_eventual_ready rT rC (HashMap u) c \<and>
            \<not> pair_late_connection (HashMap u) c) \<or>
         (PState qt=w \<and> pair_eventual_ready rT rC (HashMap u) d \<and>
            \<not> pair_late_connection (HashMap u) d)))"

lemma ep_actual_selected_clean:
  assumes power: "clength*scale=2^N"
    and traces: "length ffs\<le>N" and comps: "length cfs\<le>N"
    and event: "ep_actual_selected rT rC rt ffs fv alphas cfs cv start j v M out"
  shows "ep_clean_selected rT rC {raw. weighted_semantic_hit rT rC M start raw}
    rt ffs cfs start j v M out"
proof -
  obtain c r d u x Mr z Md w y qs qt where out: "out=Some ((c,r,d),u)"
    and c: "c=(M,QueryIndexChallenge (Suc j) v,x)"
    and r: "r=(Mr,QueryIndexChallenge j start,z)"
    and d: "d=(Md,QueryIndexChallenge (Suc j) w,y)"
    and fresh: "fmlookup Mr (QueryIndexChallenge j start)=None"
    and MMr: "channel_for_hash_map M \<le> channel_for_hash_map Mr"
    and lookup: "fmlookup (HashMap u) (QueryIndexChallenge j start)=Some z"
    and ext: "channel_for_hash_map M \<le> u"
    and extc: "channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M) \<le> u"
    and extd: "channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M) \<le> channel_for_hash_map Md"
    and clean: "\<not> hash_map_output_collision u"
    and ntc: "\<not> hash_map_new_output_hit (causal_route_targets rt ffs cfs M v)
      (channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x M)) u"
    and ntp: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets M \<union> {start})
      (channel_for_hash_map M) u"
    and hit: "weighted_semantic_hit rT rC (HashMap u) start z"
    and counter: "PQueryCounter qs=j" and state: "PState qs=start" and qext: "qt\<le>u"
    and success: "Some ((),qt) \<in> set_dist
      (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) qs)"
    and selected: "(PState qt=v \<and> pair_eventual_ready rT rC (HashMap u) c \<and> \<not> pair_late_connection (HashMap u) c) \<or>
      (PState qt=w \<and> pair_eventual_ready rT rC (HashMap u) d \<and> \<not> pair_late_connection (HashMap u) d)"
    using event unfolding ep_actual_selected_def by (auto split: option.splits prod.splits)
  have freshM: "fmlookup M (QueryIndexChallenge j start)=None"
    using hash_extension_none[OF MMr] fresh by (simp add: channel_for_hash_map_def)
  have oldhit: "weighted_semantic_hit rT rC M start z"
    by (rule ep_semantic_before_parent[OF ext freshM lookup ntp hit])
  let ?S = "{raw. weighted_semantic_hit rT rC M start raw}"
  have route: "z\<in>pair_route_fiber ?S rt ffs cfs start u (PState qt)"
    using ep_success_route_with_log[OF power traces comps success qext,
      where raw=z and S="?S"] lookup oldhit
    by (simp add: counter state)
  have good: "(PState qt=v \<and> pair_insert_good rT rC c) \<or>
    (PState qt=w \<and> pair_insert_good rT rC d)"
    using selected pair_eventual_recovery by blast
  show ?thesis unfolding ep_clean_selected_def out
    using c r d fresh oldhit ext extc extd clean ntc good route
    unfolding ep_fresh_def ep_raw_def by auto
qed

lemma ep_actual_selected_probability:
  assumes power: "clength*scale=2^N"
    and traces: "length ffs\<le>N" and comps: "length cfs\<le>N"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and initial: "PState adversary_initial_state \<notin> hash_map_output_values (channel_for_hash_map M)"
  shows "wp_event (ep_experiment D C K (QueryIndexChallenge (Suc j) v) (QueryIndexChallenge j start))
    (ep_actual_selected rT rC rt ffs fv alphas cfs cv start j v M) s \<le> (ro_mca_weighted_semantic_base rT rC)^2"
proof -
  have "wp_event (ep_experiment D C K (QueryIndexChallenge (Suc j) v) (QueryIndexChallenge j start))
      (ep_actual_selected rT rC rt ffs fv alphas cfs cv start j v M) s \<le>
    wp_event (ep_experiment D C K (QueryIndexChallenge (Suc j) v) (QueryIndexChallenge j start))
      (ep_clean_selected rT rC {raw. weighted_semantic_hit rT rC M start raw} rt ffs cfs start j v M) s"
    by (rule wp_event_mono) (rule ep_actual_selected_clean[OF power traces comps])
  also have "... \<le> (ro_mca_weighted_semantic_base rT rC)^2"
    by (rule ep_clean_selected_probability[OF clean initial])
  finally show ?thesis .
qed

end

subsection \<open>Finite Candidate Accounting\<close>

datatype 'a fc_account =
  FC_Pre "'a set" "'a set" | FC_Live 'a | FC_Won | FC_Lost

context soundness
begin

text \<open>Ghost accounting for one fixed parent key. No hash call is suppressed.\<close>

definition fc_valid where
  "fc_valid S acc \<longleftrightarrow> (case acc of FC_Pre W B \<Rightarrow> W\<subseteq>B \<and> B\<subseteq>S
    | FC_Live z \<Rightarrow> z\<in>S | FC_Won \<Rightarrow> True | FC_Lost \<Rightarrow> True)"

fun fc_potential where
  "fc_potential rT rC S (FC_Pre W B) = ep_mass W + ro_mca_weighted_semantic_base rT rC * ep_mass (S-B)"
| "fc_potential rT rC S (FC_Live z) = ro_mca_weighted_semantic_base rT rC"
| "fc_potential rT rC S FC_Won = 1"
| "fc_potential rT rC S FC_Lost = 0"

definition fc_fiber where
  "fc_fiber S rt ffs cfs start j (e :: ('f protocol_hash_input,'f) fmap \<times> 'f protocol_hash_input \<times> 'f) =
    (case e of (M,k,x) \<Rightarrow> (case k of QueryIndexChallenge i v \<Rightarrow>
      if i=Suc j \<and> fmlookup M k=None
      then pair_route_fiber S rt ffs cfs start (channel_for_hash_map M) v
      else {} | _ \<Rightarrow> {}))"

fun fc_step where
  "fc_step rT rC S rt ffs cfs start j (FC_Pre W B) e =
    (if fst (snd e)=QueryIndexChallenge j start then
       if ep_fresh (QueryIndexChallenge j start) e then
         if ep_raw e\<in>W then FC_Won
         else if ep_raw e\<in>S-B then FC_Live (ep_raw e) else FC_Lost
       else FC_Lost
     else let A=fc_fiber S rt ffs cfs start j e-B in
       FC_Pre (W\<union>(if pair_insert_good rT rC e then A else {})) (B\<union>A))"
| "fc_step rT rC S rt ffs cfs start j (FC_Live z) e =
    (if z\<in>fc_fiber S rt ffs cfs start j e then
       if pair_insert_good rT rC e then FC_Won else FC_Lost
     else FC_Live z)"
| "fc_step rT rC S rt ffs cfs start j FC_Won e = FC_Won"
| "fc_step rT rC S rt ffs cfs start j FC_Lost e = FC_Lost"

lemma fc_fiber_subset: "fc_fiber S rt ffs cfs start j e \<subseteq> S"
  unfolding fc_fiber_def pair_route_fiber_def
  by (auto split: prod.splits protocol_hash_input.splits)

lemma fc_fiber_answer_independent:
  "fc_fiber S rt ffs cfs start j (M,k,x) =
   fc_fiber S rt ffs cfs start j (M,k,y)"
  by (simp add: fc_fiber_def)

lemma fc_valid_step:
  assumes "fc_valid S acc"
  shows "fc_valid S (fc_step rT rC S rt ffs cfs start j acc e)"
  using assms fc_fiber_subset[of S rt ffs cfs start j e]
  by (cases acc) (auto simp: fc_valid_def Let_def)

lemma fc_mass_disjoint:
  assumes disj: "A\<inter>B={}"
  shows "ep_mass (A\<union>B)=ep_mass A+ep_mass B"
proof -
  have sub: "A\<subseteq>A\<union>B" by blast
  have diff: "(A\<union>B)-A=B" using disj by blast
  show ?thesis using ep_mass_partition[OF sub] by (simp add: diff)
qed

lemma fc_reservation_partition:
  assumes AS: "A\<subseteq>S-B"
  shows "ep_mass (S-B) = ep_mass A + ep_mass (S-(B\<union>A))"
proof -
  have eq: "(S-B)-A = S-(B\<union>A)" by blast
  show ?thesis using ep_mass_partition[OF AS] by (simp only: eq)
qed

lemma fc_probe_payoff_bound:
  fixes L :: "(('f protocol_hash_input,'f) fmap \<times> 'f protocol_hash_input \<times> 'f) \<Rightarrow> prob"
  assumes point: "\<And>raw. L (HashMap s,k,raw) \<le>
    a + (if pair_insert_good rT rC (HashMap s,k,raw) then b else 0)"
  shows "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow> L e) s \<le>
    a + b * ro_mca_weighted_semantic_base rT rC"
proof -
  let ?E = "\<lambda>out. case out of None \<Rightarrow> False | Some (e,t) \<Rightarrow> pair_insert_good rT rC e"
  have "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow> L e) s \<le>
    wp (pair_probe k) (\<lambda>out. a + (if ?E out then b else 0)) s"
  proof (rule wp_mono_on_support)
    fix out
    assume mem: "out\<in>set_dist (execute (pair_probe k) s)"
    show "(case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow> L e) \<le> a + (if ?E out then b else 0)"
    proof (cases out)
      case None
      then show ?thesis by simp
    next
      case (Some et)
      obtain e t where et: "et=(e,t)" by (cases et) simp
      obtain raw where "e=(HashMap s,k,raw)"
        using mem Some et by (auto elim: pair_probe_outcome)
      then show ?thesis using point by (simp add: Some et)
    qed
  qed
  also have "... = a + b * wp_event (pair_probe k) ?E s"
    by (simp only: causal_wp_add causal_wp_const causal_wp_indicator)
  also have "... \<le> a + b * ro_mca_weighted_semantic_base rT rC"
    by (rule add_left_mono, rule mult_left_mono[OF wp_pair_probe]) simp
  finally show ?thesis .
qed

lemma fc_pre_child_step_bound:
  assumes valid: "fc_valid S (FC_Pre W B)"
    and different: "k\<noteq>QueryIndexChallenge j start"
  shows "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
    fc_potential rT rC S (fc_step rT rC S rt ffs cfs start j (FC_Pre W B) e)) s
    \<le> fc_potential rT rC S (FC_Pre W B)"
proof -
  let ?A = "fc_fiber S rt ffs cfs start j (HashMap s,k,undefined)-B"
  have WB: "W\<subseteq>B" using valid by (simp add: fc_valid_def)
  have AS: "?A\<subseteq>S-B" using fc_fiber_subset by blast
  have disj: "W\<inter>?A={}" using WB by blast
  have split: "ep_mass (S-B)=ep_mass ?A+ep_mass (S-(B\<union>?A))"
    by (rule fc_reservation_partition[OF AS])
  have "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
      fc_potential rT rC S (fc_step rT rC S rt ffs cfs start j (FC_Pre W B) e)) s \<le>
    (ep_mass W + ro_mca_weighted_semantic_base rT rC * ep_mass (S-(B\<union>?A))) + ep_mass ?A * ro_mca_weighted_semantic_base rT rC"
  proof (rule fc_probe_payoff_bound)
    fix raw
    have A: "fc_fiber S rt ffs cfs start j (HashMap s,k,raw)-B=?A"
      by (simp add: fc_fiber_def)
    show "fc_potential rT rC S
      (fc_step rT rC S rt ffs cfs start j (FC_Pre W B) (HashMap s,k,raw)) \<le>
      ep_mass W + ro_mca_weighted_semantic_base rT rC * ep_mass (S-(B\<union>?A)) +
      (if pair_insert_good rT rC (HashMap s,k,raw) then ep_mass ?A else 0)"
      using different fc_mass_disjoint[OF disj]
      by (simp add: Let_def A algebra_simps)
  qed
  also have "... = fc_potential rT rC S (FC_Pre W B)"
    by (simp add: split algebra_simps)
  finally show ?thesis .
qed

lemma fc_pre_parent_step_bound:
  assumes valid: "fc_valid S (FC_Pre W B)"
  shows "wp (pair_probe (QueryIndexChallenge j start))
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
      fc_potential rT rC S (fc_step rT rC S rt ffs cfs start j (FC_Pre W B) e)) s \<le>
    fc_potential rT rC S (FC_Pre W B)"
proof -
  let ?k = "QueryIndexChallenge j start"
  let ?X = "\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow> if ep_fresh ?k e \<and> ep_raw e\<in>W then 1 else 0"
  let ?Y = "\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow> if ep_fresh ?k e \<and> ep_raw e\<in>S-B then ro_mca_weighted_semantic_base rT rC else 0"
  have "wp (pair_probe ?k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
      fc_potential rT rC S (fc_step rT rC S rt ffs cfs start j (FC_Pre W B) e)) s \<le>
    wp (pair_probe ?k) (\<lambda>out. ?X out + ?Y out) s"
  proof (rule wp_mono_on_support)
    fix out
    assume mem: "out\<in>set_dist (execute (pair_probe ?k) s)"
    show "(case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
      fc_potential rT rC S (fc_step rT rC S rt ffs cfs start j (FC_Pre W B) e))
      \<le> ?X out + ?Y out"
    proof (cases out)
      case None
      then show ?thesis by simp
    next
      case (Some et)
      obtain e t where et: "et=(e,t)" by (cases et) simp
      obtain raw where e: "e=(HashMap s,?k,raw)"
        using mem Some et by (auto elim: pair_probe_outcome)
      show ?thesis by (simp add: Some et e split: if_splits)
    qed
  qed
  also have "... = wp (pair_probe ?k) ?X s + wp (pair_probe ?k) ?Y s"
    by (rule causal_wp_add)
  also have "... \<le> ep_mass W * 1 + ep_mass (S-B) * ro_mca_weighted_semantic_base rT rC"
    by (rule add_mono; rule ep_probe_guarded_weight)
  finally show ?thesis by (simp add: mult.commute)
qed

lemma fc_live_step_bound:
  "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
    fc_potential rT rC S (fc_step rT rC S rt ffs cfs start j (FC_Live z) e)) s \<le> ro_mca_weighted_semantic_base rT rC"
proof (cases "z\<in>fc_fiber S rt ffs cfs start j (HashMap s,k,undefined)")
  case True
  have "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
      fc_potential rT rC S (fc_step rT rC S rt ffs cfs start j (FC_Live z) e)) s
    \<le> 0 + 1 * ro_mca_weighted_semantic_base rT rC"
  proof (rule fc_probe_payoff_bound)
    fix raw
    show "fc_potential rT rC S
      (fc_step rT rC S rt ffs cfs start j (FC_Live z) (HashMap s,k,raw)) \<le>
      0 + (if pair_insert_good rT rC (HashMap s,k,raw) then 1 else 0)"
      using True by (simp add: fc_fiber_def)
  qed
  then show ?thesis by simp
next
  case False
  have "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
      fc_potential rT rC S (fc_step rT rC S rt ffs cfs start j (FC_Live z) e)) s
    \<le> ro_mca_weighted_semantic_base rT rC + 0 * ro_mca_weighted_semantic_base rT rC"
  proof (rule fc_probe_payoff_bound)
    fix raw
    show "fc_potential rT rC S
      (fc_step rT rC S rt ffs cfs start j (FC_Live z) (HashMap s,k,raw)) \<le>
      ro_mca_weighted_semantic_base rT rC + (if pair_insert_good rT rC (HashMap s,k,raw) then 0 else 0)"
      using False by (simp add: fc_fiber_def)
  qed
  then show ?thesis by simp
qed

lemma fc_step_potential_bound:
  assumes valid: "fc_valid S acc"
  shows "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
    fc_potential rT rC S (fc_step rT rC S rt ffs cfs start j acc e)) s \<le>
    fc_potential rT rC S acc"
proof (cases acc)
  case (FC_Pre W B)
  show ?thesis
  proof (cases "k=QueryIndexChallenge j start")
    case True
    show ?thesis unfolding FC_Pre True by (rule fc_pre_parent_step_bound) (use valid FC_Pre in simp)
  next
    case False
    show ?thesis unfolding FC_Pre by (rule fc_pre_child_step_bound[OF _ False]) (use valid FC_Pre in simp)
  qed
next
  case (FC_Live z)
  show ?thesis unfolding FC_Live by (simp only: fc_potential.simps; rule fc_live_step_bound)
next
  case FC_Won
  show ?thesis unfolding FC_Won fc_step.simps fc_potential.simps
    by (rule wp_le_const_on_support) (simp split: option.splits prod.splits)
next
  case FC_Lost
  show ?thesis unfolding FC_Lost fc_step.simps fc_potential.simps
    by (rule wp_le_const_on_support) (simp split: option.splits prod.splits)
qed

end

subsection \<open>Finite Candidate Log\<close>

context soundness
begin

text \<open>A bounded adaptive stream of original hash calls. A selector can stop,
fail, or choose any tag; an arbitrary private context is carried between choices. Accounting is not
passed to that selector.\<close>

fun fc_walk where
  "fc_walk 0 C step priv hist acc = return (acc,hist)"
| "fc_walk (Suc n) C step priv hist acc = do {
    choice \<leftarrow> C priv hist;
    case choice of None \<Rightarrow> return (acc,hist)
    | Some k \<Rightarrow> do {
        e \<leftarrow> pair_probe (fst k);
        fc_walk n C step (snd k) (hist@[e]) (step acc e)}}"

definition fc_won_event where
  "fc_won_event out \<longleftrightarrow> (case out of None \<Rightarrow> False | Some ((acc,hist),u) \<Rightarrow> acc=FC_Won)"

lemma fc_walk_potential:
  assumes valid: "I acc"
    and preserve: "\<And>acc e. I acc \<Longrightarrow> I (step acc e)"
    and one: "\<And>acc k t. I acc \<Longrightarrow>
      wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow> P (step acc e)) t \<le> P acc"
  shows "wp (fc_walk n C step priv hist acc)
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((acc,hist),u) \<Rightarrow> P acc) s \<le> P acc"
  using valid
proof (induction n arbitrary: priv hist acc s)
  case 0
  then show ?case by (simp add: wpsimps)
next
  case (Suc n)
  let ?V = "\<lambda>out. case out of None \<Rightarrow> 0 | Some ((acc,hist),u) \<Rightarrow> P acc"
  show ?case
    unfolding fc_walk.simps wp_bind
  proof (rule wp_le_const_on_support)
    fix out
    assume mem: "out\<in>set_dist (execute (C priv hist) s)"
    show "(case out of None \<Rightarrow> ?V None | Some (choice,t) \<Rightarrow>
      wp (case choice of None \<Rightarrow> return (acc,hist) | Some k \<Rightarrow>
        pair_probe (fst k) \<bind> (\<lambda>e. fc_walk n C step (snd k) (hist@[e]) (step acc e))) ?V t) \<le> P acc"
    proof (cases out)
      case None
      then show ?thesis by simp
    next
      case (Some ct)
      obtain choice t where ct: "ct=(choice,t)" by (cases ct) simp
      have bound: "wp (case choice of None \<Rightarrow> return (acc,hist) | Some k \<Rightarrow>
        pair_probe (fst k) \<bind> (\<lambda>e. fc_walk n C step (snd k) (hist@[e]) (step acc e))) ?V t \<le> P acc"
      proof (cases choice)
        case None
        then show ?thesis by (simp add: wpsimps)
      next
        case (Some k)
        have "wp (pair_probe (fst k) \<bind> (\<lambda>e. fc_walk n C step (snd k) (hist@[e]) (step acc e))) ?V t \<le>
          wp (pair_probe (fst k)) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow> P (step acc e)) t"
          unfolding wp_bind
        proof (rule wp_mono_on_support)
          fix eout
          assume "eout\<in>set_dist (execute (pair_probe (fst k)) t)"
          show "(case eout of None \<Rightarrow> ?V None | Some (e,u) \<Rightarrow>
              wp (fc_walk n C step (snd k) (hist@[e]) (step acc e)) ?V u) \<le>
            (case eout of None \<Rightarrow> 0 | Some (e,u) \<Rightarrow> P (step acc e))"
            using Suc.IH[OF preserve[OF Suc.prems]]
            by (cases eout) (auto split: prod.splits)
        qed
        also have "... \<le> P acc" by (rule one[OF Suc.prems])
        finally show ?thesis using Some by simp
      qed
      then show ?thesis by (simp add: Some ct)
    qed
  qed
qed

lemma fc_walk_accounting_bound:
  assumes valid: "fc_valid S acc"
  shows "wp (fc_walk n C (fc_step rT rC S rt ffs cfs start j) priv hist acc)
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((acc,hist),u) \<Rightarrow> fc_potential rT rC S acc) s \<le>
    fc_potential rT rC S acc"
  by (rule fc_walk_potential[where I="fc_valid S" and P="fc_potential rT rC S", OF valid])
    (rule fc_valid_step, assumption, rule fc_step_potential_bound, assumption)

lemma fc_walk_won_bound:
  "wp_event (fc_walk n C (fc_step rT rC S rt ffs cfs start j) priv hist (FC_Pre {} {}))
    fc_won_event s \<le> ro_mca_weighted_semantic_base rT rC * ep_mass S"
proof -
  have "wp_event (fc_walk n C (fc_step rT rC S rt ffs cfs start j) priv hist (FC_Pre {} {}))
      fc_won_event s \<le>
    wp (fc_walk n C (fc_step rT rC S rt ffs cfs start j) priv hist (FC_Pre {} {}))
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((acc,hist),u) \<Rightarrow> fc_potential rT rC S acc) s"
    unfolding wp_event_def
    by (rule wp_mono_on_support)
      (auto simp: fc_won_event_def split: option.splits prod.splits fc_account.splits)
  also have "... \<le> fc_potential rT rC S (FC_Pre {} {})"
    by (rule fc_walk_accounting_bound) (simp add: fc_valid_def)
  finally show ?thesis by (simp add: ep_mass_def)
qed

fun fc_history where
  "fc_history (M :: ('f protocol_hash_input,'f) fmap) [] U \<longleftrightarrow> M=U"
| "fc_history M (e#es) U \<longleftrightarrow> (case e of (Me,k,x) \<Rightarrow>
    Me=M \<and> (fmlookup M k=None \<or> fmlookup M k=Some x) \<and>
    fc_history (fmupd k x M) es U)"

lemma fc_history_extension:
  assumes "fc_history M es U"
  shows "channel_for_hash_map M \<le> channel_for_hash_map U"
  using assms
proof (induction es arbitrary: M)
  case Nil
  then show ?case using hash_ext_refl
    by fastforce
next
  case (Cons e es)
  obtain Me k x where e: "e=(Me,k,x)" by (cases e) auto
  have eq: "Me=M" and lookup: "fmlookup M k=None \<or> fmlookup M k=Some x"
    and tail: "fc_history (fmupd k x M) es U"
    using Cons.prems by (auto simp: e)
  have step: "channel_for_hash_map M \<le> channel_for_hash_map (fmupd k x M)"
    using lookup unfolding channel_for_hash_map_def less_eq_hash_ext_def less_eq_fmap_def by auto
  show ?case by (rule hash_ext_trans[OF step Cons.IH[OF tail]])
qed

lemma fc_history_append:
  "fc_history M (xs@ys) U \<longleftrightarrow> (\<exists>V. fc_history M xs V \<and> fc_history V ys U)"
  by (induction xs arbitrary: M) (auto split: prod.splits)

lemma fc_walk_log:
  assumes selectors: "\<And>priv h. hash_map_preserving (C priv h)"
    and out: "Some ((acc',hist'),u) \<in> set_dist (execute (fc_walk n C step priv hist acc) s)"
  shows "\<exists>es. hist'=hist@es \<and> length es\<le>n \<and>
    acc'=foldl step acc es \<and> fc_history (HashMap s) es (HashMap u)"
  using out
proof (induction n arbitrary: priv s hist acc acc' hist' u)
  case 0
  then show ?case by auto
next
  case (Suc n)
  obtain choice t where choice:
    "Some (choice,t) \<in> set_dist (execute (C priv hist) s)"
    and tail: "Some ((acc',hist'),u) \<in> set_dist
      (execute (case choice of None \<Rightarrow> return (acc,hist)
        | Some k \<Rightarrow> pair_probe (fst k) \<bind> (\<lambda>e. fc_walk n C step (snd k) (hist@[e]) (step acc e))) t)"
    using Suc.prems by (auto elim!: set_dist_bindE)
  have maps: "HashMap t=HashMap s"
    using selectors choice unfolding hash_map_preserving_def by blast
  show ?case
  proof (cases choice)
    case None
    have eq: "acc'=acc" "hist'=hist" "u=t" using tail by (auto simp: None)
    show ?thesis by (intro exI[of _ "[]"]) (use eq maps in auto)
  next
    case (Some k)
    obtain e t1 where probe: "Some (e,t1) \<in> set_dist (execute (pair_probe (fst k)) t)"
      and rest: "Some ((acc',hist'),u) \<in> set_dist
        (execute (fc_walk n C step (snd k) (hist@[e]) (step acc e)) t1)"
      using tail by (auto simp: Some elim!: set_dist_bindE)
    obtain raw where e: "e=(HashMap t,fst k,raw)"
      and t1: "t1=t\<lparr>HashMap:=fmupd (fst k) raw (HashMap t)\<rparr>"
      and h: "Some (raw,t1)\<in>set_dist (execute (hash (fst k)) t)"
      by (rule pair_probe_outcome[OF probe])
    have fresh: "fmlookup (HashMap t) (fst k)=None \<or> fmlookup (HashMap t) (fst k)=Some raw"
    proof -
      have "fmlookup (HashMap t) (fst k)=None \<or>
        fmlookup (HashMap t) (fst k)=fmlookup (HashMap t1) (fst k)"
        using hash_outcome(1)[OF h]
        unfolding less_eq_hash_ext_def less_eq_fmap_def by blast
      then show ?thesis by (simp add: t1)
    qed
    obtain es where hist': "hist'=(hist@[e])@es" and len: "length es\<le>n"
      and acc': "acc'=foldl step (step acc e) es"
      and history: "fc_history (HashMap t1) es (HashMap u)"
      using Suc.IH[OF rest] by blast
    show ?thesis
      by (intro exI[of _ "e#es"])
        (use hist' len acc' history maps fresh e t1 in auto)
  qed
qed

lemma fc_history_entry:
  assumes history: "fc_history M (pre @ e # post) U"
  obtains Me k x where "e=(Me,k,x)" "fc_history M pre Me"
    "fmlookup Me k=None \<or> fmlookup Me k=Some x"
    "fc_history (fmupd k x Me) post U"
proof -
  obtain Me k x where e: "e=(Me,k,x)" by (cases e) auto
  have "fc_history M pre Me"
    "fmlookup Me k=None \<or> fmlookup Me k=Some x"
    "fc_history (fmupd k x Me) post U"
    using history by (auto simp: fc_history_append e)
  then show ?thesis by (rule that[OF e])
qed

lemma fc_history_member:
  assumes history: "fc_history M es U" and member: "e\<in>set es"
  obtains Me k x where "e=(Me,k,x)"
    "channel_for_hash_map M \<le> channel_for_hash_map Me"
    "channel_for_hash_map Me \<le> channel_for_hash_map U"
    "channel_for_hash_map (fmupd k x Me) \<le> channel_for_hash_map U"
    "fmlookup U k=Some x"
proof -
  obtain pre post where es: "es=pre@e#post" using split_list[OF member] by blast
  obtain Me k x where e: "e=(Me,k,x)" and pre: "fc_history M pre Me"
    and lookup: "fmlookup Me k=None \<or> fmlookup Me k=Some x"
    and post: "fc_history (fmupd k x Me) post U"
    by (rule fc_history_entry[OF history[unfolded es]])
  have MMe: "channel_for_hash_map M \<le> channel_for_hash_map Me"
    by (rule fc_history_extension[OF pre])
  have MeU: "channel_for_hash_map Me \<le> channel_for_hash_map U"
    by (rule fc_history_extension[where es="e#post"]) (use post lookup in \<open>simp add: e\<close>)
  have postU: "channel_for_hash_map (fmupd k x Me) \<le> channel_for_hash_map U"
    by (rule fc_history_extension[OF post])
  have stored: "fmlookup U k=Some x"
    using hash_extension_lookup[OF _ postU, where x=k and y=x]
    by (simp add: channel_for_hash_map_def)
  show ?thesis by (rule that[OF e MMe MeU postU stored])
qed

lemma fc_history_prefix_no_key:
  assumes history: "fc_history M es U" and fresh: "fmlookup U k=None"
  shows "\<forall>e\<in>set es. fst (snd e)\<noteq>k"
proof (intro ballI)
  fix e
  assume mem: "e\<in>set es"
  obtain Me ke x where e: "e=(Me,ke,x)" and stored: "fmlookup U ke=Some x"
    by (rule fc_history_member[OF history mem])
  show "fst (snd e)\<noteq>k" using fresh stored by (auto simp: e)
qed

lemma fc_history_old_not_fresh:
  assumes history: "fc_history M es U" and old: "fmlookup M k=Some x"
    and member: "e\<in>set es"
  shows "\<not> ep_fresh k e"
proof -
  obtain Me ke y where e: "e=(Me,ke,y)"
    and ext: "channel_for_hash_map M \<le> channel_for_hash_map Me"
    by (rule fc_history_member[OF history member])
  have "fmlookup Me k=Some x"
    using hash_extension_lookup[OF _ ext, where x=k and y=x] old
    by (simp add: channel_for_hash_map_def)
  then show ?thesis by (simp add: ep_fresh_def e)
qed

lemma fc_history_unique_fresh_key:
  assumes history: "fc_history M (pre @ (Me,k,x)#post) U"
    and fresh: "fmlookup Me k=None"
    and member: "e\<in>set (pre@post)"
  shows "\<not> ep_fresh k e"
proof -
  have pre: "fc_history M pre Me" and post: "fc_history (fmupd k x Me) post U"
    using history by (auto simp: fc_history_append)
  have prefix: "\<forall>e\<in>set pre. fst (snd e)\<noteq>k"
    by (rule fc_history_prefix_no_key[OF pre fresh])
  have suffix: "\<And>e. e\<in>set post \<Longrightarrow> \<not> ep_fresh k e"
    by (rule fc_history_old_not_fresh[OF post, where x=x]) simp
  show ?thesis using member prefix suffix
    by (auto simp: ep_fresh_def split: prod.splits)
qed

fun fc_plain where
  "fc_plain 0 C priv hist = return hist"
| "fc_plain (Suc n) C priv hist = do {
    choice \<leftarrow> C priv hist;
    case choice of None \<Rightarrow> return hist | Some k \<Rightarrow> do {
      e \<leftarrow> pair_probe (fst k); fc_plain n C (snd k) (hist@[e])}}"

lemma fc_walk_erase_account:
  "fc_walk n C step priv hist acc \<bind> (\<lambda>res. return (snd res)) = fc_plain n C priv hist"
proof (induction n arbitrary: priv hist acc)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
    unfolding fc_walk.simps fc_plain.simps sm_bind_assoc
  proof (rule arg_cong[where f="\<lambda>tail. C priv hist \<bind> tail"], rule ext)
    fix choice
    show "(case choice of None \<Rightarrow> return (acc,hist)
        | Some k \<Rightarrow> pair_probe (fst k) \<bind> (\<lambda>e. fc_walk n C step (snd k) (hist@[e]) (step acc e))) \<bind>
        (\<lambda>res. return (snd res)) =
      (case choice of None \<Rightarrow> return hist
        | Some k \<Rightarrow> pair_probe (fst k) \<bind> (\<lambda>e. fc_plain n C (snd k) (hist@[e])))"
      by (cases choice) (simp_all add: sm_bind_assoc Suc.IH)
  qed
qed

lemma fc_probe_erase_record:
  "pair_probe k \<bind> (\<lambda>e. return (ep_raw e)) = hash k"
  unfolding ep_raw_def by (rule pair_probe_projection)

end

subsection \<open>Finite Candidate Clean Path\<close>

context soundness
begin

definition fc_tracks where
  "fc_tracks z parent child acc \<longleftrightarrow>
    (if parent then if child then acc=FC_Won else acc=FC_Live z
     else \<exists>W B. acc=FC_Pre W B \<and> W\<subseteq>B \<and> (if child then z\<in>W else z\<notin>B))"

lemma fc_tracks_other:
  assumes tracks: "fc_tracks z parent child acc"
    and key: "parent \<or> fst (snd e)\<noteq>QueryIndexChallenge j start"
    and miss: "z\<notin>fc_fiber S rt ffs cfs start j e"
  shows "fc_tracks z parent child (fc_step rT rC S rt ffs cfs start j acc e)"
  using assms
  by (auto simp: fc_tracks_def Let_def split: if_splits)

lemma fc_tracks_child:
  assumes tracks: "fc_tracks z parent False acc"
    and key: "fst (snd e)\<noteq>QueryIndexChallenge j start"
    and hit: "z\<in>fc_fiber S rt ffs cfs start j e"
    and good: "pair_insert_good rT rC e"
  shows "fc_tracks z parent True (fc_step rT rC S rt ffs cfs start j acc e)"
  using assms by (auto simp: fc_tracks_def Let_def split: if_splits)

lemma fc_tracks_parent:
  assumes tracks: "fc_tracks z False child acc"
    and key: "fst (snd e)=QueryIndexChallenge j start"
    and fresh: "ep_fresh (QueryIndexChallenge j start) e"
    and raw: "ep_raw e=z" and z: "z\<in>S"
  shows "fc_tracks z True child (fc_step rT rC S rt ffs cfs start j acc e)"
  using assms by (auto simp: fc_tracks_def split: if_splits)

lemma fc_tracks_fold_other:
  assumes tracks: "fc_tracks z parent child acc"
    and other: "\<And>e. e\<in>set es \<Longrightarrow>
      (parent \<or> fst (snd e)\<noteq>QueryIndexChallenge j start) \<and>
      z\<notin>fc_fiber S rt ffs cfs start j e"
  shows "fc_tracks z parent child
    (foldl (fc_step rT rC S rt ffs cfs start j) acc es)"
  using tracks other
  proof (induction es arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  have one: "fc_tracks z parent child (fc_step rT rC S rt ffs cfs start j acc e)"
    by (rule fc_tracks_other[OF Cons.prems(1)]) (use Cons.prems(2) in auto)
  show ?case unfolding foldl.simps
    by (rule Cons.IH[OF one]) (use Cons.prems(2) in auto)
qed

lemma fc_won_fold:
  "foldl (fc_step rT rC S rt ffs cfs start j) FC_Won es = FC_Won"
  by (induction es) simp_all

lemma fc_two_markers_win:
  assumes z: "z\<in>S"
    and child: "z\<in>fc_fiber S rt ffs cfs start j ce" "pair_insert_good rT rC ce"
      "fst (snd ce)\<noteq>QueryIndexChallenge j start"
    and parent: "fst (snd re)=QueryIndexChallenge j start"
      "ep_fresh (QueryIndexChallenge j start) re" "ep_raw re=z"
    and before: "\<And>e. e\<in>set pre \<Longrightarrow> fst (snd e)\<noteq>QueryIndexChallenge j start \<and>
      z\<notin>fc_fiber S rt ffs cfs start j e"
    and middle: "\<And>e. e\<in>set mid \<Longrightarrow> (parent_first \<or> fst (snd e)\<noteq>QueryIndexChallenge j start) \<and>
      z\<notin>fc_fiber S rt ffs cfs start j e"
  shows "foldl (fc_step rT rC S rt ffs cfs start j) (FC_Pre {} {})
    (pre @ (if parent_first then [re]@mid@[ce] else [ce]@mid@[re]) @ post) = FC_Won"
proof -
  let ?step = "fc_step rT rC S rt ffs cfs start j"
  let ?a = "foldl ?step (FC_Pre {} {}) pre"
  have initial: "fc_tracks z False False (FC_Pre {} {})" by (simp add: fc_tracks_def)
  have pre: "fc_tracks z False False ?a"
    by (rule fc_tracks_fold_other[OF initial]) (use before in auto)
  show ?thesis
  proof (cases parent_first)
    case True
    have r: "fc_tracks z True False (?step ?a re)"
      by (rule fc_tracks_parent[OF pre parent(1,2,3) z])
    have mid: "fc_tracks z True False (foldl ?step (?step ?a re) mid)"
      by (rule fc_tracks_fold_other[OF r]) (use middle True in auto)
    have c: "fc_tracks z True True (?step (foldl ?step (?step ?a re) mid) ce)"
      by (rule fc_tracks_child[OF mid child(3,1,2)])
    show ?thesis using c by (simp add: True fc_tracks_def fc_won_fold)
  next
    case False
    have c: "fc_tracks z False True (?step ?a ce)"
      by (rule fc_tracks_child[OF pre child(3,1,2)])
    have mid: "fc_tracks z False True (foldl ?step (?step ?a ce) mid)"
      by (rule fc_tracks_fold_other[OF c]) (use middle False in auto)
    have r: "fc_tracks z True True (?step (foldl ?step (?step ?a ce) mid) re)"
      by (rule fc_tracks_parent[OF mid parent(1,2,3) z])
    show ?thesis using r by (simp add: False fc_tracks_def fc_won_fold)
  qed
qed

lemma fc_fiber_determines_key:
  assumes history: "fc_history M es U"
    and member: "e\<in>set es"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map U)"
    and route: "z\<in>pair_route_fiber S rt ffs cfs start (channel_for_hash_map U) v"
    and hit: "z\<in>fc_fiber S rt ffs cfs start j e"
  shows "ep_fresh (QueryIndexChallenge (Suc j) v) e"
proof -
  obtain Me k x where e: "e=(Me,k,x)"
    and ext: "channel_for_hash_map Me \<le> channel_for_hash_map U"
    by (rule fc_history_member[OF history member])
  obtain w where k: "k=QueryIndexChallenge (Suc j) w" and fresh: "fmlookup Me k=None"
    and old: "z\<in>pair_route_fiber S rt ffs cfs start (channel_for_hash_map Me) w"
    using hit unfolding fc_fiber_def e
    by (auto split: protocol_hash_input.splits if_splits)
  have later: "z\<in>pair_route_fiber S rt ffs cfs start (channel_for_hash_map U) w"
    using causal_route_mono[OF ext] old by blast
  have eq: "w=v"
  proof (rule ccontr)
    assume neq: "w\<noteq>v"
    have "pair_route_fiber S rt ffs cfs start (channel_for_hash_map U) w \<inter>
      pair_route_fiber S rt ffs cfs start (channel_for_hash_map U) v = {}"
      by (rule pair_route_fibers_disjoint[OF clean neq])
    then show False using later route by blast
  qed
  show ?thesis using fresh eq by (simp add: ep_fresh_def e k)
qed

lemma fc_other_fibers_miss:
  assumes history: "fc_history M (pre@(Me,QueryIndexChallenge (Suc j) v,x)#post) U"
    and fresh: "fmlookup Me (QueryIndexChallenge (Suc j) v)=None"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map U)"
    and route: "z\<in>pair_route_fiber S rt ffs cfs start (channel_for_hash_map U) v"
    and member: "e\<in>set (pre@post)"
  shows "z\<notin>fc_fiber S rt ffs cfs start j e"
proof
  assume hit: "z\<in>fc_fiber S rt ffs cfs start j e"
  have entry: "e\<in>set (pre@(Me,QueryIndexChallenge (Suc j) v,x)#post)"
    using member by auto
  have "ep_fresh (QueryIndexChallenge (Suc j) v) e"
    by (rule fc_fiber_determines_key[OF history entry clean route hit])
  then show False using fc_history_unique_fresh_key[OF history fresh member] by blast
qed

lemma fc_selected_log_wins:
  assumes history: "fc_history M
    (pre @ (if parent_first then [re]@mid@[ce] else [ce]@mid@[re]) @ post) U"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map U)"
    and route: "z\<in>pair_route_fiber S rt ffs cfs start (channel_for_hash_map U) v"
    and ce: "ce=(Mc,QueryIndexChallenge (Suc j) v,x)"
    and freshc: "fmlookup Mc (QueryIndexChallenge (Suc j) v)=None"
    and child: "z\<in>fc_fiber S rt ffs cfs start j ce" "pair_insert_good rT rC ce"
    and re: "re=(Mr,QueryIndexChallenge j start,z)"
    and freshp: "fmlookup Mr (QueryIndexChallenge j start)=None"
  shows "foldl (fc_step rT rC S rt ffs cfs start j) (FC_Pre {} {})
    (pre @ (if parent_first then [re]@mid@[ce] else [ce]@mid@[re]) @ post) = FC_Won"
proof -
  have z: "z\<in>S" using route unfolding pair_route_fiber_def by blast
  have parent: "fst (snd re)=QueryIndexChallenge j start"
    "ep_fresh (QueryIndexChallenge j start) re" "ep_raw re=z"
    using freshp by (simp_all add: re ep_fresh_def ep_raw_def)
  have ckey: "fst (snd ce)\<noteq>QueryIndexChallenge j start" by (simp add: ce)
  have both: "(\<forall>e\<in>set pre. fst (snd e)\<noteq>QueryIndexChallenge j start \<and>
    z\<notin>fc_fiber S rt ffs cfs start j e) \<and>
    (\<forall>e\<in>set mid. (parent_first \<or> fst (snd e)\<noteq>QueryIndexChallenge j start) \<and>
    z\<notin>fc_fiber S rt ffs cfs start j e)"
  proof (cases parent_first)
    case True
    have ph: "fc_history M pre Mr"
      using history by (auto simp: True re fc_history_append)
    have keys: "\<forall>e\<in>set pre. fst (snd e)\<noteq>QueryIndexChallenge j start"
      by (rule fc_history_prefix_no_key[OF ph freshp])
    have ch: "fc_history M ((pre@[re]@mid)@(Mc,QueryIndexChallenge (Suc j) v,x)#post) U"
      using history by (simp add: True ce)
    have miss: "\<And>e. e\<in>set pre \<union> set mid \<Longrightarrow> z\<notin>fc_fiber S rt ffs cfs start j e"
      by (rule fc_other_fibers_miss[OF ch freshc clean route]) auto
    show ?thesis using keys miss True by auto
  next
    case False
    have ph: "fc_history M (pre@[ce]@mid) Mr"
      using history by (auto simp: False re fc_history_append)
    have keys: "\<forall>e\<in>set (pre@[ce]@mid). fst (snd e)\<noteq>QueryIndexChallenge j start"
      by (rule fc_history_prefix_no_key[OF ph freshp])
    have ch: "fc_history M (pre@(Mc,QueryIndexChallenge (Suc j) v,x)#(mid@[re]@post)) U"
      using history by (simp add: False ce)
    have miss: "\<And>e. e\<in>set pre \<union> set mid \<Longrightarrow> z\<notin>fc_fiber S rt ffs cfs start j e"
      by (rule fc_other_fibers_miss[OF ch freshc clean route]) auto
    show ?thesis using keys miss False by auto
  qed
  show ?thesis
    by (rule fc_two_markers_win[OF z child(1,2) ckey parent])
      (use both in auto)
qed

end

subsection \<open>Finite Candidate Ledger\<close>

context soundness
begin

definition fc_target where
  "fc_target R M = weighted_semantic_interval_targets M \<union> R"

definition fc_bad_record where
  "fc_bad_record R e \<longleftrightarrow> (case e of (M,k,x) \<Rightarrow>
    fmlookup M k=None \<and> x\<in>fc_target R M)"

definition fc_no_bad where
  "fc_no_bad R es \<longleftrightarrow> (\<forall>e\<in>set es. \<not> fc_bad_record R e)"

lemma fc_target_mono:
  assumes ext: "channel_for_hash_map M \<le> channel_for_hash_map U"
  shows "fc_target R M \<subseteq> fc_target R U"
proof -
  have keep: "\<And>k x. fmlookup M k=Some x \<Longrightarrow> fmlookup U k=Some x"
  proof -
    fix k x
    assume old: "fmlookup M k=Some x"
    have lookup: "fmlookup (HashMap (channel_for_hash_map M)) k=Some x"
      using old by (simp add: channel_for_hash_map_def)
    show "fmlookup U k=Some x" using hash_extension_lookup[OF lookup ext]
      by (simp add: channel_for_hash_map_def)
  qed
  have ai: "transcript_absorb_input_values M \<subseteq> transcript_absorb_input_values U"
    unfolding transcript_absorb_input_values_def using keep by blast
  have am: "transcript_absorb_message_values M \<subseteq> transcript_absorb_message_values U"
    unfolding transcript_absorb_message_values_def using keep by blast
  have qi: "query_index_state_values M \<subseteq> query_index_state_values U"
    unfolding query_index_state_values_def using keep by blast
  have mc: "hash_map_merkle_child_values (channel_for_hash_map M) \<subseteq>
    hash_map_merkle_child_values (channel_for_hash_map U)"
    unfolding hash_map_merkle_child_values_def merkle_node_child_output_relation_def
      channel_for_hash_map_def
    using keep by (auto; blast)
  show ?thesis using ai am qi mc
    unfolding fc_target_def weighted_semantic_interval_targets_def by blast
qed

lemma fc_target_card:
  "card (fc_target R M) \<le> 5*card (fmdom' M)+card R"
  using card_Un_le[of "weighted_semantic_interval_targets M" R] weighted_semantic_interval_targets_card[of M]
  unfolding fc_target_def by linarith

lemma fc_history_no_target_hit:
  assumes history: "fc_history M es U" and no_bad: "fc_no_bad R es"
  shows "\<not> hash_map_new_output_hit (fc_target R M)
    (channel_for_hash_map M) (channel_for_hash_map U)"
  using history no_bad
proof (induction es arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain Me k x where e: "e=(Me,k,x)" by (cases e) auto
  have Me: "Me=M" and lookup: "fmlookup M k=None \<or> fmlookup M k=Some x"
    and tail: "fc_history (fmupd k x M) es U"
    and nob: "\<not> fc_bad_record R (M,k,x)" and rest: "fc_no_bad R es"
    using Cons.prems by (auto simp: e fc_no_bad_def)
  let ?A = "channel_for_hash_map (fmupd k x M)"
  have MA: "channel_for_hash_map M \<le> ?A"
    using lookup unfolding channel_for_hash_map_def less_eq_hash_ext_def less_eq_fmap_def by auto
  have AU: "?A \<le> channel_for_hash_map U" by (rule fc_history_extension[OF tail])
  have sub: "fc_target R M \<subseteq> fc_target R (fmupd k x M)"
    by (rule fc_target_mono[OF MA])
  have no_tail: "\<not> hash_map_new_output_hit (fc_target R M) ?A (channel_for_hash_map U)"
    using Cons.IH[OF tail rest] hash_map_new_output_hit_subset[OF sub] by blast
  have no_head: "\<not> hash_map_new_output_hit (fc_target R M) (channel_for_hash_map M) ?A"
    using nob unfolding fc_bad_record_def hash_map_new_output_hit_def channel_for_hash_map_def
    by auto
  show ?case using hash_map_new_output_hit_trans_decomp[OF MA AU] no_head no_tail by blast
qed

lemma fc_record_no_late:
  assumes history: "fc_history M (pre@(Me,QueryIndexChallenge i v,x)#post) U"
    and no_bad: "fc_no_bad R (pre@(Me,QueryIndexChallenge i v,x)#post)"
    and sub: "D\<subseteq>weighted_semantic_interval_targets Me \<union> {v} \<union> R"
  shows "\<not> hash_map_new_output_hit D
    (channel_for_hash_map (fmupd (QueryIndexChallenge i v) x Me)) (channel_for_hash_map U)"
proof -
  have tail: "fc_history (fmupd (QueryIndexChallenge i v) x Me) post U"
    using history by (auto simp: fc_history_append)
  have rest: "fc_no_bad R post" using no_bad by (auto simp: fc_no_bad_def)
  have target: "D\<subseteq>fc_target R (fmupd (QueryIndexChallenge i v) x Me)"
    using sub by (simp add: fc_target_def weighted_semantic_interval_targets_query_update)
  show ?thesis using fc_history_no_target_hit[OF tail rest]
    hash_map_new_output_hit_subset[OF target] by blast
qed

fun fc_charge where
  "fc_charge R 0 hcap = (0::prob)"
| "fc_charge R (Suc n) hcap =
    nnreal (5*hcap+card R) / nnreal size + fc_charge R n (Suc hcap)"

lemma fc_bad_probe_bound:
  "wp_event (pair_probe k)
    (\<lambda>out. case out of None \<Rightarrow> False | Some (e,t) \<Rightarrow> fc_bad_record R e) s \<le>
    nnreal (5*card (fmdom' (HashMap s))+card R) / nnreal size"
proof (cases "fmlookup (HashMap s) k=None")
  case True
  have exact: "wp_event (pair_probe k)
      (\<lambda>out. case out of None \<Rightarrow> False | Some (e,t) \<Rightarrow> fc_bad_record R e) s =
    ep_mass (fc_target R (HashMap s))"
    unfolding pair_probe_def wp_event_def fc_bad_record_def ep_mass_def
    using True dist_expect_hash_dist_fresh_indicator[OF True, of "fc_target R (HashMap s)"]
    by (simp add: wpsimps)
  show ?thesis unfolding exact ep_mass_def by (rule nnreal_nat_divide_right_mono[OF fc_target_card])
next
  case False
  have zero: "wp_event (pair_probe k)
      (\<lambda>out. case out of None \<Rightarrow> False | Some (e,t) \<Rightarrow> fc_bad_record R e) s = 0"
    using False unfolding pair_probe_def wp_event_def fc_bad_record_def by (force simp: wpsimps)
  show ?thesis by (simp add: zero)
qed

definition fc_bad_count :: "'f set \<Rightarrow> (('f protocol_hash_input,'f) fmap \<times> 'f protocol_hash_input \<times> 'f) list \<Rightarrow> prob" where
  "fc_bad_count R hist = sum_list (map (\<lambda>e. if fc_bad_record R e then 1 else 0) hist)"

lemma fc_bad_count_append:
  "fc_bad_count R (hist@[e]) = fc_bad_count R hist + (if fc_bad_record R e then 1 else 0)"
  by (simp add: fc_bad_count_def)

lemma fc_probe_card:
  assumes out: "Some (e,t)\<in>set_dist (execute (pair_probe k) s)"
    and cap: "card (fmdom' (HashMap s))\<le>hcap"
  shows "card (fmdom' (HashMap t))\<le>Suc hcap"
proof -
  obtain raw where t: "t=s\<lparr>HashMap:=fmupd k raw (HashMap s)\<rparr>"
    by (rule pair_probe_outcome[OF out])
  have "card (fmdom' (HashMap t))\<le>Suc (card (fmdom' (HashMap s)))"
    by (simp add: t card_insert_if)
  also have "...\<le>Suc hcap" using cap by simp
  finally show ?thesis .
qed

lemma fc_walk_bad_count_bound:
  assumes selectors: "\<And>priv h. hash_map_preserving (C priv h)"
    and cap: "card (fmdom' (HashMap s))\<le>hcap"
  shows "wp (fc_walk n C step priv hist acc)
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((acc,hist),u) \<Rightarrow> fc_bad_count R hist) s \<le>
    fc_bad_count R hist + fc_charge R n hcap"
  using cap
proof (induction n arbitrary: priv s hist acc hcap)
  case 0
  then show ?case by (simp add: wpsimps)
next
  case (Suc n)
  let ?P = "\<lambda>out. case out of None \<Rightarrow> 0 | Some ((acc,hist),u) \<Rightarrow> fc_bad_count R hist"
  let ?b = "nnreal (5*hcap+card R) / nnreal size"
  let ?tail = "fc_charge R n (Suc hcap)"
  show ?case unfolding fc_walk.simps wp_bind fc_charge.simps
  proof (rule wp_le_const_on_support)
    fix out
    assume mem: "out\<in>set_dist (execute (C priv hist) s)"
    show "(case out of None \<Rightarrow> ?P None | Some (choice,t) \<Rightarrow>
      wp (case choice of None \<Rightarrow> return (acc,hist) | Some k \<Rightarrow>
        pair_probe (fst k) \<bind> (\<lambda>e. fc_walk n C step (snd k) (hist@[e]) (step acc e))) ?P t)
      \<le> fc_bad_count R hist + (?b+?tail)"
    proof (cases out)
      case None
      then show ?thesis by simp
    next
      case (Some ct)
      obtain choice t where ct: "ct=(choice,t)" by (cases ct) simp
      have choice_out: "Some (choice,t)\<in>set_dist (execute (C priv hist) s)"
        using mem by (simp add: Some ct)
      have maps: "HashMap t=HashMap s"
        using selectors choice_out unfolding hash_map_preserving_def by blast
      have tcap: "card (fmdom' (HashMap t))\<le>hcap" using Suc.prems by (simp add: maps)
      have bound: "wp (case choice of None \<Rightarrow> return (acc,hist) | Some k \<Rightarrow>
        pair_probe (fst k) \<bind> (\<lambda>e. fc_walk n C step (snd k) (hist@[e]) (step acc e))) ?P t \<le>
        fc_bad_count R hist + (?b+?tail)"
      proof (cases choice)
        case None
        then show ?thesis by (simp add: wpsimps)
      next
        case (Some k)
        let ?E = "\<lambda>out. case out of None \<Rightarrow> False | Some (e,u) \<Rightarrow> fc_bad_record R e"
        have "wp (pair_probe (fst k) \<bind> (\<lambda>e. fc_walk n C step (snd k) (hist@[e]) (step acc e))) ?P t \<le>
          wp (pair_probe (fst k)) (\<lambda>out. fc_bad_count R hist + ?tail + (if ?E out then 1 else 0)) t"
          unfolding wp_bind
        proof (rule wp_mono_on_support)
          fix eout
          assume emem: "eout\<in>set_dist (execute (pair_probe (fst k)) t)"
          show "(case eout of None \<Rightarrow> ?P None | Some (e,u) \<Rightarrow>
              wp (fc_walk n C step (snd k) (hist@[e]) (step acc e)) ?P u) \<le>
            fc_bad_count R hist + ?tail + (if ?E eout then 1 else 0)"
          proof (cases eout)
            case None
            then show ?thesis by simp
          next
            case (Some eu)
            obtain e u where eu: "eu=(e,u)" by (cases eu) simp
            have eo: "Some (e,u)\<in>set_dist (execute (pair_probe (fst k)) t)"
              using emem by (simp add: Some eu)
            have ucap: "card (fmdom' (HashMap u))\<le>Suc hcap"
              by (rule fc_probe_card[OF eo tcap])
            have cont: "wp (fc_walk n C step (snd k) (hist@[e]) (step acc e)) ?P u \<le>
              fc_bad_count R (hist@[e]) + ?tail"
              by (rule Suc.IH[OF ucap])
            show ?thesis using cont
              by (simp add: Some eu fc_bad_count_append add.assoc add.left_commute add.commute)
          qed
        qed
        also have "... = fc_bad_count R hist + ?tail + wp_event (pair_probe (fst k)) ?E t"
          by (simp only: causal_wp_add causal_wp_const wp_event_def)
        also have "... \<le> fc_bad_count R hist + ?tail + ?b"
        proof (rule add_left_mono)
          have "wp_event (pair_probe (fst k)) ?E t \<le>
            nnreal (5*card (fmdom' (HashMap t))+card R) / nnreal size"
            by (rule fc_bad_probe_bound)
          also have "...\<le>?b" by (rule nnreal_nat_divide_right_mono) (use tcap in arith)
          finally show "wp_event (pair_probe (fst k)) ?E t\<le>?b" .
        qed
        finally show ?thesis by (simp add: Some add.assoc add.commute add.left_commute)
      qed
      then show ?thesis by (simp add: Some ct)
    qed
  qed
qed

lemma fc_bad_count_detects:
  "\<not>fc_no_bad R hist \<Longrightarrow> 1\<le>fc_bad_count R hist"
  by (induction hist) (auto simp: fc_no_bad_def fc_bad_count_def)

lemma fc_walk_bad_event_bound:
  assumes selectors: "\<And>priv h. hash_map_preserving (C priv h)"
    and cap: "card (fmdom' (HashMap s))\<le>hcap"
  shows "wp_event (fc_walk n C step priv [] acc)
    (\<lambda>out. case out of None \<Rightarrow> False | Some ((acc,hist),u) \<Rightarrow> \<not>fc_no_bad R hist) s
    \<le> fc_charge R n hcap"
proof -
  have "wp_event (fc_walk n C step priv [] acc)
      (\<lambda>out. case out of None \<Rightarrow> False | Some ((acc,hist),u) \<Rightarrow> \<not>fc_no_bad R hist) s \<le>
    wp (fc_walk n C step priv [] acc)
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((acc,hist),u) \<Rightarrow> fc_bad_count R hist) s"
    unfolding wp_event_def
    by (rule wp_mono_on_support) (auto intro: fc_bad_count_detects split: option.splits prod.splits)
  also have "... \<le> fc_bad_count R [] + fc_charge R n hcap"
    by (rule fc_walk_bad_count_bound[OF selectors cap])
  finally show ?thesis by (simp add: fc_bad_count_def)
qed

lemma fc_charge_real:
  "nn2real (fc_charge R n hcap) =
    (real n * (5 * real hcap + real (card R)) +
      5 * real n * (real n - 1) / 2) / real size"
proof (induction n arbitrary: hcap)
  case 0
  show ?case by simp
next
  case (Suc n)
  have numerator:
    "real (5*hcap+card R) +
      (real n * (5*real (Suc hcap)+real (card R)) + 5*real n*(real n-1)/2) =
      real (Suc n)*(5*real hcap+real (card R)) + 5*real (Suc n)*(real (Suc n)-1)/2"
    by (simp add: algebra_simps diff_divide_distrib)
  show ?case
    by (simp only: fc_charge.simps nn2real_add nn2real_divide nn2real_nnreal Suc.IH
      add_divide_distrib[symmetric] numerator)
qed

end

subsection \<open>Finite Candidate Result\<close>

context soundness
begin

text \<open>An augmented actual-success residual event. No clean-execution
or semantic-residual premise is built into the actual verifier.\<close>

definition fc_selected_event where
  "fc_selected_event rT rC rt ffs fv alphas cfs cv start j out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some ((acc,hist),u) \<Rightarrow>
      \<exists>pre mid post parent_first Mc v x Mr z qs qt.
        let ce=(Mc,QueryIndexChallenge (Suc j) v,x);
            re=(Mr,QueryIndexChallenge j start,z)
        in hist=pre@(if parent_first then [re]@mid@[ce] else [ce]@mid@[re])@post \<and>
          fmlookup Mc (QueryIndexChallenge (Suc j) v)=None \<and>
          fmlookup Mr (QueryIndexChallenge j start)=None \<and>
          \<not> hash_map_output_collision (channel_for_hash_map (HashMap u)) \<and>
          weighted_semantic_hit rT rC (HashMap u) start z \<and>
          pair_eventual_ready rT rC (HashMap u) ce \<and>
          PQueryCounter qs=j \<and> PState qs=start \<and> PState qt=v \<and> qt\<le>u \<and>
          Some ((),qt)\<in>set_dist
            (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) qs))"

lemma fc_selected_history_wins:
  assumes power: "clength*scale=2^N"
    and traces: "length ffs\<le>N" and comps: "length cfs\<le>N"
    and history: "fc_history M hist (HashMap u)"
    and event: "fc_selected_event rT rC rt ffs fv alphas cfs cv start j (Some ((acc,hist),u))"
    and nob: "fc_no_bad (causal_route_roots rt ffs cfs \<union> {start}) hist"
  shows "foldl (fc_step rT rC {raw. weighted_semantic_hit rT rC M start raw}
    rt ffs cfs start j) (FC_Pre {} {}) hist = FC_Won"
proof -
  obtain pre mid post parent_first Mc v x Mr z qs qt where
    hist: "hist=pre@(if parent_first then [(Mr,QueryIndexChallenge j start,z)]@mid@[(Mc,QueryIndexChallenge (Suc j) v,x)]
      else [(Mc,QueryIndexChallenge (Suc j) v,x)]@mid@[(Mr,QueryIndexChallenge j start,z)])@post"
    and freshc: "fmlookup Mc (QueryIndexChallenge (Suc j) v)=None"
    and freshp: "fmlookup Mr (QueryIndexChallenge j start)=None"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map (HashMap u))"
    and parenthit: "weighted_semantic_hit rT rC (HashMap u) start z"
    and childready: "pair_eventual_ready rT rC (HashMap u) (Mc,QueryIndexChallenge (Suc j) v,x)"
    and counter: "PQueryCounter qs=j" and start: "PState qs=start"
    and successor: "PState qt=v" and ext: "qt\<le>u"
    and actual: "Some ((),qt)\<in>set_dist
      (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) qs)"
    using event unfolding fc_selected_event_def by (auto simp: Let_def)
  let ?ce = "(Mc,QueryIndexChallenge (Suc j) v,x)"
  let ?re = "(Mr,QueryIndexChallenge j start,z)"
  let ?U = "channel_for_hash_map (HashMap u)"
  let ?R = "causal_route_roots rt ffs cfs \<union> {start}"
  let ?S = "{raw. weighted_semantic_hit rT rC M start raw}"
  let ?cp = "if parent_first then pre@[?re]@mid else pre"
  let ?cs = "if parent_first then post else mid@[?re]@post"
  let ?pp = "if parent_first then pre else pre@[?ce]@mid"
  let ?ps = "if parent_first then mid@[?ce]@post else post"
  have hc: "hist=?cp@?ce#?cs" and hp: "hist=?pp@?re#?ps"
    using hist by (cases parent_first; simp)+
  have prefix: "fc_history M ?pp Mr"
    using history by (auto simp: hp fc_history_append)
  have MMr: "channel_for_hash_map M \<le> channel_for_hash_map Mr"
    by (rule fc_history_extension[OF prefix])
  have freshM: "fmlookup M (QueryIndexChallenge j start)=None"
    using hash_extension_none[OF MMr] freshp by (simp add: channel_for_hash_map_def)
  have MU: "channel_for_hash_map M \<le> ?U" by (rule fc_history_extension[OF history])
  have memberp: "?re\<in>set hist" by (simp add: hp)
  have lookup: "fmlookup (HashMap u) (QueryIndexChallenge j start)=Some z"
    by (rule fc_history_member[OF history memberp]) auto
  have ntp: "\<not> hash_map_new_output_hit (weighted_semantic_interval_targets M \<union> {start})
    (channel_for_hash_map M) u"
    using fc_history_no_target_hit[OF history nob]
    unfolding fc_target_def hash_map_new_output_hit_def channel_for_hash_map_def by auto
  have Mactual: "channel_for_hash_map M\<le>u"
    using MU by (simp add: channel_for_hash_map_def less_eq_hash_ext_def)
  have oldhit: "z\<in>?S"
    using ep_semantic_before_parent[OF Mactual freshM lookup ntp parenthit] by simp
  have child_nt: "\<not> pair_late_connection (HashMap u) ?ce"
    using fc_record_no_late[OF history[unfolded hc] nob[unfolded hc],
      where D="weighted_semantic_interval_targets Mc \<union> {v}"]
    by (auto simp: pair_late_connection_def)
  have childgood: "pair_insert_good rT rC ?ce"
    by (rule pair_eventual_recovery[OF childready child_nt])
  have child_route_nt: "\<not> hash_map_new_output_hit (causal_route_targets rt ffs cfs Mc v)
    (channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x Mc)) ?U"
    by (rule fc_record_no_late[OF history[unfolded hc] nob[unfolded hc]])
      (auto simp: causal_route_targets_def)
  have child_ext: "channel_for_hash_map (fmupd (QueryIndexChallenge (Suc j) v) x Mc)\<le>?U"
    by (rule fc_history_member[OF history, where e="?ce"]) (simp add: hc, auto)
  have qext: "qt\<le>?U" using ext by (simp add: channel_for_hash_map_def less_eq_hash_ext_def)
  have route: "z\<in>pair_route_fiber ?S rt ffs cfs start ?U v"
    using ep_success_route_with_log[OF power traces comps actual qext, where raw=z and S="?S"]
      lookup oldhit by (simp add: channel_for_hash_map_def counter start successor)
  have oldroute: "z\<in>pair_route_fiber ?S rt ffs cfs start (channel_for_hash_map Mc) v"
    using route causal_route_first_insertion_recovery[OF child_ext child_route_nt] by simp
  have fiber: "z\<in>fc_fiber ?S rt ffs cfs start j ?ce"
    using freshc oldroute by (simp add: fc_fiber_def)
  show ?thesis unfolding hist
    by (rule fc_selected_log_wins[OF history[unfolded hist] clean route refl freshc fiber childgood refl freshp])
qed

lemma fc_selected_event_complete_bound:
  assumes power: "clength*scale=2^N"
    and traces: "length ffs\<le>N" and comps: "length cfs\<le>N"
    and selectors: "\<And>priv h. hash_map_preserving (C priv h)"
    and cap: "card (fmdom' (HashMap s))\<le>hcap"
    and clean: "\<not> hash_map_output_collision (channel_for_hash_map (HashMap s))"
    and initial: "PState adversary_initial_state \<notin> hash_map_output_values (channel_for_hash_map (HashMap s))"
  shows "wp_event
    (fc_walk n C (fc_step rT rC {raw. weighted_semantic_hit rT rC (HashMap s) start raw}
      rt ffs cfs start j) priv [] (FC_Pre {} {}))
    (fc_selected_event rT rC rt ffs fv alphas cfs cv start j) s \<le>
    (ro_mca_weighted_semantic_base rT rC)^2 + fc_charge (causal_route_roots rt ffs cfs \<union> {start}) n hcap"
proof -
  let ?S = "{raw. weighted_semantic_hit rT rC (HashMap s) start raw}"
  let ?R = "causal_route_roots rt ffs cfs \<union> {start}"
  let ?step = "fc_step rT rC ?S rt ffs cfs start j"
  let ?run = "fc_walk n C ?step priv [] (FC_Pre {} {})"
  let ?E = "fc_selected_event rT rC rt ffs fv alphas cfs cv start j"
  let ?B = "\<lambda>out. case out of None \<Rightarrow> False | Some ((acc,hist),u) \<Rightarrow> \<not>fc_no_bad ?R hist"
  have split: "\<And>out. out\<in>set_dist (execute ?run s) \<Longrightarrow> ?E out \<Longrightarrow> fc_won_event out \<or> ?B out"
  proof -
    fix out
    assume mem: "out\<in>set_dist (execute ?run s)" and event: "?E out"
    obtain acc hist u where out: "out=Some ((acc,hist),u)"
      using event unfolding fc_selected_event_def by (auto split: option.splits prod.splits)
    have actual: "Some ((acc,hist),u)\<in>set_dist (execute ?run s)"
      using mem by (simp add: out)
    have history: "fc_history (HashMap s) hist (HashMap u)"
      and fold: "acc=foldl ?step (FC_Pre {} {}) hist"
      using fc_walk_log[OF selectors actual] by auto
    show "fc_won_event out \<or> ?B out"
    proof (cases "fc_no_bad ?R hist")
      case True
      have win: "foldl ?step (FC_Pre {} {}) hist=FC_Won"
        by (rule fc_selected_history_wins[OF power traces comps history _ True])
          (use event in \<open>simp add: out\<close>)
      show ?thesis using fold win by (simp add: out fc_won_event_def)
    next
      case False
      then show ?thesis by (simp add: out)
    qed
  qed
  have "wp_event ?run ?E s \<le>
    wp ?run (\<lambda>out. (if fc_won_event out then 1 else 0) + (if ?B out then 1 else 0)) s"
    unfolding wp_event_def
    by (rule wp_mono_on_support) (use split in auto)
  also have "... = wp_event ?run fc_won_event s + wp_event ?run ?B s"
    unfolding wp_event_def by (rule causal_wp_add)
  also have "... \<le> ro_mca_weighted_semantic_base rT rC * ep_mass ?S + fc_charge ?R n hcap"
    by (rule add_mono[OF fc_walk_won_bound fc_walk_bad_event_bound[OF selectors cap]])
  also have "... \<le> (ro_mca_weighted_semantic_base rT rC)^2 + fc_charge ?R n hcap"
  proof (rule add_right_mono)
    have mass: "ep_mass ?S\<le>ro_mca_weighted_semantic_base rT rC"
      unfolding ep_mass_def by (rule nnreal_nat_divide_right_mono[OF weighted_semantic_hit_fiber[OF clean initial]])
    show "ro_mca_weighted_semantic_base rT rC * ep_mass ?S\<le>(ro_mca_weighted_semantic_base rT rC)^2"
      unfolding power2_eq_square by (rule mult_left_mono[OF mass]) simp
  qed
  finally show ?thesis .
qed

end

end
