(* Title: Stark/Soundness_FRI_Weighted_Long_Paths.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Long_Paths
  imports
    "Soundness_FRI_Weighted_Execution_Replay"
begin

section \<open>Long Paths for weighted MCA soundness\<close>

text \<open>Finite-depth weighted scores preserve all query repetitions, including arbitrary oracle insertion order. Counter levels prevent reuse of a sampled key along one path; bad connections are charged separately.\<close>

subsection \<open>Long Path Weighted Score\<close>

text \<open>An abstract finite-depth score, not a new protocol or public premise.
Counter levels prevent one sampled key occurring twice on a single path.\<close>

definition lpw_mean :: "('a::finite \<Rightarrow> prob) \<Rightarrow> prob" where
  "lpw_mean f = (\<Sum>x\<in>UNIV. f x) / Nat.of_nat CARD('a)"

lemma lpw_mean_cong:
  "(\<And>x. f x = g x) \<Longrightarrow> lpw_mean f = lpw_mean g"
  by (simp add: lpw_mean_def)

lemma lpw_div_mono: "(a::prob)\<le>b \<Longrightarrow> a/c\<le>b/c"
  by transfer (simp add: divide_right_mono)

lemma lpw_mult_div: "(a::prob)*b/c=a*(b/c)"
  by transfer simp

lemma lpw_div_div: "(a::prob)/b/c=a/(b*c)"
  by transfer simp

lemma lpw_div_cancel: "(a::prob)\<noteq>0 \<Longrightarrow> a*b/a=b"
  by transfer simp

lemma lpw_mean_const [simp]: "lpw_mean (\<lambda>x::'a::finite. c) = c"
  by (simp add: lpw_mean_def lpw_div_cancel)

lemma lpw_mean_mono:
  "(\<And>x. f x \<le> g x) \<Longrightarrow> lpw_mean f \<le> lpw_mean g"
  unfolding lpw_mean_def by (intro lpw_div_mono sum_mono) auto

lemma lpw_mean_scale:
  "lpw_mean (\<lambda>x. c * f x) = c * lpw_mean f"
  by (simp add: lpw_mean_def sum_distrib_left[symmetric] lpw_mult_div)

lemma lpw_mean_swap:
  "lpw_mean (\<lambda>x. lpw_mean (\<lambda>y. f x y)) =
   lpw_mean (\<lambda>y. lpw_mean (\<lambda>x. f x y))"
  unfolding lpw_mean_def
  by (simp add: sum_divide_nnreal lpw_div_div)
     (subst sum.swap, simp only: mult.commute)

fun lpw_score ::
  "('a::finite set) \<Rightarrow> prob \<Rightarrow> (nat \<times> 'v \<Rightarrow> 'a \<Rightarrow> 'v option) \<Rightarrow>
   (nat \<times> 'v \<Rightarrow> 'a option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> prob" where
  "lpw_score S p D X 0 i v = 1"
| "lpw_score S p D X (Suc n) i v =
   (let c = \<lambda>x. if x\<in>S then
       (case D (i,v) x of None \<Rightarrow> p^n | Some w \<Rightarrow> lpw_score S p D X n (Suc i) w)
     else 0
    in case X (i,v) of None \<Rightarrow> lpw_mean c | Some x \<Rightarrow> c x)"

lemma lpw_score_cong:
  assumes "\<And>j w. i\<le>j \<Longrightarrow> X (j,w)=Y (j,w)"
  shows "lpw_score S p D X n i v = lpw_score S p D Y n i v"
  using assms
proof (induction n arbitrary: i v)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have here: "X (i,v)=Y (i,v)" by (rule Suc.prems) simp
  have tail: "\<And>w. lpw_score S p D X n (Suc i) w =
      lpw_score S p D Y n (Suc i) w"
    by (rule Suc.IH) (use Suc.prems in auto)
  have tails: "lpw_score S p D X n (Suc i) = lpw_score S p D Y n (Suc i)"
    by (rule ext, rule tail)
  show ?case by (simp only: lpw_score.simps here tails)
qed

lemma lpw_score_update_before:
  assumes "k<i"
  shows "lpw_score S p D (X((k,w):=Some x)) n i v = lpw_score S p D X n i v"
  by (rule lpw_score_cong) (use assms in auto)

lemma lpw_mean_eval:
  "lpw_mean (\<lambda>z. case opt of None \<Rightarrow> lpw_mean (f z) | Some x \<Rightarrow> f z x) =
   (case opt of None \<Rightarrow> lpw_mean (\<lambda>x. lpw_mean (\<lambda>z. f z x)) | Some x \<Rightarrow> lpw_mean (\<lambda>z. f z x))"
  proof (cases opt)
  case None
  show ?thesis unfolding None option.case
    using lpw_mean_swap[of f] .
next
  case (Some x)
  then show ?thesis by simp
qed

lemma lpw_score_fresh_average:
  assumes fresh: "X (k,w)=None"
  shows "lpw_mean (\<lambda>x. lpw_score S p D (X((k,w):=Some x)) n i v) =
    lpw_score S p D X n i v"
proof (induction n arbitrary: i v)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "(k,w)=(i,v)")
    case True
    have tail: "\<And>x z. lpw_score S p D (X((k,w):=Some x)) n (Suc i) z =
        lpw_score S p D X n (Suc i) z"
      by (rule lpw_score_update_before) (use True in auto)
    have tails: "\<And>x. lpw_score S p D (X((k,w):=Some x)) n (Suc i) =
        lpw_score S p D X n (Suc i)"
      by (rule ext, rule tail)
    show ?thesis
      apply (simp only: lpw_score.simps Let_def tails)
      using fresh True by simp
  next
    case False
    have here: "\<And>x. (X((k,w):=Some x)) (i,v)=X(i,v)"
      using False by auto
    have point: "\<And>y. lpw_mean (\<lambda>x. if y\<in>S then
        (case D(i,v) y of None \<Rightarrow> p^n |
         Some z \<Rightarrow> lpw_score S p D (X((k,w):=Some x)) n (Suc i) z) else 0) =
        (if y\<in>S then (case D(i,v) y of None \<Rightarrow> p^n |
         Some z \<Rightarrow> lpw_score S p D X n (Suc i) z) else 0)"
      proof -
      fix y
      show "lpw_mean (\<lambda>x. if y\<in>S then
        (case D(i,v) y of None \<Rightarrow> p^n |
         Some z \<Rightarrow> lpw_score S p D (X((k,w):=Some x)) n (Suc i) z) else 0) =
        (if y\<in>S then (case D(i,v) y of None \<Rightarrow> p^n |
         Some z \<Rightarrow> lpw_score S p D X n (Suc i) z) else 0)"
        by (cases "y\<in>S"; cases "D(i,v) y") (simp_all add: Suc.IH)
    qed
    show ?thesis
      by (simp only: lpw_score.simps Let_def here lpw_mean_eval point)
  qed
qed

definition lpw_mass :: "'a::finite set \<Rightarrow> prob" where
  "lpw_mass S = lpw_mean (\<lambda>x. if x\<in>S then 1 else 0)"

lemma lpw_mean_indicator_weight:
  "lpw_mean (\<lambda>x. if x\<in>S then c else 0) = lpw_mass S * c"
proof -
  have point: "\<And>x. (if x\<in>S then c else 0) = c * (if x\<in>S then 1 else 0)"
    by simp
  show ?thesis by (simp only: point lpw_mean_scale lpw_mass_def mult.commute)
qed

lemma lpw_mass_card:
  "lpw_mass (S::'a::finite set) = nnreal(card S)/nnreal(CARD('a))"
  unfolding lpw_mass_def lpw_mean_def
  by (simp add: sum.If_cases)

lemma lpw_score_unrouted:
  assumes query: "X(i,v)=None" and routes: "\<And>x. D(i,v) x=None"
  shows "lpw_score S p D X (Suc n) i v = lpw_mass S * p^n"
  by (simp add: Let_def query routes lpw_mean_indicator_weight cong: if_cong)

lemma lpw_score_initial:
  assumes mass: "lpw_mass S\<le>p"
  shows "lpw_score S p (\<lambda>k x. None) (\<lambda>k. None) n i v \<le> p^n"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc m)
  have "lpw_mass S*p^m \<le> p*p^m"
    by (rule mult_right_mono[OF mass]) simp
  then show ?thesis by (simp add: Suc lpw_score_unrouted lpw_mean_indicator_weight cong: if_cong)
qed

subsection \<open>Long Path Route Birth\<close>

text \<open>Route insertion is safe for a whole forward-closed unqueried region.
No chronological order of the query answers is assumed.\<close>

lemma lpw_select_mono:
  assumes "\<And>x. f x\<le>g x"
  shows "(case opt of None \<Rightarrow> lpw_mean f | Some x \<Rightarrow> f x) \<le>
    (case opt of None \<Rightarrow> lpw_mean g | Some x \<Rightarrow> g x)"
  using assms by (cases opt) (auto intro: lpw_mean_mono)

lemma lpw_score_virgin_region:
  assumes mass: "lpw_mass S\<le>p"
    and empty: "\<And>j w. w\<in>V \<Longrightarrow> X(j,w)=None"
    and closed: "\<And>j v x w. v\<in>V \<Longrightarrow> D(j,v) x=Some w \<Longrightarrow> w\<in>V"
    and vertex: "v\<in>V"
  shows "lpw_score S p D X n i v \<le> p^n"
  using vertex
proof (induction n arbitrary: i v)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have raw: "\<And>x. (if x\<in>S then
      (case D(i,v) x of None \<Rightarrow> p^n | Some w \<Rightarrow> lpw_score S p D X n (Suc i) w)
      else 0) \<le> (if x\<in>S then p^n else 0)"
  proof -
    fix x
    show "(if x\<in>S then
      (case D(i,v) x of None \<Rightarrow> p^n | Some w \<Rightarrow> lpw_score S p D X n (Suc i) w)
      else 0) \<le> (if x\<in>S then p^n else 0)"
      by (cases "x\<in>S"; cases "D(i,v) x")
        (auto intro: Suc.IH closed[OF Suc.prems])
  qed
  have avg: "lpw_mean (\<lambda>x. if x\<in>S then
      (case D(i,v) x of None \<Rightarrow> p^n | Some w \<Rightarrow> lpw_score S p D X n (Suc i) w)
      else 0) \<le> lpw_mean (\<lambda>x. if x\<in>S then p^n else 0)"
    by (rule lpw_mean_mono, rule raw)
  have "lpw_score S p D X (Suc n) i v \<le> lpw_mass S*p^n"
    unfolding lpw_score.simps Let_def empty[OF Suc.prems] option.case
    using avg by (simp only: lpw_mean_indicator_weight)
  also have "... \<le> p*p^n" by (rule mult_right_mono[OF mass]) simp
  finally show ?case by simp
qed

lemma lpw_score_new_routes:
  assumes mass: "lpw_mass S\<le>p"
    and keep: "\<And>key x w. D key x=Some w \<Longrightarrow> E key x=Some w"
    and added: "\<And>key x w. D key x=None \<Longrightarrow> E key x=Some w \<Longrightarrow> w\<in>V"
    and empty: "\<And>j w. w\<in>V \<Longrightarrow> X(j,w)=None"
    and closed: "\<And>j v x w. v\<in>V \<Longrightarrow> E(j,v) x=Some w \<Longrightarrow> w\<in>V"
  shows "lpw_score S p E X n i v \<le> lpw_score S p D X n i v"
proof (induction n arbitrary: i v)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have child: "\<And>x. (case E(i,v) x of None \<Rightarrow> p^n |
      Some w \<Rightarrow> lpw_score S p E X n (Suc i) w) \<le>
      (case D(i,v) x of None \<Rightarrow> p^n |
      Some w \<Rightarrow> lpw_score S p D X n (Suc i) w)"
  proof -
    fix x
    show "(case E(i,v) x of None \<Rightarrow> p^n |
      Some w \<Rightarrow> lpw_score S p E X n (Suc i) w) \<le>
      (case D(i,v) x of None \<Rightarrow> p^n |
      Some w \<Rightarrow> lpw_score S p D X n (Suc i) w)"
    proof (cases "D(i,v) x")
      case None
      show ?thesis
      proof (cases "E(i,v) x")
        case None
        then show ?thesis using \<open>D(i,v) x=None\<close> by simp
      next
        case (Some w)
        have "w\<in>V" by (rule added[OF None Some])
        have "lpw_score S p E X n (Suc i) w \<le> p^n"
          by (rule lpw_score_virgin_region[where V=V])
             (use mass empty closed \<open>w\<in>V\<close> in auto)
        then show ?thesis by (simp add: None Some)
      qed
    next
      case (Some w)
      have "E(i,v) x=Some w" by (rule keep[OF Some])
      then show ?thesis using Suc.IH[of "Suc i" w] by (simp add: Some)
    qed
  qed
  show ?case
    unfolding lpw_score.simps Let_def
    by (rule lpw_select_mono) (use child in auto)
qed

fun lpw_accept ::
  "'a::finite set \<Rightarrow> (nat \<times> 'v \<Rightarrow> 'a \<Rightarrow> 'v option) \<Rightarrow>
   (nat \<times> 'v \<Rightarrow> 'a option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> bool" where
  "lpw_accept S D X 0 i v = True"
| "lpw_accept S D X (Suc n) i v =
   (\<exists>x. X(i,v)=Some x \<and> x\<in>S \<and>
     (n=0 \<or> (\<exists>w. D(i,v) x=Some w \<and> lpw_accept S D X n (Suc i) w)))"

lemma lpw_accept_score:
  assumes "lpw_accept S D X n i v"
  shows "lpw_score S p D X n i v = 1"
  using assms
proof (induction n arbitrary: i v)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain x where query: "X(i,v)=Some x" and good: "x\<in>S"
    and rest: "n=0 \<or> (\<exists>w. D(i,v) x=Some w \<and> lpw_accept S D X n (Suc i) w)"
    using Suc.prems by auto
  show ?case
  proof (cases "n=0")
    case True
    then show ?thesis
      by (simp add: Let_def query good split: option.splits)
  next
    case False
    obtain w where edge: "D(i,v) x=Some w" and accepted: "lpw_accept S D X n (Suc i) w"
      using rest False by auto
    have tail: "lpw_score S p D X n (Suc i) w=1" by (rule Suc.IH[OF accepted])
    show ?thesis by (simp add: Let_def query good edge tail)
  qed
qed

subsection \<open>Long Path Actual Routes\<close>

context soundness
begin

definition lpa_route where
  "lpa_route rt ffs cfs M key raw =
    (let F = pair_route_fiber UNIV rt ffs cfs (snd key) (channel_for_hash_map M)
     in if \<exists>w. raw\<in>F w then Some (SOME w. raw\<in>F w) else None)"

lemma lpa_route_someD:
  assumes "lpa_route rt ffs cfs M key raw=Some w"
  shows "raw\<in>pair_route_fiber UNIV rt ffs cfs (snd key) (channel_for_hash_map M) w"
proof -
  let ?P = "\<lambda>w. raw\<in>pair_route_fiber UNIV rt ffs cfs (snd key) (channel_for_hash_map M) w"
  have ex: "\<exists>w. ?P w" and eq: "(SOME w. ?P w)=w"
    using assms by (auto simp: lpa_route_def Let_def split: if_splits)
  have "?P (SOME w. ?P w)" by (rule someI_ex[OF ex])
  then show ?thesis by (simp only: eq)
qed

lemma lpa_route_someI:
  assumes clean: "\<not>hash_map_output_collision (channel_for_hash_map M)"
    and hit: "raw\<in>pair_route_fiber UNIV rt ffs cfs (snd key) (channel_for_hash_map M) w"
  shows "lpa_route rt ffs cfs M key raw=Some w"
proof -
  let ?P = "\<lambda>v. raw\<in>pair_route_fiber UNIV rt ffs cfs (snd key) (channel_for_hash_map M) v"
  have unique: "\<And>v. ?P v \<Longrightarrow> v=w"
  proof -
    fix v
    assume "?P v"
    then show "v=w"
      using pair_route_fibers_disjoint[OF clean, of v w UNIV rt ffs cfs "snd key"] hit
      by blast
  qed
  have choice: "(SOME v. ?P v)=w" by (rule some_equality) (rule hit, erule unique)
  have ex: "\<exists>v. ?P v" using hit by blast
  show ?thesis by (simp only: lpa_route_def Let_def ex if_True choice)
qed

lemma lpa_route_query_update:
  "lpa_route rt ffs cfs (fmupd (QueryIndexChallenge j v) raw M) =
   lpa_route rt ffs cfs M"
  by (rule ext)+ (simp add: lpa_route_def Let_def causal_route_query_update)

lemma lpa_query_values_nonquery:
  assumes nonquery: "\<And>j v. key\<noteq>QueryIndexChallenge j v"
  shows "fmlookup (fmupd key raw M) (QueryIndexChallenge j v) =
    fmlookup M (QueryIndexChallenge j v)"
  using nonquery by auto

lemma lpa_route_chain:
  assumes route: "lpa_route rt ffs cfs M (j,v) raw=Some w"
  shows "\<exists>xs. ro_absorb_lookup_chain (channel_for_hash_map M) v xs w"
  using lpa_route_someD[OF route] by (auto simp: pair_route_fiber_def)

lemma lpa_clean_prefix:
  assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
  shows "\<not>hash_map_output_collision (channel_for_hash_map M)"
  using clean hash_map_output_collision_mono[OF _ ext] by blast

lemma lpa_route_keep:
  assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
    and old: "lpa_route rt ffs cfs M key raw=Some w"
  shows "lpa_route rt ffs cfs U key raw=Some w"
proof (rule lpa_route_someI[OF clean])
  show "raw\<in>pair_route_fiber UNIV rt ffs cfs (snd key) (channel_for_hash_map U) w"
    using lpa_route_someD[OF old] causal_route_mono[OF ext] by blast
qed

lemma lpa_added_route_endpoint:
  assumes fresh: "fmlookup M key=None"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map (fmupd key z M))"
    and roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets M"
    and nohit: "z\<notin>weighted_semantic_interval_targets M"
    and old: "lpa_route rt ffs cfs M parent raw=None"
    and added: "lpa_route rt ffs cfs (fmupd key z M) parent raw=Some w"
  shows "w=z"
proof (rule ccontr)
  assume neq: "w\<noteq>z"
  let ?U = "fmupd key z M"
  have ext: "channel_for_hash_map M\<le>channel_for_hash_map ?U"
    using fresh unfolding channel_for_hash_map_def less_eq_hash_ext_def less_eq_fmap_def by auto
  have nt: "\<not>hash_map_new_output_hit (causal_route_targets rt ffs cfs M w)
      (channel_for_hash_map M) (channel_for_hash_map ?U)"
    using nohit roots neq
    unfolding hash_map_new_output_hit_def channel_for_hash_map_def causal_route_targets_def
    by auto
  have fibers: "pair_route_fiber UNIV rt ffs cfs (snd parent) (channel_for_hash_map ?U) w =
     pair_route_fiber UNIV rt ffs cfs (snd parent) (channel_for_hash_map M) w"
    by (rule causal_route_interval_pullback[OF ext nt])
  have hit: "raw\<in>pair_route_fiber UNIV rt ffs cfs (snd parent) (channel_for_hash_map M) w"
    using lpa_route_someD[OF added] by (simp only: fibers)
  have before: "\<not>hash_map_output_collision (channel_for_hash_map M)"
    by (rule lpa_clean_prefix[OF ext clean])
  have "lpa_route rt ffs cfs M parent raw=Some w"
    by (rule lpa_route_someI[OF before hit])
  then show False using old by simp
qed

definition lpa_samples where
  "lpa_samples M key = fmlookup M (QueryIndexChallenge (fst key) (snd key))"

definition lpa_reachable where
  "lpa_reachable M start = {w. \<exists>xs. ro_absorb_lookup_chain (channel_for_hash_map M) start xs w}"

lemma lpa_reachable_self [simp]: "v\<in>lpa_reachable M v"
  unfolding lpa_reachable_def by (rule CollectI, rule exI[of _ "[]"]) simp

lemma lpa_reachable_step:
  assumes v: "v\<in>lpa_reachable M start"
    and edge: "lpa_route rt ffs cfs M (j,v) raw=Some w"
  shows "w\<in>lpa_reachable M start"
proof -
  obtain xs where xs: "ro_absorb_lookup_chain (channel_for_hash_map M) start xs v"
    using v by (auto simp: lpa_reachable_def)
  obtain ys where ys: "ro_absorb_lookup_chain (channel_for_hash_map M) v ys w"
    using lpa_route_chain[OF edge] by blast
  have "ro_absorb_lookup_chain (channel_for_hash_map M) start (xs@ys) w"
    by (rule ro_absorb_lookup_chain_append[OF xs ys])
  then show ?thesis unfolding lpa_reachable_def by blast
qed

lemma lpa_new_region_unqueried:
  assumes fresh: "fmlookup M key=None"
    and nonquery: "\<And>j v. key\<noteq>QueryIndexChallenge j v"
    and nohit: "z\<notin>weighted_semantic_interval_targets M"
    and reachable: "w\<in>lpa_reachable (fmupd key z M) z"
  shows "lpa_samples (fmupd key z M) (j,w)=None"
proof -
  let ?U = "fmupd key z M"
  have ext: "channel_for_hash_map M\<le>channel_for_hash_map ?U"
    using fresh unfolding channel_for_hash_map_def less_eq_hash_ext_def less_eq_fmap_def by auto
  have nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
      (channel_for_hash_map M) (channel_for_hash_map ?U)"
    using nohit unfolding hash_map_new_output_hit_def channel_for_hash_map_def by auto
  obtain xs where chain: "ro_absorb_lookup_chain (channel_for_hash_map ?U) z xs w"
    using reachable by (auto simp: lpa_reachable_def)
  have old: "fmlookup M (QueryIndexChallenge j w)=None"
    by (rule ab_no_old_child_connection[OF ext nt nohit chain])
  show ?thesis using nonquery old by (auto simp: lpa_samples_def)
qed

lemma lpa_nonquery_score:
  assumes mass: "lpw_mass S\<le>p"
    and fresh: "fmlookup M key=None"
    and nonquery: "\<And>j v. key\<noteq>QueryIndexChallenge j v"
    and nohit: "z\<notin>weighted_semantic_interval_targets M"
    and roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets M"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map (fmupd key z M))"
  shows "lpw_score S p (lpa_route rt ffs cfs (fmupd key z M))
      (lpa_samples (fmupd key z M)) n i v \<le>
    lpw_score S p (lpa_route rt ffs cfs M) (lpa_samples M) n i v"
proof -
  let ?U = "fmupd key z M"
  let ?V = "lpa_reachable ?U z"
  have samples: "lpa_samples ?U=lpa_samples M"
    by (rule ext) (use nonquery in \<open>auto simp: lpa_samples_def\<close>)
  have ext: "channel_for_hash_map M\<le>channel_for_hash_map ?U"
    using fresh unfolding channel_for_hash_map_def less_eq_hash_ext_def less_eq_fmap_def by auto
  have keep: "\<And>parent x w. lpa_route rt ffs cfs M parent x=Some w \<Longrightarrow>
      lpa_route rt ffs cfs ?U parent x=Some w"
    by (rule lpa_route_keep[OF ext clean])
  have added: "\<And>parent x w. lpa_route rt ffs cfs M parent x=None \<Longrightarrow>
      lpa_route rt ffs cfs ?U parent x=Some w \<Longrightarrow> w\<in>?V"
    using lpa_added_route_endpoint[OF fresh clean roots nohit] by force
  have empty: "\<And>j w. w\<in>?V \<Longrightarrow> lpa_samples ?U (j,w)=None"
    by (rule lpa_new_region_unqueried[OF fresh nonquery nohit])
  have "lpw_score S p (lpa_route rt ffs cfs ?U) (lpa_samples ?U) n i v \<le>
      lpw_score S p (lpa_route rt ffs cfs M) (lpa_samples ?U) n i v"
    by (rule lpw_score_new_routes[where V="?V"])
       (use mass keep added empty lpa_reachable_step in auto)
  then show ?thesis by (simp only: samples)
qed

end

subsection \<open>Long Path Actual Drift\<close>

context soundness
begin

lemma lpd_wp_sum:
  assumes "finite A"
  shows "wp m (\<lambda>out. \<Sum>x\<in>A. F x out) s = (\<Sum>x\<in>A. wp m (F x) s)"
  using assms
  by (induction A rule: finite_induct) (simp_all add: causal_wp_add causal_wp_const)

lemma lpd_probe_mean:
  fixes f :: "'f \<Rightarrow> prob"
  assumes fresh: "fmlookup (HashMap s) key=None"
  shows "wp (pair_probe key)
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> f(ep_raw e)) s = lpw_mean f"
proof -
  let ?I = "\<lambda>x out. case out of None \<Rightarrow> False | Some(e,t) \<Rightarrow> ep_raw e=x"
  have point: "\<And>out. (case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> f(ep_raw e)) =
       (\<Sum>x\<in>UNIV. if ?I x out then f x else 0)"
    by (simp split: option.splits prod.splits)
  have single: "\<And>x. wp (pair_probe key) (\<lambda>out. if ?I x out then f x else 0) s =
       ep_mass {x} * f x"
  proof -
    fix x
    have eq: "(\<lambda>out. if ?I x out then f x else 0) =
       (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> if ep_raw e\<in>{x} then f x else 0)"
      by (rule ext) (simp split: option.splits prod.splits)
    show "wp (pair_probe key) (\<lambda>out. if ?I x out then f x else 0) s =
       ep_mass {x} * f x"
      unfolding eq by (rule ep_probe_raw_weight[OF fresh])
  qed
  have "wp (pair_probe key)
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> f(ep_raw e)) s =
      (\<Sum>x\<in>UNIV. ep_mass {x} * f x)"
    by (simp only: point lpd_wp_sum[OF finite] single)
  also have "... = lpw_mean f"
    unfolding ep_mass_def lpw_mean_def
    by (simp add: size_card lpw_mult_div[symmetric] mult.commute sum_divide_nnreal)
  finally show ?thesis .
qed

lemma lpd_samples_query_update:
  "lpa_samples (fmupd (QueryIndexChallenge j v) raw M) =
    (lpa_samples M)((j,v):=Some raw)"
  by (rule ext) (auto simp: lpa_samples_def)

definition lpd_score where
  "lpd_score S p rt ffs cfs n i v M =
    lpw_score S p (lpa_route rt ffs cfs M) (lpa_samples M) n i v"

lemma lpd_query_fresh_average:
  assumes fresh: "fmlookup M (QueryIndexChallenge j w)=None"
  shows "lpw_mean (\<lambda>raw. lpd_score S p rt ffs cfs n i v
       (fmupd (QueryIndexChallenge j w) raw M)) =
    lpd_score S p rt ffs cfs n i v M"
  unfolding lpd_score_def lpa_route_query_update lpd_samples_query_update
  by (rule lpw_score_fresh_average) (use fresh in \<open>simp add: lpa_samples_def\<close>)

lemma lpd_query_wp:
  assumes fresh: "fmlookup (HashMap s) (QueryIndexChallenge j w)=None"
  shows "wp (pair_probe (QueryIndexChallenge j w))
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
       lpd_score S p rt ffs cfs n i v (fmupd (QueryIndexChallenge j w) (ep_raw e) (HashMap s))) s =
    lpd_score S p rt ffs cfs n i v (HashMap s)"
  using lpd_probe_mean[OF fresh, of
    "\<lambda>raw. lpd_score S p rt ffs cfs n i v (fmupd (QueryIndexChallenge j w) raw (HashMap s))"]
    lpd_query_fresh_average[OF fresh] by simp

lemma lpd_probe_state:
  assumes out: "Some(e,t)\<in>set_dist (execute (pair_probe key) s)"
  obtains raw where "e=(HashMap s,key,raw)"
    "HashMap t=fmupd key raw (HashMap s)"
    "fmlookup (HashMap s) key=None \<or> fmlookup (HashMap s) key=Some raw"
proof -
  obtain raw where e: "e=(HashMap s,key,raw)"
    and t: "t=s\<lparr>HashMap:=fmupd key raw (HashMap s)\<rparr>"
    and hash: "Some(raw,t)\<in>set_dist (execute (hash key) s)"
    by (rule pair_probe_outcome[OF out])
  have "fmlookup (HashMap s) key=None \<or>
      fmlookup (HashMap s) key=fmlookup (HashMap t) key"
    using hash_outcome(1)[OF hash]
    unfolding less_eq_hash_ext_def less_eq_fmap_def by blast
  then show ?thesis using e t that by simp
qed

lemma lpd_stopped_probe:
  assumes mass: "lpw_mass S\<le>p"
    and roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets (HashMap s)"
  shows "wp (pair_probe key)
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
      if \<not>fc_bad_record {} e \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
      then lpd_score S p rt ffs cfs n i v (HashMap t) else 0) s \<le>
    lpd_score S p rt ffs cfs n i v (HashMap s)"
proof -
  let ?G = "\<lambda>e t. \<not>fc_bad_record {} e \<and>
    \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))"
  let ?V = "lpd_score S p rt ffs cfs n i v"
  show ?thesis
  proof (cases "fmlookup (HashMap s) key=None \<and> (\<exists>j w. key=QueryIndexChallenge j w)")
    case True
    obtain j w where key: "key=QueryIndexChallenge j w"
      and fresh: "fmlookup (HashMap s) (QueryIndexChallenge j w)=None"
      using True by auto
    have "wp (pair_probe key)
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> if ?G e t then ?V (HashMap t) else 0) s \<le>
      wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
        ?V (fmupd key (ep_raw e) (HashMap s))) s"
    proof (rule wp_mono_on_support)
      fix out
      assume mem: "out\<in>set_dist (execute (pair_probe key) s)"
      show "(case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> if ?G e t then ?V (HashMap t) else 0) \<le>
        (case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> ?V (fmupd key (ep_raw e) (HashMap s)))"
      proof (cases out)
        case None
        then show ?thesis by simp
      next
        case (Some et)
        obtain e t where et: "et=(e,t)" by (cases et) simp
        obtain raw where e: "e=(HashMap s,key,raw)" and maps: "HashMap t=fmupd key raw (HashMap s)"
          using mem Some et by (auto elim: lpd_probe_state)
        show ?thesis by (simp add: Some et e maps ep_raw_def split: if_splits)
      qed
    qed
    also have "... = ?V (HashMap s)" unfolding key by (rule lpd_query_wp[OF fresh])
    finally show ?thesis .
  next
    case False
    show ?thesis
    proof (rule wp_le_const_on_support)
      fix out
      assume mem: "out\<in>set_dist (execute (pair_probe key) s)"
      show "(case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> if ?G e t then ?V (HashMap t) else 0) \<le>
        ?V (HashMap s)"
      proof (cases out)
        case None
        then show ?thesis by simp
      next
        case (Some et)
        obtain e t where et: "et=(e,t)" by (cases et) simp
        obtain raw where e: "e=(HashMap s,key,raw)" and maps: "HashMap t=fmupd key raw (HashMap s)"
          and lookup: "fmlookup (HashMap s) key=None \<or> fmlookup (HashMap s) key=Some raw"
          using mem Some et by (auto elim: lpd_probe_state)
        show ?thesis
        proof (cases "?G e t")
          case False
          then show ?thesis by (auto simp: Some et)
        next
          case True
          have post: "\<not>hash_map_output_collision (channel_for_hash_map (fmupd key raw (HashMap s)))"
            using True by (simp add: maps)
          have bound: "?V (HashMap t)\<le>?V (HashMap s)"
          proof (cases "fmlookup (HashMap s) key=None")
            case True
            have nonquery: "\<And>j w. key\<noteq>QueryIndexChallenge j w" using False True by blast
            have nohit: "raw\<notin>weighted_semantic_interval_targets (HashMap s)"
              using \<open>?G e t\<close> True by (simp add: e fc_bad_record_def fc_target_def)
            show ?thesis unfolding maps lpd_score_def
              by (rule lpa_nonquery_score[OF mass True nonquery nohit roots post])
          next
            case False
            have cached: "fmlookup (HashMap s) key=Some raw" using lookup False by blast
            have update: "fmupd key raw (HashMap s)=HashMap s"
            proof (rule Finite_Map.fmap_ext)
              fix kk
              show "fmlookup (fmupd key raw (HashMap s)) kk=fmlookup (HashMap s) kk"
                using cached by auto
            qed
            have "HashMap t=HashMap s" using maps update by simp
            then show ?thesis by simp
          qed
          show ?thesis using bound True by (simp add: Some et)
        qed
      qed
    qed
  qed
qed

end

subsection \<open>Long Path Logged Bound\<close>

context soundness
begin

definition lpl_alive where
  "lpl_alive M0 hist M \<longleftrightarrow> fc_history M0 hist M \<and> fc_no_bad {} hist \<and>
    \<not>hash_map_output_collision (channel_for_hash_map M)"

lemma lpl_alive_previous:
  assumes post: "lpl_alive M0 (hist@[(M,key,raw)]) (fmupd key raw M)"
  shows "lpl_alive M0 hist M"
proof -
  have hist: "fc_history M0 hist M"
    and tail: "fc_history M [(M,key,raw)] (fmupd key raw M)"
    and nb: "fc_no_bad {} hist"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map (fmupd key raw M))"
    using post by (auto simp: lpl_alive_def fc_history_append fc_no_bad_def)
  have ext: "channel_for_hash_map M\<le>channel_for_hash_map (fmupd key raw M)"
    by (rule fc_history_extension[OF tail])
  have "\<not>hash_map_output_collision (channel_for_hash_map M)"
    by (rule lpa_clean_prefix[OF ext clean])
  then show ?thesis using hist nb by (simp add: lpl_alive_def)
qed

lemma lpl_potential:
  assumes mass: "lpw_mass S\<le>p"
    and roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets M0"
  shows "lp_potential (\<lambda>fuel hist M. if lpl_alive M0 hist M
    then lpd_score S p rt ffs cfs n i v M else 0)"
proof -
  let ?V = "lpd_score S p rt ffs cfs n i v"
  let ?P = "\<lambda>hist M. if lpl_alive M0 hist M then ?V M else 0"
  have one: "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
      ?P (hist@[e]) (HashMap t)) s \<le> ?P hist (HashMap s)"
    for key hist s
  proof (cases "lpl_alive M0 hist (HashMap s)")
    case True
    have ext: "channel_for_hash_map M0\<le>channel_for_hash_map (HashMap s)"
      using True unfolding lpl_alive_def by (blast intro: fc_history_extension)
    have mono: "weighted_semantic_interval_targets M0\<subseteq>weighted_semantic_interval_targets (HashMap s)"
      using fc_target_mono[OF ext, where R="{}"] by (simp add: fc_target_def)
    have at: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets (HashMap s)"
      using roots mono by blast
    have "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
        ?P (hist@[e]) (HashMap t)) s \<le>
      wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
        if \<not>fc_bad_record {} e \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
        then ?V (HashMap t) else 0) s"
      by (rule wp_mono_on_support)
         (auto simp: lpl_alive_def fc_no_bad_def split: option.splits prod.splits if_splits)
    also have "... \<le> ?V (HashMap s)" by (rule lpd_stopped_probe[OF mass at])
    finally show ?thesis using True by simp
  next
    case False
    have "wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
        ?P (hist@[e]) (HashMap t)) s \<le> 0"
    proof (rule wp_le_const_on_support)
      fix out
      assume mem: "out\<in>set_dist (execute (pair_probe key) s)"
      show "(case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> ?P (hist@[e]) (HashMap t)) \<le> 0"
      proof (cases out)
        case None
        then show ?thesis by simp
      next
        case (Some et)
        obtain e t where et: "et=(e,t)" by (cases et) simp
        obtain raw where e: "e=(HashMap s,key,raw)" and maps: "HashMap t=fmupd key raw (HashMap s)"
          using mem Some et by (auto elim: lpd_probe_state)
        have no: "\<not>lpl_alive M0 (hist@[e]) (HashMap t)"
          using False lpl_alive_previous[of M0 hist "HashMap s" key raw]
          by (auto simp: e maps)
        show ?thesis by (simp add: Some et no)
      qed
    qed
    then show ?thesis using False by simp
  qed
  show ?thesis unfolding lp_potential_def using one by auto
qed

lemma lpl_logged_score:
  assumes logged: "lp_rule q m L"
    and mass: "lpw_mass S\<le>p"
    and roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets (HashMap s)"
  shows "wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow>
    if lpl_alive (HashMap s) es (HashMap t)
    then lpd_score S p rt ffs cfs n i v (HashMap t) else 0) s \<le>
    lpd_score S p rt ffs cfs n i v (HashMap s)"
proof -
  have pot: "lp_potential (\<lambda>fuel hist M. if lpl_alive (HashMap s) hist M
      then lpd_score S p rt ffs cfs n i v M else 0)"
    by (rule lpl_potential[OF mass roots])
  have "wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow>
      if lpl_alive (HashMap s) es (HashMap t)
      then lpd_score S p rt ffs cfs n i v (HashMap t) else 0) s \<le>
      (if lpl_alive (HashMap s) [] (HashMap s)
       then lpd_score S p rt ffs cfs n i v (HashMap s) else 0)"
    using lp_ruleD[OF logged pot, where hist="[]" and s=s]
    by (simp only: append_Nil cong: option.case_cong prod.case_cong)
  also have "... \<le> lpd_score S p rt ffs cfs n i v (HashMap s)" by simp
  finally show ?thesis .
qed

definition lpl_path_event where
  "lpl_path_event S rt ffs cfs n i v out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some((x,es),t) \<Rightarrow>
      \<not>hash_map_output_collision (channel_for_hash_map (HashMap t)) \<and>
      lpw_accept S (lpa_route rt ffs cfs (HashMap t)) (lpa_samples (HashMap t)) n i v)"

lemma lpl_logged_path_bound:
  assumes logged: "lp_rule q m L"
    and mass: "lpw_mass S\<le>p"
    and roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets (HashMap s)"
    and cap: "card(fmdom' (HashMap s))\<le>hcap"
  shows "wp_event L (lpl_path_event S rt ffs cfs n i v) s \<le>
    lpd_score S p rt ffs cfs n i v (HashMap s) + fc_charge ({}::'f set) q hcap"
proof -
  let ?V = "\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow>
    if lpl_alive (HashMap s) es (HashMap t)
    then lpd_score S p rt ffs cfs n i v (HashMap t) else 0"
  let ?B = "\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow> fc_bad_count ({}::'f set) es"
  have point: "(if lpl_path_event S rt ffs cfs n i v out then 1 else 0) \<le> ?V out+?B out"
    if mem: "out\<in>set_dist (execute L s)" for out
  proof (cases "lpl_path_event S rt ffs cfs n i v out")
    case False
    then show ?thesis by simp
  next
    case True
    obtain x es t where out: "out=Some((x,es),t)"
      and clean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap t))"
      and acc: "lpw_accept S (lpa_route rt ffs cfs (HashMap t)) (lpa_samples (HashMap t)) n i v"
      using True unfolding lpl_path_event_def by (auto split: option.splits prod.splits)
    have hist: "fc_history (HashMap s) es (HashMap t)"
      using logged mem unfolding lp_rule_def lg_trace_def by (auto simp: out)
    show ?thesis
    proof (cases "fc_no_bad {} es")
      case True
      have alive: "lpl_alive (HashMap s) es (HashMap t)"
        by (simp add: lpl_alive_def hist True clean)
      have score: "lpd_score S p rt ffs cfs n i v (HashMap t)=1"
        unfolding lpd_score_def by (rule lpw_accept_score[OF acc])
      show ?thesis using alive score \<open>lpl_path_event S rt ffs cfs n i v out\<close> by (simp add: out)
    next
      case False
      have bad: "1\<le>fc_bad_count ({}::'f set) es" by (rule fc_bad_count_detects[OF False])
      have dead: "\<not>lpl_alive (HashMap s) es (HashMap t)"
        using False by (simp add: lpl_alive_def)
      have "1\<le>?V out+?B out" using bad by (simp add: out dead)
      then show ?thesis using \<open>lpl_path_event S rt ffs cfs n i v out\<close> by simp
    qed
  qed
  have "wp_event L (lpl_path_event S rt ffs cfs n i v) s \<le> wp L (\<lambda>out. ?V out+?B out) s"
    unfolding wp_event_def by (rule wp_mono_on_support) (rule point)
  also have "...=wp L ?V s+wp L ?B s" by (rule causal_wp_add)
  also have "...\<le>lpd_score S p rt ffs cfs n i v (HashMap s)+fc_charge ({}::'f set) q hcap"
    by (rule add_mono)
       (rule lpl_logged_score[OF logged mass roots], rule ll_logged_bad_count[OF logged cap])
  finally show ?thesis .
qed

lemma lpl_score_at_birth:
  assumes mass: "lpw_mass S\<le>p"
    and fresh: "fmlookup M key=None"
    and nonquery: "\<And>j w. key\<noteq>QueryIndexChallenge j w"
    and nohit: "z\<notin>weighted_semantic_interval_targets M"
  shows "lpd_score S p rt ffs cfs n i z (fmupd key z M) \<le> p^n"
  unfolding lpd_score_def
  by (rule lpw_score_virgin_region[where V="lpa_reachable (fmupd key z M) z"])
     (use mass lpa_new_region_unqueried[OF fresh nonquery nohit] lpa_reachable_step in auto)

lemma lpl_logged_after_birth:
  assumes logged: "lp_rule q m L"
    and mass: "lpw_mass S\<le>p"
    and fresh: "fmlookup M key=None"
    and nonquery: "\<And>j w. key\<noteq>QueryIndexChallenge j w"
    and nohit: "z\<notin>weighted_semantic_interval_targets M"
    and initial: "HashMap s=fmupd key z M"
    and roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets (HashMap s)"
    and cap: "card(fmdom' (HashMap s))\<le>hcap"
  shows "wp_event L (lpl_path_event S rt ffs cfs n i z) s \<le> p^n+fc_charge ({}::'f set) q hcap"
proof -
  have "wp_event L (lpl_path_event S rt ffs cfs n i z) s \<le>
    lpd_score S p rt ffs cfs n i z (HashMap s)+fc_charge ({}::'f set) q hcap"
    by (rule lpl_logged_path_bound[OF logged mass roots cap])
  also have "...\<le>p^n+fc_charge ({}::'f set) q hcap"
    unfolding initial by (rule add_right_mono[OF lpl_score_at_birth[OF mass fresh nonquery nohit]])
  finally show ?thesis .
qed

definition lpl_original_path_event where
  "lpl_original_path_event S rt ffs cfs n i v out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some(x,t) \<Rightarrow>
      \<not>hash_map_output_collision (channel_for_hash_map (HashMap t)) \<and>
      lpw_accept S (lpa_route rt ffs cfs (HashMap t)) (lpa_samples (HashMap t)) n i v)"

lemma lpl_erase_event:
  assumes logged: "lp_rule q m L"
  shows "wp_event m (lpl_original_path_event S rt ffs cfs n i v) s =
    wp_event L (lpl_path_event S rt ffs cfs n i v) s"
proof -
  have trace: "lg_trace q m L" using logged by (simp add: lp_rule_def)
  let ?P = "\<lambda>out. if lpl_original_path_event S rt ffs cfs n i v out then 1 else 0"
  have eq: "(\<lambda>out. case out of None \<Rightarrow> ?P None | Some((x,es),t) \<Rightarrow> ?P (Some(x,t))) =
      (\<lambda>out. if lpl_path_event S rt ffs cfs n i v out then 1 else 0)"
    by (rule ext) (auto simp: lpl_original_path_event_def lpl_path_event_def
        split: option.splits prod.splits)
  show ?thesis unfolding wp_event_def
    using lg_wp_erase[OF trace, where s=s and P="?P"] by (simp only: eq)
qed

lemma lpl_original_after_birth:
  assumes controlled: "lc_program q m"
    and mass: "lpw_mass S\<le>p"
    and fresh: "fmlookup M key=None"
    and nonquery: "\<And>j w. key\<noteq>QueryIndexChallenge j w"
    and nohit: "z\<notin>weighted_semantic_interval_targets M"
    and initial: "HashMap s=fmupd key z M"
    and roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets (HashMap s)"
    and cap: "card(fmdom' (HashMap s))\<le>hcap"
  shows "wp_event m (lpl_original_path_event S rt ffs cfs n i z) s \<le>
    p^n+fc_charge ({}::'f set) q hcap"
proof -
  obtain L where logged: "lp_rule q m L" using controlled by (auto simp: lc_program_def)
  show ?thesis unfolding lpl_erase_event[OF logged]
    by (rule lpl_logged_after_birth[OF logged mass fresh nonquery nohit initial roots cap])
qed

lemma lpl_mass_eq: "lpw_mass (S::'f set)=ep_mass S"
  unfolding ep_mass_def lpw_mass_card by (simp add: size_card)

fun lpl_family_score where
  "lpl_family_score rT rC n (AP_Family S rt ffs cfs start j) M =
    lpd_score S (ro_mca_weighted_semantic_base rT rC) rt ffs cfs n j start M"

lemma lpl_canonical_birth_score:
  assumes birth: "as_birth rT rC j (M,key,start)=Some f"
    and no_bad: "\<not>fc_bad_record {} (M,key,start)"
  shows "lpl_family_score rT rC n f (fmupd key start M) \<le> (ro_mca_weighted_semantic_base rT rC)^n"
proof -
  obtain pred msg where key: "key=TranscriptAbsorb pred msg"
    and fresh: "fmlookup M key=None"
    and fam: "f=as_family rT rC (fmupd key start M) start j"
    using birth unfolding as_birth_def
    by (auto simp: Let_def split: protocol_hash_input.splits if_splits)
  have nohit: "start\<notin>weighted_semantic_interval_targets M"
    using no_bad fresh by (simp add: fc_bad_record_def fc_target_def)
  have valid: "ap_valid rT rC (f,FC_Pre {} {})" by (rule as_birth_valid[OF birth])
  have mass: "lpw_mass {raw. weighted_semantic_hit rT rC (fmupd key start M) start raw}\<le>ro_mca_weighted_semantic_base rT rC"
    using valid by (simp add: fam as_family_def lpl_mass_eq)
  show ?thesis unfolding fam as_family_def lpl_family_score.simps
    by (rule lpl_score_at_birth[OF mass fresh _ nohit]) (simp add: key)
qed

lemma lpl_canonical_birth_roots:
  assumes birth: "as_birth rT rC j (M,key,start)=Some (AP_Family S rt ffs cfs v k)"
  shows "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets (fmupd key start M)"
proof -
  let ?U = "fmupd key start M"
  have header: "\<exists>data. as_header ?U start data"
    and family: "AP_Family S rt ffs cfs v k=as_family rT rC ?U start j"
    using birth unfolding as_birth_def
    by (auto simp: Let_def split: protocol_hash_input.splits if_splits)
  have "as_header ?U start (as_data ?U start)" by (rule as_data_header[OF header])
  then have roots: "causal_route_roots (staged_trace_root (as_data ?U start))
      (map (\<lambda>root. ((0::'f),root)) (staged_trace_fri_roots (as_data ?U start)))
      (map (\<lambda>root. ((0::'f),root)) (staged_composition_fri_roots (as_data ?U start)))
      \<subseteq>weighted_semantic_interval_targets ?U"
    by (rule as_header_roots_targets)
  show ?thesis using family roots by (auto simp: as_family_def)
qed

end

end
