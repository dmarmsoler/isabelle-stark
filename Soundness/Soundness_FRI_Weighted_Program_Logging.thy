(* Title: Stark/Soundness_FRI_Weighted_Program_Logging.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Program_Logging
  imports
    "Soundness_FRI_Weighted_Adaptive_Families"
begin

section \<open>Program Logging for weighted MCA soundness\<close>

text \<open>A result-preserving logger and potential calculus for the original controlled programs. Erasure recovers the unchanged state-monad experiment; the log is proof instrumentation, not a protocol change.\<close>

subsection \<open>Result Preserving Log\<close>

context soundness
begin

definition lg_lift where
  "lg_lift m = m \<bind> (\<lambda>x. return (x,[]))"

definition lg_hash where
  "lg_hash k = pair_probe k \<bind> (\<lambda>e. return (ep_raw e,[e]))"

definition lg_bind where
  "lg_bind L K = L \<bind> (\<lambda>(x,xs). K x \<bind> (\<lambda>(y,ys). return (y,xs@ys)))"

definition lg_erase where
  "lg_erase L = L \<bind> (\<lambda>(x,xs). return x)"

definition lg_trace where
  "lg_trace n m L \<longleftrightarrow> lg_erase L=m \<and>
    (\<forall>s x es t. Some ((x,es),t)\<in>set_dist (execute L s) \<longrightarrow>
      fc_history (HashMap s) es (HashMap t) \<and> length es\<le>n)"

lemma lg_erase_lift[simp]: "lg_erase (lg_lift m)=m"
  unfolding lg_erase_def lg_lift_def by (simp add: sm_bind_assoc)

lemma lg_erase_hash[simp]: "lg_erase (lg_hash k)=hash k"
  unfolding lg_erase_def lg_hash_def by (simp add: sm_bind_assoc fc_probe_erase_record)

lemma lg_erase_bind:
  "lg_erase (lg_bind L K)=lg_erase L \<bind> (\<lambda>x. lg_erase (K x))"
  unfolding lg_erase_def lg_bind_def by (simp add: sm_bind_assoc split_def)

lemma lg_trace_lift:
  assumes preserving: "hash_map_preserving m"
  shows "lg_trace 0 m (lg_lift m)"
  using preserving unfolding lg_trace_def hash_map_preserving_def
  by (auto simp: lg_lift_def lg_erase_def sm_bind_assoc elim!: set_dist_bindE)

lemma lg_bind_outcome:
  assumes out: "Some ((z,es),t)\<in>set_dist (execute (lg_bind L K) s)"
  obtains x xs u ys where
    "Some ((x,xs),u)\<in>set_dist (execute L s)"
    "Some ((z,ys),t)\<in>set_dist (execute (K x) u)" "es=xs@ys"
  using out unfolding lg_bind_def by (auto elim!: set_dist_bindE)

lemma lg_trace_bind:
  assumes left: "lg_trace q m L" and right: "\<And>x. lg_trace r (k x) (K x)"
  shows "lg_trace (q+r) (m \<bind> k) (lg_bind L K)"
proof -
  have erase: "lg_erase (lg_bind L K)=m \<bind> k"
    using left right unfolding lg_trace_def by (simp add: lg_erase_bind)
  have logs: "\<And>s z es t. Some ((z,es),t)\<in>set_dist (execute (lg_bind L K) s) \<Longrightarrow>
      fc_history (HashMap s) es (HashMap t) \<and> length es\<le>q+r"
  proof -
    fix s z es t
    assume out: "Some ((z,es),t)\<in>set_dist (execute (lg_bind L K) s)"
    obtain x xs u ys where first: "Some ((x,xs),u)\<in>set_dist (execute L s)"
      and second: "Some ((z,ys),t)\<in>set_dist (execute (K x) u)" and es: "es=xs@ys"
      by (rule lg_bind_outcome[OF out])
    have a: "fc_history (HashMap s) xs (HashMap u)" "length xs\<le>q"
      using left first unfolding lg_trace_def by auto
    have b: "fc_history (HashMap u) ys (HashMap t)" "length ys\<le>r"
      using right[of x] second unfolding lg_trace_def by auto
    show "fc_history (HashMap s) es (HashMap t) \<and> length es\<le>q+r"
      using a b by (auto simp: es fc_history_append)
  qed
  show ?thesis using erase logs unfolding lg_trace_def by blast
qed

lemma lg_trace_weaken:
  "lg_trace q m L \<Longrightarrow> q\<le>r \<Longrightarrow> lg_trace r m L"
  unfolding lg_trace_def
  by force

lemma lg_trace_hash: "lg_trace 1 (hash k) (lg_hash k)"
proof -
  have logs: "\<And>s x es t. Some ((x,es),t)\<in>set_dist (execute (lg_hash k) s) \<Longrightarrow>
    fc_history (HashMap s) es (HashMap t) \<and> length es\<le>1"
  proof -
    fix s x es t
    assume out: "Some ((x,es),t)\<in>set_dist (execute (lg_hash k) s)"
    obtain e where probe: "Some (e,t)\<in>set_dist (execute (pair_probe k) s)"
      and es: "es=[e]" using out unfolding lg_hash_def
      by (auto elim!: set_dist_bindE)
    obtain raw where e: "e=(HashMap s,k,raw)"
      and t: "t=s\<lparr>HashMap:=fmupd k raw (HashMap s)\<rparr>"
      and h: "Some (raw,t)\<in>set_dist (execute (hash k) s)"
      by (rule pair_probe_outcome[OF probe])
    have fresh: "fmlookup (HashMap s) k=None \<or> fmlookup (HashMap s) k=Some raw"
    proof -
      have "fmlookup (HashMap s) k=None \<or>
        fmlookup (HashMap s) k=fmlookup (HashMap t) k"
        using hash_outcome(1)[OF h]
        unfolding less_eq_hash_ext_def less_eq_fmap_def by blast
      then show ?thesis by (simp add: t)
    qed
    show "fc_history (HashMap s) es (HashMap t) \<and> length es\<le>1"
      using fresh by (simp add: es e t)
  qed
  show ?thesis using logs unfolding lg_trace_def by simp
qed

lemma lg_history_card:
  assumes history: "fc_history M es U"
  shows "card (fmdom' U)\<le>card (fmdom' M)+length es"
  using history
proof (induction es arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain Me k x where e: "e=(Me,k,x)" by (cases e) auto
  have tail: "fc_history (fmupd k x M) es U"
    using Cons.prems by (simp add: e)
  have cap: "card (fmdom' (fmupd k x M))\<le>Suc (card (fmdom' M))"
    by (simp add: card_insert_if)
  show ?case using Cons.IH[OF tail] cap by simp
qed

lemma lg_trace_card:
  assumes logged: "lg_trace q m L"
    and out: "Some ((x,es),t)\<in>set_dist (execute L s)"
    and cap: "card (fmdom' (HashMap s))\<le>hcap"
  shows "card (fmdom' (HashMap t))\<le>hcap+q"
proof -
  have hist: "fc_history (HashMap s) es (HashMap t)" and len: "length es\<le>q"
    using logged out unfolding lg_trace_def by auto
  show ?thesis using lg_history_card[OF hist] cap len by linarith
qed

lemma lg_wp_erase:
  assumes trace: "lg_trace q m L"
  shows "wp m P s = wp L (\<lambda>out. case out of None \<Rightarrow> P None
    | Some ((x,es),t) \<Rightarrow> P (Some (x,t))) s"
proof -
  have erase: "m=L \<bind> (\<lambda>p. return (fst p))"
    using trace unfolding lg_trace_def lg_erase_def by (simp add: split_def)
  show ?thesis unfolding erase wp_bind_return_map
    by (rule arg_cong[where f="\<lambda>Q. wp L Q s"], rule ext)
      (auto split: option.splits prod.splits)
qed

lemma lg_erase_outcome:
  assumes trace: "lg_trace q m L"
  shows "Some (x,t)\<in>set_dist (execute m s) \<longleftrightarrow>
    (\<exists>es. Some ((x,es),t)\<in>set_dist (execute L s))"
  using trace unfolding lg_trace_def lg_erase_def
  by (auto elim!: set_dist_bindE intro: set_dist_bindI)

end

subsection \<open>Logged Potential Rules\<close>

context soundness
begin

definition lp_potential where
  "lp_potential P \<longleftrightarrow>
    (\<forall>a b hist M. a\<le>b \<longrightarrow> P a hist M\<le>P b hist M) \<and>
    (\<forall>n hist k s. wp (pair_probe k)
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow> P n (hist@[e]) (HashMap t)) s
      \<le> P (Suc n) hist (HashMap s))"

definition lp_rule where
  "lp_rule q m L \<longleftrightarrow> lg_trace q m L \<and>
    (\<forall>P n hist s. lp_potential P \<longrightarrow>
      wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow>
        P n (hist@es) (HashMap t)) s \<le> P (q+n) hist (HashMap s))"

lemma lp_rule_lift:
  assumes preserving: "hash_map_preserving m"
  shows "lp_rule 0 m (lg_lift m)"
proof -
  have bound: "\<And>P n hist s. wp (lg_lift m)
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> P n (hist@es) (HashMap t)) s
      \<le> P n hist (HashMap s)"
    unfolding lg_lift_def wp_bind_return_map
    by (rule wp_le_const_on_support)
      (use preserving in \<open>auto simp: hash_map_preserving_def split: option.splits prod.splits\<close>)
  show ?thesis using bound lg_trace_lift[OF preserving]
    unfolding lp_rule_def
    by fastforce
qed

lemma lp_rule_hash: "lp_rule 1 (hash k) (lg_hash k)"
proof -
  have bound: "\<And>P n hist s. lp_potential P \<Longrightarrow> wp (lg_hash k)
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> P n (hist@es) (HashMap t)) s
      \<le> P (Suc n) hist (HashMap s)"
    unfolding lg_hash_def wp_bind_return_map
    by (simp add: lp_potential_def)
  show ?thesis using bound lg_trace_hash
    unfolding lp_rule_def by simp
qed

lemma lp_ruleD:
  assumes rule: "lp_rule q m L" and potential: "lp_potential P"
  shows "wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow>
      P n (hist@es) (HashMap t)) s \<le> P (q+n) hist (HashMap s)"
  using rule potential unfolding lp_rule_def by blast

lemma lp_rule_bind:
  assumes left: "lp_rule q m L" and right: "\<And>x. lp_rule r (k x) (K x)"
  shows "lp_rule (q+r) (m \<bind> k) (lg_bind L K)"
proof -
  have trace: "lg_trace (q+r) (m \<bind> k) (lg_bind L K)"
    by (rule lg_trace_bind) (use left right in \<open>auto simp: lp_rule_def\<close>)
  have bound: "wp (lg_bind L K)
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> P n (hist@es) (HashMap t)) s
      \<le> P (q+r+n) hist (HashMap s)"
    if potential: "lp_potential P" for P n hist s
  proof -
    have cont: "wp (K x \<bind> (\<lambda>(y,ys). return (y,xs@ys)))
        (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> P n (hist@es) (HashMap t)) t
        \<le> P (r+n) (hist@xs) (HashMap t)" for x xs t
    proof -
      have mapped: "wp (K x \<bind> (\<lambda>(y,ys). return (y,xs@ys)))
          (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> P n (hist@es) (HashMap t)) t =
        wp (K x) (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((y,ys),u) \<Rightarrow>
          P n ((hist@xs)@ys) (HashMap u)) t"
        unfolding split_def wp_bind_return_map
        by (rule arg_cong[where f="\<lambda>V. wp (K x) V t"], rule ext)
          (auto split: option.splits prod.splits)
      show ?thesis unfolding mapped
        by (rule lp_ruleD[OF right[of x] potential])
    qed
    have "wp (lg_bind L K)
        (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> P n (hist@es) (HashMap t)) s
      \<le> wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,xs),t) \<Rightarrow>
        P (r+n) (hist@xs) (HashMap t)) s"
      unfolding lg_bind_def wp_bind
      by (rule wp_mono_on_support)
        (use cont in \<open>auto split: option.splits prod.splits\<close>)
    also have "... \<le> P (q+(r+n)) hist (HashMap s)"
      by (rule lp_ruleD[OF left potential])
    finally show ?thesis by (simp add: add.assoc)
  qed
  show ?thesis using trace bound unfolding lp_rule_def by blast
qed

lemma lp_rule_weaken:
  assumes rule: "lp_rule q m L" and le: "q\<le>r"
  shows "lp_rule r m L"
proof -
  have trace: "lg_trace r m L"
    using rule le lg_trace_weaken unfolding lp_rule_def by blast
  have bound: "wp L
      (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> P n (hist@es) (HashMap t)) s
      \<le> P (r+n) hist (HashMap s)"
    if potential: "lp_potential P" for P n hist s
  proof -
    have "wp L
        (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> P n (hist@es) (HashMap t)) s
        \<le> P (q+n) hist (HashMap s)"
      by (rule lp_ruleD[OF rule potential])
    also have "... \<le> P (r+n) hist (HashMap s)"
      using potential le unfolding lp_potential_def by simp
    finally show ?thesis .
  qed
  show ?thesis using trace bound unfolding lp_rule_def by blast
qed

end

subsection \<open>Logged Controlled Programs\<close>

context soundness
begin

definition lc_program :: "nat \<Rightarrow> ('a, 'f protocol_channel) state_monad \<Rightarrow> bool" where
  "lc_program q m \<longleftrightarrow> (\<exists>L. lp_rule q m L)"

lemma lc_preserving:
  "hash_map_preserving m \<Longrightarrow> lc_program 0 m"
  unfolding lc_program_def using lp_rule_lift by blast

lemma lc_hash: "lc_program 1 (hash k :: ('f, 'f protocol_channel) state_monad)"
  unfolding lc_program_def by (rule exI[of _ "lg_hash k"]) (rule lp_rule_hash)

lemma lc_bind:
  assumes left: "lc_program q m" and right: "\<And>x. lc_program r (k x)"
  shows "lc_program (q+r) (m \<bind> k)"
proof -
  obtain L where L: "lp_rule q m L" using left unfolding lc_program_def by blast
  have "\<forall>x. \<exists>K. lp_rule r (k x) K" using right unfolding lc_program_def by blast
  then obtain K where K: "\<And>x. lp_rule r (k x) (K x)" by metis
  show ?thesis unfolding lc_program_def
    by (rule exI[of _ "lg_bind L K"], rule lp_rule_bind[OF L]) (rule K)
qed

lemma lc_weaken:
  "lc_program q m \<Longrightarrow> q\<le>r \<Longrightarrow> lc_program r m"
  unfolding lc_program_def using lp_rule_weaken by blast

lemma lc_controlled:
  assumes controlled: "controlled_ro_program q m"
  shows "lc_program q m"
  using controlled
proof (induction rule: controlled_ro_program.induct)
  case (Return x)
  show ?case by (rule lc_preserving) (rule hash_map_preserving_return)
next
  case Fail
  show ?case by (rule lc_preserving) (rule hash_map_preserving_throw)
next
  case (Sample d)
  show ?case by (rule lc_preserving) (rule hash_map_preserving_state_independent_sample)
next
  case (Query q k x)
  have "lc_program (1+q) (hash x \<bind> k)"
    by (rule lc_bind[OF lc_hash]) (use Query.IH in blast)
  then show ?case by simp
next
  case (Bind q m r k)
  show ?case by (rule lc_bind) (use Bind.IH in blast)+
next
  case (Weaken q m r)
  show ?case by (rule lc_weaken[OF Weaken.IH Weaken.hyps(2)])
qed

end

subsection \<open>Logged Score Ledger\<close>

context soundness
begin

lemma ll_fold_valid:
  assumes old: "ap_invariant rT rC tickets"
    and births: "\<And>e f. birth e=Some f \<Longrightarrow> ap_valid rT rC (f,FC_Pre {} {})"
  shows "ap_invariant rT rC (foldl (ap_step rT rC birth) tickets es)"
  using old
proof (induction es arbitrary: tickets)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  have next_inv: "ap_invariant rT rC (ap_step rT rC birth tickets e)"
    by (rule ap_step_valid[OF Cons.prems]) (rule births)
  show ?case using Cons.IH[OF next_inv] by simp
qed

lemma ll_portfolio_potential:
  assumes old: "ap_invariant rT rC tickets"
    and births: "\<And>e f. birth e=Some f \<Longrightarrow> ap_valid rT rC (f,FC_Pre {} {})"
  shows "lp_potential (\<lambda>n hist M.
    ap_score rT rC (foldl (ap_step rT rC birth) tickets hist)+nnreal n*(ro_mca_weighted_semantic_base rT rC)^2)"
proof -
  let ?step="ap_step rT rC birth"
  let ?c="(ro_mca_weighted_semantic_base rT rC)^2"
  have mono: "ap_score rT rC (foldl ?step tickets hist)+nnreal a*?c \<le>
      ap_score rT rC (foldl ?step tickets hist)+nnreal b*?c"
    if "a\<le>b" for a b :: nat and hist
    using that by (intro add_left_mono mult_right_mono) auto
  have one: "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
      ap_score rT rC (foldl ?step tickets (hist@[e]))+nnreal n*?c) s \<le>
    ap_score rT rC (foldl ?step tickets hist)+nnreal (Suc n)*?c" for k hist n s
  proof -
    have inv: "ap_invariant rT rC (foldl ?step tickets hist)"
      by (rule ll_fold_valid[OF old births])
    have "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
        ap_score rT rC (foldl ?step tickets (hist@[e]))+nnreal n*?c) s \<le>
      wp (pair_probe k) (\<lambda>out. (case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
        ap_score rT rC (?step (foldl ?step tickets hist) e))+nnreal n*?c) s"
      by (rule wp_mono_on_support) (auto split: option.splits prod.splits)
    also have "... \<le> ap_score rT rC (foldl ?step tickets hist)+?c+nnreal n*?c"
      unfolding causal_wp_add causal_wp_const
      by (rule add_right_mono[OF ap_step_bound[OF inv births]])
    finally show ?thesis by (simp add: algebra_simps)
  qed
  show ?thesis using mono one unfolding lp_potential_def by blast
qed

lemma ll_logged_score:
  assumes logged: "lp_rule q m L"
    and old: "ap_invariant rT rC tickets"
    and births: "\<And>e f. birth e=Some f \<Longrightarrow> ap_valid rT rC (f,FC_Pre {} {})"
  shows "wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow>
    ap_score rT rC (foldl (ap_step rT rC birth) tickets es)) s
    \<le> ap_score rT rC tickets+nnreal q*(ro_mca_weighted_semantic_base rT rC)^2"
proof -
  have potential: "lp_potential (\<lambda>n hist M.
      ap_score rT rC (foldl (ap_step rT rC birth) tickets hist)+nnreal n*(ro_mca_weighted_semantic_base rT rC)^2)"
    by (rule ll_portfolio_potential[OF old]) (rule births)
  have "wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow>
      ap_score rT rC (foldl (ap_step rT rC birth) tickets es)) s \<le>
    wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow>
      ap_score rT rC (foldl (ap_step rT rC birth) tickets ([]@es))+nnreal 0*(ro_mca_weighted_semantic_base rT rC)^2) s"
    by (rule wp_mono_on_support) (auto split: option.splits prod.splits)
  also have "... \<le> ap_score rT rC tickets+nnreal q*(ro_mca_weighted_semantic_base rT rC)^2"
    using lp_ruleD[OF logged potential, where n=0 and hist="[]" and s=s] by simp
  finally show ?thesis .

qed

lemma ll_charge_add:
  "fc_charge R (q+r) hcap = fc_charge R q hcap+fc_charge R r (hcap+q)"
  by (induction q arbitrary: hcap) (simp_all add: add.assoc)

lemma ll_charge_mono_h:
  assumes le: "hcap\<le>hcap'"
  shows "fc_charge R n hcap\<le>fc_charge R n hcap'"
  using le
proof (induction n arbitrary: hcap hcap')
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case unfolding fc_charge.simps
    by (rule add_mono)
      (rule nnreal_nat_divide_right_mono, use Suc.prems in linarith,
       rule Suc.IH, use Suc.prems in simp)
qed

lemma ll_charge_mono_n:
  assumes le: "q\<le>r"
  shows "fc_charge R q hcap\<le>fc_charge R r hcap"
proof -
  obtain d where r: "r=q+d" using le by (auto simp: le_iff_add)
  show ?thesis by (simp add: r ll_charge_add)
qed

lemma ll_ledger_potential:
  fixes R :: "'f set"
  shows "lp_potential (\<lambda>n hist M. fc_bad_count R hist+fc_charge R n (card (fmdom' M)))"
proof -
  have mono: "fc_bad_count R hist+fc_charge R a (card (fmdom' M)) \<le>
      fc_bad_count R hist+fc_charge R b (card (fmdom' M))"
    if "a\<le>b" for a b hist and M :: "('f protocol_hash_input,'f) fmap"
    by (rule add_left_mono[OF ll_charge_mono_n[OF that]])
  have one: "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
        fc_bad_count R (hist@[e])+fc_charge R n (card (fmdom' (HashMap t)))) s
      \<le> fc_bad_count R hist+fc_charge R (Suc n) (card (fmdom' (HashMap s)))" for k hist n s
  proof -
    let ?h="card (fmdom' (HashMap s))"
    let ?tail="fc_charge R n (Suc ?h)"
    let ?I="\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow> if fc_bad_record R e then 1 else 0"
    have point: "fc_charge R n (card (fmdom' (HashMap t)))\<le>?tail"
      if out: "Some (e,t)\<in>set_dist (execute (pair_probe k) s)" for e t
      by (rule ll_charge_mono_h[OF fc_probe_card[OF out order_refl]])
    have "wp (pair_probe k) (\<lambda>out. case out of None \<Rightarrow> 0 | Some (e,t) \<Rightarrow>
        fc_bad_count R (hist@[e])+fc_charge R n (card (fmdom' (HashMap t)))) s
        \<le> wp (pair_probe k) (\<lambda>out. ?I out+(fc_bad_count R hist+?tail)) s"
      by (rule wp_mono_on_support)
        (use point in \<open>auto simp: fc_bad_count_append add.commute add.left_commute
          intro: add_left_mono split: option.splits prod.splits\<close>)
    also have "... = wp_event (pair_probe k)
        (\<lambda>out. case out of None \<Rightarrow> False | Some (e,t) \<Rightarrow> fc_bad_record R e) s
        +(fc_bad_count R hist+?tail)"
      unfolding causal_wp_add causal_wp_const wp_event_def
      by (rule arg_cong[where f="\<lambda>P. wp (pair_probe k) P s+(fc_bad_count R hist+?tail)"], rule ext)
        (auto split: option.splits prod.splits)
    also have "... \<le> nnreal (5*?h+card R)/nnreal size+(fc_bad_count R hist+?tail)"
      by (rule add_right_mono[OF fc_bad_probe_bound])
    finally show ?thesis by (simp add: add.assoc add.commute add.left_commute)
  qed
  show ?thesis using mono one unfolding lp_potential_def by blast
qed

lemma ll_logged_bad_count:
  fixes R :: "'f set"
  assumes logged: "lp_rule q m L"
    and cap: "card (fmdom' (HashMap s))\<le>hcap"
  shows "wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> fc_bad_count R es) s
    \<le> fc_charge R q hcap"
proof -
  have "wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> fc_bad_count R es) s \<le>
    wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow>
      fc_bad_count R ([]@es)+fc_charge R 0 (card (fmdom' (HashMap t)))) s"
    by (rule wp_mono_on_support) (auto split: option.splits prod.splits)
  also have "... \<le> fc_charge R q (card (fmdom' (HashMap s)))"
    using lp_ruleD[OF logged ll_ledger_potential[where R=R], where n=0 and hist="[]" and s=s]
    by (simp add: fc_bad_count_def)
  also have "... \<le> fc_charge R q hcap" by (rule ll_charge_mono_h[OF cap])
  finally show ?thesis .
qed

end

subsection \<open>Logged Residual Bound\<close>

context soundness
begin

lemma lr_canonical_score:
  assumes logged: "lp_rule q m L"
  shows "wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow>
    ap_score rT rC (foldl (ap_step rT rC (as_birth rT rC j)) [] es)) s
    \<le> nnreal q*(ro_mca_weighted_semantic_base rT rC)^2"
proof -
  have "wp L (\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow>
      ap_score rT rC (foldl (ap_step rT rC (as_birth rT rC j)) [] es)) s
      \<le> ap_score rT rC []+nnreal q*(ro_mca_weighted_semantic_base rT rC)^2"
    by (rule ll_logged_score[OF logged])
      (simp add: ap_invariant_def, rule as_birth_valid)
  then show ?thesis by (simp add: ap_score_def)
qed

lemma lr_selected_bound:
  fixes m :: "('a, 'f protocol_channel) state_monad"
  assumes logged: "lp_rule q m L"
    and power: "clength*scale=2^N"
    and cap: "card (fmdom' (HashMap s))\<le>hcap"
  shows "wp_event L (ar_selected_event rT rC j N) s \<le>
    nnreal q*(ro_mca_weighted_semantic_base rT rC)^2+fc_charge ({}::'f set) q hcap"
proof -
  let ?step="ap_step rT rC (as_birth rT rC j)"
  let ?V="\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> ap_score rT rC (foldl ?step [] es)"
  let ?B="\<lambda>out. case out of None \<Rightarrow> 0 | Some ((x,es),t) \<Rightarrow> fc_bad_count ({}::'f set) es"
  have point: "(if ar_selected_event rT rC j N out then 1 else 0)\<le>?V out+?B out"
    if supported: "out\<in>set_dist (execute L s)" for out
  proof (cases "ar_selected_event rT rC j N out")
    case False
    then show ?thesis by simp
  next
    case True
    obtain x es t where out: "out=Some ((x,es),t)"
      using True unfolding ar_selected_event_def by (auto split: option.splits prod.splits)
    have hist: "fc_history (HashMap s) es (HashMap t)"
      using logged supported unfolding lp_rule_def lg_trace_def by (auto simp: out)
    show ?thesis
    proof (cases "fc_no_bad {} es")
      case True
      have event: "ar_selected_event rT rC j N (Some ((x,es),t))"
        using \<open>ar_selected_event rT rC j N out\<close> by (simp add: out)
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
  have "wp_event L (ar_selected_event rT rC j N) s \<le> wp L (\<lambda>out. ?V out+?B out) s"
    unfolding wp_event_def by (rule wp_mono_on_support) (rule point)
  also have "...=wp L ?V s+wp L ?B s" by (rule causal_wp_add)
  also have "...\<le>nnreal q*(ro_mca_weighted_semantic_base rT rC)^2+fc_charge ({}::'f set) q hcap"
    by (rule add_mono[OF lr_canonical_score[OF logged] ll_logged_bad_count[OF logged cap]])
  finally show ?thesis .
qed

end

end
