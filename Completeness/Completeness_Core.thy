(*  Title:      Stark/Completeness_Core.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Completeness_Core
  imports Stark_Core.Stark
begin

text \<open>Core verification locale, honest-trace predicates, and WP/no-failure infrastructure.\<close>

locale verification =
  p: prover concat omega shift scale clength powers to_nat of_nat size spec rounds vals +
  v: verifier concat omega shift scale clength powers to_nat of_nat size spec rounds spec2
  for concat :: "'f::proth_field \<Rightarrow> 'f \<Rightarrow> 'f"
  and omega :: 'f
  and shift :: 'f
  and scale :: nat
  and clength :: nat
  and powers :: nat
  and of_nat:: "nat \<Rightarrow> 'f"
  and to_nat:: "'f \<Rightarrow> nat"
  and size:: nat
  and spec:: "(('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat) list"
  and rounds :: nat
  and spec2:: "(('f list \<Rightarrow> 'f) \<times> nat list) list"
  and vals :: "'f list"
  +
  assumes constraint_degree_bound:
    "\<And>c roots d.
      (c, roots, d) \<in> set spec \<Longrightarrow>
      degree (c p.f_powers) \<le> d * (clength - 1)"
begin

fun root_check
where
  "root_check p [] = True"
| "root_check p (r#rs) = (poly p r = 0 \<and> root_check p rs)"

definition exec
  where "exec \<equiv> do {
    fr \<leftarrow> p.prover_monad;
    modify (\<lambda>c. c\<lparr>PState := 0, PTranscript:=rev (PTranscript c),
      PTraceFriCounter := 0, PCompositionFriCounter := 0,
      PAlphaCounter := 0, PQueryCounter := 0\<rparr>);
    v.verify_monad
  }"

definition init_state
  where "init_state \<equiv>
    \<lparr>HashMap = fmempty, PState = 0, PTranscript = [],
     PTraceFriCounter = 0, PCompositionFriCounter = 0,
     PAlphaCounter = 0, PQueryCounter = 0\<rparr>"

definition verifier_replay_state
  where "verifier_replay_state s \<equiv>
    s\<lparr>PState := 0, PTranscript := rev (PTranscript s),
      PTraceFriCounter := 0, PCompositionFriCounter := 0,
      PAlphaCounter := 0, PQueryCounter := 0\<rparr>"

definition constraint_roots_vanish
  where
    "constraint_roots_vanish c roots \<longleftrightarrow>
      (\<forall>r \<in> set (p.g_map roots). poly (c p.f_powers) r = 0)"

definition declared_degree_sound
  where
    "declared_degree_sound c roots d \<longleftrightarrow>
      degree (c p.f_powers) \<le> d * (clength - 1)"

definition roots_distinct
  where
    "roots_distinct roots \<longleftrightarrow> distinct (p.g_map roots)"

definition honest_trace_algebra
  where
    "honest_trace_algebra \<longleftrightarrow>
      (\<forall>(c, roots, d) \<in> set spec.
        constraint_roots_vanish c roots)"

definition honest_trace_valid
  where
    "honest_trace_valid \<longleftrightarrow> honest_trace_algebra"

definition no_failure
  where "no_failure m s \<longleftrightarrow> None \<notin> dom (dist (execute m s))"

definition transcript_extends
  where "transcript_extends t s \<longleftrightarrow> (\<exists>xs. PTranscript t = xs @ PTranscript s)"

lemma declared_degree_sound_from_constraint_degree_bound:
  assumes "(c, roots, d) \<in> set spec"
  shows "declared_degree_sound c roots d"
  using constraint_degree_bound[OF assms]
  unfolding declared_degree_sound_def .

lemma roots_distinct_from_spec_roots_distinct:
  assumes "(c, roots, d) \<in> set spec"
  shows "roots_distinct roots"
  using p.g_map_distinct[OF assms]
  unfolding roots_distinct_def .

lemma maxDegree_less_eval_domain:
  "p.maxDegree < clength * scale"
  by (rule p.maxDegree_less_eval_domain)

lemma wp_error_assert[wpsimps]:
  "wp_error (assert b) s = (if b then 0 else 1)"
  unfolding assert_def by (simp add: wpsimps)

lemma no_failure_assert_bindI:
  assumes b
    and "None \<notin> dom (dist (execute (k ()) s))"
  shows "None \<notin> dom (dist (execute (assert b \<bind> k) s))"
  using assms unfolding assert_def by simp

lemma no_failure_bind_returnI:
  assumes "None \<notin> dom (dist (execute m s))"
  shows "None \<notin> dom (dist (execute (m \<bind> (\<lambda>x. return (f x))) s))"
  by (rule no_failure_bindI[OF assms]) simp

lemma no_failure_mfoldI:
  assumes step:
    "\<And>m a s. m \<in> set ms \<Longrightarrow>
      None \<notin> dom (dist (execute (m a) s))"
  shows "None \<notin> dom (dist (execute (mfold a ms) s))"
  using step
proof (induction ms arbitrary: a s)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  show ?case
    unfolding mfold.simps
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute (m a) s))"
      using Cons.prems by simp
  next
    fix x t
    assume "Some (x, t) \<in> set_dist (execute (m a) s)"
    show "None \<notin> dom (dist (execute (mfold x ms) t))"
      by (rule Cons.IH) (use Cons.prems in simp)
  qed
qed

lemma no_failure_mfold_invariantI:
  assumes init: "I a s"
    and step_nf:
      "\<And>m a s. m \<in> set ms \<Longrightarrow> I a s \<Longrightarrow>
        None \<notin> dom (dist (execute (m a) s))"
    and step_inv:
      "\<And>m a s x t. m \<in> set ms \<Longrightarrow> I a s \<Longrightarrow>
        Some (x, t) \<in> set_dist (execute (m a) s) \<Longrightarrow> I x t"
  shows "None \<notin> dom (dist (execute (mfold a ms) s))"
  using init step_nf step_inv
proof (induction ms arbitrary: a s)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  show ?case
    unfolding mfold.simps
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute (m a) s))"
      using Cons.prems by simp
  next
    fix x t
    assume outcome: "Some (x, t) \<in> set_dist (execute (m a) s)"
    have inv_xt: "I x t"
      using Cons.prems(1) Cons.prems(3)[of m a s x t] outcome by simp
    show "None \<notin> dom (dist (execute (mfold x ms) t))"
    proof (rule Cons.IH[OF inv_xt])
      fix m' a' s'
      assume "m' \<in> set ms" and "I a' s'"
      then show "None \<notin> dom (dist (execute (m' a') s'))"
        using Cons.prems by simp
    next
      fix m' a' s' x' t'
      assume m'_in: "m' \<in> set ms" and inv: "I a' s'"
        and out: "Some (x', t') \<in> set_dist (execute (m' a') s')"
      show "I x' t'"
        using Cons.prems(3)[of m' a' s' x' t'] m'_in inv out by simp
    qed
  qed
qed

lemma no_failure_mfold_map_index_fromI:
  assumes init: "I k a s"
    and step_nf:
      "\<And>j x a s. k \<le> j \<Longrightarrow> j < k + length xs \<Longrightarrow>
        x = xs ! (j - k) \<Longrightarrow> I j a s \<Longrightarrow>
        None \<notin> dom (dist (execute (F x a) s))"
    and step_inv:
      "\<And>j x a s y t. k \<le> j \<Longrightarrow> j < k + length xs \<Longrightarrow>
        x = xs ! (j - k) \<Longrightarrow> I j a s \<Longrightarrow>
        Some (y, t) \<in> set_dist (execute (F x a) s) \<Longrightarrow>
        I (Suc j) y t"
  shows "None \<notin> dom (dist (execute (mfold a (map F xs)) s))"
  using init step_nf step_inv
proof (induction xs arbitrary: k a s)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
    unfolding mfold.simps list.map
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute (F x a) s))"
      by (rule Cons.prems(2)[of k x a s]) (use Cons.prems(1) in simp_all)
  next
    fix y t
    assume step_out: "Some (y, t) \<in> set_dist (execute (F x a) s)"
    have inv_next: "I (Suc k) y t"
      by (rule Cons.prems(3)[of k x a s y t])
        (use Cons.prems(1) step_out in simp_all)
    show "None \<notin> dom (dist (execute (mfold y (map F xs)) t))"
    proof (rule Cons.IH[OF inv_next])
      fix j x' a' s'
      assume ge: "Suc k \<le> j"
        and lt: "j < Suc k + length xs"
        and x'_eq: "x' = xs ! (j - Suc k)"
        and inv: "I j a' s'"
      have j_gt: "k < j"
        using ge by simp
      have j_lt: "j < k + length (x # xs)"
        using lt by simp
      have nth_eq: "x' = (x # xs) ! (j - k)"
        using x'_eq j_gt by simp
      show "None \<notin> dom (dist (execute (F x' a') s'))"
        by (rule Cons.prems(2)[OF _ j_lt nth_eq inv]) (use ge in simp)
    next
      fix j x' a' s' y' t'
      assume ge: "Suc k \<le> j"
        and lt: "j < Suc k + length xs"
        and x'_eq: "x' = xs ! (j - Suc k)"
        and inv: "I j a' s'"
        and out: "Some (y', t') \<in> set_dist (execute (F x' a') s')"
      have j_gt: "k < j"
        using ge by simp
      have j_lt: "j < k + length (x # xs)"
        using lt by simp
      have nth_eq: "x' = (x # xs) ! (j - k)"
        using x'_eq j_gt by simp
      show "I (Suc j) y' t'"
        by (rule Cons.prems(3)[OF _ j_lt nth_eq inv out]) (use ge in simp)
    qed
  qed
qed

lemma no_failure_mfold_map_indexI:
  assumes init: "I 0 a s"
    and step_nf:
      "\<And>j x a s. j < length xs \<Longrightarrow>
        x = xs ! j \<Longrightarrow> I j a s \<Longrightarrow>
        None \<notin> dom (dist (execute (F x a) s))"
    and step_inv:
      "\<And>j x a s y t. j < length xs \<Longrightarrow>
        x = xs ! j \<Longrightarrow> I j a s \<Longrightarrow>
        Some (y, t) \<in> set_dist (execute (F x a) s) \<Longrightarrow>
        I (Suc j) y t"
  shows "None \<notin> dom (dist (execute (mfold a (map F xs)) s))"
  by (rule no_failure_mfold_map_index_fromI[
      where I=I and k=0 and xs=xs and F=F, OF init])
    (use step_nf step_inv in simp_all)

lemma no_failure_mmapI:
  assumes step: "\<And>m s. m \<in> set ms \<Longrightarrow> None \<notin> dom (dist (execute m s))"
  shows "None \<notin> dom (dist (execute (mmap ms) s))"
  using step
proof (induction ms arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  show ?case
    unfolding mmap.simps
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute m s))"
      using Cons.prems by simp
  next
    fix x t
    assume "Some (x, t) \<in> set_dist (execute m s)"
    show "None \<notin> dom (dist (execute (mmap ms \<bind> (\<lambda>xs. return (x # xs))) t))"
      by (rule no_failure_bind_returnI)
        (rule Cons.IH, use Cons.prems in simp)
  qed
qed

lemma no_failure_mfold2I:
  assumes step: "\<And>x s. x \<in> set xs \<Longrightarrow> None \<notin> dom (dist (execute (f x) s))"
  shows "None \<notin> dom (dist (execute (mfold2 f xs) s))"
  using step
proof (induction xs arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
    unfolding mfold2.simps
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute (f x) s))"
      using Cons.prems by simp
  next
    fix y t
    assume "Some (y, t) \<in> set_dist (execute (f x) s)"
    show "None \<notin> dom (dist (execute (mfold2 f xs) t))"
      by (rule Cons.IH) (use Cons.prems in simp)
  qed
qed

lemma no_failure_ntimesI:
  assumes step: "\<And>s. None \<notin> dom (dist (execute m s))"
  shows "None \<notin> dom (dist (execute (ntimes m n) s))"
  using assms
proof (induction n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
    unfolding ntimes.simps
  proof (rule no_failure_bindI[OF Suc.prems])
    fix x t
    assume "Some (x, t) \<in> set_dist (execute m s)"
    show "None \<notin> dom (dist (execute (ntimes m n \<bind> (\<lambda>xs. return (x # xs))) t))"
      by (rule no_failure_bind_returnI) (rule Suc.IH[OF Suc.prems])
  qed
qed

lemma no_failure_ntimes_invariantI:
  assumes init: "I s"
    and step_nf: "\<And>s. I s \<Longrightarrow> None \<notin> dom (dist (execute m s))"
    and step_inv:
      "\<And>x s t. I s \<Longrightarrow> Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow> I t"
  shows "None \<notin> dom (dist (execute (ntimes m n) s))"
  using init
proof (induction n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
    unfolding ntimes.simps
  proof (rule no_failure_bindI[OF step_nf[OF Suc.prems]])
    fix x t
    assume step: "Some (x, t) \<in> set_dist (execute m s)"
    have "I t"
      by (rule step_inv[OF Suc.prems step])
    then show "None \<notin> dom (dist (execute (ntimes m n \<bind> (\<lambda>xs. return (x # xs))) t))"
      by (rule no_failure_bind_returnI[OF Suc.IH])
  qed
qed

lemma ntimes_hash_extends:
  fixes m :: "('a, ('f, 'b) protocol_channel_scheme) state_monad"
  assumes step_ext:
      "\<And>x (s::('f, 'b) protocol_channel_scheme) t.
        Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow> s \<le> t"
    and outcome: "Some (xs, t) \<in> set_dist (execute (ntimes m n) s)"
  shows "s \<le> t"
  using outcome
proof (induction n arbitrary: xs s t)
  case 0
  then show ?case
    using p.hash_ext_refl[of s] by simp
next
  case (Suc n)
  have expanded:
    "Some (xs, t) \<in>
      set_dist (execute
        (m \<bind> (\<lambda>x. ntimes m n \<bind> (\<lambda>ys. return (x # ys)))) s)"
    using Suc.prems by simp
  show ?case
  proof (rule p.set_dist_bindE[OF expanded])
    fix x u
    assume step: "Some (x, u) \<in> set_dist (execute m s)"
      and rest:
        "Some (xs, t) \<in>
          set_dist (execute (ntimes m n \<bind> (\<lambda>ys. return (x # ys))) u)"
    show ?thesis
    proof (rule p.set_dist_bindE[OF rest])
      fix ys v
      assume tail_v: "Some (ys, v) \<in> set_dist (execute (ntimes m n) u)"
        and ret: "Some (xs, t) \<in> set_dist (execute (return (x # ys)) v)"
      have tail: "Some (ys, t) \<in> set_dist (execute (ntimes m n) u)"
        using tail_v ret by simp
      have "s \<le> u"
        by (rule step_ext[OF step])
      moreover have "u \<le> t"
        by (rule Suc.IH[OF tail])
      ultimately show ?thesis
        unfolding less_eq_hash_ext_def less_eq_fmap_def
        by (metis option.distinct(1))
    qed
  qed
qed

lemma ntimes_transcript_extends:
  assumes step_ext:
      "\<And>x s t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow> transcript_extends t s"
    and outcome: "Some (xs, t) \<in> set_dist (execute (ntimes m n) s)"
  shows "transcript_extends t s"
  using outcome
proof (induction n arbitrary: xs s t)
  case 0
  then show ?case
    unfolding transcript_extends_def by simp
next
  case (Suc n)
  have expanded:
    "Some (xs, t) \<in>
      set_dist (execute
        (m \<bind> (\<lambda>x. ntimes m n \<bind> (\<lambda>ys. return (x # ys)))) s)"
    using Suc.prems by simp
  show ?case
  proof (rule p.set_dist_bindE[OF expanded])
    fix x u
    assume step: "Some (x, u) \<in> set_dist (execute m s)"
      and rest:
        "Some (xs, t) \<in>
          set_dist (execute (ntimes m n \<bind> (\<lambda>ys. return (x # ys))) u)"
    show ?thesis
    proof (rule p.set_dist_bindE[OF rest])
      fix ys v
      assume tail_v: "Some (ys, v) \<in> set_dist (execute (ntimes m n) u)"
        and ret: "Some (xs, t) \<in> set_dist (execute (return (x # ys)) v)"
      have tail: "Some (ys, t) \<in> set_dist (execute (ntimes m n) u)"
        using tail_v ret by simp
      have "transcript_extends u s"
        by (rule step_ext[OF step])
      moreover have "transcript_extends t u"
        by (rule Suc.IH[OF tail])
      ultimately show ?thesis
        unfolding transcript_extends_def by auto
    qed
  qed
qed

lemma ntimes_Suc_outcomeE:
  assumes outcome: "Some (xs, t) \<in> set_dist (execute (ntimes m (Suc n)) s)"
  obtains x ys u where
    "Some (x, u) \<in> set_dist (execute m s)"
    "Some (ys, t) \<in> set_dist (execute (ntimes m n) u)"
    "xs = x # ys"
proof -
  have expanded:
    "Some (xs, t) \<in>
      set_dist (execute (m \<bind> (\<lambda>x. ntimes m n \<bind> (\<lambda>ys. return (x # ys)))) s)"
    using outcome by simp
  show ?thesis
  proof (rule p.set_dist_bindE[OF expanded])
    fix x u
    assume step: "Some (x, u) \<in> set_dist (execute m s)"
      and rest:
        "Some (xs, t) \<in>
          set_dist (execute (ntimes m n \<bind> (\<lambda>ys. return (x # ys))) u)"
    show ?thesis
    proof (rule p.set_dist_bindE[OF rest])
      fix ys v
      assume tail_v: "Some (ys, v) \<in> set_dist (execute (ntimes m n) u)"
        and ret: "Some (xs, t) \<in> set_dist (execute (return (x # ys)) v)"
      have tail: "Some (ys, t) \<in> set_dist (execute (ntimes m n) u)"
        using tail_v ret by simp
      have xs_eq: "xs = x # ys"
        using ret by simp
      show ?thesis
        by (rule that[OF step tail xs_eq])
    qed
  qed
qed

definition prover_query_round
  where
    "prover_query_round f_merkle f_ls f_ms ls ms \<equiv>
      do {
        idx \<leftarrow> p.receive_query_index_challenge;
        mmap (p.decommit_on_query (p.index (to_nat idx)) f_merkle);
        mfold (p.index (to_nat idx)) (p.decommit_on_fri_layers (butlast (zip f_ls f_ms)));
        mfold (p.index (to_nat idx)) (p.decommit_on_fri_layers (butlast (zip ls ms)));
        return ()
      }"

definition verifier_query_round
  where
    "verifier_query_round fr f_fl f_final as fl final \<equiv>
      do {
        idx \<leftarrow> p.receive_query_index_challenge;
        let idx' = p.index (to_nat idx);
        fv \<leftarrow> mmap (v.check_decommit_on_query fr idx');
        (f_i, f_x, f_len, f_pw) \<leftarrow>
          mfold
            (idx', hd fv, clength * scale, 1)
            (v.receive_query_commits f_fl);
        assert (f_x = f_final);
        (i, x, len, pw) \<leftarrow>
          mfold
            (idx', v.cp_eval as fv (p.h ^ idx' * shift), clength * scale, 1)
            (v.receive_query_commits fl);
        assert (x = final)
      }"

lemma send_no_failure:
  "None \<notin> dom (dist (execute (p.send x) s))"
  by (rule p.send_no_failure)

lemma create_no_failure:
  "None \<notin> dom (dist (execute (p.create xs) s))"
  by (rule p.create_no_failure)

lemma fri_commit_no_failure:
  "None \<notin> dom (dist (execute (p.fri_commit n ps ds ls ms) s))"
proof (induction n arbitrary: ps ds ls ms s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
    unfolding p.fri_commit.simps
  proof (rule no_failure_bindI[OF send_no_failure])
    fix u s1
    assume "Some (u, s1) \<in> set_dist (execute (p.send (value (last ms))) s)"
    show "None \<notin> dom (dist (execute
      (p.receive_random_field_element \<bind>
        (\<lambda>b. let (next_poly, next_domain, next_layer) =
              p.next_fri_layer (last ps) (last ds) b
            in p.create next_layer \<bind>
              (\<lambda>m. p.fri_commit n
                (ps @ [next_poly]) (ds @ [next_domain])
                (ls @ [next_layer]) (ms @ [m])))) s1))"
    proof (rule no_failure_bindI[OF p.receive_random_field_element_no_failure])
      fix b s2
      assume "Some (b, s2) \<in> set_dist (execute p.receive_random_field_element s1)"
      obtain next_poly next_domain next_layer where next_layer_eq:
        "p.next_fri_layer (last ps) (last ds) b =
          (next_poly, next_domain, next_layer)"
        by (cases "p.next_fri_layer (last ps) (last ds) b")
      show "None \<notin> dom (dist (execute
        (let (next_poly, next_domain, next_layer) =
              p.next_fri_layer (last ps) (last ds) b
          in p.create next_layer \<bind>
            (\<lambda>m. p.fri_commit n
              (ps @ [next_poly]) (ds @ [next_domain])
              (ls @ [next_layer]) (ms @ [m]))) s2))"
        unfolding next_layer_eq split Let_def
      proof (rule no_failure_bindI[OF create_no_failure])
        fix m s3
        assume "Some (m, s3) \<in> set_dist (execute (p.create next_layer) s2)"
        show "None \<notin> dom (dist (execute
          (p.fri_commit n (ps @ [next_poly]) (ds @ [next_domain])
            (ls @ [next_layer]) (ms @ [m])) s3))"
          by (rule Suc.IH)
      qed
    qed
  qed
qed

lemma fri_commit_with_no_failure:
  assumes receiver_no_failure:
    "\<And>s. None \<notin> dom (dist (execute receive_challenge s))"
  shows
    "None \<notin> dom (dist
      (execute (p.fri_commit_with receive_challenge n ps ds ls ms) s))"
proof (induction n arbitrary: ps ds ls ms s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
    unfolding p.fri_commit_with.simps
  proof (rule no_failure_bindI[OF send_no_failure])
    fix u s1
    assume "Some (u, s1) \<in> set_dist (execute (p.send (value (last ms))) s)"
    show "None \<notin> dom (dist (execute
      (receive_challenge \<bind>
        (\<lambda>b. let (next_poly, next_domain, next_layer) =
              p.next_fri_layer (last ps) (last ds) b
            in p.create next_layer \<bind>
              (\<lambda>m. p.fri_commit_with receive_challenge n
                (ps @ [next_poly]) (ds @ [next_domain])
                (ls @ [next_layer]) (ms @ [m])))) s1))"
    proof (rule no_failure_bindI[OF receiver_no_failure])
      fix b s2
      assume "Some (b, s2) \<in> set_dist (execute receive_challenge s1)"
      obtain next_poly next_domain next_layer where next_layer_eq:
        "p.next_fri_layer (last ps) (last ds) b =
          (next_poly, next_domain, next_layer)"
        by (cases "p.next_fri_layer (last ps) (last ds) b")
      show "None \<notin> dom (dist (execute
        (let (next_poly, next_domain, next_layer) =
              p.next_fri_layer (last ps) (last ds) b
          in p.create next_layer \<bind>
            (\<lambda>m. p.fri_commit_with receive_challenge n
              (ps @ [next_poly]) (ds @ [next_domain])
              (ls @ [next_layer]) (ms @ [m]))) s2))"
        unfolding next_layer_eq split Let_def
      proof (rule no_failure_bindI[OF create_no_failure])
        fix m s3
        assume "Some (m, s3) \<in> set_dist (execute (p.create next_layer) s2)"
        show "None \<notin> dom (dist (execute
          (p.fri_commit_with receive_challenge n
            (ps @ [next_poly]) (ds @ [next_domain])
            (ls @ [next_layer]) (ms @ [m])) s3))"
          by (rule Suc.IH)
      qed
    qed
  qed
qed

lemma trace_fri_commit_no_failure:
  "None \<notin> dom (dist (execute (p.trace_fri_commit n ps ds ls ms) s))"
  unfolding p.trace_fri_commit_def
  by (rule fri_commit_with_no_failure)
    (rule p.receive_trace_fri_challenge_no_failure)

lemma composition_fri_commit_no_failure:
  "None \<notin> dom (dist (execute (p.composition_fri_commit n ps ds ls ms) s))"
  unfolding p.composition_fri_commit_def
  by (rule fri_commit_with_no_failure)
    (rule p.receive_composition_fri_challenge_no_failure)

lemma honest_alpha_send_round_no_failure:
  "None \<notin> dom (dist (execute
    (do {
      a \<leftarrow> p.receive_alpha_challenge;
      p.send a;
      return a
    }) s))"
  by (intro no_failure_bindI)
    (simp_all add: p.receive_alpha_challenge_no_failure send_no_failure)

lemma prover_decommit_on_query_step_no_failure:
  "None \<notin> dom (dist (execute
    (do {
      p.send x;
      mfold2 p.send path
    }) s))"
proof (rule no_failure_bindI[OF send_no_failure])
  fix u t
  assume "Some (u, t) \<in> set_dist (execute (p.send x) s)"
  show "None \<notin> dom (dist (execute (mfold2 p.send path) t))"
    by (rule no_failure_mfold2I) (simp add: send_no_failure)
qed

lemma prover_decommit_on_query_no_failure:
  "None \<notin> dom (dist (execute (mmap (p.decommit_on_query idx f_merkle)) s))"
  unfolding p.decommit_on_query_def
  by (rule no_failure_mmapI)
    (auto intro!: prover_decommit_on_query_step_no_failure)

lemma prover_decommit_on_fri_layer_no_failure:
  "None \<notin> dom (dist (execute
    (do {
      let len = length l;
      let idx' = idx mod len;
      let sidx = (idx' + (len div 2)) mod len;
      p.send (l ! idx');
      mfold2 p.send (get_authentication_path len idx' m);
      p.send (l ! sidx);
      mfold2 p.send (get_authentication_path len sidx m);
      return idx'
    }) s))"
  unfolding Let_def
proof (rule no_failure_bindI[OF send_no_failure])
  fix u s1
  assume "Some (u, s1) \<in> set_dist (execute (p.send (l ! (idx mod length l))) s)"
  show "None \<notin> dom (dist (execute
    (mfold2 p.send (get_authentication_path (length l) (idx mod length l) m) \<bind>
      (\<lambda>_. p.send (l ! ((idx mod length l + length l div 2) mod length l)) \<bind>
        (\<lambda>_. mfold2 p.send
          (get_authentication_path (length l)
            ((idx mod length l + length l div 2) mod length l) m) \<bind>
          (\<lambda>_. return (idx mod length l))))) s1))"
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute
      (mfold2 p.send (get_authentication_path (length l) (idx mod length l) m)) s1))"
      by (rule no_failure_mfold2I) (simp add: send_no_failure)
  next
    fix u2 s2
    assume "Some (u2, s2) \<in> set_dist (execute
      (mfold2 p.send (get_authentication_path (length l) (idx mod length l) m)) s1)"
    show "None \<notin> dom (dist (execute
      (p.send (l ! ((idx mod length l + length l div 2) mod length l)) \<bind>
        (\<lambda>_. mfold2 p.send
          (get_authentication_path (length l)
            ((idx mod length l + length l div 2) mod length l) m) \<bind>
          (\<lambda>_. return (idx mod length l)))) s2))"
    proof (rule no_failure_bindI[OF send_no_failure])
      fix u3 s3
      assume "Some (u3, s3) \<in> set_dist (execute
        (p.send (l ! ((idx mod length l + length l div 2) mod length l))) s2)"
      show "None \<notin> dom (dist (execute
        (mfold2 p.send
          (get_authentication_path (length l)
            ((idx mod length l + length l div 2) mod length l) m) \<bind>
          (\<lambda>_. return (idx mod length l))) s3))"
        by (rule no_failure_bind_returnI)
          (rule no_failure_mfold2I, simp add: send_no_failure)
    qed
  qed
qed

lemma prover_decommit_on_fri_layers_no_failure:
  "None \<notin> dom (dist (execute (mfold idx (p.decommit_on_fri_layers fs)) s))"
  unfolding p.decommit_on_fri_layers_def
  by (rule no_failure_mfoldI)
    (auto intro!: prover_decommit_on_fri_layer_no_failure)

lemma prover_query_round_no_failure:
  "None \<notin> dom (dist (execute (prover_query_round f_merkle f_ls f_ms ls ms) s))"
  unfolding prover_query_round_def
proof (rule no_failure_bindI[OF p.receive_query_index_challenge_no_failure])
  fix idx s1
  assume "Some (idx, s1) \<in> set_dist (execute p.receive_query_index_challenge s)"
  show "None \<notin> dom (dist (execute
    (mmap (p.decommit_on_query (p.index (to_nat idx)) f_merkle) \<bind>
      (\<lambda>_. mfold (p.index (to_nat idx))
        (p.decommit_on_fri_layers (butlast (zip f_ls f_ms))) \<bind>
        (\<lambda>_. mfold (p.index (to_nat idx))
          (p.decommit_on_fri_layers (butlast (zip ls ms))) \<bind>
          (\<lambda>_. return ())))) s1))"
  proof (rule no_failure_bindI[OF prover_decommit_on_query_no_failure])
    fix u2 s2
    assume "Some (u2, s2) \<in> set_dist (execute
      (mmap (p.decommit_on_query (p.index (to_nat idx)) f_merkle)) s1)"
    show "None \<notin> dom (dist (execute
      (mfold (p.index (to_nat idx))
        (p.decommit_on_fri_layers (butlast (zip f_ls f_ms))) \<bind>
        (\<lambda>_. mfold (p.index (to_nat idx))
          (p.decommit_on_fri_layers (butlast (zip ls ms))) \<bind>
          (\<lambda>_. return ()))) s2))"
    proof (rule no_failure_bindI[OF prover_decommit_on_fri_layers_no_failure])
      fix u3 s3
      assume "Some (u3, s3) \<in> set_dist (execute
        (mfold (p.index (to_nat idx))
          (p.decommit_on_fri_layers (butlast (zip f_ls f_ms)))) s2)"
      show "None \<notin> dom (dist (execute
        (mfold (p.index (to_nat idx))
          (p.decommit_on_fri_layers (butlast (zip ls ms))) \<bind>
          (\<lambda>_. return ())) s3))"
        by (rule no_failure_bind_returnI)
          (rule prover_decommit_on_fri_layers_no_failure)
    qed
  qed
qed

lemma prover_after_fri_layers_tail_no_failure:
  "None \<notin> dom (dist (execute
    (do {
      p.send (hd (last ls));
      ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds
    }) s))"
proof (rule no_failure_bindI[OF send_no_failure])
  fix u s1
  assume "Some (u, s1) \<in> set_dist (execute (p.send (hd (last ls))) s)"
  show "None \<notin> dom (dist (execute
    (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds) s1))"
    by (rule no_failure_ntimesI) (rule prover_query_round_no_failure)
qed

lemma prover_after_fri_commit_no_failure:
  "None \<notin> dom (dist (execute
    ((case fri_data of (ps, ds, ls, ms) \<Rightarrow>
      do {
        p.send (hd (last ls));
        ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds
      })) s))"
proof -
  obtain ps ds ls ms where fri_data_eq: "fri_data = (ps, ds, ls, ms)"
    by (cases fri_data)
  show ?thesis
    unfolding fri_data_eq case_prod_unfold
    by (rule prover_after_fri_layers_tail_no_failure)
qed

lemma prover_after_fri_commit_named_no_failure:
  "None \<notin> dom (dist (execute
    ((case fri_data of (ps, ds, ls, ms) \<Rightarrow>
      do {
        p.send (hd (last ls));
        ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds
      })) s))"
proof -
  obtain ps ds ls ms where fri_data_eq: "fri_data = (ps, ds, ls, ms)"
    by (cases fri_data)
  show ?thesis
    unfolding fri_data_eq
    apply (simp add: case_prod_unfold)
    apply (rule no_failure_bindI[OF send_no_failure])
    apply (rule no_failure_ntimesI)
    apply (rule prover_query_round_no_failure)
    done
qed

lemma prover_after_alphas_no_failure:
  "None \<notin> dom (dist (execute
    (do {
      p.send (of_nat (degree (p.cp as p.f_powers)));
      cp_merkle \<leftarrow> p.create (p.cp_eval as);
      (ps, ds, ls, ms) \<leftarrow>
        p.composition_fri_commit (ceil_log (degree (p.cp as p.f_powers) + 1))
          [p.cp as p.f_powers] [p.eval_domain] [p.cp_eval as] [cp_merkle];
      p.send (hd (last ls));
      ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds
    }) s))"
  unfolding Let_def
  by (intro no_failure_bindI no_failure_bind_returnI)
    (simp_all add: create_no_failure composition_fri_commit_no_failure
      send_no_failure
      p.receive_random_field_element_no_failure prover_decommit_on_query_no_failure
      p.receive_alpha_challenge_no_failure p.receive_query_index_challenge_no_failure
      prover_decommit_on_fri_layers_no_failure prover_after_fri_commit_no_failure
      prover_after_fri_commit_named_no_failure)

lemma prover_after_trace_fri_commit_no_failure:
  "None \<notin> dom (dist (execute
    ((case trace_fri_data of (f_ps, f_ds, f_ls, f_ms) \<Rightarrow>
      do {
        p.send (hd (last f_ls));
        as \<leftarrow> mmap (replicate (length spec)
          (do {
            a \<leftarrow> p.receive_alpha_challenge;
            p.send a;
            return a
          }));
        p.send (of_nat (degree (p.cp as p.f_powers)));
        cp_merkle \<leftarrow> p.create (p.cp_eval as);
        (ps, ds, ls, ms) \<leftarrow>
          p.composition_fri_commit (ceil_log (degree (p.cp as p.f_powers) + 1))
            [p.cp as p.f_powers] [p.eval_domain] [p.cp_eval as] [cp_merkle];
        p.send (hd (last ls));
        ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds
      })) s))"
proof -
  obtain f_ps f_ds f_ls f_ms where trace_fri_data_eq:
    "trace_fri_data = (f_ps, f_ds, f_ls, f_ms)"
    by (cases trace_fri_data)
  show ?thesis
    unfolding trace_fri_data_eq case_prod_unfold Let_def
    by (intro no_failure_bindI no_failure_mmapI)
      (simp_all add: send_no_failure honest_alpha_send_round_no_failure
        prover_after_alphas_no_failure create_no_failure
        composition_fri_commit_no_failure
        p.receive_alpha_challenge_no_failure p.receive_query_index_challenge_no_failure
        no_failure_ntimesI prover_query_round_no_failure split: prod.splits)
qed

lemma prover_monad_no_failure:
  "None \<notin> dom (dist (execute p.prover_monad init_state))"
  unfolding p.prover_monad_def Let_def
  apply (rule no_failure_bindI)
   apply (rule create_no_failure)
  apply (rule no_failure_bindI)
   apply (rule send_no_failure)
  apply (rule no_failure_bindI)
   apply (rule trace_fri_commit_no_failure)
  apply (simp only: prover_query_round_def[symmetric])
  apply (rule prover_after_trace_fri_commit_no_failure)
  done

lemma mfold_map_index_outcome_invariant_fromI:
  assumes init: "I k a s"
    and step_inv:
      "\<And>j x a s y t. k \<le> j \<Longrightarrow> j < k + length xs \<Longrightarrow>
        x = xs ! (j - k) \<Longrightarrow> I j a s \<Longrightarrow>
        Some (y, t) \<in> set_dist (execute (F x a) s) \<Longrightarrow>
        I (Suc j) y t"
    and outcome:
      "Some (y, t) \<in> set_dist (execute (mfold a (map F xs)) s)"
  shows "I (k + length xs) y t"
  using init step_inv outcome
proof (induction xs arbitrary: k a s y t)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(3) obtain y0 t0 where
    head: "Some (y0, t0) \<in> set_dist (execute (F x a) s)"
    and tail:
      "Some (y, t) \<in> set_dist (execute (mfold y0 (map F xs)) t0)"
    unfolding mfold.simps by (auto elim!: p.set_dist_bindE)
  have inv_next: "I (Suc k) y0 t0"
    by (rule Cons.prems(2)[of k x a s y0 t0])
      (use Cons.prems(1) head in simp_all)
  have tail_inv: "I (Suc k + length xs) y t"
  proof (rule Cons.IH[OF inv_next _ tail])
    fix j x' a' s' y' t'
    assume ge: "Suc k \<le> j"
      and lt: "j < Suc k + length xs"
      and x'_eq: "x' = xs ! (j - Suc k)"
      and inv: "I j a' s'"
      and out: "Some (y', t') \<in> set_dist (execute (F x' a') s')"
    have j_gt: "k < j"
      using ge by simp
    have j_lt: "j < k + length (x # xs)"
      using lt by simp
    have nth_eq: "x' = (x # xs) ! (j - k)"
      using x'_eq j_gt by simp
    show "I (Suc j) y' t'"
      by (rule Cons.prems(2)[OF _ j_lt nth_eq inv out]) (use ge in simp)
  qed
  then show ?case by simp
qed

lemma mfold_map_index_outcome_invariantI:
  assumes init: "I 0 a s"
    and step_inv:
      "\<And>j x a s y t. j < length xs \<Longrightarrow>
        x = xs ! j \<Longrightarrow> I j a s \<Longrightarrow>
        Some (y, t) \<in> set_dist (execute (F x a) s) \<Longrightarrow>
        I (Suc j) y t"
    and outcome:
      "Some (y, t) \<in> set_dist (execute (mfold a (map F xs)) s)"
  shows "I (length xs) y t"
  using mfold_map_index_outcome_invariant_fromI[
      where I=I and k=0 and xs=xs and F=F, OF init _ outcome]
    step_inv
  by simp

lemma set_dist_bindI:
  assumes "Some (x, u) \<in> set_dist (execute m s)"
    and "Some (y, t) \<in> set_dist (execute (f x) u)"
  shows "Some (y, t) \<in> set_dist (execute (m \<bind> f) s)"
proof -
  let ?K = "bind_cont_map (map_fun id dist \<circ> execute \<circ> f)"
  have x_dom: "Some (x, u) \<in> dom (dist (execute m s))"
    using assms(1) unfolding set_dist_def .
  have y_dom': "Some (y, t) \<in> dom (dist (execute (f x) u))"
    using assms(2) unfolding set_dist_def .
  have y_dom: "Some (y, t) \<in> dom (?K (Some (x, u)))"
    using assms(2)
    unfolding set_dist_def bind_cont_map_def
    by (simp add: o_def map_fun_def)
  have x_pos: "0 < the (dist (execute m s) (Some (x, u)))"
    using x_dom by simp
  have y_pos: "0 < the (dist (execute (f x) u) (Some (y, t)))"
    using y_dom' by simp
  have y_opt_pos:
    "0 < option_default (?K (Some (x, u)) (Some (y, t)))"
    using y_dom' y_pos
    by (cases "dist (execute (f x) u) (Some (y, t))")
      (auto simp: bind_cont_map_def o_def map_fun_def domIff)
  have term_pos:
    "0 <
      the (dist (execute m s) (Some (x, u))) *
      option_default (?K (Some (x, u)) (Some (y, t)))"
    using x_pos y_opt_pos by simp
  have sum_nonzero:
    "(\<Sum>i\<in>dom (dist (execute m s)).
        the (dist (execute m s) i) *
        option_default (?K i (Some (y, t)))) \<noteq> 0"
  proof -
    have "0 <
      (\<Sum>i\<in>dom (dist (execute m s)).
        the (dist (execute m s) i) *
        option_default (?K i (Some (y, t))))"
      using sum_pos2[OF finite_dom_dist x_dom, of
        "\<lambda>i. the (dist (execute m s) i) *
          option_default (?K i (Some (y, t)))"]
        term_pos
      by auto
    then show ?thesis by simp
  qed
  have "Some (y, t) \<in>
    {z \<in> (\<Union>i\<in>dom (dist (execute m s)). dom (?K i)).
      (\<Sum>i\<in>dom (dist (execute m s)).
        the (dist (execute m s) i) * option_default (?K i z)) \<noteq> 0}"
    using x_dom y_dom sum_nonzero by auto
  then show ?thesis
    unfolding set_dist_def sm_bind.rep_eq dist_bind.rep_eq
    by (simp add: o_def map_fun_def dom_map_bind)
qed

lemma set_dist_execute_throw_empty[simp]:
  "Some x \<notin> set_dist (execute throw s)"
  unfolding throw.rep_eq dist_throw_def dist_delta_dist delta_map_def set_dist_def
  by simp

lemma assert_outcomeD:
  assumes outcome: "Some ((), t) \<in> set_dist (execute (assert b) s)"
  shows "b" "t = s"
proof -
  show b
  proof (cases b)
    case True
    then show ?thesis .
  next
    case False
    then show ?thesis
      using outcome by (simp add: assert_def)
  qed
  then show "t = s"
    using outcome by (simp add: assert_def)
qed

lemma assert_hash_extends:
  assumes "Some ((), t) \<in>
    set_dist (execute (assert b) (s::('f, 'a) protocol_channel_scheme))"
  shows "s \<le> t"
  using assert_outcomeD(2)[OF assms] p.hash_ext_refl[of s] by simp

lemma modify_verifier_replay_state_outcome:
  assumes "Some (u, t) \<in>
    set_dist (execute
      (modify (\<lambda>c. c\<lparr>PState := 0, PTranscript := rev (PTranscript c),
        PTraceFriCounter := 0, PCompositionFriCounter := 0,
        PAlphaCounter := 0, PQueryCounter := 0\<rparr>)) s)"
  shows "u = () \<and> t = verifier_replay_state s"
  using assms
  unfolding verifier_replay_state_def modify_def
  by (auto elim!: p.set_dist_bindE)

lemma transcript_extends_refl[simp]:
  "transcript_extends s s"
  unfolding transcript_extends_def by simp

lemma transcript_extends_trans:
  assumes "transcript_extends u s"
    and "transcript_extends t u"
  shows "transcript_extends t s"
  using assms unfolding transcript_extends_def by auto

lemma read_hash_extends:
  assumes "Some (x, t) \<in> set_dist (execute p.read s)"
  shows "s \<le> t"
  by (rule p.read_hash_extends[OF assms])

lemma ntimes_read_hash_extends:
  assumes "Some (xs, t) \<in> set_dist (execute (ntimes p.read n) s)"
  shows "s \<le> t"
  using assms
proof (induction n arbitrary: xs s t)
  case 0
  then show ?case
    by (simp add: p.hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain x ys u where
    read: "Some (x, u) \<in> set_dist (execute p.read s)"
    and reads:
      "Some (ys, t) \<in> set_dist (execute (ntimes p.read n) u)"
    by (auto elim!: p.set_dist_bindE)
  have "s \<le> u"
    using read by (rule read_hash_extends)
  moreover have "u \<le> t"
    using reads by (rule Suc.IH)
  ultimately show ?case
    by (rule p.hash_ext_trans)
qed

lemma check_authentication_path_hash_extends:
  assumes outcome:
    "Some (h, t) \<in>
      set_dist (execute (p.check_authentication_path len i v path) s)"
  shows "s \<le> t"
  by (rule p.check_authentication_path_hash_extends[OF outcome])

lemma honest_trace_valid_raw_algebra:
  assumes "honest_trace_valid"
  shows
    "\<forall>(c, roots, d) \<in> set spec.
      (\<forall>r \<in> set (p.g_map roots). poly (c p.f_powers) r = 0) \<and>
      degree (c p.f_powers) \<le> d * (clength - 1) \<and>
      distinct (p.g_map roots)"
  using assms
  unfolding honest_trace_valid_def honest_trace_algebra_def
    constraint_roots_vanish_def
  using constraint_degree_bound p.g_map_distinct
  by force

lemma honest_trace_valid_algebra:
  assumes "honest_trace_valid"
  shows "honest_trace_algebra"
  using assms unfolding honest_trace_valid_def by simp

lemma straight_line_honest_transcript_replay:
  assumes "PTranscript s = []"
    and "Some ((), sent) \<in> set_dist (execute (mfold2 p.send xs) s)"
    and "Some (ys, replayed) \<in>
      set_dist (execute
        (ntimes p.read (length xs))
        (sent\<lparr>PState := PState s, PTranscript := rev (PTranscript sent)\<rparr>))"
  shows "ys = xs \<and> replayed = sent\<lparr>PTranscript := []\<rparr>"
  using p.honest_transcript_replay_mfold2_ntimes[OF assms] .

lemma honest_alpha_round_replay_no_failure:
  assumes lookup: "fmlookup (HashMap s) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
  shows
    "None \<notin> dom (dist (execute
      (do {
        a0 \<leftarrow> p.receive_alpha_challenge;
        let a0' = a0;
        a1 \<leftarrow> p.read;
        let a1' = a1;
        assert (a0' = a1');
        return a1'
      }) (s\<lparr>PTranscript := a # rest\<rparr>)))"
proof -
  let ?start = "s\<lparr>PTranscript := a # rest\<rparr>"
  let ?prefix =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      a1 \<leftarrow> p.read;
      return (a0, a1)
    }"
  have lookup_start:
    "fmlookup (HashMap ?start) (AlphaChallenge (PAlphaCounter ?start) (PState ?start)) = Some a"
    using lookup by simp
  have prefix_no_failure:
    "None \<notin> dom (dist (execute ?prefix ?start))"
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute p.receive_alpha_challenge ?start))"
      by (rule p.receive_alpha_challenge_no_failure)
  next
    fix a0 t
    assume rand: "Some (a0, t) \<in> set_dist (execute p.receive_alpha_challenge ?start)"
    have tr_t: "PTranscript t = a # rest"
      using p.receive_alpha_challenge_known_outcome[OF lookup_start rand] by simp
    show "None \<notin> dom (dist (execute (p.read \<bind> (\<lambda>a1. return (a0, a1))) t))"
    proof (rule no_failure_bindI)
      show "None \<notin> dom (dist (execute p.read t))"
        by (rule p.read_no_failure) (simp add: tr_t)
    next
      fix a1 u
      assume "Some (a1, u) \<in> set_dist (execute p.read t)"
      show "None \<notin> dom (dist (execute (return (a0, a1)) u))"
        by simp
    qed
  qed
  have full:
    "(do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }) =
    (?prefix \<bind> (\<lambda>(a0, a1). assert (a0 = a1) \<bind> (\<lambda>_. return a1)))"
    by (simp add: Let_def sm_bind_assoc split: prod.splits)
  show ?thesis
    unfolding full
  proof (rule no_failure_bindI[OF prefix_no_failure])
    fix aa t
    assume prefix: "Some (aa, t) \<in> set_dist (execute ?prefix ?start)"
    obtain a0 a1 where aa_eq: "aa = (a0, a1)"
      by (cases aa)
    from prefix[unfolded aa_eq] obtain r_state where
      rand:
        "Some (a0, r_state) \<in> set_dist (execute p.receive_alpha_challenge ?start)"
      and read:
        "Some (a1, t) \<in> set_dist (execute p.read r_state)"
      by (auto elim!: p.set_dist_bindE)
    have rand_res:
      "a0 = a \<and> PState r_state = PState s \<and> PTranscript r_state = a # rest"
      using p.receive_alpha_challenge_known_outcome[OF lookup_start rand] by simp
    have read_start:
      "r_state = r_state\<lparr>PTranscript := a # rest\<rparr>"
      using rand_res by simp
    have read':
      "Some (a1, t) \<in> set_dist (execute p.read (r_state\<lparr>PTranscript := a # rest\<rparr>))"
      by (subst read_start[symmetric]) (rule read)
    have "a1 = a"
      using p.read_cons_outcome[OF read'] rand_res by simp
    then show "None \<notin> dom
      (dist (execute ((case aa of (a0, a1) \<Rightarrow> assert (a0 = a1) \<bind> (\<lambda>_. return a1))) t))"
      using rand_res unfolding aa_eq assert_def by simp
  qed
qed

lemma honest_alpha_round_replay_outcome:
  assumes lookup: "fmlookup (HashMap s) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    and outcome:
      "Some (y, t) \<in> set_dist (execute
        (do {
          a0 \<leftarrow> p.receive_alpha_challenge;
          let a0' = a0;
          a1 \<leftarrow> p.read;
          let a1' = a1;
          assert (a0' = a1');
          return a1'
        }) (s\<lparr>PTranscript := a # rest\<rparr>))"
  shows
    "y = a \<and>
     PState t = concat (PState s) a \<and>
     PTranscript t = rest \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = Suc (PAlphaCounter s) \<and>
     PQueryCounter t = PQueryCounter s \<and>
     s \<le> t"
proof -
  let ?start = "s\<lparr>PTranscript := a # rest\<rparr>"
  from outcome obtain a0 r_state read_state where
    rand:
      "Some (a0, r_state) \<in> set_dist (execute p.receive_alpha_challenge ?start)"
    and read:
      "Some (y, read_state) \<in> set_dist (execute p.read r_state)"
    and assert_ok: "Some ((), t) \<in> set_dist (execute (assert (a0 = y)) read_state)"
    by (auto simp: Let_def elim!: p.set_dist_bindE)
  have lookup_start: "fmlookup (HashMap ?start) (AlphaChallenge (PAlphaCounter ?start) (PState ?start)) = Some a"
    using lookup by simp
  have rand_known:
    "a0 = a \<and>
     PState r_state = PState s \<and>
     PTranscript r_state = a # rest \<and>
     ?start \<le> r_state"
    using p.receive_alpha_challenge_known_outcome[OF lookup_start rand] by simp
  have read_start:
    "r_state = r_state\<lparr>PTranscript := a # rest\<rparr>"
    using rand_known by simp
  have read':
    "Some (y, read_state) \<in>
      set_dist (execute p.read (r_state\<lparr>PTranscript := a # rest\<rparr>))"
    by (subst read_start[symmetric]) (rule read)
  have read_res:
    "y = a \<and>
     read_state =
       r_state\<lparr>PState := concat (PState r_state) a, PTranscript := rest\<rparr>"
    using p.read_cons_outcome[OF read'] by simp
  have t_eq: "t = read_state"
    using assert_ok rand_known read_res
    unfolding assert_def by simp
  have alpha_counter:
    "PAlphaCounter t = Suc (PAlphaCounter s)"
    using p.receive_alpha_challenge_counter_outcome[OF rand] rand_known read_res
    unfolding t_eq by simp
  have other_counters:
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PQueryCounter t = PQueryCounter s"
    using p.receive_alpha_challenge_counter_outcome[OF rand] rand_known read_res
    unfolding t_eq by simp
  have s_t: "s \<le> t"
  proof -
    have s_start: "s \<le> ?start"
      unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    have start_r: "?start \<le> r_state"
      using rand_known by simp
    have r_read: "r_state \<le> read_state"
      using read_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    show ?thesis
      using s_start start_r r_read unfolding t_eq
      by (meson p.hash_ext_trans)
  qed
  show ?thesis
    using rand_known read_res t_eq alpha_counter other_counters s_t by simp
qed

lemma honest_alpha_round_replay_parts_outcome:
  assumes lookup: "fmlookup (HashMap s) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    and rand:
      "Some (a0, r_state) \<in>
        set_dist (execute p.receive_alpha_challenge (s\<lparr>PTranscript := a # rest\<rparr>))"
    and read:
      "Some (y, read_state) \<in> set_dist (execute p.read r_state)"
    and assert_ok:
      "Some ((), t) \<in> set_dist (execute (assert (a0 = y)) read_state)"
  shows
    "y = a \<and>
     PState t = concat (PState s) a \<and>
     PTranscript t = rest \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = Suc (PAlphaCounter s) \<and>
     PQueryCounter t = PQueryCounter s \<and>
     s \<le> t"
proof -
  let ?start = "s\<lparr>PTranscript := a # rest\<rparr>"
  have lookup_start: "fmlookup (HashMap ?start) (AlphaChallenge (PAlphaCounter ?start) (PState ?start)) = Some a"
    using lookup by simp
  have rand_known:
    "a0 = a \<and>
     PState r_state = PState s \<and>
     PTranscript r_state = a # rest \<and>
     ?start \<le> r_state"
    using p.receive_alpha_challenge_known_outcome[OF lookup_start rand] by simp
  have read_start:
    "r_state = r_state\<lparr>PTranscript := a # rest\<rparr>"
    using rand_known by simp
  have read':
    "Some (y, read_state) \<in>
      set_dist (execute p.read (r_state\<lparr>PTranscript := a # rest\<rparr>))"
    by (subst read_start[symmetric]) (rule read)
  have read_res:
    "y = a \<and>
     read_state =
       r_state\<lparr>PState := concat (PState r_state) a, PTranscript := rest\<rparr>"
    using p.read_cons_outcome[OF read'] by simp
  have t_eq: "t = read_state"
    using assert_ok rand_known read_res
    unfolding assert_def by simp
  have alpha_counter:
    "PAlphaCounter t = Suc (PAlphaCounter s)"
    using p.receive_alpha_challenge_counter_outcome[OF rand] rand_known read_res
    unfolding t_eq by simp
  have other_counters:
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PQueryCounter t = PQueryCounter s"
    using p.receive_alpha_challenge_counter_outcome[OF rand] rand_known read_res
    unfolding t_eq by simp
  have s_t: "s \<le> t"
  proof -
    have s_start: "s \<le> ?start"
      unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    have start_r: "?start \<le> r_state"
      using rand_known by simp
    have r_read: "r_state \<le> read_state"
      using read_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    show ?thesis
      using s_start start_r r_read unfolding t_eq
      by (meson p.hash_ext_trans)
  qed
  show ?thesis
    using rand_known read_res t_eq alpha_counter other_counters s_t by simp
qed

lemma honest_receive_fri_commit_replay_outcome:
  assumes lookup: "fmlookup (HashMap s) (FiatShamirChallenge (concat (PState s) fri_root)) = Some challenge"
    and outcome:
      "Some ((b, r), t) \<in>
        set_dist (execute v.receive_fri_commits (s\<lparr>PTranscript := fri_root # rest\<rparr>))"
  shows
    "r = fri_root \<and>
     b = challenge \<and>
     PState t = concat (PState s) fri_root \<and>
     PTranscript t = rest \<and>
     s \<le> t"
proof -
  from outcome obtain u where
    read_root: "Some (r, u) \<in> set_dist (execute p.read (s\<lparr>PTranscript := fri_root # rest\<rparr>))"
    and rand: "Some (b, t) \<in> set_dist (execute p.receive_random_field_element u)"
    unfolding v.receive_fri_commits_def
    by (auto elim!: p.set_dist_bindE)
  have read_res:
    "r = fri_root \<and>
     u = s\<lparr>PState := concat (PState s) fri_root, PTranscript := rest\<rparr>"
    using p.read_cons_outcome[OF read_root] by simp
  have lookup_u: "fmlookup (HashMap u) (FiatShamirChallenge (PState u)) = Some challenge"
    using lookup read_res by simp
  have rand_res:
    "b = challenge \<and> PState t = concat (PState s) fri_root \<and> PTranscript t = rest \<and> u \<le> t"
    using p.receive_random_field_element_known_outcome[OF lookup_u rand] read_res by simp
  have s_u: "s \<le> u"
    using read_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s_t: "s \<le> t"
    using s_u rand_res by (meson p.hash_ext_trans)
  show ?thesis
    using read_res rand_res s_t by simp
qed

lemma honest_receive_fri_commit_no_failure:
  assumes "PTranscript s \<noteq> []"
  shows
  "None \<notin> dom (dist (execute v.receive_fri_commits s))"
  using assms
  unfolding v.receive_fri_commits_def
  by (intro no_failure_bindI) (simp_all add: p.read_no_failure p.receive_random_field_element_no_failure)

lemma receive_fri_commit_preserves_query_counter:
  assumes outcome:
    "Some (br, t) \<in> set_dist (execute v.receive_fri_commits s)"
  shows "PQueryCounter t = PQueryCounter s"
proof -
	  from outcome obtain r u b where
	    read_root: "Some (r, u) \<in> set_dist (execute p.read s)"
	    and rand: "Some (b, t) \<in> set_dist (execute p.receive_random_field_element u)"
	    unfolding v.receive_fri_commits_def
	    by (auto elim!: p.set_dist_bindE)
	  have q_read: "PQueryCounter u = PQueryCounter s"
	  proof (cases "PTranscript s")
	    case Nil
	    then have False
	      using read_root
	      unfolding p.read_def protocol_read_def assert_def
	      by (auto elim!: p.set_dist_bindE)
	    then show ?thesis by simp
	  next
	    case (Cons x xs)
	    then show ?thesis
	      using p.read_nonempty_outcome[OF read_root Cons] by simp
	  qed
  have q_rand: "PQueryCounter t = PQueryCounter u"
    using p.receive_random_field_element_counter_outcome[OF rand] by simp
  show ?thesis
    using q_read q_rand by simp
qed

lemma receive_fri_commits_preserves_query_counter:
  assumes outcome:
    "Some (brs, t) \<in> set_dist (execute (ntimes v.receive_fri_commits n) s)"
  shows "PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction n arbitrary: brs s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain br u brs' where
    head: "Some (br, u) \<in> set_dist (execute v.receive_fri_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes v.receive_fri_commits n) u)"
    by (auto elim!: p.set_dist_bindE)
  have q_head: "PQueryCounter u = PQueryCounter s"
    by (rule receive_fri_commit_preserves_query_counter[OF head])
  have q_tail: "PQueryCounter t = PQueryCounter u"
    by (rule Suc.IH[OF tail])
  show ?case
    using q_head q_tail by simp
qed

lemma honest_receive_fri_commits_list_outcome:
  assumes lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap s) (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i)"
    and len: "length challenges = length roots"
    and outcome:
      "Some (brs, t) \<in>
        set_dist (execute (ntimes v.receive_fri_commits (length roots))
          (s\<lparr>PTranscript := roots @ rest\<rparr>))"
  shows
    "brs = zip challenges roots \<and>
     PState t = foldl concat (PState s) roots \<and>
     PTranscript t = rest \<and>
     s \<le> t"
  using lookups len outcome
proof (induction roots arbitrary: challenges brs s t rest)
  case Nil
  have brs_eq: "brs = []"
    using Nil.prems(3) by simp
  have t_eq: "t = s\<lparr>PTranscript := rest\<rparr>"
    using Nil.prems(3) by simp
  have s_t: "s \<le> t"
    unfolding t_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  show ?case
    using brs_eq t_eq s_t Nil.prems(2) by simp
next
  case (Cons root roots)
  from Cons.prems(2) obtain challenge challenges' where challenges_eq:
    "challenges = challenge # challenges'"
    by (cases challenges) auto
  from Cons.prems(3) obtain br u brs' where
    head:
      "Some (br, u) \<in>
        set_dist (execute v.receive_fri_commits
          (s\<lparr>PTranscript := root # (roots @ rest)\<rparr>))"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes v.receive_fri_commits (length roots)) u)"
    and brs_eq: "brs = br # brs'"
    by (auto elim!: p.set_dist_bindE)
  have lookup_root:
    "fmlookup (HashMap s) (FiatShamirChallenge (concat (PState s) root)) = Some challenge"
    using spec[OF Cons.prems(1), of 0] challenges_eq by simp
  obtain b r where br_eq: "br = (b, r)"
    by (cases br)
  have head_out:
    "r = root \<and>
     b = challenge \<and>
     PState u = concat (PState s) root \<and>
     PTranscript u = roots @ rest \<and>
     s \<le> u"
    using honest_receive_fri_commit_replay_outcome[
      OF lookup_root head[unfolded br_eq]]
    unfolding br_eq by simp
  have tail_lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap u) (FiatShamirChallenge (foldl concat (PState u) (take (Suc i) roots))) =
        Some (challenges' ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length roots"
    have old_lookup:
      "fmlookup (HashMap s)
        (FiatShamirChallenge (foldl concat (PState s) (take (Suc (Suc i)) (root # roots)))) =
        Some ((challenge # challenges') ! Suc i)"
      using spec[OF Cons.prems(1), of "Suc i"] i_bound challenges_eq by simp
    have key_eq:
      "foldl concat (PState s) (take (Suc (Suc i)) (root # roots)) =
        foldl concat (PState u) (take (Suc i) roots)"
      using head_out by simp
    show "fmlookup (HashMap u) (FiatShamirChallenge (foldl concat (PState u) (take (Suc i) roots))) =
      Some (challenges' ! i)"
      using p.hash_extension_lookup[OF old_lookup, of u] head_out key_eq i_bound
      by simp
  qed
  have u_update: "u\<lparr>PTranscript := roots @ rest\<rparr> = u"
    using head_out by simp
  have tail':
    "Some (brs', t) \<in>
      set_dist (execute (ntimes v.receive_fri_commits (length roots))
        (u\<lparr>PTranscript := roots @ rest\<rparr>))"
    using tail unfolding u_update .
  have tail_len: "length challenges' = length roots"
    using Cons.prems(2) challenges_eq by simp
  have tail_out:
    "brs' = zip challenges' roots \<and>
     PState t = foldl concat (PState u) roots \<and>
     PTranscript t = rest \<and>
     u \<le> t"
    using Cons.IH[OF tail_lookups tail_len tail'] .
  have s_t: "s \<le> t"
    using head_out tail_out by (meson p.hash_ext_trans)
  show ?case
    using brs_eq br_eq head_out tail_out s_t challenges_eq by simp
qed

lemma honest_receive_fri_commits_list_no_failure:
  assumes lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap s) (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i)"
    and len: "length challenges = length roots"
  shows
    "None \<notin> dom (dist (execute
      (ntimes v.receive_fri_commits (length roots))
      (s\<lparr>PTranscript := roots @ rest\<rparr>)))"
  using lookups len
proof (induction roots arbitrary: challenges s rest)
  case Nil
  then show ?case by simp
next
  case (Cons root roots)
  from Cons.prems(2) obtain challenge challenges' where challenges_eq:
    "challenges = challenge # challenges'"
    by (cases challenges) auto
  have lookup_root:
    "fmlookup (HashMap s) (FiatShamirChallenge (concat (PState s) root)) = Some challenge"
    using spec[OF Cons.prems(1), of 0] challenges_eq by simp
  have head_nf:
    "None \<notin> dom (dist (execute v.receive_fri_commits
      (s\<lparr>PTranscript := root # (roots @ rest)\<rparr>)))"
    by (rule honest_receive_fri_commit_no_failure) simp
  have case_eq:
    "?case =
      (None \<notin> dom (dist (execute
        (v.receive_fri_commits \<bind>
          (\<lambda>br. ntimes v.receive_fri_commits (length roots) \<bind>
            (\<lambda>brs. return (br # brs))))
        (s\<lparr>PTranscript := root # (roots @ rest)\<rparr>))))"
    by simp
  show ?case
    unfolding case_eq
  proof (rule no_failure_bindI[OF head_nf])
    fix br u
    assume head:
      "Some (br, u) \<in>
        set_dist (execute v.receive_fri_commits
          (s\<lparr>PTranscript := root # roots @ rest\<rparr>))"
    obtain b r where br_eq: "br = (b, r)"
      by (cases br)
    have head_out:
      "r = root \<and>
       b = challenge \<and>
       PState u = concat (PState s) root \<and>
       PTranscript u = roots @ rest \<and>
       s \<le> u"
      using honest_receive_fri_commit_replay_outcome[
        OF lookup_root head[unfolded br_eq]]
      unfolding br_eq by simp
    have tail_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap u) (FiatShamirChallenge (foldl concat (PState u) (take (Suc i) roots))) =
          Some (challenges' ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < length roots"
      have old_lookup:
        "fmlookup (HashMap s)
          (FiatShamirChallenge (foldl concat (PState s) (take (Suc (Suc i)) (root # roots)))) =
          Some ((challenge # challenges') ! Suc i)"
        using spec[OF Cons.prems(1), of "Suc i"] i_bound challenges_eq by simp
      have key_eq:
        "foldl concat (PState s) (take (Suc (Suc i)) (root # roots)) =
          foldl concat (PState u) (take (Suc i) roots)"
        using head_out by simp
      show "fmlookup (HashMap u) (FiatShamirChallenge (foldl concat (PState u) (take (Suc i) roots))) =
        Some (challenges' ! i)"
        using p.hash_extension_lookup[OF old_lookup, of u] head_out key_eq i_bound
        by simp
    qed
    have tail_len: "length challenges' = length roots"
      using Cons.prems(2) challenges_eq by simp
    have tail_nf_start:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_fri_commits (length roots))
        (u\<lparr>PTranscript := roots @ rest\<rparr>)))"
      using Cons.IH[OF tail_lookups tail_len, of rest] .
    have u_update: "u\<lparr>PTranscript := roots @ rest\<rparr> = u"
      using head_out by simp
    have tail_nf:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_fri_commits (length roots)) u))"
      using tail_nf_start unfolding u_update .
    show "None \<notin> dom (dist (execute
      (ntimes v.receive_fri_commits (length roots) \<bind>
        (\<lambda>brs. return (br # brs))) u))"
      by (rule no_failure_bindI[OF tail_nf]) simp
  qed
qed

lemma honest_receive_fri_commit_with_no_failure:
  assumes receiver_nf:
    "\<And>s. None \<notin> dom (dist (execute receive_challenge s))"
    and tr: "PTranscript s \<noteq> []"
  shows
    "None \<notin> dom (dist
      (execute (v.receive_fri_commits_with receive_challenge) s))"
  using tr
  unfolding v.receive_fri_commits_with_def
  by (intro no_failure_bindI)
    (simp_all add: p.read_no_failure receiver_nf)

lemma honest_receive_trace_fri_commit_replay_outcome:
  assumes lookup:
      "fmlookup (HashMap s)
        (TraceFriChallenge (PTraceFriCounter s)
          (concat (PState s) fri_root)) = Some challenge"
    and outcome:
      "Some ((b, r), t) \<in>
        set_dist (execute
          v.receive_trace_fri_commits
          (s\<lparr>PTranscript := fri_root # rest\<rparr>))"
  shows
    "r = fri_root \<and>
     b = challenge \<and>
     PState t = concat (PState s) fri_root \<and>
     PTranscript t = rest \<and>
     PTraceFriCounter t = Suc (PTraceFriCounter s) \<and>
     s \<le> t"
proof -
  from outcome obtain u where
    read_root:
      "Some (r, u) \<in>
        set_dist (execute p.read
          (s\<lparr>PTranscript := fri_root # rest\<rparr>))"
    and rand:
      "Some (b, t) \<in> set_dist (execute p.receive_trace_fri_challenge u)"
    unfolding v.receive_trace_fri_commits_def v.receive_fri_commits_with_def
    by (auto elim!: p.set_dist_bindE)
  have read_res:
    "r = fri_root \<and>
     u = s\<lparr>PState := concat (PState s) fri_root, PTranscript := rest\<rparr>"
    using p.read_cons_outcome[OF read_root] by simp
  have lookup_u:
    "fmlookup (HashMap u) (TraceFriChallenge (PTraceFriCounter u) (PState u)) = Some challenge"
    using lookup read_res by simp
  have rand_res:
    "b = challenge \<and> PState t = concat (PState s) fri_root \<and>
     PTranscript t = rest \<and> u \<le> t"
    using p.receive_trace_fri_challenge_known_outcome[OF lookup_u rand]
      read_res by simp
  have rand_counter:
    "PTraceFriCounter t = Suc (PTraceFriCounter s)"
    using p.receive_trace_fri_challenge_counter_outcome[OF rand] read_res
    by simp
  have s_u: "s \<le> u"
    using read_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s_t: "s \<le> t"
    using s_u rand_res by (meson p.hash_ext_trans)
  show ?thesis
    using read_res rand_res rand_counter s_t by simp
qed

lemma honest_receive_composition_fri_commit_replay_outcome:
  assumes lookup:
      "fmlookup (HashMap s)
        (CompositionFriChallenge (PCompositionFriCounter s)
          (concat (PState s) fri_root)) =
        Some challenge"
    and outcome:
      "Some ((b, r), t) \<in>
        set_dist (execute
          v.receive_composition_fri_commits
          (s\<lparr>PTranscript := fri_root # rest\<rparr>))"
  shows
    "r = fri_root \<and>
     b = challenge \<and>
     PState t = concat (PState s) fri_root \<and>
     PTranscript t = rest \<and>
     PCompositionFriCounter t = Suc (PCompositionFriCounter s) \<and>
     s \<le> t"
proof -
  from outcome obtain u where
    read_root:
      "Some (r, u) \<in>
        set_dist (execute p.read
          (s\<lparr>PTranscript := fri_root # rest\<rparr>))"
    and rand:
      "Some (b, t) \<in>
        set_dist (execute p.receive_composition_fri_challenge u)"
    unfolding v.receive_composition_fri_commits_def
      v.receive_fri_commits_with_def
    by (auto elim!: p.set_dist_bindE)
  have read_res:
    "r = fri_root \<and>
     u = s\<lparr>PState := concat (PState s) fri_root, PTranscript := rest\<rparr>"
    using p.read_cons_outcome[OF read_root] by simp
  have lookup_u:
    "fmlookup (HashMap u) (CompositionFriChallenge (PCompositionFriCounter u) (PState u)) =
      Some challenge"
    using lookup read_res by simp
  have rand_res:
    "b = challenge \<and> PState t = concat (PState s) fri_root \<and>
     PTranscript t = rest \<and> u \<le> t"
    using p.receive_composition_fri_challenge_known_outcome[OF lookup_u rand]
      read_res by simp
  have rand_counter:
    "PCompositionFriCounter t = Suc (PCompositionFriCounter s)"
    using p.receive_composition_fri_challenge_counter_outcome[OF rand] read_res
    by simp
  have s_u: "s \<le> u"
    using read_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s_t: "s \<le> t"
    using s_u rand_res by (meson p.hash_ext_trans)
  show ?thesis
    using read_res rand_res rand_counter s_t by simp
qed

lemma read_preserves_counters:
  assumes outcome: "Some (r, t) \<in> set_dist (execute p.read s)"
  shows
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
proof (cases "PTranscript s")
  case Nil
  then have False
    using outcome
    unfolding p.read_def protocol_read_def assert_def
    by (auto elim!: p.set_dist_bindE)
  then show ?thesis by simp
next
  case (Cons x xs)
	  then show ?thesis
	    using p.read_nonempty_outcome[OF outcome Cons] by simp
	qed

lemma ntimes_read_preserves_query_counter:
  assumes outcome: "Some (xs, t) \<in> set_dist (execute (ntimes p.read n) s)"
  shows "PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction n arbitrary: xs s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain x u xs' where
    head: "Some (x, u) \<in> set_dist (execute p.read s)"
    and tail: "Some (xs', t) \<in> set_dist (execute (ntimes p.read n) u)"
    by (auto elim!: p.set_dist_bindE)
  have q_head: "PQueryCounter u = PQueryCounter s"
    using read_preserves_counters[OF head] by simp
  have q_tail: "PQueryCounter t = PQueryCounter u"
    by (rule Suc.IH[OF tail])
  show ?case
    using q_head q_tail by simp
qed

lemma receive_trace_fri_commit_preserves_other_counters:
  assumes outcome:
    "Some (br, t) \<in> set_dist (execute v.receive_trace_fri_commits s)"
  shows
    "PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  from outcome obtain r u b where
    read_root: "Some (r, u) \<in> set_dist (execute p.read s)"
    and rand: "Some (b, t) \<in> set_dist (execute p.receive_trace_fri_challenge u)"
    unfolding v.receive_trace_fri_commits_def v.receive_fri_commits_with_def
    by (auto elim!: p.set_dist_bindE)
  have read_res:
    "PCompositionFriCounter u = PCompositionFriCounter s \<and>
     PAlphaCounter u = PAlphaCounter s \<and>
     PQueryCounter u = PQueryCounter s"
    using read_preserves_counters[OF read_root] by simp
  show ?thesis
    using p.receive_trace_fri_challenge_counter_outcome[OF rand] read_res
    by simp
qed

lemma receive_composition_fri_commit_preserves_other_counters:
  assumes outcome:
    "Some (br, t) \<in> set_dist (execute v.receive_composition_fri_commits s)"
  shows
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  from outcome obtain r u b where
    read_root: "Some (r, u) \<in> set_dist (execute p.read s)"
    and rand:
      "Some (b, t) \<in> set_dist (execute p.receive_composition_fri_challenge u)"
    unfolding v.receive_composition_fri_commits_def
      v.receive_fri_commits_with_def
    by (auto elim!: p.set_dist_bindE)
  have read_res:
    "PTraceFriCounter u = PTraceFriCounter s \<and>
     PAlphaCounter u = PAlphaCounter s \<and>
     PQueryCounter u = PQueryCounter s"
    using read_preserves_counters[OF read_root] by simp
  show ?thesis
    using p.receive_composition_fri_challenge_counter_outcome[OF rand]
      read_res
    by simp
qed

lemma receive_trace_fri_commits_preserves_other_counters:
  assumes outcome:
    "Some (brs, t) \<in>
      set_dist (execute (ntimes v.receive_trace_fri_commits n) s)"
  shows
    "PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction n arbitrary: brs s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain br u brs' where
    head: "Some (br, u) \<in> set_dist (execute v.receive_trace_fri_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes v.receive_trace_fri_commits n) u)"
    by (auto elim!: p.set_dist_bindE)
  have head_pres:
    "PCompositionFriCounter u = PCompositionFriCounter s \<and>
     PAlphaCounter u = PAlphaCounter s \<and>
     PQueryCounter u = PQueryCounter s"
    using receive_trace_fri_commit_preserves_other_counters[OF head] .
  have tail_pres:
    "PCompositionFriCounter t = PCompositionFriCounter u \<and>
     PAlphaCounter t = PAlphaCounter u \<and>
     PQueryCounter t = PQueryCounter u"
    using Suc.IH[OF tail] .
  show ?case
    using head_pres tail_pres by simp
qed

lemma receive_composition_fri_commits_preserves_other_counters:
  assumes outcome:
    "Some (brs, t) \<in>
      set_dist (execute (ntimes v.receive_composition_fri_commits n) s)"
  shows
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction n arbitrary: brs s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain br u brs' where
    head:
      "Some (br, u) \<in>
        set_dist (execute v.receive_composition_fri_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes v.receive_composition_fri_commits n) u)"
    by (auto elim!: p.set_dist_bindE)
  have head_pres:
    "PTraceFriCounter u = PTraceFriCounter s \<and>
     PAlphaCounter u = PAlphaCounter s \<and>
     PQueryCounter u = PQueryCounter s"
    using receive_composition_fri_commit_preserves_other_counters[OF head] .
  have tail_pres:
    "PTraceFriCounter t = PTraceFriCounter u \<and>
     PAlphaCounter t = PAlphaCounter u \<and>
     PQueryCounter t = PQueryCounter u"
    using Suc.IH[OF tail] .
  show ?case
    using head_pres tail_pres by simp
qed

lemma honest_receive_fri_commits_list_outcome_with:
  fixes counter :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat"
    and tag :: "nat \<Rightarrow> 'f \<Rightarrow> 'f protocol_hash_input"
  assumes step:
      "\<And>s root rest challenge b r t.
        fmlookup (HashMap s) (tag (counter s) (concat (PState s) root)) =
          Some challenge \<Longrightarrow>
        Some ((b, r), t) \<in>
          set_dist (execute receive_commits
            (s\<lparr>PTranscript := root # rest\<rparr>)) \<Longrightarrow>
        r = root \<and>
        b = challenge \<and>
        PState t = concat (PState s) root \<and>
        PTranscript t = rest \<and>
        counter t = Suc (counter s) \<and>
        s \<le> t"
    and counter_update:
      "\<And>s tr. counter (s\<lparr>PTranscript := tr\<rparr>) = counter s"
    and lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap s)
          (tag (counter s + i)
            (foldl concat (PState s) (take (Suc i) roots))) =
          Some (challenges ! i)"
    and len: "length challenges = length roots"
    and outcome:
      "Some (brs, t) \<in>
        set_dist (execute (ntimes receive_commits (length roots))
          (s\<lparr>PTranscript := roots @ rest\<rparr>))"
  shows
    "brs = zip challenges roots \<and>
     PState t = foldl concat (PState s) roots \<and>
     PTranscript t = rest \<and>
     counter t = counter s + length roots \<and>
     s \<le> t"
  using lookups len outcome
proof (induction roots arbitrary: challenges brs s t rest)
  case Nil
  have brs_eq: "brs = []"
    using Nil.prems(3) by simp
  have t_eq: "t = s\<lparr>PTranscript := rest\<rparr>"
    using Nil.prems(3) by simp
  have s_t: "s \<le> t"
    unfolding t_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have counter_t: "counter t = counter s"
    using t_eq counter_update by simp
  show ?case
    using brs_eq t_eq s_t counter_t Nil.prems(2) by simp
next
  case (Cons root roots)
  from Cons.prems(2) obtain challenge challenges' where challenges_eq:
    "challenges = challenge # challenges'"
    by (cases challenges) auto
  from Cons.prems(3) obtain br u brs' where
    head:
      "Some (br, u) \<in>
        set_dist (execute receive_commits
          (s\<lparr>PTranscript := root # (roots @ rest)\<rparr>))"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes receive_commits (length roots)) u)"
    and brs_eq: "brs = br # brs'"
    by (auto elim!: p.set_dist_bindE)
  have lookup_root:
    "fmlookup (HashMap s)
      (tag (counter s) (concat (PState s) root)) = Some challenge"
    using spec[OF Cons.prems(1), of 0] challenges_eq by simp
  obtain b r where br_eq: "br = (b, r)"
    by (cases br)
  have head_out:
    "r = root \<and>
     b = challenge \<and>
     PState u = concat (PState s) root \<and>
     PTranscript u = roots @ rest \<and>
     counter u = Suc (counter s) \<and>
     s \<le> u"
    using step[OF lookup_root head[unfolded br_eq]]
    unfolding br_eq by simp
  have tail_lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap u)
        (tag (counter u + i)
          (foldl concat (PState u) (take (Suc i) roots))) =
        Some (challenges' ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length roots"
    have old_lookup:
      "fmlookup (HashMap s)
        (tag (counter s + Suc i)
          (foldl concat (PState s) (take (Suc (Suc i)) (root # roots)))) =
        Some ((challenge # challenges') ! Suc i)"
      using spec[OF Cons.prems(1), of "Suc i"] i_bound challenges_eq by simp
    have key_eq:
      "foldl concat (PState s) (take (Suc (Suc i)) (root # roots)) =
        foldl concat (PState u) (take (Suc i) roots)"
      using head_out by simp
    show "fmlookup (HashMap u)
        (tag (counter u + i)
          (foldl concat (PState u) (take (Suc i) roots))) =
      Some (challenges' ! i)"
      using p.hash_extension_lookup[OF old_lookup, of u] head_out key_eq i_bound
      by simp
  qed
  have u_update: "u\<lparr>PTranscript := roots @ rest\<rparr> = u"
    using head_out by simp
  have tail':
    "Some (brs', t) \<in>
      set_dist (execute (ntimes receive_commits (length roots))
        (u\<lparr>PTranscript := roots @ rest\<rparr>))"
    using tail unfolding u_update .
  have tail_len: "length challenges' = length roots"
    using Cons.prems(2) challenges_eq by simp
  have tail_out:
    "brs' = zip challenges' roots \<and>
     PState t = foldl concat (PState u) roots \<and>
     PTranscript t = rest \<and>
     counter t = counter u + length roots \<and>
     u \<le> t"
    using Cons.IH[OF tail_lookups tail_len tail'] .
  have s_t: "s \<le> t"
    using head_out tail_out by (meson p.hash_ext_trans)
  show ?case
    using brs_eq br_eq head_out tail_out s_t challenges_eq by simp
qed

lemma honest_receive_fri_commits_list_no_failure_with:
  fixes counter :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat"
    and tag :: "nat \<Rightarrow> 'f \<Rightarrow> 'f protocol_hash_input"
  assumes step:
      "\<And>s root rest challenge b r t.
        fmlookup (HashMap s) (tag (counter s) (concat (PState s) root)) =
          Some challenge \<Longrightarrow>
        Some ((b, r), t) \<in>
          set_dist (execute receive_commits
            (s\<lparr>PTranscript := root # rest\<rparr>)) \<Longrightarrow>
        r = root \<and>
        b = challenge \<and>
        PState t = concat (PState s) root \<and>
        PTranscript t = rest \<and>
        counter t = Suc (counter s) \<and>
        s \<le> t"
    and step_nf:
      "\<And>s. PTranscript s \<noteq> [] \<Longrightarrow>
        None \<notin> dom (dist (execute receive_commits s))"
    and lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap s)
          (tag (counter s + i)
            (foldl concat (PState s) (take (Suc i) roots))) =
          Some (challenges ! i)"
    and len: "length challenges = length roots"
  shows
    "None \<notin> dom (dist (execute
      (ntimes receive_commits (length roots))
      (s\<lparr>PTranscript := roots @ rest\<rparr>)))"
  using lookups len
proof (induction roots arbitrary: challenges s rest)
  case Nil
  then show ?case by simp
next
  case (Cons root roots)
  from Cons.prems(2) obtain challenge challenges' where challenges_eq:
    "challenges = challenge # challenges'"
    by (cases challenges) auto
  have lookup_root:
    "fmlookup (HashMap s)
      (tag (counter s) (concat (PState s) root)) = Some challenge"
    using spec[OF Cons.prems(1), of 0] challenges_eq by simp
  have head_nf:
    "None \<notin> dom (dist (execute receive_commits
      (s\<lparr>PTranscript := root # (roots @ rest)\<rparr>)))"
    by (rule step_nf) simp
  have case_eq:
    "?case =
      (None \<notin> dom (dist (execute
        (receive_commits \<bind>
          (\<lambda>br. ntimes receive_commits (length roots) \<bind>
            (\<lambda>brs. return (br # brs))))
        (s\<lparr>PTranscript := root # (roots @ rest)\<rparr>))))"
    by simp
  show ?case
    unfolding case_eq
  proof (rule no_failure_bindI[OF head_nf])
    fix br u
    assume head:
      "Some (br, u) \<in>
        set_dist (execute receive_commits
          (s\<lparr>PTranscript := root # roots @ rest\<rparr>))"
    obtain b r where br_eq: "br = (b, r)"
      by (cases br)
    have head_out:
      "r = root \<and>
       b = challenge \<and>
       PState u = concat (PState s) root \<and>
       PTranscript u = roots @ rest \<and>
       counter u = Suc (counter s) \<and>
       s \<le> u"
      using step[OF lookup_root head[unfolded br_eq]]
      unfolding br_eq by simp
    have tail_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap u)
          (tag (counter u + i)
            (foldl concat (PState u) (take (Suc i) roots))) =
          Some (challenges' ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < length roots"
      have old_lookup:
        "fmlookup (HashMap s)
          (tag (counter s + Suc i)
            (foldl concat (PState s) (take (Suc (Suc i)) (root # roots)))) =
          Some ((challenge # challenges') ! Suc i)"
        using spec[OF Cons.prems(1), of "Suc i"] i_bound challenges_eq by simp
      have key_eq:
        "foldl concat (PState s) (take (Suc (Suc i)) (root # roots)) =
          foldl concat (PState u) (take (Suc i) roots)"
        using head_out by simp
      show "fmlookup (HashMap u)
          (tag (counter u + i)
            (foldl concat (PState u) (take (Suc i) roots))) =
        Some (challenges' ! i)"
        using p.hash_extension_lookup[OF old_lookup, of u] head_out key_eq i_bound
        by simp
    qed
    have tail_len: "length challenges' = length roots"
      using Cons.prems(2) challenges_eq by simp
    have tail_nf_start:
      "None \<notin> dom (dist (execute
        (ntimes receive_commits (length roots))
        (u\<lparr>PTranscript := roots @ rest\<rparr>)))"
      using Cons.IH[OF tail_lookups tail_len, of rest] .
    have u_update: "u\<lparr>PTranscript := roots @ rest\<rparr> = u"
      using head_out by simp
    have tail_nf:
      "None \<notin> dom (dist (execute
        (ntimes receive_commits (length roots)) u))"
      using tail_nf_start unfolding u_update .
    show "None \<notin> dom (dist (execute
      (ntimes receive_commits (length roots) \<bind>
        (\<lambda>brs. return (br # brs))) u))"
      by (rule no_failure_bindI[OF tail_nf]) simp
  qed
qed

lemma honest_receive_trace_fri_commits_list_outcome:
  assumes lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap s)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i)"
    and len: "length challenges = length roots"
    and outcome:
      "Some (brs, t) \<in>
        set_dist (execute (ntimes v.receive_trace_fri_commits (length roots))
          (s\<lparr>PTranscript := roots @ rest\<rparr>))"
  shows
    "brs = zip challenges roots \<and>
     PState t = foldl concat (PState s) roots \<and>
     PTranscript t = rest \<and>
     s \<le> t"
proof -
  have counter_update:
    "\<And>s tr. PTraceFriCounter (s\<lparr>PTranscript := tr\<rparr>) = PTraceFriCounter s"
    by simp
  have res:
    "brs = zip challenges roots \<and>
     PState t = foldl concat (PState s) roots \<and>
     PTranscript t = rest \<and>
     PTraceFriCounter t = PTraceFriCounter s + length roots \<and>
     s \<le> t"
    by (rule honest_receive_fri_commits_list_outcome_with
        [where counter=PTraceFriCounter and tag=TraceFriChallenge,
          OF honest_receive_trace_fri_commit_replay_outcome counter_update lookups len outcome])
  then show ?thesis by simp
qed

lemma honest_receive_composition_fri_commits_list_outcome:
  assumes lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap s)
        (CompositionFriChallenge
          (PCompositionFriCounter s + i)
          (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i)"
    and len: "length challenges = length roots"
    and outcome:
      "Some (brs, t) \<in>
        set_dist (execute
          (ntimes v.receive_composition_fri_commits (length roots))
          (s\<lparr>PTranscript := roots @ rest\<rparr>))"
  shows
    "brs = zip challenges roots \<and>
     PState t = foldl concat (PState s) roots \<and>
     PTranscript t = rest \<and>
     s \<le> t"
proof -
  have counter_update:
    "\<And>s tr. PCompositionFriCounter
      (s\<lparr>PTranscript := tr\<rparr>) = PCompositionFriCounter s"
    by simp
  have res:
    "brs = zip challenges roots \<and>
     PState t = foldl concat (PState s) roots \<and>
     PTranscript t = rest \<and>
     PCompositionFriCounter t = PCompositionFriCounter s + length roots \<and>
     s \<le> t"
    by (rule honest_receive_fri_commits_list_outcome_with
        [where counter=PCompositionFriCounter and tag=CompositionFriChallenge,
          OF honest_receive_composition_fri_commit_replay_outcome
            counter_update lookups len outcome])
  then show ?thesis by simp
qed

lemma honest_receive_trace_fri_commits_list_no_failure:
  assumes lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap s)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i)"
    and len: "length challenges = length roots"
  shows
    "None \<notin> dom (dist (execute
      (ntimes v.receive_trace_fri_commits (length roots))
      (s\<lparr>PTranscript := roots @ rest\<rparr>)))"
  using lookups len
proof (induction roots arbitrary: challenges s rest)
  case Nil
  then show ?case by simp
next
  case (Cons root roots)
  from Cons.prems(2) obtain challenge challenges' where challenges_eq:
    "challenges = challenge # challenges'"
    by (cases challenges) auto
  have lookup_root:
    "fmlookup (HashMap s)
      (TraceFriChallenge (PTraceFriCounter s) (concat (PState s) root)) =
      Some challenge"
    using spec[OF Cons.prems(1), of 0] challenges_eq by simp
  have head_nf:
    "None \<notin> dom (dist (execute v.receive_trace_fri_commits
      (s\<lparr>PTranscript := root # (roots @ rest)\<rparr>)))"
    by (rule v.receive_trace_fri_commits_no_failure) simp
  have case_eq:
    "?case =
      (None \<notin> dom (dist (execute
        (v.receive_trace_fri_commits \<bind>
          (\<lambda>br. ntimes v.receive_trace_fri_commits (length roots) \<bind>
            (\<lambda>brs. return (br # brs))))
        (s\<lparr>PTranscript := root # (roots @ rest)\<rparr>))))"
    by simp
  show ?case
    unfolding case_eq
  proof (rule no_failure_bindI[OF head_nf])
    fix br u
    assume head:
      "Some (br, u) \<in>
        set_dist (execute v.receive_trace_fri_commits
          (s\<lparr>PTranscript := root # roots @ rest\<rparr>))"
    obtain b r where br_eq: "br = (b, r)"
      by (cases br)
    have head_out:
      "r = root \<and>
       b = challenge \<and>
       PState u = concat (PState s) root \<and>
       PTranscript u = roots @ rest \<and>
       PTraceFriCounter u = Suc (PTraceFriCounter s) \<and>
       s \<le> u"
      using honest_receive_trace_fri_commit_replay_outcome[
        OF lookup_root head[unfolded br_eq]]
      unfolding br_eq by simp
    have tail_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap u)
          (TraceFriChallenge
            (PTraceFriCounter u + i)
            (foldl concat (PState u) (take (Suc i) roots))) =
          Some (challenges' ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < length roots"
      have old_lookup:
        "fmlookup (HashMap s)
          (TraceFriChallenge
            (PTraceFriCounter s + Suc i)
            (foldl concat (PState s) (take (Suc (Suc i)) (root # roots)))) =
          Some ((challenge # challenges') ! Suc i)"
        using spec[OF Cons.prems(1), of "Suc i"] i_bound challenges_eq
        by simp
      have key_eq:
        "foldl concat (PState s) (take (Suc (Suc i)) (root # roots)) =
          foldl concat (PState u) (take (Suc i) roots)"
        using head_out by simp
      show "fmlookup (HashMap u)
          (TraceFriChallenge
            (PTraceFriCounter u + i)
            (foldl concat (PState u) (take (Suc i) roots))) =
        Some (challenges' ! i)"
        using p.hash_extension_lookup[OF old_lookup, of u] head_out key_eq
          i_bound
        by simp
    qed
    have tail_len: "length challenges' = length roots"
      using Cons.prems(2) challenges_eq by simp
    have tail_nf_start:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_trace_fri_commits (length roots))
        (u\<lparr>PTranscript := roots @ rest\<rparr>)))"
      using Cons.IH[OF tail_lookups tail_len, of rest] .
    have u_update: "u\<lparr>PTranscript := roots @ rest\<rparr> = u"
      using head_out by simp
    have tail_nf:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_trace_fri_commits (length roots)) u))"
      using tail_nf_start unfolding u_update .
    show "None \<notin> dom (dist (execute
      (ntimes v.receive_trace_fri_commits (length roots) \<bind>
        (\<lambda>brs. return (br # brs))) u))"
      by (rule no_failure_bindI[OF tail_nf]) simp
  qed
qed

lemma honest_receive_composition_fri_commits_list_no_failure:
  assumes lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap s)
        (CompositionFriChallenge
          (PCompositionFriCounter s + i)
          (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i)"
    and len: "length challenges = length roots"
  shows
    "None \<notin> dom (dist (execute
      (ntimes v.receive_composition_fri_commits (length roots))
      (s\<lparr>PTranscript := roots @ rest\<rparr>)))"
  using lookups len
proof (induction roots arbitrary: challenges s rest)
  case Nil
  then show ?case by simp
next
  case (Cons root roots)
  from Cons.prems(2) obtain challenge challenges' where challenges_eq:
    "challenges = challenge # challenges'"
    by (cases challenges) auto
  have lookup_root:
    "fmlookup (HashMap s)
      (CompositionFriChallenge (PCompositionFriCounter s)
        (concat (PState s) root)) =
      Some challenge"
    using spec[OF Cons.prems(1), of 0] challenges_eq by simp
  have head_nf:
    "None \<notin> dom (dist (execute v.receive_composition_fri_commits
      (s\<lparr>PTranscript := root # (roots @ rest)\<rparr>)))"
    by (rule v.receive_composition_fri_commits_no_failure) simp
  have case_eq:
    "?case =
      (None \<notin> dom (dist (execute
        (v.receive_composition_fri_commits \<bind>
          (\<lambda>br. ntimes v.receive_composition_fri_commits (length roots) \<bind>
            (\<lambda>brs. return (br # brs))))
        (s\<lparr>PTranscript := root # (roots @ rest)\<rparr>))))"
    by simp
  show ?case
    unfolding case_eq
  proof (rule no_failure_bindI[OF head_nf])
    fix br u
    assume head:
      "Some (br, u) \<in>
        set_dist (execute v.receive_composition_fri_commits
          (s\<lparr>PTranscript := root # roots @ rest\<rparr>))"
    obtain b r where br_eq: "br = (b, r)"
      by (cases br)
    have head_out:
      "r = root \<and>
       b = challenge \<and>
       PState u = concat (PState s) root \<and>
       PTranscript u = roots @ rest \<and>
       PCompositionFriCounter u = Suc (PCompositionFriCounter s) \<and>
       s \<le> u"
      using honest_receive_composition_fri_commit_replay_outcome[
        OF lookup_root head[unfolded br_eq]]
      unfolding br_eq by simp
    have tail_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap u)
          (CompositionFriChallenge
            (PCompositionFriCounter u + i)
            (foldl concat (PState u) (take (Suc i) roots))) =
          Some (challenges' ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < length roots"
      have old_lookup:
        "fmlookup (HashMap s)
          (CompositionFriChallenge
            (PCompositionFriCounter s + Suc i)
            (foldl concat (PState s) (take (Suc (Suc i)) (root # roots)))) =
          Some ((challenge # challenges') ! Suc i)"
        using spec[OF Cons.prems(1), of "Suc i"] i_bound challenges_eq
        by simp
      have key_eq:
        "foldl concat (PState s) (take (Suc (Suc i)) (root # roots)) =
          foldl concat (PState u) (take (Suc i) roots)"
        using head_out by simp
      show "fmlookup (HashMap u)
          (CompositionFriChallenge
            (PCompositionFriCounter u + i)
            (foldl concat (PState u) (take (Suc i) roots))) =
        Some (challenges' ! i)"
        using p.hash_extension_lookup[OF old_lookup, of u] head_out key_eq
          i_bound
        by simp
    qed
    have tail_len: "length challenges' = length roots"
      using Cons.prems(2) challenges_eq by simp
    have tail_nf_start:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_composition_fri_commits (length roots))
        (u\<lparr>PTranscript := roots @ rest\<rparr>)))"
      using Cons.IH[OF tail_lookups tail_len, of rest] .
    have u_update: "u\<lparr>PTranscript := roots @ rest\<rparr> = u"
      using head_out by simp
    have tail_nf:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_composition_fri_commits (length roots)) u))"
      using tail_nf_start unfolding u_update .
    show "None \<notin> dom (dist (execute
      (ntimes v.receive_composition_fri_commits (length roots) \<bind>
        (\<lambda>brs. return (br # brs))) u))"
      by (rule no_failure_bindI[OF tail_nf]) simp
  qed
qed

lemma honest_fri_commit_lengths:
  assumes "Some ((ps', ds', ls', ms'), t) \<in>
    set_dist (execute (p.fri_commit n ps ds ls ms) s)"
  shows
    "length ps' = length ps + n \<and>
     length ds' = length ds + n \<and>
     length ls' = length ls + n \<and>
     length ms' = length ms + n"
  using p.fri_commit_lengths[OF assms] .

lemma honest_fri_commit_extends:
  assumes "Some ((ps', ds', ls', ms'), t) \<in>
    set_dist (execute (p.fri_commit n ps ds ls ms) s)"
  shows "s \<le> t"
  using p.fri_commit_extends[OF assms] .

lemma honest_fri_commit_layers_are_evaluations:
  assumes init:
    "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
      ls ! i = map (poly (ps ! i)) (ds ! i)"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (p.fri_commit n ps ds ls ms) s)"
    and lens: "length ps = length ds" "length ds = length ls"
    and bounds: "i < length ps'" "i < length ds'" "i < length ls'"
  shows "ls' ! i = map (poly (ps' ! i)) (ds' ! i)"
  using p.fri_commit_layers_are_evaluations[OF init outcome lens bounds] .

lemma honest_fri_commit_created_trees:
  assumes init:
    "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow> p.created_tree (ls ! i) (ms ! i) s"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (p.fri_commit n ps ds ls ms) s)"
    and lens: "length ls = length ms"
    and bounds: "i < length ls'" "i < length ms'"
  shows "p.created_tree (ls' ! i) (ms' ! i) t"
  using p.fri_commit_created_trees[OF init outcome lens bounds] .

lemma honest_prover_monad_outcome:
  assumes outcome:
    "Some (final, t) \<in> set_dist (execute p.prover_monad init_state)"
  obtains f_merkle s1 s2 f_nrounds f_ps f_ds f_ls f_ms s_trace_fri
      s_trace_final as s3 cp' s4 cp_merkle s5 nrounds ps ds ls ms s6 s_final
  where
    "Some (f_merkle, s1) \<in>
      set_dist (execute (p.create p.f_eval) init_state)"
    "p.created_tree p.f_eval f_merkle s1"
    "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    "f_nrounds = ceil_log clength"
    "Some ((f_ps, f_ds, f_ls, f_ms), s_trace_fri) \<in>
      set_dist (execute
        (p.trace_fri_commit f_nrounds [p.f] [p.eval_domain] [p.f_eval]
          [f_merkle]) s2)"
    "length f_ps = Suc f_nrounds"
    "length f_ds = Suc f_nrounds"
    "length f_ls = Suc f_nrounds"
    "length f_ms = Suc f_nrounds"
    "\<And>i. i < length f_ps \<Longrightarrow> i < length f_ds \<Longrightarrow> i < length f_ls \<Longrightarrow>
      f_ls ! i = map (poly (f_ps ! i)) (f_ds ! i)"
    "\<And>i. i < length f_ls \<Longrightarrow> i < length f_ms \<Longrightarrow>
      p.created_tree (f_ls ! i) (f_ms ! i) s_trace_fri"
    "Some ((), s_trace_final) \<in> set_dist (execute (p.send (hd (last f_ls))) s_trace_fri)"
    "Some (as, s3) \<in>
      set_dist (execute
        (mmap (replicate (length spec)
          (do {
            a \<leftarrow> p.receive_alpha_challenge;
            p.send a;
            return a
          }))) s_trace_final)"
    "cp' = p.cp as p.f_powers"
    "Some ((), s4) \<in> set_dist (execute (p.send (of_nat (degree cp'))) s3)"
    "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
    "p.created_tree (p.cp_eval as) cp_merkle s5"
    "nrounds = ceil_log (degree cp' + 1)"
    "Some ((ps, ds, ls, ms), s6) \<in>
      set_dist (execute
        (p.composition_fri_commit nrounds [cp'] [p.eval_domain]
          [p.cp_eval as] [cp_merkle]) s5)"
    "length ps = Suc nrounds"
    "length ds = Suc nrounds"
    "length ls = Suc nrounds"
    "length ms = Suc nrounds"
    "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
      ls ! i = map (poly (ps ! i)) (ds ! i)"
    "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
      p.created_tree (ls ! i) (ms ! i) s6"
    "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    "Some (final, t) \<in>
      set_dist (execute
        (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds) s_final)"
proof -
  from outcome obtain f_merkle s1 s2 f_ps f_ds f_ls f_ms s_trace_fri
      s_trace_final as s3 s4 cp_merkle s5 ps ds ls ms s6 s_final where
    create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and send_f:
      "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    and trace_fri:
      "Some ((f_ps, f_ds, f_ls, f_ms), s_trace_fri) \<in>
        set_dist (execute
          (p.trace_fri_commit (ceil_log clength)
            [p.f] [p.eval_domain] [p.f_eval] [f_merkle]) s2)"
    and trace_final_send:
      "Some ((), s_trace_final) \<in>
        set_dist (execute (p.send (hd (last f_ls))) s_trace_fri)"
    and alphas:
      "Some (as, s3) \<in>
        set_dist (execute
          (mmap (replicate (length spec)
            (do {
              a \<leftarrow> p.receive_alpha_challenge;
              p.send a;
              return a
            }))) s_trace_final)"
    and send_degree:
      "Some ((), s4) \<in>
        set_dist (execute (p.send (of_nat (degree (p.cp as p.f_powers)))) s3)"
    and create_cp:
      "Some (cp_merkle, s5) \<in>
        set_dist (execute (p.create (p.cp_eval as)) s4)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.composition_fri_commit
            (ceil_log (degree (p.cp as p.f_powers) + 1))
            [p.cp as p.f_powers] [p.eval_domain] [p.cp_eval as] [cp_merkle]) s5)"
    and final_send:
      "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and round_tail:
      "Some (final, t) \<in>
        set_dist (execute
          (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds) s_final)"
    unfolding p.prover_monad_def
    by (auto simp: Let_def init_state_def prover_query_round_def
        split: prod.splits elim!: p.set_dist_bindE)
  let ?cp' = "p.cp as p.f_powers"
  let ?nrounds = "ceil_log (degree ?cp' + 1)"
  have created_f: "p.created_tree p.f_eval f_merkle s1"
    using p.create_outcome[OF create_f] by simp
  let ?f_nrounds = "ceil_log clength"
  have trace_fri_lengths:
    "length f_ps = Suc ?f_nrounds"
    "length f_ds = Suc ?f_nrounds"
    "length f_ls = Suc ?f_nrounds"
    "length f_ms = Suc ?f_nrounds"
    using p.trace_fri_commit_lengths[OF trace_fri] by simp_all
  have trace_fri_layers:
    "\<And>i. i < length f_ps \<Longrightarrow> i < length f_ds \<Longrightarrow> i < length f_ls \<Longrightarrow>
      f_ls ! i = map (poly (f_ps ! i)) (f_ds ! i)"
  proof (rule p.trace_fri_commit_layers_are_evaluations[OF _ trace_fri])
    fix i
    assume "i < length [p.f]" "i < length [p.eval_domain]" "i < length [p.f_eval]"
    then show "[p.f_eval] ! i =
      map (poly ([p.f] ! i)) ([p.eval_domain] ! i)"
      unfolding p.f_eval_def by simp
  qed simp_all
  have trace_fri_created:
    "\<And>i. i < length f_ls \<Longrightarrow> i < length f_ms \<Longrightarrow>
      p.created_tree (f_ls ! i) (f_ms ! i) s_trace_fri"
  proof (rule p.trace_fri_commit_created_trees[OF _ trace_fri])
    fix i
    assume "i < length [p.f_eval]" "i < length [f_merkle]"
    then show "p.created_tree ([p.f_eval] ! i) ([f_merkle] ! i) s2"
    proof -
      have "s1 \<le> s2"
        using p.send_outcome[OF send_f]
        unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
      then have "p.created_tree p.f_eval f_merkle s2"
        using p.created_tree_mono[OF created_f] by blast
      then show ?thesis
        using \<open>i < length [p.f_eval]\<close> \<open>i < length [f_merkle]\<close> by simp
    qed
  qed simp_all
  have created_cp: "p.created_tree (p.cp_eval as) cp_merkle s5"
    using p.create_outcome[OF create_cp] by simp
  have fri_lengths:
    "length ps = Suc ?nrounds"
    "length ds = Suc ?nrounds"
    "length ls = Suc ?nrounds"
    "length ms = Suc ?nrounds"
    using p.composition_fri_commit_lengths[OF fri] by simp_all
  have fri_layers:
    "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
      ls ! i = map (poly (ps ! i)) (ds ! i)"
  proof (rule p.composition_fri_commit_layers_are_evaluations[OF _ fri])
    fix i
    assume "i < length [?cp']" "i < length [p.eval_domain]" "i < length [p.cp_eval as]"
    then show "[p.cp_eval as] ! i =
      map (poly ([?cp'] ! i)) ([p.eval_domain] ! i)"
      unfolding p.cp_eval_def by simp
  qed simp_all
  have fri_created:
    "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
      p.created_tree (ls ! i) (ms ! i) s6"
  proof (rule p.composition_fri_commit_created_trees[OF _ fri])
    fix i
    assume "i < length [p.cp_eval as]" "i < length [cp_merkle]"
    then show "p.created_tree ([p.cp_eval as] ! i) ([cp_merkle] ! i) s5"
      using created_cp by simp
  qed simp_all
  show ?thesis
    by (rule that[
        OF create_f created_f send_f refl trace_fri trace_fri_lengths(1)
        trace_fri_lengths(2) trace_fri_lengths(3) trace_fri_lengths(4)
        trace_fri_layers trace_fri_created trace_final_send alphas refl send_degree create_cp created_cp
        refl fri fri_lengths(1) fri_lengths(2) fri_lengths(3) fri_lengths(4)
        fri_layers fri_created final_send round_tail])
qed

lemma honest_verifier_monad_outcome:
  assumes outcome:
    "Some (result, t) \<in> set_dist (execute v.verify_monad s)"
  obtains fr s1 f_fl s_fri f_final s_fri_final as s2 dg s3 s4 fl s5 final s6
  where
    "Some (fr, s1) \<in> set_dist (execute p.read s)"
    "Some (f_fl, s_fri) \<in>
      set_dist (execute
        (ntimes v.receive_trace_fri_commits (ceil_log clength)) s1)"
    "Some (f_final, s_fri_final) \<in> set_dist (execute p.read s_fri)"
    "Some (as, s2) \<in>
      set_dist (execute
        (mmap (replicate (length spec)
          (do {
            a0 \<leftarrow> p.receive_alpha_challenge;
            let a0' = a0;
            a1 \<leftarrow> p.read;
            let a1' = a1;
            assert (a0' = a1');
            return a1'
          }))) s_fri_final)"
    "Some (dg, s3) \<in> set_dist (execute p.read s2)"
    "Some ((), s4) \<in>
      set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s3)"
    "to_nat dg \<le> p.maxDegree"
    "s4 = s3"
    "Some (fl, s5) \<in>
      set_dist (execute
        (ntimes v.receive_composition_fri_commits
          (ceil_log (to_nat dg + 1))) s4)"
    "Some (final, s6) \<in> set_dist (execute p.read s5)"
    "Some (result, t) \<in>
      set_dist (execute
        (ntimes (verifier_query_round fr f_fl f_final as fl final) rounds) s6)"
proof -
  from outcome obtain fr s1 f_fl s_fri f_final s_fri_final as s2 dg s3 s4 fl s5 final s6 where
    read_fr: "Some (fr, s1) \<in> set_dist (execute p.read s)"
    and trace_fri_reads:
      "Some (f_fl, s_fri) \<in>
        set_dist (execute
          (ntimes v.receive_trace_fri_commits (ceil_log clength)) s1)"
    and read_trace_final:
      "Some (f_final, s_fri_final) \<in> set_dist (execute p.read s_fri)"
    and alphas:
      "Some (as, s2) \<in>
        set_dist (execute
          (mmap (replicate (length spec)
            (do {
              a0 \<leftarrow> p.receive_alpha_challenge;
              let a0' = a0;
              a1 \<leftarrow> p.read;
              let a1' = a1;
              assert (a0' = a1');
              return a1'
            }))) s_fri_final)"
    and read_dg: "Some (dg, s3) \<in> set_dist (execute p.read s2)"
    and degree_assert:
      "Some ((), s4) \<in>
        set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s3)"
    and fri_reads:
      "Some (fl, s5) \<in>
        set_dist (execute
          (ntimes v.receive_composition_fri_commits
            (ceil_log (to_nat dg + 1))) s4)"
    and read_final: "Some (final, s6) \<in> set_dist (execute p.read s5)"
    and round_tail:
      "Some (result, t) \<in>
        set_dist (execute
          (ntimes (verifier_query_round fr f_fl f_final as fl final) rounds) s6)"
    unfolding v.verify_monad_def
    by (auto simp: Let_def verifier_query_round_def
        split: prod.splits elim!: p.set_dist_bindE)
  have degree_ok: "to_nat dg \<le> p.maxDegree"
    using degree_assert
    by (cases "to_nat dg \<le> p.maxDegree") (auto simp: assert_def)
  have s4_eq: "s4 = s3"
    using degree_assert
    by (cases "to_nat dg \<le> p.maxDegree") (auto simp: assert_def)
  show ?thesis
    by (rule that[
        OF read_fr trace_fri_reads read_trace_final alphas read_dg degree_assert degree_ok s4_eq fri_reads
          read_final round_tail])
qed

lemma exec_success_splits:
  assumes outcome:
    "Some (result, t) \<in> set_dist (execute exec init_state)"
  obtains prover_result prover_state replay_state
  where
    "Some (prover_result, prover_state) \<in>
      set_dist (execute p.prover_monad init_state)"
    "Some ((), replay_state) \<in>
      set_dist (execute
        (modify (\<lambda>c. c\<lparr>PState := 0, PTranscript := rev (PTranscript c),
          PTraceFriCounter := 0, PCompositionFriCounter := 0,
          PAlphaCounter := 0, PQueryCounter := 0\<rparr>))
        prover_state)"
    "replay_state = verifier_replay_state prover_state"
    "Some (result, t) \<in> set_dist (execute v.verify_monad replay_state)"
proof -
  from outcome obtain prover_result prover_state replay_unit replay_state where
    prover:
      "Some (prover_result, prover_state) \<in>
        set_dist (execute p.prover_monad init_state)"
    and reset:
      "Some (replay_unit, replay_state) \<in>
        set_dist (execute
          (modify (\<lambda>c. c\<lparr>PState := 0, PTranscript := rev (PTranscript c),
            PTraceFriCounter := 0, PCompositionFriCounter := 0,
            PAlphaCounter := 0, PQueryCounter := 0\<rparr>))
          prover_state)"
    and verifier:
      "Some (result, t) \<in> set_dist (execute v.verify_monad replay_state)"
    unfolding exec_def
    by (auto elim!: p.set_dist_bindE)
  have reset_res:
    "replay_unit = () \<and> replay_state = verifier_replay_state prover_state"
    using modify_verifier_replay_state_outcome[OF reset] .
  show ?thesis
    by (rule that[OF prover _ _ verifier])
      (use reset reset_res in simp_all)
qed

lemma exec_success_prover_outcome:
  assumes outcome:
    "Some (result, t) \<in> set_dist (execute exec init_state)"
  obtains prover_result prover_state replay_state
      f_merkle s1 s2 f_nrounds f_ps f_ds f_ls f_ms s_trace_fri
      s_trace_final as s3 cp' s4 cp_merkle s5 nrounds ps ds ls ms s6 s_final
  where
    "Some (prover_result, prover_state) \<in>
      set_dist (execute p.prover_monad init_state)"
    "replay_state = verifier_replay_state prover_state"
    "Some (f_merkle, s1) \<in>
      set_dist (execute (p.create p.f_eval) init_state)"
    "p.created_tree p.f_eval f_merkle s1"
    "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    "f_nrounds = ceil_log clength"
    "Some ((f_ps, f_ds, f_ls, f_ms), s_trace_fri) \<in>
      set_dist (execute
        (p.trace_fri_commit f_nrounds [p.f] [p.eval_domain] [p.f_eval]
          [f_merkle]) s2)"
    "length f_ps = Suc f_nrounds"
    "length f_ds = Suc f_nrounds"
    "length f_ls = Suc f_nrounds"
    "length f_ms = Suc f_nrounds"
    "\<And>i. i < length f_ps \<Longrightarrow> i < length f_ds \<Longrightarrow> i < length f_ls \<Longrightarrow>
      f_ls ! i = map (poly (f_ps ! i)) (f_ds ! i)"
    "\<And>i. i < length f_ls \<Longrightarrow> i < length f_ms \<Longrightarrow>
      p.created_tree (f_ls ! i) (f_ms ! i) s_trace_fri"
    "Some ((), s_trace_final) \<in> set_dist (execute (p.send (hd (last f_ls))) s_trace_fri)"
    "Some (as, s3) \<in>
      set_dist (execute
        (mmap (replicate (length spec)
          (do {
            a \<leftarrow> p.receive_alpha_challenge;
            p.send a;
            return a
          }))) s_trace_final)"
    "cp' = p.cp as p.f_powers"
    "Some ((), s4) \<in> set_dist (execute (p.send (of_nat (degree cp'))) s3)"
    "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
    "p.created_tree (p.cp_eval as) cp_merkle s5"
    "nrounds = ceil_log (degree cp' + 1)"
    "Some ((ps, ds, ls, ms), s6) \<in>
      set_dist (execute
        (p.composition_fri_commit nrounds [cp'] [p.eval_domain]
          [p.cp_eval as] [cp_merkle]) s5)"
    "length ps = Suc nrounds"
    "length ds = Suc nrounds"
    "length ls = Suc nrounds"
    "length ms = Suc nrounds"
    "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
      ls ! i = map (poly (ps ! i)) (ds ! i)"
    "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
      p.created_tree (ls ! i) (ms ! i) s6"
    "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    "Some (prover_result, prover_state) \<in>
      set_dist (execute
        (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds) s_final)"
proof -
  from exec_success_splits[OF outcome] obtain prover_result prover_state replay_state where
    prover:
      "Some (prover_result, prover_state) \<in>
        set_dist (execute p.prover_monad init_state)"
    and replay: "replay_state = verifier_replay_state prover_state"
    by blast
  show ?thesis
  proof (rule honest_prover_monad_outcome[OF prover])
    fix f_merkle s1 s2 f_nrounds f_ps f_ds f_ls f_ms s_trace_fri
        s_trace_final as s3 cp' s4 cp_merkle s5 nrounds ps ds ls ms s6 s_final
    assume create_f:
        "Some (f_merkle, s1) \<in>
          set_dist (execute (p.create p.f_eval) init_state)"
      and created_f: "p.created_tree p.f_eval f_merkle s1"
      and send_f: "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
      and f_nrounds_def: "f_nrounds = ceil_log clength"
      and trace_fri:
        "Some ((f_ps, f_ds, f_ls, f_ms), s_trace_fri) \<in>
          set_dist (execute
            (p.trace_fri_commit f_nrounds [p.f] [p.eval_domain] [p.f_eval]
              [f_merkle]) s2)"
      and trace_len_ps: "length f_ps = Suc f_nrounds"
      and trace_len_ds: "length f_ds = Suc f_nrounds"
      and trace_len_ls: "length f_ls = Suc f_nrounds"
      and trace_len_ms: "length f_ms = Suc f_nrounds"
      and trace_layers:
        "\<And>i. i < length f_ps \<Longrightarrow> i < length f_ds \<Longrightarrow> i < length f_ls \<Longrightarrow>
          f_ls ! i = map (poly (f_ps ! i)) (f_ds ! i)"
      and trace_trees:
        "\<And>i. i < length f_ls \<Longrightarrow> i < length f_ms \<Longrightarrow>
          p.created_tree (f_ls ! i) (f_ms ! i) s_trace_fri"
      and trace_final_send:
        "Some ((), s_trace_final) \<in> set_dist (execute (p.send (hd (last f_ls))) s_trace_fri)"
      and alphas:
        "Some (as, s3) \<in>
          set_dist (execute
            (mmap (replicate (length spec)
              (do {
                a \<leftarrow> p.receive_alpha_challenge;
                p.send a;
                return a
              }))) s_trace_final)"
      and cp'_def: "cp' = p.cp as p.f_powers"
      and send_degree:
        "Some ((), s4) \<in> set_dist (execute (p.send (of_nat (degree cp'))) s3)"
      and create_cp:
        "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
      and created_cp: "p.created_tree (p.cp_eval as) cp_merkle s5"
      and nrounds_def: "nrounds = ceil_log (degree cp' + 1)"
      and fri:
        "Some ((ps, ds, ls, ms), s6) \<in>
          set_dist (execute
            (p.composition_fri_commit nrounds [cp'] [p.eval_domain]
              [p.cp_eval as] [cp_merkle]) s5)"
      and len_ps: "length ps = Suc nrounds"
      and len_ds: "length ds = Suc nrounds"
      and len_ls: "length ls = Suc nrounds"
      and len_ms: "length ms = Suc nrounds"
      and layers:
        "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
          ls ! i = map (poly (ps ! i)) (ds ! i)"
      and trees:
        "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
          p.created_tree (ls ! i) (ms ! i) s6"
      and final_send:
        "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
      and round_tail:
        "Some (prover_result, prover_state) \<in>
          set_dist (execute
            (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds) s_final)"
    show ?thesis
      using prover replay create_f created_f send_f f_nrounds_def trace_fri
        trace_len_ps trace_len_ds trace_len_ls trace_len_ms trace_layers
        trace_trees trace_final_send alphas cp'_def send_degree
        create_cp created_cp nrounds_def fri len_ps len_ds len_ls len_ms
        layers trees final_send round_tail
      by (rule that)
  qed
qed

lemma exec_success_verifier_replay_outcome:
  assumes outcome:
    "Some (result, t) \<in> set_dist (execute exec init_state)"
  obtains prover_result prover_state replay_state
      fr s1 f_fl s_fri f_final s_fri_final as s2 dg s3 s4 fl s5 final s6
  where
    "Some (prover_result, prover_state) \<in>
      set_dist (execute p.prover_monad init_state)"
    "replay_state = verifier_replay_state prover_state"
    "Some (fr, s1) \<in> set_dist (execute p.read replay_state)"
    "Some (f_fl, s_fri) \<in>
      set_dist (execute
        (ntimes v.receive_trace_fri_commits (ceil_log clength)) s1)"
    "Some (f_final, s_fri_final) \<in> set_dist (execute p.read s_fri)"
    "Some (as, s2) \<in>
      set_dist (execute
        (mmap (replicate (length spec)
          (do {
            a0 \<leftarrow> p.receive_alpha_challenge;
            let a0' = a0;
            a1 \<leftarrow> p.read;
            let a1' = a1;
            assert (a0' = a1');
            return a1'
          }))) s_fri_final)"
    "Some (dg, s3) \<in> set_dist (execute p.read s2)"
    "Some ((), s4) \<in>
      set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s3)"
    "to_nat dg \<le> p.maxDegree"
    "s4 = s3"
    "Some (fl, s5) \<in>
      set_dist (execute
        (ntimes v.receive_composition_fri_commits
          (ceil_log (to_nat dg + 1))) s4)"
    "Some (final, s6) \<in> set_dist (execute p.read s5)"
    "Some (result, t) \<in>
      set_dist (execute
        (ntimes (verifier_query_round fr f_fl f_final as fl final) rounds) s6)"
proof -
  from exec_success_splits[OF outcome] obtain prover_result prover_state replay_state where
    prover:
      "Some (prover_result, prover_state) \<in>
        set_dist (execute p.prover_monad init_state)"
    and replay: "replay_state = verifier_replay_state prover_state"
    and verifier:
      "Some (result, t) \<in> set_dist (execute v.verify_monad replay_state)"
    by blast
  show ?thesis
  proof (rule honest_verifier_monad_outcome[OF verifier])
    fix fr s1 f_fl s_fri f_final s_fri_final as s2 dg s3 s4 fl s5 final s6
    assume read_fr: "Some (fr, s1) \<in> set_dist (execute p.read replay_state)"
      and trace_fri_reads:
        "Some (f_fl, s_fri) \<in>
          set_dist (execute
            (ntimes v.receive_trace_fri_commits (ceil_log clength)) s1)"
      and read_trace_final:
        "Some (f_final, s_fri_final) \<in> set_dist (execute p.read s_fri)"
      and alphas:
        "Some (as, s2) \<in>
          set_dist (execute
            (mmap (replicate (length spec)
              (do {
                a0 \<leftarrow> p.receive_alpha_challenge;
                let a0' = a0;
                a1 \<leftarrow> p.read;
                let a1' = a1;
                assert (a0' = a1');
                return a1'
              }))) s_fri_final)"
      and read_dg: "Some (dg, s3) \<in> set_dist (execute p.read s2)"
      and degree_assert:
        "Some ((), s4) \<in>
          set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s3)"
      and degree_ok: "to_nat dg \<le> p.maxDegree"
      and s4_eq: "s4 = s3"
      and fri_reads:
        "Some (fl, s5) \<in>
          set_dist (execute
            (ntimes v.receive_composition_fri_commits
              (ceil_log (to_nat dg + 1))) s4)"
      and read_final: "Some (final, s6) \<in> set_dist (execute p.read s5)"
      and round_tail:
        "Some (result, t) \<in>
          set_dist (execute
            (ntimes (verifier_query_round fr f_fl f_final as fl final) rounds) s6)"
    show ?thesis
      by (rule that[
          OF prover replay read_fr trace_fri_reads read_trace_final alphas read_dg degree_assert degree_ok s4_eq
            fri_reads read_final round_tail])
  qed
qed

end

end
