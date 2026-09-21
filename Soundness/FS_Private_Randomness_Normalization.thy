(* Title: Stark/FS_Private_Randomness_Normalization.thy
   License: BSD-3-Clause *)

theory FS_Private_Randomness_Normalization
  imports "Stark.FS_Fixed_Randomness_Replay"
begin

section \<open>Oracle-independent normalization of private randomness\<close>

text \<open>
  Every program in the existing terminating, finite-support FS syntax is
  represented by an oracle-independent finite distribution of fixed programs.
  Query continuations remain adaptive. At a query node we pre-sample a
  continuation for every field answer, then let the actual oracle answer select
  the branch. No oracle answer is sampled or conditioned on by this construction.

  The finite answer type is already supplied by the protocol field. The chosen
  enumeration is a proof-level existence construction, not a claim of efficient
  precomputation. No verifier, oracle, staged interface or public premise changes.
\<close>

subsection \<open>Finite private mixtures and continuation marginals\<close>

definition fs_dist_bind :: "'a dist \<Rightarrow> ('a \<Rightarrow> 'b dist) \<Rightarrow> 'b dist" where
  "fs_dist_bind d k = dist_map (\<lambda>out. fst (the out))
    (execute (lift (\<lambda>(_::unit). d) \<bind> (\<lambda>x. lift (\<lambda>_. k x))) ())"

lemma fs_dist_bind_expect:
  "dist_expect (fs_dist_bind d k) F =
    dist_expect d (\<lambda>x. dist_expect (k x) F)"
  unfolding fs_dist_bind_def
  by (simp add: dist_expect_map wp_def[symmetric] wp_bind wp_lift)

lemma fs_expect_zero_iff:
  "dist_expect d F = 0 \<longleftrightarrow> (\<forall>x\<in>set_dist d. F x = 0)"
  by (simp add: dist_expect_def set_dist_def sum_nonneg_eq_0_iff)

lemma fs_dist_bind_support:
  "set_dist (fs_dist_bind d k) = (\<Union>x\<in>set_dist d. set_dist (k x))"
proof (rule Set.set_eqI)
  fix z
  have "(dist_expect (fs_dist_bind d k) (\<lambda>y. if y=z then 1 else 0) = 0) =
      (dist_expect d (\<lambda>x. dist_expect (k x) (\<lambda>y. if y=z then 1 else 0)) = 0)"
    by (simp only: fs_dist_bind_expect)
  then show "(z \<in> set_dist (fs_dist_bind d k)) = (z \<in> (\<Union>x\<in>set_dist d. set_dist (k x)))"
    by (auto simp: fs_expect_zero_iff split: if_splits)
qed

lemma fs_expect_const:
  "dist_expect d (\<lambda>_. c) = c"
  unfolding dist_expect_def
  by (simp add: sum_distrib_right[symmetric] sum_map_def[symmetric])

lemma fs_expect_cong:
  assumes "\<And>x. x \<in> set_dist d \<Longrightarrow> F x = G x"
  shows "dist_expect d F = dist_expect d G"
  unfolding dist_expect_def
  by (intro sum.cong refl) (use assms in \<open>auto simp: set_dist_def\<close>)


lemma fs_expect_swap:
  "dist_expect d (\<lambda>a. dist_expect e (\<lambda>b. F a b)) =
    dist_expect e (\<lambda>b. dist_expect d (\<lambda>a. F a b))"
  unfolding dist_expect_def
  by (simp only: sum_distrib_left mult.left_commute) (rule sum.swap)

lemma fs_expect_wp_swap:
  "dist_expect d (\<lambda>x. wp m (F x) s) =
    wp m (\<lambda>out. dist_expect d (\<lambda>x. F x out)) s"
  unfolding wp_def by (rule fs_expect_swap)

lemma fs_delta_support[simp]:
  "set_dist (delta_dist x) = {x}"
  by (auto simp: set_dist_def dist_delta_dist delta_map_def)

fun fs_dist_functions ::
  "'i list \<Rightarrow> ('i \<Rightarrow> 'a dist) \<Rightarrow> ('i \<Rightarrow> 'a) dist"
where
  "fs_dist_functions [] d = delta_dist (\<lambda>_. undefined)"
| "fs_dist_functions (x#xs) d =
    fs_dist_bind (d x) (\<lambda>a. dist_map (\<lambda>f. f(x:=a)) (fs_dist_functions xs d))"

lemma fs_dist_functions_support:
  assumes "f \<in> set_dist (fs_dist_functions xs d)" "x \<in> set xs"
  shows "f x \<in> set_dist (d x)"
  using assms
  by (induction xs arbitrary: f)
    (auto simp: fs_dist_bind_support set_dist_dist_map split: if_splits)

lemma fs_dist_functions_marginal:
  assumes "distinct xs" "x \<in> set xs"
  shows "dist_expect (fs_dist_functions xs d) (\<lambda>f. F (f x)) =
    dist_expect (d x) F"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "a=x")
    case True
    then show ?thesis
      by (simp add: fs_dist_bind_expect dist_expect_map fs_expect_const)
  next
    case False
    with Cons show ?thesis
      by (simp add: fs_dist_bind_expect dist_expect_map fs_expect_const)
  qed
qed

subsection \<open>Fixed-program normalization and uniform query caps\<close>

text \<open>
  The arbitrary default function of the finite product is overwritten at every
  field value. Its support theorem applies to all possible oracle answers, not
  only answers observed in a particular run.
\<close>

definition fs_private_domain :: "'f::finite list" where
  "fs_private_domain = (SOME xs. distinct xs \<and> set xs = UNIV)"

lemma fs_private_domain:
  "distinct (fs_private_domain :: 'f::finite list)"
  "set (fs_private_domain :: 'f::finite list) = UNIV"
  unfolding fs_private_domain_def
  by (metis (mono_tags, lifting) finite_class.finite_UNIV
      finite_distinct_list verit_sko_ex')+

primrec fs_normalize ::
  "('f::finite,'a) fs_program \<Rightarrow> ('f,'a) fs_program dist"
where
  "fs_normalize (FS_Return x) = delta_dist (FS_Return x)"
| "fs_normalize FS_Fail = delta_dist FS_Fail"
| "fs_normalize (FS_Query key k) =
    dist_map (FS_Query key)
      (fs_dist_functions fs_private_domain (\<lambda>y. fs_normalize (k y)))"
| "fs_normalize (FS_Sample d k) = fs_dist_bind d (\<lambda>x. fs_normalize (k x))"

lemma fs_normalize_fixed:
  assumes "T \<in> set_dist (fs_normalize P)"
  shows "fs_fixed T"
  using assms
proof (induction P arbitrary: T)
  case (FS_Return x)
  then show ?case by (auto intro: fs_fixed.Return)
next
  case FS_Fail
  then show ?case by (auto intro: fs_fixed.Fail)
next
  case (FS_Query key k)
  then obtain f where T: "T = FS_Query key f"
    and f: "f \<in> set_dist (fs_dist_functions fs_private_domain (\<lambda>y. fs_normalize (k y)))"
    by (auto simp: set_dist_dist_map)
  have "fs_fixed (f y)" for y
    using fs_dist_functions_support[OF f, of y] FS_Query.IH fs_private_domain(2)
    by auto
  then show ?case unfolding T by (rule fs_fixed.Query)
next
  case (FS_Sample d k)
  then show ?case by (auto simp: fs_dist_bind_support)
qed

lemma fs_normalize_bound:
  assumes "fs_query_bound q P" "T \<in> set_dist (fs_normalize P)"
  shows "fs_query_bound q T"
  using assms
proof (induction arbitrary: T rule: fs_query_bound.induct)
  case (Return q x)
  then show ?case by (auto intro: fs_query_bound.Return)
next
  case (Fail q)
  then show ?case by (auto intro: fs_query_bound.Fail)
next
  case (Query q k key)
  then obtain f where T: "T = FS_Query key f"
    and f: "f \<in> set_dist (fs_dist_functions fs_private_domain (\<lambda>y. fs_normalize (k y)))"
    by (auto simp: set_dist_dist_map)
  have "fs_query_bound q (f y)" for y
    using fs_dist_functions_support[OF f, of y] Query.IH fs_private_domain(2)
    by auto
  then show ?case unfolding T by (rule fs_query_bound.Query)
next
  case (Sample q k d)
  then show ?case by (auto simp: fs_dist_bind_support)
qed

lemma fs_dist_expect_ext:
  assumes "\<And>F. dist_expect d F = dist_expect e F"
  shows "d=e"
proof (rule dist_inject[THEN iffD1], rule ext)
  fix x
  have weights: "option_default (dist d x) = option_default (dist e x)"
    using assms[of "\<lambda>y. if y=x then 1 else 0"]
    by (simp add: dist_expect_indicator)
  show "dist d x = dist e x"
    using weights dist_nonzero_on_dom[of x d] dist_nonzero_on_dom[of x e]
    by (cases "dist d x"; cases "dist e x") auto
qed

lemma fs_wp_ext:
  assumes "\<And>F s. wp m F s = wp n F s"
  shows "m=n"
  by (rule execute_inject[THEN iffD1], rule ext, rule fs_dist_expect_ext)
    (use assms in \<open>simp add: wp_def\<close>)

lemma fs_expect_le_const:
  assumes "\<And>x. x \<in> set_dist d \<Longrightarrow> F x \<le> c"
  shows "dist_expect d F \<le> c"
proof -
  have "dist_expect d F \<le> dist_expect d (\<lambda>_. c)"
    unfolding dist_expect_def
    by (intro sum_mono mult_left_mono) (use assms in \<open>auto simp: set_dist_def\<close>)
  then show ?thesis by (simp add: fs_expect_const)
qed

context soundness
begin

subsection \<open>Exact execution, failure and successful-count preservation\<close>

lemma fs_normalize_count_wp:
  "dist_expect (fs_normalize P) (\<lambda>T. wp (fs_count_run T) F s) =
    wp (fs_count_run P) F s"
proof (induction P arbitrary: F s)
  case (FS_Return x)
  then show ?case by simp
next
  case FS_Fail
  then show ?case by simp
next
  case (FS_Query key k)
  have marginal: "dist_expect
      (fs_dist_functions fs_private_domain (\<lambda>y. fs_normalize (k y)))
      (\<lambda>f. wp (fs_count_run (f y)) H t) = wp (fs_count_run (k y)) H t"
    for y H t
    using fs_dist_functions_marginal[OF fs_private_domain(1),
      where d="\<lambda>y. fs_normalize (k y)" and x=y
        and F="\<lambda>T. wp (fs_count_run T) H t"]
    by (simp add: fs_private_domain FS_Query.IH)
  show ?case
    apply (simp only: fs_normalize.simps dist_expect_map fs_count_run.simps wp_bind)
    apply (subst fs_expect_wp_swap)
    apply (rule arg_cong[where f="\<lambda>G. wp (hash key) G s"])
    apply (rule ext)
    subgoal for out
      by (cases out)
        (auto simp: fs_expect_const marginal split: prod.splits)
    done
next
  case (FS_Sample d k)
  then show ?case
    by (simp add: fs_dist_bind_expect wp_bind wp_lift)
qed

lemma fs_normalize_count:
  "(lift (\<lambda>_. fs_normalize P) \<bind> fs_count_run) = fs_count_run P"
  by (rule fs_wp_ext)
    (simp add: wp_bind wp_lift fs_normalize_count_wp)

lemma fs_normalize_run:
  "(lift (\<lambda>_. fs_normalize P) \<bind> fs_run) = fs_run P"
proof -
  have "(lift (\<lambda>_. fs_normalize P) \<bind> fs_count_run) \<bind>
      (\<lambda>(x,n). return x) = fs_run P"
    by (simp add: fs_normalize_count fs_count_run_erases)
  then show ?thesis
    by (simp add: sm_bind_assoc fs_count_run_erases)
qed

lemma fs_normalize_run_wp:
  "dist_expect (fs_normalize P) (\<lambda>T. wp (fs_run T) F s) =
    wp (fs_run P) F s"
  using arg_cong[OF fs_normalize_run[of P], where f="\<lambda>m. wp m F s"]
  by (simp add: wp_bind wp_lift)

lemma fs_normalize_follow_wp:
  "dist_expect (fs_normalize P) (\<lambda>T. wp (fs_run T \<bind> k) F s) =
    wp (fs_run P \<bind> k) F s"
  by (simp only: wp_bind fs_normalize_run_wp)

lemma fs_normalize_acceptance:
  "dist_expect (fs_normalize P) fs_acceptance_probability =
    fs_acceptance_probability P"
  unfolding fs_acceptance_probability_def fs_security_experiment_def wp_event_def
  by (rule fs_normalize_follow_wp)

subsection \<open>Connection to the bounded two-callback replay pilot\<close>

text \<open>
  The mixture selects one fixed program for both callbacks. It is not fresh
  private sampling in each callback and does not add a private-state field to the
  staged record. The two callbacks still have allowance Q each; normalization
  does not make replay free.
\<close>

lemma fs_normalize_two_callbacks:
  assumes ext: "\<And>x. hash_extension_preserving (gap x)"
  shows "dist_expect (fs_normalize P)
      (\<lambda>T. wp (fs_two_callbacks T select_first select_second gap) F s) =
    wp (fs_run P \<bind> (\<lambda>x. gap (select_first x) \<bind>
      (\<lambda>_. return (select_first x,select_second x)))) F s"
proof -
  have "dist_expect (fs_normalize P)
      (\<lambda>T. wp (fs_two_callbacks T select_first select_second gap) F s) =
    dist_expect (fs_normalize P) (\<lambda>T. wp (fs_run T \<bind>
      (\<lambda>x. gap (select_first x) \<bind>
        (\<lambda>_. return (select_first x,select_second x)))) F s)"
    by (rule fs_expect_cong; rule fs_two_callbacks_wp)
      (auto intro: fs_normalize_fixed ext)
  also have "... = wp (fs_run P \<bind>
      (\<lambda>x. gap (select_first x) \<bind>
        (\<lambda>_. return (select_first x,select_second x)))) F s"
    by (rule fs_normalize_follow_wp)
  finally show ?thesis .
qed

lemma fs_normalize_two_callbacks_actual:
  "dist_expect (fs_normalize P)
      (\<lambda>T. wp (fs_two_callbacks T select_first select_second
        ro_record_staged_message) F s) =
    wp (fs_run P \<bind> (\<lambda>x. ro_record_staged_message (select_first x) \<bind>
      (\<lambda>_. return (select_first x,select_second x)))) F s"
  by (rule fs_normalize_two_callbacks) (rule fs_record_extends)

lemma fs_normalize_callback_controls:
  assumes bound: "fs_query_bound q P"
    and member: "T \<in> set_dist (fs_normalize P)"
  shows "controlled_ro_program q
      (trace_root_stage (fs_replay_pair_attacker T select_first select_second A))"
    and "\<And>i bs. controlled_ro_program q
      (trace_fri_root_stage (fs_replay_pair_attacker T select_first select_second A) i bs)"
  using fs_two_callbacks_actual_controls[
    OF fs_normalize_bound[OF bound member] fs_normalize_fixed[OF member]]
  by blast+

lemma fs_normalize_two_callbacks_count:
  assumes ext: "\<And>x. hash_extension_preserving (gap x)"
  shows "dist_expect (fs_normalize P)
      (\<lambda>T. wp (fs_two_callbacks_count T select_first select_second gap) F s) =
    wp (fs_count_run P \<bind> (\<lambda>(x,n). gap (select_first x) \<bind>
      (\<lambda>_. return ((select_first x,select_second x),2*n)))) F s"
proof -
  have "dist_expect (fs_normalize P)
      (\<lambda>T. wp (fs_two_callbacks_count T select_first select_second gap) F s) =
    dist_expect (fs_normalize P) (\<lambda>T. wp (fs_count_run T \<bind>
      (\<lambda>(x,n). gap (select_first x) \<bind>
        (\<lambda>_. return ((select_first x,select_second x),2*n)))) F s)"
    by (rule fs_expect_cong; rule fs_two_callbacks_exact_count_wp)
      (auto intro: fs_normalize_fixed ext)
  also have "... = wp (fs_count_run P \<bind>
      (\<lambda>(x,n). gap (select_first x) \<bind>
        (\<lambda>_. return ((select_first x,select_second x),2*n)))) F s"
    by (simp only: wp_bind fs_normalize_count_wp)
  finally show ?thesis .
qed

subsection \<open>Reduction to fixed programs and an interleaved example\<close>

text \<open>
  The following lifting rule supplies no soundness estimate itself: its fixed
  program bound must still be proved. The full staged transcript reconstruction
  and global query-to-allowance relationship remain separate obligations.
\<close>

lemma fs_fixed_acceptance_suffices:
  assumes bound: "fs_query_bound q P"
    and fixed_bound: "\<And>T. fs_fixed T \<Longrightarrow> fs_query_bound q T \<Longrightarrow>
      fs_acceptance_probability T \<le> epsilon"
  shows "fs_acceptance_probability P \<le> epsilon"
proof -
  have "dist_expect (fs_normalize P) fs_acceptance_probability \<le> epsilon"
    by (rule fs_expect_le_const; rule fixed_bound)
      (auto intro: fs_normalize_fixed fs_normalize_bound[OF bound])
  then show ?thesis by (simp only: fs_normalize_acceptance)
qed

text \<open>
  Both the private distribution and the next query key may depend on the first
  oracle answer. Repeated keys are permitted. The example does not construct an
  accepting STARK proof.
\<close>

definition fs_interleaved_two_query where
  "fs_interleaved_two_query key choices next_key result =
    FS_Query key (\<lambda>y. FS_Sample (choices y) (\<lambda>seed.
      FS_Query (next_key y seed) (\<lambda>z. FS_Return (result y seed z))))"

lemma fs_interleaved_two_query_bound:
  "fs_query_bound 2 (fs_interleaved_two_query key choices next_key result)"
  unfolding fs_interleaved_two_query_def numeral_2_eq_2
  by (auto intro: fs_query_bound.intros)

lemma fs_interleaved_two_query_count:
  "fs_count_run (fs_interleaved_two_query key choices next_key result) =
    (hash key \<bind> (\<lambda>y. lift (\<lambda>_. choices y) \<bind> (\<lambda>seed.
      hash (next_key y seed) \<bind> (\<lambda>z. return (result y seed z,2)))))"
  by (simp add: fs_interleaved_two_query_def sm_bind_assoc numeral_2_eq_2)

lemma fs_interleaved_normalized_cap:
  assumes "T \<in> set_dist (fs_normalize
    (fs_interleaved_two_query key choices next_key result))"
  shows "fs_fixed T \<and> fs_query_bound 2 T"
  using fs_normalize_fixed[OF assms]
    fs_normalize_bound[OF fs_interleaved_two_query_bound assms] by blast

end

ML \<open>
  val fs_normalization_checked = @{thms fs_dist_bind_expect
    fs_expect_zero_iff
    fs_dist_bind_support
    fs_expect_const
    fs_expect_cong
    fs_expect_swap
    fs_expect_wp_swap
    fs_delta_support
    fs_dist_functions_support
    fs_dist_functions_marginal
    fs_private_domain
    fs_normalize_fixed
    fs_normalize_bound
    fs_dist_expect_ext
    fs_wp_ext
    fs_expect_le_const
    soundness.fs_normalize_count_wp
    soundness.fs_normalize_count
    soundness.fs_normalize_run
    soundness.fs_normalize_run_wp
    soundness.fs_normalize_follow_wp
    soundness.fs_normalize_acceptance
    soundness.fs_normalize_two_callbacks
    soundness.fs_normalize_two_callbacks_actual
    soundness.fs_normalize_callback_controls
    soundness.fs_normalize_two_callbacks_count
    soundness.fs_fixed_acceptance_suffices
    soundness.fs_interleaved_two_query_bound
    soundness.fs_interleaved_two_query_count
    soundness.fs_interleaved_normalized_cap};
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then ()
    else error "Unexpected normalization proof dependency") fs_normalization_checked;
  writeln ("Normalization checked conclusions: " ^
    Int.toString (length fs_normalization_checked));
\<close>

end
