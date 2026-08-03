(*  Title:      Stark/Prob_Dist.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Prob_Dist
  imports
    NNReal
    "HOL-Library.Monad_Syntax"
    "HOL-Library.FSet"
begin

section \<open>Probability Distributions\<close>

text \<open>
  This is a formalization of a datatype for finite probability distributions.

  The mathematical presentation uses finitely supported probability maps.  This
  gives a direct specification of distributions and bind: a distribution is a
  partial map whose domain is finite and whose weights sum to one, and bind
  computes the probability of a result by summing over the finite support of
  the first computation.

  The most direct code equation for bind is not executable for arbitrary result
  and state types, however.  The map operation @{const dom} needs to enumerate
  the support of a map, and Isabelle's generated code can only do that for
  types in the @{class enum} class.  Thus a purely map-based implementation of
  bind would impose an unwanted executability restriction on the types used by
  the monad.

  To avoid this, the theory keeps the map-based definitions as the abstract
  specification, but provides alternative executable equations in terms of
  finite sets.  The finite-set representation explicitly stores the support and
  weights, so generated code can iterate over those stored elements without
  requiring the underlying types to be enumerable.  This makes the executable
  version suitable for arbitrary result and state types.

  A previous list-based version has the same basic idea, but converting finite
  sets to lists in a canonical way requires an ordering on the element type, so
  that approach introduces a @{class linorder} constraint.  The finite-set
  implementation used here is therefore more general: it avoids both the
  @{class enum} constraint of map-domain enumeration and the @{class linorder}
  constraint of canonical list conversion.

  The theory also proofs monadic laws for probability distributions and registers the type as a BNF.
\<close>


subsection \<open>Finite Set Aggregation\<close>

subsubsection \<open>Finite set sums\<close>

lemma fsum_ffilter_neutral:
  assumes "\<And>x. x |\<in>| A \<Longrightarrow> \<not> P x \<Longrightarrow> f x = 0"
  shows "fsum f (ffilter P A) = fsum f A"
  unfolding fsum_fset_sum
  apply (rule sum.mono_neutral_left)
  using assms by auto

lemma fsum_ffilter_if:
  "fsum f (ffilter P A) = fsum (\<lambda>x. if P x then f x else 0) A"
proof -
  have "fsum f (ffilter P A) = (\<Sum>x\<in>{x \<in> fset A. P x}. f x)"
    apply (simp add: fsum_fset_sum)
    by (metis Collect_conj_eq Int_commute Collect_mem_eq)
  also have "... = (\<Sum>x\<in>fset A. if P x then f x else 0)"
    by (rule sum.inter_filter) simp
  also have "... = fsum (\<lambda>x. if P x then f x else 0) A"
    by (simp add: fsum_fset_sum)
  finally show ?thesis .
qed


subsubsection \<open>Summing pairs by key\<close>

definition sum_fset_x :: "'a \<Rightarrow> ('a \<times> 'w::comm_monoid_add) fset \<Rightarrow> 'w" where
  "sum_fset_x x xs = fsum snd (ffilter (\<lambda>p. fst p = x) xs)"

lemma sum_fset_x_notin_fst:
  assumes "x |\<notin>| fimage fst A"
  shows "sum_fset_x x A = 0"
proof -
  have "ffilter (\<lambda>p. fst p = x) A = {||}"
    using assms
    by (rule_tac fset_eqI) auto
  then show ?thesis
    unfolding sum_fset_x_def by (simp add: fsum_fset_sum)
qed

lemma sum_fset_x_unique:
  assumes uniq: "inj_on fst (fset A)"
  assumes mem: "(x, p) |\<in>| A"
  shows "sum_fset_x x A = p"
proof -
  have "ffilter (\<lambda>q. fst q = x) A = {|(x, p)|}"
    using uniq mem
    apply (rule_tac fset_eqI) apply (auto simp: inj_on_def) by fastforce
  then show ?thesis
    unfolding sum_fset_x_def
    by (simp add: fsum_fset_sum)
qed


subsubsection \<open>Squashing pairs by key\<close>

definition squish :: "('a \<times> 'w::comm_monoid_add) fset \<Rightarrow> ('a \<times> 'w) fset" where
  "squish xs = fimage (\<lambda>x. (x, sum_fset_x x xs)) (fimage fst xs)"

lemma squish_fst_unique:
  assumes "(x, p) |\<in>| squish A" "(x, q) |\<in>| squish A"
  shows "p = q"
  using assms unfolding squish_def by auto

lemma squish_inj_on_fst:
  "inj_on fst (fset (squish A))"
  unfolding squish_def inj_on_def
  by auto

lemma squish_id_if_inj_on_fst:
  assumes uniq: "inj_on fst (fset A)"
  shows "squish A = A"
proof (rule fset_eqI)
  fix z:: "'a \<times> 'b"
  obtain x p where z: "z = (x, p)"
    by (cases z)
  show "(z |\<in>| squish A) = (z |\<in>| A)"
  proof
    assume "z |\<in>| squish A"
    then obtain q where q: "(x, q) |\<in>| A" and p: "p = sum_fset_x x A"
      unfolding z squish_def by auto
    then have "sum_fset_x x A = q"
      using uniq by (simp add: sum_fset_x_unique)
    then show "z |\<in>| A"
      using q p unfolding z by simp
  next
    assume zA: "z |\<in>| A"
    then have "sum_fset_x x A = p"
      using uniq unfolding z by (simp add: sum_fset_x_unique)
    then show "z |\<in>| squish A"
      using zA unfolding z squish_def by force
  qed
qed

lemma fsum_squish:
  "fsum snd (squish A) = fsum snd A"
proof -
  have inj: "inj_on (\<lambda>x. (x, sum_fset_x x A)) (fst ` fset A)"
    by (auto intro!: inj_onI)

  have "fsum snd (squish A) =
        (\<Sum>x\<in>fst ` fset A. sum_fset_x x A)"
    unfolding squish_def
    apply (simp add: fsum_fset_sum fimage.rep_eq sum.reindex[OF inj] o_def)
    by (smt (verit) image_cong image_image inj split_pairs sum.reindex_cong)
  also have "... =
        (\<Sum>x\<in>fst ` fset A. \<Sum>p\<in>{p\<in>fset A. fst p = x}. snd p)"
    unfolding sum_fset_x_def
    apply (intro sum.cong refl) apply (simp add: fsum_fset_sum Int_def)
    by (metis (lifting) Collect_cong)
  also have "... = (\<Sum>p\<in>fset A. snd p)"
    by (rule sum.group) auto
  also have "... = fsum snd A"
    by (simp add: fsum_fset_sum)
  finally show ?thesis .
qed

subsection \<open>Probability Maps\<close>

subsubsection \<open>Summing probability maps\<close>

definition sum_map :: "('a \<rightharpoonup> nnreal) \<Rightarrow> nnreal" where
"sum_map f \<equiv> (\<Sum>i\<in>dom f. the (f i))"

type_synonym prob = nnreal

text \<open>
  Probability weights are represented by @{typ nnreal}: finite, non-negative
  real numbers.  Keeping non-negativity as a type invariant avoids carrying
  explicit @{term "0 \<le> p"} assumptions through sums, bind, map, expectation,
  and normalization proofs.

  Plain @{typ real} would admit negative weights, so every constructor and
  intermediate probability calculation would need extra invariants and proof
  obligations to rule them out.  Strictly positive reals are also not a good
  fit: the development needs a zero weight for absent probabilities, empty
  sums, pruning zero-mass outcomes, and intermediate aggregation before the
  stored support is normalized.

  The separate invariant on the distribution type below that excludes zero
  weights from the domain is therefore intentional.  The weight type supports
  zero where computations need it, while distributions store only the non-zero
  support.
\<close>

abbreviation some_map
where
  "some_map \<equiv> (let x=SOME x::'a. True in (Map.empty(x:=Some 1)))"

subsubsection \<open>Dirac delta distribution\<close>

definition delta_map :: "'a \<Rightarrow> 'a \<rightharpoonup> prob"
where
  "delta_map x = Map.empty(x:=Some 1)"

subsubsection \<open>Normalization\<close>

definition norm_fset :: "('a \<times> prob) fset \<Rightarrow> ('a \<times> prob) fset"
where
  "norm_fset xs =
    (if fsum snd xs = 0
   then {|(undefined, 1)|}
   else
    (let
      xs' = squish xs;
      q = fsum snd xs'
     in ffilter (\<lambda>p. snd p \<noteq> 0) (fimage (\<lambda>(x, p). (x, p / q)) xs')))"

subsubsection \<open>Maps from finite sets\<close>

definition map_of_val :: "('a \<times> 'b) fset \<Rightarrow> 'a \<Rightarrow> 'b" where
  "map_of_val A x =
    snd (fthe_elem (ffilter (\<lambda>p. fst p = x) A))"

definition map_of :: "('a \<times> 'b) fset \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "map_of A x =
    (if x |\<in>| fimage fst A then Some (map_of_val A x) else None)"

lemma dom_map_of_subset:
  "dom (map_of A) \<subseteq> fset (fimage fst A)"
  unfolding map_of_def
  by (auto split:if_split_asm)

lemma finite_dom_map_of[simp]:
  "finite (dom (map_of A))"
  using dom_map_of_subset[of A]
  by (meson finite_fset finite_subset)

lemma map_of_singleton:
  "map_of {|(x, y)|} = Map.empty(x := Some y)"
proof
  fix z
  show "map_of {|(x, y)|} z = (Map.empty(x := Some y)) z"
  proof (cases "z = x")
    case True
    have filt: "ffilter (\<lambda>p. fst p = x) {|(x, y)|} = {|(x, y)|}"
      by (rule fset_eqI) auto
    show ?thesis
      using True
      unfolding map_of_def map_of_val_def
      by (simp add: filt)
  next
    case False
    then show ?thesis
      unfolding map_of_def
      by simp
  qed
qed

lemma map_of_val_unique_key:
  assumes uniq: "\<And>y z. (x, y) |\<in>| A \<Longrightarrow> (x, z) |\<in>| A \<Longrightarrow> y = z"
  assumes mem: "(x, y) |\<in>| A"
  shows "map_of_val A x = y"
proof -
  have filt: "ffilter (\<lambda>p. fst p = x) A = {|(x, y)|}"
  proof (rule fset_eqI)
    fix p
    show "(p |\<in>| ffilter (\<lambda>p. fst p = x) A) = (p |\<in>| {|(x, y)|})"
    proof
      assume p: "p |\<in>| ffilter (\<lambda>p. fst p = x) A"
      then obtain z where p_eq: "p = (x, z)" and pA: "(x, z) |\<in>| A"
        by (cases p) auto
      have "z = y"
        using uniq[OF pA mem] .
      then show "p |\<in>| {|(x, y)|}"
        using p_eq by simp
    next
      assume "p |\<in>| {|(x, y)|}"
      then show "p |\<in>| ffilter (\<lambda>p. fst p = x) A"
        using mem by auto
    qed
  qed

  show ?thesis
    unfolding map_of_val_def
    by (simp add: filt)
qed

lemma map_of_nonzero_on_dom:
  assumes uniq: "\<And>x y z. (x, y) |\<in>| A \<Longrightarrow> (x, z) |\<in>| A \<Longrightarrow> y = z"
  assumes nonzero: "\<And>x p. (x, p) |\<in>| A \<Longrightarrow> p \<noteq> 0"
  assumes x: "x \<in> dom (map_of A)"
  shows "the (map_of A x) \<noteq> 0"
proof -
  from x have xin: "x |\<in>| fimage fst A"
    unfolding map_of_def by (auto split: if_splits)
  then obtain p where xp: "(x, p) |\<in>| A"
    by auto
  have "map_of_val A x = p"
    by (rule map_of_val_unique_key[OF uniq xp])
  then have "map_of A x = Some p"
    using xin unfolding map_of_def by simp
  then show ?thesis
    using nonzero[OF xp] by simp
qed

definition map_of_fset :: "('a \<times> prob) fset \<Rightarrow> 'a \<rightharpoonup> prob" where
  "map_of_fset A =
    (let q = fsum snd A in
       if q = 0 then Map.empty(undefined := Some 1)
       else map_of (norm_fset A))"

lemma finite_dom_map_of_fset: "finite (dom (map_of_fset A))"
  unfolding map_of_fset_def
  by (simp add: Let_def)

lemma norm_fset_fst_unique:
  assumes "(x, p) |\<in>| norm_fset A" "(x, q) |\<in>| norm_fset A"
  shows "p = q"
proof (cases "fsum snd A = 0")
  case True
  then show ?thesis
    using assms unfolding norm_fset_def by auto
next
  case False
  from assms False obtain r s where
    r: "(x, r) |\<in>| squish A" "p = r / fsum snd (squish A)"
    and s: "(x, s) |\<in>| squish A" "q = s / fsum snd (squish A)"
    unfolding norm_fset_def Let_def by auto
  then have "r = s"
    using squish_fst_unique by fast
  then show ?thesis
    using r s by simp
qed

lemma norm_fset_nonzero_snd:
  assumes "(x, p) |\<in>| norm_fset A"
  shows "p \<noteq> 0"
  using assms
  unfolding norm_fset_def
  by (auto simp: Let_def split: if_splits prod.splits)

lemma fsum_norm_fset:
  "fsum snd (norm_fset A) = 1"
proof (cases "fsum snd A = 0")
  case True
  then show ?thesis
    unfolding norm_fset_def by (simp add: fsum_fset_sum)
next
  case False
  define S where "S = squish A"
  define q where "q = fsum snd S"

  have q0: "q \<noteq> 0"
    using False fsum_squish unfolding S_def q_def apply simp
    by (simp add: fsum_squish)

  have norm:
    "norm_fset A =
      ffilter (\<lambda>p. snd p \<noteq> 0) (fimage (\<lambda>p. (fst p, snd p / q)) S)"
    using False unfolding norm_fset_def S_def q_def
    by (simp add: Let_def case_prod_unfold)

  have inj_norm: "inj_on (\<lambda>p. (fst p, snd p / q)) (fset S)"
  proof (rule inj_onI)
    fix a b
    assume aS: "a \<in> fset S" and bS: "b \<in> fset S"
      and eq: "(fst a, snd a / q) = (fst b, snd b / q)"
    obtain x p where a: "a = (x, p)" by (cases a)
    obtain y r where b: "b = (y, r)" by (cases b)
    from eq have xy: "x = y"
      by (simp add: a b)
    have "p = r"
      using squish_fst_unique[of x p A r] aS bS xy
      unfolding a b S_def by simp
    then show "a = b"
      using xy by (simp add: a b)
  qed

  have "fsum snd (norm_fset A) =
        fsum snd (ffilter (\<lambda>p. snd p \<noteq> 0) (fimage (\<lambda>p. (fst p, snd p / q)) S))"
    by (simp add: norm)
  also have "... = fsum snd (fimage (\<lambda>p. (fst p, snd p / q)) S)"
    by (rule fsum_ffilter_neutral) auto
  also have "... = fsum (\<lambda>p. snd p / q) S"
    using inj_norm
    by (simp add: fsum_fset_sum fimage.rep_eq sum.reindex o_def)
  also have "... = q / q"
    by (simp add: fsum_divide_nnreal q_def)
  also have "... = 1"
    by (rule divide_self[OF q0])
  finally show ?thesis .
qed

lemma norm_fset_singleton_1:
  "norm_fset {|(x, 1)|} = {|(x, 1::nnreal)|}"
proof -
  let ?A = "{|(x, 1::nnreal)|}"

  have total: "fsum snd ?A = 1"
    by (simp add: fsum_fset_sum)

  have sx: "sum_fset_x x ?A = 1"
    unfolding sum_fset_x_def
    by (simp add: fsum_fset_sum)

  have squish: "squish ?A = ?A"
  proof (rule fset_eqI)
    fix z
    show "(z |\<in>| squish ?A) = (z |\<in>| ?A)"
      unfolding squish_def
      using sx by auto
  qed

  have img:
    "fimage (\<lambda>(x, p). (x, p / fsum snd ?A)) (squish ?A) = ?A"
  proof (rule fset_eqI)
    fix z
    show "(z |\<in>| fimage (\<lambda>(x, p). (x, p / fsum snd ?A)) (squish ?A)) =
          (z |\<in>| ?A)"
      using total squish by auto
  qed

  show ?thesis
    unfolding norm_fset_def
    using total squish img
    apply (simp add: Let_def) by fastforce
qed

lemma sum_map_of:
  assumes uniq: "\<And>x y z. (x, y) |\<in>| A \<Longrightarrow> (x, z) |\<in>| A \<Longrightarrow> y = z"
  shows "sum_map (map_of A) = fsum snd A"
proof -
  have dom: "dom (map_of A) = fset (fimage fst A)"
    unfolding map_of_def apply auto
     apply (metis option.discI)
    by force

  have inj: "inj_on fst (fset A)"
  proof (rule inj_onI)
    fix p q
    assume pA: "p \<in> fset A" and qA: "q \<in> fset A" and fst: "fst p = fst q"
    obtain x y where p: "p = (x, y)" by (cases p)
    obtain z where q: "q = (x, z)"
      using fst p by (cases q) auto
    have "y = z"
      using uniq[of x y z] pA qA unfolding p q by simp
    then show "p = q"
      unfolding p q by simp
  qed

  have val: "p |\<in>| A \<Longrightarrow> the (map_of A (fst p)) = snd p" for p
  proof -
    assume pA: "p |\<in>| A"
    have filt: "ffilter (\<lambda>q. fst q = fst p) A = {|p|}"
    proof (rule fset_eqI)
      fix q
      show "(q |\<in>| ffilter (\<lambda>q. fst q = fst p) A) = (q |\<in>| {|p|})"
      proof
        assume qf: "q |\<in>| ffilter (\<lambda>q. fst q = fst p) A"
        then have qA: "q |\<in>| A" and fq: "fst q = fst p" by auto
        obtain x y where p: "p = (x, y)" by (cases p)
        obtain z where q: "q = (x, z)"
          using fq p by (cases q) auto
        have "z = y"
          using uniq[of x z y] qA pA unfolding p q by simp
        then show "q |\<in>| {|p|}"
          unfolding p q by simp
      next
        assume "q |\<in>| {|p|}"
        then show "q |\<in>| ffilter (\<lambda>q. fst q = fst p) A"
          using pA by auto
      qed
    qed
    then show ?thesis
      using pA unfolding map_of_def map_of_val_def by auto
  qed

  have "sum_map (map_of A) =
        (\<Sum>x\<in>fset (fimage fst A). the (map_of A x))"
    unfolding sum_map_def dom by simp
  also have "... = (\<Sum>p\<in>fset A. the (map_of A (fst p)))"
    using inj by (simp add: fimage.rep_eq sum.reindex)
  also have "... = (\<Sum>p\<in>fset A. snd p)"
    using val by (intro sum.cong) auto
  also have "... = fsum snd A"
    by (simp add: fsum_fset_sum)
  finally show ?thesis .
qed

lemma sum_map_1: "sum_map (map_of_fset A) = 1"
proof (cases "fsum snd A = 0")
  case True
  then show ?thesis
    unfolding map_of_fset_def sum_map_def by (simp add: Let_def)
next
  case False
  have "sum_map (map_of_fset A) = sum_map (map_of (norm_fset A))"
    using False unfolding map_of_fset_def by (simp add: Let_def)
  also have "... = fsum snd (norm_fset A)"
    by (rule sum_map_of) (rule norm_fset_fst_unique)
  also have "... = 1"
    by (rule fsum_norm_fset)
  finally show ?thesis .
qed

lemma map_of_fset_nonzero_on_dom:
  assumes "x \<in> dom (map_of_fset A)"
  shows "the (map_of_fset A x) \<noteq> 0"
proof (cases "fsum snd A = 0")
  case True
  then show ?thesis
    using assms unfolding map_of_fset_def by (simp add: Let_def)
next
  case False
  then have map_eq: "map_of_fset A = map_of (norm_fset A)"
    unfolding map_of_fset_def by (simp add: Let_def)
  show ?thesis
    unfolding map_eq
  proof (rule map_of_nonzero_on_dom)
    show "\<And>x y z. (x, y) |\<in>| norm_fset A \<Longrightarrow> (x, z) |\<in>| norm_fset A \<Longrightarrow> y = z"
      by (rule norm_fset_fst_unique)
    show "\<And>x p. (x, p) |\<in>| norm_fset A \<Longrightarrow> p \<noteq> 0"
      by (rule norm_fset_nonzero_snd)
    show "x \<in> dom (map_of (norm_fset A))"
      using assms map_eq by simp
  qed
qed

lemma delta_map_map_of_fset_singleton:
  "delta_map x = map_of_fset {|(x, 1)|}"
proof -
  let ?A = "{|(x, 1::nnreal)|}"

  have total: "fsum snd ?A = 1"
    by (simp add: fsum_fset_sum)

  have norm: "norm_fset ?A = ?A"
    by (rule norm_fset_singleton_1)

  have "map_of_fset ?A = map_of ?A"
    unfolding map_of_fset_def
    using total norm
    by (simp add: Let_def)

  also have "... = Map.empty(x := Some 1)"
    by (rule map_of_singleton)

  finally show ?thesis
    unfolding delta_map_def by simp
qed

abbreviation option_default where "option_default a \<equiv> case_option (0::nnreal) id a"

lemma option_default_if_zero[simp]:
  "option_default (if p = 0 then None else Some p) = p"
  by (cases "p = (0::nnreal)") simp_all

subsubsection \<open>Raw items\<close>

definition raw_items :: "('a \<rightharpoonup> prob) \<Rightarrow> ('a \<times> prob) set" where
  "raw_items f = image (\<lambda>x. (x, the (f x))) (dom f)"

subsection \<open>Probability distributions\<close>

typedef 'a dist =
  "{f. finite (dom f) \<and> sum_map f = 1 \<and> (\<forall>x\<in>dom f. the (f x) \<noteq> 0)}
    :: ('a \<rightharpoonup> prob) set"
  morphisms dist abs_dist
proof
  fix x::'a
  show "some_map \<in>
      {f. finite (dom f) \<and> sum_map f = 1 \<and> (\<forall>x\<in>dom f. the (f x) \<noteq> 0)}"
    unfolding sum_map_def by simp
qed

setup_lifting type_definition_dist

lemma norm_fset_inj_on_fst:
  "inj_on fst (fset (norm_fset A))"
proof (cases "fsum snd A = 0")
  case True
  then show ?thesis
  unfolding norm_fset_def by (simp add: inj_on_def)
next
  case False
  then show ?thesis
    using squish_inj_on_fst[of A]
    unfolding inj_on_def
    unfolding norm_fset_def apply (auto simp: Let_def split: prod.splits)
    by fastforce
qed

lift_definition dist_of_fset :: "('a \<times> prob) fset \<Rightarrow> 'a dist"
is map_of_fset
  by (auto simp add: finite_dom_map_of_fset sum_map_1 map_of_fset_nonzero_on_dom)

subsubsection \<open>Delta Distributions\<close>

definition delta_dist :: "'a \<Rightarrow> 'a dist"
  where "delta_dist x = dist_of_fset {|(x, 1)|}"

lemma dist_delta_dist:
  "dist (delta_dist x) = delta_map x"
  unfolding delta_dist_def
  by (simp add: dist_of_fset.rep_eq delta_map_map_of_fset_singleton)

subsubsection \<open>Uniform Distributions\<close>

definition dist_uniform :: "'a fset \<Rightarrow> 'a dist"
  where "dist_uniform xs = dist_of_fset ((\<lambda>x. (x, 1::prob)) |`| xs)"

lemma fsum_snd_uniform_ones:
  "fsum snd ((\<lambda>x. (x, 1::nnreal)) |`| xs) = nnreal (fcard xs)"
proof -
  have inj: "inj_on (\<lambda>x. (x, 1::nnreal)) (fset xs)"
    by (auto intro!: inj_onI)

  have "fsum snd ((\<lambda>x. (x, 1::nnreal)) |`| xs) =
      (\<Sum>x\<in>fset xs. (1::nnreal))"
    by (simp add: fsum_fset_sum fimage.rep_eq sum.reindex[OF inj] o_def)
  also have "... = nnreal (card (fset xs))"
    by (rule sum_1_nnreal) simp
  also have "... = nnreal (fcard xs)"
     by (metis fcard.rep_eq)
  finally show ?thesis .
qed

lemma norm_fset_uniform_ones:
  assumes "xs \<noteq> {||}"
  shows
    "norm_fset ((\<lambda>x. (x, 1::nnreal)) |`| xs) =
      ((\<lambda>x. (x, 1 / nnreal (fcard xs))) |`| xs)"
proof -
  let ?A = "((\<lambda>x. (x, 1::nnreal)) |`| xs)"
  let ?B = "((\<lambda>x. (x, 1 / nnreal (fcard xs))) |`| xs)"

  have total: "fsum snd ?A = nnreal (fcard xs)"
    by (rule fsum_snd_uniform_ones)

  have nonzero: "fsum snd ?A \<noteq> 0"
    using assms total by simp

  have inj: "inj_on fst (fset ?A)"
    by (auto simp: fimage.rep_eq inj_on_def)

  have squish_A: "squish ?A = ?A"
    by (rule squish_id_if_inj_on_fst[OF inj])

  have img:
    "fimage (\<lambda>(x, p). (x, p / fsum snd ?A)) ?A = ?B"
    using total
    by (rule_tac fset_eqI) (auto simp: fimage.rep_eq)

  have filt:
    "ffilter (\<lambda>p. snd p \<noteq> 0) ?B = ?B"
    using assms
    by (rule_tac fset_eqI) auto

  show ?thesis
    unfolding norm_fset_def
    using nonzero squish_A img filt
    by (simp add: Let_def)
qed

subsubsection \<open>Die\<close>

definition die :: "nat \<Rightarrow> nat dist"
  where "die n = dist_uniform (fset_of_list ([1..<Suc n]))"

subsubsection \<open>Coin\<close>

definition coin :: "prob \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a dist"
  where "coin f x y = dist_of_fset {|(x,f),(y,1-f)|}"

subsection \<open>Distribution Items\<close>

context
  includes fset.lifting
begin

lift_definition items :: "'a dist \<Rightarrow> ('a \<times> prob) fset"
is raw_items unfolding raw_items_def by simp

end

lemma map_of_val_unique:
  assumes uniq: "inj_on fst (fset A)"
  assumes mem: "(x, y) |\<in>| A"
  shows "map_of_val A x = y"
proof -
  have filt: "ffilter (\<lambda>p. fst p = x) A = {|(x, y)|}"
  proof (rule fset_eqI)
    fix p
    show "(p |\<in>| ffilter (\<lambda>p. fst p = x) A) = (p |\<in>| {|(x, y)|})"
    proof
      assume p: "p |\<in>| ffilter (\<lambda>p. fst p = x) A"
      then have pA: "p |\<in>| A" and fst_p: "fst p = x"
        by auto
      have "p = (x, y)"
        using uniq pA mem fst_p
        unfolding inj_on_def
        by fastforce
      then show "p |\<in>| {|(x, y)|}"
        by simp
    next
      assume "p |\<in>| {|(x, y)|}"
      then show "p |\<in>| ffilter (\<lambda>p. fst p = x) A"
        using mem by auto
    qed
  qed

  show ?thesis
    unfolding map_of_val_def
    by (simp add: filt)
qed

lemma raw_items_map_of_unique:
  assumes uniq: "inj_on fst (fset A)"
  shows "raw_items (map_of A) = fset A"
proof
  show "raw_items (map_of A) \<subseteq> fset A"
  proof
    fix z
    assume z: "z \<in> raw_items (map_of A)"
    then obtain x where
      xdom: "x \<in> dom (map_of A)"
      and z_eq: "z = (x, the (map_of A x))"
      unfolding raw_items_def by auto

    from xdom have xin: "x |\<in>| fimage fst A"
      unfolding map_of_def by (auto split: if_splits)

    then obtain y where xy: "(x, y) |\<in>| A"
      by auto

    have "the (map_of A x) = y"
      using xin map_of_val_unique[OF uniq xy]
      unfolding map_of_def by simp

    then show "z \<in> fset A"
      using z_eq xy by simp
  qed
next
  show "fset A \<subseteq> raw_items (map_of A)"
  proof
    fix z
    assume zA: "z \<in> fset A"
    obtain x y where z_eq: "z = (x, y)"
      by (cases z)

    have xy: "(x, y) |\<in>| A"
      using zA z_eq by simp

    have xin: "x |\<in>| fimage fst A"
      using xy apply auto by force

    have map_x: "map_of A x = Some y"
      using xin map_of_val_unique[OF uniq xy]
      unfolding map_of_def by simp

    then have "x \<in> dom (map_of A)"
      by auto

    moreover have "z = (x, the (map_of A x))"
      using z_eq map_x by simp

    ultimately show "z \<in> raw_items (map_of A)"
      unfolding raw_items_def by auto
  qed
qed

lemma raw_items_map_of_fset:
  "raw_items (map_of_fset xs) = fset (norm_fset xs)"
proof (cases "fsum snd xs = 0")
  case True
  then show ?thesis
    unfolding raw_items_def map_of_fset_def norm_fset_def
    by (simp add: Let_def)
next
  case False
  have "raw_items (map_of_fset xs) = raw_items (map_of (norm_fset xs))"
    using False
    unfolding map_of_fset_def
    by (simp add: Let_def)
  also have "... = fset (norm_fset xs)"
    by (rule raw_items_map_of_unique) (rule norm_fset_inj_on_fst)
  finally show ?thesis .
qed

lemma fset_eq_transfer_aux[transfer_rule]:
  "Transfer.Rel
    (rel_fun (pcr_fset (rel_prod (=) (=)))
      (rel_fun (rel_fset (rel_prod (=) (=))) (=)))
    (\<lambda>a b. a = fset b) (=)"
  unfolding rel_fun_def
  by (simp add: Rel_def cr_fset_def fset.pcr_cr_eq fset.rel_eq fset_cong prod.rel_eq)

definition sum_fset_by ::
  "'a \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> prob) \<Rightarrow> 'i fset \<Rightarrow> prob"
where
  "sum_fset_by x key weight I =
    fsum weight (ffilter (\<lambda>i. key i = x) I)"

definition map_of_fset_by ::
  "('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> prob) \<Rightarrow> 'i fset \<Rightarrow> 'a \<rightharpoonup> prob"
where
  "map_of_fset_by key weight I =
    (let q = fsum weight I in
      if q = 0 then Map.empty(undefined := Some 1)
      else (\<lambda>x.
        let p = sum_fset_by x key weight I / q
        in if p = 0 then None else Some p))"

lemma fsum_by_total:
  "fsum (\<lambda>x. sum_fset_by x key weight I) (fimage key I) = fsum weight I"
proof -
  have "fsum (\<lambda>x. sum_fset_by x key weight I) (fimage key I) =
    (\<Sum>x\<in>key ` fset I. \<Sum>i\<in>{i \<in> fset I. key i = x}. weight i)"
    unfolding sum_fset_by_def
    apply (simp add: fsum_fset_sum fimage.rep_eq)
    by (metis Int_commute Collect_conj_eq Collect_mem_eq)
  also have "... = (\<Sum>i\<in>fset I. weight i)"
    apply (rule sum.group) by auto
  also have "... = fsum weight I"
    by (simp add: fsum_fset_sum)
  finally show ?thesis .
qed

lemma finite_dom_map_of_fset_by[simp]:
  "finite (dom (map_of_fset_by key weight I))"
proof -
  have "dom (map_of_fset_by key weight I) \<subseteq> fset (fimage key I) \<union> {undefined}"
    unfolding map_of_fset_by_def sum_fset_by_def
    apply (auto simp: Let_def fsum_fset_sum)
    by (metis ffmember_filter[of _ "\<lambda>uub. key uub = _" I] filter_fset[of "\<lambda>uub. key uub = _" I] image_iff[of _ key "fset I"] option.discI[of None]
        sum.not_neutral_contains_not_neutral[of weight "fset (ffilter (\<lambda>uub. key uub = _) I)"])
  then show ?thesis
    by (simp add: finite_subset)
qed

lemma sum_fset_by_notin:
  assumes "x \<notin> fset (fimage key I)"
  shows "sum_fset_by x key weight I = 0"
  using assms
  unfolding sum_fset_by_def
  apply (simp add: fsum_fset_sum fimage.rep_eq)
  by (smt (verit) Int_emptyI image_iff mem_Collect_eq nnreal_0 sum.empty)

lemma dom_map_of_fset_by:
  assumes q: "fsum weight I \<noteq> 0"
  shows
    "dom (map_of_fset_by key weight I) =
      {x \<in> fset (fimage key I). sum_fset_by x key weight I \<noteq> 0}"
proof
  show "dom (map_of_fset_by key weight I)
      \<subseteq> {x \<in> fset (fimage key I). sum_fset_by x key weight I \<noteq> 0}"
  proof
    fix x
    assume x: "x \<in> dom (map_of_fset_by key weight I)"
    then have nz: "sum_fset_by x key weight I \<noteq> 0"
      using q
      unfolding map_of_fset_by_def
      by (auto simp: Let_def split: if_splits)

    moreover have "x \<in> fset (fimage key I)"
      using nz sum_fset_by_notin[of x key I weight]
      by blast

    ultimately show "x \<in> {x \<in> fset (fimage key I). sum_fset_by x key weight I \<noteq> 0}"
      by simp
  qed
next
  show "{x \<in> fset (fimage key I). sum_fset_by x key weight I \<noteq> 0}
      \<subseteq> dom (map_of_fset_by key weight I)"
    using q
    unfolding map_of_fset_by_def
    by (auto simp: Let_def)
qed

lemma sum_map_map_of_fset_by[simp]:
  "sum_map (map_of_fset_by key weight I) = 1"
proof (cases "fsum weight I = 0")
  case True
  then show ?thesis
    unfolding map_of_fset_by_def sum_map_def
    by simp
next
  case False
  let ?q = "fsum weight I"
  let ?S = "{x \<in> fset (fimage key I). sum_fset_by x key weight I \<noteq> 0}"

  have dom: "dom (map_of_fset_by key weight I) = ?S"
    using False by (rule dom_map_of_fset_by)

  have val:
    "\<And>x. x \<in> ?S \<Longrightarrow>
      the (map_of_fset_by key weight I x) =
      sum_fset_by x key weight I / ?q"
    using False
    unfolding map_of_fset_by_def
    by (auto simp: Let_def)

  have "sum_map (map_of_fset_by key weight I) =
      (\<Sum>x\<in>?S. the (map_of_fset_by key weight I x))"
    unfolding sum_map_def dom by simp
  also have "... =
      (\<Sum>x\<in>?S. sum_fset_by x key weight I / ?q)"
    by (intro sum.cong refl val)
  also have "... =
      (\<Sum>x\<in>fset (fimage key I). sum_fset_by x key weight I / ?q)"
    apply (rule sum.mono_neutral_left)
      apply simp
     apply auto
    done
  also have "... =
      (\<Sum>x\<in>fset (fimage key I). sum_fset_by x key weight I) / ?q"
    by (rule sum_divide_nnreal) simp
  also have "... = ?q / ?q"
    using fsum_by_total[of key weight I]
    by (simp add: fsum_fset_sum)
  also have "... = 1"
    by (rule divide_self[OF False])
  finally show ?thesis .
qed


definition squish_by ::
  "('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> prob) \<Rightarrow> 'i fset \<Rightarrow> ('a \<times> prob) fset"
where
  "squish_by key weight I =
    fimage (\<lambda>x. (x, sum_fset_by x key weight I)) (fimage key I)"

definition dist_of_fset_by ::
  "('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> prob) \<Rightarrow> 'i fset \<Rightarrow> 'a dist"
where
  "dist_of_fset_by key weight I =
    dist_of_fset (squish_by key weight I)"

lemma fimage_fst_squish_by[simp]:
  "fimage fst (squish_by key weight I) = fimage key I"
  unfolding squish_by_def
  by (rule fset_eqI) auto

lemma squish_by_inj_on_fst:
  "inj_on fst (fset (squish_by key weight I))"
  unfolding squish_by_def inj_on_def
  by auto

lemma fsum_snd_squish_by:
  "fsum snd (squish_by key weight I) = fsum weight I"
proof -
  have inj:
    "inj_on (\<lambda>x. (x, sum_fset_by x key weight I)) (fset (fimage key I))"
    by (auto intro!: inj_onI)

  have "fsum snd (squish_by key weight I) =
    fsum (\<lambda>x. sum_fset_by x key weight I) (fimage key I)"
    unfolding squish_by_def
    apply (simp add: fsum_fset_sum fimage.rep_eq sum.reindex[OF inj] o_def)
    by (smt (verit) fset.set_map image_cong image_image inj sndI sum.reindex_cong)
  also have "... = fsum weight I"
    by (rule fsum_by_total)
  finally show ?thesis .
qed

lemma sum_fset_x_squish_by:
  "sum_fset_x x (squish_by key weight I) = sum_fset_by x key weight I"
proof (cases "x |\<in>| fimage key I")
  case True
  then have "(x, sum_fset_by x key weight I) |\<in>| squish_by key weight I"
    unfolding squish_by_def by auto
  then show ?thesis
    using squish_by_inj_on_fst
    by (metis squish_by_inj_on_fst \<open>(x, sum_fset_by x key weight I) |\<in>| squish_by key weight I\<close> sum_fset_x_unique)
next
  case False
  then show ?thesis
    using sum_fset_x_notin_fst[of x "squish_by key weight I"]
      sum_fset_by_notin[of x key I weight]
    by simp
qed

lemma norm_fset_squish_by_1:
  assumes total: "fsum weight I = 1"
  shows
    "norm_fset (squish_by key weight I) =
      ffilter (\<lambda>p. snd p \<noteq> 0) (squish_by key weight I)"
proof -
  let ?A = "squish_by key weight I"

  have total_A: "fsum snd ?A = 1"
    using total by (simp add: fsum_snd_squish_by)

  have squish_A: "squish ?A = ?A"
    by (rule squish_id_if_inj_on_fst) (rule squish_by_inj_on_fst)

  have div_A: "fimage (\<lambda>(x, p). (x, p / fsum snd ?A)) ?A = ?A"
    using total_A
    by (rule_tac fset_eqI) auto

  show ?thesis
    unfolding norm_fset_def
    by (simp add: total_A squish_A div_A Let_def)
qed

lemma map_of_filtered_unique:
  assumes uniq: "inj_on fst (fset A)"
  shows
    "map_of (ffilter (\<lambda>p. snd p \<noteq> 0) A) x =
      (if sum_fset_x x A = 0 then None else Some (sum_fset_x x A))"
proof (cases "x |\<in>| fimage fst A")
  case False
  then have sx: "sum_fset_x x A = 0"
    by (rule sum_fset_x_notin_fst)
  moreover have "x |\<notin>| fimage fst (ffilter (\<lambda>p. snd p \<noteq> 0) A)"
    using False by auto
  ultimately show ?thesis
    unfolding map_of_def by simp
next
  case True
  then obtain p where pA: "(x, p) |\<in>| A"
    by auto
  have sx: "sum_fset_x x A = p"
    using uniq pA by (rule sum_fset_x_unique)

  show ?thesis
  proof (cases "p = 0")
    case True
    have "x |\<notin>| fimage fst (ffilter (\<lambda>p. snd p \<noteq> 0) A)"
      using uniq pA True
      apply (auto simp: inj_on_def) by fastforce
    then show ?thesis
      using sx True unfolding map_of_def by simp
  next
    case False
    have filt:
      "ffilter (\<lambda>q. fst q = x) (ffilter (\<lambda>p. snd p \<noteq> 0) A) = {|(x, p)|}"
      using uniq pA False
      apply (rule_tac fset_eqI) apply (auto simp: inj_on_def) by fastforce
    have xin: "x |\<in>| fimage fst (ffilter (\<lambda>p. snd p \<noteq> 0) A)"
      using pA False apply auto by force
    have val:
      "map_of_val (ffilter (\<lambda>p. snd p \<noteq> 0) A) x = p"
      unfolding map_of_val_def
      by (simp add: filt)
    show ?thesis
      using sx False xin val
      unfolding map_of_def by simp
  qed
qed

lemma map_of_fset_squish_by_1:
  assumes total: "fsum weight I = 1"
  shows "map_of_fset (squish_by key weight I) = map_of_fset_by key weight I"
proof
  fix x
  let ?A = "squish_by key weight I"

  have total_A: "fsum snd ?A = 1"
    using total by (simp add: fsum_snd_squish_by)

  have "map_of_fset ?A x =
    map_of (ffilter (\<lambda>p. snd p \<noteq> 0) ?A) x"
    unfolding map_of_fset_def
    using total_A norm_fset_squish_by_1[OF total]
    apply simp by (rule arg_cong2)
  also have "... =
    (if sum_fset_x x ?A = 0 then None else Some (sum_fset_x x ?A))"
    by (rule map_of_filtered_unique) (rule squish_by_inj_on_fst)
  also have "... =
    (if sum_fset_by x key weight I = 0 then None else Some (sum_fset_by x key weight I))"
    by (simp add: sum_fset_x_squish_by)
  also have "... = map_of_fset_by key weight I x"
    using total
    unfolding map_of_fset_by_def
    by simp
  finally show "map_of_fset ?A x = map_of_fset_by key weight I x" .
qed

lemma dist_of_fset_by_rep_eq_1:
  assumes total: "fsum weight I = 1"
  shows "dist (dist_of_fset_by key weight I) = map_of_fset_by key weight I"
  unfolding dist_of_fset_by_def dist_of_fset.rep_eq
  using map_of_fset_squish_by_1[OF total] .

lemma sum_fset_by_id:
  "sum_fset_by x id weight I = (if x |\<in>| I then weight x else 0)"
  unfolding sum_fset_by_def fsum_fset_sum
  by (simp add: ffilter.rep_eq)

lemma dist_of_fset_by_id_apply:
  assumes total: "fsum weight I = 1"
  shows "dist (dist_of_fset_by id weight I) x =
    (let p = (if x |\<in>| I then weight x else 0) in
      if p = 0 then None else Some p)"
  using dist_of_fset_by_rep_eq_1[OF total, of id] total
  by (simp add: map_of_fset_by_def sum_fset_by_id)


lemma sum_map_dist[simp]:
  "sum_map (dist d) = 1"
  by transfer simp

lemma finite_dom_dist[simp]:
  "finite (dom (dist d))"
  by transfer simp

lemma dist_nonzero_on_dom[simp]:
  assumes "x \<in> dom (dist d)"
  shows "the (dist d x) \<noteq> 0"
  using assms by transfer simp

lemma fset_items:
  "fset (items d) = (\<lambda>x. (x, the (dist d x))) ` dom (dist d)"
  apply transfer apply (simp add: raw_items_def)
  by (metis fset.rep_transfer Rel_def)

lemma fsum_items:
  "fsum h (items d) = (\<Sum>x\<in>dom (dist d). h (x, the (dist d x)))"
proof -
  have inj: "inj_on (\<lambda>x. (x, the (dist d x))) (dom (dist d))"
    by (auto intro!: inj_onI)
  show ?thesis
    unfolding fsum_fset_sum fset_items
    by (subst sum.reindex[OF inj]) simp
qed

lemma fsum_items_key:
  "fsum (\<lambda>xp. if fst xp = x then snd xp else 0) (items d) =
    option_default (dist d x)"
  unfolding fsum_items
  apply simp
  using id_apply by fastforce

lemma fsum_snd_items[simp]:
  "fsum snd (items d) = 1"
  unfolding fsum_items sum_map_def apply simp
  by (metis sum_map_def sum_map_dist)

lemma fsum_fbind_fimage_Pair:
  "fsum h (fbind A (\<lambda>a. fimage (\<lambda>b. (a, b)) (B a))) =
    fsum (\<lambda>a. fsum (\<lambda>b. h (a, b)) (B a)) A"
proof -
  have set_eq:
    "fset (fbind A (\<lambda>a. fimage (\<lambda>b. (a, b)) (B a))) =
      (SIGMA a:fset A. fset (B a))"
    by (auto simp: fbind.rep_eq fimage.rep_eq Set.bind_def)

  have "sum h (SIGMA a:fset A. fset (B a)) =
    (\<Sum>a\<in>fset A. \<Sum>b\<in>fset (B a). h (a, b))"
    by (subst sum.Sigma) auto
  then show ?thesis
    unfolding fsum_fset_sum
    by (simp add: set_eq)
qed

lemma fsum_fbind_fimage_Pair_right:
  "fsum h (fbind A (\<lambda>a. fimage (\<lambda>b. (b, a)) (B a))) =
    fsum (\<lambda>a. fsum (\<lambda>b. h (b, a)) (B a)) A"
proof -
  have set_eq:
    "fset (fbind A (\<lambda>a. fimage (\<lambda>b. (b, a)) (B a))) =
      (\<Union>a\<in>fset A. (\<lambda>b. (b, a)) ` fset (B a))"
    by (auto simp: fbind.rep_eq fimage.rep_eq Set.bind_def)
  have "sum h (\<Union>a\<in>fset A. (\<lambda>b. (b, a)) ` fset (B a)) =
    (\<Sum>a\<in>fset A. sum h ((\<lambda>b. (b, a)) ` fset (B a)))"
    by (subst sum.UNION_disjoint) auto
  also have "... = (\<Sum>a\<in>fset A. \<Sum>b\<in>fset (B a). h (b, a))"
    by (intro sum.cong refl, subst sum.reindex) (auto simp: inj_on_def)
  finally have sum_eq:
    "sum h (\<Union>a\<in>fset A. (\<lambda>b. (b, a)) ` fset (B a)) =
      (\<Sum>a\<in>fset A. \<Sum>b\<in>fset (B a). h (b, a))" .
  then show ?thesis
    unfolding fsum_fset_sum
    by (simp add: set_eq)
qed

lemma sum_fset_by_bind_items:
  "sum_fset_by x
      (\<lambda>(ms, ks). fst ks)
      (\<lambda>(ms, ks). snd ms * snd ks)
      (fbind (items d) (\<lambda>ms.
        case ms of ((a, s'), p) \<Rightarrow>
          fimage (\<lambda>ks. (ms, ks)) (items (k a s')))) =
    (\<Sum>i\<in>dom (dist d).
      the (dist d i) * option_default (dist (k (fst i) (snd i)) x))"
  unfolding sum_fset_by_def
  apply (simp add: fsum_ffilter_if fsum_fbind_fimage_Pair case_prod_unfold)
  unfolding fsum_items
  apply (intro sum.cong refl)
  apply (simp add: fsum_mult_left_nnreal fsum_items_key)
  by (simp add: dom_def option.case_eq_if)

lemma fsum_items_mult_left:
  "fsum (\<lambda>x. c * snd x) (items d) = c"
proof -
  have "fsum (\<lambda>x. c * snd x) (items d) =
    c * fsum snd (items d)"
    by (rule fsum_mult_left_nnreal)
  also have "... = c"
    by simp
  finally show ?thesis .
qed

lemma fsum_bind_items_total:
  "fsum
      (\<lambda>(ms, ks). snd ms * snd ks)
      (fbind (items d) (\<lambda>ms.
        case ms of ((a, s'), p) \<Rightarrow>
          fimage (\<lambda>ks. (ms, ks)) (items (k a s')))) = 1"
proof -
  have "fsum
      (\<lambda>(ms, ks). snd ms * snd ks)
      (fbind (items d) (\<lambda>ms.
        case ms of ((a, s'), p) \<Rightarrow>
          fimage (\<lambda>ks. (ms, ks)) (items (k a s')))) =
    fsum
      (\<lambda>ms. fsum (\<lambda>ks. snd ms * snd ks)
        (items (k (fst (fst ms)) (snd (fst ms)))))
      (items d)"
    by (simp add: fsum_fbind_fimage_Pair case_prod_unfold)

  also have "... = fsum snd (items d)"
    by (intro fsum.cong refl) (simp add: fsum_items_mult_left)

  also have "... = 1"
    by simp

  finally show ?thesis .
qed

subsection \<open>Mapper\<close>

definition dist_map:: "('a \<Rightarrow> 'b) \<Rightarrow> 'a dist \<Rightarrow> 'b dist"
where
  "dist_map f a = dist_of_fset_by (f \<circ> fst) snd (items a)"

definition set_dist :: "'a dist \<Rightarrow> 'a set"
where
  "set_dist d = dom (dist d)"

lemma set_dist_dist_of_fset_by_id_subset:
  assumes total: "fsum weight I = 1"
  shows "set_dist (dist_of_fset_by id weight I) \<subseteq> fset I"
  using dist_of_fset_by_id_apply[OF total]
  unfolding set_dist_def
  by (auto simp: Let_def split: if_splits)

subsection \<open>Relator\<close>

definition rel_dist :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a dist \<Rightarrow> 'b dist \<Rightarrow> bool"
where
  "rel_dist R p q \<longleftrightarrow>
    (\<exists>r :: ('a \<times> 'b) dist.
      set_dist r \<subseteq> {(x, y). R x y} \<and>
      dist_map fst r = p \<and>
      dist_map snd r = q)"

lemma nnreal_mult_div_cancel:
  fixes a b :: nnreal
  assumes "b \<noteq> 0"
  shows "a * b / b = a"
  using assms by transfer simp

subsection \<open>BNF Setup\<close>

definition glue_items ::
  "('a \<times> 'b) dist \<Rightarrow> ('b \<times> 'c) dist \<Rightarrow>
    ((('a \<times> 'b) \<times> prob) \<times> (('b \<times> 'c) \<times> prob)) fset"
where
  "glue_items p q =
    fbind (items p)
      (\<lambda>ab. fimage (\<lambda>bc. (ab, bc))
        (ffilter (\<lambda>bc. snd (fst ab) = fst (fst bc)) (items q)))"

definition glue_weight ::
  "('a \<times> 'b) dist \<Rightarrow>
    ((('a \<times> 'b) \<times> prob) \<times> (('b \<times> 'c) \<times> prob)) \<Rightarrow> prob"
where
  "glue_weight p x =
    snd (fst x) * snd (snd x) /
      the (dist (dist_map snd p) (snd (fst (fst x))))"

definition glue_key ::
  "((('a \<times> 'b) \<times> prob) \<times> (('b \<times> 'c) \<times> prob)) \<Rightarrow> 'a \<times> 'c"
where
  "glue_key x = (fst (fst (fst x)), snd (fst (snd x)))"

definition glue_source ::
  "('a \<times> 'b) dist \<Rightarrow> ('b \<times> 'c) dist \<Rightarrow>
    ((('a \<times> 'b) \<times> prob) \<times> (('b \<times> 'c) \<times> prob)) dist"
where
  "glue_source p q = dist_of_fset_by id (glue_weight p) (glue_items p q)"

definition glue_dist :: "('a \<times> 'b) dist \<Rightarrow> ('b \<times> 'c) dist \<Rightarrow> ('a \<times> 'c) dist"
where
  "glue_dist p q = dist_map glue_key (glue_source p q)"

lemma dist_map_rep_eq:
  "dist (dist_map f d) = map_of_fset_by (f \<circ> fst) snd (items d)"
  unfolding dist_map_def
  by (rule dist_of_fset_by_rep_eq_1) simp

lemma sum_fset_by_items:
  "sum_fset_by x (f \<circ> fst) snd (items d) =
    (\<Sum>y\<in>{y \<in> dom (dist d). f y = x}. the (dist d y))"
proof -
  let ?g = "\<lambda>y. (y, the (dist d y))"
  let ?S = "{y \<in> dom (dist d). f y = x}"
  have inj: "inj_on ?g {y \<in> dom (dist d). f y = x}"
    by (auto intro!: inj_onI)
  have filt:
    "{i \<in> ?g ` dom (dist d). (f \<circ> fst) i = x} =
      ?g ` {y \<in> dom (dist d). f y = x}"
    by auto
  have set_eq:
    "{i. (f \<circ> fst) i = x} \<inter> fset (items d) = ?g ` ?S"
    by (auto simp: fset_items)
  have "sum snd ({i. (f \<circ> fst) i = x} \<inter> fset (items d)) =
      sum snd (?g ` ?S)"
    using set_eq by simp
  also have "... = (\<Sum>y\<in>?S. snd (?g y))"
    by (simp add: sum.reindex[OF inj])
  also have "... = (\<Sum>y\<in>?S. the (dist d y))"
    by simp
  finally have sum_eq:
    "sum snd ({i. (f \<circ> fst) i = x} \<inter> fset (items d)) =
      (\<Sum>y\<in>?S. the (dist d y))" .
  have set_eq':
    "{i. i |\<in>| items d \<and> (f \<circ> fst) i = x} = ?g ` ?S"
    by (auto simp: fset_items)
  have sum_eq':
    "(\<Sum>i | i |\<in>| items d \<and> (f \<circ> fst) i = x. snd i) =
      (\<Sum>y\<in>?S. the (dist d y))"
    using set_eq' by (simp add: sum.reindex[OF inj])
  show ?thesis
    unfolding sum_fset_by_def fsum_fset_sum
    using sum_eq by (simp add: ffilter.rep_eq Int_def)
qed

lemma dist_map_apply:
  "dist (dist_map f d) x =
    (let p = (\<Sum>y\<in>{y \<in> dom (dist d). f y = x}. the (dist d y))
     in if p = 0 then None else Some p)"
proof -
  have total: "fsum snd (items d) \<noteq> 0"
    by simp
  show ?thesis
    unfolding dist_map_rep_eq map_of_fset_by_def sum_fset_by_items
    using total by (simp add: Let_def)
qed

lemma fsum_items_filter_dist_map:
  "fsum snd (ffilter (\<lambda>i. f (fst i) = x) (items d)) =
    (\<Sum>y\<in>{y \<in> dom (dist d). f y = x}. the (dist d y))"
  using sum_fset_by_items[of x f d]
  by (simp add: sum_fset_by_def comp_def)

lemma fsum_items_filter_dist_map_on_dom:
  assumes "x \<in> dom (dist (dist_map f d))"
  shows "fsum snd (ffilter (\<lambda>i. f (fst i) = x) (items d)) =
    the (dist (dist_map f d) x)"
proof -
  let ?p = "(\<Sum>y\<in>{y \<in> dom (dist d). f y = x}. the (dist d y))"
  have "dist (dist_map f d) x = Some ?p"
    using assms by (simp add: dist_map_apply Let_def domIff split: if_splits)
  then show ?thesis
    by (simp add: fsum_items_filter_dist_map)
qed

lemma dist_map_dist_of_fset_by_id_apply:
  assumes total: "fsum weight I = 1"
  shows "dist (dist_map f (dist_of_fset_by id weight I)) x =
    (let p = fsum weight (ffilter (\<lambda>i. f i = x) I)
     in if p = 0 then None else Some p)"
proof -
  let ?d = "dist_of_fset_by id weight I"
  let ?D = "{y \<in> fset I. weight y \<noteq> 0}"
  let ?S = "{y \<in> dom (dist ?d). f y = x}"
  let ?T = "{y \<in> fset I. f y = x}"
  have T_eq: "?T = {i. f i = x} \<inter> fset I"
    by auto
  have dom_eq: "dom (dist ?d) = ?D"
    using dist_of_fset_by_id_apply[OF total]
    by (auto simp: Let_def split: if_splits)
  have sum_eq:
    "(\<Sum>y\<in>?S. the (dist ?d y)) = (\<Sum>y\<in>?T. weight y)"
  proof -
    have "(\<Sum>y\<in>?S. the (dist ?d y)) = (\<Sum>y\<in>{y \<in> ?T. weight y \<noteq> 0}. weight y)"
      using dist_of_fset_by_id_apply[OF total]
      by (intro sum.cong) (auto simp: dom_eq Let_def split: if_splits)
    also have "... = (\<Sum>y\<in>?T. weight y)"
      by (rule sum.mono_neutral_left) auto
    finally show ?thesis .
  qed
  show ?thesis
    unfolding dist_map_apply fsum_fset_sum
    using sum_eq by (simp add: ffilter.rep_eq Let_def T_eq)
qed

lemma set_dist_dist_map:
  "set_dist (dist_map f d) = f ` set_dist d"
proof -
  have sum_nonzero:
    "(\<Sum>y\<in>{y \<in> dom (dist d). f y = f x}. the (dist d y)) \<noteq> 0"
    if x: "x \<in> dom (dist d)" for x
  proof -
    let ?S = "{y \<in> dom (dist d). f y = f x}"
    have fin: "finite ?S"
      by simp
    have xS: "x \<in> ?S"
      using x by simp
    moreover have "0 < the (dist d x)"
      using x by simp
    ultimately show ?thesis
      using sum_pos2[OF fin xS, of "\<lambda>y. the (dist d y)"]
      by auto
  qed

  show ?thesis
  proof
    show "set_dist (dist_map f d) \<subseteq> f ` set_dist d"
    proof
      fix z
      assume z: "z \<in> set_dist (dist_map f d)"
      let ?S = "{y \<in> dom (dist d). f y = z}"
      have fin: "finite ?S"
        by simp
      have p_ne: "(\<Sum>y\<in>?S. the (dist d y)) \<noteq> 0"
        using z unfolding set_dist_def dist_map_apply
        by (auto simp: Let_def split: if_splits)
      have "\<exists>y. y \<in> ?S"
      proof (rule ccontr)
        assume "\<not> (\<exists>y. y \<in> ?S)"
        then have "?S = {}"
          by auto
        then show False
          using p_ne by (metis sum.empty)
      qed
      then obtain y where y: "y \<in> ?S"
        by blast
      then show "z \<in> f ` set_dist d"
        unfolding set_dist_def by auto
    qed
  next
    show "f ` set_dist d \<subseteq> set_dist (dist_map f d)"
    proof
      fix z
      assume "z \<in> f ` set_dist d"
      then obtain x where x: "x \<in> dom (dist d)" and z: "z = f x"
        unfolding set_dist_def by auto
      have "(\<Sum>y\<in>{y \<in> dom (dist d). f y = z}. the (dist d y)) \<noteq> 0"
        using sum_nonzero[OF x] z by simp
      then show "z \<in> set_dist (dist_map f d)"
        unfolding set_dist_def dist_map_apply
        by (simp add: Let_def domIff)
    qed
  qed
qed

lemma fsum_glue_weight_inner:
  fixes p :: "('a \<times> 'b) dist" and q :: "('b \<times> 'c) dist"
  assumes mid: "dist_map snd p = dist_map fst q"
    and ab: "ab |\<in>| items p"
  shows "fsum (\<lambda>bc. glue_weight p (ab, bc))
    (ffilter (\<lambda>bc. snd (fst ab) = fst (fst bc)) (items q)) = snd ab"
proof -
  let ?b = "snd (fst ab)"
  let ?den = "the (dist (dist_map snd p) ?b)"
  have fst_ab_dom: "fst ab \<in> dom (dist p)"
    using ab by (auto simp: fset_items)
  have b_dom: "?b \<in> dom (dist (dist_map snd p))"
    using fst_ab_dom set_dist_dist_map[of snd p]
    unfolding set_dist_def by auto
  then have den_ne: "?den \<noteq> 0"
    by simp
  have sum_q:
    "fsum snd (ffilter (\<lambda>bc. fst (fst bc) = ?b) (items q)) = ?den"
    using fsum_items_filter_dist_map_on_dom[of ?b fst q] mid b_dom
    by simp
  have "fsum (\<lambda>bc. glue_weight p (ab, bc))
    (ffilter (\<lambda>bc. snd (fst ab) = fst (fst bc)) (items q)) =
    fsum (\<lambda>bc. snd ab * snd bc / ?den)
      (ffilter (\<lambda>bc. fst (fst bc) = ?b) (items q))"
    unfolding glue_weight_def by (simp add: eq_commute)
  also have "... =
    snd ab * fsum snd (ffilter (\<lambda>bc. fst (fst bc) = ?b) (items q)) / ?den"
    by (simp add: fsum_divide_nnreal fsum_mult_left_nnreal)
  also have "... = snd ab"
    using sum_q den_ne by (simp add: nnreal_mult_div_cancel)
  finally show ?thesis .
qed

lemma fsum_glue_weight_inner_left:
  fixes p :: "('a \<times> 'b) dist" and q :: "('b \<times> 'c) dist"
  assumes mid: "dist_map snd p = dist_map fst q"
    and bc: "bc |\<in>| items q"
  shows "fsum (\<lambda>ab. glue_weight p (ab, bc))
    (ffilter (\<lambda>ab. snd (fst ab) = fst (fst bc)) (items p)) = snd bc"
proof -
  let ?b = "fst (fst bc)"
  let ?den = "the (dist (dist_map snd p) ?b)"
  have fst_bc_dom: "fst bc \<in> dom (dist q)"
    using bc by (auto simp: fset_items)
  have b_dom_q: "?b \<in> dom (dist (dist_map fst q))"
    using fst_bc_dom set_dist_dist_map[of fst q]
    unfolding set_dist_def by auto
  then have b_dom_p: "?b \<in> dom (dist (dist_map snd p))"
    using mid by simp
  then have den_ne: "?den \<noteq> 0"
    by simp
  have sum_p:
    "fsum snd (ffilter (\<lambda>ab. snd (fst ab) = ?b) (items p)) = ?den"
    using fsum_items_filter_dist_map_on_dom[of ?b snd p] b_dom_p
    by simp
  have "fsum (\<lambda>ab. glue_weight p (ab, bc))
    (ffilter (\<lambda>ab. snd (fst ab) = fst (fst bc)) (items p)) =
    fsum (\<lambda>ab. snd bc * snd ab / ?den)
      (ffilter (\<lambda>ab. snd (fst ab) = ?b) (items p))"
    unfolding glue_weight_def by (simp add: mult.commute)
  also have "... =
    snd bc * fsum snd (ffilter (\<lambda>ab. snd (fst ab) = ?b) (items p)) / ?den"
    by (simp add: fsum_divide_nnreal fsum_mult_left_nnreal)
  also have "... = snd bc"
    using sum_p den_ne by (simp add: nnreal_mult_div_cancel)
  finally show ?thesis .
qed

lemma glue_items_commute:
  "glue_items p q =
    fbind (items q)
      (\<lambda>bc. fimage (\<lambda>ab. (ab, bc))
        (ffilter (\<lambda>ab. snd (fst ab) = fst (fst bc)) (items p)))"
  unfolding glue_items_def
  by (rule fset_eqI) (auto simp: fbind.rep_eq fimage.rep_eq Set.bind_def)

lemma fsum_glue_weight:
  fixes p :: "('a \<times> 'b) dist" and q :: "('b \<times> 'c) dist"
  assumes mid: "dist_map snd p = dist_map fst q"
  shows "fsum (glue_weight p) (glue_items p q) = 1"
proof -
  have "fsum (glue_weight p) (glue_items p q) =
    fsum (\<lambda>ab. fsum (\<lambda>bc. glue_weight p (ab, bc))
      (ffilter (\<lambda>bc. snd (fst ab) = fst (fst bc)) (items q))) (items p)"
    unfolding glue_items_def
    by (simp add: fsum_fbind_fimage_Pair)
  also have "... = fsum snd (items p)"
    by (intro fsum.cong refl) (simp add: fsum_glue_weight_inner[OF mid])
  also have "... = 1"
    by simp
  finally show ?thesis .
qed

lemma fsum_glue_weight_fst:
  fixes p :: "('a \<times> 'b) dist" and q :: "('b \<times> 'c) dist"
  assumes mid: "dist_map snd p = dist_map fst q"
  shows "fsum (glue_weight p)
      (ffilter (\<lambda>i. fst (glue_key i) = a) (glue_items p q)) =
    fsum snd (ffilter (\<lambda>ab. fst (fst ab) = a) (items p))"
proof -
  have "fsum (glue_weight p)
      (ffilter (\<lambda>i. fst (glue_key i) = a) (glue_items p q)) =
    fsum (\<lambda>ab. fsum (\<lambda>bc.
        if fst (fst ab) = a then glue_weight p (ab, bc) else 0)
      (ffilter (\<lambda>bc. snd (fst ab) = fst (fst bc)) (items q))) (items p)"
    unfolding glue_items_def
    by (simp add: fsum_ffilter_if fsum_fbind_fimage_Pair glue_key_def)
  also have "... = fsum (\<lambda>ab. if fst (fst ab) = a then snd ab else 0) (items p)"
  proof (intro fsum.cong refl)
    fix ab
    assume ab: "ab |\<in>| items p"
    show "fsum (\<lambda>bc. if fst (fst ab) = a then glue_weight p (ab, bc) else 0)
        (ffilter (\<lambda>bc. snd (fst ab) = fst (fst bc)) (items q)) =
      (if fst (fst ab) = a then snd ab else 0)"
    proof (cases "fst (fst ab) = a")
      case True
      then show ?thesis
        using fsum_glue_weight_inner[OF mid ab] by simp
    next
      case False
      then show ?thesis
        by (simp add: fsum_fset_sum)
    qed
  qed
  also have "... = fsum snd (ffilter (\<lambda>ab. fst (fst ab) = a) (items p))"
    by (simp add: fsum_ffilter_if)
  finally show ?thesis .
qed

lemma fsum_glue_weight_snd:
  fixes p :: "('a \<times> 'b) dist" and q :: "('b \<times> 'c) dist"
  assumes mid: "dist_map snd p = dist_map fst q"
  shows "fsum (glue_weight p)
      (ffilter (\<lambda>i. snd (glue_key i) = c) (glue_items p q)) =
    fsum snd (ffilter (\<lambda>bc. snd (fst bc) = c) (items q))"
proof -
  have "fsum (glue_weight p)
      (ffilter (\<lambda>i. snd (glue_key i) = c) (glue_items p q)) =
    fsum (\<lambda>bc. fsum (\<lambda>ab.
        if snd (fst bc) = c then glue_weight p (ab, bc) else 0)
      (ffilter (\<lambda>ab. snd (fst ab) = fst (fst bc)) (items p))) (items q)"
    unfolding glue_items_commute
    by (simp add: fsum_ffilter_if fsum_fbind_fimage_Pair_right glue_key_def)
  also have "... = fsum (\<lambda>bc. if snd (fst bc) = c then snd bc else 0) (items q)"
  proof (intro fsum.cong refl)
    fix bc
    assume bc: "bc |\<in>| items q"
    show "fsum (\<lambda>ab. if snd (fst bc) = c then glue_weight p (ab, bc) else 0)
        (ffilter (\<lambda>ab. snd (fst ab) = fst (fst bc)) (items p)) =
      (if snd (fst bc) = c then snd bc else 0)"
    proof (cases "snd (fst bc) = c")
      case True
      then show ?thesis
        using fsum_glue_weight_inner_left[OF mid bc] by simp
    next
      case False
      then show ?thesis
        by (simp add: fsum_fset_sum)
    qed
  qed
  also have "... = fsum snd (ffilter (\<lambda>bc. snd (fst bc) = c) (items q))"
    by (simp add: fsum_ffilter_if)
  finally show ?thesis .
qed

lemma dist_map_id:
  "dist_map id = id"
proof (rule ext, rule dist_inject[THEN iffD1], rule ext)
  fix d::"'a dist" and x::'a
  show "dist.dist (dist_map id d) x = dist.dist (id d) x"
  proof (cases "x \<in> dom (dist d)")
    case True
    have S: "{y \<in> dom (dist d). id y = x} = {x}"
      using True by auto
    have D: "dist d x = Some (the (dist d x))"
      using True by auto
    have NZ: "the (dist d x) \<noteq> 0"
      using True by simp
    have "dist (dist_map id d) x =
      (let p = (\<Sum>y\<in>{y \<in> dom (dist d). id y = x}. the (dist d y))
       in if p = 0 then None else Some p)"
      by (rule dist_map_apply)
    also have "... = Some (the (dist d x))"
      using S NZ by simp
    also have "... = dist d x"
      using D by simp
    finally show ?thesis by simp
  next
    case False
    have S: "{y \<in> dom (dist d). id y = x} = {}"
      using False by auto
    have S': "{y. y = x \<and> y \<in> dom (dist d)} = {}"
      using False by auto
    have p0: "(\<Sum>y | y = x \<and> y \<in> dom (dist d). the (dist d y)) = 0"
      by (simp add: S')
    have D: "dist d x = None"
      using False by auto
    have "dist (dist_map id d) x =
      (let p = (\<Sum>y\<in>{y \<in> dom (dist d). id y = x}. the (dist d y))
       in if p = 0 then None else Some p)"
      by (rule dist_map_apply)
    also have "... = None"
      using S S' p0 by simp
    also have "... = dist d x"
      using D by simp
    finally show ?thesis by simp
  qed
qed

lemma dist_map_delta_dist[simp]:
  "dist_map f (delta_dist x) = delta_dist (f x)"
proof (rule dist_inject[THEN iffD1], rule ext)
  fix y
  show "dist (dist_map f (delta_dist x)) y = dist (delta_dist (f x)) y"
  proof (cases "f x = y")
    case True
    have "{z \<in> dom (dist (delta_dist x)). f z = y} = {x}"
      using True by (auto simp: dist_delta_dist delta_map_def)
    then show ?thesis
      using True by (simp add: dist_map_apply dist_delta_dist delta_map_def)
  next
    case False
    have "{z \<in> dom (dist (delta_dist x)). f z = y} = {}"
      using False by (auto simp: dist_delta_dist delta_map_def)
    then show ?thesis
      using False by (simp add: dist_map_apply dist_delta_dist delta_map_def)
  qed
qed

lemma dist_map_cong:
  assumes "\<And>x. x \<in> set_dist d \<Longrightarrow> f x = g x"
  shows "dist_map f d = dist_map g d"
proof (rule dist_inject[THEN iffD1], rule ext)
  fix y
  have "{x \<in> dom (dist d). f x = y} = {x \<in> dom (dist d). g x = y}"
    using assms unfolding set_dist_def by (auto simp: domIff)
  then show "dist (dist_map f d) y = dist (dist_map g d) y"
    by (simp add: dist_map_apply)
qed

lemma sum_partition_by_image:
  fixes w :: "'a \<Rightarrow> nnreal"
  assumes fin: "finite M"
  shows
    "(\<Sum>y\<in>{y \<in> f ` M. g y = x}. \<Sum>z\<in>{z \<in> M. f z = y}. w z) =
     (\<Sum>z\<in>{z \<in> M. g (f z) = x}. w z)"
proof -
  let ?Y = "{y \<in> f ` M. g y = x}"
  have finY: "finite ?Y"
    using fin by simp
  have finM: "finite M"
    by (rule fin)
  have filter_sum:
    "(\<Sum>z\<in>{z \<in> M. f z = y}. w z) =
     (\<Sum>z\<in>M. if f z = y then w z else 0)" for y
  proof -
    have "(\<Sum>z\<in>M. if f z = y then w z else 0) =
      (\<Sum>z\<in>{z \<in> M. f z = y}. w z)"
      using fin
      by (intro sum.mono_neutral_cong_right) auto
    then show ?thesis by simp
  qed

  have "(\<Sum>y\<in>?Y. \<Sum>z\<in>{z \<in> M. f z = y}. w z) =
    (\<Sum>y\<in>?Y. \<Sum>z\<in>M. if f z = y then w z else 0)"
    by (rule sum.cong) (simp_all add: filter_sum)
  also have "... =
    (\<Sum>z\<in>M. \<Sum>y\<in>?Y. if f z = y then w z else 0)"
    by (rule sum.swap)
  also have "... =
    (\<Sum>z\<in>M. if g (f z) = x then w z else 0)"
  proof (intro sum.cong refl)
    fix z
    assume z: "z \<in> M"
    show "(\<Sum>y\<in>?Y. if f z = y then w z else 0) =
      (if g (f z) = x then w z else 0)"
    proof (cases "g (f z) = x")
      case True
      then have fz: "f z \<in> ?Y"
        using z by simp
      have "(\<Sum>y\<in>?Y. if f z = y then w z else 0) =
        (\<Sum>y\<in>?Y. if y = f z then w z else 0)"
        by (intro sum.cong refl) simp
      also have "... = w z"
        using finY fz by (simp)
      finally show ?thesis
        using True by simp
    next
      case False
      then have "\<And>y. y \<in> ?Y \<Longrightarrow> f z \<noteq> y"
        by auto
      then show ?thesis
        using False by simp
    qed
  qed
  also have "... = (\<Sum>z\<in>{z \<in> M. g (f z) = x}. w z)"
    using finM by (rule sum.inter_filter[symmetric])
  finally show ?thesis .
qed

lemma dist_map_comp:
  "dist_map (g \<circ> f) = dist_map g \<circ> dist_map f"
proof (rule ext)
  fix d
  show "dist_map (g \<circ> f) d = (dist_map g \<circ> dist_map f) d"
  proof (rule dist_inject[THEN iffD1], rule ext)
  fix x
  let ?M = "dom (dist d)"
  let ?lhs = "(\<Sum>y\<in>{y \<in> dom (dist (dist_map f d)). g y = x}.
      the (dist (dist_map f d) y))"
  let ?rhs = "(\<Sum>z\<in>{z \<in> ?M. (g \<circ> f) z = x}. the (dist d z))"

  have dom_map: "dom (dist (dist_map f d)) = f ` ?M"
    using set_dist_dist_map[of f d]
    unfolding set_dist_def by simp

  have lhs_sum:
    "?lhs =
      (\<Sum>y\<in>{y \<in> f ` ?M. g y = x}.
        \<Sum>z\<in>{z \<in> ?M. f z = y}. the (dist d z))"
  proof -
    have Aeq:
      "{y \<in> dom (dist (dist_map f d)). g y = x} =
      {y \<in> f ` ?M. g y = x}"
      by (simp add: dom_map)
    show ?thesis
      unfolding Aeq
  proof (intro sum.cong refl)
    fix y
    assume "y \<in> {y \<in> f ` ?M. g y = x}"
    then have y_dom: "y \<in> dom (dist (dist_map f d))"
      by (simp add: dom_map)
    have nz:
      "(\<Sum>z\<in>{z \<in> ?M. f z = y}. the (dist d z)) \<noteq> 0"
      using y_dom unfolding dist_map_apply
      by (auto simp: Let_def split: if_splits)
    have "dist (dist_map f d) y =
      Some (\<Sum>z\<in>{z \<in> ?M. f z = y}. the (dist d z))"
      unfolding dist_map_apply using nz by simp
    then show "the (dist (dist_map f d) y) =
      (\<Sum>z\<in>{z \<in> ?M. f z = y}. the (dist d z))"
      by simp
  qed
  qed

  have part:
    "(\<Sum>y\<in>{y \<in> f ` ?M. g y = x}.
        \<Sum>z\<in>{z \<in> ?M. f z = y}. the (dist d z)) =
     (\<Sum>z\<in>{z \<in> ?M. g (f z) = x}. the (dist d z))"
    by (rule sum_partition_by_image) simp
  have sums_eq: "?lhs = ?rhs"
    using lhs_sum part by (simp add: comp_def)

  have left:
    "dist (dist_map (\<lambda>z. g (f z)) d) x =
      (let p = ?rhs in if p = 0 then None else Some p)"
    by (simp add: dist_map_apply)
  have right:
    "dist (dist_map g (dist_map f d)) x =
      (let p = ?lhs in if p = 0 then None else Some p)"
    by (simp add: dist_map_apply)

  show "dist (dist_map (g \<circ> f) d) x =
    dist ((dist_map g \<circ> dist_map f) d) x"
    unfolding comp_def
    using left right sums_eq by simp
  qed
qed

lemma dist_map_fst_glue_dist:
  fixes p :: "('a \<times> 'b) dist" and q :: "('b \<times> 'c) dist"
  assumes mid: "dist_map snd p = dist_map fst q"
  shows "dist_map fst (glue_dist p q) = dist_map fst p"
proof (rule dist_inject[THEN iffD1], rule ext)
  fix a
  have total: "fsum (glue_weight p) (glue_items p q) = 1"
    by (rule fsum_glue_weight[OF mid])
  have comp_fst:
    "dist_map fst (glue_dist p q) = dist_map (fst \<circ> glue_key) (glue_source p q)"
    unfolding glue_dist_def
    by (metis comp_apply dist_map_comp)
  have left:
    "dist (dist_map fst (glue_dist p q)) a =
      (let s = fsum (glue_weight p)
          (ffilter (\<lambda>i. fst (glue_key i) = a) (glue_items p q))
       in if s = 0 then None else Some s)"
    unfolding comp_fst glue_source_def
    using dist_map_dist_of_fset_by_id_apply[OF total, of "fst \<circ> glue_key" a]
    by (simp add: comp_def)
  have right:
    "dist (dist_map fst p) a =
      (let s = fsum snd (ffilter (\<lambda>ab. fst (fst ab) = a) (items p))
       in if s = 0 then None else Some s)"
    by (simp add: dist_map_apply fsum_items_filter_dist_map[symmetric])
  show "dist (dist_map fst (glue_dist p q)) a = dist (dist_map fst p) a"
    using left right fsum_glue_weight_fst[OF mid, of a] by simp
qed

lemma dist_map_snd_glue_dist:
  fixes p :: "('a \<times> 'b) dist" and q :: "('b \<times> 'c) dist"
  assumes mid: "dist_map snd p = dist_map fst q"
  shows "dist_map snd (glue_dist p q) = dist_map snd q"
proof (rule dist_inject[THEN iffD1], rule ext)
  fix c
  have total: "fsum (glue_weight p) (glue_items p q) = 1"
    by (rule fsum_glue_weight[OF mid])
  have comp_snd:
    "dist_map snd (glue_dist p q) = dist_map (snd \<circ> glue_key) (glue_source p q)"
    unfolding glue_dist_def
    by (metis comp_apply dist_map_comp)
  have left:
    "dist (dist_map snd (glue_dist p q)) c =
      (let s = fsum (glue_weight p)
          (ffilter (\<lambda>i. snd (glue_key i) = c) (glue_items p q))
       in if s = 0 then None else Some s)"
    unfolding comp_snd glue_source_def
    using dist_map_dist_of_fset_by_id_apply[OF total, of "snd \<circ> glue_key" c]
    by (simp add: comp_def)
  have right:
    "dist (dist_map snd q) c =
      (let s = fsum snd (ffilter (\<lambda>bc. snd (fst bc) = c) (items q))
       in if s = 0 then None else Some s)"
    by (simp add: dist_map_apply fsum_items_filter_dist_map[symmetric])
  show "dist (dist_map snd (glue_dist p q)) c = dist (dist_map snd q) c"
    using left right fsum_glue_weight_snd[OF mid, of c] by simp
qed

lemma set_dist_glue_dist_subset:
  fixes p :: "('a \<times> 'b) dist" and q :: "('b \<times> 'c) dist"
  assumes mid: "dist_map snd p = dist_map fst q"
    and Rp: "set_dist p \<subseteq> {(a, b). R a b}"
    and Sq: "set_dist q \<subseteq> {(b, c). S b c}"
  shows "set_dist (glue_dist p q) \<subseteq> {(a, c). (R OO S) a c}"
proof
  fix ac
  assume ac: "ac \<in> set_dist (glue_dist p q)"
  let ?src = "glue_source p q"
  have total: "fsum (glue_weight p) (glue_items p q) = 1"
    by (rule fsum_glue_weight[OF mid])
  obtain x where x_src: "x \<in> set_dist ?src" and ac_x: "ac = glue_key x"
    using ac set_dist_dist_map[of glue_key ?src]
    unfolding glue_dist_def by auto
  have x_I: "x \<in> fset (glue_items p q)"
    using x_src set_dist_dist_of_fset_by_id_subset[OF total]
    unfolding glue_source_def by auto
  then obtain ab bc where x: "x = (ab, bc)"
    and ab: "ab |\<in>| items p"
    and bc: "bc |\<in>| items q"
    and match: "snd (fst ab) = fst (fst bc)"
    unfolding glue_items_def
    by (auto simp: fbind.rep_eq fimage.rep_eq Set.bind_def)
  have ab_supp: "fst ab \<in> set_dist p"
    using ab unfolding set_dist_def by (auto simp: fset_items)
  have bc_supp: "fst bc \<in> set_dist q"
    using bc unfolding set_dist_def by (auto simp: fset_items)
  show "ac \<in> {(a, c). (R OO S) a c}"
    using Rp Sq ab_supp bc_supp match ac_x
    unfolding x glue_key_def
    by (cases "fst ab"; cases "fst bc"; auto)
qed

lemma rel_dist_OO:
  "(rel_dist R OO rel_dist S) \<le> rel_dist (R OO S)"
proof
  fix x z
  assume "(rel_dist R OO rel_dist S) x z"
  then obtain y where xy: "rel_dist R x y" and yz: "rel_dist S y z"
    by auto
  obtain p where pR: "set_dist p \<subseteq> {(a, b). R a b}"
    and p_fst: "dist_map fst p = x"
    and p_snd: "dist_map snd p = y"
    using xy unfolding rel_dist_def by auto
  obtain q where qS: "set_dist q \<subseteq> {(b, c). S b c}"
    and q_fst: "dist_map fst q = y"
    and q_snd: "dist_map snd q = z"
    using yz unfolding rel_dist_def by auto
  have mid: "dist_map snd p = dist_map fst q"
    using p_snd q_fst by simp
  have "rel_dist (R OO S) x z"
    unfolding rel_dist_def
  proof (intro exI conjI)
    show "set_dist (glue_dist p q) \<subseteq> {(a, c). (R OO S) a c}"
      by (rule set_dist_glue_dist_subset[OF mid pR qS])
    show "dist_map fst (glue_dist p q) = x"
      using dist_map_fst_glue_dist[OF mid] p_fst by simp
    show "dist_map snd (glue_dist p q) = z"
      using dist_map_snd_glue_dist[OF mid] q_snd by simp
  qed
  then show "rel_dist (R OO S) x z" .
qed

bnf dist: "'a dist"
  map: dist_map
  sets: set_dist
  bd: natLeq
  wits: delta_dist
  rel: rel_dist
proof -
  show "dist_map id = id"
    by (rule dist_map_id)
next
  show "\<And>f g. dist_map (g \<circ> f) = dist_map g \<circ> dist_map f"
    by (rule dist_map_comp)
next
  show "\<And>x f g. (\<And>z. z \<in> set_dist x \<Longrightarrow> f z = g z) \<Longrightarrow> dist_map f x = dist_map g x"
    by (rule dist_map_cong)
next
  show "\<And>f. set_dist \<circ> dist_map f = (`) f \<circ> set_dist"
    by (simp add: fun_eq_iff set_dist_dist_map)
next
  show "card_order natLeq"
    by (rule natLeq_card_order)
next
  show "BNF_Cardinal_Arithmetic.cinfinite natLeq"
    by (rule natLeq_cinfinite)
next
  show "regularCard natLeq"
    by (rule regularCard_natLeq)
next
  show "\<And>x. ordLess2 (card_of (set_dist x)) natLeq"
    unfolding set_dist_def
    by (simp add: finite_iff_ordLess_natLeq[symmetric])
next
  show "\<And>R S. rel_dist R OO rel_dist S \<le> rel_dist (R OO S)"
    by (rule rel_dist_OO)
next
  show "\<And>R. rel_dist R =
      (\<lambda>x y. \<exists>z. set_dist z \<subseteq> {(x, y). R x y} \<and>
        dist_map fst z = x \<and> dist_map snd z = y)"
    by (auto simp: fun_eq_iff rel_dist_def)
next
  show "\<And>b z. b \<in> set_dist (delta_dist z) \<Longrightarrow> b = z"
    unfolding set_dist_def by (simp add: dist_delta_dist delta_map_def)
qed

subsection \<open>Code Generator Setup\<close>

text \<open>
  We implement distributions using finite sets of key-value pairs.
  Note that we use a code datatype here since we want to use a different datatype for implementation
  as the raw datatype which was used to define the type.
\<close>

code_datatype dist_of_fset

lemma delta_dist_code[code]:
  "delta_dist x = dist_of_fset {|(x, 1)|}"
  unfolding delta_dist_def by simp

declare [[code drop: squish]]

lemma squish_code[code]:
  "squish xs = fbind (fimage fst xs) (\<lambda>x. {|(x, sum_fset_x x xs)|})"
  unfolding squish_def
  by (rule fset_eqI) (auto simp: fbind.rep_eq fimage.rep_eq Set.bind_def)

lemma dist_code[code]: "dist (dist_of_fset A) = (let q = fsum snd A in
       if q = 0 then Map.empty(undefined := Some 1)
       else map_of (norm_fset A))"
  by (simp add: dist_of_fset.rep_eq map_of_fset_def)

lemma dist_uniform_code[code]:
  "dist_uniform xs = dist_of_fset ((\<lambda>x. (x, 1::prob)) |`| xs)"
  unfolding dist_uniform_def by simp

lemma items_code[code]:
  "items (dist_of_fset xs) = norm_fset xs"
  apply transfer_start
       apply transfer_step
      apply transfer_step
     apply transfer_step
    apply (rule fset_eq_transfer_aux)
   apply transfer_step
  apply transfer_end
  by (rule raw_items_map_of_fset)

declare [[code drop: squish_by]]

lemma squish_by_code[code]:
  "squish_by key weight I =
    fbind (fimage key I) (\<lambda>x. {|(x, sum_fset_by x key weight I)|})"
  unfolding squish_by_def
  by (rule fset_eqI) (auto simp: fbind.rep_eq fimage.rep_eq Set.bind_def)

subsubsection \<open>Examples\<close>
thm eq_transfer
instantiation dist::(type) equal
begin
lift_definition equal_dist::"'a dist \<Rightarrow> 'a dist \<Rightarrow> bool"
is "(=)" .
instance by (intro_classes, transfer, simp)
end

lemma eq_fset_set_transfer:
  assumes "bi_unique A"
  shows "Transfer.Rel (rel_fun (pcr_fset A) (rel_fun (pcr_fset A) (=))) (=) (=)"
  using assms FSet.fset.bi_unique eq_transfer
  unfolding Transfer.Rel_def
  by blast

lemma eq_iff_raw_items_eq:
  fixes a b
  assumes "finite (dom a) \<and> sum_map a = 1 \<and> (\<forall>x\<in>dom a. the (a x) \<noteq> 0)"
      and "finite (dom b) \<and> sum_map b = 1 \<and> (\<forall>x\<in>dom b. the (b x) \<noteq> 0)"
    shows "(a = b) = (raw_items a = raw_items b)"
proof
  assume "a = b"
  then show "raw_items a = raw_items b"
    by simp
next
  assume raw_eq: "raw_items a = raw_items b"
  show "a = b"
  proof
    fix x
    show "a x = b x"
    proof (cases "x \<in> dom a")
      case True
      then have "(x, the (a x)) \<in> raw_items a"
        unfolding raw_items_def by blast
      then have "(x, the (a x)) \<in> raw_items b"
        using raw_eq by simp
      then have "x \<in> dom b" "the (a x) = the (b x)"
        unfolding raw_items_def by auto
      then show ?thesis
        using True by (cases "a x"; cases "b x") auto
    next
      case False
      show ?thesis
      proof (cases "x \<in> dom b")
        case True
        then have "(x, the (b x)) \<in> raw_items b"
          unfolding raw_items_def by blast
        then have "(x, the (b x)) \<in> raw_items a"
          using raw_eq by simp
        then have "x \<in> dom a"
          unfolding raw_items_def by auto
        then show ?thesis
          using False by simp
      next
        case False
        then show ?thesis
          using \<open>x \<notin> dom a\<close> by (simp add: domIff)
      qed
    qed
  qed
qed

lemma equal_dist_code[code]:
  "equal_class.equal a b = (items a = items b)"
  apply transfer_start
         apply transfer_step
        apply transfer_step
       apply (rule eq_fset_set_transfer)
       apply transfer_step
      apply transfer_step
     apply transfer_step
    apply transfer_step
  apply transfer_step
  apply transfer_end
  by (rule eq_iff_raw_items_eq)

lemma
  "dist_of_fset {|(True, 1), (False, 1), (False, 1)|}
  = dist_of_fset {|(True, 0.5), (False, 0.5)|}"
  by eval

lemma
  "dist_of_fset {|(1::nat, 1), (2, 1), (2, 1)|}
    = dist_of_fset {|(1::nat, 1), (2, 1), (2, 1)|}"
  by eval

lemma "dist_uniform {|1,2,3::nat|} = dist_of_fset {|(1, 1), (2, 1), (3, 1)|}"
  by eval

lemma
  "delta_dist (True) = dist_of_fset {|(True, 1)|}"
  by eval

lemma "coin 0.5 (1::nat) 0 = dist_of_fset ({|(1, (1 / 2)), (0, (1 / 2))|})"
  by eval

lemma "die 6 = dist_of_fset {|(1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1)|}"
  by eval

end
