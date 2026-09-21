(*  Title:      Stark/Hash_Monad.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Hash_Monad
  imports Main Prob_Monad "HOL-Library.Finite_Map" "HOL.Enum"
begin

section \<open>Finite Map setup\<close>

definition fmap_of_fun :: "('a::finite \<Rightarrow> 'b option) \<Rightarrow> ('a, 'b) fmap" where
  "fmap_of_fun f = Abs_fmap f"
lemma fmlookup_fmap_of_fun[simp]:
  "fmlookup (fmap_of_fun f) = f"
  unfolding fmap_of_fun_def
  by (simp add: Abs_fmap_inverse)
lemma fmap_of_fun_fmlookup[simp]:
  "fmap_of_fun (fmlookup m) = m"
  by (rule fmap_ext) simp

instantiation fmap :: (enum, enum) enum
begin
definition enum_fmap :: "('a, 'b) fmap list" where
  "enum_fmap = map fmap_of_fun (enum_class.enum :: ('a \<Rightarrow> 'b option) list)"
definition enum_all_fmap :: "(('a, 'b) fmap \<Rightarrow> bool) \<Rightarrow> bool" where
  "enum_all_fmap P =
     enum_class.enum_all (\<lambda>f :: 'a \<Rightarrow> 'b option. P (fmap_of_fun f))"
definition enum_ex_fmap :: "(('a, 'b) fmap \<Rightarrow> bool) \<Rightarrow> bool" where
  "enum_ex_fmap P =
     enum_class.enum_ex (\<lambda>f :: 'a \<Rightarrow> 'b option. P (fmap_of_fun f))"
instance
proof standard
  show "UNIV = set (enum_class.enum :: ('a, 'b) fmap list)"
    unfolding enum_fmap_def
  proof (rule subset_antisym)
    show "UNIV \<subseteq> set (map fmap_of_fun
        (enum_class.enum :: ('a \<Rightarrow> 'b option) list))"
      by (metis UNIV_I enum_UNIV fmap_of_fun_fmlookup image_eqI set_map subsetI)
    show "set (map fmap_of_fun
        (enum_class.enum :: ('a \<Rightarrow> 'b option) list)) \<subseteq> UNIV"
      by simp
  qed
  show "distinct (enum_class.enum :: ('a, 'b) fmap list)"
  proof -
    have "inj_on fmap_of_fun (set (enum_class.enum :: ('a \<Rightarrow> 'b option) list))"
      by (rule inj_onI) (metis fmlookup_fmap_of_fun)
    then show ?thesis
      by (simp add: enum_fmap_def enum_distinct distinct_map)
  qed
  show "enum_class.enum_all P = Ball UNIV P" for P :: "('a, 'b) fmap \<Rightarrow> bool"
    apply (auto simp: enum_all_fmap_def enum_all_UNIV )
    by (metis fmap_of_fun_fmlookup)
  show "enum_class.enum_ex P = Bex UNIV P" for P :: "('a, 'b) fmap \<Rightarrow> bool"
    apply (auto simp: enum_ex_fmap_def enum_ex_UNIV)
    by (metis fmap_of_fun_fmlookup)
qed
end

section \<open>Hashing\<close>

text \<open>
  Protocols should not encode semantically different random-oracle queries as
  the same raw value before hashing.  The STARK protocol uses field-valued hash
  outputs and messages, but Merkle leaves, Merkle internal nodes, and
  Fiat-Shamir challenge queries need distinct input domains.  The datatype
  below provides that shared domain-separated input vocabulary.
\<close>

datatype 'a protocol_hash_input =
    MerkleLeaf 'a
  | MerkleNode 'a 'a
  | TranscriptAbsorb 'a 'a
  | FiatShamirChallenge 'a
  | TraceFriChallenge nat 'a
  | CompositionFriChallenge nat 'a
  | AlphaChallenge nat 'a
  | QueryIndexChallenge nat 'a

record ('a, 'b) hash =
  HashMap :: "('a, 'b) fmap"

instantiation hash_ext :: (enum, enum, enum) enum
begin
definition enum_hash_ext :: "('a, 'b, 'c) hash_ext list" where
  "enum_hash_ext =
     map (\<lambda>(m :: ('a, 'b) fmap, z :: 'c). (hash_ext m z :: ('a, 'b, 'c) hash_ext))
       (List.product
         (enum_class.enum :: ('a, 'b) fmap list)
         (enum_class.enum :: 'c list))"
definition enum_all_hash_ext :: "(('a, 'b, 'c) hash_ext \<Rightarrow> bool) \<Rightarrow> bool" where
  "enum_all_hash_ext P =
     enum_class.enum_all (\<lambda>m :: ('a, 'b) fmap.
       enum_class.enum_all (\<lambda>z :: 'c. P (hash_ext m z :: ('a, 'b, 'c) hash_ext)))"
definition enum_ex_hash_ext :: "(('a, 'b, 'c) hash_ext \<Rightarrow> bool) \<Rightarrow> bool" where
  "enum_ex_hash_ext P =
     enum_class.enum_ex (\<lambda>m :: ('a, 'b) fmap.
       enum_class.enum_ex (\<lambda>z :: 'c. P (hash_ext m z :: ('a, 'b, 'c) hash_ext)))"
instance
proof standard
  show "UNIV = set (enum_class.enum :: ('a, 'b, 'c) hash_ext list)"
    unfolding enum_hash_ext_def
  proof (rule subset_antisym)
    show "UNIV \<subseteq>
      set (map (\<lambda>(m :: ('a, 'b) fmap, z :: 'c).
        (hash_ext m z :: ('a, 'b, 'c) hash_ext))
        (List.product
          (enum_class.enum :: ('a, 'b) fmap list)
          (enum_class.enum :: 'c list)))"
      by (auto, case_tac x, auto simp: enum_UNIV)
    show "set (map (\<lambda>(m :: ('a, 'b) fmap, z :: 'c).
        (hash_ext m z :: ('a, 'b, 'c) hash_ext))
        (List.product
          (enum_class.enum :: ('a, 'b) fmap list)
          (enum_class.enum :: 'c list))) \<subseteq> UNIV"
      by simp
  qed
  show "distinct (enum_class.enum :: ('a, 'b, 'c) hash_ext list)"
    by (auto simp: enum_hash_ext_def enum_distinct distinct_map inj_on_def
      intro!: distinct_product)
  show "enum_class.enum_all P = Ball UNIV P" for P :: "('a, 'b, 'c) hash_ext \<Rightarrow> bool"
    unfolding enum_all_hash_ext_def
    by (auto simp: enum_all_UNIV; metis hash.ext_surjective)
  show "enum_class.enum_ex P = Bex UNIV P" for P :: "('a, 'b, 'c) hash_ext \<Rightarrow> bool"
    unfolding enum_ex_hash_ext_def
    by (auto simp: enum_ex_UNIV; metis hash.ext_surjective)
qed
end

type_synonym ('a, 'b, 'c, 'd) hash_monad = "('c, ('a, 'b, 'd) hash_scheme) state_monad"

definition hash_default :: "'a::finite dist"
  where "hash_default = dist_uniform (fUNIV :: 'a fset)"

definition option_default_dist :: "'a::finite option \<Rightarrow> 'a dist"
  where "option_default_dist a = case_option hash_default delta_dist a"

definition hash_dist :: "'a \<Rightarrow> ('a, 'b::finite, 'c) hash_scheme \<Rightarrow> 'b dist"
where
  "hash_dist a s = option_default_dist (fmlookup (HashMap s) a)"

definition modify_HashMap :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b, unit, 'd) hash_monad" where
"modify_HashMap x a = modify (\<lambda>s. s\<lparr>HashMap := fmupd x a (HashMap s)\<rparr>)"

definition apply_hash :: "'b \<Rightarrow> ('b, 'a, 'a::finite, 'c) hash_monad" where
  "apply_hash x = lift (hash_dist x)"

definition hash :: "'b \<Rightarrow> ('b, 'a, 'a::finite, 'c) hash_monad"
where
  "hash x \<equiv>
    do {
      a \<leftarrow> apply_hash x;
      modify_HashMap x a;
      return a
    }"

instantiation fmap :: (type, type) ord
begin

definition "less_eq a b \<equiv> (\<forall>x. fmlookup a x = None \<or> fmlookup a x = fmlookup b x)"

definition "less a b \<equiv> less_eq a b \<and> (\<exists>x. fmlookup a x = None \<and> fmlookup b x \<noteq> None)"

instance ..

end

instantiation hash_ext :: (type, type, type) ord
begin

definition "less_eq a b \<equiv> (HashMap a) \<le> (HashMap b)"

definition "less a b \<equiv>  (HashMap a) < (HashMap b)"

instance ..

end

definition less_eq_hash :: "('a, 'b) hash \<Rightarrow> ('a, 'b) hash \<Rightarrow> bool"
  where "less_eq_hash (a::('a, 'b) hash) (b::('a, 'b) hash) \<equiv> (HashMap a) \<le> (HashMap b)"

definition less_hash :: "('a, 'b) hash \<Rightarrow> ('a, 'b) hash \<Rightarrow> bool"
  where "less_hash (a::('a, 'b) hash) (b::('a, 'b) hash) \<equiv> (HashMap a) < (HashMap b)"

lemma dist_expect_eq_1:
  assumes "\<And>x. x \<in> dom (dist d) \<Longrightarrow> Q x = 1"
  shows "dist_expect d Q = 1"
proof -
  have "dist_expect d Q = (\<Sum>x\<in>dom (dist d). the (dist d x))"
    unfolding dist_expect_def
    by (intro sum.cong refl) (simp add: assms)
  also have "... = sum_map (dist d)"
    unfolding sum_map_def by simp
  also have "... = 1"
    by simp
  finally show ?thesis .
qed

lemma hash_expect_known:
  assumes "fmlookup (HashMap s) x = Some y"
  shows
    "dist_expect (lift_dist (hash_dist x) s)
       (\<lambda>r. case r of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if y = z then 1 else 0) = 1"
proof -
  have "lift_dist (hash_dist x) s = delta_dist (Some (y, s))"
    using assms
    by (simp add: lift_dist_def hash_dist_def option_default_dist_def)
  then show ?thesis
    by simp
qed

lemma hash_expect_known_extension:
  assumes "fmlookup (HashMap s0) x = Some y"
    and "s0 \<le> t"
  shows
    "dist_expect (lift_dist (hash_dist x) t)
       (\<lambda>r. case r of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if y = z then 1 else 0) = 1"
proof -
  have "fmlookup (HashMap t) x = Some y"
    using assms
    unfolding less_eq_hash_ext_def less_eq_fmap_def
    by (metis option.distinct(1))
  then show ?thesis
    by (rule hash_expect_known)
qed

lemma hash_expect_after_update_extension:
  assumes "s0\<lparr>HashMap := fmupd x y (HashMap s0)\<rparr> \<le> t"
  shows
    "dist_expect (lift_dist (hash_dist x) t)
       (\<lambda>r. case r of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if y = z then 1 else 0) = 1"
  using assms
  by (intro hash_expect_known_extension) simp_all

lemma hash_expect_after_update_extension_dist_map:
  assumes "s0\<lparr>HashMap := fmupd x y (HashMap s0)\<rparr> \<le> t"
  shows
    "dist_expect (dist_map (\<lambda>z. Some (z, t)) (hash_dist x t))
       (\<lambda>r. case r of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if y = z then 1 else 0) = 1"
  using hash_expect_after_update_extension[OF assms]
  by (simp add: lift_dist_def)

lemma hash_dist_expect_after_update_extension:
  assumes "s0\<lparr>HashMap := fmupd x y (HashMap s0)\<rparr> \<le> t"
  shows "dist_expect (hash_dist x t) (\<lambda>z. if y = z then 1 else 0) = 1"
  using hash_expect_after_update_extension[OF assms]
  by (simp add: lift_dist_def dist_expect_map)

lemma None_notin_dist_map_Some[simp]:
  "None \<notin> dom (dist (dist_map (\<lambda>x. Some (x, s)) d))"
  using set_dist_dist_map[of "\<lambda>x. Some (x, s)" d]
  unfolding set_dist_def
  by auto

lemma hash_update_extends:
  assumes "y \<in> dom (dist (hash_dist x s))"
  shows "s \<le> s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>"
  unfolding less_eq_hash_ext_def less_eq_fmap_def
proof (intro allI)
  fix z
  show "fmlookup (HashMap s) z = None \<or>
    fmlookup (HashMap s) z =
      fmlookup (HashMap (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)) z"
  proof (cases "fmlookup (HashMap s) x")
    case None
    then show ?thesis
      by (cases "z = x") simp_all
  next
    case (Some old)
    then have "y = old"
      using assms
      unfolding hash_dist_def option_default_dist_def
      by (simp add: dist_delta_dist delta_map_def)
    with Some show ?thesis
      by (cases "z = x") simp_all
  qed
qed

lemma dist_expect_then_hash_after_extension:
  assumes "\<And>r t.
    Some (r, t) \<in> dom (dist d) \<Longrightarrow>
      s0\<lparr>HashMap := fmupd x y (HashMap s0)\<rparr> \<le> t"
  shows
    "dist_expect d
      (\<lambda>r. case r of None \<Rightarrow> 1 | Some (r, t) \<Rightarrow>
        dist_expect (lift_dist (hash_dist x) t)
          (\<lambda>z. case z of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if y = z then 1 else 0)) = 1"
proof (rule dist_expect_eq_1)
  fix z
  assume z: "z \<in> dom (dist d)"
  show "(case z of None \<Rightarrow> 1 | Some (r, t) \<Rightarrow>
        dist_expect (lift_dist (hash_dist x) t)
          (\<lambda>z. case z of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if y = z then 1 else 0)) = 1"
  proof (cases z)
    case None
    then show ?thesis by simp
  next
    case (Some rt)
    then obtain r t where rt: "z = Some (r, t)"
      by (cases rt) simp
    then show ?thesis
      using assms[of r t] z
      by (simp add: hash_expect_after_update_extension)
  qed
qed

lemma dist_expect_then_hash_after_extension_dist_map:
  assumes "\<And>r t.
    Some (r, t) \<in> dom (dist d) \<Longrightarrow>
      s0\<lparr>HashMap := fmupd x y (HashMap s0)\<rparr> \<le> t"
  shows
    "dist_expect d
      (\<lambda>r. case r of None \<Rightarrow> 1 | Some (r, t) \<Rightarrow>
        dist_expect (dist_map (\<lambda>z. Some (z, t)) (hash_dist x t))
          (\<lambda>z. case z of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if y = z then 1 else 0)) = 1"
proof -
  show ?thesis
  proof (rule dist_expect_eq_1)
    fix z
    assume z: "z \<in> dom (dist d)"
    show "(case z of None \<Rightarrow> 1 | Some (r, t) \<Rightarrow>
        dist_expect (dist_map (\<lambda>z. Some (z, t)) (hash_dist x t))
          (\<lambda>z. case z of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if y = z then 1 else 0)) = 1"
    proof (cases z)
      case None
      then show ?thesis by simp
    next
      case (Some rt)
      then obtain r t where rt: "z = Some (r, t)"
        by (cases rt) simp
      then show ?thesis
      proof -
        have "dist_expect (lift_dist (hash_dist x) t)
            (\<lambda>z. case z of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if y = z then 1 else 0) = 1"
          using assms[of r t] z rt
          by (simp add: hash_expect_after_update_extension)
        then show ?thesis
          using rt by (simp add: lift_dist_def)
      qed
    qed
  qed
qed

lemma send_intermediate_send_same:
  assumes intermediate_no_fail:
    "\<And>a s'. None \<notin>
        dom (dist (execute (between a)
          (s'\<lparr>HashMap := fmupd x a (HashMap s')\<rparr>)))"
  assumes intermediate_extends:
    "\<And>a s' r t.
      Some (r, t) \<in>
        dom (dist (execute (between a)
          (s'\<lparr>HashMap := fmupd x a (HashMap s')\<rparr>))) \<Longrightarrow>
      s'\<lparr>HashMap := fmupd x a (HashMap s')\<rparr> \<le> t"
  shows
  "wp_event
    (do {
      a \<leftarrow> hash x;
      _ \<leftarrow> between a;
      b \<leftarrow> hash x;
      return (a = b)
    })
    (\<lambda>r. case r of None \<Rightarrow> False | Some (ok, _) \<Rightarrow> ok)
    s = 1"
  unfolding wp_event_def hash_def apply_hash_def modify_HashMap_def
  apply (simp add: wpsimps)
  apply (rule dist_expect_eq_1)
  apply (simp add: wp_def)
  apply (rule dist_expect_eq_1)
  apply (case_tac xaa)
   apply (simp add: intermediate_no_fail)
  apply (clarsimp simp: wpsimps split: prod.splits)
  apply (rule hash_dist_expect_after_update_extension)
  by (rule_tac a=xa and s'=s and r=x1 and t=x2 in intermediate_extends) (simp add: domIff)

subsection \<open>Weakest Precondition Calculus\<close>

lemma wp_hash[wpsimps]:
  "wp (hash x) Q s =
    dist_expect (hash_dist x s)
      (\<lambda>xa. Q (Some (xa, s\<lparr>HashMap := fmupd x xa (HashMap s)\<rparr>)))"
  by (simp add:hash_def wpsimps apply_hash_def modify_HashMap_def)

lemma wp_hashI[wp]:
  assumes "P \<le>
    dist_expect (hash_dist x s)
      (\<lambda>xa. Q (Some (xa, s\<lparr>HashMap := fmupd x xa (HashMap s)\<rparr>)))"
  shows "P \<le> wp (hash x) Q s"
  using assms by (simp add:wpsimps)

subsection \<open>Code Generator Setup\<close>

text \<open>
  @{term hash_default} does not execute since it is using @{term fUNIV}.
  Thus, we provide an alternative implementation for enumerable datatypes which
  can be used for execution.
\<close>

subsubsection \<open>Enums\<close>

definition hash_default_enum :: "'a::enum dist"
  where "hash_default_enum = hash_default"

declare hash_default_enum_def[symmetric,code]

lemma hash_default_enum_code[code]:
  "hash_default_enum = dist_uniform (fset_of_list (Enum.enum :: 'a::enum list))"
proof -
  have "Abs_fset (UNIV :: 'a set) = fset_of_list (Enum.enum :: 'a list)"
    by (rule fset_inject[THEN iffD1])
      (simp add: Abs_fset_inverse fset_of_list.rep_eq enum_UNIV)
  then have "(fUNIV :: 'a fset) = fset_of_list (Enum.enum :: 'a list)"
    by (simp add:FSet.top_fset.abs_eq)
  then show ?thesis
     unfolding hash_default_enum_def hash_default_def by simp
qed


value "fmupd (1::nat) (2::nat) fmempty"

value "execute (hash True) \<lparr>HashMap = (fmempty::(bool, bool) fmap)\<rparr>"

value "execute (apply_hash True) \<lparr>HashMap = (fmempty::(bool, bool) fmap)\<rparr>"

value "execute (modify_HashMap True True) \<lparr>HashMap = (fmempty::(bool, bool) fmap)\<rparr>"

value "execute (put True) False"

value "execute (
      do {
        a \<leftarrow> hash True;
        x \<leftarrow> hash False;
        b \<leftarrow> hash True;
        return (a = b)
      }) \<lparr>HashMap = (fmempty::(bool, bool) fmap)\<rparr>"

end
