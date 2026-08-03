(*  Title:      Stark/Merkle_Tree.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Merkle_Tree
  imports
    "HOL-Library.Tree"
    "HOL-Library.Discrete_Functions"
    Galois_Field_5
    Hash_Monad
begin

section \<open>Merkle Trees\<close>

text \<open>
  This theory defines Merkle tree creation, authentication paths, and checking
  in the probabilistic hash monad.  The STARK prover uses these commitments for
  trace, composition, and FRI layers, while the verifier checks sampled
  openings against the recorded roots.
\<close>

(* The explicit length parameter mirrors the verifier-side path check. *)
fun get_authentication_path::"nat \<Rightarrow> nat \<Rightarrow> 'a tree \<Rightarrow> 'a list"
where
  "get_authentication_path lgth idx (Node l v r) =
    (if lgth = 1 then [] else
    (if idx < lgth div 2
      then (value r) # (get_authentication_path (lgth div 2) idx l)
      else (value l) # (get_authentication_path (lgth div 2) (idx - (lgth div 2)) r)))"

locale merkle_tree =
  fixes concat :: "'a::finite \<Rightarrow> 'a \<Rightarrow> 'b"
begin

fun create::"'b list \<Rightarrow> ('b, 'a, 'a tree, 'c) hash_monad"
where
  "create [] = return \<langle>\<rangle>"
| "create [x] =
    do {
       h \<leftarrow> hash x;
       return \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>
    }"
| "create xs =
    do {
      let i = length xs div 2;
      ln \<leftarrow> create (take i xs);
      rn \<leftarrow> create (drop i xs);
      val \<leftarrow> hash (concat (value ln) (value rn));
      return \<langle>ln, val, rn\<rangle>
    }"

fun check_authentication_path:: "nat \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> ('b, 'a, 'a, 'c) hash_monad"
where
  "check_authentication_path lgth idx leaf_data [] = hash leaf_data"
| "check_authentication_path lgth idx leaf_data (a#ap) =
    (if idx < lgth div 2
      then
        do {
          x \<leftarrow> check_authentication_path (lgth div 2) idx leaf_data ap;
          hash (concat x a)
        }
      else
        do {
          x \<leftarrow> check_authentication_path (lgth div 2) (idx - (lgth div 2)) leaf_data ap;
          hash (concat a x)
        })"

end

subsection \<open>Weakest Precondition Calculus\<close>

context merkle_tree
begin

lemma wp_check_authentication_path[wp]:
  assumes "ap = [] \<Longrightarrow> P \<le> wp (hash leaf_data) Q s"
  assumes "\<And>a list.
       ap = a # list \<Longrightarrow>
       idx < lgth div 2 \<Longrightarrow>
       P \<le> wp (check_authentication_path (lgth div 2) idx leaf_data list \<bind> (\<lambda>x. hash (concat x a))) Q s"
  assumes "\<And>a list.
       ap = a # list \<Longrightarrow>
       \<not> idx < lgth div 2 \<Longrightarrow>
       P \<le> wp (check_authentication_path (lgth div 2) (idx - lgth div 2) leaf_data list \<bind>
                (\<lambda>x. hash (concat a x)))
             Q s"
  shows "P \<le> wp (check_authentication_path lgth idx leaf_data ap) Q s"
  using assms by (cases ap) (auto)

lemma wp_create[wp]:
  assumes "xs = [] \<Longrightarrow> P \<le> wp (return \<langle>\<rangle>) Q s"
  assumes "\<And>x. xs = [x] \<Longrightarrow> P \<le> wp (hash x \<bind> (\<lambda>h. return \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>)) Q s"
  assumes "\<And>v vb vc.
       xs = v # vb # vc \<Longrightarrow>
       P \<le> wp (local.create (v # take (length vc div 2) (vb # vc)) \<bind>
                (\<lambda>ln. local.create (drop (length vc div 2) (vb # vc)) \<bind>
                      (\<lambda>rn. hash (concat (value ln) (value rn)) \<bind> (\<lambda>val. return \<langle>ln, val, rn\<rangle>))))
             Q s"
  shows "P \<le> wp (create xs) Q s"
  using assms by (cases xs rule:create.cases) (auto)

end

subsection \<open>Boolean interpretation\<close>

definition concat_bool:: "bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "concat_bool = (\<and>)"

global_interpretation test_merkle:
  merkle_tree concat_bool
  defines test_create = test_merkle.create
    and test_check_authentication_path = test_merkle.check_authentication_path
  .

lemma
  "execute (test_create [True, True, True, True]) \<lparr>HashMap = (fmempty::(bool, bool) fmap)\<rparr> =
  dist_of_fset (
    {|(Some (\<langle>\<langle>\<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>, True, \<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>\<rangle>, False, \<langle>\<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>, True, \<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>, \<lparr>HashMap = fmap_of_list [(True, False), (False, True)]\<rparr>),
      (1 / 4)),
     (Some (\<langle>\<langle>\<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>, False, \<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>\<rangle>, False, \<langle>\<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>, False, \<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>, \<lparr>HashMap = fmap_of_list [(True, False), (False, False)]\<rparr>),
      (1 / 4)),
     (Some (\<langle>\<langle>\<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>, True, \<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>\<rangle>, True, \<langle>\<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>, True, \<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>, \<lparr>HashMap = fmap_of_list [(True, True)]\<rparr>), (1 / 2))|})"
  by eval

lemma
  "execute (test_create [True, False, True, False]) \<lparr>HashMap = (fmempty::(bool, bool) fmap)\<rparr> =
  dist_of_fset (
    {|(Some (\<langle>\<langle>\<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>, True, \<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>\<rangle>, False, \<langle>\<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>, True, \<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>, \<lparr>HashMap = fmap_of_list [(True, False), (False, True)]\<rparr>),
        (1 / 4)),
       (Some (\<langle>\<langle>\<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>, False, \<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>\<rangle>, False, \<langle>\<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>, False, \<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>, \<lparr>HashMap = fmap_of_list [(True, False), (False, False)]\<rparr>),
        (1 / 4)),
       (Some (\<langle>\<langle>\<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>, True, \<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>\<rangle>, True, \<langle>\<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>, True, \<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>, \<lparr>HashMap = fmap_of_list [(True, True), (False, True)]\<rparr>), (1 / 4)),
       (Some (\<langle>\<langle>\<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>, False, \<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>\<rangle>, False, \<langle>\<langle>\<langle>\<rangle>, True, \<langle>\<rangle>\<rangle>, False, \<langle>\<langle>\<rangle>, False, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>, \<lparr>HashMap = fmap_of_list [(True, True), (False, False)]\<rparr>),
        (1 / 4))|})"
  by eval

lemma "execute
  (do {
    let x = [True, True, True, True];
    r \<leftarrow> test_create x;
    let ap = get_authentication_path (length x) 2 r;
    r2 \<leftarrow> test_check_authentication_path (length x) 2 True ap;
    return (r2 = value r)
  }) \<lparr>HashMap = (fmempty::(bool, bool) fmap)\<rparr>
=
dist_of_fset (
    {|(Some (True, \<lparr>HashMap = fmap_of_list [(True, True)]\<rparr>), (1 / 2)), (Some (True, \<lparr>HashMap = fmap_of_list [(True, False), (False, False)]\<rparr>), (1 / 4)),
     (Some (True, \<lparr>HashMap = fmap_of_list [(True, False), (False, True)]\<rparr>), (1 / 4))|})"
  by eval

subsection \<open>GF5 interpretation\<close>

definition concat_gf5:: "gf5 \<Rightarrow> gf5 \<Rightarrow> gf5"
where
  "concat_gf5 = (+)"

global_interpretation merkle_gf5:
  merkle_tree concat_gf5
  defines gf5_create = merkle_gf5.create
    and gf5_check_authentication_path = merkle_gf5.check_authentication_path
  .

value "execute (gf5_create [1, 2, 3]) \<lparr>HashMap = (fmempty::(gf5, gf5) fmap)\<rparr>"

subsection \<open>Domain-separated protocol Merkle interface\<close>

text \<open>
  The generic Merkle locale already separates hash outputs from hash inputs:
  leaves have a separate input type, hash outputs have the field type, and
  internal nodes are encoded by the locale parameter.  Instantiating that
  parameter with the constructor MerkleNode and wrapping leaves with
  MerkleLeaf gives the STARK protocol a domain-separated Merkle API without
  duplicating the existing Merkle proofs.
\<close>

global_interpretation protocol_merkle:
  merkle_tree "(\<lambda>x y. MerkleNode x y)"
  defines protocol_merkle_create_raw = protocol_merkle.create
    and protocol_merkle_check_authentication_path_raw =
      protocol_merkle.check_authentication_path
  .

definition protocol_create
  :: "'a::finite list \<Rightarrow>
      ('a protocol_hash_input, 'a, 'a tree, 'c) hash_monad"
  where
    "protocol_create xs =
      protocol_merkle.create (map MerkleLeaf xs)"

definition protocol_check_authentication_path
  :: "nat \<Rightarrow> nat \<Rightarrow> 'a::finite \<Rightarrow> 'a list \<Rightarrow>
      ('a protocol_hash_input, 'a, 'a, 'c) hash_monad"
  where
    "protocol_check_authentication_path len idx leaf path =
      protocol_merkle.check_authentication_path len idx (MerkleLeaf leaf) path"

subsection \<open>Sanity Check\<close>

context merkle_tree
begin

text \<open>
  The created-tree predicate is a proof-only invariant connecting the result of create to the final hash-map state.
  It is needed because create samples hashes probabilistically, while authentication-path checking later
  recomputes hashes.
  To prove the recomputation succeeds with probability 1, the proof needs to know those sampled hashes
  are already recorded in the hash map, so future calls to hash replay the same values instead of sampling
  fresh ones.
  So the created-tree predicate is not part of the Merkle API.
  It is a ghost invariant used to bridge "this tree was produced by create"
  and "checking its authentication path will replay the same root hash."
\<close>

fun created_tree::"'b list \<Rightarrow> 'a tree \<Rightarrow> ('b, 'a, 'c) hash_scheme \<Rightarrow> bool"
where
  "created_tree [] t s \<longleftrightarrow> t = \<langle>\<rangle>"
| "created_tree [x] t s \<longleftrightarrow>
    (\<exists>h. t = \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle> \<and> fmlookup (HashMap s) x = Some h)"
| "created_tree xs t s \<longleftrightarrow>
    (let i = length xs div 2 in
      \<exists>l h r. t = \<langle>l, h, r\<rangle> \<and>
        created_tree (take i xs) l s \<and>
        created_tree (drop i xs) r s \<and>
        fmlookup (HashMap s) (concat (value l) (value r)) = Some h)"

declare created_tree.simps[simp del]

lemma set_dist_bindE:
  assumes "Some (y, t) \<in> set_dist (execute (m \<bind> f) s)"
  obtains x u where "Some (x, u) \<in> set_dist (execute m s)"
    and "Some (y, t) \<in> set_dist (execute (f x) u)"
proof -
  let ?K = "bind_cont_map (map_fun id dist \<circ> execute \<circ> f)"
  have bind_dom:
    "Some (y, t) \<in> dom (map_bind (dist \<circ> execute m) ?K s)"
    using assms
    unfolding set_dist_def sm_bind.rep_eq dist_bind.rep_eq
    by (simp add: o_def map_fun_def)
  then have union:
    "Some (y, t) \<in>
      (\<Union>i\<in>dom (dist (execute m s)). dom (?K i))"
    using dom_map_bind[of "dist \<circ> execute m" ?K s]
    by auto
  then obtain i where i_dom: "i \<in> dom (dist (execute m s))"
    and y_dom: "Some (y, t) \<in> dom (?K i)"
    by auto
  obtain x u where i: "i = Some (x, u)"
  proof (cases i)
    case None
    then have False
      using y_dom
      unfolding bind_cont_map_def delta_map_def
      by simp
    then show ?thesis ..
  next
    case (Some p)
    then obtain a b where "i = Some (a, b)"
      by (cases p) auto
    then show ?thesis
      by (rule that)
  qed
  have "Some (x, u) \<in> set_dist (execute m s)"
    using i_dom i unfolding set_dist_def by simp
  moreover have "Some (y, t) \<in> set_dist (execute (f x) u)"
    using y_dom i
    unfolding set_dist_def bind_cont_map_def
    by (simp add: o_def map_fun_def)
  ultimately show ?thesis
    by (rule that)
qed

lemma set_dist_return_iff[simp]:
  "Some (y, t) \<in> set_dist (execute (return x) s) \<longleftrightarrow> y = x \<and> t = s"
  unfolding set_dist_def return.rep_eq dist_return_def
  by (simp add: dist_delta_dist delta_map_def)

lemma set_dist_get_iff[simp]:
  "Some (y, t) \<in> set_dist (execute get s) \<longleftrightarrow> y = s \<and> t = s"
  unfolding set_dist_def get.rep_eq dist_get_def
  by (simp add: dist_delta_dist delta_map_def)

lemma set_dist_put_iff[simp]:
  "Some (y, t) \<in> set_dist (execute (put s') s) \<longleftrightarrow> y = () \<and> t = s'"
  unfolding set_dist_def put.rep_eq dist_put_def
  by (simp add: dist_delta_dist delta_map_def)

lemma hash_outcome:
  assumes "Some (h, t) \<in> set_dist (execute (hash x) s)"
  shows "s \<le> t"
    and "fmlookup (HashMap t) x = Some h"
proof -
  from assms obtain a s1 where
    a: "Some (a, s1) \<in> set_dist (execute (apply_hash x) s)"
    and rest: "Some (h, t) \<in>
      set_dist (execute (modify_HashMap x a \<bind> (\<lambda>_. return a)) s1)"
  proof -
    have "Some (h, t) \<in>
      set_dist (execute
        (apply_hash x \<bind> (\<lambda>a. modify_HashMap x a \<bind> (\<lambda>_. return a))) s)"
      using assms unfolding hash_def .
    then show ?thesis
      by (rule set_dist_bindE) (rule that)
  qed
  have a_img: "Some (a, s1) \<in> (\<lambda>a. Some (a, s)) ` set_dist (hash_dist x s)"
    using a
    unfolding apply_hash_def lift.rep_eq lift_dist_def
    by (simp add: set_dist_dist_map)
  then have s1: "s1 = s"
    by auto
  from a_img have a_dom: "a \<in> dom (dist (hash_dist x s))"
    unfolding set_dist_def by auto
  from rest obtain u s2 where
    mod: "Some (u, s2) \<in> set_dist (execute (modify_HashMap x a) s1)"
    and ret: "Some (h, t) \<in> set_dist (execute (return a) s2)"
    by (elim set_dist_bindE)
  from mod have s2: "s2 = s1\<lparr>HashMap := fmupd x a (HashMap s1)\<rparr>"
    unfolding modify_HashMap_def modify_def
    by (auto elim!: set_dist_bindE)
  from ret have h: "h = a" and t: "t = s2"
    by auto
  show "s \<le> t"
    using a_dom unfolding s1 s2 h t by (rule hash_update_extends)
  show "fmlookup (HashMap t) x = Some h"
    using a_dom unfolding s1 s2 h t hash_dist_def option_default_dist_def
    by (cases "fmlookup (HashMap s) x") (auto simp: dist_delta_dist delta_map_def)
qed

lemma hash_extension_lookup:
  assumes "fmlookup (HashMap s0) x = Some y"
    and "s0 \<le> s"
  shows "fmlookup (HashMap s) x = Some y"
  using assms
  unfolding less_eq_hash_ext_def less_eq_fmap_def
  by (metis option.distinct(1))

lemma hash_ext_trans:
  assumes "s0 \<le> s1" and "s1 \<le> s2"
  shows "s0 \<le> (s2::('b, 'a, 'c) hash_scheme)"
  using assms
  unfolding less_eq_hash_ext_def less_eq_fmap_def
  by (metis order.trans)

lemma hash_ext_refl:
  "s \<le> (s::('b, 'a, 'c) hash_scheme)"
  unfolding less_eq_hash_ext_def less_eq_fmap_def
  by simp

lemma created_tree_mono:
  assumes "created_tree xs t s0"
    and "s0 \<le> s"
  shows "created_tree xs t s"
  using assms
  by (induction xs t s0 arbitrary: s rule: created_tree.induct)
    (auto simp: Let_def created_tree.simps dest: hash_extension_lookup)

lemma create_outcome:
  assumes "Some (r, t) \<in> set_dist (execute (create xs) s)"
  shows "s \<le> t \<and> created_tree xs r t"
  using assms
proof (induction xs arbitrary: r s t rule: measure_induct_rule[of length])
  case (less xs)
  show ?case
	  proof (cases xs rule: create.cases)
	    case 1
	    with less.prems show ?thesis
	      by (auto simp: created_tree.simps intro: hash_ext_refl)
  next
    case (2 x)
    from less.prems[unfolded 2] obtain h s1 where
      h: "Some (h, s1) \<in> set_dist (execute (hash x) s)"
      and ret: "Some (r, t) \<in>
        set_dist (execute (return \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>) s1)"
      by (auto elim!: set_dist_bindE)
    then show ?thesis
      using hash_outcome unfolding 2 by (auto simp: created_tree.simps)
  next
    case (3 v vb vc)
    let ?i = "length xs div 2"
    have len_ge: "2 \<le> length xs"
      unfolding 3 by simp
    have take_less: "length (take ?i xs) < length xs"
      using len_ge by simp
    have drop_less: "length (drop ?i xs) < length xs"
      using len_ge by simp
    have take_eq: "take ?i xs = v # take (length vc div 2) (vb # vc)"
      unfolding 3 by simp
    have drop_eq: "drop ?i xs = drop (length vc div 2) (vb # vc)"
      unfolding 3 by simp
    have split_create: "Some (r, t) \<in> set_dist (execute
      (create (take ?i xs) \<bind>
        (\<lambda>l. create (drop ?i xs) \<bind>
          (\<lambda>rn. hash (concat (value l) (value rn)) \<bind>
            (\<lambda>val. return \<langle>l, val, rn\<rangle>)))) s)"
      using less.prems unfolding 3 take_eq drop_eq by simp
    from split_create obtain l s1 where
      l: "Some (l, s1) \<in> set_dist (execute (create (take ?i xs)) s)"
      and rest1: "Some (r, t) \<in>
        set_dist (execute
          (create (drop ?i xs) \<bind>
            (\<lambda>rn. hash (concat (value l) (value rn)) \<bind>
              (\<lambda>val. return \<langle>l, val, rn\<rangle>))) s1)"
      by (rule set_dist_bindE) (rule that)
    from rest1 obtain rn s2 where
      rn: "Some (rn, s2) \<in> set_dist (execute (create (drop ?i xs)) s1)"
      and rest2: "Some (r, t) \<in>
        set_dist (execute
          (hash (concat (value l) (value rn)) \<bind>
            (\<lambda>val. return \<langle>l, val, rn\<rangle>)) s2)"
      by (rule set_dist_bindE) (rule that)
    from rest2 obtain val s3 where
      val: "Some (val, s3) \<in> set_dist (execute (hash (concat (value l) (value rn))) s2)"
      and ret: "Some (r, t) \<in> set_dist (execute (return \<langle>l, val, rn\<rangle>) s3)"
      by (auto elim!: set_dist_bindE)
    have left_out: "s \<le> s1 \<and> created_tree (take ?i xs) l s1"
      by (rule less.IH[OF take_less l])
    have right_out: "s1 \<le> s2 \<and> created_tree (drop ?i xs) rn s2"
      by (rule less.IH[OF drop_less rn])
    have s2_s3: "s2 \<le> s3" and root_lookup:
      "fmlookup (HashMap s3) (concat (value l) (value rn)) = Some val"
      using hash_outcome[OF val] by auto
    from ret have r: "r = \<langle>l, val, rn\<rangle>" and t: "t = s3"
      by auto
    have s1_s3: "s1 \<le> s3"
      using right_out s2_s3 by (auto intro: hash_ext_trans)
    have st3: "s \<le> s3"
      using left_out s1_s3 by (auto intro: hash_ext_trans)
    have "created_tree (take ?i xs) l s3"
      using left_out s1_s3 by (auto intro: created_tree_mono)
    moreover have "created_tree (drop ?i xs) rn s3"
      using right_out s2_s3 by (auto intro: created_tree_mono)
    ultimately have "created_tree xs r t"
      using root_lookup unfolding r t 3 by (auto simp: created_tree.simps Let_def)
    with st3 show ?thesis
      unfolding t by simp
  qed
qed

lemma hash_replay:
  assumes "fmlookup (HashMap s0) x = Some y"
    and "s0 \<le> s"
  shows "wp_event (hash x) (\<lambda>r. case r of None \<Rightarrow> False | Some (z, _) \<Rightarrow> z = y) s = 1"
proof -
  have flip:
    "(\<lambda>r. case r of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if z = y then 1 else 0) =
     (\<lambda>r. case r of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if y = z then 1 else 0)"
    by (rule ext) (auto split: option.splits prod.splits)
  have "dist_expect (lift_dist (hash_dist x) s)
      (\<lambda>r. case r of None \<Rightarrow> 0 | Some (z, u) \<Rightarrow> if z = y then 1 else 0) = 1"
    using hash_expect_known_extension[OF assms]
    unfolding flip .
  then show ?thesis
    unfolding wp_event_def wp_hash lift_dist_def
    by (simp add: dist_expect_map)
qed

lemma singleton_index:
  assumes "xs = [x]"
    and "i < length xs"
  shows "i = 0" and "xs ! i = x"
  using assms by (cases i; auto)+

lemma check_created_tree_outcome:
  assumes "created_tree xs r s0"
    and "length xs = 2 ^ n"
    and "i < length xs"
    and "v = xs ! i"
    and "s0 \<le> s"
    and "Some (h, t) \<in> set_dist (execute
      (check_authentication_path (length xs) i v
        (get_authentication_path (length xs) i r)) s)"
  shows "h = value r \<and> s \<le> t"
  using assms
proof (induction n arbitrary: xs r i v s0 s h t)
  case 0
  have len1: "length xs = 1"
  proof -
    have "length xs = (2::nat) ^ 0"
      using "0.prems"(2) .
    also have "... = 1"
      by (rule power_0)
    finally show ?thesis .
  qed
  obtain x where xs: "xs = [x]"
  proof (cases xs)
    case Nil
    then show ?thesis
      using len1 by simp
  next
    case (Cons y ys)
    then have "Suc (length ys) = Suc 0"
      using len1 by (simp only: length_Cons)
    then have "length ys = 0"
      by simp
    then have "ys = []"
      by (simp only: length_0_conv)
    then show ?thesis
      using Cons that by simp
  qed
  then obtain val where r: "r = \<langle>\<langle>\<rangle>, val, \<langle>\<rangle>\<rangle>"
    and lookup: "fmlookup (HashMap s0) x = Some val"
    using "0.prems"(1) by (auto simp: created_tree.simps)
  have i0: "i = 0"
    using singleton_index(1)[OF xs "0.prems"(3)] by assumption
  have v_x: "v = x"
    using "0.prems"(4) singleton_index(2)[OF xs "0.prems"(3)] by simp
  have outcome_hash: "Some (h, t) \<in> set_dist (execute (hash x) s)"
    using "0.prems"(6) unfolding xs r v_x by simp
  have s_t: "s \<le> t"
    by (rule hash_outcome(1)[OF outcome_hash])
	  have s0_t: "s0 \<le> t"
	    using "0.prems"(5) s_t by (meson hash_ext_trans)
  have "fmlookup (HashMap t) x = Some val"
    by (rule hash_extension_lookup[OF lookup s0_t])
  moreover have "fmlookup (HashMap t) x = Some h"
    by (rule hash_outcome(2)[OF outcome_hash])
  ultimately show "h = value r \<and> s \<le> t"
    unfolding r using s_t by auto
next
  case (Suc n)
  let ?m = "2 ^ n"
  let ?lxs = "take ?m xs"
  let ?rxs = "drop ?m xs"
  have len: "length xs = 2 * ?m"
    using Suc.prems(2) by simp
  then have mid: "length xs div 2 = ?m"
    by simp
  obtain a b cs where xs_cons: "xs = a # b # cs"
    using len by (cases xs; cases "tl xs") auto
  have m_eq: "2 ^ n = Suc (length cs div 2)"
    using mid unfolding xs_cons by simp
  have take_mid_eq: "?lxs = a # take (length cs div 2) (b # cs)"
    unfolding xs_cons m_eq by simp
  have drop_mid_eq: "?rxs = drop (length cs div 2) (b # cs)"
    unfolding xs_cons m_eq by simp
  from Suc.prems(1) obtain l root rr where
    r: "r = \<langle>l, root, rr\<rangle>"
    and l_created': "created_tree (a # take (length cs div 2) (b # cs)) l s0"
    and r_created': "created_tree (drop (length cs div 2) (b # cs)) rr s0"
    and lookup: "fmlookup (HashMap s0) (concat (value l) (value rr)) = Some root"
    unfolding xs_cons
    by (auto simp: created_tree.simps Let_def mid intro: that)
  have l_created: "created_tree ?lxs l s0"
    using l_created' unfolding take_mid_eq .
  have r_created: "created_tree ?rxs rr s0"
    using r_created' unfolding drop_mid_eq .
  have len_l: "length ?lxs = 2 ^ n"
    using len by simp
  have len_r: "length ?rxs = 2 ^ n"
    using len by simp
  show "h = value r \<and> s \<le> t"
  proof (cases "i < ?m")
    case True
    have v_l: "v = ?lxs ! i"
      using Suc.prems(3,4) True len by (simp add: nth_take)
    have i_l: "i < length ?lxs"
      using True len_l by simp
    have split_check: "Some (h, t) \<in> set_dist (execute
      (check_authentication_path (length ?lxs) i v
        (get_authentication_path (length ?lxs) i l) \<bind>
        (\<lambda>x. hash (concat x (value rr)))) s)"
      using Suc.prems(6) True unfolding r
      by (simp add: mid len_l len)
    from split_check obtain x s1 where
      check_l: "Some (x, s1) \<in> set_dist (execute
        (check_authentication_path (length ?lxs) i v
          (get_authentication_path (length ?lxs) i l)) s)"
      and hash_root: "Some (h, t) \<in> set_dist (execute (hash (concat x (value rr))) s1)"
      by (rule set_dist_bindE) (rule that)
    have left_out: "x = value l \<and> s \<le> s1"
      by (rule Suc.IH[OF l_created len_l i_l v_l Suc.prems(5) check_l])
    have x: "x = value l"
      using left_out by simp
    have s_s1: "s \<le> s1"
      using left_out by simp
    have s1_t: "s1 \<le> t"
      using hash_outcome(1)[OF hash_root] .
    have s0_t: "s0 \<le> t"
      using Suc.prems(5) s_s1 s1_t by (meson hash_ext_trans)
    have "fmlookup (HashMap t) (concat (value l) (value rr)) = Some root"
      by (rule hash_extension_lookup[OF lookup s0_t])
    moreover have "fmlookup (HashMap t) (concat (value l) (value rr)) = Some h"
      using hash_outcome(2)[OF hash_root] unfolding x .
    ultimately show "h = value r \<and> s \<le> t"
      unfolding r using s_s1 s1_t by (auto intro: hash_ext_trans)
  next
    case False
    have i_ge: "?m \<le> i"
      using False by simp
    have i_r: "i - ?m < length ?rxs"
      using Suc.prems(3) len i_ge by simp
    have v_r: "v = ?rxs ! (i - ?m)"
      using Suc.prems(3,4) i_ge len
      by (simp add: nth_drop)
    have split_check: "Some (h, t) \<in> set_dist (execute
      (check_authentication_path (length ?rxs) (i - ?m) v
        (get_authentication_path (length ?rxs) (i - ?m) rr) \<bind>
        (\<lambda>x. hash (concat (value l) x))) s)"
      using Suc.prems(6) False unfolding r
      by (simp add: mid len_r len)
    from split_check obtain x s1 where
      check_r: "Some (x, s1) \<in> set_dist (execute
        (check_authentication_path (length ?rxs) (i - ?m) v
          (get_authentication_path (length ?rxs) (i - ?m) rr)) s)"
      and hash_root: "Some (h, t) \<in> set_dist (execute (hash (concat (value l) x)) s1)"
      by (rule set_dist_bindE) (rule that)
    have right_out: "x = value rr \<and> s \<le> s1"
      by (rule Suc.IH[OF r_created len_r i_r v_r Suc.prems(5) check_r])
    have x: "x = value rr"
      using right_out by simp
    have s_s1: "s \<le> s1"
      using right_out by simp
    have s1_t: "s1 \<le> t"
      using hash_outcome(1)[OF hash_root] .
    have s0_t: "s0 \<le> t"
      using Suc.prems(5) s_s1 s1_t by (meson hash_ext_trans)
    have "fmlookup (HashMap t) (concat (value l) (value rr)) = Some root"
      by (rule hash_extension_lookup[OF lookup s0_t])
    moreover have "fmlookup (HashMap t) (concat (value l) (value rr)) = Some h"
      using hash_outcome(2)[OF hash_root] unfolding x .
    ultimately show "h = value r \<and> s \<le> t"
      unfolding r using s_s1 s1_t by (auto intro: hash_ext_trans)
  qed
qed

lemma check_created_tree:
  assumes "created_tree xs r s0"
    and "length xs = 2 ^ n"
    and "i < length xs"
    and "v = xs ! i"
    and "s0 \<le> s"
    and "None \<notin> dom (dist (execute
      (check_authentication_path (length xs) i v
        (get_authentication_path (length xs) i r)) s))"
  shows "wp_event
    (check_authentication_path (length xs) i v
      (get_authentication_path (length xs) i r))
    (\<lambda>out. case out of None \<Rightarrow> False | Some (r', _) \<Rightarrow> r' = value r) s = 1"
  unfolding wp_event_def wp_def
proof (rule dist_expect_eq_1)
  fix p
  assume p: "p \<in> dom (dist (execute
    (check_authentication_path (length xs) i v
      (get_authentication_path (length xs) i r)) s))"
  obtain a b where p_eq: "p = Some (a, b)"
    using p assms(6)
    by (cases p) auto
  have support: "Some (a, b) \<in> set_dist (execute
    (check_authentication_path (length xs) i v
      (get_authentication_path (length xs) i r)) s)"
    using p unfolding p_eq set_dist_def .
  then have a_eq: "a = value r"
    using check_created_tree_outcome[OF assms(1-5) support] by simp
  have goal: "(if (case p of None \<Rightarrow> False | Some (r', _) \<Rightarrow> r' = value r) then 1 else 0) = 1"
    using a_eq by (simp add: p_eq)
  from goal show "(if (case p of None \<Rightarrow> False | Some (r', _) \<Rightarrow> r' = value r) then 1 else 0) = 1" .
qed

proposition create_check:
  assumes "length x = 2 ^ n"
    and "i < length x"
    and "v = x ! i"
    and "None \<notin> dom (dist (execute
      (do {
        r \<leftarrow> create x;
        let ap = get_authentication_path (length x) i r;
        r2 \<leftarrow> check_authentication_path (length x) i v ap;
        return (r2 = value r)
      }) \<lparr>HashMap = fmempty\<rparr>))"
  shows "1 \<le> wp_event
    (do {
      r \<leftarrow> create x;
      let ap = get_authentication_path (length x) i r;
      r2 \<leftarrow> check_authentication_path (length x) i v ap;
      return (r2 = value r)
    }) (\<lambda>out. case out of None \<Rightarrow> False | Some (r, _) \<Rightarrow> r) \<lparr>HashMap = fmempty\<rparr>"
proof -
  let ?s0 = "\<lparr>HashMap = fmempty\<rparr>"
  let ?m = "do {
      r \<leftarrow> create x;
      let ap = get_authentication_path (length x) i r;
      r2 \<leftarrow> check_authentication_path (length x) i v ap;
      return (r2 = value r)
    }"
  have "wp_event ?m (\<lambda>out. case out of None \<Rightarrow> False | Some (r, _) \<Rightarrow> r) ?s0 = 1"
    unfolding wp_event_def wp_def
  proof (rule dist_expect_eq_1)
    fix p
    assume p: "p \<in> dom (dist (execute ?m ?s0))"
    obtain ok sf where p_eq: "p = Some (ok, sf)"
      using p assms(4)
      by (cases p) auto
    have p_set: "Some (ok, sf) \<in> set_dist (execute ?m ?s0)"
      using p unfolding p_eq set_dist_def .
    from p_set obtain r s1 where
      create_r: "Some (r, s1) \<in> set_dist (execute (create x) ?s0)"
      and rest: "Some (ok, sf) \<in> set_dist (execute
        (let ap = get_authentication_path (length x) i r in
          check_authentication_path (length x) i v ap \<bind>
          (\<lambda>r2. return (r2 = value r))) s1)"
      by (rule set_dist_bindE) (rule that)
    from rest obtain r2 s2 where
      check_r: "Some (r2, s2) \<in> set_dist (execute
        (check_authentication_path (length x) i v
          (get_authentication_path (length x) i r)) s1)"
      and ret: "Some (ok, sf) \<in> set_dist (execute (return (r2 = value r)) s2)"
      by (auto simp: Let_def elim!: set_dist_bindE)
    have created: "created_tree x r s1"
      using create_outcome[OF create_r] by simp
    have "r2 = value r"
      using check_created_tree_outcome[
        OF created assms(1-3) hash_ext_refl check_r] by simp
    with ret have ok: "ok"
      by auto
    have goal: "(if (case p of None \<Rightarrow> False | Some (r, _) \<Rightarrow> r) then 1 else 0) = 1"
      using ok by (simp add: p_eq)
    from goal show "(if (case p of None \<Rightarrow> False | Some (r, _) \<Rightarrow> r) then 1 else 0) = 1" .
  qed
  then show ?thesis
    by simp
qed

end

definition protocol_created_tree
  :: "'a::finite list \<Rightarrow> 'a tree \<Rightarrow>
      ('a protocol_hash_input, 'a, 'c) hash_scheme \<Rightarrow> bool"
  where
    "protocol_created_tree xs r s \<longleftrightarrow>
      protocol_merkle.created_tree (map MerkleLeaf xs) r s"

lemma protocol_created_tree_mono:
  assumes "protocol_created_tree xs r s0"
    and "s0 \<le> s"
  shows "protocol_created_tree xs r s"
  using assms
  unfolding protocol_created_tree_def
  by (rule protocol_merkle.created_tree_mono)

lemma protocol_create_outcome:
  assumes "Some (r, t) \<in> set_dist (execute (protocol_create xs) s)"
  shows "s \<le> t \<and> protocol_created_tree xs r t"
proof -
  have raw:
    "Some (r, t) \<in>
      set_dist (execute (protocol_merkle.create (map MerkleLeaf xs)) s)"
    using assms unfolding protocol_create_def .
  show ?thesis
    using protocol_merkle.create_outcome[OF raw]
    unfolding protocol_created_tree_def by simp
qed

lemma protocol_check_created_tree_outcome:
  assumes created: "protocol_created_tree xs r s0"
    and length_xs: "length xs = 2 ^ n"
    and i_bound: "i < length xs"
    and v: "v = xs ! i"
    and ext: "s0 \<le> s"
    and check:
      "Some (r2, t) \<in> set_dist (execute
        (protocol_check_authentication_path (length xs) i v
          (get_authentication_path (length xs) i r)) s)"
  shows "r2 = value r \<and> s \<le> t"
proof -
  have raw_created:
    "protocol_merkle.created_tree (map MerkleLeaf xs) r s0"
    using created unfolding protocol_created_tree_def .
  have raw_check:
    "Some (r2, t) \<in> set_dist (execute
      (protocol_merkle.check_authentication_path
        (length (map MerkleLeaf xs)) i (MerkleLeaf v)
        (get_authentication_path (length (map MerkleLeaf xs)) i r)) s)"
    using check unfolding protocol_check_authentication_path_def by simp
  have leaf_eq: "MerkleLeaf v = map MerkleLeaf xs ! i"
    using i_bound v by simp
  show ?thesis
    by (rule protocol_merkle.check_created_tree_outcome
        [OF raw_created _ _ leaf_eq ext raw_check])
      (use length_xs i_bound in simp_all)
qed

subsubsection \<open>Length\<close>

context merkle_tree
begin

lemma create_get_authentication_path_len:
  assumes "Some (r, t) \<in> set_dist (execute (create xs) s)"
    and "0 < lgth"
    and "lgth \<le> length xs"
  shows "length (get_authentication_path lgth idx r) = floor_log lgth"
  using assms
proof (induction xs arbitrary: r s t lgth idx rule: measure_induct_rule[of length])
  case (less xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      using less.prems by simp
  next
    case (Cons x ys)
    have xs_Cons: "xs = x # ys"
      using Cons by simp
    show ?thesis
    proof (cases ys)
      case Nil
      then obtain h s1 where r: "r = \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>"
        using less.prems xs_Cons by (auto elim!: set_dist_bindE)
      have "lgth = 1"
        using less.prems xs_Cons Nil by simp
      then show ?thesis
        unfolding r by (simp add: floor_log_Suc_zero)
    next
      case (Cons y zs)
      let ?i = "length xs div 2"
      have xs_eq: "xs = x # y # zs"
        using xs_Cons \<open>ys = y # zs\<close> by simp
      have len_ge: "2 \<le> length xs"
        using xs_eq by simp
      have take_eq: "take ?i xs = x # take (length zs div 2) (y # zs)"
        unfolding xs_eq by simp
      have drop_eq: "drop ?i xs = drop (length zs div 2) (y # zs)"
        unfolding xs_eq by simp
      have split_create: "Some (r, t) \<in> set_dist (execute
        (create (take ?i xs) \<bind>
          (\<lambda>l. create (drop ?i xs) \<bind>
            (\<lambda>rn. hash (concat (value l) (value rn)) \<bind>
              (\<lambda>val. return \<langle>l, val, rn\<rangle>)))) s)"
        using less.prems(1) unfolding xs_eq take_eq drop_eq by simp
      from split_create obtain l s1 where
        l: "Some (l, s1) \<in> set_dist (execute (create (take ?i xs)) s)"
        and rest1: "Some (r, t) \<in>
          set_dist (execute
            (create (drop ?i xs) \<bind>
              (\<lambda>rn. hash (concat (value l) (value rn)) \<bind>
                (\<lambda>val. return \<langle>l, val, rn\<rangle>))) s1)"
        by (rule set_dist_bindE) (rule that)
      from rest1 obtain rr s2 where
        rr: "Some (rr, s2) \<in> set_dist (execute (create (drop ?i xs)) s1)"
        and rest2: "Some (r, t) \<in>
          set_dist (execute
            (hash (concat (value l) (value rr)) \<bind>
              (\<lambda>val. return \<langle>l, val, rr\<rangle>)) s2)"
        by (rule set_dist_bindE) (rule that)
      from rest2 obtain val s3 where
        val: "Some (val, s3) \<in> set_dist (execute (hash (concat (value l) (value rr))) s2)"
        and ret: "Some (r, t) \<in> set_dist (execute (return \<langle>l, val, rr\<rangle>) s3)"
        by (auto elim!: set_dist_bindE)
      have r: "r = \<langle>l, val, rr\<rangle>"
        using ret by simp
      show ?thesis
      proof (cases "lgth = 1")
        case True
        then show ?thesis
          unfolding r by (simp add: floor_log_Suc_zero)
      next
        case False
        have lgth_ge: "2 \<le> lgth"
          using False less.prems by simp
        have half_pos: "0 < lgth div 2"
          using lgth_ge by simp
        have take_less: "length (take ?i xs) < length xs"
          using len_ge by simp
        have drop_less: "length (drop ?i xs) < length xs"
          using len_ge by simp
        have half_le_i: "lgth div 2 \<le> ?i"
          using less.prems(3) by simp
        have half_le_take: "lgth div 2 \<le> length (take ?i xs)"
          using half_le_i by simp
        have half_le_drop: "lgth div 2 \<le> length (drop ?i xs)"
          using half_le_i len_ge by simp
        have left_len:
          "length (get_authentication_path (lgth div 2) idx l) = floor_log (lgth div 2)"
          by (rule less.IH[OF take_less l half_pos half_le_take])
        have right_len:
          "length (get_authentication_path (lgth div 2) (idx - lgth div 2) rr) =
            floor_log (lgth div 2)"
          by (rule less.IH[OF drop_less rr half_pos half_le_drop])
        have floor_eq: "floor_log lgth = Suc (floor_log (lgth div 2))"
          using floor_log_rec[OF lgth_ge] .
        show ?thesis
        proof (cases "idx < lgth div 2")
          case True
          have "length (get_authentication_path lgth idx r) =
              Suc (floor_log (lgth div 2))"
            using False True left_len unfolding r by simp
          then show ?thesis
            by (simp only: floor_eq)
        next
          case False
          have "length (get_authentication_path lgth idx r) =
              Suc (floor_log (lgth div 2))"
            using \<open>lgth \<noteq> 1\<close> False right_len unfolding r by simp
          then show ?thesis
            by (simp only: floor_eq)
        qed
      qed
    qed
  qed
qed

lemma get_authentication_path_len:
  assumes "execute (create xs) s = d"
      and "x \<in> dom (dist d)"
      and "x = Some (r, h)"
      and "xs \<noteq> []"
    shows "length (get_authentication_path (length xs) idx r) = floor_log (length xs)"
proof -
  have support: "Some (r, h) \<in> set_dist (execute (create xs) s)"
    using assms(1-3) unfolding set_dist_def by simp
  show ?thesis
    by (rule create_get_authentication_path_len[OF support])
      (use assms(4) in simp_all)
qed

end

end
