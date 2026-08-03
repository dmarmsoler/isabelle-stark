(*  Title:      Stark/Staged_Security_Experiment_Composition_Tree_Output.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Tree_Output
  imports Staged_Security_Experiment_Composition
begin

text \<open>
  Bridges for the composition tree-output side event.

  The actual-alpha-prefix experiment carries the concrete alpha-prefix state
  through the verifier run.  This layer relates that path-specific event back
  to the ordinary checked data-state experiment, so later bounds can be proved
  once for the data-state event.
\<close>

context soundness
begin

lemma hash_map_new_output_hit_Un_iff:
  "hash_map_new_output_hit (A \<union> B) s t \<longleftrightarrow>
    hash_map_new_output_hit A s t \<or> hash_map_new_output_hit B s t"
  unfolding hash_map_new_output_hit_def by blast

lemma hash_new_output_hit_event_Un_iff:
  "hash_new_output_hit_event (A \<union> B) s out \<longleftrightarrow>
    hash_new_output_hit_event A s out \<or>
    hash_new_output_hit_event B s out"
  unfolding hash_new_output_hit_event_def
  by (cases out) (auto simp: hash_map_new_output_hit_Un_iff)

lemma hash_map_new_output_hit_tree_root_or_subtree:
  assumes hit: "hash_map_new_output_hit (set_tree tree) s t"
  shows
    "hash_map_new_output_hit {value tree} s t \<or>
      (\<exists>l v r. tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r) s t)"
  using hit
  unfolding hash_map_new_output_hit_def
  by (cases tree) auto

lemma hash_map_new_output_hit_two_trees_root_or_subtree:
  assumes hit:
    "hash_map_new_output_hit (set_tree trace_tree \<union> set_tree composition_tree)
      s t"
  shows
    "hash_map_new_output_hit {value trace_tree, value composition_tree} s t \<or>
      (\<exists>l v r. trace_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r) s t) \<or>
      (\<exists>l v r. composition_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r) s t)"
proof -
  from hit have split:
    "hash_map_new_output_hit (set_tree trace_tree) s t \<or>
     hash_map_new_output_hit (set_tree composition_tree) s t"
    unfolding hash_map_new_output_hit_Un_iff .
  from split show ?thesis
  proof
    assume trace_hit: "hash_map_new_output_hit (set_tree trace_tree) s t"
    from hash_map_new_output_hit_tree_root_or_subtree[OF trace_hit]
    show ?thesis
    proof
      assume root_hit: "hash_map_new_output_hit {value trace_tree} s t"
      have "hash_map_new_output_hit
          {value trace_tree, value composition_tree} s t"
        by (rule hash_map_new_output_hit_subset[OF _ root_hit]) auto
      then show ?thesis by simp
    next
      assume "\<exists>l v r. trace_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r) s t"
      then show ?thesis by blast
    qed
  next
    assume composition_hit:
      "hash_map_new_output_hit (set_tree composition_tree) s t"
    from hash_map_new_output_hit_tree_root_or_subtree[OF composition_hit]
    show ?thesis
    proof
      assume root_hit:
        "hash_map_new_output_hit {value composition_tree} s t"
      have "hash_map_new_output_hit
          {value trace_tree, value composition_tree} s t"
        by (rule hash_map_new_output_hit_subset[OF _ root_hit]) auto
      then show ?thesis by simp
    next
      assume "\<exists>l v r. composition_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r) s t"
      then show ?thesis by blast
    qed
  qed
qed

lemma card_set_tree_le_inorder_length:
  "card (set_tree t) \<le> length (inorder t)"
  using card_length[of "inorder t"]
  by simp

lemma protocol_created_tree_inorder_length_bound:
  assumes created: "protocol_created_tree xs t s"
  shows "length (inorder t) \<le> 2 * length xs - 1"
  using created
proof (induction xs arbitrary: t rule: length_induct)
  case (1 xs)
  show ?case
  proof (cases "length xs = 0")
    case True
    then have xs_eq: "xs = []"
      by simp
    then show ?thesis
      using "1.prems"
      unfolding protocol_created_tree_def
      by (simp add: protocol_merkle.created_tree.simps)
  next
    case False
    show ?thesis
    proof (cases "length xs = 1")
      case True
      then obtain x where xs_eq: "xs = [x]"
        by (cases xs) auto
      from protocol_created_tree_singletonD[OF "1.prems"[unfolded xs_eq]]
      obtain h where t_eq: "t = \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>"
        by blast
      then show ?thesis
        using xs_eq by simp
    next
      case False
      then have len_ge: "2 \<le> length xs"
        using \<open>length xs \<noteq> 0\<close> by linarith
      let ?i = "length xs div 2"
      have i_pos: "0 < ?i"
        using len_ge by simp
      have i_lt: "?i < length xs"
        using len_ge by simp
      from "1.prems" obtain l h r where
        i_def: "?i = length xs div 2"
        and
        t_eq: "t = \<langle>l, h, r\<rangle>"
        and left: "protocol_created_tree (take ?i xs) l s"
        and right: "protocol_created_tree (drop ?i xs) r s"
        using protocol_created_tree_internalD[OF "1.prems" len_ge]
        by blast
      have drop_lt: "length (drop ?i xs) < length xs"
        using i_pos by simp
      have right_bound: "length (inorder r) \<le>
          2 * length (drop ?i xs) - 1"
        using "1.IH"[rule_format, OF drop_lt, of r] right by simp
      have take_lt: "length (take ?i xs) < length xs"
        using i_lt by simp
      have left_bound: "length (inorder l) \<le>
          2 * length (take ?i xs) - 1"
        using "1.IH"[rule_format, OF take_lt, of l] left by simp
      have take_pos: "0 < length (take ?i xs)"
        using i_pos i_lt by simp
      have drop_pos: "0 < length (drop ?i xs)"
        using i_lt by simp
      have "length (inorder t) =
          Suc (length (inorder l) + length (inorder r))"
        using t_eq by simp
      also have "... \<le>
          Suc ((2 * length (take ?i xs) - 1) +
            (2 * length (drop ?i xs) - 1))"
        using left_bound right_bound by simp
      also have "... = 2 * length xs - 1"
        using take_pos drop_pos i_lt by simp
      finally show ?thesis .
    qed
  qed
qed

lemma created_tree_inorder_length_bound:
  assumes created: "created_tree xs t s"
  shows "length (inorder t) \<le> 2 * length xs - 1"
  using protocol_created_tree_inorder_length_bound[
      OF created[unfolded created_tree_def]]
  .

lemma created_tree_card_set_tree_bound:
  assumes created: "created_tree xs t s"
  shows "card (set_tree t) \<le> 2 * length xs - 1"
  by (rule order.trans[OF card_set_tree_le_inorder_length
        created_tree_inorder_length_bound[OF created]])

lemma protocol_merkle_created_tree_same_inputs_value_eq:
  assumes left: "protocol_merkle.created_tree xs left_tree s"
    and right: "protocol_merkle.created_tree xs right_tree s"
  shows "value left_tree = value right_tree"
  using assms
proof (induction xs arbitrary: left_tree right_tree rule: length_induct)
  case (1 xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      using "1.prems"
      by (simp add: protocol_merkle.created_tree.simps)
  next
    case (Cons x rest)
    have xs_cons: "xs = x # rest"
      using Cons by simp
    show ?thesis
    proof (cases rest)
      case Nil
      then obtain left_hash right_hash where
        left_tree:
          "left_tree = \<langle>\<langle>\<rangle>, left_hash, \<langle>\<rangle>\<rangle>"
          "fmlookup (HashMap s) x = Some left_hash"
        and right_tree:
          "right_tree = \<langle>\<langle>\<rangle>, right_hash, \<langle>\<rangle>\<rangle>"
          "fmlookup (HashMap s) x = Some right_hash"
        using "1.prems" Cons Nil
        by (auto simp: protocol_merkle.created_tree.simps)
      then show ?thesis by simp
    next
      case (Cons y ys)
      have xs_eq: "xs = x # y # ys"
        using xs_cons Cons by simp
      let ?i = "length xs div 2"
      have len: "2 \<le> length xs"
        using xs_eq by simp
      obtain ll lh lr i where i_def: "i = ?i"
        and left_tree_eq: "left_tree = \<langle>ll, lh, lr\<rangle>"
        and ll_created: "protocol_merkle.created_tree (take i xs) ll s"
        and lr_created: "protocol_merkle.created_tree (drop i xs) lr s"
        and lh_lookup:
          "fmlookup (HashMap s) (MerkleNode (value ll) (value lr)) =
            Some lh"
        using "1.prems"(1) xs_eq
        by (auto simp: protocol_merkle.created_tree.simps Let_def)
      obtain rl rh rr j where j_def: "j = ?i"
        and right_tree_eq: "right_tree = \<langle>rl, rh, rr\<rangle>"
        and rl_created: "protocol_merkle.created_tree (take j xs) rl s"
        and rr_created: "protocol_merkle.created_tree (drop j xs) rr s"
        and rh_lookup:
          "fmlookup (HashMap s) (MerkleNode (value rl) (value rr)) =
            Some rh"
        using "1.prems"(2) xs_eq
        by (auto simp: protocol_merkle.created_tree.simps Let_def)
      have j_i: "j = i"
        using i_def j_def by simp
      have i_pos: "0 < i"
        using i_def len by simp
      have i_lt: "i < length xs"
        using i_def len by simp
      have take_less: "length (take i xs) < length xs"
        using i_lt by simp
      have drop_less: "length (drop i xs) < length xs"
        using i_pos i_lt by simp
      have left_value: "value ll = value rl"
        by (rule "1.IH"[rule_format, OF take_less ll_created])
          (use rl_created j_i in simp)
      have right_value: "value lr = value rr"
        by (rule "1.IH"[rule_format, OF drop_less lr_created])
          (use rr_created j_i in simp)
      have "lh = rh"
        using lh_lookup rh_lookup left_value right_value by simp
      then show ?thesis
        using left_tree_eq right_tree_eq by simp
    qed
  qed
qed

lemma protocol_created_tree_same_table_value_eq:
  assumes left: "protocol_created_tree xs left_tree s"
    and right: "protocol_created_tree xs right_tree s"
  shows "value left_tree = value right_tree"
  by (rule protocol_merkle_created_tree_same_inputs_value_eq
      [OF left[unfolded protocol_created_tree_def]
          right[unfolded protocol_created_tree_def]])

lemma created_tree_same_table_value_eq:
  assumes left: "created_tree xs left_tree s"
    and right: "created_tree xs right_tree s"
  shows "value left_tree = value right_tree"
  by (rule protocol_created_tree_same_table_value_eq
      [OF left[unfolded created_tree_def] right[unfolded created_tree_def]])

definition merkle_node_child_output_relation
  :: "'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "merkle_node_child_output_relation x y \<longleftrightarrow>
      (\<exists>z. x = MerkleNode y z \<or> x = MerkleNode z y)"

lemma merkle_node_child_output_relation_values_subset:
  "{y. merkle_node_child_output_relation x y} \<subseteq>
    (case x of
      MerkleNode l r \<Rightarrow> {l, r}
    | _ \<Rightarrow> {})"
  unfolding merkle_node_child_output_relation_def
  by (cases x) auto

lemma merkle_node_child_output_relation_fiber_card_bound:
  "card {y. merkle_node_child_output_relation x y} \<le> 2"
proof -
  have finite_values:
    "finite
      (case x of
        MerkleNode l r \<Rightarrow> {l, r}
      | _ \<Rightarrow> {})"
    by (cases x) simp_all
  have "card {y. merkle_node_child_output_relation x y} \<le>
      card
        (case x of
          MerkleNode l r \<Rightarrow> {l, r}
        | _ \<Rightarrow> {})"
    by (rule card_mono[OF finite_values])
      (rule merkle_node_child_output_relation_values_subset)
  also have "... \<le> 2"
  proof (cases x)
    case (MerkleNode l r)
    then show ?thesis
      by (simp add: card_insert_if)
  qed simp_all
  finally show ?thesis .
qed

definition merkle_root_or_child_output_relation
  :: "'f set \<Rightarrow> 'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "merkle_root_or_child_output_relation roots x y \<longleftrightarrow>
      y \<in> roots \<or> merkle_node_child_output_relation x y"

lemma merkle_root_or_child_output_relation_values_subset:
  "{y. merkle_root_or_child_output_relation roots x y} \<subseteq>
    roots \<union>
      (case x of
        MerkleNode l r \<Rightarrow> {l, r}
      | _ \<Rightarrow> {})"
  unfolding merkle_root_or_child_output_relation_def
  using merkle_node_child_output_relation_values_subset
  by blast

lemma merkle_root_or_child_output_relation_fiber_card_bound:
  assumes finite_roots: "finite roots"
  shows "card {y. merkle_root_or_child_output_relation roots x y} \<le>
    card roots + 2"
proof -
  have finite_values:
    "finite
      (roots \<union>
        (case x of
          MerkleNode l r \<Rightarrow> {l, r}
        | _ \<Rightarrow> {}))"
    using finite_roots by (cases x) simp_all
  have "card {y. merkle_root_or_child_output_relation roots x y} \<le>
      card
        (roots \<union>
          (case x of
            MerkleNode l r \<Rightarrow> {l, r}
          | _ \<Rightarrow> {}))"
    by (rule card_mono[OF finite_values])
      (rule merkle_root_or_child_output_relation_values_subset)
  also have "... \<le>
      card roots +
      card
        (case x of
          MerkleNode l r \<Rightarrow> {l, r}
        | _ \<Rightarrow> {})"
  proof -
    show ?thesis
      by (rule card_Un_le)
  qed
  also have "... \<le> card roots + 2"
  proof (cases x)
    case (MerkleNode l r)
    then show ?thesis
      by (simp add: card_insert_if)
  qed simp_all
  finally show ?thesis .
qed

lemma hash_relation_program_protocol_check_authentication_path_raw:
  fixes leaf :: "'f protocol_hash_input"
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b (Suc (length path))
    (protocol_merkle.check_authentication_path len i leaf path ::
      ('f, 'f protocol_channel) state_monad)"
proof (induction path arbitrary: len i)
  case Nil
  have "hash_relation_program R b 1
      (hash leaf :: ('f, 'f protocol_channel) state_monad)"
    by (rule hash_relation_program_hash[OF fibers])
  then show ?case
    by (simp add: protocol_merkle.check_authentication_path.simps)
next
  case (Cons a path)
  show ?case
  proof (cases "i < len div 2")
    case True
    have rec:
      "hash_relation_program R b (Suc (length path))
        (protocol_merkle.check_authentication_path (len div 2) i leaf path ::
          ('f, 'f protocol_channel) state_monad)"
      using Cons.IH[of "len div 2" i] by simp
    have bound:
      "hash_relation_program R b (Suc (length path) + 1)
        ((protocol_merkle.check_authentication_path (len div 2) i leaf path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>x. hash (MerkleNode x a)))"
      by (rule hash_relation_program_bind)
        (rule rec, rule hash_relation_program_hash[OF fibers])
    show ?thesis
      using True bound
      by (simp add: protocol_merkle.check_authentication_path.simps)
  next
    case False
    have rec:
      "hash_relation_program R b (Suc (length path))
        (protocol_merkle.check_authentication_path
          (len div 2) (i - len div 2) leaf path ::
          ('f, 'f protocol_channel) state_monad)"
      using Cons.IH[of "len div 2" "i - len div 2"] by simp
    have bound:
      "hash_relation_program R b (Suc (length path) + 1)
        ((protocol_merkle.check_authentication_path
          (len div 2) (i - len div 2) leaf path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>x. hash (MerkleNode a x)))"
      by (rule hash_relation_program_bind)
        (rule rec, rule hash_relation_program_hash[OF fibers])
    show ?thesis
      using False bound
      by (simp add: protocol_merkle.check_authentication_path.simps)
  qed
qed

lemma hash_relation_program_check_authentication_path:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b (Suc (length path))
    (check_authentication_path len i v path)"
  unfolding check_authentication_path_def protocol_check_authentication_path_def
  by (rule hash_relation_program_protocol_check_authentication_path_raw
      [OF fibers])

lemma hash_relation_program_check_authentication_path_assert_return:
  fixes path :: "'f list"
    and v root :: "'f"
    and r :: "'r"
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b (Suc (length path))
      ((check_authentication_path len i v path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = root) \<bind> (\<lambda>_. return r)))"
proof -
  have tail:
    "hash_relation_program R b (0 + 0)
      (assert (ap = root) \<bind> (\<lambda>_. return r) ::
        ('r, 'f protocol_channel) state_monad)"
    for ap
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_assert, rule hash_relation_program_zero
        [OF hash_map_preserving_return])
  have "hash_relation_program R b (Suc (length path) + (0 + 0))
      ((check_authentication_path len i v path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = root) \<bind> (\<lambda>_. return r)))"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_check_authentication_path[OF fibers],
        rule tail)
  then show ?thesis by simp
qed

lemma hash_relation_program_check_authentication_path_assert_bind:
  fixes path :: "'f list"
    and v root :: "'f"
    and k :: "unit \<Rightarrow> ('r, 'f protocol_channel) state_monad"
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
    and k: "\<And>u. hash_relation_program R b n (k u)"
  shows
    "hash_relation_program R b (Suc (length path) + n)
      ((check_authentication_path len i v path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = root) \<bind> k))"
proof -
  have tail:
    "hash_relation_program R b (0 + n)
      (assert (ap = root) \<bind> k ::
        ('r, 'f protocol_channel) state_monad)"
    for ap
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_assert, rule k)
  have "hash_relation_program R b (Suc (length path) + (0 + n))
      ((check_authentication_path len i v path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = root) \<bind> k))"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_check_authentication_path[OF fibers],
        rule tail)
  then show ?thesis by simp
qed

lemma hash_relation_program_read:
  "hash_relation_program R b 0
    (read :: ('f, 'f, unit) protocol_c_monad)"
  by (rule hash_relation_program_zero)
    (rule hash_map_preserving_read)

lemma hash_relation_program_ntimes:
  fixes m :: "('x, 'f protocol_channel) state_monad"
  assumes m: "hash_relation_program R b n m"
  shows "hash_relation_program R b (k * n) (ntimes m k)"
  using m
proof (induction k)
  case 0
  then show ?case
    by (simp add: hash_relation_program_zero[OF hash_map_preserving_return])
next
  case (Suc k)
  have tail: "hash_relation_program R b (k * n) (ntimes m k)"
    using Suc.IH Suc.prems by simp
  have cont:
    "hash_relation_program R b (k * n + 0)
      (ntimes m k \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule hash_relation_program_bind)
      (rule tail, rule hash_relation_program_zero[OF hash_map_preserving_return])
  have "hash_relation_program R b (n + (k * n + 0))
      (m \<bind> (\<lambda>x. ntimes m k \<bind> (\<lambda>xs. return (x # xs))))"
    by (rule hash_relation_program_bind[OF Suc.prems cont])
  then show ?case by simp
qed

lemma hash_relation_program_mmap:
  fixes ms :: "('x, 'f protocol_channel) state_monad list"
  assumes ms: "\<And>m. m \<in> set ms \<Longrightarrow> hash_relation_program R b n m"
  shows "hash_relation_program R b (length ms * n) (mmap ms)"
  using ms
proof (induction ms)
  case Nil
  then show ?case
    by (simp add: hash_relation_program_zero[OF hash_map_preserving_return])
next
  case (Cons m ms)
  have head: "hash_relation_program R b n m"
    using Cons.prems by simp
  have tail: "hash_relation_program R b (length ms * n) (mmap ms)"
    using Cons.IH Cons.prems by simp
  have cont:
    "hash_relation_program R b (length ms * n + 0)
      (mmap ms \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule hash_relation_program_bind)
      (rule tail, rule hash_relation_program_zero[OF hash_map_preserving_return])
  have "hash_relation_program R b (n + (length ms * n + 0))
      (m \<bind> (\<lambda>x. mmap ms \<bind> (\<lambda>xs. return (x # xs))))"
    by (rule hash_relation_program_bind[OF head cont])
  then show ?case by simp
qed

lemma hash_relation_program_mfold:
  fixes steps :: "('x \<Rightarrow> ('x, 'f protocol_channel) state_monad) list"
  assumes steps:
    "\<And>step x. step \<in> set steps \<Longrightarrow>
      hash_relation_program R b n (step x)"
  shows "hash_relation_program R b (length steps * n) (mfold x steps)"
  using steps
proof (induction steps arbitrary: x)
  case Nil
  then show ?case
    by (simp add: hash_relation_program_zero[OF hash_map_preserving_return])
next
  case (Cons step steps)
  have head: "hash_relation_program R b n (step x)"
    using Cons.prems by simp
  have tail:
    "\<And>y. hash_relation_program R b (length steps * n) (mfold y steps)"
    using Cons.IH Cons.prems by simp
  have "hash_relation_program R b (n + length steps * n)
      (step x \<bind> (\<lambda>y. mfold y steps))"
    by (rule hash_relation_program_bind[OF head tail])
  then show ?case by simp
qed

lemma hash_relation_program_ntimes_read_bind:
  fixes k :: "'f list \<Rightarrow> ('y, 'f protocol_channel) state_monad"
  assumes k:
    "\<And>xs. length xs = n \<Longrightarrow> hash_relation_program R b q (k xs)"
  shows
    "hash_relation_program R b q
      ((ntimes read n :: ('f list, 'f protocol_channel) state_monad) \<bind> k)"
proof -
  have reads:
    "hash_relation_program R b (n * 0)
      (ntimes read n :: ('f list, 'f protocol_channel) state_monad)"
    by (rule hash_relation_program_ntimes[OF hash_relation_program_read])
  have "hash_relation_program R b (n * 0 + q)
      ((ntimes read n :: ('f list, 'f protocol_channel) state_monad) \<bind> k)"
  proof (rule hash_relation_program_bind_on_outcomes[OF reads])
    fix s xs t
    assume out:
      "Some (xs, t) \<in>
        set_dist
          (execute
            (ntimes read n :: ('f list, 'f protocol_channel) state_monad)
            s)"
    then have "length xs = n"
      using ntimes_read_any_outcome by blast
    then show "hash_relation_program R b q (k xs)"
      by (rule k)
  qed
  then show ?thesis by simp
qed

lemma hash_relation_program_check_decommit_on_query_step:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b (Suc (floor_log (scale * clength)))
      (do {
        qh \<leftarrow> read;
        let len = scale * clength;
        qh_path \<leftarrow> ntimes read (floor_log len);
        ap \<leftarrow> check_authentication_path len i qh qh_path;
        assert (ap = fr);
        return qh
      })"
proof -
  let ?len = "scale * clength"
  have after_path:
    "hash_relation_program R b (Suc (floor_log ?len))
      ((check_authentication_path ?len i qh qh_path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
    if path_len: "length qh_path = floor_log ?len"
    for qh qh_path
    using path_len
    by (subst path_len[symmetric])
      (rule hash_relation_program_check_authentication_path_assert_return
        [OF fibers])
  have after_reads:
    "hash_relation_program R b (Suc (floor_log ?len))
      ((ntimes read (floor_log ?len) ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>qh_path.
          (check_authentication_path ?len i qh qh_path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))"
    for qh
    by (rule hash_relation_program_ntimes_read_bind)
      (rule after_path)
  have "hash_relation_program R b (0 + Suc (floor_log ?len))
      (read \<bind>
        (\<lambda>qh.
          (ntimes read (floor_log ?len) ::
            ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>qh_path.
            (check_authentication_path ?len i qh qh_path ::
              ('f, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))))"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_read, rule after_reads)
  then show ?thesis
    by (simp add: Let_def)
qed

lemma hash_relation_program_check_decommit_on_query:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (length (powers_scaled idx) * Suc (floor_log (scale * clength)))
      (mmap (check_decommit_on_query fr idx))"
proof -
  let ?step =
    "\<lambda>i. do {
      qh \<leftarrow> read;
      let len = scale * clength;
      qh_path \<leftarrow> ntimes read (floor_log len);
      ap \<leftarrow> check_authentication_path len i qh qh_path;
      assert (ap = fr);
      return qh
    }"
  have mapped_general:
    "\<And>xs. hash_relation_program R b
      (length xs + length xs * floor_log (scale * clength))
      (mmap (map ?step xs))"
  proof -
    fix xs
    show "hash_relation_program R b
      (length xs + length xs * floor_log (scale * clength))
      (mmap (map ?step xs))"
    proof (induction xs)
    case Nil
    then show ?case
      by (simp add: hash_relation_program_zero[OF hash_map_preserving_return])
  next
    case (Cons i rest)
    have head:
      "hash_relation_program R b (Suc (floor_log (scale * clength)))
        (?step i)"
      by (rule hash_relation_program_check_decommit_on_query_step[OF fibers])
    have tail:
      "hash_relation_program R b
        (length rest + length rest * floor_log (scale * clength))
        (mmap (map ?step rest))"
      by (rule Cons.IH)
    have cont:
      "hash_relation_program R b
        ((length rest + length rest * floor_log (scale * clength)) + 0)
        (mmap (map ?step rest) \<bind> (\<lambda>xs. return (x # xs)))"
      for x
      by (rule hash_relation_program_bind)
        (rule tail, rule hash_relation_program_zero[OF hash_map_preserving_return])
    have "hash_relation_program R b
        (Suc (floor_log (scale * clength)) +
          ((length rest + length rest * floor_log (scale * clength)) + 0))
        (?step i \<bind> (\<lambda>x. mmap (map ?step rest) \<bind>
          (\<lambda>xs. return (x # xs))))"
      by (rule hash_relation_program_bind[OF head cont])
    then show ?case
      by (simp add: algebra_simps)
    qed
  qed
  have mapped:
    "hash_relation_program R b
      (length (powers_scaled idx) +
        length (powers_scaled idx) * floor_log (scale * clength))
      (mmap (map ?step (powers_scaled idx)))"
    by (rule mapped_general)
  show ?thesis
    using mapped
    unfolding check_decommit_on_query_def by simp
qed

lemma hash_relation_program_fri_layer_opening_finish:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
    and xp_path_len: "length xp_path = floor_log len"
    and xn_path_len: "length xn_path = floor_log len"
  shows
    "hash_relation_program R b
      (Suc (floor_log len) + Suc (floor_log len))
      (fri_layer_opening_finish b' f i x len pw xp xp_path xn xn_path)"
proof -
  let ?H = "Suc (floor_log len)"
  let ?sidx = "(i + len div 2) mod len"
  let ?out =
    "(i mod (len div 2),
      (xp + xn) div 2 +
        b' * ((xp - xn) div (2 * ((h ^ i) * shift) ^ pw)),
      len div 2, pw + pw)"
  have second:
    "hash_relation_program R b ?H
      ((check_authentication_path len ?sidx xn xn_path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out)))"
    by (subst xn_path_len[symmetric])
      (rule hash_relation_program_check_authentication_path_assert_return
        [OF fibers])
  have first0:
    "hash_relation_program R b (Suc (length xp_path) + ?H)
      ((check_authentication_path len i xp xp_path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out)))))"
    by (rule hash_relation_program_check_authentication_path_assert_bind
        [OF fibers])
      (use second in simp)
  have first:
    "hash_relation_program R b (?H + ?H)
      ((check_authentication_path len i xp xp_path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out)))))"
    using first0 xp_path_len by simp
  have raw:
    "hash_relation_program R b (0 + (?H + ?H))
      ((assert (xp = x) ::
          (unit, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>_.
          (check_authentication_path len i xp xp_path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = f) \<bind>
            (\<lambda>_.
              (check_authentication_path len ?sidx xn xn_path ::
                ('f, 'f protocol_channel) state_monad) \<bind>
              (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_assert, rule first)
  show ?thesis
    using raw unfolding fri_layer_opening_finish_def
    by (simp add: Let_def)
qed

lemma hash_relation_program_fri_layer_opening_step:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (Suc (floor_log len) + Suc (floor_log len))
      (fri_layer_opening_step (b', f) (i, x, len, pw))"
proof -
  let ?N = "Suc (floor_log len) + Suc (floor_log len)"
  have after_xn_path:
    "hash_relation_program R b ?N
      ((ntimes read (floor_log len) ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xn_path.
          fri_layer_opening_finish b' f i x len pw xp xp_path xn xn_path))"
    if xp_path_len: "length xp_path = floor_log len"
    for xp xp_path xn
  proof (rule hash_relation_program_ntimes_read_bind)
    fix xn_path :: "'f list"
    assume xn_path_len: "length xn_path = floor_log len"
    show "hash_relation_program R b ?N
      (fri_layer_opening_finish b' f i x len pw xp xp_path xn xn_path)"
      by (rule hash_relation_program_fri_layer_opening_finish
          [OF fibers xp_path_len xn_path_len])
  qed
  have after_xn:
    "hash_relation_program R b ?N
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b' f i x len pw xp xp_path xn xn_path)))"
    if xp_path_len: "length xp_path = floor_log len"
    for xp xp_path
  proof -
    have "hash_relation_program R b (0 + ?N)
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b' f i x len pw xp xp_path xn xn_path)))"
      by (rule hash_relation_program_bind)
        (rule hash_relation_program_read, rule after_xn_path[OF xp_path_len])
    then show ?thesis by simp
  qed
  have after_xp_path:
    "hash_relation_program R b ?N
      ((ntimes read (floor_log len) ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xp_path.
          read \<bind>
          (\<lambda>xn.
            (ntimes read (floor_log len) ::
              ('f list, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>xn_path.
              fri_layer_opening_finish b' f i x len pw xp xp_path xn xn_path))))"
    for xp
  proof (rule hash_relation_program_ntimes_read_bind)
    fix xp_path :: "'f list"
    assume xp_path_len: "length xp_path = floor_log len"
    show "hash_relation_program R b ?N
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b' f i x len pw xp xp_path xn xn_path)))"
      by (rule after_xn[OF xp_path_len])
  qed
  have "hash_relation_program R b (0 + ?N)
      (read \<bind>
        (\<lambda>xp.
          (ntimes read (floor_log len) ::
            ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xp_path.
            read \<bind>
            (\<lambda>xn.
              (ntimes read (floor_log len) ::
                ('f list, 'f protocol_channel) state_monad) \<bind>
              (\<lambda>xn_path.
                fri_layer_opening_finish b' f i x len pw xp xp_path xn xn_path)))))"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_read, rule after_xp_path)
  then show ?thesis
    unfolding fri_layer_opening_step_unfold_finish by simp
qed

lemma hash_relation_program_fri_layer_opening_steps_mfold_state:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
    and init:
      "case st of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
  shows
    "hash_relation_program R b
      (length fl * (Suc L + Suc L))
      (mfold st (map fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
  using init
proof (induction fl arbitrary: st)
  case Nil
  then show ?case
    by (simp add: hash_relation_program_zero[OF hash_map_preserving_return])
next
  case (Cons bf fl)
  obtain i x len pw where st_eq: "st = (i, x, len, pw)"
    by (cases st)
  obtain b' f where bf_eq: "bf = (b', f)"
    by (cases bf)
  let ?N = "Suc L + Suc L"
  have head_exact:
    "hash_relation_program R b
      (Suc (floor_log len) + Suc (floor_log len))
      (fri_layer_opening_step (b', f) (i, x, len, pw))"
    by (rule hash_relation_program_fri_layer_opening_step[OF fibers])
  have head_le:
    "Suc (floor_log len) + Suc (floor_log len) \<le> ?N"
    using Cons.prems unfolding st_eq by simp
  have head:
    "hash_relation_program R b ?N
      (fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    unfolding bf_eq st_eq
    by (rule hash_relation_program_mono[OF head_le head_exact])
  have tail:
    "hash_relation_program R b (length fl * ?N)
      (mfold z (map fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    if out:
      "Some (z, t) \<in>
        set_dist (execute (fri_layer_opening_step bf st) s)"
    for z and s :: "'f protocol_channel" and t :: "'f protocol_channel"
  proof -
    from fri_layer_opening_step_outcome[OF out[unfolded bf_eq st_eq]]
    obtain xp xp_path xn xn_path x' where
      z_eq: "z = (i mod (len div 2), x', len div 2, pw + pw)"
      by blast
    have len_le: "floor_log len \<le> L"
      using Cons.prems unfolding st_eq by simp
    have next_len: "floor_log (len div 2) \<le> L"
      using floor_log_div2_le_self[of len] len_le by linarith
    have z_inv:
      "case z of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
      unfolding z_eq using next_len by simp
    show ?thesis
      by (rule Cons.IH[OF z_inv])
  qed
  have "hash_relation_program R b (?N + length fl * ?N)
      ((fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>z. mfold z (map fri_layer_opening_step fl)))"
    by (rule hash_relation_program_bind_on_outcomes[OF head]) (rule tail)
  then show ?case
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_relation_program_receive_query_commits_mfold:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
    and init: "floor_log len \<le> L"
  shows
    "hash_relation_program R b
      (length fl * (Suc L + Suc L))
      (mfold (i, x, len, pw) (receive_query_commits fl))"
  unfolding receive_query_commits_eq_fri_layer_opening_steps
proof -
  have st_inv:
    "case (i, x, len, pw) of
      (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
    using init by simp
  show "hash_relation_program R b (length fl * (Suc L + Suc L))
    (mfold (i, x, len, pw) (map fri_layer_opening_step fl) ::
      (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    by (rule hash_relation_program_fri_layer_opening_steps_mfold_state
        [OF fibers st_inv])
qed

lemma hash_relation_program_check_decommit_on_query_exact:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b verifier_query_decommit_hash_budget
      (mmap (check_decommit_on_query fr idx))"
proof -
  have exact:
    "hash_relation_program R b
      (length (powers_scaled idx) * Suc (floor_log (scale * clength)))
      (mmap (check_decommit_on_query fr idx))"
    by (rule hash_relation_program_check_decommit_on_query[OF fibers])
  show ?thesis
    using exact
    unfolding verifier_query_decommit_hash_budget_def powers_scaled_def
    by (simp add: mult.commute)
qed

lemma hash_relation_program_verifier_query_round_program_exact:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (1 + verifier_query_decommit_hash_budget +
        (length f_fl + length fl) * verifier_fri_layer_hash_budget)
      (verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?L = "floor_log (clength * scale)"
  let ?B = "verifier_fri_layer_hash_budget"
  have B_eq: "?B = Suc ?L + Suc ?L"
    unfolding verifier_fri_layer_hash_budget_def by simp
  have after_comp:
    "hash_relation_program R b (length fl * ?B + 0)
      ((mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))"
    for idx fv
  proof (rule hash_relation_program_bind)
    show "hash_relation_program R b (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_relation_program_receive_query_commits_mfold)
        (rule fibers, simp)
    show "\<And>x. hash_relation_program R b 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, 'f protocol_channel) state_monad)"
      by (simp add: hash_relation_program_assert split: prod.splits)
  qed
  have after_trace:
    "hash_relation_program R b
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pow).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
    for idx fv
  proof (rule hash_relation_program_bind)
    show "hash_relation_program R b (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_relation_program_receive_query_commits_mfold)
        (rule fibers, simp)
    fix x :: "nat \<times> 'f \<times> nat \<times> nat"
    obtain f_i f_x f_len f_pow where x_eq:
      "x = (f_i, f_x, f_len, f_pow)"
      by (cases x) auto
    have case_budget:
      "hash_relation_program R b (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule hash_relation_program_bind)
        (rule hash_relation_program_assert, rule after_comp)
    show "hash_relation_program R b (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, f_pow) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, 'f protocol_channel) state_monad)"
      using case_budget
      unfolding x_eq
      by (simp split: prod.splits)
  qed
  have after_query:
    "hash_relation_program R b
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + (0 + (length fl * ?B + 0))))
      (mmap (check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_check_decommit_on_query_exact[OF fibers],
        rule after_trace)
  have after_query_simple:
    "hash_relation_program R b
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      (mmap (check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    using after_query[of idx] by simp
  have after_random:
    "hash_relation_program R b
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      ((let idx' = index (to_nat idx) in
          mmap (check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    for idx
    using after_query_simple[of "index (to_nat idx)"]
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
  have "hash_relation_program R b
      (1 + (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B)))
      (receive_query_index_challenge \<bind>
        (\<lambda>idx.
          let idx' = index (to_nat idx) in
          mmap (check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_receive_query_index_challenge[OF fibers],
        rule after_random)
  then show ?thesis
    unfolding verifier_query_round_program_def
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
qed

lemma hash_relation_program_verifier_query_round_program:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
    and len_f: "length f_fl \<le> ceil_log clength"
    and len_c: "length fl \<le> ceil_log (maxDegree + 1)"
  shows
    "hash_relation_program R b verifier_query_round_hash_budget
      (verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?N = "verifier_fri_layer_hash_budget"
  have exact:
    "hash_relation_program R b
      (1 + verifier_query_decommit_hash_budget +
        (length f_fl + length fl) * ?N)
      (verifier_query_round_program fr f_fl f_final as fl final)"
    by (rule hash_relation_program_verifier_query_round_program_exact
        [OF fibers])
  have le:
    "1 + verifier_query_decommit_hash_budget +
        (length f_fl + length fl) * ?N
      \<le> verifier_query_round_hash_budget"
    using len_f len_c
    unfolding verifier_query_round_hash_budget_def
    by simp
  show ?thesis
    by (rule hash_relation_program_mono[OF le exact])
qed

lemma wp_verifier_query_round_program_hash_relation_hit_bound:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
    and len_f: "length f_fl \<le> ceil_log clength"
    and len_c: "length fl \<le> ceil_log (maxDegree + 1)"
  shows
    "wp_event
      (verifier_query_round_program fr f_fl f_final as fl final)
      (hash_relation_hit_event R s) s \<le>
      hash_relation_budget_value b verifier_query_round_hash_budget"
proof -
  have program:
    "hash_relation_program R b verifier_query_round_hash_budget
      (verifier_query_round_program fr f_fl f_final as fl final)"
    by (rule hash_relation_program_verifier_query_round_program
        [OF fibers len_f len_c])
  then show ?thesis
    unfolding hash_relation_program_def hash_relation_budget_def by blast
qed

lemma wp_verifier_query_round_program_merkle_root_or_child_relation_bound:
  assumes finite_roots: "finite roots"
    and len_f: "length f_fl \<le> ceil_log clength"
    and len_c: "length fl \<le> ceil_log (maxDegree + 1)"
  shows
    "wp_event
      (verifier_query_round_program fr f_fl f_final as fl final)
      (hash_relation_hit_event
        (merkle_root_or_child_output_relation roots) s) s \<le>
      hash_relation_budget_value (card roots + 2)
        verifier_query_round_hash_budget"
  by (rule wp_verifier_query_round_program_hash_relation_hit_bound)
    (rule merkle_root_or_child_output_relation_fiber_card_bound
      [OF finite_roots], rule len_f, rule len_c)

lemma hash_relation_program_ntimes_verifier_query_round_program:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
    and len_f: "length f_fl \<le> ceil_log clength"
    and len_c: "length fl \<le> ceil_log (maxDegree + 1)"
  shows
    "hash_relation_program R b (n * verifier_query_round_hash_budget)
      (ntimes
        (verifier_query_round_program fr f_fl f_final as fl final) n)"
proof (rule hash_relation_program_ntimes)
  show "\<And>x.
      hash_relation_program R b verifier_query_round_hash_budget
        (verifier_query_round_program fr f_fl f_final as fl final)"
    by (rule hash_relation_program_verifier_query_round_program
        [OF fibers len_f len_c])
qed

lemma wp_ntimes_verifier_query_round_program_hash_relation_hit_bound:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
    and len_f: "length f_fl \<le> ceil_log clength"
    and len_c: "length fl \<le> ceil_log (maxDegree + 1)"
  shows
    "wp_event
      (ntimes
        (verifier_query_round_program fr f_fl f_final as fl final) n)
      (hash_relation_hit_event R s) s \<le>
      hash_relation_budget_value b
        (n * verifier_query_round_hash_budget)"
proof -
  have program:
    "hash_relation_program R b (n * verifier_query_round_hash_budget)
      (ntimes
        (verifier_query_round_program fr f_fl f_final as fl final) n)"
    by (rule hash_relation_program_ntimes_verifier_query_round_program
        [OF fibers len_f len_c])
  then show ?thesis
    unfolding hash_relation_program_def hash_relation_budget_def by blast
qed

lemma wp_ntimes_verifier_query_round_program_merkle_root_or_child_relation_bound:
  assumes finite_roots: "finite roots"
    and len_f: "length f_fl \<le> ceil_log clength"
    and len_c: "length fl \<le> ceil_log (maxDegree + 1)"
  shows
    "wp_event
      (ntimes
        (verifier_query_round_program fr f_fl f_final as fl final) n)
      (hash_relation_hit_event
        (merkle_root_or_child_output_relation roots) s) s \<le>
      hash_relation_budget_value (card roots + 2)
        (n * verifier_query_round_hash_budget)"
  by (rule wp_ntimes_verifier_query_round_program_hash_relation_hit_bound)
    (rule merkle_root_or_child_output_relation_fiber_card_bound
      [OF finite_roots], rule len_f, rule len_c)

definition checked_staged_security_with_actual_alpha_prefix_tree_output_case
  where
    "checked_staged_security_with_actual_alpha_prefix_tree_output_case P out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, _) \<Rightarrow>
          (let packed = fst (fst x);
               prefix_state = snd (fst packed);
               data = snd packed;
               attacker_state = snd (fst x);
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>result final_state trace_table composition_table as
              query_idxs dg composition_fri_roots final rest trace_tree
              composition_tree.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            verifier_header_transcript s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              as dg composition_fri_roots final rest \<and>
            created_tree trace_table trace_tree final_state \<and>
            created_tree composition_table composition_tree final_state \<and>
            P trace_tree composition_tree prefix_state final_state))"

definition checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit =
      checked_staged_security_with_actual_alpha_prefix_tree_output_case
        (\<lambda>trace_tree composition_tree prefix_state final_state.
          hash_map_new_output_hit
            {value trace_tree, value composition_tree}
            prefix_state final_state)"

definition
  checked_staged_security_with_actual_alpha_prefix_tree_subtree_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_tree_subtree_output_hit =
      checked_staged_security_with_actual_alpha_prefix_tree_output_case
        (\<lambda>trace_tree composition_tree prefix_state final_state.
          (\<exists>l v r. trace_tree = \<langle>l, v, r\<rangle> \<and>
            hash_map_new_output_hit (set_tree l \<union> set_tree r)
              prefix_state final_state) \<or>
          (\<exists>l v r. composition_tree = \<langle>l, v, r\<rangle> \<and>
            hash_map_new_output_hit (set_tree l \<union> set_tree r)
              prefix_state final_state))"

lemma checked_staged_security_with_actual_alpha_prefix_tree_output_hit_imp_root_or_subtree:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_tree_output_hit out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit out \<or>
      checked_staged_security_with_actual_alpha_prefix_tree_subtree_output_hit
        out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_tree_output_hit_def
    by simp
next
  case (Some result_pack)
  then obtain x checked_final_state where out_eq:
      "out = Some (x, checked_final_state)"
    by (cases result_pack) simp
  let ?packed = "fst (fst x)"
  let ?prefix_state = "snd (fst ?packed)"
  let ?data = "snd ?packed"
  let ?attacker_state = "snd (fst x)"
  let ?s =
    "verifier_state_from_adversary ?attacker_state
      (staged_proof_transcript ?data)"
  from hit obtain result final_state trace_table composition_table as
      query_idxs dg composition_fri_roots final rest trace_tree
      composition_tree where
    verify_out:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root ?data)
        (staged_trace_fri_roots ?data)
        (staged_trace_final ?data)
        as dg composition_fri_roots final rest"
    and trace_created:
      "created_tree trace_table trace_tree final_state"
    and composition_created:
      "created_tree composition_table composition_tree final_state"
    and tree_hit:
      "hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        ?prefix_state final_state"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_tree_output_hit_def
      Let_def
    apply simp
    by blast
  have split:
    "hash_map_new_output_hit
        {value trace_tree, value composition_tree}
        ?prefix_state final_state \<or>
      (\<exists>l v r. trace_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r)
          ?prefix_state final_state) \<or>
      (\<exists>l v r. composition_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r)
          ?prefix_state final_state)"
    by (rule hash_map_new_output_hit_two_trees_root_or_subtree
        [OF tree_hit])
  from split show ?thesis
  proof
    assume root_hit:
      "hash_map_new_output_hit
        {value trace_tree, value composition_tree}
        ?prefix_state final_state"
    have "checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit
        out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit_def
        checked_staged_security_with_actual_alpha_prefix_tree_output_case_def
        Let_def
      using verify_out bound header trace_created composition_created root_hit
      apply simp
      by blast
    then show ?thesis by simp
  next
    assume subtree_hit:
      "(\<exists>l v r. trace_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r)
          ?prefix_state final_state) \<or>
      (\<exists>l v r. composition_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r)
          ?prefix_state final_state)"
    have
      "checked_staged_security_with_actual_alpha_prefix_tree_subtree_output_hit
        out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_tree_subtree_output_hit_def
        checked_staged_security_with_actual_alpha_prefix_tree_output_case_def
        Let_def
      using verify_out bound header trace_created composition_created
        subtree_hit
      apply simp
      by blast
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_tree_output_hit_bound_from_root_and_subtree:
  assumes root_bound:
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit s
      \<le> R"
    and subtree_bound:
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_tree_subtree_output_hit s
      \<le> S"
  shows
    "wp_event m checked_staged_security_with_actual_alpha_prefix_tree_output_hit
      s \<le> R + S"
proof -
  have
    "wp_event m checked_staged_security_with_actual_alpha_prefix_tree_output_hit
      s \<le>
     wp_event m
      (\<lambda>out.
        checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit
          out \<or>
        checked_staged_security_with_actual_alpha_prefix_tree_subtree_output_hit
          out)
      s"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_actual_alpha_prefix_tree_output_hit_imp_root_or_subtree)
  also have "... \<le>
      wp_event m
        checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit s +
      wp_event m
        checked_staged_security_with_actual_alpha_prefix_tree_subtree_output_hit
        s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + S"
    by (rule add_mono[OF root_bound subtree_bound])
  finally show ?thesis .
qed

definition checked_staged_security_with_actual_alpha_prefix_transcript_root_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_transcript_root_output_hit
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, _) \<Rightarrow>
          (let packed = fst (fst x);
               prefix_state = snd (fst packed);
               data = snd packed;
               attacker_state = snd (fst x);
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>result final_state trace_table composition_table as
              query_idxs dg composition_fri_roots final rest.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            verifier_header_transcript s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              as dg composition_fri_roots final rest \<and>
            hash_map_new_output_hit
              {staged_trace_root data, hd composition_fri_roots}
              prefix_state final_state))"

lemma checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit_imp_transcript_root_output_hit:
  assumes root_hit:
    "checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_transcript_root_output_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using root_hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit_def
      checked_staged_security_with_actual_alpha_prefix_tree_output_case_def
    by simp
next
  case (Some result_pack)
  then obtain x checked_final_state where out_eq:
      "out = Some (x, checked_final_state)"
    by (cases result_pack) simp
  let ?packed = "fst (fst x)"
  let ?prefix_state = "snd (fst ?packed)"
  let ?data = "snd ?packed"
  let ?attacker_state = "snd (fst x)"
  let ?s =
    "verifier_state_from_adversary ?attacker_state
      (staged_proof_transcript ?data)"
  from root_hit obtain result final_state trace_table composition_table as
      query_idxs dg composition_fri_roots final rest trace_tree
      composition_tree where
    verify_out:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root ?data)
        (staged_trace_fri_roots ?data)
        (staged_trace_final ?data)
        as dg composition_fri_roots final rest"
    and trace_created:
      "created_tree trace_table trace_tree final_state"
    and composition_created:
      "created_tree composition_table composition_tree final_state"
    and tree_root_hit:
      "hash_map_new_output_hit
        {value trace_tree, value composition_tree}
        ?prefix_state final_state"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit_def
      checked_staged_security_with_actual_alpha_prefix_tree_output_case_def
      Let_def
    apply simp
    by blast
  from bound obtain fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    header':
      "verifier_header_transcript ?s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and trace_bind:
      "merkle_root_binds_table fr' trace_table final_state"
    and composition_bind:
      "merkle_root_binds_table (hd composition_fri_roots')
        composition_table final_state"
    unfolding accepted_with_bound_tables_def by auto
  have header_eq:
    "fr' = staged_trace_root ?data \<and>
     f_fri_roots' = staged_trace_fri_roots ?data \<and>
     f_final' = staged_trace_final ?data \<and>
     dg' = dg \<and>
     composition_fri_roots' = composition_fri_roots \<and>
     final' = final \<and>
     rest' = rest"
    using verifier_header_transcript_unique[OF header' header]
    by simp
  then have fr_eq: "fr' = staged_trace_root ?data"
    and comp_roots_eq:
      "composition_fri_roots' = composition_fri_roots"
    by simp_all
  from trace_bind obtain trace_root_tree where
    trace_root_created:
      "created_tree trace_table trace_root_tree final_state"
    and trace_root_eq: "fr' = value trace_root_tree"
    unfolding merkle_root_binds_table_def by blast
  have trace_value_eq:
    "value trace_tree = staged_trace_root ?data"
    using created_tree_same_table_value_eq
        [OF trace_created trace_root_created]
      trace_root_eq fr_eq
    by simp
  from composition_bind obtain composition_root_tree where
    composition_root_created:
      "created_tree composition_table composition_root_tree final_state"
    and composition_root_eq:
      "hd composition_fri_roots' = value composition_root_tree"
    unfolding merkle_root_binds_table_def by blast
  have composition_value_eq:
    "value composition_tree = hd composition_fri_roots"
    using created_tree_same_table_value_eq
        [OF composition_created composition_root_created]
      composition_root_eq comp_roots_eq
    by simp
  have transcript_root_hit:
    "hash_map_new_output_hit
      {staged_trace_root ?data, hd composition_fri_roots}
      ?prefix_state final_state"
    using tree_root_hit trace_value_eq composition_value_eq by simp
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_transcript_root_output_hit_def
      Let_def
    using verify_out bound header transcript_root_hit
    apply simp
    by blast
qed

lemma checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit_bound_from_transcript_roots:
  assumes root_bound:
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_transcript_root_output_hit
      s \<le> R"
  shows
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit s
      \<le> R"
  by (rule order.trans[OF _ root_bound])
    (rule wp_event_mono,
      rule
        checked_staged_security_with_actual_alpha_prefix_tree_root_output_hit_imp_transcript_root_output_hit)

definition
  checked_staged_security_with_actual_alpha_prefix_transcript_root_preverifier_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_transcript_root_preverifier_output_hit
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, _) \<Rightarrow>
          (let packed = fst (fst x);
               prefix_state = snd (fst packed);
               data = snd packed;
               attacker_state = snd (fst x);
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>result final_state trace_table composition_table as
              query_idxs dg composition_fri_roots final rest.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            verifier_header_transcript s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              as dg composition_fri_roots final rest \<and>
            hash_map_new_output_hit
              {staged_trace_root data, hd composition_fri_roots}
              prefix_state s))"

definition
  checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, _) \<Rightarrow>
          (let packed = fst (fst x);
               data = snd packed;
               attacker_state = snd (fst x);
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>result final_state trace_table composition_table as
              query_idxs dg composition_fri_roots final rest.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            verifier_header_transcript s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              as dg composition_fri_roots final rest \<and>
            hash_map_new_output_hit
              {staged_trace_root data, hd composition_fri_roots}
              s final_state))"

lemma checked_staged_security_with_actual_alpha_prefix_transcript_root_output_hit_imp_preverifier_or_verifier_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_transcript_root_output_hit
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_transcript_root_preverifier_output_hit
        out \<or>
      checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit
        out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_transcript_root_output_hit_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state checked_result
      checked_final_state where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state),
          checked_result), checked_final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have support_some:
    "Some (((((prefix, prefix_state), data), attacker_state),
        checked_result), checked_final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
    using support unfolding out_eq .
  from support_some obtain trans_out where trans_out:
      "Some (((prefix, prefix_state), data), attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_with_alpha_prefix_program A)
            adversary_initial_state)"
    unfolding
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  from checked_staged_transcript_with_alpha_prefix_program_support
      [OF wf controlled trans_out]
  have prefix_ext: "prefix_state \<le> attacker_state"
    by blast
  have prefix_s: "prefix_state \<le> ?s"
    by (rule
        alpha_prefix_hash_extends_verifier_state_from_adversary_right
        [OF prefix_ext])
  from hit obtain result final_state trace_table composition_table as
      query_idxs dg composition_fri_roots final rest where
    verify_out:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        as dg composition_fri_roots final rest"
    and root_hit:
      "hash_map_new_output_hit
        {staged_trace_root data, hd composition_fri_roots}
        prefix_state final_state"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_transcript_root_output_hit_def
      Let_def
    by simp blast
  have s_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verify_out])
  from hash_map_new_output_hit_trans_decomp
      [OF prefix_s s_final root_hit]
  show ?thesis
  proof
    assume pre:
      "hash_map_new_output_hit
        {staged_trace_root data, hd composition_fri_roots}
        prefix_state ?s"
    have
      "checked_staged_security_with_actual_alpha_prefix_transcript_root_preverifier_output_hit
        out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_transcript_root_preverifier_output_hit_def
        Let_def
      using verify_out bound header pre
      by simp blast
    then show ?thesis by simp
  next
    assume verifier:
      "hash_map_new_output_hit
        {staged_trace_root data, hd composition_fri_roots}
        ?s final_state"
    have
      "checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit
        out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit_def
        Let_def
      using verify_out bound header verifier
      by simp blast
    then show ?thesis by simp
  qed
qed

lemma verifier_header_transcript_initial_roots_subset_transcript:
  assumes header:
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    and nonempty: "composition_fri_roots \<noteq> []"
  shows "{fr, hd composition_fri_roots} \<subseteq> set (PTranscript s)"
  using header nonempty
  unfolding verifier_header_transcript_def verifier_header_messages_def
  by (cases composition_fri_roots) auto

definition
  checked_staged_security_with_actual_alpha_prefix_verifier_transcript_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_verifier_transcript_output_hit
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, _) \<Rightarrow>
          (let packed = fst (fst x);
               data = snd packed;
               attacker_state = snd (fst x);
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>result final_state trace_table composition_table as
              query_idxs.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            hash_map_new_output_hit (set (PTranscript s)) s final_state))"

lemma checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit_imp_verifier_transcript_output_hit:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_verifier_transcript_output_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit_def
    by simp
next
  case (Some result_pack)
  then obtain x checked_final_state where out_eq:
      "out = Some (x, checked_final_state)"
    by (cases result_pack) simp
  let ?packed = "fst (fst x)"
  let ?data = "snd ?packed"
  let ?attacker_state = "snd (fst x)"
  let ?s =
    "verifier_state_from_adversary ?attacker_state
      (staged_proof_transcript ?data)"
  from hit obtain result final_state trace_table composition_table as
      query_idxs dg composition_fri_roots final rest where
    verify_out:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root ?data)
        (staged_trace_fri_roots ?data)
        (staged_trace_final ?data)
        as dg composition_fri_roots final rest"
    and root_hit:
      "hash_map_new_output_hit
        {staged_trace_root ?data, hd composition_fri_roots}
        ?s final_state"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit_def
      Let_def
    by simp blast
  from bound obtain result' final_state' fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    out_eq':
      "Some (result, final_state) = Some (result', final_state')"
    and header':
      "verifier_header_transcript ?s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and nonempty': "composition_fri_roots' \<noteq> []"
    unfolding accepted_with_bound_tables_def by blast
  have header_eq:
    "fr' = staged_trace_root ?data \<and>
     f_fri_roots' = staged_trace_fri_roots ?data \<and>
     f_final' = staged_trace_final ?data \<and>
     dg' = dg \<and>
     composition_fri_roots' = composition_fri_roots \<and>
     final' = final \<and>
     rest' = rest"
    using verifier_header_transcript_unique[OF header' header]
    by simp
  have nonempty: "composition_fri_roots \<noteq> []"
    using nonempty' header_eq by simp
  have subset:
    "{staged_trace_root ?data, hd composition_fri_roots}
      \<subseteq> set (PTranscript ?s)"
    by (rule verifier_header_transcript_initial_roots_subset_transcript
        [OF header nonempty])
  have transcript_hit:
    "hash_map_new_output_hit (set (PTranscript ?s)) ?s final_state"
    by (rule hash_map_new_output_hit_subset[OF subset root_hit])
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_verifier_transcript_output_hit_def
      Let_def
    using verify_out bound transcript_hit
    by simp blast
qed

lemma checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit_bound_from_verifier_transcript_output:
  assumes transcript_bound:
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_verifier_transcript_output_hit
      s \<le> C"
  shows
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit
      s \<le> C"
  by (rule order.trans[OF _ transcript_bound])
    (rule wp_event_mono,
      rule
        checked_staged_security_with_actual_alpha_prefix_transcript_root_verifier_output_hit_imp_verifier_transcript_output_hit)

lemma checked_staged_security_with_actual_alpha_prefix_tree_output_hit_imp_data_state_alpha_prefix_tree_output_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit: "checked_staged_security_with_actual_alpha_prefix_tree_output_hit
      out"
  shows
    "case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), data), attacker_state),
          checked_result), checked_final_state) \<Rightarrow>
        checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A
          (Some (((data, attacker_state), checked_result),
            checked_final_state))"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding checked_staged_security_with_actual_alpha_prefix_tree_output_hit_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state checked_result
      checked_final_state where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state),
          checked_result), checked_final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from support[unfolded out_eq] obtain trans_out where trans_out:
      "Some (((prefix, prefix_state), data), attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_with_alpha_prefix_program A)
            adversary_initial_state)"
    unfolding
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  from checked_staged_transcript_with_alpha_prefix_program_support
      [OF wf controlled trans_out]
  have prefix_out:
      "Some (prefix, prefix_state) \<in>
        set_dist
          (execute (staged_alpha_prefix_program A)
            adversary_initial_state)"
    and root_eq: "staged_trace_root data = fst prefix"
    and trace_roots_eq:
      "staged_trace_fri_roots data = fst (snd prefix)"
    and trace_bs_eq:
      "staged_trace_fri_challenges data = fst (snd (snd prefix))"
    and trace_final_eq:
      "staged_trace_final data = snd (snd (snd prefix))"
    by blast+
  have actual_body:
    "\<exists>result final_state trace_table composition_table as query_idxs dg
        composition_fri_roots final rest trace_tree composition_tree.
      Some (result, final_state) \<in> set_dist (execute verify_monad ?s) \<and>
      accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs \<and>
      verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        as dg composition_fri_roots final rest \<and>
      created_tree trace_table trace_tree final_state \<and>
      created_tree composition_table composition_tree final_state \<and>
      hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
    using hit
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_tree_output_hit_def
      Let_def
    by simp
  from actual_body obtain result final_state trace_table composition_table as
      query_idxs dg composition_fri_roots final rest trace_tree
      composition_tree where
    verify_out:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        as dg composition_fri_roots final rest"
    and trace_created: "created_tree trace_table trace_tree final_state"
    and composition_created:
      "created_tree composition_table composition_tree final_state"
    and tree_hit:
      "hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
    by blast
  have data_hit:
    "checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A
      (Some (((data, attacker_state), checked_result),
        checked_final_state))"
    by (rule
        checked_staged_security_with_data_state_alpha_prefix_tree_output_hitI
        [OF prefix_out root_eq trace_roots_eq trace_bs_eq trace_final_eq
          verify_out bound header trace_created composition_created
          tree_hit])
  show ?thesis
    unfolding out_eq
    using data_hit by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_tree_output_hit_bound_from_data_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and data_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A)
        adversary_initial_state \<le> T"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_tree_output_hit
      adversary_initial_state \<le> T"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  let ?DataTree =
    "checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A"
  have "wp_event ?M checked_staged_security_with_actual_alpha_prefix_tree_output_hit
      adversary_initial_state \<le>
    wp_event ?M
      (\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (x, t) \<Rightarrow> ?DataTree (Some (?project x, t)))
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit:
      "checked_staged_security_with_actual_alpha_prefix_tree_output_hit out"
    show
      "(case out of None \<Rightarrow> False
        | Some (x, t) \<Rightarrow> ?DataTree (Some (?project x, t)))"
      using
        checked_staged_security_with_actual_alpha_prefix_tree_output_hit_imp_data_state_alpha_prefix_tree_output_hit_on_support
        [OF wf controlled support hit]
      by (cases out) (auto split: prod.splits)
  qed
  also have "... =
    wp_event (?M \<bind> (\<lambda>x. return (?project x))) ?DataTree
      adversary_initial_state"
    unfolding
      checked_staged_security_with_data_state_alpha_prefix_tree_output_hit_def
    by (subst wp_event_bind_return_map)
      (simp split: option.splits prod.splits)
  also have "... =
    wp_event (checked_staged_security_experiment_with_data_state A)
      ?DataTree adversary_initial_state"
    using
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
      [of A]
    by simp
  also have "... \<le> T"
    by (rule data_bound)
  finally show ?thesis .
qed

text \<open>
  Branch-specific tree-output events.

  The actual-prefix tree-output events are existential over verifier
  witnesses for a fixed prefix.  They are useful for deterministic reductions,
  but too coarse for direct verifier-local WP bounds.  The following auxiliary
  events tie the witness to the current verifier branch of the checked
  experiment, so target-budget lemmas can be applied without changing the
  public theorem interface.
\<close>

definition
  checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, final_state) \<Rightarrow>
          (let packed = fst (fst x);
               data = snd packed;
               attacker_state = snd (fst x);
               result = snd x;
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>trace_table composition_table as query_idxs.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            hash_map_new_output_hit (set (PTranscript s)) s final_state))"

definition
  checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, final_state) \<Rightarrow>
          (let packed = fst (fst x);
               data = snd packed;
               attacker_state = snd (fst x);
               result = snd x;
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>trace_table composition_table as query_idxs dg
              composition_fri_roots final rest.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            verifier_header_transcript s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              as dg composition_fri_roots final rest \<and>
            hash_map_new_output_hit
              {staged_trace_root data, hd composition_fri_roots}
              s final_state))"

lemma branch_verifier_transcript_output_hit_imp_verifier_transcript_output_hit:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_verifier_transcript_output_hit
      out"
  using hit
  unfolding
    checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit_def
    checked_staged_security_with_actual_alpha_prefix_verifier_transcript_output_hit_def
    Let_def
  by (cases out) (fastforce split: prod.splits)+

lemma branch_transcript_root_verifier_output_hit_imp_branch_verifier_transcript_output_hit:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit_def
    by simp
next
  case (Some result_pack)
  then obtain x final_state where out_eq: "out = Some (x, final_state)"
    by (cases result_pack) simp
  let ?packed = "fst (fst x)"
  let ?data = "snd ?packed"
  let ?attacker_state = "snd (fst x)"
  let ?result = "snd x"
  let ?s =
    "verifier_state_from_adversary ?attacker_state
      (staged_proof_transcript ?data)"
  from hit obtain trace_table composition_table as query_idxs dg
      composition_fri_roots final rest where
    verify_out:
      "Some (?result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s (Some (?result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root ?data)
        (staged_trace_fri_roots ?data)
        (staged_trace_final ?data)
        as dg composition_fri_roots final rest"
    and root_hit:
      "hash_map_new_output_hit
        {staged_trace_root ?data, hd composition_fri_roots}
        ?s final_state"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit_def
      Let_def
    by simp blast
  from bound obtain result' final_state' fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    out_eq':
      "Some (?result, final_state) = Some (result', final_state')"
    and header':
      "verifier_header_transcript ?s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and nonempty': "composition_fri_roots' \<noteq> []"
    unfolding accepted_with_bound_tables_def by blast
  have header_eq:
    "fr' = staged_trace_root ?data \<and>
     f_fri_roots' = staged_trace_fri_roots ?data \<and>
     f_final' = staged_trace_final ?data \<and>
     dg' = dg \<and>
     composition_fri_roots' = composition_fri_roots \<and>
     final' = final \<and>
     rest' = rest"
    using verifier_header_transcript_unique[OF header' header]
    by simp
  have nonempty: "composition_fri_roots \<noteq> []"
    using nonempty' header_eq by simp
  have subset:
    "{staged_trace_root ?data, hd composition_fri_roots}
      \<subseteq> set (PTranscript ?s)"
    by (rule verifier_header_transcript_initial_roots_subset_transcript
        [OF header nonempty])
  have transcript_hit:
    "hash_map_new_output_hit (set (PTranscript ?s)) ?s final_state"
    by (rule hash_map_new_output_hit_subset[OF subset root_hit])
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit_def
      Let_def
    using verify_out bound transcript_hit
    by simp blast
qed

lemma branch_transcript_root_verifier_output_hit_bound_from_branch_verifier_transcript_output:
  assumes transcript_bound:
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
      s \<le> C"
  shows
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
      s \<le> C"
  by (rule order.trans[OF _ transcript_bound])
    (rule wp_event_mono,
      rule
        branch_transcript_root_verifier_output_hit_imp_branch_verifier_transcript_output_hit)

lemma actual_alpha_prefix_branch_verifier_transcript_output_cont_imp_hash_new_output_hit:
  fixes packed and attacker_state
  defines "s \<equiv>
    verifier_state_from_adversary attacker_state
      (staged_proof_transcript (snd packed))"
  assumes hit:
    "(case out of
        None \<Rightarrow>
          checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
            None
      | Some (result, t) \<Rightarrow>
          checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
            (Some (((packed, attacker_state), result), t)))"
  shows "hash_new_output_hit_event (set (PTranscript s)) s out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit_def
    by simp
next
  case (Some result_state)
  then obtain result t where result_state: "result_state = (result, t)"
    by (cases result_state) simp
  have "hash_map_new_output_hit (set (PTranscript s)) s t"
    using hit Some result_state
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit_def
      s_def Let_def
    by (auto split: prod.splits)
  then show ?thesis
    using Some result_state
    unfolding hash_new_output_hit_event_def by simp
qed

lemma wp_verify_monad_bind_return_actual_alpha_prefix_branch_verifier_transcript_output_hit_bound:
  fixes packed and attacker_state
  defines "s \<equiv>
    verifier_state_from_adversary attacker_state
      (staged_proof_transcript (snd packed))"
  shows
    "wp_event
      (verify_monad \<bind>
        (\<lambda>result. return ((packed, attacker_state), result)))
      checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
      s \<le>
      hash_target_budget_value (set (staged_proof_transcript (snd packed)))
        verifier_hash_query_budget"
proof -
  have mono:
    "wp_event verify_monad
      (\<lambda>out. case out of
        None \<Rightarrow>
          checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
            None
      | Some (x, t) \<Rightarrow>
          checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
            (Some (((packed, attacker_state), x), t))) s \<le>
     wp_event verify_monad
      (hash_new_output_hit_event (set (PTranscript s)) s) s"
  proof (rule wp_event_mono)
    fix out
    assume hit:
      "(case out of
        None \<Rightarrow>
          checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
            None
      | Some (x, t) \<Rightarrow>
          checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
            (Some (((packed, attacker_state), x), t)))"
    show "hash_new_output_hit_event (set (PTranscript s)) s out"
      using hit
      unfolding
        checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit_def
        hash_new_output_hit_event_def s_def Let_def
      by (cases out) (auto split: prod.splits)
  qed
  have target:
    "wp_event verify_monad
      (hash_new_output_hit_event (set (PTranscript s)) s) s \<le>
      hash_target_budget_value (set (PTranscript s))
        verifier_hash_query_budget"
    by (rule wp_verify_monad_hash_new_output_hit_bound)
  have cont_bound:
    "wp_event verify_monad
      (\<lambda>out. case out of
        None \<Rightarrow>
          checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
            None
      | Some (x, t) \<Rightarrow>
          checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
            (Some (((packed, attacker_state), x), t))) s \<le>
      hash_target_budget_value (set (staged_proof_transcript (snd packed)))
        verifier_hash_query_budget"
    using order.trans[OF mono target]
    unfolding s_def by simp
  show ?thesis
    apply (subst wp_event_bind_return_map)
    using cont_bound
    apply (simp split: option.splits prod.splits)
    done
qed

lemma wp_verify_monad_bind_return_actual_alpha_prefix_branch_transcript_root_verifier_output_hit_bound:
  fixes packed and attacker_state
  defines "s \<equiv>
    verifier_state_from_adversary attacker_state
      (staged_proof_transcript (snd packed))"
  shows
    "wp_event
      (verify_monad \<bind>
        (\<lambda>result. return ((packed, attacker_state), result)))
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
      s \<le>
      hash_target_budget_value (set (staged_proof_transcript (snd packed)))
        verifier_hash_query_budget"
proof -
  have transcript_bound:
    "wp_event
      (verify_monad \<bind>
        (\<lambda>result. return ((packed, attacker_state), result)))
      checked_staged_security_with_actual_alpha_prefix_branch_verifier_transcript_output_hit
      s \<le>
      hash_target_budget_value (set (staged_proof_transcript (snd packed)))
        verifier_hash_query_budget"
    unfolding s_def
    by (rule
      wp_verify_monad_bind_return_actual_alpha_prefix_branch_verifier_transcript_output_hit_bound)
  show ?thesis
    by (rule
      branch_transcript_root_verifier_output_hit_bound_from_branch_verifier_transcript_output
      [OF transcript_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit_bound_from_transcript_targets:
  assumes target_bound:
    "\<And>packed attacker_state.
      Some (packed, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_with_alpha_prefix_program A)
            adversary_initial_state) \<Longrightarrow>
      hash_target_budget_value (set (staged_proof_transcript (snd packed)))
        verifier_hash_query_budget \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
      adversary_initial_state \<le> C"
  unfolding checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
proof (rule wp_event_bind_bound_by_cont)
  show
    "\<not>
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
        None"
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit_def
    by simp
next
  fix packed attacker_state
  assume support:
    "Some (packed, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_with_alpha_prefix_program A)
          adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript (snd packed))"
  have cont_eq:
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript (snd packed))) \<bind>
          (\<lambda>_. verify_monad \<bind>
            (\<lambda>result. return ((packed, s), result)))))
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
      attacker_state =
     wp_event
      (verify_monad \<bind>
        (\<lambda>result. return ((packed, attacker_state), result)))
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
      ?s"
    unfolding wp_event_def by (simp add: wpsimps)
  have verifier_bound:
    "wp_event
      (verify_monad \<bind>
        (\<lambda>result. return ((packed, attacker_state), result)))
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
      ?s \<le>
      hash_target_budget_value (set (staged_proof_transcript (snd packed)))
        verifier_hash_query_budget"
    by (rule
      wp_verify_monad_bind_return_actual_alpha_prefix_branch_transcript_root_verifier_output_hit_bound)
  show
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript (snd packed))) \<bind>
          (\<lambda>_. verify_monad \<bind>
            (\<lambda>result. return ((packed, s), result)))))
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
      attacker_state \<le> C"
    unfolding cont_eq
    by (rule order.trans[OF verifier_bound target_bound[OF support]])
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit_bound_from_concrete_transcript_targets:
  assumes target_bound:
    "\<And>packed attacker_state.
      Some (packed, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_with_alpha_prefix_program A)
            adversary_initial_state) \<Longrightarrow>
      concrete_transcript_target_error (staged_proof_transcript (snd packed))
        \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
      adversary_initial_state \<le> C"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit_bound_from_transcript_targets)
  fix packed attacker_state
  assume support:
    "Some (packed, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_with_alpha_prefix_program A)
          adversary_initial_state)"
  show
    "hash_target_budget_value (set (staged_proof_transcript (snd packed)))
      verifier_hash_query_budget \<le> C"
    using target_bound[OF support]
    unfolding concrete_transcript_target_error_def hash_target_budget_value_def
    by (simp add: mult.commute)
qed

end

end
