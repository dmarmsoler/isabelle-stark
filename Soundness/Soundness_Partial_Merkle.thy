(*  Title:      Stark/Soundness_Partial_Merkle.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Partial_Merkle
  imports
    Staged_Security_Experiment
begin

section \<open>Partial Merkle Openings\<close>

text \<open>
  This theory records the authenticated openings that the verifier actually
  observes.  It provides partial table candidates, consistency predicates, and
  reductions from inconsistent authenticated openings to hash-collision events.
\<close>

record 'f authenticated_opening =
  opening_root :: 'f
  opening_length :: nat
  opening_index :: nat
  opening_value :: 'f
  opening_path :: "'f list"

fun merkle_path_bound
  :: "'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "merkle_path_bound rt len idx v [] s \<longleftrightarrow>
    fmlookup (HashMap s) (MerkleLeaf v) = Some rt"
| "merkle_path_bound rt len idx v (sibling # path) s \<longleftrightarrow>
    (if idx < len div 2 then
      (\<exists>child.
        merkle_path_bound child (len div 2) idx v path s \<and>
        fmlookup (HashMap s) (MerkleNode child sibling) = Some rt)
    else
      (\<exists>child.
        merkle_path_bound child (len div 2) (idx - len div 2)
          v path s \<and>
        fmlookup (HashMap s) (MerkleNode sibling child) = Some rt))"

context soundness
begin

definition authenticated_opening_in
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f authenticated_opening \<Rightarrow> bool"
where
  "authenticated_opening_in s opening \<longleftrightarrow>
    opening_index opening < opening_length opening \<and>
    length (opening_path opening) =
      floor_log (opening_length opening) \<and>
    merkle_path_bound
      (opening_root opening)
      (opening_length opening)
      (opening_index opening)
      (opening_value opening)
      (opening_path opening)
      s"

definition partial_authenticated_table
  :: "'f \<Rightarrow> nat \<Rightarrow> 'f authenticated_opening list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "partial_authenticated_table rt len openings s \<longleftrightarrow>
    (\<forall>opening \<in> set openings.
      opening_root opening = rt \<and>
      opening_length opening = len \<and>
      authenticated_opening_in s opening)"

lemma merkle_path_bound_mono:
  assumes bound: "merkle_path_bound rt len idx v path s"
    and ext: "s \<le> t"
  shows "merkle_path_bound rt len idx v path t"
  using bound
proof (induction path arbitrary: rt len idx)
  case Nil
  then show ?case
    using hash_extension_lookup[OF _ ext] by simp
next
  case (Cons sibling path)
  show ?case
  proof (cases "idx < len div 2")
    case True
    then obtain child where
      child:
        "merkle_path_bound child (len div 2) idx v path s"
      and lookup:
        "fmlookup (HashMap s) (MerkleNode child sibling) = Some rt"
      using Cons.prems by auto
    have child_t:
      "merkle_path_bound child (len div 2) idx v path t"
      by (rule Cons.IH[OF child])
    have lookup_t:
      "fmlookup (HashMap t) (MerkleNode child sibling) = Some rt"
      by (rule hash_extension_lookup[OF lookup ext])
    show ?thesis
      using True child_t lookup_t
      by (auto intro!: exI[of _ child])
  next
    case False
    then obtain child where
      child:
        "merkle_path_bound child (len div 2) (idx - len div 2)
          v path s"
      and lookup:
        "fmlookup (HashMap s) (MerkleNode sibling child) = Some rt"
      using Cons.prems by auto
    have child_t:
      "merkle_path_bound child (len div 2) (idx - len div 2)
        v path t"
      by (rule Cons.IH[OF child])
    have lookup_t:
      "fmlookup (HashMap t) (MerkleNode sibling child) = Some rt"
      by (rule hash_extension_lookup[OF lookup ext])
    show ?thesis
      using False child_t lookup_t
      by (auto intro!: exI[of _ child])
  qed
qed

lemma authenticated_opening_in_mono:
  assumes opn_auth: "authenticated_opening_in s opn"
    and ext: "s \<le> t"
  shows "authenticated_opening_in t opn"
  using opn_auth merkle_path_bound_mono[OF _ ext]
  unfolding authenticated_opening_in_def by blast

lemma partial_authenticated_table_mono:
  assumes table: "partial_authenticated_table rt len openings s"
    and ext: "s \<le> t"
  shows "partial_authenticated_table rt len openings t"
  using table authenticated_opening_in_mono[OF _ ext]
  unfolding partial_authenticated_table_def by blast

lemma merkle_path_bound_root_lookup:
  assumes "merkle_path_bound rt len idx v path s"
  shows "\<exists>input. fmlookup (HashMap s) input = Some rt"
  using assms
proof (induction path arbitrary: rt len idx)
  case Nil
  then show ?case
    by (intro exI[of _ "MerkleLeaf v"]) simp
next
  case (Cons sibling path)
  then show ?case
    by (cases "idx < len div 2") auto
qed

lemma authenticated_opening_root_lookup:
  assumes "authenticated_opening_in s opening"
  shows "\<exists>input. fmlookup (HashMap s) input = Some (opening_root opening)"
  using assms
  unfolding authenticated_opening_in_def
  by (blast intro: merkle_path_bound_root_lookup)

lemma authenticated_opening_root_late_output_preexisting_or_new_hit:
  assumes ext: "s \<le> t"
    and auth: "authenticated_opening_in t opening"
  shows
    "(\<exists>input. fmlookup (HashMap s) input = Some (opening_root opening)) \<or>
     hash_map_new_output_hit {opening_root opening} s t"
proof -
  from authenticated_opening_root_lookup[OF auth]
  obtain input where lookup_t:
    "fmlookup (HashMap t) input = Some (opening_root opening)"
    by blast
  show ?thesis
  proof (cases "fmlookup (HashMap s) input")
    case None
    then have "hash_map_new_output_hit {opening_root opening} s t"
      unfolding hash_map_new_output_hit_def
      using lookup_t by blast
    then show ?thesis by simp
  next
    case (Some old)
    have lookup_t_old: "fmlookup (HashMap t) input = Some old"
      by (rule hash_extension_lookup[OF Some ext])
    then have "old = opening_root opening"
      using lookup_t by simp
    then show ?thesis
      using Some by blast
  qed
qed

lemma partial_authenticated_table_root_late_output_preexisting_or_new_hit:
  assumes ext: "s \<le> t"
    and table: "partial_authenticated_table rt len openings t"
    and opn_in: "opening \<in> set openings"
  shows
    "(\<exists>input. fmlookup (HashMap s) input = Some rt) \<or>
     hash_map_new_output_hit {rt} s t"
proof -
  have auth: "authenticated_opening_in t opening"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have root_eq: "opening_root opening = rt"
    using table opn_in unfolding partial_authenticated_table_def by blast
  show ?thesis
    using authenticated_opening_root_late_output_preexisting_or_new_hit
      [OF ext auth]
    unfolding root_eq .
qed

lemma merkle_path_bound_root_in_map:
  assumes "merkle_path_bound rt len idx v path s"
  shows "merkle_path_root_in_map s len idx v path = Some rt"
  using assms
proof (induction path arbitrary: rt len idx)
  case Nil
  then show ?case by simp
next
  case (Cons sibling path)
  then show ?case
    by (cases "idx < len div 2") auto
qed

lemma merkle_path_root_in_map_some_imp_bound:
  assumes "merkle_path_root_in_map s len idx v path = Some rt"
  shows "merkle_path_bound rt len idx v path s"
  using assms
proof (induction path arbitrary: rt len idx)
  case Nil
  then show ?case by simp
next
  case (Cons sibling path)
  show ?case
  proof (cases "idx < len div 2")
    case True
    from Cons.prems obtain child where
      child_root:
        "merkle_path_root_in_map s (len div 2) idx v path =
          Some child"
      and lookup:
        "fmlookup (HashMap s) (MerkleNode child sibling) = Some rt"
      using True by (auto split: option.splits)
    have child_bound:
      "merkle_path_bound child (len div 2) idx v path s"
      by (rule Cons.IH[OF child_root])
    show ?thesis
      using True child_bound lookup by auto
  next
    case False
    from Cons.prems obtain child where
      child_root:
        "merkle_path_root_in_map s (len div 2) (idx - len div 2)
          v path = Some child"
      and lookup:
        "fmlookup (HashMap s) (MerkleNode sibling child) = Some rt"
      using False by (auto split: option.splits)
    have child_bound:
      "merkle_path_bound child (len div 2) (idx - len div 2) v path s"
      by (rule Cons.IH[OF child_root])
    show ?thesis
      using False child_bound lookup by auto
  qed
qed

fun merkle_path_target_roots
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f set"
where
  "merkle_path_target_roots t rt len idx v [] = {rt}"
| "merkle_path_target_roots t rt len idx v (sibling # path) =
    {rt} \<union>
      (if idx < len div 2 then
        (case merkle_path_root_in_map t (len div 2) idx v path of
          None \<Rightarrow> {}
        | Some child \<Rightarrow>
            merkle_path_target_roots t child (len div 2) idx v path)
       else
        (case merkle_path_root_in_map t (len div 2) (idx - len div 2)
            v path of
          None \<Rightarrow> {}
        | Some child \<Rightarrow>
            merkle_path_target_roots t child (len div 2)
              (idx - len div 2) v path))"

lemma finite_merkle_path_target_roots[simp]:
  "finite (merkle_path_target_roots t rt len idx v path)"
  by (induction path arbitrary: rt len idx)
    (auto split: option.splits if_splits)

lemma card_merkle_path_target_roots_le:
  "card (merkle_path_target_roots t rt len idx v path) \<le> Suc (length path)"
proof (induction path arbitrary: rt len idx)
  case Nil
  then show ?case by simp
next
  case (Cons sibling path)
  show ?case
  proof (cases "idx < len div 2")
    case True
    then show ?thesis
    proof (cases "merkle_path_root_in_map t (len div 2) idx v path")
      case None
      then show ?thesis
        using True by simp
    next
      case (Some child)
      have finite_child:
        "finite (merkle_path_target_roots t child (len div 2) idx v path)"
        by simp
      have card_le:
        "card ({rt} \<union>
          merkle_path_target_roots t child (len div 2) idx v path) \<le>
         Suc (card
          (merkle_path_target_roots t child (len div 2) idx v path))"
        using finite_child by (simp add: card_insert_if)
      also have "... \<le> Suc (Suc (length path))"
        using Cons.IH[of child "len div 2" idx] by simp
      finally show ?thesis
        using True Some by simp
    qed
  next
    case False
    then show ?thesis
    proof (cases
        "merkle_path_root_in_map t (len div 2) (idx - len div 2) v path")
      case None
      then show ?thesis
        using False by simp
    next
      case (Some child)
      have finite_child:
        "finite (merkle_path_target_roots t child (len div 2)
          (idx - len div 2) v path)"
        by simp
      have card_le:
        "card ({rt} \<union>
          merkle_path_target_roots t child (len div 2)
            (idx - len div 2) v path) \<le>
         Suc (card
          (merkle_path_target_roots t child (len div 2)
            (idx - len div 2) v path))"
        using finite_child by (simp add: card_insert_if)
      also have "... \<le> Suc (Suc (length path))"
        using Cons.IH[of child "len div 2" "idx - len div 2"] by simp
      finally show ?thesis
        using False Some by simp
    qed
  qed
qed

lemma merkle_path_bound_pullback_or_new_output_hit:
  assumes ext: "s \<le> t"
    and bound: "merkle_path_bound rt len idx v path t"
  shows
    "merkle_path_bound rt len idx v path s \<or>
     hash_map_new_output_hit
      (merkle_path_target_roots t rt len idx v path) s t"
  using bound
proof (induction path arbitrary: rt len idx)
  case Nil
  have lookup_t: "fmlookup (HashMap t) (MerkleLeaf v) = Some rt"
    using Nil.prems by simp
  show ?case
  proof (cases "fmlookup (HashMap s) (MerkleLeaf v)")
    case None
    then have
      "hash_map_new_output_hit
        (merkle_path_target_roots t rt len idx v []) s t"
      unfolding hash_map_new_output_hit_def
      using lookup_t by simp blast
    then show ?thesis by simp
  next
    case (Some old)
    have lookup_t_old: "fmlookup (HashMap t) (MerkleLeaf v) = Some old"
      by (rule hash_extension_lookup[OF Some ext])
    then have "old = rt"
      using lookup_t by simp
    then have "merkle_path_bound rt len idx v [] s"
      using Some by simp
    then show ?thesis by simp
  qed
next
  case (Cons sibling path)
  show ?case
  proof (cases "idx < len div 2")
    case True
    from Cons.prems obtain child where child_bound:
        "merkle_path_bound child (len div 2) idx v path t"
      and lookup_t:
        "fmlookup (HashMap t) (MerkleNode child sibling) = Some rt"
      using True by auto
    have child_root:
      "merkle_path_root_in_map t (len div 2) idx v path = Some child"
      by (rule merkle_path_bound_root_in_map[OF child_bound])
    show ?thesis
    proof (cases "fmlookup (HashMap s) (MerkleNode child sibling)")
      case None
      then have root_hit:
        "hash_map_new_output_hit {rt} s t"
        unfolding hash_map_new_output_hit_def
        using lookup_t by blast
      have subset:
        "{rt} \<subseteq>
          merkle_path_target_roots t rt len idx v (sibling # path)"
        using True child_root by simp
      have
        "hash_map_new_output_hit
          (merkle_path_target_roots t rt len idx v (sibling # path)) s t"
        by (rule hash_map_new_output_hit_subset[OF subset root_hit])
      then show ?thesis by simp
    next
      case (Some old)
      have lookup_t_old:
        "fmlookup (HashMap t) (MerkleNode child sibling) = Some old"
        by (rule hash_extension_lookup[OF Some ext])
      then have old_eq: "old = rt"
        using lookup_t by simp
      have lookup_s:
        "fmlookup (HashMap s) (MerkleNode child sibling) = Some rt"
        using Some old_eq by simp
      from Cons.IH[OF child_bound]
      have child_pullback:
        "merkle_path_bound child (len div 2) idx v path s \<or>
         hash_map_new_output_hit
          (merkle_path_target_roots t child (len div 2) idx v path) s t"
        .
      then show ?thesis
      proof
        assume child_s:
          "merkle_path_bound child (len div 2) idx v path s"
        then have "merkle_path_bound rt len idx v (sibling # path) s"
          using True lookup_s by auto
        then show ?thesis by simp
      next
        assume child_hit:
          "hash_map_new_output_hit
            (merkle_path_target_roots t child (len div 2) idx v path) s t"
        have subset:
          "merkle_path_target_roots t child (len div 2) idx v path
            \<subseteq>
           merkle_path_target_roots t rt len idx v (sibling # path)"
          using True child_root by auto
        have
          "hash_map_new_output_hit
            (merkle_path_target_roots t rt len idx v (sibling # path)) s t"
          by (rule hash_map_new_output_hit_subset[OF subset child_hit])
        then show ?thesis by simp
      qed
    qed
  next
    case False
    from Cons.prems obtain child where child_bound:
        "merkle_path_bound child (len div 2) (idx - len div 2) v path t"
      and lookup_t:
        "fmlookup (HashMap t) (MerkleNode sibling child) = Some rt"
      using False by auto
    have child_root:
      "merkle_path_root_in_map t (len div 2) (idx - len div 2) v path =
        Some child"
      by (rule merkle_path_bound_root_in_map[OF child_bound])
    show ?thesis
    proof (cases "fmlookup (HashMap s) (MerkleNode sibling child)")
      case None
      then have root_hit:
        "hash_map_new_output_hit {rt} s t"
        unfolding hash_map_new_output_hit_def
        using lookup_t by blast
      have subset:
        "{rt} \<subseteq>
          merkle_path_target_roots t rt len idx v (sibling # path)"
        using False child_root by simp
      have
        "hash_map_new_output_hit
          (merkle_path_target_roots t rt len idx v (sibling # path)) s t"
        by (rule hash_map_new_output_hit_subset[OF subset root_hit])
      then show ?thesis by simp
    next
      case (Some old)
      have lookup_t_old:
        "fmlookup (HashMap t) (MerkleNode sibling child) = Some old"
        by (rule hash_extension_lookup[OF Some ext])
      then have old_eq: "old = rt"
        using lookup_t by simp
      have lookup_s:
        "fmlookup (HashMap s) (MerkleNode sibling child) = Some rt"
        using Some old_eq by simp
      from Cons.IH[OF child_bound]
      have child_pullback:
        "merkle_path_bound child (len div 2) (idx - len div 2) v path s \<or>
         hash_map_new_output_hit
          (merkle_path_target_roots t child (len div 2)
            (idx - len div 2) v path) s t"
        .
      then show ?thesis
      proof
        assume child_s:
          "merkle_path_bound child (len div 2) (idx - len div 2) v path s"
        then have "merkle_path_bound rt len idx v (sibling # path) s"
          using False lookup_s by auto
        then show ?thesis by simp
      next
        assume child_hit:
          "hash_map_new_output_hit
            (merkle_path_target_roots t child (len div 2)
              (idx - len div 2) v path) s t"
        have subset:
          "merkle_path_target_roots t child (len div 2)
              (idx - len div 2) v path
            \<subseteq>
           merkle_path_target_roots t rt len idx v (sibling # path)"
          using False child_root by auto
        have
          "hash_map_new_output_hit
            (merkle_path_target_roots t rt len idx v (sibling # path)) s t"
          by (rule hash_map_new_output_hit_subset[OF subset child_hit])
        then show ?thesis by simp
      qed
    qed
  qed
qed

lemma authenticated_opening_pullback_or_new_output_hit:
  assumes ext: "s \<le> t"
    and auth: "authenticated_opening_in t opening"
  shows
    "authenticated_opening_in s opening \<or>
     hash_map_new_output_hit
      (merkle_path_target_roots t
        (opening_root opening)
        (opening_length opening)
        (opening_index opening)
        (opening_value opening)
        (opening_path opening)) s t"
proof -
  have idx_bound: "opening_index opening < opening_length opening"
    using auth unfolding authenticated_opening_in_def by simp
  have path_len:
    "length (opening_path opening) =
      floor_log (opening_length opening)"
    using auth unfolding authenticated_opening_in_def by simp
  have bound_t:
    "merkle_path_bound
      (opening_root opening)
      (opening_length opening)
      (opening_index opening)
      (opening_value opening)
      (opening_path opening) t"
    using auth unfolding authenticated_opening_in_def by simp
  from merkle_path_bound_pullback_or_new_output_hit[OF ext bound_t]
  show ?thesis
  proof
    assume bound_s:
      "merkle_path_bound
        (opening_root opening)
        (opening_length opening)
        (opening_index opening)
        (opening_value opening)
        (opening_path opening) s"
    have "authenticated_opening_in s opening"
      unfolding authenticated_opening_in_def
      using idx_bound path_len bound_s by simp
    then show ?thesis by simp
  next
    assume
      "hash_map_new_output_hit
        (merkle_path_target_roots t
          (opening_root opening)
          (opening_length opening)
          (opening_index opening)
          (opening_value opening)
          (opening_path opening)) s t"
    then show ?thesis by simp
  qed
qed

lemma partial_authenticated_table_opening_pullback_or_new_output_hit:
  assumes ext: "s \<le> t"
    and table: "partial_authenticated_table rt len openings t"
    and opn_in: "opening \<in> set openings"
  shows
    "authenticated_opening_in s opening \<or>
     hash_map_new_output_hit
      (merkle_path_target_roots t rt len
        (opening_index opening)
        (opening_value opening)
        (opening_path opening)) s t"
proof -
  have auth: "authenticated_opening_in t opening"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have root_eq: "opening_root opening = rt"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have len_eq: "opening_length opening = len"
    using table opn_in unfolding partial_authenticated_table_def by blast
  show ?thesis
    using authenticated_opening_pullback_or_new_output_hit[OF ext auth]
    unfolding root_eq len_eq .
qed

lemma partial_authenticated_table_pullback_or_new_output_hit:
  assumes ext: "s \<le> t"
    and table: "partial_authenticated_table rt len openings t"
  shows
    "partial_authenticated_table rt len openings s \<or>
     (\<exists>opening \<in> set openings.
      hash_map_new_output_hit
        (merkle_path_target_roots t rt len
          (opening_index opening)
          (opening_value opening)
          (opening_path opening)) s t)"
proof (cases
    "\<exists>opening \<in> set openings.
      hash_map_new_output_hit
        (merkle_path_target_roots t rt len
          (opening_index opening)
          (opening_value opening)
          (opening_path opening)) s t")
  case True
  then show ?thesis by simp
next
  case False
  have table_s:
    "partial_authenticated_table rt len openings s"
    unfolding partial_authenticated_table_def
  proof
    fix opn
    assume opn_in: "opn \<in> set openings"
    have root_eq: "opening_root opn = rt"
      using table opn_in unfolding partial_authenticated_table_def by blast
    have len_eq: "opening_length opn = len"
      using table opn_in unfolding partial_authenticated_table_def by blast
    have auth_s: "authenticated_opening_in s opn"
    proof -
      have pullback:
        "authenticated_opening_in s opn \<or>
         hash_map_new_output_hit
          (merkle_path_target_roots t rt len
            (opening_index opn)
            (opening_value opn)
            (opening_path opn)) s t"
        by (rule partial_authenticated_table_opening_pullback_or_new_output_hit
            [OF ext table opn_in])
      then show ?thesis
        using False opn_in by blast
    qed
    show
      "opening_root opn = rt \<and>
       opening_length opn = len \<and>
       authenticated_opening_in s opn"
      using root_eq len_eq auth_s by simp
  qed
  then show ?thesis by simp
qed

lemma protocol_created_tree_get_authentication_path_len:
  assumes created: "protocol_created_tree xs tree s"
    and pos: "0 < lgth"
    and le: "lgth \<le> length xs"
  shows "length (get_authentication_path lgth idx tree) = floor_log lgth"
  using assms
proof (induction xs arbitrary: tree lgth idx rule: measure_induct_rule[of length])
  case (less xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      using less.prems by simp
  next
    case (Cons x ys)
    show ?thesis
    proof (cases ys)
      case Nil
      then have lgth_eq: "lgth = 1"
        using less.prems Cons by simp
      obtain h where tree_eq: "tree = \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>"
        using protocol_created_tree_singletonD[OF less.prems(1)[unfolded Cons Nil]]
        by blast
      show ?thesis
        unfolding tree_eq lgth_eq by (simp add: floor_log_Suc_zero)
    next
      case (Cons y zs)
      let ?mid = "length xs div 2"
      have xs_eq: "xs = x # y # zs"
        using \<open>xs = x # ys\<close> \<open>ys = y # zs\<close> by simp
      have len_ge: "2 \<le> length xs"
        unfolding xs_eq by simp
      obtain l h r i where i_eq: "i = ?mid"
        and tree_eq: "tree = \<langle>l, h, r\<rangle>"
        and left_i: "protocol_created_tree (take i xs) l s"
        and right_i: "protocol_created_tree (drop i xs) r s"
        and root_lookup:
          "fmlookup (HashMap s) (MerkleNode (value l) (value r)) =
            Some h"
        by (rule protocol_created_tree_internalD[OF less.prems(1) len_ge])
      have left: "protocol_created_tree (take ?mid xs) l s"
        using left_i i_eq by simp
      have right: "protocol_created_tree (drop ?mid xs) r s"
        using right_i i_eq by simp
      show ?thesis
      proof (cases "lgth = 1")
        case True
        then show ?thesis
          unfolding tree_eq by (simp add: floor_log_Suc_zero)
      next
        case False
        note lgth_ne_one = False
        have lgth_ge: "2 \<le> lgth"
          using lgth_ne_one less.prems by simp
        have half_pos: "0 < lgth div 2"
          using lgth_ge by simp
        have take_less: "length (take ?mid xs) < length xs"
          using len_ge by simp
        have drop_less: "length (drop ?mid xs) < length xs"
          using len_ge by simp
        have half_le_take: "lgth div 2 \<le> length (take ?mid xs)"
          using less.prems(3) by simp
        have half_le_drop: "lgth div 2 \<le> length (drop ?mid xs)"
          using less.prems(3) len_ge by simp
        have left_len:
          "length (get_authentication_path (lgth div 2) idx l) =
            floor_log (lgth div 2)"
          by (rule less.IH[OF take_less left half_pos half_le_take])
        have right_len:
          "length (get_authentication_path (lgth div 2)
              (idx - lgth div 2) r) =
            floor_log (lgth div 2)"
          by (rule less.IH[OF drop_less right half_pos half_le_drop])
        have floor_eq: "floor_log lgth = Suc (floor_log (lgth div 2))"
          using floor_log_rec[OF lgth_ge] .
        show ?thesis
        proof (cases "idx < lgth div 2")
          case True
          then have "length (get_authentication_path lgth idx tree) =
              Suc (floor_log (lgth div 2))"
            using lgth_ne_one left_len unfolding tree_eq by simp
          then show ?thesis
            by (simp only: floor_eq)
        next
          case False
          then have "length (get_authentication_path lgth idx tree) =
              Suc (floor_log (lgth div 2))"
            using lgth_ne_one right_len unfolding tree_eq by simp
          then show ?thesis
            by (simp only: floor_eq)
        qed
      qed
    qed
  qed
qed

lemma created_tree_get_authentication_path_len:
  assumes created: "created_tree xs tree s"
    and xs_nonempty: "xs \<noteq> []"
  shows "length (get_authentication_path (length xs) idx tree) =
    floor_log (length xs)"
  by (rule protocol_created_tree_get_authentication_path_len
      [OF created[unfolded created_tree_def]])
    (use xs_nonempty in simp_all)

lemma merkle_root_binds_table_authenticated_openings:
  assumes bind: "merkle_root_binds_table rt table final_state"
    and len_table: "length table = scale * clength"
    and idxs_bound: "\<And>idx. idx \<in> set idxs \<Longrightarrow> idx < scale * clength"
  obtains openings where
    "map opening_index openings = idxs"
    "map opening_value openings = map ((!) table) idxs"
    "partial_authenticated_table rt (scale * clength) openings final_state"
proof -
  obtain tree where created:
      "created_tree table tree final_state"
    and rt_eq: "rt = value tree"
    using bind unfolding merkle_root_binds_table_def by blast
  let ?opening = "\<lambda>idx.
    \<lparr>opening_root = rt,
      opening_length = scale * clength,
      opening_index = idx,
      opening_value = table ! idx,
      opening_path = get_authentication_path (length table) idx tree\<rparr>"
  let ?openings = "map ?opening idxs"
  have auth_all:
    "\<forall>opn \<in> set ?openings.
      opening_root opn = rt \<and>
      opening_length opn = scale * clength \<and>
      authenticated_opening_in final_state opn"
  proof
    fix opn
    assume opn_in: "opn \<in> set ?openings"
    then obtain idx where idx_in: "idx \<in> set idxs"
      and opn_eq: "opn = ?opening idx"
      by auto
    have idx_bound_len: "idx < length table"
      using idxs_bound[OF idx_in] len_table by simp
    have idx_bound_domain: "idx < scale * clength"
      by (rule idxs_bound[OF idx_in])
    obtain n where len_pow: "length table = 2 ^ n"
      using len_table eval_domain_length_power
      by (metis mult.commute)
    have root_in_map:
      "merkle_path_root_in_map final_state (length table) idx
        (table ! idx) (get_authentication_path (length table) idx tree) =
        Some rt"
      using protocol_created_tree_path_root_in_map
          [OF created[unfolded created_tree_def] len_pow idx_bound_len]
      unfolding rt_eq .
    have path_bound:
      "merkle_path_bound rt (length table) idx (table ! idx)
        (get_authentication_path (length table) idx tree) final_state"
      by (rule merkle_path_root_in_map_some_imp_bound[OF root_in_map])
    have path_len:
      "length (get_authentication_path (length table) idx tree) =
        floor_log (scale * clength)"
    proof -
      have table_nonempty: "table \<noteq> []"
        using idx_bound_len by auto
      show ?thesis
        using created_tree_get_authentication_path_len[OF created table_nonempty,
            of idx] len_table
        by simp
    qed
    have auth: "authenticated_opening_in final_state opn"
      unfolding authenticated_opening_in_def opn_eq
      using idx_bound_domain path_len path_bound len_table by simp
    show "opening_root opn = rt \<and>
      opening_length opn = scale * clength \<and>
      authenticated_opening_in final_state opn"
      using auth unfolding opn_eq by simp
  qed
  have partial_table:
    "partial_authenticated_table rt (scale * clength) ?openings
      final_state"
    using auth_all unfolding partial_authenticated_table_def by blast
  have indices: "map opening_index ?openings = idxs"
    by (induction idxs) simp_all
  have value_map: "map opening_value ?openings = map ((!) table) idxs"
    by (induction idxs) simp_all
  show ?thesis
    by (rule that[OF indices value_map partial_table])
qed

lemma authenticated_opening_root_in_map:
  assumes "authenticated_opening_in s opening"
  shows
    "merkle_path_root_in_map s
      (opening_length opening)
      (opening_index opening)
      (opening_value opening)
      (opening_path opening) =
      Some (opening_root opening)"
proof -
  have bound:
    "merkle_path_bound
      (opening_root opening)
      (opening_length opening)
      (opening_index opening)
      (opening_value opening)
      (opening_path opening) s"
    using assms unfolding authenticated_opening_in_def by simp
  show ?thesis
    by (rule merkle_path_bound_root_in_map[OF bound])
qed

lemma check_authentication_path_outcome_bound:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (rt, t) \<in>
      set_dist (execute (check_authentication_path len idx v path) s)"
  shows "merkle_path_bound rt len idx v path t"
  using outcome
proof (induction path arbitrary: rt len idx s t)
  case Nil
  have hash_out:
    "Some (rt, t) \<in>
      set_dist
        (execute
          (hash (MerkleLeaf v) ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) s)"
    using Nil.prems
    unfolding check_authentication_path_def
      protocol_check_authentication_path_def
    by simp
  show ?case using hash_outcome(2)[OF hash_out] by simp
next
  case (Cons sibling path)
  show ?case
  proof (cases "idx < len div 2")
    case True
    from Cons.prems obtain child u where
      rec_out:
        "Some (child, u) \<in>
          set_dist
            (execute
              (check_authentication_path (len div 2) idx v path) s)"
      and hash_out:
        "Some (rt, t) \<in>
          set_dist
            (execute
              (hash (MerkleNode child sibling) ::
                ('f, ('f, 'a) protocol_channel_scheme) state_monad) u)"
      unfolding check_authentication_path_def
        protocol_check_authentication_path_def
      using True
      by (auto simp: protocol_merkle.check_authentication_path.simps
          elim!: set_dist_bindE)
    have child_u:
      "merkle_path_bound child (len div 2) idx v path u"
      by (rule Cons.IH[OF rec_out])
    have ext: "u \<le> t"
      by (rule hash_outcome(1)[OF hash_out])
    have child_t:
      "merkle_path_bound child (len div 2) idx v path t"
      by (rule merkle_path_bound_mono[OF child_u ext])
    have lookup:
      "fmlookup (HashMap t) (MerkleNode child sibling) = Some rt"
      by (rule hash_outcome(2)[OF hash_out])
    show ?thesis
      using True child_t lookup
      by (auto intro!: exI[of _ child])
  next
    case False
    from Cons.prems obtain child u where
      rec_out:
        "Some (child, u) \<in>
          set_dist
            (execute
              (check_authentication_path
                (len div 2) (idx - len div 2) v path) s)"
      and hash_out:
        "Some (rt, t) \<in>
          set_dist
            (execute
              (hash (MerkleNode sibling child) ::
                ('f, ('f, 'a) protocol_channel_scheme) state_monad) u)"
      unfolding check_authentication_path_def
        protocol_check_authentication_path_def
      using False
      by (auto simp: protocol_merkle.check_authentication_path.simps
          elim!: set_dist_bindE)
    have child_u:
      "merkle_path_bound child (len div 2) (idx - len div 2)
        v path u"
      by (rule Cons.IH[OF rec_out])
    have ext: "u \<le> t"
      by (rule hash_outcome(1)[OF hash_out])
    have child_t:
      "merkle_path_bound child (len div 2) (idx - len div 2)
        v path t"
      by (rule merkle_path_bound_mono[OF child_u ext])
    have lookup:
      "fmlookup (HashMap t) (MerkleNode sibling child) = Some rt"
      by (rule hash_outcome(2)[OF hash_out])
    show ?thesis
      using False child_t lookup
      by (auto intro!: exI[of _ child])
  qed
qed

lemma query_decommitment_step_authenticated_opening:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes idx_bound: "idx < scale * clength"
    and outcome:
      "Some (qh, t) \<in>
        set_dist (execute (query_decommitment_step rt idx) s)"
  obtains path opn where
    "opn =
      \<lparr>opening_root = rt,
       opening_length = scale * clength,
       opening_index = idx,
       opening_value = qh,
       opening_path = path\<rparr>"
    "authenticated_opening_in t opn"
proof -
  let ?len = "scale * clength"
  from outcome obtain s1 path s2 ap s3 s4 where
    read_qh:
      "Some (qh, s1) \<in> set_dist (execute read s)"
    and read_path:
      "Some (path, s2) \<in>
        set_dist (execute (ntimes read (floor_log ?len)) s1)"
    and check:
      "Some (ap, s3) \<in>
        set_dist
          (execute (check_authentication_path ?len idx qh path) s2)"
    and assert_ap:
      "Some ((), s4) \<in> set_dist (execute (assert (ap = rt)) s3)"
    and ret:
      "Some (qh, t) \<in> set_dist (execute (return qh) s4)"
    unfolding query_decommitment_step_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  have path_length: "length path = floor_log ?len"
    using ntimes_read_any_outcome[OF read_path] by simp
  have ap_eq: "ap = rt"
    using assert_ap unfolding assert_def
    by (cases "ap = rt") (auto simp: throw_no_outcome)
  have s4: "s4 = s3"
    using assert_ap ap_eq unfolding assert_def by simp
  have t: "t = s3"
    using ret unfolding s4 by simp
  have path_bound:
    "merkle_path_bound rt ?len idx qh path t"
  proof -
    have "merkle_path_bound ap ?len idx qh path s3"
      by (rule check_authentication_path_outcome_bound[OF check])
    then show ?thesis unfolding ap_eq t .
  qed
  let ?opn =
    "\<lparr>opening_root = rt,
      opening_length = ?len,
      opening_index = idx,
      opening_value = qh,
      opening_path = path\<rparr>"
  have authenticated: "authenticated_opening_in t ?opn"
    unfolding authenticated_opening_in_def
    using idx_bound path_length path_bound by simp
  show ?thesis
    by (rule that[of ?opn path]) (simp_all add: authenticated)
qed

lemma mmap_query_decommitment_steps_authenticated_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes idxs_bound: "\<And>idx. idx \<in> set idxs \<Longrightarrow> idx < scale * clength"
    and outcome:
      "Some (leaves, t) \<in>
        set_dist (execute (mmap (map (query_decommitment_step rt) idxs)) s)"
  shows
    "\<exists>openings.
      length openings = length idxs \<and>
      map opening_value openings = leaves \<and>
      map opening_index openings = idxs \<and>
      partial_authenticated_table rt (scale * clength) openings t"
  using outcome idxs_bound
proof (induction idxs arbitrary: s leaves t)
  case Nil
  then have "leaves = []" and "t = s"
    by simp_all
  moreover have
    "partial_authenticated_table rt (scale * clength) [] t"
    unfolding partial_authenticated_table_def by simp
  ultimately show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Cons idx idxs)
  from Cons.prems obtain leaf leaves' s1 where
    head:
      "Some (leaf, s1) \<in>
        set_dist (execute (query_decommitment_step rt idx) s)"
    and tail:
      "Some (leaves', t) \<in>
        set_dist (execute (mmap (map (query_decommitment_step rt) idxs)) s1)"
    and leaves_eq: "leaves = leaf # leaves'"
    by (auto elim!: set_dist_bindE)
  have idx_bound: "idx < scale * clength"
    by (rule Cons.prems(2)) simp
  from query_decommitment_step_authenticated_opening[OF idx_bound head]
  obtain path opn where
    opn_eq:
      "opn =
        \<lparr>opening_root = rt,
         opening_length = scale * clength,
         opening_index = idx,
         opening_value = leaf,
         opening_path = path\<rparr>"
    and opn_auth_s1: "authenticated_opening_in s1 opn"
    by blast
  have tail_bound:
    "\<And>idx. idx \<in> set idxs \<Longrightarrow> idx < scale * clength"
    by (rule Cons.prems(2)) simp
  from Cons.IH[OF tail tail_bound] obtain openings where
    len_openings: "length openings = length idxs"
    and values_openings: "map opening_value openings = leaves'"
    and idx_openings: "map opening_index openings = idxs"
    and table_tail:
      "partial_authenticated_table rt (scale * clength) openings t"
    by blast
  have s1_t: "s1 \<le> t"
    using mmap_query_decommitment_steps_outcome[OF tail] by blast
  have opn_auth_t: "authenticated_opening_in t opn"
    by (rule authenticated_opening_in_mono[OF opn_auth_s1 s1_t])
  let ?openings = "opn # openings"
  have table_all:
    "partial_authenticated_table rt (scale * clength) ?openings t"
    using opn_auth_t table_tail opn_eq
    unfolding partial_authenticated_table_def by simp
  show ?case
    using len_openings values_openings idx_openings leaves_eq opn_eq table_all
    by (intro exI[of _ ?openings]) simp
qed

lemma check_decommit_on_query_authenticated_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes idx_in: "idx \<in> query_sample_space"
    and outcome:
      "Some (leaves, t) \<in>
        set_dist (execute (mmap (check_decommit_on_query rt idx)) s)"
  obtains openings where
    "length openings = length (powers_scaled idx)"
    "map opening_value openings = leaves"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table rt (scale * clength) openings t"
proof -
  have map_eq:
    "check_decommit_on_query rt idx =
      map (query_decommitment_step rt) (powers_scaled idx)"
    unfolding check_decommit_on_query_def query_decommitment_step_def by simp
  have idxs_bound:
    "\<And>i. i \<in> set (powers_scaled idx) \<Longrightarrow> i < scale * clength"
    using query_sample_space_powers_scaled_bound[OF idx_in]
    by (simp add: mult.commute)
  from mmap_query_decommitment_steps_authenticated_openings
      [OF idxs_bound outcome[unfolded map_eq]]
  obtain openings where
    "length openings = length (powers_scaled idx)"
    "map opening_value openings = leaves"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table rt (scale * clength) openings t"
    by blast
  then show ?thesis by (rule that)
qed

lemma fri_layer_opening_finish_authenticated_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes idx_bound: "idx < len"
    and sibling_bound: "(idx + len div 2) mod len < len"
    and xp_path_length: "length xp_path = floor_log len"
    and xn_path_length: "length xn_path = floor_log len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (fri_layer_opening_finish b rt idx x len pw
              xp xp_path xn xn_path) s)"
  obtains xp_opening xn_opening where
    "xp_opening =
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = idx,
       opening_value = xp,
       opening_path = xp_path\<rparr>"
    "xn_opening =
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = (idx + len div 2) mod len,
       opening_value = xn,
       opening_path = xn_path\<rparr>"
    "authenticated_opening_in t xp_opening"
    "authenticated_opening_in t xn_opening"
proof -
  from outcome obtain s1 ap1 s2 s3 ap2 s4 s5 where
    assert_xp:
      "Some ((), s1) \<in> set_dist (execute (assert (xp = x)) s)"
    and check_xp:
      "Some (ap1, s2) \<in>
        set_dist
          (execute (check_authentication_path len idx xp xp_path) s1)"
    and assert_ap1:
      "Some ((), s3) \<in> set_dist (execute (assert (ap1 = rt)) s2)"
    and check_xn:
      "Some (ap2, s4) \<in>
        set_dist
          (execute
            (check_authentication_path len
              ((idx + len div 2) mod len) xn xn_path) s3)"
    and assert_ap2:
      "Some ((), s5) \<in> set_dist (execute (assert (ap2 = rt)) s4)"
    and ret:
      "Some (out, t) \<in>
        set_dist
          (execute
            (return
              (idx mod (len div 2),
               (xp + xn) div 2 +
                 b * ((xp - xn) div
                   (2 * ((h ^ idx) * shift) ^ pw)),
               len div 2, pw + pw)) s5)"
    unfolding fri_layer_opening_finish_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  have ap1_eq: "ap1 = rt"
    using assert_ap1 unfolding assert_def
    by (cases "ap1 = rt") (auto simp: throw_no_outcome)
  have ap2_eq: "ap2 = rt"
    using assert_ap2 unfolding assert_def
    by (cases "ap2 = rt") (auto simp: throw_no_outcome)
  have xp_eq: "xp = x"
    using assert_xp unfolding assert_def
    by (cases "xp = x") (auto simp: throw_no_outcome)
  have s1: "s1 = s"
    using assert_xp xp_eq unfolding assert_def by simp
  have s3: "s3 = s2"
    using assert_ap1 ap1_eq unfolding assert_def by simp
  have s5: "s5 = s4"
    using assert_ap2 ap2_eq unfolding assert_def by simp
  have t: "t = s4"
    using ret unfolding s5 by simp
  have xp_bound_s2:
    "merkle_path_bound rt len idx xp xp_path s2"
  proof -
    have "merkle_path_bound ap1 len idx xp xp_path s2"
      by (rule check_authentication_path_outcome_bound[OF check_xp])
    then show ?thesis unfolding ap1_eq .
  qed
  have s2_s4: "s2 \<le> s4"
    unfolding s3[symmetric]
    by (rule check_authentication_path_hash_extends[OF check_xn])
  have xp_bound:
    "merkle_path_bound rt len idx xp xp_path t"
    unfolding t
    by (rule merkle_path_bound_mono[OF xp_bound_s2 s2_s4])
  have xn_bound:
    "merkle_path_bound rt len ((idx + len div 2) mod len)
      xn xn_path t"
  proof -
    have "merkle_path_bound ap2 len ((idx + len div 2) mod len)
        xn xn_path s4"
      by (rule check_authentication_path_outcome_bound[OF check_xn])
    then show ?thesis unfolding ap2_eq t .
  qed
  let ?xp_opening =
    "\<lparr>opening_root = rt,
      opening_length = len,
      opening_index = idx,
      opening_value = xp,
      opening_path = xp_path\<rparr>"
  let ?xn_opening =
    "\<lparr>opening_root = rt,
      opening_length = len,
      opening_index = (idx + len div 2) mod len,
      opening_value = xn,
      opening_path = xn_path\<rparr>"
  have xp_authenticated: "authenticated_opening_in t ?xp_opening"
    unfolding authenticated_opening_in_def
    using idx_bound xp_path_length xp_bound by simp
  have xn_authenticated: "authenticated_opening_in t ?xn_opening"
    unfolding authenticated_opening_in_def
    using sibling_bound xn_path_length xn_bound by simp
  show ?thesis
    by (rule that[of ?xp_opening ?xn_opening])
      (simp_all add: xp_authenticated xn_authenticated)
qed

lemma fri_layer_opening_step_authenticated_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes len_pos: "0 < len"
    and idx_bound: "idx < len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
  obtains xp_opening xn_opening where
    "opening_root xp_opening = rt"
    "opening_length xp_opening = len"
    "opening_index xp_opening = idx"
    "opening_root xn_opening = rt"
    "opening_length xn_opening = len"
    "opening_index xn_opening = (idx + len div 2) mod len"
    "authenticated_opening_in t xp_opening"
    "authenticated_opening_in t xn_opening"
proof -
  from outcome[unfolded fri_layer_opening_step_unfold_finish]
  obtain xp s1 xp_path s2 xn s3 xn_path s4 where
    read_xp: "Some (xp, s1) \<in> set_dist (execute read s)"
    and read_xp_path:
      "Some (xp_path, s2) \<in>
        set_dist (execute (ntimes read (floor_log len)) s1)"
    and read_xn: "Some (xn, s3) \<in> set_dist (execute read s2)"
    and read_xn_path:
      "Some (xn_path, s4) \<in>
        set_dist (execute (ntimes read (floor_log len)) s3)"
    and finish:
      "Some (out, t) \<in>
        set_dist
          (execute
            (fri_layer_opening_finish b rt idx x len pw
              xp xp_path xn xn_path) s4)"
    by (auto elim!: set_dist_bindE)
  have xp_path_length: "length xp_path = floor_log len"
    using ntimes_read_any_outcome[OF read_xp_path] by simp
  have xn_path_length: "length xn_path = floor_log len"
    using ntimes_read_any_outcome[OF read_xn_path] by simp
  have sibling_bound: "(idx + len div 2) mod len < len"
    using len_pos by simp
  from fri_layer_opening_finish_authenticated_openings
      [OF idx_bound sibling_bound xp_path_length xn_path_length finish]
  obtain xp_opening xn_opening where
    xp_eq:
      "xp_opening =
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr>"
    and xn_eq:
      "xn_opening =
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = (idx + len div 2) mod len,
         opening_value = xn,
         opening_path = xn_path\<rparr>"
    and xp_auth: "authenticated_opening_in t xp_opening"
    and xn_auth: "authenticated_opening_in t xn_opening"
    by blast
  show ?thesis
    by (rule that[of xp_opening xn_opening])
      (use xp_eq xn_eq xp_auth xn_auth in simp_all)
qed

lemma fri_layer_opening_step_partial_authenticated_table:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes len_pos: "0 < len"
    and idx_bound: "idx < len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
  obtains openings where
    "partial_authenticated_table rt len openings t"
    "map opening_index openings = [idx, (idx + len div 2) mod len]"
    "length openings = 2"
proof -
  from fri_layer_opening_step_authenticated_openings
      [OF len_pos idx_bound outcome]
  obtain xp_opening xn_opening where
    xp_root: "opening_root xp_opening = rt"
    and xp_len: "opening_length xp_opening = len"
    and xp_idx: "opening_index xp_opening = idx"
    and xn_root: "opening_root xn_opening = rt"
    and xn_len: "opening_length xn_opening = len"
    and xn_idx:
      "opening_index xn_opening = (idx + len div 2) mod len"
    and xp_auth: "authenticated_opening_in t xp_opening"
    and xn_auth: "authenticated_opening_in t xn_opening"
    by blast
  let ?openings = "[xp_opening, xn_opening]"
  have table: "partial_authenticated_table rt len ?openings t"
    unfolding partial_authenticated_table_def
    using xp_root xp_len xp_auth xn_root xn_len xn_auth by simp
  have indices:
    "map opening_index ?openings = [idx, (idx + len div 2) mod len]"
    using xp_idx xn_idx by simp
  show ?thesis
    by (rule that[OF table indices]) simp
qed

lemma verifier_query_round_after_index_authenticated_trace_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some ((), t) \<in>
      set_dist
        (execute
          (verifier_query_round_after_index_program
            fr f_fl f_final as fl final raw) s)"
  obtains idx leaves openings where
    "idx = index (to_nat raw)"
    "length openings = length (powers_scaled idx)"
    "map opening_value openings = leaves"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) openings t"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have idx_in: "?idx \<in> query_sample_space"
    using index_less_query_sample_space
    unfolding query_sample_space_def by simp
  from check_decommit_on_query_authenticated_openings
      [OF idx_in query_decommit]
  obtain openings where
    len_openings: "length openings = length (powers_scaled ?idx)"
    and values_openings: "map opening_value openings = fv"
    and idx_openings: "map opening_index openings = powers_scaled ?idx"
    and table_s1:
      "partial_authenticated_table fr (scale * clength) openings s1"
    by blast
  from receive_query_commits_layers_outcome[OF trace_fri]
  obtain trace_layer_chunks trace_fri_chunk where
    s1_s2: "s1 \<le> s2"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  from receive_query_commits_layers_outcome[OF comp_fri]
  obtain comp_layer_chunks comp_fri_chunk where
    s3_s4: "s3 \<le> s4"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  have s1_t: "s1 \<le> t"
    using s1_s2 s3_s4 unfolding s3_eq t_eq
    by (meson hash_ext_trans)
  have table_t:
    "partial_authenticated_table fr (scale * clength) openings t"
    by (rule partial_authenticated_table_mono[OF table_s1 s1_t])
  show ?thesis
    by (rule that[OF refl len_openings values_openings idx_openings table_t])
qed

lemma verifier_query_round_after_index_authenticated_composition_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
  obtains idx openings where
    "idx = index (to_nat raw)"
    "partial_authenticated_table composition_root (scale * clength)
      openings t"
    "map opening_index openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    "length openings = 2"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have comp_steps:
    "receive_query_commits fl =
      fri_layer_opening_step (b, composition_root) #
        receive_query_commits fl_tail"
    unfolding fl_eq receive_query_commits_def fri_layer_opening_step_def
    by simp
  from comp_fri[unfolded comp_steps]
  obtain out1 s_head where
    head:
      "Some (out1, s_head) \<in>
        set_dist
          (execute
            (fri_layer_opening_step (b, composition_root)
              (?idx, cp_eval as fv (h ^ ?idx * shift),
                clength * scale, 1)) s3)"
    and tail:
      "Some (c_out, s4) \<in>
        set_dist (execute (mfold out1 (receive_query_commits fl_tail))
          s_head)"
    by (auto elim!: set_dist_bindE)
  have len_pos: "0 < clength * scale"
    using eval_domain_nontrivial by linarith
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  from fri_layer_opening_step_partial_authenticated_table
      [OF len_pos idx_bound head]
  obtain openings where
    table_head:
      "partial_authenticated_table composition_root (clength * scale)
        openings s_head"
    and indices:
      "map opening_index openings =
        [?idx, (?idx + (clength * scale) div 2) mod (clength * scale)]"
    and len_openings: "length openings = 2"
    by (rule fri_layer_opening_step_partial_authenticated_table
        [OF len_pos idx_bound head])
  obtain i1 x1 len1 pw1 where out1_eq: "out1 = (i1, x1, len1, pw1)"
    by (cases out1)
  from receive_query_commits_layers_outcome[OF tail[unfolded out1_eq]]
  obtain tail_layer_chunks tail_chunk where s_head_s4: "s_head \<le> s4"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  have table_t:
    "partial_authenticated_table composition_root (scale * clength)
      openings t"
    using partial_authenticated_table_mono[OF table_head s_head_s4]
    unfolding t_eq by (simp add: mult.commute)
  have indices':
    "map opening_index openings =
      [?idx, fri_sibling_index (scale * clength) ?idx]"
    using indices
    unfolding fri_sibling_index_def
    by (simp add: mult.commute)
  show ?thesis
    by (rule that[OF refl table_t indices' len_openings])
qed

lemma verifier_query_round_program_authenticated_trace_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some ((), t) \<in>
      set_dist
        (execute
          (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx leaves openings where
    "idx = index (to_nat raw)"
    "length openings = length (powers_scaled idx)"
    "map opening_value openings = leaves"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) openings t"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    rand:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  from verifier_query_round_after_index_authenticated_trace_openings[OF tail]
  obtain idx leaves openings where
    idx_eq: "idx = index (to_nat raw)"
    and len_openings: "length openings = length (powers_scaled idx)"
    and values_openings: "map opening_value openings = leaves"
    and idx_openings: "map opening_index openings = powers_scaled idx"
    and table_t:
      "partial_authenticated_table fr (scale * clength) openings t"
    by blast
  show ?thesis
    by (rule that[OF idx_eq len_openings values_openings idx_openings table_t])
qed

lemma verifier_query_round_program_authenticated_composition_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx openings where
    "idx = index (to_nat raw)"
    "partial_authenticated_table composition_root (scale * clength)
      openings t"
    "map opening_index openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    "length openings = 2"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    rand:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  from verifier_query_round_after_index_authenticated_composition_openings
      [OF fl_eq tail]
  obtain idx openings where
    idx_eq: "idx = index (to_nat raw)"
    and table_t:
      "partial_authenticated_table composition_root (scale * clength)
        openings t"
    and idx_openings:
      "map opening_index openings =
        [idx, fri_sibling_index (scale * clength) idx]"
    and len_openings: "length openings = 2"
    by blast
  show ?thesis
    by (rule that[OF idx_eq table_t idx_openings len_openings])
qed

lemma ntimes_verifier_query_rounds_authenticated_trace_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (results, t) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final) n)
          s)"
  obtains raw_idxs query_idxs trace_openings where
    "length raw_idxs = n"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length trace_openings = n"
    "\<And>i. i < n \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    "\<And>i. i < n \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) t"
proof -
  have
    "\<exists>raw_idxs query_idxs trace_openings.
      length raw_idxs = n \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length trace_openings = n \<and>
      (\<forall>i < n.
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)) \<and>
      (\<forall>i < n.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) t)"
    using outcome
  proof (induction n arbitrary: s results t)
    case 0
    then show ?case
      by (intro exI[of _ "[]"]) simp
  next
    case (Suc n)
    from Suc.prems obtain u results' s1 where
      head:
        "Some (u, s1) \<in>
          set_dist
            (execute
              (verifier_query_round_program fr f_fl f_final as fl final) s)"
      and tail:
        "Some (results', t) \<in>
          set_dist
            (execute
              (ntimes
                (verifier_query_round_program fr f_fl f_final as fl final)
                n) s1)"
      and results_eq: "results = u # results'"
      by (auto elim!: set_dist_bindE)
    have u_eq: "u = ()"
      by (cases u) simp
    from verifier_query_round_program_authenticated_trace_openings
        [OF head[unfolded u_eq]]
    obtain raw idx leaves openings where
      idx_eq: "idx = index (to_nat raw)"
      and idx_openings: "map opening_index openings = powers_scaled idx"
      and table_s1:
        "partial_authenticated_table fr (scale * clength) openings s1"
      by blast
    from Suc.IH[OF tail] obtain raw_tail idx_tail openings_tail where
      len_raw_tail: "length raw_tail = n"
      and idx_tail_eq:
        "idx_tail = map (\<lambda>raw. index (to_nat raw)) raw_tail"
      and len_openings_tail: "length openings_tail = n"
      and tail_indices:
        "\<forall>i < n.
          map opening_index (openings_tail ! i) =
            powers_scaled (idx_tail ! i)"
      and tail_tables:
        "\<forall>i < n.
          partial_authenticated_table fr (scale * clength)
            (openings_tail ! i) t"
      by blast
    have s1_t: "s1 \<le> t"
      using ntimes_verifier_query_rounds_outcome[OF tail] by blast
    have table_t:
      "partial_authenticated_table fr (scale * clength) openings t"
      by (rule partial_authenticated_table_mono[OF table_s1 s1_t])
    let ?raws = "raw # raw_tail"
    let ?idxs = "idx # idx_tail"
    let ?openings = "openings # openings_tail"
    have idxs_eq:
      "?idxs = map (\<lambda>raw. index (to_nat raw)) ?raws"
      using idx_eq idx_tail_eq by simp
    have indices_all:
      "\<forall>i < Suc n.
        map opening_index (?openings ! i) =
          powers_scaled (?idxs ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < Suc n"
      show "map opening_index (?openings ! i) =
          powers_scaled (?idxs ! i)"
      proof (cases i)
        case 0
        then show ?thesis
          using idx_openings by simp
      next
        case (Suc j)
        then show ?thesis
          using i_bound tail_indices by simp
      qed
    qed
    have tables_all:
      "\<forall>i < Suc n.
        partial_authenticated_table fr (scale * clength)
          (?openings ! i) t"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < Suc n"
      show "partial_authenticated_table fr (scale * clength)
          (?openings ! i) t"
      proof (cases i)
        case 0
        then show ?thesis
          using table_t by simp
      next
        case (Suc j)
        then show ?thesis
          using i_bound tail_tables by simp
      qed
    qed
    show ?case
      apply (intro exI[of _ ?raws] exI[of _ ?idxs] exI[of _ ?openings]
          conjI)
          apply (simp add: len_raw_tail)
         apply (rule idxs_eq)
        apply (simp add: len_openings_tail)
       apply (rule indices_all)
      apply (rule tables_all)
      done
  qed
  then obtain raw_idxs query_idxs trace_openings where
    "length raw_idxs = n"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length trace_openings = n"
    "\<And>i. i < n \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    "\<And>i. i < n \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) t"
    by blast
  then show ?thesis by (rule that)
qed

lemma ntimes_verifier_query_rounds_authenticated_composition_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
  obtains raw_idxs query_idxs composition_openings where
    "length raw_idxs = n"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length composition_openings = n"
    "\<And>i. i < n \<Longrightarrow>
      map opening_index (composition_openings ! i) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)]"
    "\<And>i. i < n \<Longrightarrow>
      partial_authenticated_table composition_root (scale * clength)
        (composition_openings ! i) t"
proof -
  have
    "\<exists>raw_idxs query_idxs composition_openings.
      length raw_idxs = n \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length composition_openings = n \<and>
      (\<forall>i < n.
        map opening_index (composition_openings ! i) =
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)]) \<and>
      (\<forall>i < n.
        partial_authenticated_table composition_root (scale * clength)
          (composition_openings ! i) t)"
    using outcome
  proof (induction n arbitrary: s results t)
    case 0
    then show ?case
      by (intro exI[of _ "[]"]) simp
  next
    case (Suc n)
    from Suc.prems obtain u results' s1 where
      head:
        "Some (u, s1) \<in>
          set_dist
            (execute
              (verifier_query_round_program fr f_fl f_final as fl final) s)"
      and tail:
        "Some (results', t) \<in>
          set_dist
            (execute
              (ntimes
                (verifier_query_round_program fr f_fl f_final as fl final)
                n) s1)"
      by (auto elim!: set_dist_bindE)
    have u_eq: "u = ()"
      by (cases u) simp
    from verifier_query_round_program_authenticated_composition_openings
        [OF fl_eq head[unfolded u_eq]]
    obtain raw idx openings where
      idx_eq: "idx = index (to_nat raw)"
      and table_s1:
        "partial_authenticated_table composition_root (scale * clength)
          openings s1"
      and idx_openings:
        "map opening_index openings =
          [idx, fri_sibling_index (scale * clength) idx]"
      and len_openings: "length openings = 2"
      by (rule verifier_query_round_program_authenticated_composition_openings
          [OF fl_eq head[unfolded u_eq]])
    from Suc.IH[OF tail] obtain raw_tail idx_tail openings_tail where
      len_raw_tail: "length raw_tail = n"
      and idx_tail_eq:
        "idx_tail = map (\<lambda>raw. index (to_nat raw)) raw_tail"
      and len_openings_tail: "length openings_tail = n"
      and tail_indices:
        "\<forall>i < n.
          map opening_index (openings_tail ! i) =
            [idx_tail ! i,
             fri_sibling_index (scale * clength) (idx_tail ! i)]"
      and tail_tables:
        "\<forall>i < n.
          partial_authenticated_table composition_root (scale * clength)
            (openings_tail ! i) t"
      by blast
    have s1_t: "s1 \<le> t"
      using ntimes_verifier_query_rounds_outcome[OF tail] by blast
    have table_t:
      "partial_authenticated_table composition_root (scale * clength)
        openings t"
      by (rule partial_authenticated_table_mono[OF table_s1 s1_t])
    let ?raws = "raw # raw_tail"
    let ?idxs = "idx # idx_tail"
    let ?openings = "openings # openings_tail"
    have idxs_eq:
      "?idxs = map (\<lambda>raw. index (to_nat raw)) ?raws"
      using idx_eq idx_tail_eq by simp
    have indices_all:
      "\<forall>i < Suc n.
        map opening_index (?openings ! i) =
          [?idxs ! i, fri_sibling_index (scale * clength) (?idxs ! i)]"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < Suc n"
      show "map opening_index (?openings ! i) =
          [?idxs ! i, fri_sibling_index (scale * clength) (?idxs ! i)]"
      proof (cases i)
        case 0
        then show ?thesis
          using idx_openings by simp
      next
        case (Suc j)
        then show ?thesis
          using i_bound tail_indices by simp
      qed
    qed
    have tables_all:
      "\<forall>i < Suc n.
        partial_authenticated_table composition_root (scale * clength)
          (?openings ! i) t"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < Suc n"
      show "partial_authenticated_table composition_root (scale * clength)
          (?openings ! i) t"
      proof (cases i)
        case 0
        then show ?thesis
          using table_t by simp
      next
        case (Suc j)
        then show ?thesis
          using i_bound tail_tables by simp
      qed
    qed
    show ?case
      apply (intro exI[of _ ?raws] exI[of _ ?idxs]
          exI[of _ ?openings] conjI)
          apply (simp add: len_raw_tail)
         apply (rule idxs_eq)
        apply (simp add: len_openings_tail)
       apply (rule indices_all)
      apply (rule tables_all)
      done
  qed
  then obtain raw_idxs query_idxs composition_openings where
    len_raw: "length raw_idxs = n"
    and idxs_eq: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_openings: "length composition_openings = n"
    and indices:
      "\<forall>i < n.
        map opening_index (composition_openings ! i) =
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)]"
    and tables:
      "\<forall>i < n.
        partial_authenticated_table composition_root (scale * clength)
          (composition_openings ! i) t"
    by (elim exE conjE, blast)
  show ?thesis
    by (rule that[OF len_raw idxs_eq len_openings])
      (use indices tables in auto)
qed

lemma ntimes_verifier_query_rounds_authenticated_trace_openings_no_raws:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (results, t) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final) n)
          s)"
  obtains query_idxs trace_openings where
    "length query_idxs = n"
    "length trace_openings = n"
    "\<And>i. i < n \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    "\<And>i. i < n \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) t"
proof (rule ntimes_verifier_query_rounds_authenticated_trace_openings
    [OF outcome])
  fix raw_idxs query_idxs trace_openings
  assume len_raw: "length raw_idxs = n"
    and idxs_eq: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_openings: "length trace_openings = n"
    and indices:
      "\<And>i. i < n \<Longrightarrow>
        map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    and tables:
      "\<And>i. i < n \<Longrightarrow>
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) t"
  have len_query_idxs: "length query_idxs = n"
    using len_raw idxs_eq by simp
  show ?thesis
    by (rule that[OF len_query_idxs len_openings indices tables])
qed

lemma verify_monad_authenticated_trace_openings:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  obtains fr query_idxs trace_openings where
    "length query_idxs = rounds"
    "length trace_openings = rounds"
    "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    "\<And>i. i < rounds \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
proof -
  from verify_monad_header_extraction[OF outcome]
  obtain fr f_fl f_final as dg fl final query_state where
    query_out:
      "Some (result, final_state) \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
    by metis
  from ntimes_verifier_query_rounds_authenticated_trace_openings
      [OF query_out]
  obtain raw_idxs query_idxs trace_openings where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_def:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_openings: "length trace_openings = rounds"
    and indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
    and tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) final_state"
    by blast
  have len_query_idxs: "length query_idxs = rounds"
    using len_raw query_idxs_def by simp
  show ?thesis
    by (rule that[OF len_query_idxs len_openings indices tables])
qed

definition accepted_with_partial_trace_openings
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> nat list \<Rightarrow> 'f authenticated_opening list list \<Rightarrow> bool"
where
  "accepted_with_partial_trace_openings s out fr query_idxs trace_openings \<longleftrightarrow>
    accepted out \<and>
    (\<exists>result final_state.
      out = Some (result, final_state) \<and>
      length query_idxs = rounds \<and>
      length trace_openings = rounds \<and>
      (\<forall>i < rounds.
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)) \<and>
      (\<forall>i < rounds.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) final_state))"

lemma accepted_with_partial_trace_openings_imp_accepted:
  assumes "accepted_with_partial_trace_openings s out fr query_idxs trace_openings"
  shows "accepted out"
  using assms unfolding accepted_with_partial_trace_openings_def by simp

lemma accepted_with_partial_trace_openings_shapes:
  assumes "accepted_with_partial_trace_openings s out fr query_idxs trace_openings"
  shows "length query_idxs = rounds"
    and "length trace_openings = rounds"
    and "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
  using assms unfolding accepted_with_partial_trace_openings_def by blast+

definition table_agrees_with_authenticated_openings
  :: "'f list \<Rightarrow> nat \<Rightarrow> 'f authenticated_opening list \<Rightarrow> bool"
where
  "table_agrees_with_authenticated_openings table len openings \<longleftrightarrow>
    length table = len \<and>
    (\<forall>opening \<in> set openings.
      opening_index opening < len \<and>
      table ! opening_index opening = opening_value opening)"

lemma table_agrees_with_authenticated_openings_subset:
  assumes agrees:
      "table_agrees_with_authenticated_openings table len openings"
    and subset: "set openings' \<subseteq> set openings"
  shows "table_agrees_with_authenticated_openings table len openings'"
  using assms
  unfolding table_agrees_with_authenticated_openings_def by blast

lemma table_agrees_with_authenticated_openings_consistent_exists:
  assumes idx_bound:
      "\<And>opn. opn \<in> set openings \<Longrightarrow> opening_index opn < len"
    and consistent:
      "\<And>opn opn'. opn \<in> set openings \<Longrightarrow>
        opn' \<in> set openings \<Longrightarrow>
        opening_index opn = opening_index opn' \<Longrightarrow>
        opening_value opn = opening_value opn'"
  shows "\<exists>table. table_agrees_with_authenticated_openings table len
    openings"
proof -
  let ?value =
    "\<lambda>j. if \<exists>opn \<in> set openings. opening_index opn = j
      then opening_value
        (SOME opn. opn \<in> set openings \<and> opening_index opn = j)
      else 0"
  let ?table = "map ?value [0..<len]"
  have agrees:
    "\<And>opn. opn \<in> set openings \<Longrightarrow>
      ?table ! opening_index opn = opening_value opn"
  proof -
    fix opn
    assume opn_in: "opn \<in> set openings"
    let ?chosen =
      "SOME opn'. opn' \<in> set openings \<and>
        opening_index opn' = opening_index opn"
    have ex_chosen:
      "\<exists>opn'. opn' \<in> set openings \<and>
        opening_index opn' = opening_index opn"
      using opn_in by blast
    have chosen:
      "?chosen \<in> set openings \<and>
        opening_index ?chosen = opening_index opn"
      by (rule someI_ex[OF ex_chosen])
    have value_eq:
      "opening_value ?chosen = opening_value opn"
      using consistent[OF conjunct1[OF chosen] opn_in conjunct2[OF chosen]]
      by simp
    have "?table ! opening_index opn = ?value (opening_index opn)"
      using idx_bound[OF opn_in] by simp
    also have "... = opening_value ?chosen"
    proof -
      have "\<exists>opn' \<in> set openings. opening_index opn' =
          opening_index opn"
        using opn_in by blast
      then show ?thesis by simp
    qed
    also have "... = opening_value opn"
      by (rule value_eq)
    finally show "?table ! opening_index opn = opening_value opn" .
  qed
  have "table_agrees_with_authenticated_openings ?table len openings"
    unfolding table_agrees_with_authenticated_openings_def
    using idx_bound agrees by simp
  then show ?thesis by blast
qed

definition partial_trace_table_candidate
  :: "'f list \<Rightarrow> 'f authenticated_opening list list \<Rightarrow> bool"
where
  "partial_trace_table_candidate trace_table trace_openings \<longleftrightarrow>
    length trace_table = scale * clength \<and>
    length trace_openings = rounds \<and>
    (\<forall>i < rounds.
      table_agrees_with_authenticated_openings trace_table
        (scale * clength) (trace_openings ! i))"

definition partial_trace_table_candidates
  :: "'f authenticated_opening list list \<Rightarrow> 'f list set"
where
  "partial_trace_table_candidates trace_openings =
    {trace_table. partial_trace_table_candidate trace_table trace_openings}"

definition accepted_with_partial_composition_openings
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> nat list \<Rightarrow> 'f authenticated_opening list list \<Rightarrow> bool"
where
  "accepted_with_partial_composition_openings s out composition_root
      query_idxs composition_openings \<longleftrightarrow>
    accepted out \<and>
    (\<exists>result final_state.
      out = Some (result, final_state) \<and>
      length query_idxs = rounds \<and>
      length composition_openings = rounds \<and>
      (\<forall>i < rounds.
        map opening_index (composition_openings ! i) =
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)]) \<and>
      (\<forall>i < rounds.
        partial_authenticated_table composition_root (scale * clength)
          (composition_openings ! i) final_state))"

definition partial_composition_table_candidate
  :: "'f list \<Rightarrow> 'f authenticated_opening list list \<Rightarrow> bool"
where
  "partial_composition_table_candidate composition_table composition_openings
    \<longleftrightarrow>
      length composition_table = scale * clength \<and>
      length composition_openings = rounds \<and>
      (\<forall>i < rounds.
        table_agrees_with_authenticated_openings composition_table
          (scale * clength) (composition_openings ! i))"

definition partial_composition_table_candidates
  :: "'f authenticated_opening list list \<Rightarrow> 'f list set"
where
  "partial_composition_table_candidates composition_openings =
    {composition_table.
      partial_composition_table_candidate composition_table
        composition_openings}"

lemma partial_trace_table_candidateD:
  assumes cand: "partial_trace_table_candidate trace_table trace_openings"
    and i_bound: "i < rounds"
    and opn_in: "opn \<in> set (trace_openings ! i)"
  shows "length trace_table = scale * clength"
    and "opening_index opn < scale * clength"
    and "trace_table ! opening_index opn = opening_value opn"
  using assms
  unfolding partial_trace_table_candidate_def
    table_agrees_with_authenticated_openings_def
  by blast+

lemma table_agrees_with_authenticated_openings_map_values:
  assumes agrees:
      "table_agrees_with_authenticated_openings table len openings"
    and idxs: "map opening_index openings = idxs"
  shows "map ((!) table) idxs = map opening_value openings"
proof (rule nth_equalityI)
  show "length (map ((!) table) idxs) =
      length (map opening_value openings)"
  proof -
    have "length idxs = length openings"
      using arg_cong[OF idxs, of length] by simp
    then show ?thesis by simp
  qed
next
  fix k
  assume k_bound: "k < length (map ((!) table) idxs)"
  have len_idxs: "length idxs = length openings"
    using arg_cong[OF idxs, of length] by simp
  then have k_openings: "k < length openings"
    using k_bound len_idxs by simp
  have idx_eq: "idxs ! k = opening_index (openings ! k)"
    using idxs k_openings by (metis length_map nth_map)
  have opening_in: "openings ! k \<in> set openings"
    by (rule nth_mem[OF k_openings])
  have "table ! opening_index (openings ! k) =
      opening_value (openings ! k)"
    using agrees opening_in
    unfolding table_agrees_with_authenticated_openings_def by blast
  then show "map ((!) table) idxs ! k =
      map opening_value openings ! k"
    using k_bound k_openings idx_eq by simp
qed

lemma partial_trace_table_candidate_query_values:
  assumes cand: "partial_trace_table_candidate trace_table trace_openings"
    and i_bound: "i < rounds"
    and idxs:
      "map opening_index (trace_openings ! i) = powers_scaled idx"
  shows
    "map ((!) trace_table) (powers_scaled idx) =
      map opening_value (trace_openings ! i)"
proof -
  have agrees:
    "table_agrees_with_authenticated_openings trace_table
      (scale * clength) (trace_openings ! i)"
    using cand i_bound unfolding partial_trace_table_candidate_def by blast
  show ?thesis
    by (rule table_agrees_with_authenticated_openings_map_values
        [OF agrees idxs])
qed

lemma partial_trace_table_candidates_iff:
  "trace_table \<in> partial_trace_table_candidates trace_openings \<longleftrightarrow>
    partial_trace_table_candidate trace_table trace_openings"
  unfolding partial_trace_table_candidates_def by simp

lemma accepted_with_partial_composition_openings_imp_accepted:
  assumes
    "accepted_with_partial_composition_openings s out composition_root
      query_idxs composition_openings"
  shows "accepted out"
  using assms
  unfolding accepted_with_partial_composition_openings_def by simp

lemma accepted_with_partial_composition_openings_shapes:
  assumes
    "accepted_with_partial_composition_openings s out composition_root
      query_idxs composition_openings"
  shows "length query_idxs = rounds"
    and "length composition_openings = rounds"
    and "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (composition_openings ! i) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)]"
  using assms
  unfolding accepted_with_partial_composition_openings_def by blast+

definition accepted_with_partial_initial_openings
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> nat list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> bool"
where
  "accepted_with_partial_initial_openings s out fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings \<longleftrightarrow>
    accepted out \<and>
    composition_fri_roots \<noteq> [] \<and>
    (\<exists>rest.
      verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest) \<and>
    accepted_with_partial_trace_openings s out fr trace_query_idxs
      trace_openings \<and>
    accepted_with_partial_composition_openings s out
      (hd composition_fri_roots) composition_query_idxs composition_openings"

lemma accepted_with_partial_initial_openings_imp_accepted:
  assumes
    "accepted_with_partial_initial_openings s out fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings"
  shows "accepted out"
  using assms unfolding accepted_with_partial_initial_openings_def by simp

lemma accepted_with_partial_initial_openings_shapes:
  assumes
    "accepted_with_partial_initial_openings s out fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings"
  shows "composition_fri_roots \<noteq> []"
    and "\<exists>rest. verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    and "accepted_with_partial_trace_openings s out fr trace_query_idxs
      trace_openings"
    and "accepted_with_partial_composition_openings s out
      (hd composition_fri_roots) composition_query_idxs composition_openings"
  using assms unfolding accepted_with_partial_initial_openings_def by blast+

lemma query_rounds_accepted_with_partial_composition_openings:
  fixes s query_state final_state :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
  obtains query_idxs composition_openings where
    "accepted_with_partial_composition_openings s
      (Some (results, final_state)) composition_root query_idxs
      composition_openings"
proof -
  from ntimes_verifier_query_rounds_authenticated_composition_openings
      [OF fl_eq outcome]
  obtain raw_idxs query_idxs composition_openings where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_def:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_openings: "length composition_openings = rounds"
    and indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (composition_openings ! i) =
          [query_idxs ! i,
           fri_sibling_index (scale * clength) (query_idxs ! i)]"
    and tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table composition_root (scale * clength)
          (composition_openings ! i) final_state"
    by blast
  have len_query_idxs: "length query_idxs = rounds"
    using len_raw query_idxs_def by simp
  have partial:
    "accepted_with_partial_composition_openings s
      (Some (results, final_state)) composition_root query_idxs
      composition_openings"
    unfolding accepted_with_partial_composition_openings_def accepted_def
    apply (intro conjI exI)
        apply simp
       apply simp
      apply (rule len_query_idxs)
     apply (rule len_openings)
    using indices tables by simp_all
  show ?thesis
    by (rule that[OF partial])
qed

lemma verify_monad_accepted_with_partial_composition_openings_if_bound_tables:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs_bound"
  obtains composition_root query_idxs composition_openings where
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) composition_root query_idxs
      composition_openings"
    "merkle_root_binds_table composition_root composition_table final_state"
proof -
  from verify_monad_header_extraction[OF outcome]
  obtain fr f_fl f_final as' dg fl final query_state where
    header:
      "verifier_header_transcript s fr (map snd f_fl) f_final as' dg
        (map snd fl) final (PTranscript query_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as' fl final)
              rounds)
            query_state)"
    by metis
  from bound obtain fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and comp_nonempty: "composition_fri_roots' \<noteq> []"
    and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots')
        composition_table final_state"
    unfolding accepted_with_bound_tables_def by blast
  have eqs:
    "fr' = fr \<and>
     f_fri_roots' = map snd f_fl \<and>
     f_final' = f_final \<and>
     as = as' \<and>
     dg' = dg \<and>
     composition_fri_roots' = map snd fl \<and>
     final' = final \<and>
     rest' = PTranscript query_state"
    using verifier_header_transcript_unique[OF header' header] by simp
  then have fl_nonempty: "fl \<noteq> []"
    using comp_nonempty by (cases fl) simp_all
  then obtain b composition_root fl_tail where fl_eq:
    "fl = (b, composition_root) # fl_tail"
    by (cases fl) auto
  have comp_root_eq: "hd composition_fri_roots' = composition_root"
    using eqs fl_eq comp_nonempty by simp
  from query_rounds_accepted_with_partial_composition_openings
      [OF fl_eq query_out]
  obtain query_idxs composition_openings where partial:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) composition_root query_idxs
      composition_openings"
    by blast
  have bind:
    "merkle_root_binds_table composition_root composition_table final_state"
    using comp_bind unfolding comp_root_eq .
  show ?thesis
    by (rule that[OF partial bind])
qed

lemma verify_monad_accepted_with_partial_composition_openings_if_header_nonempty:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header0:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
  obtains query_idxs composition_openings where
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots) query_idxs
      composition_openings"
proof -
  from verify_monad_header_extraction[OF outcome]
  obtain fr' f_fl f_final' as' dg' fl final' query_state where
    header:
      "verifier_header_transcript s fr' (map snd f_fl) f_final' as' dg'
        (map snd fl) final' (PTranscript query_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl f_final' as' fl
                final') rounds)
            query_state)"
    by metis
  have eqs:
    "fr' = fr \<and>
     map snd f_fl = f_fri_roots \<and>
     f_final' = f_final \<and>
     as' = as \<and>
     dg' = dg \<and>
     map snd fl = composition_fri_roots \<and>
     final' = final \<and>
     PTranscript query_state = rest"
    using verifier_header_transcript_unique[OF header header0] by simp
  have fl_nonempty: "fl \<noteq> []"
    using comp_nonempty eqs by (cases fl) simp_all
  then obtain b composition_root fl_tail where fl_eq:
    "fl = (b, composition_root) # fl_tail"
    by (cases fl) auto
  have root_eq: "composition_root = hd composition_fri_roots"
  proof -
    have map_eq: "map snd fl = composition_fri_roots"
      using eqs by simp
    then have "composition_root # map snd fl_tail = composition_fri_roots"
      unfolding fl_eq by simp
    then have "hd composition_fri_roots = composition_root"
      by (metis list.sel(1))
    then show ?thesis
      by simp
  qed
  from query_rounds_accepted_with_partial_composition_openings
      [OF fl_eq query_out]
  obtain query_idxs composition_openings where partial:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) composition_root query_idxs
      composition_openings"
    by blast
  show ?thesis
    by (rule that[of query_idxs composition_openings])
      (use partial root_eq in simp)
qed

lemma partial_composition_table_candidateD:
  assumes
    cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and i_bound: "i < rounds"
    and opn_in: "opn \<in> set (composition_openings ! i)"
  shows "length composition_table = scale * clength"
    and "opening_index opn < scale * clength"
    and "composition_table ! opening_index opn = opening_value opn"
  using assms
  unfolding partial_composition_table_candidate_def
    table_agrees_with_authenticated_openings_def
  by blast+

lemma partial_composition_table_candidate_query_values:
  assumes cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and i_bound: "i < rounds"
    and idxs:
      "map opening_index (composition_openings ! i) =
        [idx, fri_sibling_index (scale * clength) idx]"
  shows
    "map ((!) composition_table)
        [idx, fri_sibling_index (scale * clength) idx] =
      map opening_value (composition_openings ! i)"
proof -
  have agrees:
    "table_agrees_with_authenticated_openings composition_table
      (scale * clength) (composition_openings ! i)"
    using cand i_bound
    unfolding partial_composition_table_candidate_def by blast
  show ?thesis
    by (rule table_agrees_with_authenticated_openings_map_values
        [OF agrees idxs])
qed

lemma partial_composition_table_candidate_query_value:
  assumes cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and i_bound: "i < rounds"
    and idxs:
      "map opening_index (composition_openings ! i) =
        [idx, fri_sibling_index (scale * clength) idx]"
  shows
    "composition_table ! idx =
      opening_value ((composition_openings ! i) ! 0)"
proof -
  have vals:
    "map ((!) composition_table)
        [idx, fri_sibling_index (scale * clength) idx] =
      map opening_value (composition_openings ! i)"
    by (rule partial_composition_table_candidate_query_values
        [OF cand i_bound idxs])
  have len_openings: "length (composition_openings ! i) = 2"
  proof -
    have "length (map opening_index (composition_openings ! i)) =
        length [idx, fri_sibling_index (scale * clength) idx]"
      using arg_cong[OF idxs, of length] by simp
    then show ?thesis by simp
  qed
  have value0:
    "map ((!) composition_table)
        [idx, fri_sibling_index (scale * clength) idx] ! 0 =
      map opening_value (composition_openings ! i) ! 0"
    using vals by simp
  show ?thesis
    using value0 len_openings by (cases "composition_openings ! i") auto
qed

lemma partial_composition_table_candidates_iff:
  "composition_table \<in>
      partial_composition_table_candidates composition_openings \<longleftrightarrow>
    partial_composition_table_candidate composition_table composition_openings"
  unfolding partial_composition_table_candidates_def by simp

lemma verify_monad_accepted_with_partial_trace_openings:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  obtains fr query_idxs trace_openings where
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr query_idxs trace_openings"
proof -
  show ?thesis
  proof (rule verify_monad_authenticated_trace_openings[OF outcome])
    fix fr query_idxs trace_openings
    assume len_query_idxs: "length query_idxs = rounds"
      and len_openings: "length trace_openings = rounds"
      and indices:
        "\<And>i. i < rounds \<Longrightarrow>
          map opening_index (trace_openings ! i) =
            powers_scaled (query_idxs ! i)"
      and tables:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_authenticated_table fr (scale * clength)
            (trace_openings ! i) final_state"
    have partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
      unfolding accepted_with_partial_trace_openings_def accepted_def
      apply (intro conjI exI)
          apply simp
         apply simp
        apply (rule len_query_idxs)
       apply (rule len_openings)
      using indices tables by simp_all
    show ?thesis
      by (rule that[OF partial])
  qed
qed

lemma verify_monad_accepted_with_partial_trace_openings_for_header:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header0:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  obtains query_idxs trace_openings where
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr query_idxs trace_openings"
proof -
  from verify_monad_header_extraction[OF outcome]
  obtain fr' f_fl f_final' as' dg' fl final' query_state where
    header:
      "verifier_header_transcript s fr' (map snd f_fl) f_final' as' dg'
        (map snd fl) final' (PTranscript query_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl f_final' as' fl
                final') rounds)
            query_state)"
    by metis
  have fr_eq: "fr' = fr"
    using verifier_header_transcript_unique[OF header header0] by simp
  obtain query_idxs trace_openings where
    len_query_idxs: "length query_idxs = rounds"
    and len_openings: "length trace_openings = rounds"
    and indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
      and tables:
        "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table fr' (scale * clength)
          (trace_openings ! i) final_state"
  proof (rule ntimes_verifier_query_rounds_authenticated_trace_openings_no_raws
      [OF query_out])
    fix query_idxs trace_openings
    assume len_query_idxs: "length query_idxs = rounds"
      and len_openings: "length trace_openings = rounds"
      and indices:
        "\<And>i. i < rounds \<Longrightarrow>
          map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
      and tables:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_authenticated_table fr' (scale * clength)
            (trace_openings ! i) final_state"
    show ?thesis
      by (rule that[OF len_query_idxs len_openings indices tables])
  qed
  have partial:
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr query_idxs trace_openings"
  proof -
    have all_indices:
      "\<forall>i < rounds.
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
      using indices by blast
    have all_tables:
      "\<forall>i < rounds.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) final_state"
      using tables fr_eq by simp
    show ?thesis
      unfolding accepted_with_partial_trace_openings_def accepted_def
      by (intro conjI exI[of _ result] exI[of _ final_state])
        (use len_query_idxs len_openings all_indices all_tables in simp_all)
  qed
  show ?thesis
    by (rule that[OF partial])
qed

lemma verify_monad_accepted_with_partial_initial_openings_if_header_nonempty:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
  obtains trace_query_idxs trace_openings composition_query_idxs
      composition_openings where
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr trace_query_idxs trace_openings"
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots)
      composition_query_idxs composition_openings"
proof -
  from verify_monad_accepted_with_partial_trace_openings_for_header
      [OF outcome header]
  obtain trace_query_idxs trace_openings where trace_partial:
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr trace_query_idxs trace_openings"
    by blast
  from verify_monad_accepted_with_partial_composition_openings_if_header_nonempty
      [OF outcome header comp_nonempty]
  obtain composition_query_idxs composition_openings where composition_partial:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots)
      composition_query_idxs composition_openings"
    by blast
  show ?thesis
    by (rule that[OF trace_partial composition_partial])
qed

lemma verify_monad_accepted_with_partial_initial_openings:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
  obtains trace_query_idxs trace_openings composition_query_idxs
      composition_openings where
    "accepted_with_partial_initial_openings s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings"
proof -
  from verify_monad_accepted_with_partial_initial_openings_if_header_nonempty
      [OF outcome header comp_nonempty]
  obtain trace_query_idxs trace_openings composition_query_idxs
      composition_openings where
    trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and composition_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    by blast
  have accepted_out: "accepted (Some (result, final_state))"
    by (rule accepted_with_partial_trace_openings_imp_accepted
        [OF trace_partial])
  have evidence:
    "accepted_with_partial_initial_openings s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings"
    unfolding accepted_with_partial_initial_openings_def
    by (intro conjI exI[of _ rest])
      (use accepted_out comp_nonempty header trace_partial
        composition_partial in simp_all)
  show ?thesis
    by (rule that[OF evidence])
qed

lemma merkle_path_bound_unique_value_if_clean:
  assumes clean: "\<not> hash_map_output_collision s"
    and first: "merkle_path_bound rt len idx v path s"
    and second: "merkle_path_bound rt len idx v' path' s"
    and same_length: "length path = length path'"
  shows "v = v'"
  using first second same_length
proof (induction path arbitrary: path' rt len idx)
  case Nil
  then have path': "path' = []" by simp
  have first_lookup:
    "fmlookup (HashMap s) (MerkleLeaf v) = Some rt"
    using Nil.prems(1) by simp
  have second_lookup:
    "fmlookup (HashMap s) (MerkleLeaf v') = Some rt"
    using Nil.prems(2) path' by simp
  show ?case
  proof (rule ccontr)
    assume "v \<noteq> v'"
    then have keys: "MerkleLeaf v \<noteq> MerkleLeaf v'" by simp
    have "hash_map_output_collision s"
      by (rule hash_map_output_collisionI
          [OF keys first_lookup second_lookup])
    then show False using clean by contradiction
  qed
next
  case (Cons sibling path)
  from Cons.prems(3) obtain sibling' path'' where
    path': "path' = sibling' # path''"
    and lengths: "length path = length path''"
    by (cases path') auto
  show ?case
  proof (cases "idx < len div 2")
    case True
    obtain child where
      child:
        "merkle_path_bound child (len div 2) idx v path s"
      and first_lookup:
        "fmlookup (HashMap s) (MerkleNode child sibling) = Some rt"
      using Cons.prems(1) True by auto
    obtain child' where
      child':
        "merkle_path_bound child' (len div 2) idx v' path'' s"
      and second_lookup:
        "fmlookup (HashMap s) (MerkleNode child' sibling') = Some rt"
      using Cons.prems(2) True path' by auto
    have node_eq:
      "MerkleNode child sibling = MerkleNode child' sibling'"
    proof (rule ccontr)
      assume neq:
        "MerkleNode child sibling \<noteq> MerkleNode child' sibling'"
      have "hash_map_output_collision s"
        by (rule hash_map_output_collisionI
            [OF neq first_lookup second_lookup])
      then show False using clean by contradiction
    qed
    have child_eq: "child = child'" using node_eq by simp
    show ?thesis
      by (rule Cons.IH[OF child _ lengths])
        (use child' child_eq in simp)
  next
    case False
    obtain child where
      child:
        "merkle_path_bound child (len div 2) (idx - len div 2)
          v path s"
      and first_lookup:
        "fmlookup (HashMap s) (MerkleNode sibling child) = Some rt"
      using Cons.prems(1) False by auto
    obtain child' where
      child':
        "merkle_path_bound child' (len div 2) (idx - len div 2)
          v' path'' s"
      and second_lookup:
        "fmlookup (HashMap s) (MerkleNode sibling' child') = Some rt"
      using Cons.prems(2) False path' by auto
    have node_eq:
      "MerkleNode sibling child = MerkleNode sibling' child'"
    proof (rule ccontr)
      assume neq:
        "MerkleNode sibling child \<noteq> MerkleNode sibling' child'"
      have "hash_map_output_collision s"
        by (rule hash_map_output_collisionI
            [OF neq first_lookup second_lookup])
      then show False using clean by contradiction
    qed
    have child_eq: "child = child'" using node_eq by simp
    show ?thesis
      by (rule Cons.IH[OF child _ lengths])
        (use child' child_eq in simp)
  qed
qed

lemma inconsistent_authenticated_openings_imp_hash_collision:
  assumes first: "authenticated_opening_in s opening"
    and second: "authenticated_opening_in s opening'"
    and same_root: "opening_root opening = opening_root opening'"
    and same_length: "opening_length opening = opening_length opening'"
    and same_index: "opening_index opening = opening_index opening'"
    and different_value: "opening_value opening \<noteq> opening_value opening'"
  shows "hash_map_output_collision s"
proof (rule ccontr)
  assume clean: "\<not> hash_map_output_collision s"
  have path_lengths:
    "length (opening_path opening) = length (opening_path opening')"
    using first second same_length
    unfolding authenticated_opening_in_def by simp
  have first_bound:
    "merkle_path_bound
      (opening_root opening)
      (opening_length opening)
      (opening_index opening)
      (opening_value opening)
      (opening_path opening)
      s"
    using first unfolding authenticated_opening_in_def by blast
  have second_bound:
    "merkle_path_bound
      (opening_root opening')
      (opening_length opening')
      (opening_index opening')
      (opening_value opening')
      (opening_path opening')
      s"
    using second unfolding authenticated_opening_in_def by blast
  have values_eq:
    "opening_value opening = opening_value opening'"
  proof (rule merkle_path_bound_unique_value_if_clean[
      OF clean first_bound _ path_lengths])
    show
      "merkle_path_bound
        (opening_root opening)
        (opening_length opening)
        (opening_index opening)
        (opening_value opening')
        (opening_path opening')
        s"
      using second_bound same_root same_length same_index by simp
  qed
  show False using different_value values_eq by contradiction
qed

lemma partial_authenticated_table_values_unique_if_clean:
  assumes table: "partial_authenticated_table rt len openings s"
    and clean: "\<not> hash_map_output_collision s"
    and first: "opening \<in> set openings"
    and second: "opening' \<in> set openings"
    and same_index: "opening_index opening = opening_index opening'"
  shows "opening_value opening = opening_value opening'"
proof (rule ccontr)
  assume different: "opening_value opening \<noteq> opening_value opening'"
  have first_auth: "authenticated_opening_in s opening"
    using table first unfolding partial_authenticated_table_def by blast
  have second_auth: "authenticated_opening_in s opening'"
    using table second unfolding partial_authenticated_table_def by blast
  have roots: "opening_root opening = opening_root opening'"
  proof -
    have "opening_root opening = rt"
      using table first unfolding partial_authenticated_table_def by blast
    moreover have "opening_root opening' = rt"
      using table second unfolding partial_authenticated_table_def by blast
    ultimately show ?thesis by simp
  qed
  have lengths: "opening_length opening = opening_length opening'"
  proof -
    have "opening_length opening = len"
      using table first unfolding partial_authenticated_table_def by blast
    moreover have "opening_length opening' = len"
      using table second unfolding partial_authenticated_table_def by blast
    ultimately show ?thesis by simp
  qed
  have "hash_map_output_collision s"
    by (rule inconsistent_authenticated_openings_imp_hash_collision[
          OF first_auth second_auth roots lengths same_index different])
  then show False using clean by contradiction
qed

lemma accepted_with_partial_trace_openings_values_unique_if_clean:
  assumes partial:
      "accepted_with_partial_trace_openings s (Some (result, final_state))
        fr query_idxs trace_openings"
    and clean: "\<not> hash_map_output_collision final_state"
    and i_bound: "i < rounds"
    and opn_in: "opn \<in> set (trace_openings ! i)"
    and opn'_in: "opn' \<in> set (trace_openings ! i)"
    and same_index: "opening_index opn = opening_index opn'"
  shows "opening_value opn = opening_value opn'"
proof -
  have table:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! i) final_state"
    using partial i_bound unfolding accepted_with_partial_trace_openings_def
    by blast
  show ?thesis
    by (rule partial_authenticated_table_values_unique_if_clean
        [OF table clean opn_in opn'_in same_index])
qed

definition partial_trace_openings_inconsistent_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "partial_trace_openings_inconsistent_bad s out \<longleftrightarrow>
    (\<exists>fr query_idxs trace_openings result final_state i opn opn'.
      out = Some (result, final_state) \<and>
      accepted_with_partial_trace_openings s out fr query_idxs trace_openings \<and>
      i < rounds \<and>
      opn \<in> set (trace_openings ! i) \<and>
      opn' \<in> set (trace_openings ! i) \<and>
      opening_index opn = opening_index opn' \<and>
      opening_value opn \<noteq> opening_value opn')"

lemma accepted_with_partial_trace_openings_values_unique_if_no_bad:
  assumes partial:
      "accepted_with_partial_trace_openings s (Some (result, final_state))
        fr query_idxs trace_openings"
    and no_bad:
      "\<not> partial_trace_openings_inconsistent_bad s
        (Some (result, final_state))"
    and i_bound: "i < rounds"
    and opn_in: "opn \<in> set (trace_openings ! i)"
    and opn'_in: "opn' \<in> set (trace_openings ! i)"
    and same_index: "opening_index opn = opening_index opn'"
  shows "opening_value opn = opening_value opn'"
proof (rule ccontr)
  assume neq: "opening_value opn \<noteq> opening_value opn'"
  have "partial_trace_openings_inconsistent_bad s
      (Some (result, final_state))"
    unfolding partial_trace_openings_inconsistent_bad_def
    by (intro exI[of _ fr] exI[of _ query_idxs]
        exI[of _ trace_openings] exI[of _ result]
        exI[of _ final_state] exI[of _ i] exI[of _ opn]
        exI[of _ opn'])
      (use partial i_bound opn_in opn'_in same_index neq in simp)
  then show False using no_bad by contradiction
qed

lemma merkle_bound_table_agrees_with_authenticated_opening_if_clean:
  assumes bind: "merkle_root_binds_table rt table final_state"
    and len_pow: "length table = 2 ^ n"
    and auth: "authenticated_opening_in final_state opening"
    and root: "opening_root opening = rt"
    and len: "opening_length opening = length table"
    and clean: "\<not> hash_map_output_collision final_state"
  shows
    "opening_index opening < length table \<and>
      table ! opening_index opening = opening_value opening"
proof -
  from bind obtain tree where created:
      "created_tree table tree final_state"
    and rt_eq: "rt = value tree"
    unfolding merkle_root_binds_table_def by blast
  have idx_bound: "opening_index opening < length table"
    using auth len unfolding authenticated_opening_in_def by simp
  have table_root:
    "merkle_path_root_in_map final_state (length table)
      (opening_index opening) (table ! opening_index opening)
      (get_authentication_path (length table) (opening_index opening) tree) =
      Some rt"
    using protocol_created_tree_path_root_in_map[
        OF created[unfolded created_tree_def] len_pow idx_bound]
    unfolding rt_eq .
  have opening_root_in_map:
    "merkle_path_root_in_map final_state (length table)
      (opening_index opening) (opening_value opening)
      (opening_path opening) = Some rt"
    using authenticated_opening_root_in_map[OF auth] root len by simp
  have same:
    "(table ! opening_index opening = opening_value opening \<and>
      get_authentication_path (length table) (opening_index opening) tree =
        opening_path opening) \<or>
      hash_map_output_collision final_state"
    by (rule merkle_path_root_same_index_eq_or_hash_collision[
        OF table_root opening_root_in_map])
  then have value_eq:
    "table ! opening_index opening = opening_value opening"
    using clean by blast
  show ?thesis
    using idx_bound value_eq by simp
qed

lemma accepted_bound_trace_table_partial_candidate_if_clean:
  assumes bind: "merkle_root_binds_table fr trace_table final_state"
    and len_table: "length trace_table = scale * clength"
    and partial:
      "accepted_with_partial_trace_openings s (Some (result, final_state))
        fr query_idxs trace_openings"
    and clean: "\<not> hash_map_output_collision final_state"
  shows "partial_trace_table_candidate trace_table trace_openings"
proof -
  obtain n where len_pow: "clength * scale = 2 ^ n"
    using eval_domain_length_power by blast
  have table_pow: "length trace_table = 2 ^ n"
    using len_table len_pow by (simp add: mult.commute)
  have len_openings: "length trace_openings = rounds"
    using partial unfolding accepted_with_partial_trace_openings_def by blast
  have agrees:
    "\<And>i. i < rounds \<Longrightarrow>
      table_agrees_with_authenticated_openings trace_table
        (scale * clength) (trace_openings ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have table_i:
      "partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
      using partial i_bound
      unfolding accepted_with_partial_trace_openings_def by blast
    show
      "table_agrees_with_authenticated_openings trace_table
        (scale * clength) (trace_openings ! i)"
    proof -
      have opening_agrees:
        "\<forall>opn \<in> set (trace_openings ! i).
          opening_index opn < scale * clength \<and>
          trace_table ! opening_index opn = opening_value opn"
      proof
      fix opn
      assume opn_in: "opn \<in> set (trace_openings ! i)"
      have root: "opening_root opn = fr"
        using table_i opn_in unfolding partial_authenticated_table_def
        by blast
      have len: "opening_length opn = length trace_table"
        using table_i opn_in len_table
        unfolding partial_authenticated_table_def by simp
      have auth: "authenticated_opening_in final_state opn"
        using table_i opn_in unfolding partial_authenticated_table_def
        by blast
      have agreement:
        "opening_index opn < length trace_table \<and>
          trace_table ! opening_index opn = opening_value opn"
        by (rule merkle_bound_table_agrees_with_authenticated_opening_if_clean
            [OF bind table_pow auth root len clean])
      then show
        "opening_index opn < scale * clength \<and>
          trace_table ! opening_index opn = opening_value opn"
        using len_table by simp
      qed
      show ?thesis
        unfolding table_agrees_with_authenticated_openings_def
        using len_table opening_agrees by simp
    qed
  qed
  show ?thesis
    unfolding partial_trace_table_candidate_def
    using len_table len_openings agrees by simp
qed

lemma accepted_bound_composition_table_partial_candidate_if_clean:
  assumes bind:
      "merkle_root_binds_table composition_root composition_table
        final_state"
    and len_table: "length composition_table = scale * clength"
    and partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) composition_root query_idxs
        composition_openings"
    and clean: "\<not> hash_map_output_collision final_state"
  shows
    "partial_composition_table_candidate composition_table
      composition_openings"
proof -
  obtain n where len_pow: "clength * scale = 2 ^ n"
    using eval_domain_length_power by blast
  have table_pow: "length composition_table = 2 ^ n"
    using len_table len_pow by (simp add: mult.commute)
  have len_openings: "length composition_openings = rounds"
    using partial
    unfolding accepted_with_partial_composition_openings_def by blast
  have agrees:
    "\<And>i. i < rounds \<Longrightarrow>
      table_agrees_with_authenticated_openings composition_table
        (scale * clength) (composition_openings ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have table_i:
      "partial_authenticated_table composition_root (scale * clength)
        (composition_openings ! i) final_state"
      using partial i_bound
      unfolding accepted_with_partial_composition_openings_def by blast
    show
      "table_agrees_with_authenticated_openings composition_table
        (scale * clength) (composition_openings ! i)"
    proof -
      have opening_agrees:
        "\<forall>opn \<in> set (composition_openings ! i).
          opening_index opn < scale * clength \<and>
          composition_table ! opening_index opn = opening_value opn"
      proof
        fix opn
        assume opn_in: "opn \<in> set (composition_openings ! i)"
        have root: "opening_root opn = composition_root"
          using table_i opn_in unfolding partial_authenticated_table_def
          by blast
        have len: "opening_length opn = length composition_table"
          using table_i opn_in len_table
          unfolding partial_authenticated_table_def by simp
        have auth: "authenticated_opening_in final_state opn"
          using table_i opn_in unfolding partial_authenticated_table_def
          by blast
        have agreement:
          "opening_index opn < length composition_table \<and>
            composition_table ! opening_index opn = opening_value opn"
          by (rule merkle_bound_table_agrees_with_authenticated_opening_if_clean
              [OF bind table_pow auth root len clean])
        then show
          "opening_index opn < scale * clength \<and>
            composition_table ! opening_index opn = opening_value opn"
          using len_table by simp
      qed
      show ?thesis
        unfolding table_agrees_with_authenticated_openings_def
        using len_table opening_agrees by simp
    qed
  qed
  show ?thesis
    unfolding partial_composition_table_candidate_def
    using len_table len_openings agrees by simp
qed

definition partial_merkle_inconsistency_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "partial_merkle_inconsistency_bad s out \<longleftrightarrow>
    accepted out \<and>
    (\<exists>result final_state opn opn'.
      out = Some (result, final_state) \<and>
      authenticated_opening_in final_state opn \<and>
      authenticated_opening_in final_state opn' \<and>
      opening_root opn = opening_root opn' \<and>
      opening_length opn = opening_length opn' \<and>
      opening_index opn = opening_index opn' \<and>
      opening_value opn \<noteq> opening_value opn')"

lemma partial_trace_openings_inconsistent_bad_imp_partial_merkle_inconsistency_bad:
  assumes bad: "partial_trace_openings_inconsistent_bad s out"
  shows "partial_merkle_inconsistency_bad s out"
proof -
  obtain fr query_idxs trace_openings result final_state i opn opn' where
    out: "out = Some (result, final_state)"
    and partial:
      "accepted_with_partial_trace_openings s out fr query_idxs trace_openings"
    and i_bound: "i < rounds"
    and opn_in: "opn \<in> set (trace_openings ! i)"
    and opn'_in: "opn' \<in> set (trace_openings ! i)"
    and same_index: "opening_index opn = opening_index opn'"
    and diff_value: "opening_value opn \<noteq> opening_value opn'"
    using bad unfolding partial_trace_openings_inconsistent_bad_def by blast
  have table:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! i) final_state"
  proof -
    obtain result' final_state' where
      partial_out: "out = Some (result', final_state')"
      and tables:
        "\<forall>i < rounds.
          partial_authenticated_table fr (scale * clength)
            (trace_openings ! i) final_state'"
      using partial unfolding accepted_with_partial_trace_openings_def
      by auto
    have final_state_eq: "final_state' = final_state"
      using out partial_out by simp
    show ?thesis
      using tables i_bound unfolding final_state_eq by simp
  qed
  have opn_auth: "authenticated_opening_in final_state opn"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have opn'_auth: "authenticated_opening_in final_state opn'"
    using table opn'_in unfolding partial_authenticated_table_def by blast
  have same_root: "opening_root opn = opening_root opn'"
  proof -
    have root_opn: "opening_root opn = fr"
      using table opn_in unfolding partial_authenticated_table_def by simp
    have root_opn': "opening_root opn' = fr"
      using table opn'_in unfolding partial_authenticated_table_def by simp
    show ?thesis
      using root_opn root_opn' by simp
  qed
  have same_length: "opening_length opn = opening_length opn'"
  proof -
    have length_opn: "opening_length opn = scale * clength"
      using table opn_in unfolding partial_authenticated_table_def by simp
    have length_opn': "opening_length opn' = scale * clength"
      using table opn'_in unfolding partial_authenticated_table_def by simp
    show ?thesis
      using length_opn length_opn' by simp
  qed
  show ?thesis
    unfolding partial_merkle_inconsistency_bad_def
    using partial out opn_auth opn'_auth same_root same_length same_index
      diff_value
    unfolding accepted_with_partial_trace_openings_def
    by blast
qed

lemma partial_merkle_inconsistency_bad_imp_hash_map_output_collision_bad:
  assumes "partial_merkle_inconsistency_bad s out"
  shows "hash_map_output_collision_bad s out"
proof -
  obtain result final_state opn opn' where
    out: "out = Some (result, final_state)"
    and first: "authenticated_opening_in final_state opn"
    and second: "authenticated_opening_in final_state opn'"
    and same_root: "opening_root opn = opening_root opn'"
    and same_length: "opening_length opn = opening_length opn'"
    and same_index: "opening_index opn = opening_index opn'"
    and different_value:
      "opening_value opn \<noteq> opening_value opn'"
    using assms unfolding partial_merkle_inconsistency_bad_def by blast
  have collision: "hash_map_output_collision final_state"
    by (rule inconsistent_authenticated_openings_imp_hash_collision[
          OF first second same_root same_length same_index different_value])
  show ?thesis
    unfolding hash_map_output_collision_bad_def accepted_def
    using out collision by simp
  qed

lemma partial_trace_openings_inconsistent_bad_imp_hash_map_output_collision_bad:
  assumes "partial_trace_openings_inconsistent_bad s out"
  shows "hash_map_output_collision_bad s out"
  by (rule partial_merkle_inconsistency_bad_imp_hash_map_output_collision_bad)
    (rule partial_trace_openings_inconsistent_bad_imp_partial_merkle_inconsistency_bad
      [OF assms])

lemma partial_trace_openings_inconsistent_bad_mono_hash_map_output_collision_bad:
  "wp_event verify_monad (partial_trace_openings_inconsistent_bad s) s \<le>
    wp_event verify_monad (hash_map_output_collision_bad s) s"
  by (rule wp_event_mono)
    (rule partial_trace_openings_inconsistent_bad_imp_hash_map_output_collision_bad)

lemma partial_merkle_inconsistency_bad_mono_hash_map_output_collision_bad:
  "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le>
    wp_event verify_monad (hash_map_output_collision_bad s) s"
  by (rule wp_event_mono)
    (rule partial_merkle_inconsistency_bad_imp_hash_map_output_collision_bad)

lemma partial_trace_openings_inconsistent_bad_bound_from_hash_map_output_collision:
  fixes H :: prob
  assumes "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows "wp_event verify_monad (partial_trace_openings_inconsistent_bad s) s \<le>
    H"
  by (rule order_trans
      [OF partial_trace_openings_inconsistent_bad_mono_hash_map_output_collision_bad
        assms])

lemma partial_merkle_inconsistency_bad_bound_from_hash_map_output_collision:
  fixes H :: prob
  assumes "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> H"
  by (rule order_trans
      [OF partial_merkle_inconsistency_bad_mono_hash_map_output_collision_bad
        assms])

lemma partial_merkle_inconsistency_bad_imp_accepted:
  assumes "partial_merkle_inconsistency_bad s out"
  shows "accepted out"
  using assms unfolding partial_merkle_inconsistency_bad_def by simp

lemma accepted_with_partial_trace_openings_candidate_if_no_partial_merkle_bad:
  assumes partial:
      "accepted_with_partial_trace_openings s (Some (result, final_state))
        fr query_idxs trace_openings"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
  shows "\<exists>trace_table.
    partial_trace_table_candidate trace_table trace_openings"
proof -
  have len_openings: "length trace_openings = rounds"
    using partial unfolding accepted_with_partial_trace_openings_def by blast
  have table:
    "\<And>i. i < rounds \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
    using partial unfolding accepted_with_partial_trace_openings_def by blast
  have accepted_out: "accepted (Some (result, final_state))"
    by (rule accepted_with_partial_trace_openings_imp_accepted[OF partial])
  have idx_bound:
    "\<And>opn. opn \<in> set (List.concat trace_openings) \<Longrightarrow>
      opening_index opn < scale * clength"
  proof -
    fix opn
    assume opn_in: "opn \<in> set (List.concat trace_openings)"
    then obtain openings where openings_in: "openings \<in> set trace_openings"
      and opn_openings: "opn \<in> set openings"
      by auto
    then obtain i where i_bound: "i < length trace_openings"
      and openings_eq: "trace_openings ! i = openings"
      by (meson in_set_conv_nth)
    have table_i:
      "partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
      using table i_bound len_openings by simp
    have auth: "authenticated_opening_in final_state opn"
      using table_i opn_openings unfolding openings_eq
        partial_authenticated_table_def by blast
    have len: "opening_length opn = scale * clength"
      using table_i opn_openings unfolding openings_eq
        partial_authenticated_table_def by blast
    show "opening_index opn < scale * clength"
      using auth len unfolding authenticated_opening_in_def by simp
  qed
  have consistent:
    "\<And>opn opn'. opn \<in> set (List.concat trace_openings) \<Longrightarrow>
      opn' \<in> set (List.concat trace_openings) \<Longrightarrow>
      opening_index opn = opening_index opn' \<Longrightarrow>
      opening_value opn = opening_value opn'"
  proof (rule ccontr)
    fix opn opn'
    assume opn_in: "opn \<in> set (List.concat trace_openings)"
      and opn'_in: "opn' \<in> set (List.concat trace_openings)"
      and same_index: "opening_index opn = opening_index opn'"
      and neq: "opening_value opn \<noteq> opening_value opn'"
    obtain openings where openings_in: "openings \<in> set trace_openings"
      and opn_openings: "opn \<in> set openings"
      using opn_in by auto
    then obtain i where i_bound: "i < length trace_openings"
      and openings_eq: "trace_openings ! i = openings"
      by (meson in_set_conv_nth)
    obtain openings' where openings'_in: "openings' \<in> set trace_openings"
      and opn'_openings: "opn' \<in> set openings'"
      using opn'_in by auto
    then obtain j where j_bound: "j < length trace_openings"
      and openings'_eq: "trace_openings ! j = openings'"
      by (meson in_set_conv_nth)
    have table_i:
      "partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
      using table i_bound len_openings by simp
    have table_j:
      "partial_authenticated_table fr (scale * clength)
        (trace_openings ! j) final_state"
      using table j_bound len_openings by simp
    have auth: "authenticated_opening_in final_state opn"
      using table_i opn_openings unfolding openings_eq
        partial_authenticated_table_def by blast
    have auth': "authenticated_opening_in final_state opn'"
      using table_j opn'_openings unfolding openings'_eq
        partial_authenticated_table_def by blast
    have root: "opening_root opn = opening_root opn'"
      using table_i table_j opn_openings opn'_openings
      unfolding openings_eq openings'_eq partial_authenticated_table_def
      by auto
    have len: "opening_length opn = opening_length opn'"
      using table_i table_j opn_openings opn'_openings
      unfolding openings_eq openings'_eq partial_authenticated_table_def
      by auto
    have bad:
      "partial_merkle_inconsistency_bad s (Some (result, final_state))"
      unfolding partial_merkle_inconsistency_bad_def
      by (intro conjI exI[of _ result] exI[of _ final_state]
          exI[of _ opn] exI[of _ opn'])
        (use accepted_out auth auth' root len same_index neq in simp_all)
    then show False using no_bad by contradiction
  qed
  obtain trace_table where agrees_all:
    "table_agrees_with_authenticated_openings trace_table (scale * clength)
      (List.concat trace_openings)"
    using table_agrees_with_authenticated_openings_consistent_exists
        [OF idx_bound consistent]
    by blast
  have agrees:
    "\<And>i. i < rounds \<Longrightarrow>
      table_agrees_with_authenticated_openings trace_table
        (scale * clength) (trace_openings ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have "set (trace_openings ! i) \<subseteq>
        set (List.concat trace_openings)"
    proof
      fix opn
      assume opn_in: "opn \<in> set (trace_openings ! i)"
      have "trace_openings ! i \<in> set trace_openings"
        using i_bound len_openings by (intro nth_mem) simp
      then show "opn \<in> set (List.concat trace_openings)"
        using opn_in by auto
    qed
    then show
      "table_agrees_with_authenticated_openings trace_table
        (scale * clength) (trace_openings ! i)"
      by (rule table_agrees_with_authenticated_openings_subset
          [OF agrees_all])
  qed
  have len_table: "length trace_table = scale * clength"
    using agrees_all
    unfolding table_agrees_with_authenticated_openings_def by simp
  have "partial_trace_table_candidate trace_table trace_openings"
    unfolding partial_trace_table_candidate_def
    using len_table len_openings agrees by simp
  then show ?thesis by blast
qed

lemma accepted_with_partial_composition_openings_candidate_if_no_partial_merkle_bad:
  assumes partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) composition_root query_idxs
        composition_openings"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
  shows "\<exists>composition_table.
    partial_composition_table_candidate composition_table composition_openings"
proof -
  have len_openings: "length composition_openings = rounds"
    using partial
    unfolding accepted_with_partial_composition_openings_def by blast
  have table:
    "\<And>i. i < rounds \<Longrightarrow>
      partial_authenticated_table composition_root (scale * clength)
        (composition_openings ! i) final_state"
    using partial
    unfolding accepted_with_partial_composition_openings_def by blast
  have accepted_out: "accepted (Some (result, final_state))"
    by (rule accepted_with_partial_composition_openings_imp_accepted
        [OF partial])
  have idx_bound:
    "\<And>opn. opn \<in> set (List.concat composition_openings) \<Longrightarrow>
      opening_index opn < scale * clength"
  proof -
    fix opn
    assume opn_in: "opn \<in> set (List.concat composition_openings)"
    then obtain openings where openings_in:
        "openings \<in> set composition_openings"
      and opn_openings: "opn \<in> set openings"
      by auto
    then obtain i where i_bound: "i < length composition_openings"
      and openings_eq: "composition_openings ! i = openings"
      by (meson in_set_conv_nth)
    have table_i:
      "partial_authenticated_table composition_root (scale * clength)
        (composition_openings ! i) final_state"
      using table i_bound len_openings by simp
    have auth: "authenticated_opening_in final_state opn"
      using table_i opn_openings unfolding openings_eq
        partial_authenticated_table_def by blast
    have len: "opening_length opn = scale * clength"
      using table_i opn_openings unfolding openings_eq
        partial_authenticated_table_def by blast
    show "opening_index opn < scale * clength"
      using auth len unfolding authenticated_opening_in_def by simp
  qed
  have consistent:
    "\<And>opn opn'. opn \<in> set (List.concat composition_openings) \<Longrightarrow>
      opn' \<in> set (List.concat composition_openings) \<Longrightarrow>
      opening_index opn = opening_index opn' \<Longrightarrow>
      opening_value opn = opening_value opn'"
  proof (rule ccontr)
    fix opn opn'
    assume opn_in: "opn \<in> set (List.concat composition_openings)"
      and opn'_in: "opn' \<in> set (List.concat composition_openings)"
      and same_index: "opening_index opn = opening_index opn'"
      and neq: "opening_value opn \<noteq> opening_value opn'"
    obtain openings where openings_in: "openings \<in> set composition_openings"
      and opn_openings: "opn \<in> set openings"
      using opn_in by auto
    then obtain i where i_bound: "i < length composition_openings"
      and openings_eq: "composition_openings ! i = openings"
      by (meson in_set_conv_nth)
    obtain openings' where openings'_in:
        "openings' \<in> set composition_openings"
      and opn'_openings: "opn' \<in> set openings'"
      using opn'_in by auto
    then obtain j where j_bound: "j < length composition_openings"
      and openings'_eq: "composition_openings ! j = openings'"
      by (meson in_set_conv_nth)
    have table_i:
      "partial_authenticated_table composition_root (scale * clength)
        (composition_openings ! i) final_state"
      using table i_bound len_openings by simp
    have table_j:
      "partial_authenticated_table composition_root (scale * clength)
        (composition_openings ! j) final_state"
      using table j_bound len_openings by simp
    have auth: "authenticated_opening_in final_state opn"
      using table_i opn_openings unfolding openings_eq
        partial_authenticated_table_def by blast
    have auth': "authenticated_opening_in final_state opn'"
      using table_j opn'_openings unfolding openings'_eq
        partial_authenticated_table_def by blast
    have root: "opening_root opn = opening_root opn'"
      using table_i table_j opn_openings opn'_openings
      unfolding openings_eq openings'_eq partial_authenticated_table_def
      by auto
    have len: "opening_length opn = opening_length opn'"
      using table_i table_j opn_openings opn'_openings
      unfolding openings_eq openings'_eq partial_authenticated_table_def
      by auto
    have bad:
      "partial_merkle_inconsistency_bad s (Some (result, final_state))"
      unfolding partial_merkle_inconsistency_bad_def
      by (intro conjI exI[of _ result] exI[of _ final_state]
          exI[of _ opn] exI[of _ opn'])
        (use accepted_out auth auth' root len same_index neq in simp_all)
    then show False using no_bad by contradiction
  qed
  obtain composition_table where agrees_all:
    "table_agrees_with_authenticated_openings composition_table
      (scale * clength) (List.concat composition_openings)"
    using table_agrees_with_authenticated_openings_consistent_exists
        [OF idx_bound consistent]
    by blast
  have agrees:
    "\<And>i. i < rounds \<Longrightarrow>
      table_agrees_with_authenticated_openings composition_table
        (scale * clength) (composition_openings ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have "set (composition_openings ! i) \<subseteq>
        set (List.concat composition_openings)"
    proof
      fix opn
      assume opn_in: "opn \<in> set (composition_openings ! i)"
      have "composition_openings ! i \<in> set composition_openings"
        using i_bound len_openings by (intro nth_mem) simp
      then show "opn \<in> set (List.concat composition_openings)"
        using opn_in by auto
    qed
    then show
      "table_agrees_with_authenticated_openings composition_table
        (scale * clength) (composition_openings ! i)"
      by (rule table_agrees_with_authenticated_openings_subset
          [OF agrees_all])
  qed
  have len_table: "length composition_table = scale * clength"
    using agrees_all
    unfolding table_agrees_with_authenticated_openings_def by simp
  have "partial_composition_table_candidate composition_table
      composition_openings"
    unfolding partial_composition_table_candidate_def
    using len_table len_openings agrees by simp
  then show ?thesis by blast
qed

lemma accepted_with_partial_initial_openings_candidates_if_no_partial_merkle_bad:
  assumes partial:
      "accepted_with_partial_initial_openings s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
  shows "\<exists>trace_table composition_table.
    partial_trace_table_candidate trace_table trace_openings \<and>
    partial_composition_table_candidate composition_table
      composition_openings"
proof -
  have trace_partial:
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr trace_query_idxs trace_openings"
    using accepted_with_partial_initial_openings_shapes(3)[OF partial] .
  have comp_partial:
    "accepted_with_partial_composition_openings s
      (Some (result, final_state)) (hd composition_fri_roots)
      composition_query_idxs composition_openings"
    using accepted_with_partial_initial_openings_shapes(4)[OF partial] .
  obtain trace_table where trace_candidate:
    "partial_trace_table_candidate trace_table trace_openings"
    using accepted_with_partial_trace_openings_candidate_if_no_partial_merkle_bad
        [OF trace_partial no_bad]
    by blast
  obtain composition_table where comp_candidate:
    "partial_composition_table_candidate composition_table
      composition_openings"
    using
      accepted_with_partial_composition_openings_candidate_if_no_partial_merkle_bad
        [OF comp_partial no_bad]
    by blast
  show ?thesis
    using trace_candidate comp_candidate by blast
qed

lemma verify_monad_partial_initial_candidates_or_partial_merkle_bad:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
  shows
    "partial_merkle_inconsistency_bad s (Some (result, final_state)) \<or>
      (\<exists>trace_query_idxs trace_openings composition_query_idxs
          composition_openings trace_table composition_table.
        accepted_with_partial_initial_openings s
          (Some (result, final_state)) fr f_fri_roots f_final as dg
          composition_fri_roots final trace_query_idxs trace_openings
          composition_query_idxs composition_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings)"
proof (cases
    "partial_merkle_inconsistency_bad s (Some (result, final_state))")
  case True
  then show ?thesis by simp
next
  case False
  from verify_monad_accepted_with_partial_initial_openings
      [OF outcome header comp_nonempty]
  obtain trace_query_idxs trace_openings composition_query_idxs
      composition_openings where partial:
    "accepted_with_partial_initial_openings s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings"
    by blast
  obtain trace_table composition_table where candidates:
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    using accepted_with_partial_initial_openings_candidates_if_no_partial_merkle_bad
        [OF partial False]
    by blast
  show ?thesis
    using partial candidates by blast
qed

lemma partial_merkle_inconsistency_bad_mono_accepted:
  "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le>
    wp_event verify_monad accepted s"
  by (rule wp_event_mono)
    (rule partial_merkle_inconsistency_bad_imp_accepted)

end

end
