(*  Title:      Stark/Soundness_Merkle_Prefix_Target.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Merkle_Prefix_Target
  imports
    Staged_Security_Experiment_Composition_Tree_Output
    Staged_Security_Experiment_Composition_Query_Current_Path
    Soundness_Conceptual_Table
    Soundness_FRI_Layer_Merkle
begin

text \<open>
  Prefix-fixed target sets for pulling authenticated Merkle paths back through
  verifier hashing.  The first fresh node on a path targets either the
  committed root or a child already named by a Merkle-node key in the prefix
  hash map.
\<close>

context soundness
begin

definition hash_map_merkle_child_values
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f set"
where
  "hash_map_merkle_child_values s =
    {y. \<exists>x z. fmlookup (HashMap s) x = Some z \<and>
      merkle_node_child_output_relation x y}"

definition merkle_prefix_path_targets
  :: "'f set \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> 'f set"
where
  "merkle_prefix_path_targets roots s =
    roots \<union> hash_map_merkle_child_values s"


lemma hash_map_merkle_child_values_subset_images:
  "hash_map_merkle_child_values s \<subseteq>
    Set.image
      (\<lambda>x. case x of MerkleNode l r \<Rightarrow> l | _ \<Rightarrow> 0)
      (fmdom' (HashMap s)) \<union>
    Set.image
      (\<lambda>x. case x of MerkleNode l r \<Rightarrow> r | _ \<Rightarrow> 0)
      (fmdom' (HashMap s))"
  unfolding hash_map_merkle_child_values_def
    merkle_node_child_output_relation_def
proof
  fix y
  assume
    "y \<in> {y. \<exists>x z.
      fmlookup (HashMap s) x = Some z \<and>
      (\<exists>w. x = MerkleNode y w \<or> x = MerkleNode w y)}"
  then obtain x z w where
    lookup: "fmlookup (HashMap s) x = Some z"
    and shape: "x = MerkleNode y w \<or> x = MerkleNode w y"
    by blast
  have dom: "x \<in> fmdom' (HashMap s)"
    using lookup by (simp add: fmlookup_dom'_iff)
  from shape show
    "y \<in>
      Set.image
        (\<lambda>x. case x of MerkleNode l r \<Rightarrow> l | _ \<Rightarrow> 0)
        (fmdom' (HashMap s)) \<union>
      Set.image
        (\<lambda>x. case x of MerkleNode l r \<Rightarrow> r | _ \<Rightarrow> 0)
        (fmdom' (HashMap s))"
  proof
    assume left: "x = MerkleNode y w"
    have node_dom: "MerkleNode y w \<in> fmdom' (HashMap s)"
      using dom left by simp
    have
      "(case MerkleNode y w of
          MerkleNode l r \<Rightarrow> l | _ \<Rightarrow> 0) \<in>
        Set.image
          (\<lambda>x. case x of MerkleNode l r \<Rightarrow> l | _ \<Rightarrow> 0)
          (fmdom' (HashMap s))"
      by (rule imageI[OF node_dom])
    then show ?thesis by simp
  next
    assume right: "x = MerkleNode w y"
    have node_dom: "MerkleNode w y \<in> fmdom' (HashMap s)"
      using dom right by simp
    have
      "(case MerkleNode w y of
          MerkleNode l r \<Rightarrow> r | _ \<Rightarrow> 0) \<in>
        Set.image
          (\<lambda>x. case x of MerkleNode l r \<Rightarrow> r | _ \<Rightarrow> 0)
          (fmdom' (HashMap s))"
      by (rule imageI[OF node_dom])
    then show ?thesis by simp
  qed
qed
lemma finite_hash_map_merkle_child_values[simp]:
  "finite (hash_map_merkle_child_values s)"
  by (rule finite_subset[OF hash_map_merkle_child_values_subset_images])
    simp

lemma card_hash_map_merkle_child_values_le:
  "card (hash_map_merkle_child_values s) \<le>
    2 * card (fmdom' (HashMap s))"
proof -
  let ?D = "fmdom' (HashMap s)"
  let ?L =
    "Set.image
      (\<lambda>x. case x of MerkleNode l r \<Rightarrow> l | _ \<Rightarrow> 0) ?D"
  let ?R =
    "Set.image
      (\<lambda>x. case x of MerkleNode l r \<Rightarrow> r | _ \<Rightarrow> 0) ?D"
  have "card (hash_map_merkle_child_values s) \<le> card (?L \<union> ?R)"
    by (rule card_mono)
      (simp_all add: hash_map_merkle_child_values_subset_images)
  also have "... \<le> card ?L + card ?R"
    by (rule card_Un_le)
  also have "... \<le> card ?D + card ?D"
    by (rule add_mono; rule card_image_le; simp)
  also have "... = 2 * card ?D"
    by simp
  finally show ?thesis .
qed

lemma finite_merkle_prefix_path_targets[simp]:
  assumes "finite roots"
  shows "finite (merkle_prefix_path_targets roots s)"
  using assms unfolding merkle_prefix_path_targets_def by simp

lemma card_merkle_prefix_path_targets_le:
  assumes finite_roots: "finite roots"
  shows "card (merkle_prefix_path_targets roots s) \<le>
    card roots + 2 * card (fmdom' (HashMap s))"
proof -
  have "card (merkle_prefix_path_targets roots s) \<le>
      card roots + card (hash_map_merkle_child_values s)"
    unfolding merkle_prefix_path_targets_def
    by (rule card_Un_le)
  also have "... \<le> card roots + 2 * card (fmdom' (HashMap s))"
    by (rule add_left_mono[OF card_hash_map_merkle_child_values_le])
  finally show ?thesis .
qed


lemma inj_on_hash_map_outputs_if_no_collision:
  assumes clean: "\<not> hash_map_output_collision s"
  shows
    "inj_on (\<lambda>x. the (fmlookup (HashMap s) x))
      (fmdom' (HashMap s))"
  unfolding inj_on_def
proof (intro ballI impI)
  fix x y
  assume x_dom: "x \<in> fmdom' (HashMap s)"
    and y_dom: "y \<in> fmdom' (HashMap s)"
    and outputs:
      "the (fmlookup (HashMap s) x) =
       the (fmlookup (HashMap s) y)"
  from x_dom obtain x_out where
    x_lookup: "fmlookup (HashMap s) x = Some x_out"
    by (cases "fmlookup (HashMap s) x")
      (auto simp: fmlookup_dom'_iff)
  from y_dom obtain y_out where
    y_lookup: "fmlookup (HashMap s) y = Some y_out"
    by (cases "fmlookup (HashMap s) y")
      (auto simp: fmlookup_dom'_iff)
  have out_eq: "x_out = y_out"
    using outputs x_lookup y_lookup by simp
  show "x = y"
  proof (rule ccontr)
    assume "x \<noteq> y"
    then have "hash_map_output_collision s"
      unfolding hash_map_output_collision_def
      using x_lookup y_lookup out_eq by blast
    then show False
      using clean by simp
  qed
qed

lemma card_fmdom_le_hash_map_output_values_if_no_collision:
  assumes clean: "\<not> hash_map_output_collision s"
  shows
    "card (fmdom' (HashMap s)) \<le>
      card (hash_map_output_values s)"
proof -
  have inj:
    "inj_on (\<lambda>x. the (fmlookup (HashMap s) x))
      (fmdom' (HashMap s))"
    by (rule inj_on_hash_map_outputs_if_no_collision[OF clean])
  have
    "card (hash_map_output_values s) =
      card
        (Set.image (\<lambda>x. the (fmlookup (HashMap s) x))
          (fmdom' (HashMap s)))"
    unfolding hash_map_output_values_alt_def by simp
  also have "... = card (fmdom' (HashMap s))"
    by (rule card_image[OF inj])
  finally show ?thesis by simp
qed

lemma card_merkle_prefix_path_targets_le_if_no_collision:
  assumes finite_roots: "finite roots"
    and clean: "\<not> hash_map_output_collision s"
  shows "card (merkle_prefix_path_targets roots s) \<le>
    card roots + 2 * card (hash_map_output_values s)"
proof -
  have "card (merkle_prefix_path_targets roots s) \<le>
      card roots + 2 * card (fmdom' (HashMap s))"
    by (rule card_merkle_prefix_path_targets_le[OF finite_roots])
  also have "... \<le> card roots + 2 * card (hash_map_output_values s)"
    using card_fmdom_le_hash_map_output_values_if_no_collision[OF clean]
    by simp
  finally show ?thesis .
qed
lemma merkle_prefix_path_targets_mono:
  assumes "A \<subseteq> B"
  shows "merkle_prefix_path_targets A s \<subseteq>
    merkle_prefix_path_targets B s"
  using assms unfolding merkle_prefix_path_targets_def by blast

lemma merkle_path_bound_pullback_or_prefix_target_hit:
  assumes ext: "s \<le> t"
    and bound: "merkle_path_bound rt len idx v path t"
  shows
    "merkle_path_bound rt len idx v path s \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {rt} s) s t"
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
        (merkle_prefix_path_targets {rt} s) s t"
      unfolding hash_map_new_output_hit_def merkle_prefix_path_targets_def
      using lookup_t by auto
    then show ?thesis by simp
  next
    case (Some old)
    have lookup_t_old:
      "fmlookup (HashMap t) (MerkleLeaf v) = Some old"
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
    show ?thesis
    proof (cases "fmlookup (HashMap s) (MerkleNode child sibling)")
      case None
      then have
        "hash_map_new_output_hit
          (merkle_prefix_path_targets {rt} s) s t"
        unfolding hash_map_new_output_hit_def merkle_prefix_path_targets_def
        using lookup_t by auto
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
           (merkle_prefix_path_targets {child} s) s t"
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
            (merkle_prefix_path_targets {child} s) s t"
        have child_in:
          "child \<in> hash_map_merkle_child_values s"
          unfolding hash_map_merkle_child_values_def
            merkle_node_child_output_relation_def
          using Some by auto
        have subset:
          "merkle_prefix_path_targets {child} s \<subseteq>
            merkle_prefix_path_targets {rt} s"
          unfolding merkle_prefix_path_targets_def
          using child_in by blast
        have
          "hash_map_new_output_hit
            (merkle_prefix_path_targets {rt} s) s t"
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
    show ?thesis
    proof (cases "fmlookup (HashMap s) (MerkleNode sibling child)")
      case None
      then have
        "hash_map_new_output_hit
          (merkle_prefix_path_targets {rt} s) s t"
        unfolding hash_map_new_output_hit_def merkle_prefix_path_targets_def
        using lookup_t by auto
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
           (merkle_prefix_path_targets {child} s) s t"
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
            (merkle_prefix_path_targets {child} s) s t"
        have child_in:
          "child \<in> hash_map_merkle_child_values s"
          unfolding hash_map_merkle_child_values_def
            merkle_node_child_output_relation_def
          using Some by auto
        have subset:
          "merkle_prefix_path_targets {child} s \<subseteq>
            merkle_prefix_path_targets {rt} s"
          unfolding merkle_prefix_path_targets_def
          using child_in by blast
        have
          "hash_map_new_output_hit
            (merkle_prefix_path_targets {rt} s) s t"
          by (rule hash_map_new_output_hit_subset[OF subset child_hit])
        then show ?thesis by simp
      qed
    qed
  qed
qed


lemma hash_map_new_output_hit_output_values_imp_collision:
  assumes ext: "s \<le> t"
    and hit: "hash_map_new_output_hit (hash_map_output_values s) s t"
  shows "hash_map_output_collision t"
proof -
  from hit obtain x y where
    fresh: "fmlookup (HashMap s) x = None"
    and lookup_t: "fmlookup (HashMap t) x = Some y"
    and y_old: "y \<in> hash_map_output_values s"
    unfolding hash_map_new_output_hit_def by blast
  from y_old obtain old_x where
    old_lookup_s: "fmlookup (HashMap s) old_x = Some y"
    unfolding hash_map_output_values_def by blast
  have old_lookup_t: "fmlookup (HashMap t) old_x = Some y"
    by (rule hash_extension_lookup[OF old_lookup_s ext])
  have neq: "x \<noteq> old_x"
    using fresh old_lookup_s by auto
  show ?thesis
    unfolding hash_map_output_collision_def
    using neq lookup_t old_lookup_t by blast
qed

lemma merkle_path_target_roots_subset_hash_map_output_values:
  assumes ext: "s \<le> t"
    and bound: "merkle_path_bound rt len idx v path s"
  shows
    "merkle_path_target_roots t rt len idx v path \<subseteq>
      hash_map_output_values s"
  using bound
proof (induction path arbitrary: rt len idx)
  case Nil
  have lookup_s: "fmlookup (HashMap s) (MerkleLeaf v) = Some rt"
    using Nil.prems by simp
  then have "rt \<in> hash_map_output_values s"
    by (rule hash_map_output_valuesI)
  then show ?case by simp
next
  case (Cons sibling path)
  show ?case
  proof (cases "idx < len div 2")
    case True
    from Cons.prems obtain child where
      child_s: "merkle_path_bound child (len div 2) idx v path s"
      and parent_s:
        "fmlookup (HashMap s) (MerkleNode child sibling) = Some rt"
      using True by auto
    have child_t: "merkle_path_bound child (len div 2) idx v path t"
      by (rule merkle_path_bound_mono[OF child_s ext])
    have child_root:
      "merkle_path_root_in_map t (len div 2) idx v path = Some child"
      by (rule merkle_path_bound_root_in_map[OF child_t])
    have root_old: "rt \<in> hash_map_output_values s"
      by (rule hash_map_output_valuesI[OF parent_s])
    have child_subset:
      "merkle_path_target_roots t child (len div 2) idx v path \<subseteq>
        hash_map_output_values s"
      by (rule Cons.IH[OF child_s])
    show ?thesis
      using True child_root root_old child_subset by auto
  next
    case False
    from Cons.prems obtain child where
      child_s:
        "merkle_path_bound child (len div 2) (idx - len div 2) v path s"
      and parent_s:
        "fmlookup (HashMap s) (MerkleNode sibling child) = Some rt"
      using False by auto
    have child_t:
      "merkle_path_bound child (len div 2) (idx - len div 2) v path t"
      by (rule merkle_path_bound_mono[OF child_s ext])
    have child_root:
      "merkle_path_root_in_map t (len div 2) (idx - len div 2) v path =
        Some child"
      by (rule merkle_path_bound_root_in_map[OF child_t])
    have root_old: "rt \<in> hash_map_output_values s"
      by (rule hash_map_output_valuesI[OF parent_s])
    have child_subset:
      "merkle_path_target_roots t child (len div 2)
          (idx - len div 2) v path \<subseteq>
        hash_map_output_values s"
      by (rule Cons.IH[OF child_s])
    show ?thesis
      using False child_root root_old child_subset by auto
  qed
qed

lemma merkle_path_target_hit_imp_collision_or_prefix_target_hit:
  assumes ext: "s \<le> t"
    and bound: "merkle_path_bound rt len idx v path t"
    and hit:
      "hash_map_new_output_hit
        (merkle_path_target_roots t rt len idx v path) s t"
  shows
    "hash_map_output_collision t \<or>
     hash_map_new_output_hit (merkle_prefix_path_targets {rt} s) s t"
proof -
  from merkle_path_bound_pullback_or_prefix_target_hit[OF ext bound]
  show ?thesis
  proof
    assume bound_s: "merkle_path_bound rt len idx v path s"
    have subset:
      "merkle_path_target_roots t rt len idx v path \<subseteq>
        hash_map_output_values s"
      by (rule merkle_path_target_roots_subset_hash_map_output_values
          [OF ext bound_s])
    have old_hit:
      "hash_map_new_output_hit (hash_map_output_values s) s t"
      by (rule hash_map_new_output_hit_subset[OF subset hit])
    have "hash_map_output_collision t"
      by (rule hash_map_new_output_hit_output_values_imp_collision
          [OF ext old_hit])
    then show ?thesis by simp
  next
    assume
      "hash_map_new_output_hit (merkle_prefix_path_targets {rt} s) s t"
    then show ?thesis by simp
  qed
qed

lemma authenticated_opening_target_hit_imp_collision_or_prefix_target_hit:
  assumes ext: "s \<le> t"
    and auth: "authenticated_opening_in t opening"
    and hit:
      "hash_map_new_output_hit
        (merkle_path_target_roots t
          (opening_root opening)
          (opening_length opening)
          (opening_index opening)
          (opening_value opening)
          (opening_path opening)) s t"
  shows
    "hash_map_output_collision t \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {opening_root opening} s) s t"
proof -
  have bound:
    "merkle_path_bound
      (opening_root opening)
      (opening_length opening)
      (opening_index opening)
      (opening_value opening)
      (opening_path opening) t"
    using auth unfolding authenticated_opening_in_def by simp
  show ?thesis
    by (rule merkle_path_target_hit_imp_collision_or_prefix_target_hit
        [OF ext bound hit])
qed
lemma authenticated_opening_agrees_with_prefix_conceptual_table_or_prefix_target_hit:
  assumes ext: "s \<le> t"
    and clean: "\<not> hash_map_output_collision s"
    and auth: "authenticated_opening_in t opening"
  shows
    "conceptual_table s (opening_root opening) (opening_length opening) !
        opening_index opening = opening_value opening \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {opening_root opening} s) s t"
proof -
  have bound_t:
    "merkle_path_bound
      (opening_root opening)
      (opening_length opening)
      (opening_index opening)
      (opening_value opening)
      (opening_path opening) t"
    using auth unfolding authenticated_opening_in_def by simp
  from merkle_path_bound_pullback_or_prefix_target_hit[OF ext bound_t]
  show ?thesis
  proof
    assume bound_s:
      "merkle_path_bound
        (opening_root opening)
        (opening_length opening)
        (opening_index opening)
        (opening_value opening)
        (opening_path opening) s"
    have auth_s: "authenticated_opening_in s opening"
      using auth bound_s unfolding authenticated_opening_in_def by simp
    have idx:
      "opening_index opening < opening_length opening"
      using auth unfolding authenticated_opening_in_def by simp
    have
      "conceptual_table s (opening_root opening) (opening_length opening) !
        opening_index opening = opening_value opening"
      by (rule
          conceptual_table_agrees_with_authenticated_opening
          [OF clean auth_s refl refl idx])
    then show ?thesis by simp
  next
    assume
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {opening_root opening} s) s t"
    then show ?thesis by simp
  qed
qed


lemma partial_authenticated_table_agrees_with_prefix_conceptual_table_or_prefix_target_hit:
  assumes ext: "s \<le> t"
    and clean: "\<not> hash_map_output_collision s"
    and partial: "partial_authenticated_table rt len openings t"
  shows
    "table_agrees_with_authenticated_openings
       (conceptual_table s rt len) len openings \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {rt} s) s t"
proof (cases
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {rt} s) s t")
  case True
  then show ?thesis by simp
next
  case False
  have agrees:
    "\<forall>opn \<in> set openings.
      opening_index opn < len \<and>
      conceptual_table s rt len ! opening_index opn =
        opening_value opn"
  proof (intro ballI conjI)
    fix opn
    assume opn_in: "opn \<in> set openings"
    have root: "opening_root opn = rt"
      using partial opn_in
      unfolding partial_authenticated_table_def by blast
    have len_eq: "opening_length opn = len"
      using partial opn_in
      unfolding partial_authenticated_table_def by blast
    have auth: "authenticated_opening_in t opn"
      using partial opn_in
      unfolding partial_authenticated_table_def by blast
    show "opening_index opn < len"
      using auth len_eq unfolding authenticated_opening_in_def by simp
    from
      authenticated_opening_agrees_with_prefix_conceptual_table_or_prefix_target_hit
        [OF ext clean auth]
    show
      "conceptual_table s rt len ! opening_index opn =
        opening_value opn"
      using False root len_eq by simp
  qed
  have
    "table_agrees_with_authenticated_openings
      (conceptual_table s rt len) len openings"
    unfolding table_agrees_with_authenticated_openings_def
    using agrees by simp
  then show ?thesis by simp
qed


lemma accepted_with_partial_trace_openings_agrees_with_prefix_conceptual_table_or_prefix_target_hit:
  assumes ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and partial:
      "accepted_with_partial_trace_openings initial_state
        (Some (result, final_state)) fr query_idxs trace_openings"
  shows
    "partial_trace_table_candidate
       (conceptual_table prefix_state fr (scale * clength))
       trace_openings \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {fr} prefix_state)
       prefix_state final_state"
proof (cases
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {fr} prefix_state)
      prefix_state final_state")
  case True
  then show ?thesis by simp
next
  case False
  have trace_openings_length: "length trace_openings = rounds"
    using partial
    unfolding accepted_with_partial_trace_openings_def by blast
  have agrees:
    "\<forall>i < rounds.
      table_agrees_with_authenticated_openings
        (conceptual_table prefix_state fr (scale * clength))
        (scale * clength) (trace_openings ! i)"
  proof (intro allI impI)
    fix i
    assume i_round: "i < rounds"
    have partial_i:
      "partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
      using partial i_round
      unfolding accepted_with_partial_trace_openings_def by blast
    from
      partial_authenticated_table_agrees_with_prefix_conceptual_table_or_prefix_target_hit
        [OF ext clean partial_i]
    show
      "table_agrees_with_authenticated_openings
        (conceptual_table prefix_state fr (scale * clength))
        (scale * clength) (trace_openings ! i)"
      using False by simp
  qed
  have
    "partial_trace_table_candidate
      (conceptual_table prefix_state fr (scale * clength))
      trace_openings"
    unfolding partial_trace_table_candidate_def
    using trace_openings_length agrees by simp
  then show ?thesis by simp
qed


lemma fri_layer_chunk_authenticated_agrees_with_prefix_conceptual_table_or_prefix_target_hit:
  assumes ext: "s \<le> t"
    and clean: "\<not> hash_map_output_collision s"
    and authenticated:
      "fri_layer_chunk_authenticated rt len idx chunk t"
  shows
    "(\<exists>xp xp_path xn xn_path.
      fri_layer_opening_chunk len xp xp_path xn xn_path chunk \<and>
      conceptual_table s rt len ! idx = xp \<and>
      conceptual_table s rt len ! fri_sibling_index len idx = xn) \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {rt} s) s t"
proof -
  from authenticated obtain xp xp_path xn xn_path where
    chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and base_auth:
      "authenticated_opening_in t
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr>"
    and sibling_auth:
      "authenticated_opening_in t
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path\<rparr>"
    unfolding fri_layer_chunk_authenticated_def by blast
  let ?hit =
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {rt} s) s t"
  show ?thesis
  proof (cases ?hit)
    case True
    then show ?thesis by simp
  next
    case False
    have base:
      "conceptual_table s rt len ! idx = xp"
      using
        authenticated_opening_agrees_with_prefix_conceptual_table_or_prefix_target_hit
          [OF ext clean base_auth]
        False
      by simp
    have sibling:
      "conceptual_table s rt len ! fri_sibling_index len idx = xn"
      using
        authenticated_opening_agrees_with_prefix_conceptual_table_or_prefix_target_hit
          [OF ext clean sibling_auth]
        False
      by simp
    show ?thesis
      using chunk base sibling by blast
  qed
qed

end

end
