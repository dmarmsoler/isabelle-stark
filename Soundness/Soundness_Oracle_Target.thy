(*  Title:      Stark/Soundness_Oracle_Target.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Oracle_Target
  imports Soundness_FRI
begin

section \<open>Oracle Budgets and Security Experiment\<close>

text \<open>Random-oracle target-hit events and target-budget calculus.\<close>

context soundness
begin

definition hash_map_output_collision_bound
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "hash_map_output_collision_bound s \<longleftrightarrow>
      wp_event verify_monad (hash_map_output_collision_bad s) s \<le>
        merkle_binding_error"

definition hash_map_new_output_collision
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "hash_map_new_output_collision initial final \<longleftrightarrow>
      \<not> hash_map_output_collision initial \<and>
      hash_map_output_collision final"

definition hash_new_collision_event
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('r \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "hash_new_collision_event s out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (_, t) \<Rightarrow> hash_map_new_output_collision s t)"

definition hash_map_new_output_hit
  :: "'f set \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "hash_map_new_output_hit B initial final \<longleftrightarrow>
      (\<exists>x y.
        fmlookup (HashMap initial) x = None \<and>
        fmlookup (HashMap final) x = Some y \<and>
        y \<in> B)"

definition hash_new_output_hit_event
  :: "'f set \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('r \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "hash_new_output_hit_event B s out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (_, t) \<Rightarrow> hash_map_new_output_hit B s t)"

lemma hash_map_new_output_hit_subset:
  assumes subset: "A \<subseteq> B"
    and hit: "hash_map_new_output_hit A s t"
  shows "hash_map_new_output_hit B s t"
  using subset hit unfolding hash_map_new_output_hit_def by blast

lemma protocol_merkle_created_tree_pullback_or_new_output_hit:
  assumes created: "protocol_merkle.created_tree xs tree t"
    and ext: "s \<le> t"
  shows
    "protocol_merkle.created_tree xs tree s \<or>
      hash_map_new_output_hit (set_tree tree) s t"
  using created ext
proof (induction "length xs" arbitrary: xs tree s t rule: less_induct)
  case less
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      using less.prems
      by (simp add: protocol_merkle.created_tree.simps)
  next
    case (Cons x rest)
    have xs_cons: "xs = x # rest"
      using Cons by simp
    show ?thesis
    proof (cases rest)
      case Nil
      then obtain h where
        tree_eq: "tree = \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>"
        and lookup_t: "fmlookup (HashMap t) x = Some h"
        using less.prems Cons
        by (auto simp: protocol_merkle.created_tree.simps)
      show ?thesis
      proof (cases "fmlookup (HashMap s) x")
        case None
        then have "hash_map_new_output_hit (set_tree tree) s t"
          unfolding hash_map_new_output_hit_def tree_eq
          using lookup_t by auto
        then show ?thesis by simp
      next
        case (Some h')
        have lookup_t': "fmlookup (HashMap t) x = Some h'"
          by (rule hash_extension_lookup[OF Some less.prems(2)])
        then have h'_eq: "h' = h"
          using lookup_t by simp
        have "protocol_merkle.created_tree [x] tree s"
          unfolding tree_eq
          using Some h'_eq
          by (simp add: protocol_merkle.created_tree.simps)
        then show ?thesis
          using Cons Nil by simp
      qed
    next
      case (Cons y ys)
      let ?xs = "x # y # ys"
      let ?i = "length ?xs div 2"
      have xs_eq: "xs = ?xs"
        using xs_cons Cons by simp
      from less.prems(1) obtain l h r where
        tree_eq: "tree = \<langle>l, h, r\<rangle>"
        and left_t:
          "protocol_merkle.created_tree (take ?i ?xs) l t"
        and right_t:
          "protocol_merkle.created_tree (drop ?i ?xs) r t"
        and lookup_t:
          "fmlookup (HashMap t) (MerkleNode (value l) (value r)) =
            Some h"
        unfolding xs_eq
        by (auto simp: protocol_merkle.created_tree.simps Let_def)
      have i_pos: "0 < ?i"
        by simp
      have i_lt: "?i < length ?xs"
        by simp
      have len_left: "length (take ?i ?xs) < length xs"
        using i_lt unfolding xs_eq by simp
      have len_right: "length (drop ?i ?xs) < length xs"
        using i_pos unfolding xs_eq by simp
      have left_split:
        "protocol_merkle.created_tree (take ?i ?xs) l s \<or>
          hash_map_new_output_hit (set_tree l) s t"
        by (rule less.hyps[OF len_left])
          (use left_t less.prems(2) in simp_all)
      from left_split show ?thesis
      proof
        assume left_s:
          "protocol_merkle.created_tree (take ?i ?xs) l s"
        have right_split:
          "protocol_merkle.created_tree (drop ?i ?xs) r s \<or>
            hash_map_new_output_hit (set_tree r) s t"
          by (rule less.hyps[OF len_right])
            (use right_t less.prems(2) in simp_all)
        from right_split show ?thesis
        proof
          assume right_s:
            "protocol_merkle.created_tree (drop ?i ?xs) r s"
          show ?thesis
          proof (cases
              "fmlookup (HashMap s)
                (MerkleNode (value l) (value r))")
            case None
            then have "hash_map_new_output_hit (set_tree tree) s t"
              unfolding hash_map_new_output_hit_def tree_eq
              using lookup_t by auto
            then show ?thesis by simp
          next
            case (Some h')
            have lookup_t':
              "fmlookup (HashMap t) (MerkleNode (value l) (value r)) =
                Some h'"
              by (rule hash_extension_lookup[OF Some less.prems(2)])
            then have h'_eq: "h' = h"
              using lookup_t by simp
            have "protocol_merkle.created_tree ?xs tree s"
              unfolding tree_eq
              using left_s right_s Some h'_eq
              by (auto simp add: protocol_merkle.created_tree.simps Let_def)
            then have "protocol_merkle.created_tree xs tree s"
              unfolding xs_eq .
            then show ?thesis by blast
          qed
        next
          assume right_hit: "hash_map_new_output_hit (set_tree r) s t"
          have "hash_map_new_output_hit (set_tree tree) s t"
            by (rule hash_map_new_output_hit_subset[OF _ right_hit])
              (auto simp add: tree_eq)
          then show ?thesis by simp
        qed
      next
        assume left_hit: "hash_map_new_output_hit (set_tree l) s t"
        have "hash_map_new_output_hit (set_tree tree) s t"
          by (rule hash_map_new_output_hit_subset[OF _ left_hit])
            (auto simp add: tree_eq)
        then show ?thesis by simp
      qed
    qed
  qed
qed

lemma protocol_created_tree_pullback_or_new_output_hit:
  assumes created: "protocol_created_tree xs tree t"
    and ext: "s \<le> t"
  shows
    "protocol_created_tree xs tree s \<or>
      hash_map_new_output_hit (set_tree tree) s t"
  using protocol_merkle_created_tree_pullback_or_new_output_hit
      [OF created[unfolded protocol_created_tree_def] ext]
  unfolding protocol_created_tree_def .

lemma protocol_created_tree_nonempty_root_lookup:
  assumes created: "protocol_created_tree xs tree s"
    and nonempty: "xs \<noteq> []"
  obtains input where
    "fmlookup (HashMap s) input = Some (value tree)"
proof (cases "length xs = 1")
  case True
  then obtain x where xs_eq: "xs = [x]"
    using nonempty by (cases xs) auto
  from protocol_created_tree_singletonD[OF created[unfolded xs_eq]]
  obtain h where
    tree_eq: "tree = \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>"
    and lookup: "fmlookup (HashMap s) (MerkleLeaf x) = Some h"
    by blast
  show ?thesis
    by (rule that[of "MerkleLeaf x"]) (use lookup in \<open>simp add: tree_eq\<close>)
next
  case False
  have len: "2 \<le> length xs"
    using nonempty False by (cases xs; cases "tl xs") auto
  from protocol_created_tree_internalD[OF created len]
  obtain l h r i where
    tree_eq: "tree = \<langle>l, h, r\<rangle>"
    and lookup:
      "fmlookup (HashMap s) (MerkleNode (value l) (value r)) = Some h"
    by blast
  show ?thesis
    by (rule that[of "MerkleNode (value l) (value r)"])
      (use lookup in \<open>simp add: tree_eq\<close>)
qed

lemma merkle_root_binds_nonempty_table_output_lookup:
  fixes rt :: "'f"
  assumes bind: "merkle_root_binds_table rt table s"
    and nonempty: "table \<noteq> []"
  obtains input where
    "fmlookup (HashMap s) input = Some rt"
proof -
  from bind obtain tree where
    created: "created_tree table tree s"
    and root_eq: "rt = value tree"
    unfolding merkle_root_binds_table_def by blast
  from protocol_created_tree_nonempty_root_lookup
      [OF created[unfolded created_tree_def] nonempty]
  obtain input where
    "fmlookup (HashMap s) input = Some (value tree)"
    by blast
  then have lookup: "fmlookup (HashMap s) input = Some rt"
    using root_eq by simp
  show ?thesis
    by (rule that[OF lookup])
qed

lemma merkle_root_binds_table_pullback_or_new_tree_output_hit:
  assumes ext: "prefix_state \<le> final_state"
    and bind: "merkle_root_binds_table rt table final_state"
  obtains tree where
    "created_tree table tree final_state"
    "rt = value tree"
    "merkle_root_binds_table rt table prefix_state \<or>
      hash_map_new_output_hit (set_tree tree) prefix_state final_state"
proof -
  from bind obtain tree where
    created: "created_tree table tree final_state"
    and rt_eq: "rt = value tree"
    unfolding merkle_root_binds_table_def by blast
  have pullback:
    "created_tree table tree prefix_state \<or>
      hash_map_new_output_hit (set_tree tree) prefix_state final_state"
    using protocol_created_tree_pullback_or_new_output_hit
      [OF created[unfolded created_tree_def] ext]
    unfolding created_tree_def .
  have
    "merkle_root_binds_table rt table prefix_state \<or>
      hash_map_new_output_hit (set_tree tree) prefix_state final_state"
  proof -
    from pullback show ?thesis
    proof
      assume "created_tree table tree prefix_state"
      then have "merkle_root_binds_table rt table prefix_state"
      unfolding merkle_root_binds_table_def
      using rt_eq by blast
      then show ?thesis by simp
    next
      assume "hash_map_new_output_hit (set_tree tree) prefix_state final_state"
      then show ?thesis by simp
    qed
  qed
  then show ?thesis
    by (rule that[OF created rt_eq])
qed

lemma merkle_root_binds_nonempty_table_late_root_output_preexisting_or_new_hit:
  fixes rt :: "'f"
  assumes ext: "s \<le> t"
    and bind: "merkle_root_binds_table rt table t"
    and nonempty: "table \<noteq> []"
  shows
    "(\<exists>input. fmlookup (HashMap s) input = Some rt) \<or>
     hash_map_new_output_hit {rt} s t"
proof -
  from merkle_root_binds_nonempty_table_output_lookup[OF bind nonempty]
  obtain input where lookup_t:
    "fmlookup (HashMap t) input = Some rt"
    by blast
  show ?thesis
  proof (cases "fmlookup (HashMap s) input")
    case None
    then have "hash_map_new_output_hit {rt} s t"
      unfolding hash_map_new_output_hit_def
      using lookup_t by blast
    then show ?thesis by simp
  next
    case (Some old)
    have lookup_t_old: "fmlookup (HashMap t) input = Some old"
      by (rule hash_extension_lookup[OF Some ext])
    then have old_eq: "old = rt"
      using lookup_t by simp
    then show ?thesis
      using Some by blast
  qed
qed

lemma accepted_with_bound_tables_trace_root_late_output_preexisting_or_new_hit:
  assumes ext: "prefix_state \<le> final_state"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
  obtains fr f_fri_roots f_final dg composition_fri_roots final rest
  where
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    "merkle_root_binds_table fr trace_table final_state"
    "(\<exists>input. fmlookup (HashMap prefix_state) input = Some fr) \<or>
      hash_map_new_output_hit {fr} prefix_state final_state"
proof -
  from bound obtain fr f_fri_roots f_final dg composition_fri_roots final
      rest where
    header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and bind: "merkle_root_binds_table fr trace_table final_state"
    unfolding accepted_with_bound_tables_def by blast
  have nonempty: "trace_table \<noteq> []"
    using accepted_with_bound_tables_shapes(1)[OF bound]
      eval_domain_nontrivial by auto
  have late:
    "(\<exists>input. fmlookup (HashMap prefix_state) input = Some fr) \<or>
      hash_map_new_output_hit {fr} prefix_state final_state"
    by (rule
        merkle_root_binds_nonempty_table_late_root_output_preexisting_or_new_hit
        [OF ext bind nonempty])
  show ?thesis
    by (rule that[OF header bind late])
qed

lemma accepted_with_bound_tables_composition_root_late_output_preexisting_or_new_hit:
  assumes ext: "prefix_state \<le> final_state"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
  obtains fr f_fri_roots f_final dg composition_fri_roots final rest
  where
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    "composition_fri_roots \<noteq> []"
    "merkle_root_binds_table (hd composition_fri_roots) composition_table
      final_state"
    "(\<exists>input.
        fmlookup (HashMap prefix_state) input =
          Some (hd composition_fri_roots)) \<or>
      hash_map_new_output_hit {hd composition_fri_roots} prefix_state
        final_state"
proof -
  from bound obtain fr f_fri_roots f_final dg composition_fri_roots final
      rest where
    header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and bind:
      "merkle_root_binds_table (hd composition_fri_roots)
        composition_table final_state"
    unfolding accepted_with_bound_tables_def by blast
  have nonempty: "composition_table \<noteq> []"
    using accepted_with_bound_tables_shapes(2)[OF bound]
      eval_domain_nontrivial by auto
  have late:
    "(\<exists>input.
        fmlookup (HashMap prefix_state) input =
          Some (hd composition_fri_roots)) \<or>
      hash_map_new_output_hit {hd composition_fri_roots} prefix_state
        final_state"
    by (rule
        merkle_root_binds_nonempty_table_late_root_output_preexisting_or_new_hit
        [OF ext bind nonempty])
  show ?thesis
    by (rule that[OF header comp_nonempty bind late])
qed

lemma accepted_with_bound_tables_initial_roots_late_output_preexisting_or_new_hit:
  assumes ext: "prefix_state \<le> final_state"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
  obtains fr f_fri_roots f_final dg composition_fri_roots final rest
  where
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    "composition_fri_roots \<noteq> []"
    "merkle_root_binds_table fr trace_table final_state"
    "merkle_root_binds_table (hd composition_fri_roots) composition_table
      final_state"
    "(\<exists>input. fmlookup (HashMap prefix_state) input = Some fr) \<or>
      hash_map_new_output_hit {fr} prefix_state final_state"
    "(\<exists>input.
        fmlookup (HashMap prefix_state) input =
          Some (hd composition_fri_roots)) \<or>
      hash_map_new_output_hit {hd composition_fri_roots} prefix_state
        final_state"
proof -
  from accepted_with_bound_tables_trace_root_late_output_preexisting_or_new_hit
      [OF ext bound]
  obtain fr f_fri_roots f_final dg composition_fri_roots final rest where
    header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and trace_bind:
      "merkle_root_binds_table fr trace_table final_state"
    and trace_late:
      "(\<exists>input. fmlookup (HashMap prefix_state) input = Some fr) \<or>
        hash_map_new_output_hit {fr} prefix_state final_state"
    by blast
  from accepted_with_bound_tables_composition_root_late_output_preexisting_or_new_hit
      [OF ext bound]
  obtain fr' f_fri_roots' f_final' dg' composition_fri_roots' final' rest'
    where header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and comp_nonempty': "composition_fri_roots' \<noteq> []"
    and comp_bind':
      "merkle_root_binds_table (hd composition_fri_roots')
        composition_table final_state"
    and comp_late':
      "(\<exists>input.
          fmlookup (HashMap prefix_state) input =
            Some (hd composition_fri_roots')) \<or>
        hash_map_new_output_hit {hd composition_fri_roots'} prefix_state
          final_state"
    by blast
  have eqs:
    "fr' = fr \<and>
     f_fri_roots' = f_fri_roots \<and>
     f_final' = f_final \<and>
     dg' = dg \<and>
     composition_fri_roots' = composition_fri_roots \<and>
     final' = final \<and>
     rest' = rest"
    using verifier_header_transcript_unique[OF header header'] by simp
  show ?thesis
    by (rule that[OF header])
      (use comp_nonempty' comp_bind' comp_late' trace_bind trace_late eqs
        in simp_all)
qed

lemma accepted_with_bound_tables_initial_roots_late_output_preexisting_or_union_hit:
  assumes ext: "prefix_state \<le> final_state"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
  obtains fr f_fri_roots f_final dg composition_fri_roots final rest
  where
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    "composition_fri_roots \<noteq> []"
    "merkle_root_binds_table fr trace_table final_state"
    "merkle_root_binds_table (hd composition_fri_roots) composition_table
      final_state"
    "((\<exists>input. fmlookup (HashMap prefix_state) input = Some fr) \<and>
      (\<exists>input.
        fmlookup (HashMap prefix_state) input =
          Some (hd composition_fri_roots))) \<or>
      hash_map_new_output_hit {fr, hd composition_fri_roots} prefix_state
        final_state"
proof -
  from accepted_with_bound_tables_initial_roots_late_output_preexisting_or_new_hit
      [OF ext bound]
  obtain fr f_fri_roots f_final dg composition_fri_roots final rest where
    header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and trace_bind:
      "merkle_root_binds_table fr trace_table final_state"
    and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots)
        composition_table final_state"
    and trace_late:
      "(\<exists>input. fmlookup (HashMap prefix_state) input = Some fr) \<or>
        hash_map_new_output_hit {fr} prefix_state final_state"
    and comp_late:
      "(\<exists>input.
          fmlookup (HashMap prefix_state) input =
            Some (hd composition_fri_roots)) \<or>
        hash_map_new_output_hit {hd composition_fri_roots} prefix_state
          final_state"
    by blast
  have late_union:
    "((\<exists>input. fmlookup (HashMap prefix_state) input = Some fr) \<and>
      (\<exists>input.
        fmlookup (HashMap prefix_state) input =
          Some (hd composition_fri_roots))) \<or>
      hash_map_new_output_hit {fr, hd composition_fri_roots} prefix_state
        final_state"
  proof (cases
      "(\<exists>input. fmlookup (HashMap prefix_state) input = Some fr) \<and>
       (\<exists>input.
          fmlookup (HashMap prefix_state) input =
            Some (hd composition_fri_roots))")
    case True
    then show ?thesis by simp
  next
    case False
    then have
      "hash_map_new_output_hit {fr} prefix_state final_state \<or>
       hash_map_new_output_hit {hd composition_fri_roots} prefix_state
        final_state"
      using trace_late comp_late by blast
    then show ?thesis
    proof
      assume "hash_map_new_output_hit {fr} prefix_state final_state"
      then have
        "hash_map_new_output_hit {fr, hd composition_fri_roots}
          prefix_state final_state"
        using hash_map_new_output_hit_subset[of "{fr}"
          "{fr, hd composition_fri_roots}" prefix_state final_state]
        by auto
      then show ?thesis by simp
    next
      assume
        "hash_map_new_output_hit {hd composition_fri_roots} prefix_state
          final_state"
      then have
        "hash_map_new_output_hit {fr, hd composition_fri_roots}
          prefix_state final_state"
        using hash_map_new_output_hit_subset
          [of "{hd composition_fri_roots}"
            "{fr, hd composition_fri_roots}" prefix_state final_state]
        by auto
      then show ?thesis by simp
    qed
  qed
  show ?thesis
    by (rule that[OF header comp_nonempty trace_bind comp_bind late_union])
qed

lemma accepted_with_bound_tables_initial_roots_pullback_or_new_tree_output_hit:
  assumes ext: "prefix_state \<le> final_state"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
  obtains fr f_fri_roots f_final dg composition_fri_roots final rest
      trace_tree composition_tree
  where
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    "composition_fri_roots \<noteq> []"
    "created_tree trace_table trace_tree final_state"
    "fr = value trace_tree"
    "created_tree composition_table composition_tree final_state"
    "hd composition_fri_roots = value composition_tree"
    "(merkle_root_binds_table fr trace_table prefix_state \<and>
      merkle_root_binds_table (hd composition_fri_roots) composition_table
        prefix_state) \<or>
      hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
proof -
  from bound obtain fr f_fri_roots f_final dg composition_fri_roots final
      rest where
    header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and trace_bind:
      "merkle_root_binds_table fr trace_table final_state"
    and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots)
        composition_table final_state"
    unfolding accepted_with_bound_tables_def by blast
  from merkle_root_binds_table_pullback_or_new_tree_output_hit
      [OF ext trace_bind]
  obtain trace_tree where
    trace_created: "created_tree trace_table trace_tree final_state"
    and trace_root: "fr = value trace_tree"
    and trace_split:
      "merkle_root_binds_table fr trace_table prefix_state \<or>
        hash_map_new_output_hit (set_tree trace_tree) prefix_state
          final_state"
    by blast
  from merkle_root_binds_table_pullback_or_new_tree_output_hit
      [OF ext comp_bind]
  obtain composition_tree where
    comp_created:
      "created_tree composition_table composition_tree final_state"
    and comp_root:
      "hd composition_fri_roots = value composition_tree"
    and comp_split:
      "merkle_root_binds_table (hd composition_fri_roots)
        composition_table prefix_state \<or>
        hash_map_new_output_hit (set_tree composition_tree) prefix_state
          final_state"
    by blast
  have split:
    "(merkle_root_binds_table fr trace_table prefix_state \<and>
      merkle_root_binds_table (hd composition_fri_roots) composition_table
        prefix_state) \<or>
      hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
  proof -
    from trace_split show ?thesis
    proof
      assume trace_prefix:
        "merkle_root_binds_table fr trace_table prefix_state"
      from comp_split show ?thesis
      proof
        assume comp_prefix:
          "merkle_root_binds_table (hd composition_fri_roots)
            composition_table prefix_state"
        then show ?thesis
          using trace_prefix by simp
      next
        assume comp_hit:
          "hash_map_new_output_hit (set_tree composition_tree)
            prefix_state final_state"
        have "hash_map_new_output_hit
            (set_tree trace_tree \<union> set_tree composition_tree)
            prefix_state final_state"
          by (rule hash_map_new_output_hit_subset[OF _ comp_hit])
            simp
        then show ?thesis by simp
      qed
    next
      assume trace_hit:
        "hash_map_new_output_hit (set_tree trace_tree) prefix_state
          final_state"
      have "hash_map_new_output_hit
          (set_tree trace_tree \<union> set_tree composition_tree)
          prefix_state final_state"
        by (rule hash_map_new_output_hit_subset[OF _ trace_hit])
          simp
      then show ?thesis by simp
    qed
  qed
  show ?thesis
    by (rule that[OF header comp_nonempty trace_created trace_root
          comp_created comp_root split])
qed

lemma hash_map_new_output_hit_after_update:
  "hash_map_new_output_hit B s
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>) \<longleftrightarrow>
    fmlookup (HashMap s) x = None \<and> y \<in> B"
proof
  assume hit:
    "hash_map_new_output_hit B s
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
  then obtain k z where fresh:
      "fmlookup (HashMap s) k = None"
    and lookup:
      "fmlookup (fmupd x y (HashMap s)) k = Some z"
    and z_in: "z \<in> B"
    unfolding hash_map_new_output_hit_def by auto
  have "k = x"
  proof (rule ccontr)
    assume "k \<noteq> x"
    then have "fmlookup (HashMap s) k = Some z"
      using lookup by simp
    then show False
      using fresh by simp
  qed
  then show "fmlookup (HashMap s) x = None \<and> y \<in> B"
    using fresh lookup z_in by simp
next
  assume "fmlookup (HashMap s) x = None \<and> y \<in> B"
  then show
    "hash_map_new_output_hit B s
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
    unfolding hash_map_new_output_hit_def by auto
qed

lemma hash_extension_none:
  assumes ext: "s \<le> t"
    and none: "fmlookup (HashMap t) x = None"
  shows "fmlookup (HashMap s) x = None"
proof (cases "fmlookup (HashMap s) x")
  case None
  then show ?thesis .
next
  case (Some y)
  have "fmlookup (HashMap t) x = Some y"
    by (rule hash_extension_lookup[OF Some ext])
  then show ?thesis
    using none by simp
qed

lemma hash_map_new_output_hit_extend_initial:
  assumes ext: "s \<le> t"
    and hit: "hash_map_new_output_hit B t u"
  shows "hash_map_new_output_hit B s u"
proof -
  from hit obtain x y where fresh_t:
      "fmlookup (HashMap t) x = None"
    and lookup_u: "fmlookup (HashMap u) x = Some y"
    and y_in: "y \<in> B"
    unfolding hash_map_new_output_hit_def by blast
  have fresh_s: "fmlookup (HashMap s) x = None"
    by (rule hash_extension_none[OF ext fresh_t])
  show ?thesis
    unfolding hash_map_new_output_hit_def
    using fresh_s lookup_u y_in by blast
qed

lemma hash_map_new_output_hit_trans_decomp:
  assumes ext_st: "s \<le> t"
    and ext_tu: "t \<le> u"
    and hit: "hash_map_new_output_hit B s u"
  shows
    "hash_map_new_output_hit B s t \<or>
     hash_map_new_output_hit B t u"
proof -
  from hit obtain x y where fresh_s:
      "fmlookup (HashMap s) x = None"
    and lookup_u: "fmlookup (HashMap u) x = Some y"
    and y_in: "y \<in> B"
    unfolding hash_map_new_output_hit_def by blast
  show ?thesis
  proof (cases "fmlookup (HashMap t) x")
    case None
    then have "hash_map_new_output_hit B t u"
      unfolding hash_map_new_output_hit_def
      using lookup_u y_in by blast
    then show ?thesis by simp
  next
    case (Some z)
    have lookup_u_z: "fmlookup (HashMap u) x = Some z"
      by (rule hash_extension_lookup[OF Some ext_tu])
    have "z = y"
      using lookup_u lookup_u_z by simp
    then have "hash_map_new_output_hit B s t"
      unfolding hash_map_new_output_hit_def
      using fresh_s Some y_in by blast
    then show ?thesis by simp
  qed
qed

definition hash_extension_preserving
  :: "('r, ('f, 'a) protocol_channel_scheme) state_monad \<Rightarrow> bool"
  where
    "hash_extension_preserving m \<longleftrightarrow>
      (\<forall>s x t.
        Some (x, t) \<in> set_dist (execute m s) \<longrightarrow> s \<le> t)"

definition hash_map_preserving
  :: "('r, ('f, 'a) protocol_channel_scheme) state_monad \<Rightarrow> bool"
  where
    "hash_map_preserving m \<longleftrightarrow>
      (\<forall>s x t.
        Some (x, t) \<in> set_dist (execute m s) \<longrightarrow>
        HashMap t = HashMap s)"

lemma hash_map_preserving_imp_hash_extension_preserving:
  assumes "hash_map_preserving m"
  shows "hash_extension_preserving m"
  unfolding hash_extension_preserving_def
proof (intro allI impI)
  fix s x t
  assume outcome: "Some (x, t) \<in> set_dist (execute m s)"
  have "HashMap t = HashMap s"
    using assms outcome unfolding hash_map_preserving_def by blast
  then show "s \<le> t"
    unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
qed

lemma hash_extension_preserving_return:
  "hash_extension_preserving (return x)"
  unfolding hash_extension_preserving_def
  by (intro allI impI) (simp add: hash_ext_refl)

lemma hash_extension_preserving_hash:
  fixes x :: "'f protocol_hash_input"
  shows
    "hash_extension_preserving
      (hash x :: ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
  unfolding hash_extension_preserving_def
  by (intro allI impI) (rule hash_outcome(1))

lemma hash_extension_preserving_bind:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes m_ext: "hash_extension_preserving m"
    and k_ext: "\<And>x. hash_extension_preserving (k x)"
  shows "hash_extension_preserving (m \<bind> k)"
  unfolding hash_extension_preserving_def
proof (intro allI impI)
  fix s y u
  assume outcome: "Some (y, u) \<in> set_dist (execute (m \<bind> k) s)"
  from outcome obtain x t where m_out:
      "Some (x, t) \<in> set_dist (execute m s)"
    and k_out: "Some (y, u) \<in> set_dist (execute (k x) t)"
    by (auto elim!: set_dist_bindE)
  have ext_st: "s \<le> t"
    using m_ext m_out unfolding hash_extension_preserving_def by blast
  have ext_tu: "t \<le> u"
    using k_ext[of x] k_out unfolding hash_extension_preserving_def by blast
  show "s \<le> u"
    by (rule hash_ext_trans[OF ext_st ext_tu])
qed

lemma wp_hash_new_output_hit:
  fixes x :: "'f protocol_hash_input"
    and s :: "('f, 'a) protocol_channel_scheme"
  shows
    "wp_event (hash x) (hash_new_output_hit_event B s) s =
      (if fmlookup (HashMap s) x = None
       then nnreal (card B) / nnreal size
       else 0)"
proof (cases "fmlookup (HashMap s) x")
  case None
  have indicator:
    "(\<lambda>y. if hash_map_new_output_hit B s
        (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)
      then 1 else 0 :: prob) =
      (\<lambda>y. if y \<in> B then 1 else 0)"
    by (rule ext)
      (simp add: hash_map_new_output_hit_after_update None)
  have "wp_event (hash x) (hash_new_output_hit_event B s) s =
      dist_expect (hash_dist x s) (\<lambda>y. if y \<in> B then 1 else 0)"
    unfolding wp_event_def hash_new_output_hit_event_def
    by (simp add: wp_hash indicator)
  also have "... = nnreal (card B) / nnreal size"
    by (rule dist_expect_hash_dist_fresh_indicator[OF None])
  finally show ?thesis
    using None by simp
next
  case (Some y)
  have no_hit:
    "\<not> hash_map_new_output_hit B s
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
    by (simp add: hash_map_new_output_hit_after_update Some)
  show ?thesis
    unfolding wp_event_def hash_new_output_hit_event_def
    by (simp add: wp_hash Some hash_dist_def option_default_dist_def no_hit)
qed

lemma wp_hash_new_output_hit_bound:
  fixes x :: "'f protocol_hash_input"
    and s :: "('f, 'a) protocol_channel_scheme"
  shows
    "wp_event (hash x) (hash_new_output_hit_event B s) s \<le>
      nnreal (card B) / nnreal size"
  unfolding wp_hash_new_output_hit
  by simp

definition hash_target_budget_value
  :: "'f set \<Rightarrow> nat \<Rightarrow> prob"
  where
    "hash_target_budget_value B n =
      nnreal (n * card B) / nnreal size"

definition hash_target_budget
  :: "'f set \<Rightarrow> nat \<Rightarrow>
      ('r, ('f, 'a) protocol_channel_scheme) state_monad \<Rightarrow> bool"
  where
    "hash_target_budget B n m \<longleftrightarrow>
      (\<forall>s.
        wp_event m (hash_new_output_hit_event B s) s \<le>
          hash_target_budget_value B n)"

lemma hash_target_budget_value_add:
  "hash_target_budget_value B n + hash_target_budget_value B m =
    hash_target_budget_value B (n + m)"
  unfolding hash_target_budget_value_def
  by (simp add: add_divide_nnreal algebra_simps)

lemma hash_new_output_hit_event_step_bound:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes ext_st: "s \<le> t"
    and ext_m: "hash_extension_preserving m"
  shows
    "wp_event m (hash_new_output_hit_event B s) t \<le>
      (if hash_map_new_output_hit B s t then 1
       else wp_event m (hash_new_output_hit_event B t) t)"
proof (cases "hash_map_new_output_hit B s t")
  case True
  then show ?thesis
    using wp_event_le_1[of m "hash_new_output_hit_event B s" t]
    by simp
next
  case False
  have mono:
    "wp_event m (hash_new_output_hit_event B s) t \<le>
      wp_event m (hash_new_output_hit_event B t) t"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute m t)"
      and hit_s: "hash_new_output_hit_event B s out"
    show "hash_new_output_hit_event B t out"
    proof (cases out)
      case None
      then show ?thesis
        using hit_s unfolding hash_new_output_hit_event_def by simp
    next
      case (Some xu)
      then obtain x u where xu: "xu = (x, u)"
        by (cases xu) simp
      have out: "Some (x, u) \<in> set_dist (execute m t)"
        using support Some xu by simp
      have ext_tu: "t \<le> u"
        using ext_m out unfolding hash_extension_preserving_def by blast
      have hit_su: "hash_map_new_output_hit B s u"
        using hit_s Some xu unfolding hash_new_output_hit_event_def by simp
      have "hash_map_new_output_hit B s t \<or>
          hash_map_new_output_hit B t u"
        by (rule hash_map_new_output_hit_trans_decomp
            [OF ext_st ext_tu hit_su])
      then have "hash_map_new_output_hit B t u"
        using False by blast
      then show ?thesis
        using Some xu unfolding hash_new_output_hit_event_def by simp
    qed
  qed
  show ?thesis
    using False mono by simp
qed

lemma hash_map_new_output_hit_refl[simp]:
  "\<not> hash_map_new_output_hit B s s"
  unfolding hash_map_new_output_hit_def by auto

lemma hash_target_budget_return:
  "hash_target_budget B 0 (return x)"
  unfolding hash_target_budget_def hash_target_budget_value_def
    hash_new_output_hit_event_def
  by (simp add: wp_event_def wpsimps)

lemma hash_map_preserving_no_new_output_hit_on_support:
  assumes preserving: "hash_map_preserving m"
    and support: "out \<in> set_dist (execute m s)"
  shows "\<not> hash_new_output_hit_event B s out"
proof (cases out)
  case None
  then show ?thesis
    unfolding hash_new_output_hit_event_def by simp
next
  case (Some xt)
  then obtain x t where xt: "xt = (x, t)"
    by (cases xt) simp
  have out: "Some (x, t) \<in> set_dist (execute m s)"
    using support Some xt by simp
  have map_eq: "HashMap t = HashMap s"
    using preserving out unfolding hash_map_preserving_def by blast
  have "\<not> hash_map_new_output_hit B s t"
    using map_eq unfolding hash_map_new_output_hit_def by auto
  then show ?thesis
    using Some xt unfolding hash_new_output_hit_event_def by simp
qed

lemma hash_map_preserving_imp_hash_target_budget_zero:
  assumes preserving: "hash_map_preserving m"
  shows "hash_target_budget B 0 m"
  unfolding hash_target_budget_def hash_target_budget_value_def
  apply (intro allI)
  apply (rule order_trans[
        where y="wp_event m (\<lambda>_. False) _"])
   apply (rule wp_event_mono_on_support)
   apply (meson hash_map_preserving_no_new_output_hit_on_support preserving)
  unfolding wp_event_def wp_def dist_expect_def
  by simp

lemma hash_target_budget_hash:
  fixes x :: "'f protocol_hash_input"
  shows
    "hash_target_budget B 1
      (hash x :: ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
  unfolding hash_target_budget_def
proof (intro allI)
  fix s :: "('f, 'a) protocol_channel_scheme"
  show
    "wp_event (hash x) (hash_new_output_hit_event B s) s \<le>
      hash_target_budget_value B 1"
    using wp_hash_new_output_hit_bound[where x=x and s=s and B=B]
    unfolding hash_target_budget_value_def by simp
qed

lemma hash_target_budget_bind:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes m_ext: "hash_extension_preserving m"
    and m_budget: "hash_target_budget B n m"
    and k_ext: "\<And>x. hash_extension_preserving (k x)"
    and k_budget: "\<And>x. hash_target_budget B n' (k x)"
  shows "hash_target_budget B (n + n') (m \<bind> k)"
  unfolding hash_target_budget_def
proof (intro allI)
  fix s :: "('f, 'a) protocol_channel_scheme"
  let ?E = "hash_new_output_hit_event B s"
  let ?Tail =
    "\<lambda>out. case out of
      None \<Rightarrow> 0
    | Some (x, t) \<Rightarrow>
        if hash_map_new_output_hit B s t then 0
        else wp_event (k x) (hash_new_output_hit_event B t) t"
  let ?R = "\<lambda>out. (if ?E out then 1 else 0) + ?Tail out"
  have split:
    "wp_event (m \<bind> k) ?E s \<le> wp m ?R s"
  proof -
    have exact:
      "wp_event (m \<bind> k) ?E s =
        wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s"
      unfolding wp_event_def hash_new_output_hit_event_def
      by (simp add: wpsimps)
    have "wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s
        \<le> wp m ?R s"
    proof (rule wp_mono_on_support)
      fix out
      assume support: "out \<in> set_dist (execute m s)"
      show "(case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) \<le> ?R out"
      proof (cases out)
        case None
        then show ?thesis
          unfolding hash_new_output_hit_event_def by simp
      next
        case (Some xt)
        then obtain x t where xt: "xt = (x, t)"
          by (cases xt) simp
        have m_out: "Some (x, t) \<in> set_dist (execute m s)"
          using support Some xt by simp
        have ext_st: "s \<le> t"
          using m_ext m_out unfolding hash_extension_preserving_def by blast
        have step:
          "wp_event (k x) ?E t \<le>
            (if hash_map_new_output_hit B s t then 1
             else wp_event (k x) (hash_new_output_hit_event B t) t)"
          by (rule hash_new_output_hit_event_step_bound
              [OF ext_st k_ext[of x]])
        show ?thesis
        proof (cases "hash_map_new_output_hit B s t")
          case True
          then show ?thesis
            using Some xt step
            unfolding hash_new_output_hit_event_def by simp
        next
          case False
          then show ?thesis
            using Some xt step
            unfolding hash_new_output_hit_event_def by simp
        qed
      qed
    qed
    then show ?thesis
      unfolding exact .
  qed
  have head_bound:
    "wp_event m ?E s \<le> hash_target_budget_value B n"
    using m_budget unfolding hash_target_budget_def by blast
  have tail_bound:
    "wp m ?Tail s \<le> hash_target_budget_value B n'"
  proof (rule wp_le_const_on_support)
    fix out
    assume support: "out \<in> set_dist (execute m s)"
    show "?Tail out \<le> hash_target_budget_value B n'"
    proof (cases out)
      case None
      then show ?thesis
        unfolding hash_target_budget_value_def by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) simp
      have tail:
        "wp_event (k x) (hash_new_output_hit_event B t) t \<le>
          hash_target_budget_value B n'"
        using k_budget[of x] unfolding hash_target_budget_def by blast
      show ?thesis
        using Some xt tail by simp
    qed
  qed
  have "wp_event (m \<bind> k) ?E s \<le> wp m ?R s"
    by (rule split)
  also have "... = wp_event m ?E s + wp m ?Tail s"
    unfolding wp_event_def wp_def dist_expect_def
    by (simp add: sum.distrib algebra_simps
        hash_new_output_hit_event_def)
  also have "... \<le>
      hash_target_budget_value B n + hash_target_budget_value B n'"
    by (intro add_mono head_bound tail_bound)
  also have "... = hash_target_budget_value B (n + n')"
    by (rule hash_target_budget_value_add)
  finally show
    "wp_event (m \<bind> k) (hash_new_output_hit_event B s) s \<le>
      hash_target_budget_value B (n + n')" .
qed

lemma hash_target_budget_value_mono:
  assumes "m \<le> n"
  shows "hash_target_budget_value B m \<le> hash_target_budget_value B n"
  unfolding hash_target_budget_value_def
  apply (subst nn2real_le_iff[symmetric])
  using assms by (simp add: divide_right_mono mult_right_mono)

lemma hash_target_budget_mono:
  assumes "m \<le> n"
    and budget: "hash_target_budget B m p"
  shows "hash_target_budget B n p"
  unfolding hash_target_budget_def
proof (intro allI)
  fix s
  have "wp_event p (hash_new_output_hit_event B s) s \<le>
      hash_target_budget_value B m"
    using budget unfolding hash_target_budget_def by blast
  also have "... \<le> hash_target_budget_value B n"
    by (rule hash_target_budget_value_mono[OF assms(1)])
  finally show
    "wp_event p (hash_new_output_hit_event B s) s \<le>
      hash_target_budget_value B n" .
qed

definition hash_target_program
  :: "'f set \<Rightarrow> nat \<Rightarrow>
      ('r, ('f, 'a) protocol_channel_scheme) state_monad \<Rightarrow> bool"
  where
    "hash_target_program B n m \<longleftrightarrow>
      hash_extension_preserving m \<and> hash_target_budget B n m"

lemma hash_target_program_extension:
  assumes "hash_target_program B n m"
  shows "hash_extension_preserving m"
  using assms unfolding hash_target_program_def by simp

lemma hash_target_program_budget:
  assumes "hash_target_program B n m"
  shows "hash_target_budget B n m"
  using assms unfolding hash_target_program_def by simp

lemma hash_target_program_mono:
  assumes "m \<le> n"
    and program: "hash_target_program B m p"
  shows "hash_target_program B n p"
  unfolding hash_target_program_def
proof
  show "hash_extension_preserving p"
    using program unfolding hash_target_program_def by simp
  have "hash_target_budget B m p"
    using program unfolding hash_target_program_def by simp
  then show "hash_target_budget B n p"
    by (rule hash_target_budget_mono[OF assms(1)])
qed

lemma hash_target_program_return:
  "hash_target_program B 0 (return x)"
  unfolding hash_target_program_def
  by (intro conjI hash_extension_preserving_return hash_target_budget_return)

lemma hash_target_program_hash:
  fixes x :: "'f protocol_hash_input"
  shows
    "hash_target_program B 1
      (hash x :: ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
  unfolding hash_target_program_def
  by (intro conjI hash_extension_preserving_hash hash_target_budget_hash)

lemma hash_map_preserving_imp_hash_target_program_zero:
  assumes "hash_map_preserving m"
  shows "hash_target_program B 0 m"
  unfolding hash_target_program_def
  using assms hash_map_preserving_imp_hash_extension_preserving
    hash_map_preserving_imp_hash_target_budget_zero
  by blast

lemma hash_target_program_bind:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes m: "hash_target_program B n m"
    and k: "\<And>x. hash_target_program B n' (k x)"
  shows "hash_target_program B (n + n') (m \<bind> k)"
  unfolding hash_target_program_def
proof (intro conjI)
  show "hash_extension_preserving (m \<bind> k)"
    by (rule hash_extension_preserving_bind)
      (use m k in \<open>simp_all add: hash_target_program_def\<close>)
  show "hash_target_budget B (n + n') (m \<bind> k)"
    by (rule hash_target_budget_bind)
      (use m k in \<open>simp_all add: hash_target_program_def\<close>)
qed

lemma hash_extension_preserving_bind_on_outcomes:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes m_ext: "hash_extension_preserving m"
    and k_ext:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_extension_preserving (k x)"
  shows "hash_extension_preserving (m \<bind> k)"
  unfolding hash_extension_preserving_def
proof (intro allI impI)
  fix s y u
  assume outcome: "Some (y, u) \<in> set_dist (execute (m \<bind> k) s)"
  from outcome obtain x t where m_out:
      "Some (x, t) \<in> set_dist (execute m s)"
    and k_out: "Some (y, u) \<in> set_dist (execute (k x) t)"
    by (auto elim!: set_dist_bindE)
  have ext_st: "s \<le> t"
    using m_ext m_out unfolding hash_extension_preserving_def by blast
  have ext_tu: "t \<le> u"
    using k_ext[OF m_out] k_out
    unfolding hash_extension_preserving_def by blast
  show "s \<le> u"
    by (rule hash_ext_trans[OF ext_st ext_tu])
qed

lemma hash_target_budget_bind_on_outcomes:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes m_ext: "hash_extension_preserving m"
    and m_budget: "hash_target_budget B n m"
    and k_ext:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_extension_preserving (k x)"
    and k_budget:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_target_budget B n' (k x)"
  shows "hash_target_budget B (n + n') (m \<bind> k)"
  unfolding hash_target_budget_def
proof (intro allI)
  fix s :: "('f, 'a) protocol_channel_scheme"
  let ?E = "hash_new_output_hit_event B s"
  let ?Tail =
    "\<lambda>out. case out of
      None \<Rightarrow> 0
    | Some (x, t) \<Rightarrow>
        if hash_map_new_output_hit B s t then 0
        else wp_event (k x) (hash_new_output_hit_event B t) t"
  let ?R = "\<lambda>out. (if ?E out then 1 else 0) + ?Tail out"
  have split:
    "wp_event (m \<bind> k) ?E s \<le> wp m ?R s"
  proof -
    have exact:
      "wp_event (m \<bind> k) ?E s =
        wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s"
      unfolding wp_event_def hash_new_output_hit_event_def
      by (simp add: wpsimps)
    have "wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s
        \<le> wp m ?R s"
    proof (rule wp_mono_on_support)
      fix out
      assume support: "out \<in> set_dist (execute m s)"
      show "(case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) \<le> ?R out"
      proof (cases out)
        case None
        then show ?thesis
          unfolding hash_new_output_hit_event_def by simp
      next
        case (Some xt)
        then obtain x t where xt: "xt = (x, t)"
          by (cases xt) simp
        have m_out: "Some (x, t) \<in> set_dist (execute m s)"
          using support Some xt by simp
        have ext_st: "s \<le> t"
          using m_ext m_out unfolding hash_extension_preserving_def by blast
        have step:
          "wp_event (k x) ?E t \<le>
            (if hash_map_new_output_hit B s t then 1
             else wp_event (k x) (hash_new_output_hit_event B t) t)"
          by (rule hash_new_output_hit_event_step_bound
              [OF ext_st k_ext[OF m_out]])
        show ?thesis
          using Some xt step
          unfolding hash_new_output_hit_event_def
          by (cases "hash_map_new_output_hit B s t") simp_all
      qed
    qed
    then show ?thesis
      unfolding exact .
  qed
  have head_bound:
    "wp_event m ?E s \<le> hash_target_budget_value B n"
    using m_budget unfolding hash_target_budget_def by blast
  have tail_bound:
    "wp m ?Tail s \<le> hash_target_budget_value B n'"
  proof (rule wp_le_const_on_support)
    fix out
    assume support: "out \<in> set_dist (execute m s)"
    show "?Tail out \<le> hash_target_budget_value B n'"
    proof (cases out)
      case None
      then show ?thesis
        unfolding hash_target_budget_value_def by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) simp
      have m_out: "Some (x, t) \<in> set_dist (execute m s)"
        using support Some xt by simp
      have tail:
        "wp_event (k x) (hash_new_output_hit_event B t) t \<le>
          hash_target_budget_value B n'"
        using k_budget[OF m_out] unfolding hash_target_budget_def by blast
      show ?thesis
        using Some xt tail by simp
    qed
  qed
  have "wp_event (m \<bind> k) ?E s \<le> wp m ?R s"
    by (rule split)
  also have "... = wp_event m ?E s + wp m ?Tail s"
    unfolding wp_event_def wp_def dist_expect_def
    by (simp add: sum.distrib algebra_simps
        hash_new_output_hit_event_def)
  also have "... \<le>
      hash_target_budget_value B n + hash_target_budget_value B n'"
    by (intro add_mono head_bound tail_bound)
  also have "... = hash_target_budget_value B (n + n')"
    by (rule hash_target_budget_value_add)
  finally show
    "wp_event (m \<bind> k) (hash_new_output_hit_event B s) s \<le>
      hash_target_budget_value B (n + n')" .
qed

lemma hash_target_program_bind_on_outcomes:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes m: "hash_target_program B n m"
    and k:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_target_program B n' (k x)"
  shows "hash_target_program B (n + n') (m \<bind> k)"
  unfolding hash_target_program_def
proof (intro conjI)
  show "hash_extension_preserving (m \<bind> k)"
    by (rule hash_extension_preserving_bind_on_outcomes)
      (use m k in \<open>simp_all add: hash_target_program_def\<close>)
  show "hash_target_budget B (n + n') (m \<bind> k)"
    by (rule hash_target_budget_bind_on_outcomes)
      (use m k in \<open>simp_all add: hash_target_program_def\<close>)
qed

lemma hash_target_program_ntimes:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes m: "hash_target_program B n m"
  shows "hash_target_program B (k * n) (ntimes m k)"
  using m
proof (induction k)
  case 0
  then show ?case
    by (simp add: hash_target_program_return)
next
  case (Suc k)
  have tail: "hash_target_program B (k * n) (ntimes m k)"
    using Suc.IH Suc.prems by simp
  have cont:
    "hash_target_program B (k * n + 0)
      (ntimes m k \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule hash_target_program_bind[OF tail hash_target_program_return])
  have "hash_target_program B (n + (k * n + 0))
      (m \<bind> (\<lambda>x. ntimes m k \<bind> (\<lambda>xs. return (x # xs))))"
    by (rule hash_target_program_bind[OF Suc.prems cont])
  then show ?case by simp
qed

lemma hash_target_program_mmap:
  fixes ms :: "('x, ('f, 'a) protocol_channel_scheme) state_monad list"
  assumes ms: "\<And>m. m \<in> set ms \<Longrightarrow> hash_target_program B n m"
  shows "hash_target_program B (length ms * n) (mmap ms)"
  using ms
proof (induction ms)
  case Nil
  then show ?case
    by (simp add: hash_target_program_return)
next
  case (Cons m ms)
  have head: "hash_target_program B n m"
    using Cons.prems by simp
  have tail: "hash_target_program B (length ms * n) (mmap ms)"
    using Cons.IH Cons.prems by simp
  have cont:
    "hash_target_program B (length ms * n + 0)
      (mmap ms \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule hash_target_program_bind[OF tail hash_target_program_return])
  have "hash_target_program B (n + (length ms * n + 0))
      (m \<bind> (\<lambda>x. mmap ms \<bind> (\<lambda>xs. return (x # xs))))"
    by (rule hash_target_program_bind[OF head cont])
  then show ?case by simp
qed

lemma hash_target_program_mfold:
  fixes steps ::
    "('x \<Rightarrow> ('x, ('f, 'a) protocol_channel_scheme) state_monad) list"
  assumes steps:
    "\<And>step x. step \<in> set steps \<Longrightarrow>
      hash_target_program B n (step x)"
  shows "hash_target_program B (length steps * n) (mfold x steps)"
  using steps
proof (induction steps arbitrary: x)
  case Nil
  then show ?case
    by (simp add: hash_target_program_return)
next
  case (Cons step steps)
  have head: "hash_target_program B n (step x)"
    using Cons.prems by simp
  have tail:
    "\<And>y. hash_target_program B (length steps * n) (mfold y steps)"
    using Cons.IH Cons.prems by simp
  have "hash_target_program B (n + length steps * n)
      (step x \<bind> (\<lambda>y. mfold y steps))"
    by (rule hash_target_program_bind[OF head tail])
  then show ?case by simp
qed

end

end
