(*  Title:      Stark/Soundness_Core_Events.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Core_Events
  imports Soundness_Core_WP
begin

text \<open>Transcript-shape, Merkle binding, and alpha/header event definitions.\<close>

context soundness
begin

definition verifier_header_messages
  :: "'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> 'f list"
  where
    "verifier_header_messages fr f_fri_roots f_final as dg composition_fri_roots final =
      [fr] @ f_fri_roots @ [f_final] @ as @ [dg] @
      composition_fri_roots @ [final]"

definition verifier_header_state
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f"
  where
    "verifier_header_state s fr f_fri_roots f_final as dg composition_fri_roots final =
      foldl concat (PState s)
        (verifier_header_messages fr f_fri_roots f_final as dg
          composition_fri_roots final)"

definition verifier_header_transcript
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest \<longleftrightarrow>
      PTranscript s =
        verifier_header_messages fr f_fri_roots f_final as dg
          composition_fri_roots final @ rest \<and>
      length f_fri_roots = ceil_log clength \<and>
      length as = length spec \<and>
      length composition_fri_roots = ceil_log (to_nat dg + 1)"

definition merkle_root_binds_table
  :: "'f \<Rightarrow> 'f list \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "merkle_root_binds_table rt table s \<longleftrightarrow>
      (\<exists>tree :: 'f tree. created_tree table tree s \<and> rt = value tree)"

definition merkle_root_binding_collision
  :: "'f \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "merkle_root_binding_collision rt s \<longleftrightarrow>
      (\<exists>table table'.
        merkle_root_binds_table rt table s \<and>
        merkle_root_binds_table rt table' s \<and>
        table \<noteq> table')"

definition hash_map_output_collision
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "hash_map_output_collision s \<longleftrightarrow>
      (\<exists>(x :: 'f protocol_hash_input) (y :: 'f protocol_hash_input) z.
        x \<noteq> y \<and>
        fmlookup (HashMap s) x = Some z \<and>
        fmlookup (HashMap s) y = Some z)"

definition hash_map_output_values
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f set"
  where
    "hash_map_output_values s =
      {z. \<exists>x :: 'f protocol_hash_input. fmlookup (HashMap s) x = Some z}"

lemma hash_map_output_values_verifier_initial_state[simp]:
  "hash_map_output_values (verifier_initial_state tr) = {}"
  unfolding hash_map_output_values_def by simp

lemma merkle_root_binding_collisionI:
  assumes "merkle_root_binds_table rt table s"
    and "merkle_root_binds_table rt table' s"
    and "table \<noteq> table'"
  shows "merkle_root_binding_collision rt s"
  using assms unfolding merkle_root_binding_collision_def by blast

lemma merkle_root_binds_table_unique_if_no_collision:
  assumes "\<not> merkle_root_binding_collision rt s"
    and "merkle_root_binds_table rt table s"
    and "merkle_root_binds_table rt table' s"
  shows "table = table'"
  using assms unfolding merkle_root_binding_collision_def by blast

lemma merkle_root_binds_table_mono:
  assumes bind: "merkle_root_binds_table rt table s"
    and ext: "s \<le> t"
  shows "merkle_root_binds_table rt table t"
proof -
  from bind obtain tree where
    created: "created_tree table tree s"
    and root: "rt = value tree"
    unfolding merkle_root_binds_table_def by blast
  have "created_tree table tree t"
    by (rule created_tree_mono[OF created ext])
  then show ?thesis
    unfolding merkle_root_binds_table_def
    using root by blast
qed

definition hash_maps_compatible
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "hash_maps_compatible s t \<longleftrightarrow>
      (\<forall>x y z.
        fmlookup (HashMap s) x = Some y \<longrightarrow>
        fmlookup (HashMap t) x = Some z \<longrightarrow>
        y = z)"

definition hash_map_value_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "hash_map_value_conflict s t \<longleftrightarrow>
      (\<exists>x y z.
        fmlookup (HashMap s) x = Some y \<and>
        fmlookup (HashMap t) x = Some z \<and>
        y \<noteq> z)"

lemma hash_maps_compatible_iff_no_value_conflict:
  "hash_maps_compatible s t \<longleftrightarrow> \<not> hash_map_value_conflict s t"
  unfolding hash_maps_compatible_def hash_map_value_conflict_def by blast

lemma hash_map_value_conflict_sym:
  assumes "hash_map_value_conflict s t"
  shows "hash_map_value_conflict t s"
  using assms unfolding hash_map_value_conflict_def by blast

lemma hash_maps_compatible_sym:
  assumes "hash_maps_compatible s t"
  shows "hash_maps_compatible t s"
  using assms
  unfolding hash_maps_compatible_iff_no_value_conflict
  using hash_map_value_conflict_sym by blast

lemma hash_map_value_conflict_no_common_extension:
  assumes conflict: "hash_map_value_conflict s t"
    and s_ext: "s \<le> u"
    and t_ext: "t \<le> u"
  shows False
proof -
  from conflict obtain x y z where
    s_lookup: "fmlookup (HashMap s) x = Some y"
    and t_lookup: "fmlookup (HashMap t) x = Some z"
    and neq: "y \<noteq> z"
    unfolding hash_map_value_conflict_def by blast
  have u_y: "fmlookup (HashMap u) x = Some y"
    by (rule hash_extension_lookup[OF s_lookup s_ext])
  have u_z: "fmlookup (HashMap u) x = Some z"
    by (rule hash_extension_lookup[OF t_lookup t_ext])
  show False
    using u_y u_z neq by simp
qed

lemma common_extension_imp_no_hash_map_value_conflict:
  assumes s_ext: "s \<le> u"
    and t_ext: "t \<le> u"
  shows "\<not> hash_map_value_conflict s t"
  using hash_map_value_conflict_no_common_extension[OF _ s_ext t_ext] by blast

lemma hash_map_value_conflict_blocks_clean_merge_obligation:
  assumes "hash_map_value_conflict s t"
  shows "\<not> (hash_maps_compatible s t \<and>
    \<not> hash_map_output_collision (hash_state_merge s t))"
  using assms unfolding hash_maps_compatible_iff_no_value_conflict by simp

fun merkle_hash_key :: "'f protocol_hash_input \<Rightarrow> bool"
  where
    "merkle_hash_key (MerkleLeaf _) \<longleftrightarrow> True"
  | "merkle_hash_key (MerkleNode _ _) \<longleftrightarrow> True"
  | "merkle_hash_key (FiatShamirChallenge _) \<longleftrightarrow> False"
  | "merkle_hash_key (TraceFriChallenge _ _) \<longleftrightarrow> False"
  | "merkle_hash_key (CompositionFriChallenge _ _) \<longleftrightarrow> False"
  | "merkle_hash_key (AlphaChallenge _ _) \<longleftrightarrow> False"
  | "merkle_hash_key (QueryIndexChallenge _ _) \<longleftrightarrow> False"

definition merkle_hash_maps_compatible
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "merkle_hash_maps_compatible s t \<longleftrightarrow>
      (\<forall>x y z.
        merkle_hash_key x \<longrightarrow>
        fmlookup (HashMap s) x = Some y \<longrightarrow>
        fmlookup (HashMap t) x = Some z \<longrightarrow>
        y = z)"

definition merkle_hash_value_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "merkle_hash_value_conflict s t \<longleftrightarrow>
      (\<exists>x y z.
        merkle_hash_key x \<and>
        fmlookup (HashMap s) x = Some y \<and>
        fmlookup (HashMap t) x = Some z \<and>
        y \<noteq> z)"

lemma merkle_hash_maps_compatible_iff_no_value_conflict:
  "merkle_hash_maps_compatible s t \<longleftrightarrow>
    \<not> merkle_hash_value_conflict s t"
  unfolding merkle_hash_maps_compatible_def merkle_hash_value_conflict_def
  by blast

lemma merkle_hash_value_conflict_sym:
  assumes "merkle_hash_value_conflict s t"
  shows "merkle_hash_value_conflict t s"
  using assms unfolding merkle_hash_value_conflict_def by blast

lemma merkle_hash_maps_compatible_sym:
  assumes "merkle_hash_maps_compatible s t"
  shows "merkle_hash_maps_compatible t s"
  using assms unfolding merkle_hash_maps_compatible_def by blast

definition merkle_hash_extends
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "merkle_hash_extends s t \<longleftrightarrow>
      (\<forall>x y.
        merkle_hash_key x \<longrightarrow>
        fmlookup (HashMap s) x = Some y \<longrightarrow>
        fmlookup (HashMap t) x = Some y)"

lemma merkle_hash_value_conflict_no_common_extension:
  assumes conflict: "merkle_hash_value_conflict s t"
    and ext_s: "merkle_hash_extends s u"
    and ext_t: "merkle_hash_extends t u"
  shows False
proof -
  from conflict obtain x y z where
    merkle: "merkle_hash_key x"
    and s_lookup: "fmlookup (HashMap s) x = Some y"
    and t_lookup: "fmlookup (HashMap t) x = Some z"
    and neq: "y \<noteq> z"
    unfolding merkle_hash_value_conflict_def by blast
  have u_y: "fmlookup (HashMap u) x = Some y"
    using ext_s merkle s_lookup unfolding merkle_hash_extends_def by blast
  have u_z: "fmlookup (HashMap u) x = Some z"
    using ext_t merkle t_lookup unfolding merkle_hash_extends_def by blast
  show False
    using u_y u_z neq by simp
qed

lemma common_merkle_extension_imp_no_merkle_hash_value_conflict:
  assumes ext_s: "merkle_hash_extends s u"
    and ext_t: "merkle_hash_extends t u"
  shows "\<not> merkle_hash_value_conflict s t"
  using merkle_hash_value_conflict_no_common_extension[OF _ ext_s ext_t]
  by blast

lemma merkle_hash_maps_compatible_if_common_merkle_extension:
  assumes ext_s: "merkle_hash_extends s u"
    and ext_t: "merkle_hash_extends t u"
  shows "merkle_hash_maps_compatible s t"
  using common_merkle_extension_imp_no_merkle_hash_value_conflict
      [OF ext_s ext_t]
  unfolding merkle_hash_maps_compatible_iff_no_value_conflict .

definition merkle_hash_state_merge
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme"
  where
    "merkle_hash_state_merge s t =
      s\<lparr>HashMap :=
        fmfilter merkle_hash_key (HashMap s) ++\<^sub>f
        fmfilter merkle_hash_key (HashMap t)\<rparr>"

lemma merkle_hash_state_merge_extends_right:
  "merkle_hash_extends t (merkle_hash_state_merge s t)"
  unfolding merkle_hash_extends_def merkle_hash_state_merge_def
  by (simp add: fmlookup_dom_iff)

lemma merkle_hash_state_merge_extends_left_if_compatible:
  assumes compatible: "merkle_hash_maps_compatible s t"
  shows "merkle_hash_extends s (merkle_hash_state_merge s t)"
  unfolding merkle_hash_extends_def
proof (intro allI impI)
  fix x y
  assume merkle: "merkle_hash_key x"
    and s_lookup: "fmlookup (HashMap s) x = Some y"
  show "fmlookup (HashMap (merkle_hash_state_merge s t)) x = Some y"
  proof (cases "fmlookup (HashMap t) x")
    case None
    then show ?thesis
      using merkle s_lookup
      unfolding merkle_hash_state_merge_def
      by (simp add: fmlookup_dom_iff)
  next
    case (Some z)
    have "z = y"
      using compatible merkle s_lookup Some
      unfolding merkle_hash_maps_compatible_def by blast
    then show ?thesis
      using merkle Some
      unfolding merkle_hash_state_merge_def
      by (simp add: fmlookup_dom_iff)
  qed
qed

lemma merkle_hash_state_merge_lookupD:
  assumes lookup:
    "fmlookup (HashMap (merkle_hash_state_merge s t)) x = Some z"
  obtains
      "merkle_hash_key x" "fmlookup (HashMap s) x = Some z"
    | "merkle_hash_key x" "fmlookup (HashMap t) x = Some z"
proof -
  have merkle: "merkle_hash_key x"
    using lookup
    unfolding merkle_hash_state_merge_def
    by (cases "merkle_hash_key x") auto
  show ?thesis
  proof (cases "fmlookup (HashMap t) x")
    case (Some z')
    then have z_eq: "z' = z"
      using lookup merkle
      unfolding merkle_hash_state_merge_def
      by (simp add: fmlookup_dom_iff)
    show ?thesis
      by (rule that(2)[OF merkle Some[unfolded z_eq]])
  next
    case None
    have s_lookup: "fmlookup (HashMap s) x = Some z"
      using lookup merkle None
      unfolding merkle_hash_state_merge_def
      by (simp add: fmlookup_dom_iff)
    show ?thesis
      by (rule that(1)[OF merkle s_lookup])
  qed
qed

lemma merkle_hash_state_merge_clean_if_common_clean_merkle_extension:
  assumes ext_s: "merkle_hash_extends s u"
    and ext_t: "merkle_hash_extends t u"
    and clean: "\<not> hash_map_output_collision u"
  shows "\<not> hash_map_output_collision (merkle_hash_state_merge s t)"
proof
  assume collision: "hash_map_output_collision (merkle_hash_state_merge s t)"
  then obtain x y z where neq: "x \<noteq> y"
    and x_lookup:
      "fmlookup (HashMap (merkle_hash_state_merge s t)) x = Some z"
    and y_lookup:
      "fmlookup (HashMap (merkle_hash_state_merge s t)) y = Some z"
    unfolding hash_map_output_collision_def by blast
  have x_lookup_u: "fmlookup (HashMap u) x = Some z"
  proof -
    from x_lookup show ?thesis
    proof (rule merkle_hash_state_merge_lookupD)
      assume merkle: "merkle_hash_key x"
        and lookup_s: "fmlookup (HashMap s) x = Some z"
      show ?thesis
        using ext_s merkle lookup_s
        unfolding merkle_hash_extends_def by blast
    next
      assume merkle: "merkle_hash_key x"
        and lookup_t: "fmlookup (HashMap t) x = Some z"
      show ?thesis
        using ext_t merkle lookup_t
        unfolding merkle_hash_extends_def by blast
    qed
  qed
  have y_lookup_u: "fmlookup (HashMap u) y = Some z"
  proof -
    from y_lookup show ?thesis
    proof (rule merkle_hash_state_merge_lookupD)
      assume merkle: "merkle_hash_key y"
        and lookup_s: "fmlookup (HashMap s) y = Some z"
      show ?thesis
        using ext_s merkle lookup_s
        unfolding merkle_hash_extends_def by blast
    next
      assume merkle: "merkle_hash_key y"
        and lookup_t: "fmlookup (HashMap t) y = Some z"
      show ?thesis
        using ext_t merkle lookup_t
        unfolding merkle_hash_extends_def by blast
    qed
  qed
  have "hash_map_output_collision u"
    unfolding hash_map_output_collision_def
    using neq x_lookup_u y_lookup_u by blast
  then show False
    using clean by contradiction
qed

lemma common_clean_merkle_extension_imp_pairwise_merkle_clean:
  assumes ext_s: "merkle_hash_extends s u"
    and ext_t: "merkle_hash_extends t u"
    and clean: "\<not> hash_map_output_collision u"
  shows
    "\<not> merkle_hash_value_conflict s t \<and>
     \<not> hash_map_output_collision (merkle_hash_state_merge s t)"
  using common_merkle_extension_imp_no_merkle_hash_value_conflict
      [OF ext_s ext_t]
    merkle_hash_state_merge_clean_if_common_clean_merkle_extension
      [OF ext_s ext_t clean]
  by simp

definition merkle_hash_cross_output_collision
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "merkle_hash_cross_output_collision s t \<longleftrightarrow>
      (\<exists>x y z.
        merkle_hash_key x \<and> merkle_hash_key y \<and> x \<noteq> y \<and>
        ((fmlookup (HashMap s) x = Some z \<and>
          fmlookup (HashMap t) y = Some z) \<or>
         (fmlookup (HashMap t) x = Some z \<and>
          fmlookup (HashMap s) y = Some z)))"

definition merkle_hash_pairwise_coupling_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "merkle_hash_pairwise_coupling_bad s t \<longleftrightarrow>
      merkle_hash_value_conflict s t \<or>
      merkle_hash_cross_output_collision s t"

lemma merkle_hash_cross_output_collision_sym:
  assumes "merkle_hash_cross_output_collision s t"
  shows "merkle_hash_cross_output_collision t s"
  using assms unfolding merkle_hash_cross_output_collision_def by blast

lemma merkle_hash_pairwise_coupling_bad_sym:
  assumes "merkle_hash_pairwise_coupling_bad s t"
  shows "merkle_hash_pairwise_coupling_bad t s"
  using assms
  unfolding merkle_hash_pairwise_coupling_bad_def
  using merkle_hash_value_conflict_sym
    merkle_hash_cross_output_collision_sym by blast

lemma merkle_hash_state_merge_collision_imp_local_or_cross:
  assumes collision:
    "hash_map_output_collision (merkle_hash_state_merge s t)"
  shows
    "hash_map_output_collision s \<or>
     hash_map_output_collision t \<or>
     merkle_hash_cross_output_collision s t"
proof -
  from collision obtain x y z where neq: "x \<noteq> y"
    and x_lookup:
      "fmlookup (HashMap (merkle_hash_state_merge s t)) x = Some z"
    and y_lookup:
      "fmlookup (HashMap (merkle_hash_state_merge s t)) y = Some z"
    unfolding hash_map_output_collision_def by blast
  from x_lookup consider
      (xs) "merkle_hash_key x" "fmlookup (HashMap s) x = Some z"
    | (xt) "merkle_hash_key x" "fmlookup (HashMap t) x = Some z"
    by (rule merkle_hash_state_merge_lookupD)
  then show ?thesis
  proof cases
    case xs
    from y_lookup consider
        (ys) "merkle_hash_key y" "fmlookup (HashMap s) y = Some z"
      | (yt) "merkle_hash_key y" "fmlookup (HashMap t) y = Some z"
      by (rule merkle_hash_state_merge_lookupD)
    then show ?thesis
    proof cases
      case ys
      have "hash_map_output_collision s"
        unfolding hash_map_output_collision_def
        using neq xs ys by blast
      then show ?thesis by blast
    next
      case yt
      have "merkle_hash_cross_output_collision s t"
        unfolding merkle_hash_cross_output_collision_def
        using neq xs yt by blast
      then show ?thesis by blast
    qed
  next
    case xt
    from y_lookup consider
        (ys) "merkle_hash_key y" "fmlookup (HashMap s) y = Some z"
      | (yt) "merkle_hash_key y" "fmlookup (HashMap t) y = Some z"
      by (rule merkle_hash_state_merge_lookupD)
    then show ?thesis
    proof cases
      case ys
      have "merkle_hash_cross_output_collision s t"
        unfolding merkle_hash_cross_output_collision_def
        using neq xt ys by blast
      then show ?thesis by blast
    next
      case yt
      have "hash_map_output_collision t"
        unfolding hash_map_output_collision_def
        using neq xt yt by blast
      then show ?thesis by blast
    qed
  qed
qed

lemma merkle_hash_pairwise_bad_imp_local_collision_or_coupling_bad:
  assumes pair_bad:
    "merkle_hash_value_conflict s t \<or>
     hash_map_output_collision (merkle_hash_state_merge s t)"
  shows
    "hash_map_output_collision s \<or>
     hash_map_output_collision t \<or>
     merkle_hash_pairwise_coupling_bad s t"
proof (cases "merkle_hash_value_conflict s t")
  case True
  then show ?thesis
    unfolding merkle_hash_pairwise_coupling_bad_def by blast
next
  case False
  then have merge_collision:
    "hash_map_output_collision (merkle_hash_state_merge s t)"
    using pair_bad by blast
  from merkle_hash_state_merge_collision_imp_local_or_cross
      [OF merge_collision]
  show ?thesis
    unfolding merkle_hash_pairwise_coupling_bad_def by blast
qed

definition hash_state_merge
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f, 'a) protocol_channel_scheme"
  where
    "hash_state_merge s t =
      s\<lparr>HashMap := HashMap s ++\<^sub>f HashMap t\<rparr>"

lemma hash_state_merge_extends_right:
  "t \<le> hash_state_merge s t"
  unfolding hash_state_merge_def less_eq_hash_ext_def less_eq_fmap_def
  by auto

lemma hash_state_merge_extends_left_if_compatible:
  assumes compatible: "hash_maps_compatible s t"
  shows "s \<le> hash_state_merge s t"
proof -
  have lookup:
    "\<And>x y. fmlookup (HashMap s) x = Some y \<Longrightarrow>
      fmlookup (HashMap (hash_state_merge s t)) x = Some y"
  proof -
    fix x y
    assume s_lookup: "fmlookup (HashMap s) x = Some y"
    show "fmlookup (HashMap (hash_state_merge s t)) x = Some y"
    proof (cases "x |\<in>| fmdom (HashMap t)")
      case True
      then obtain z where t_lookup: "fmlookup (HashMap t) x = Some z"
        unfolding fmlookup_dom_iff by blast
      have "z = y"
        using compatible s_lookup t_lookup
        unfolding hash_maps_compatible_def by blast
      then show ?thesis
        using True t_lookup
        unfolding hash_state_merge_def by simp
    next
      case False
      then show ?thesis
        using s_lookup unfolding hash_state_merge_def by simp
    qed
  qed
  show ?thesis
    unfolding less_eq_hash_ext_def less_eq_fmap_def
  proof
    fix x
    show "fmlookup (HashMap s) x = None \<or>
      fmlookup (HashMap s) x =
        fmlookup (HashMap (hash_state_merge s t)) x"
    proof (cases "fmlookup (HashMap s) x")
      case None
      then show ?thesis by simp
    next
      case (Some y)
      then have "fmlookup (HashMap (hash_state_merge s t)) x = Some y"
        by (rule lookup)
      then show ?thesis
        using Some by simp
    qed
  qed
qed

lemma hash_maps_compatible_if_common_extension:
  assumes s_ext: "s \<le> u"
    and t_ext: "t \<le> u"
  shows "hash_maps_compatible s t"
  unfolding hash_maps_compatible_def
proof (intro allI impI)
  fix x y z
  assume s_lookup: "fmlookup (HashMap s) x = Some y"
    and t_lookup: "fmlookup (HashMap t) x = Some z"
  have u_y: "fmlookup (HashMap u) x = Some y"
    by (rule hash_extension_lookup[OF s_lookup s_ext])
  have u_z: "fmlookup (HashMap u) x = Some z"
    by (rule hash_extension_lookup[OF t_lookup t_ext])
  show "y = z"
    using u_y u_z by simp
qed

lemma hash_state_merge_le_common_extension:
  assumes s_ext: "s \<le> u"
    and t_ext: "t \<le> u"
  shows "hash_state_merge s t \<le> u"
  unfolding less_eq_hash_ext_def less_eq_fmap_def
proof
  fix x
  show "fmlookup (HashMap (hash_state_merge s t)) x = None \<or>
    fmlookup (HashMap (hash_state_merge s t)) x = fmlookup (HashMap u) x"
  proof (cases "x |\<in>| fmdom (HashMap t)")
    case True
    then obtain z where t_lookup: "fmlookup (HashMap t) x = Some z"
      unfolding fmlookup_dom_iff by blast
    have merge_lookup:
      "fmlookup (HashMap (hash_state_merge s t)) x = Some z"
      using True t_lookup unfolding hash_state_merge_def by simp
    have u_lookup: "fmlookup (HashMap u) x = Some z"
      by (rule hash_extension_lookup[OF t_lookup t_ext])
    show ?thesis
      using merge_lookup u_lookup by simp
  next
    case False
    show ?thesis
    proof (cases "fmlookup (HashMap s) x")
      case None
      then have "fmlookup (HashMap (hash_state_merge s t)) x = None"
        using False unfolding hash_state_merge_def by simp
      then show ?thesis
        by simp
    next
      case (Some y)
      then have merge_lookup:
        "fmlookup (HashMap (hash_state_merge s t)) x = Some y"
        using False unfolding hash_state_merge_def by simp
      have u_lookup: "fmlookup (HashMap u) x = Some y"
        by (rule hash_extension_lookup[OF Some s_ext])
      show ?thesis
        using merge_lookup u_lookup by simp
    qed
  qed
qed

lemma hash_state_merge_clean_if_common_clean_extension:
  assumes s_ext: "s \<le> u"
    and t_ext: "t \<le> u"
    and clean: "\<not> hash_map_output_collision u"
  shows "\<not> hash_map_output_collision (hash_state_merge s t)"
proof
  assume collision: "hash_map_output_collision (hash_state_merge s t)"
  have merge_ext: "hash_state_merge s t \<le> u"
    by (rule hash_state_merge_le_common_extension[OF s_ext t_ext])
  from collision obtain x y z where neq: "x \<noteq> y"
    and x_lookup:
      "fmlookup (HashMap (hash_state_merge s t)) x = Some z"
    and y_lookup:
      "fmlookup (HashMap (hash_state_merge s t)) y = Some z"
    unfolding hash_map_output_collision_def by blast
  have x_lookup_u: "fmlookup (HashMap u) x = Some z"
    by (rule hash_extension_lookup[OF x_lookup merge_ext])
  have y_lookup_u: "fmlookup (HashMap u) y = Some z"
    by (rule hash_extension_lookup[OF y_lookup merge_ext])
  have "hash_map_output_collision u"
    unfolding hash_map_output_collision_def
    using neq x_lookup_u y_lookup_u by blast
  then show False
    using clean by contradiction
qed

lemma hash_map_output_collisionI:
  fixes x y :: "'f protocol_hash_input"
  assumes "x \<noteq> y"
    and "fmlookup (HashMap s) x = Some z"
    and "fmlookup (HashMap s) y = Some z"
  shows "hash_map_output_collision s"
  using assms unfolding hash_map_output_collision_def by blast

lemma hash_map_output_collision_merkle_leafI:
  assumes "x \<noteq> y"
    and "fmlookup (HashMap s) (MerkleLeaf x) = Some z"
    and "fmlookup (HashMap s) (MerkleLeaf y) = Some z"
  shows "hash_map_output_collision s"
  by (rule hash_map_output_collisionI[OF _ assms(2,3)])
    (use assms(1) in simp)

lemma hash_map_output_collision_merkle_nodeI:
  assumes "(x1, x2) \<noteq> (y1, y2)"
    and "fmlookup (HashMap s) (MerkleNode x1 x2) = Some z"
    and "fmlookup (HashMap s) (MerkleNode y1 y2) = Some z"
  shows "hash_map_output_collision s"
  by (rule hash_map_output_collisionI[OF _ assms(2,3)])
    (use assms(1) in auto)

lemma hash_map_output_collision_merkle_leaf_nodeI:
  assumes "fmlookup (HashMap s) (MerkleLeaf x) = Some z"
    and "fmlookup (HashMap s) (MerkleNode y1 y2) = Some z"
  shows "hash_map_output_collision s"
  by (rule hash_map_output_collisionI[OF _ assms])
    simp

lemma hash_map_output_valuesI:
  fixes x :: "'f protocol_hash_input"
  assumes "fmlookup (HashMap s) x = Some z"
  shows "z \<in> hash_map_output_values s"
  using assms unfolding hash_map_output_values_def by blast

lemma hash_map_output_values_alt_def:
  "hash_map_output_values s =
    (\<lambda>x. the (fmlookup (HashMap s) x)) ` fmdom' (HashMap s)"
  unfolding hash_map_output_values_def
proof
  show "{z. \<exists>x. fmlookup (HashMap s) x = Some z}
      \<subseteq> (\<lambda>x. the (fmlookup (HashMap s) x)) ` fmdom' (HashMap s)"
  proof
    fix z
    assume "z \<in> {z. \<exists>x. fmlookup (HashMap s) x = Some z}"
    then obtain x where lookup: "fmlookup (HashMap s) x = Some z"
      by blast
    have "x \<in> fmdom' (HashMap s)"
      using lookup by (simp add: fmlookup_dom'_iff)
    moreover have "the (fmlookup (HashMap s) x) = z"
      using lookup by simp
    ultimately show "z \<in>
      (\<lambda>x. the (fmlookup (HashMap s) x)) ` fmdom' (HashMap s)"
      by blast
  qed
  show "(\<lambda>x. the (fmlookup (HashMap s) x)) ` fmdom' (HashMap s)
      \<subseteq> {z. \<exists>x. fmlookup (HashMap s) x = Some z}"
    by (auto simp: fmlookup_dom'_iff)
qed

lemma finite_hash_map_output_values[simp]:
  "finite (hash_map_output_values s)"
  unfolding hash_map_output_values_alt_def by simp

lemma card_hash_map_output_values_le_fmdom:
  "card (hash_map_output_values s) \<le> card (fmdom' (HashMap s))"
  unfolding hash_map_output_values_alt_def
  by (rule card_image_le) simp

lemma hash_map_output_values_after_update_subset:
  fixes x :: "'f protocol_hash_input"
  shows
    "hash_map_output_values
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>) \<subseteq>
      insert y (hash_map_output_values s)"
  unfolding hash_map_output_values_def
  by auto

lemma card_hash_map_output_values_after_update_le:
  fixes x :: "'f protocol_hash_input"
  shows
    "card (hash_map_output_values
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)) \<le>
      Suc (card (hash_map_output_values s))"
proof -
  have "card (hash_map_output_values
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)) \<le>
      card (insert y (hash_map_output_values s))"
    by (rule card_mono)
      (simp_all add: hash_map_output_values_after_update_subset)
  also have "... \<le> Suc (card (hash_map_output_values s))"
    by (simp add: card_insert_if)
  finally show ?thesis .
qed

lemma hash_map_output_collision_after_fresh_updateD:
  fixes x :: "'f protocol_hash_input"
  assumes clean: "\<not> hash_map_output_collision s"
    and fresh: "fmlookup (HashMap s) x = None"
    and collision:
      "hash_map_output_collision
        (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
  shows "y \<in> hash_map_output_values s"
proof -
  obtain a b z where neq: "a \<noteq> b"
    and a_lookup:
      "fmlookup (fmupd x y (HashMap s)) a = Some z"
    and b_lookup:
      "fmlookup (fmupd x y (HashMap s)) b = Some z"
    using collision unfolding hash_map_output_collision_def by auto
  show ?thesis
  proof (cases "a = x")
    case True
    then have z_y: "z = y"
      using a_lookup by simp
    have b_ne_x: "b \<noteq> x"
      using neq True by simp
    have "fmlookup (HashMap s) b = Some y"
      using b_lookup b_ne_x z_y by simp
    then show ?thesis
      by (rule hash_map_output_valuesI)
  next
    case a_ne_x: False
    show ?thesis
    proof (cases "b = x")
      case True
      then have z_y: "z = y"
        using b_lookup by simp
      have "fmlookup (HashMap s) a = Some y"
        using a_lookup a_ne_x z_y by simp
      then show ?thesis
        by (rule hash_map_output_valuesI)
    next
      case b_ne_x: False
      have a_old: "fmlookup (HashMap s) a = Some z"
        using a_lookup a_ne_x by simp
      have b_old: "fmlookup (HashMap s) b = Some z"
        using b_lookup b_ne_x by simp
      have "hash_map_output_collision s"
        by (rule hash_map_output_collisionI[OF neq a_old b_old])
      then show ?thesis
        using clean by contradiction
    qed
  qed
qed

lemma no_hash_map_output_collision_after_known_update:
  fixes x :: "'f protocol_hash_input"
  assumes clean: "\<not> hash_map_output_collision s"
    and known: "fmlookup (HashMap s) x = Some y"
  shows "\<not> hash_map_output_collision
    (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
proof
  assume collision:
    "hash_map_output_collision
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
  obtain a b z where neq: "a \<noteq> b"
    and a_lookup:
      "fmlookup (fmupd x y (HashMap s)) a = Some z"
    and b_lookup:
      "fmlookup (fmupd x y (HashMap s)) b = Some z"
    using collision unfolding hash_map_output_collision_def by auto
  have a_old: "fmlookup (HashMap s) a = Some z"
    using a_lookup known by (cases "a = x") simp_all
  have b_old: "fmlookup (HashMap s) b = Some z"
    using b_lookup known by (cases "b = x") simp_all
  have "hash_map_output_collision s"
    by (rule hash_map_output_collisionI[OF neq a_old b_old])
  then show False
    using clean by contradiction
qed

lemma dist_expect_uniform_fUNIV_indicator:
  fixes S :: "'f set"
  shows
    "dist_expect (dist_uniform (fUNIV :: 'f fset))
      (\<lambda>x. if x \<in> S then 1 else 0) =
      nnreal (card S) / nnreal size"
proof -
  let ?U = "(fUNIV :: 'f fset)"
  let ?w = "1 / nnreal (CARD('f))"
  let ?B = "((\<lambda>x :: 'f. (x, ?w)) |`| ?U)"

  have U_nonempty: "?U \<noteq> {||}"
  proof -
    have "(undefined :: 'f) |\<in>| ?U"
      by simp
    then show ?thesis
      by auto
  qed
  have fcard_U: "fcard ?U = CARD('f)"
    by (simp add: fcard.rep_eq)
  have total_nonzero:
    "fsum snd ((\<lambda>x :: 'f. (x, 1::prob)) |`| ?U) \<noteq> 0"
    using fsum_snd_uniform_ones[of ?U] fcard_U by simp
  have dist_eq:
    "dist (dist_uniform ?U) = map_of ?B"
    unfolding dist_uniform_def dist_of_fset.rep_eq map_of_fset_def
    using norm_fset_uniform_ones[OF U_nonempty] total_nonzero fcard_U
    by (simp add: Let_def)

  have lookup:
    "dist (dist_uniform ?U) x = Some ?w" for x :: 'f
  proof -
    have mem: "(x, ?w) |\<in>| ?B"
      by simp
    have uniq:
      "\<And>y z. (x, y) |\<in>| ?B \<Longrightarrow> (x, z) |\<in>| ?B \<Longrightarrow> y = z"
      by auto
    have val: "map_of_val ?B x = ?w"
      by (rule map_of_val_unique_key[OF uniq mem])
    have "x |\<in>| fimage fst ?B"
      using mem by force
    then have "map_of ?B x = Some (map_of_val ?B x)"
      unfolding map_of_def by simp
    also have "... = Some ?w"
      using val by simp
    finally show ?thesis
      using dist_eq by simp
  qed

  have dom_eq: "dom (dist (dist_uniform ?U)) = (UNIV :: 'f set)"
    using lookup by auto

  have "dist_expect (dist_uniform ?U) (\<lambda>x. if x \<in> S then 1 else 0) =
      (\<Sum>x\<in>UNIV. ?w * (if x \<in> S then 1 else 0))"
    unfolding dist_expect_def dom_eq
    by (intro sum.cong refl) (simp add: lookup)
  also have "... = (\<Sum>x\<in>UNIV. if x \<in> S then ?w else 0)"
    by (intro sum.cong refl) (simp split: if_splits)
  also have "... = (\<Sum>x\<in>S. ?w)"
  proof -
    have "(\<Sum>x\<in>UNIV. if x \<in> S then ?w else 0) =
        (\<Sum>x\<in>UNIV \<inter> S. ?w)"
      by (subst sum.inter_restrict[symmetric]) simp_all
    also have "... = (\<Sum>x\<in>S. ?w)"
      by simp
    finally show ?thesis .
  qed
  also have "... = (\<Sum>x\<in>S. (1::prob)) / nnreal (CARD('f))"
    by (rule sum_divide_nnreal) simp
  also have "... = nnreal (card S) / nnreal (CARD('f))"
    by (simp add: sum_1_nnreal)
  also have "... = nnreal (card S) / nnreal size"
    using size_card by simp
  finally show ?thesis .
qed

lemma dist_expect_hash_dist_fresh_output_values:
  fixes x :: "'f protocol_hash_input"
  assumes fresh: "fmlookup (HashMap s) x = None"
  shows
    "dist_expect (hash_dist x s)
      (\<lambda>y. if y \<in> hash_map_output_values s then 1 else 0) =
      nnreal (card (hash_map_output_values s)) / nnreal size"
  using fresh
  unfolding hash_dist_def option_default_dist_def hash_default_def
  by (simp add: dist_expect_uniform_fUNIV_indicator)

lemma dist_expect_hash_dist_fresh_indicator:
  fixes x :: "'f protocol_hash_input"
    and s :: "('f, 'a) protocol_channel_scheme"
  assumes fresh: "fmlookup (HashMap s) x = None"
  shows
    "dist_expect (hash_dist x s) (\<lambda>y. if y \<in> B then 1 else 0) =
      nnreal (card B) / nnreal size"
  using fresh
  unfolding hash_dist_def option_default_dist_def hash_default_def
  by (simp add: dist_expect_uniform_fUNIV_indicator)

lemma wp_hash_fresh_set:
  fixes x :: "'f protocol_hash_input"
    and s :: "('f, 'a) protocol_channel_scheme"
  assumes fresh: "fmlookup (HashMap s) x = None"
  shows
    "wp_event (hash x) (\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (y, _) \<Rightarrow> y \<in> B) s =
      nnreal (card B) / nnreal size"
  unfolding wp_event_def
  by (simp add: wp_hash dist_expect_hash_dist_fresh_indicator[OF fresh])

lemma wp_hash_fresh_singleton_outcome:
  fixes x :: "'f protocol_hash_input"
    and s :: "('f, 'a) protocol_channel_scheme"
  assumes fresh: "fmlookup (HashMap s) x = None"
  shows
    "wp_event (hash x)
      (\<lambda>out. out =
        Some (y, s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)) s =
      1 / nnreal size"
proof -
  have indicator:
    "(\<lambda>xa. if xa = y \<and>
        s\<lparr>HashMap := fmupd x xa (HashMap s)\<rparr> =
        s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>
      then 1 else 0 :: prob) =
     (\<lambda>xa. if xa \<in> {y} then 1 else 0)"
    by auto
  have "wp_event (hash x)
      (\<lambda>out. out =
        Some (y, s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)) s =
    dist_expect (hash_dist x s) (\<lambda>xa. if xa \<in> {y} then 1 else 0)"
    unfolding wp_event_def by (simp add: wp_hash indicator)
  also have "... = nnreal (card ({y} :: 'f set)) / nnreal size"
    by (rule dist_expect_hash_dist_fresh_indicator[OF fresh])
  also have "... = 1 / nnreal size"
    by simp
  finally show ?thesis .
qed

lemma hash_fresh_outcome:
  fixes x :: "'f protocol_hash_input"
    and s :: "('f, 'a) protocol_channel_scheme"
  assumes fresh: "fmlookup (HashMap s) x = None"
  shows
    "Some (y, s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>) \<in>
      set_dist (execute (hash x) s)"
proof -
  have positive:
    "0 < wp_event (hash x)
      (\<lambda>out. out =
        Some (y, s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)) s"
    using wp_hash_fresh_singleton_outcome[OF fresh, of y]
      size_card by simp
  then obtain out where support:
      "out \<in> set_dist (execute (hash x) s)"
    and out_eq:
      "out = Some (y, s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
    by (rule wp_event_pos_imp_exists_support)
  show ?thesis
    using support out_eq by simp
qed

lemma fresh_merkle_hash_has_pairwise_value_conflict:
  fixes x :: "'f protocol_hash_input"
    and s :: "('f, 'a) protocol_channel_scheme"
  assumes merkle: "merkle_hash_key x"
    and fresh: "fmlookup (HashMap s) x = None"
    and neq: "y \<noteq> z"
  shows
    "\<exists>t u.
      Some (y, t) \<in> set_dist (execute (hash x) s) \<and>
      Some (z, u) \<in> set_dist (execute (hash x) s) \<and>
      merkle_hash_value_conflict t u \<and>
      merkle_hash_pairwise_coupling_bad t u"
proof -
  let ?t = "s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>"
  let ?u = "s\<lparr>HashMap := fmupd x z (HashMap s)\<rparr>"
  have out_y: "Some (y, ?t) \<in> set_dist (execute (hash x) s)"
    by (rule hash_fresh_outcome[OF fresh])
  have out_z: "Some (z, ?u) \<in> set_dist (execute (hash x) s)"
    by (rule hash_fresh_outcome[OF fresh])
  have conflict: "merkle_hash_value_conflict ?t ?u"
    unfolding merkle_hash_value_conflict_def
    using merkle neq by auto
  then have coupling: "merkle_hash_pairwise_coupling_bad ?t ?u"
    unfolding merkle_hash_pairwise_coupling_bad_def by simp
  show ?thesis
    using out_y out_z conflict coupling by blast
qed

lemma wp_receive_tagged_random_field_element_fresh_set:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes fresh: "fmlookup (HashMap s) (tag (PState s)) = None"
  shows
    "wp_event (receive_tagged_random_field_element tag)
      (\<lambda>out. case out of None \<Rightarrow> False | Some (y, _) \<Rightarrow> y \<in> B) s =
      nnreal (card B) / nnreal size"
  unfolding wp_event_def receive_tagged_random_field_element_def
    protocol_receive_tagged_random_field_element_def
  by (simp add: wpsimps dist_expect_hash_dist_fresh_indicator[OF fresh])

lemma wp_receive_counted_tagged_random_field_element_fresh_set:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes fresh:
    "fmlookup (HashMap s) (tag (counter s) (PState s)) = None"
  shows
    "wp_event
      (protocol_receive_counted_tagged_random_field_element counter bump tag)
      (\<lambda>out. case out of None \<Rightarrow> False | Some (y, _) \<Rightarrow> y \<in> B) s =
      nnreal (card B) / nnreal size"
  unfolding wp_event_def protocol_receive_counted_tagged_random_field_element_def
  by (simp add: wpsimps dist_expect_hash_dist_fresh_indicator[OF fresh])

lemma wp_receive_alpha_challenge_fresh_set:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes fresh: "fmlookup (HashMap s) (AlphaChallenge (PAlphaCounter s) (PState s)) = None"
  shows
    "wp_event receive_alpha_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (y, _) \<Rightarrow> y \<in> B) s =
      nnreal (card B) / nnreal size"
  unfolding receive_alpha_challenge_def
  by (rule wp_receive_counted_tagged_random_field_element_fresh_set
      [where counter=PAlphaCounter
        and bump="\<lambda>s. s\<lparr>PAlphaCounter := Suc (PAlphaCounter s)\<rparr>"
        and tag=AlphaChallenge and B=B and s=s, OF fresh])

lemma wp_receive_query_index_challenge_fresh_set:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes fresh:
    "fmlookup (HashMap s) (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
  shows
    "wp_event receive_query_index_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (y, _) \<Rightarrow> y \<in> B) s =
      nnreal (card B) / nnreal size"
  unfolding receive_query_index_challenge_def
  by (rule wp_receive_counted_tagged_random_field_element_fresh_set
      [where counter=PQueryCounter
        and bump="\<lambda>s. s\<lparr>PQueryCounter := Suc (PQueryCounter s)\<rparr>"
        and tag=QueryIndexChallenge and B=B and s=s, OF fresh])

definition query_index_raw_preimage :: "nat set \<Rightarrow> 'f set"
  where
    "query_index_raw_preimage B =
      {raw. index (to_nat raw) \<in> B}"

definition query_index_nat_preimage :: "nat set \<Rightarrow> nat set"
  where
    "query_index_nat_preimage B =
      {n \<in> range to_nat. n mod query_sample_space_size \<in> B}"

lemma finite_query_index_raw_preimage[simp]:
  "finite (query_index_raw_preimage B)"
  unfolding query_index_raw_preimage_def by simp

lemma finite_query_index_nat_preimage[simp]:
  "finite (query_index_nat_preimage B)"
  unfolding query_index_nat_preimage_def by simp

lemma query_index_raw_preimage_image_to_nat:
  "to_nat ` query_index_raw_preimage B = query_index_nat_preimage B"
  unfolding query_index_raw_preimage_def query_index_nat_preimage_def
    index_def query_sample_space_size_def
  by auto

lemma card_query_index_raw_preimage_eq_nat_preimage:
  "card (query_index_raw_preimage B) = card (query_index_nat_preimage B)"
proof -
  have inj: "inj_on to_nat (query_index_raw_preimage B)"
    using to_nat_inj by (rule inj_on_subset) simp
  have "card (query_index_raw_preimage B) =
      card (to_nat ` query_index_raw_preimage B)"
    by (rule card_image[symmetric, OF inj])
  also have "... = card (query_index_nat_preimage B)"
    unfolding query_index_raw_preimage_image_to_nat ..
  finally show ?thesis .
qed

lemma wp_receive_query_index_challenge_fresh_index_set:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes fresh:
    "fmlookup (HashMap s) (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
  shows
    "wp_event receive_query_index_challenge
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B) s =
      nnreal (card (query_index_raw_preimage B)) / nnreal size"
proof -
  have event_eq:
    "(\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B) =
     (\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (raw, _) \<Rightarrow> raw \<in> query_index_raw_preimage B)"
    unfolding query_index_raw_preimage_def
    by (rule ext) (auto split: option.splits prod.splits)
  show ?thesis
    unfolding event_eq
    by (rule wp_receive_query_index_challenge_fresh_set[OF fresh])
qed

lemma card_mod_lessThan_dvd:
  assumes q_pos: "0 < q"
    and dvd: "q dvd N"
    and b_lt: "b < q"
  shows "card {n. n < N \<and> n mod q = b} = N div q"
proof -
  let ?A = "{0..<N div q}"
  let ?B = "{n. n < N \<and> n mod q = b}"
  have N_eq: "N = (N div q) * q"
    using dvd q_pos by (simp add: dvd_eq_mod_eq_0)
  have image_eq: "(\<lambda>k. k * q + b) ` ?A = ?B"
  proof
    show "(\<lambda>k. k * q + b) ` ?A \<subseteq> ?B"
    proof
      fix n
      assume "n \<in> (\<lambda>k. k * q + b) ` ?A"
      then obtain k where k_lt: "k < N div q" and n_eq: "n = k * q + b"
        by auto
      have "k * q + b < (N div q) * q"
      proof -
        have sk_le: "Suc k \<le> N div q"
          using k_lt by simp
        have skq_le: "Suc k * q \<le> (N div q) * q"
          by (rule mult_le_mono1[OF sk_le])
        have "k * q + b < k * q + q"
          using b_lt by simp
        also have "... = Suc k * q"
          by simp
        also have "... \<le> (N div q) * q"
          by (rule skq_le)
        finally show ?thesis .
      qed
      then have "n < N"
        using N_eq n_eq by simp
      moreover have "n mod q = b"
        using n_eq b_lt by simp
      ultimately show "n \<in> ?B"
        by simp
    qed
    show "?B \<subseteq> (\<lambda>k. k * q + b) ` ?A"
    proof
      fix n
      assume n_in: "n \<in> ?B"
      then have n_lt: "n < N" and n_mod: "n mod q = b"
        by simp_all
      have n_eq: "n = (n div q) * q + b"
        using div_mult_mod_eq[of n q] n_mod by simp
      have div_lt: "n div q < N div q"
      proof (rule ccontr)
        assume "\<not> n div q < N div q"
        then have ge: "N div q \<le> n div q"
          by simp
        have "N = (N div q) * q"
          by (rule N_eq)
        also have "... \<le> (n div q) * q"
          using ge by simp
        also have "... \<le> (n div q) * q + b"
          by simp
        also have "... = n"
          using n_eq by simp
        finally show False
          using n_lt by simp
      qed
      then show "n \<in> (\<lambda>k. k * q + b) ` ?A"
        using n_eq by auto
    qed
  qed
  have inj: "inj_on (\<lambda>k. k * q + b) ?A"
    using q_pos unfolding inj_on_def by auto
  have "card ?B = card ((\<lambda>k. k * q + b) ` ?A)"
    using image_eq by simp
  also have "... = card ?A"
    by (rule card_image[OF inj])
  also have "... = N div q"
    by simp
  finally show ?thesis .
qed

text \<open>
  Diagnostic divisible special case only.  The live sampler route uses the
  quotient/remainder formulas and envelopes in
  \<open>Soundness_Query_Index_Modulo_Bounds\<close>.
\<close>

lemma card_query_index_nat_preimage_uniform_range:
  assumes range_eq: "range to_nat = {0..<size}"
    and dvd: "query_sample_space_size dvd size"
    and subset: "B \<subseteq> query_sample_space"
  shows
    "card (query_index_nat_preimage B) =
      (size div query_sample_space_size) * card B"
proof -
  let ?q = query_sample_space_size
  let ?A = "\<lambda>b. {n. n < size \<and> n mod ?q = b}"
  have finite_space: "finite query_sample_space"
    unfolding query_sample_space_def by simp
  have finite_B: "finite B"
    by (rule finite_subset[OF subset finite_space])
  have B_lt: "\<And>b. b \<in> B \<Longrightarrow> b < ?q"
    using subset unfolding query_sample_space_def by auto
  have preimage_eq: "query_index_nat_preimage B = \<Union>(?A ` B)"
    unfolding query_index_nat_preimage_def range_eq by auto
  have finite_A: "\<forall>b\<in>B. finite (?A b)"
    by simp
  have disjoint:
    "\<forall>b\<in>B. \<forall>c\<in>B. b \<noteq> c \<longrightarrow> ?A b \<inter> ?A c = {}"
    by auto
  have "card (query_index_nat_preimage B) = card (\<Union>(?A ` B))"
    unfolding preimage_eq ..
  also have "... = (\<Sum>b\<in>B. card (?A b))"
    by (rule card_UN_disjoint[OF finite_B finite_A disjoint])
  also have "... = (\<Sum>b\<in>B. size div ?q)"
    by (rule sum.cong)
      (use B_lt in
        \<open>simp_all add: card_mod_lessThan_dvd[OF query_sample_space_size_pos dvd]\<close>)
  also have "... = (size div ?q) * card B"
    by simp
  finally show ?thesis .
qed

lemma wp_receive_trace_fri_challenge_fresh_set:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes fresh:
    "fmlookup (HashMap s) (TraceFriChallenge (PTraceFriCounter s) (PState s)) = None"
  shows
    "wp_event receive_trace_fri_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (y, _) \<Rightarrow> y \<in> B) s =
      nnreal (card B) / nnreal size"
  unfolding receive_trace_fri_challenge_def
  by (rule wp_receive_counted_tagged_random_field_element_fresh_set
      [where counter=PTraceFriCounter
        and bump="\<lambda>s. s\<lparr>PTraceFriCounter := Suc (PTraceFriCounter s)\<rparr>"
        and tag=TraceFriChallenge and B=B and s=s, OF fresh])

lemma wp_receive_composition_fri_challenge_fresh_set:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes fresh:
    "fmlookup (HashMap s) (CompositionFriChallenge (PCompositionFriCounter s) (PState s)) = None"
  shows
    "wp_event receive_composition_fri_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (y, _) \<Rightarrow> y \<in> B) s =
      nnreal (card B) / nnreal size"
  unfolding receive_composition_fri_challenge_def
  by (rule wp_receive_counted_tagged_random_field_element_fresh_set
      [where counter=PCompositionFriCounter
        and bump="\<lambda>s. s\<lparr>PCompositionFriCounter := Suc (PCompositionFriCounter s)\<rparr>"
        and tag=CompositionFriChallenge and B=B and s=s, OF fresh])

fun merkle_path_root_in_map
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f option"
  where
    "merkle_path_root_in_map s len idx leaf [] =
      fmlookup (HashMap s) (MerkleLeaf leaf)"
  | "merkle_path_root_in_map s len idx leaf (a # path) =
      (if idx < len div 2
       then case merkle_path_root_in_map s (len div 2) idx leaf path of
          None \<Rightarrow> None
        | Some x \<Rightarrow> fmlookup (HashMap s) (MerkleNode x a)
       else case merkle_path_root_in_map s (len div 2) (idx - len div 2)
          leaf path of
          None \<Rightarrow> None
        | Some x \<Rightarrow> fmlookup (HashMap s) (MerkleNode a x))"

lemma check_authentication_path_outcome_merkle_path_root:
  fixes root leaf :: 'f
    and s t u :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (root, t) \<in>
      set_dist (execute (check_authentication_path len idx leaf path) s)"
    and ext: "t \<le> u"
  shows "merkle_path_root_in_map u len idx leaf path = Some root"
  using outcome ext
  unfolding check_authentication_path_def protocol_check_authentication_path_def
proof (induction path arbitrary: len idx leaf s root t)
  case Nil
  then have hash_step:
    "Some (root, t) \<in> set_dist (execute (hash (MerkleLeaf leaf)) s)"
    by simp
  have lookup_t:
    "fmlookup (HashMap t) (MerkleLeaf leaf) = Some root"
    by (rule hash_outcome(2)[OF hash_step])
  show ?case
    using hash_extension_lookup[OF lookup_t Nil.prems(2)] by simp
next
  case (Cons a path)
  show ?case
  proof (cases "idx < len div 2")
    case True
    from Cons.prems(1) obtain child s1 where
      child_check:
        "Some (child, s1) \<in>
          set_dist (execute
            (protocol_merkle.check_authentication_path
              (len div 2) idx (MerkleLeaf leaf) path) s)"
      and root_hash:
        "Some (root, t) \<in>
          set_dist (execute (hash (MerkleNode child a)) s1)"
      using True by (auto elim!: set_dist_bindE)
    have s1_t: "s1 \<le> t"
      by (rule hash_outcome(1)[OF root_hash])
    have s1_u: "s1 \<le> u"
      using s1_t Cons.prems(2) by (meson hash_ext_trans)
    have child_root:
      "merkle_path_root_in_map u (len div 2) idx leaf path = Some child"
      by (rule Cons.IH[OF child_check s1_u])
    have lookup_t:
      "fmlookup (HashMap t) (MerkleNode child a) = Some root"
      by (rule hash_outcome(2)[OF root_hash])
    have lookup_u:
      "fmlookup (HashMap u) (MerkleNode child a) = Some root"
      by (rule hash_extension_lookup[OF lookup_t Cons.prems(2)])
    show ?thesis
      using True child_root lookup_u by simp
  next
    case False
    from Cons.prems(1) obtain child s1 where
      child_check:
        "Some (child, s1) \<in>
          set_dist (execute
            (protocol_merkle.check_authentication_path
              (len div 2) (idx - len div 2) (MerkleLeaf leaf) path) s)"
      and root_hash:
        "Some (root, t) \<in>
          set_dist (execute (hash (MerkleNode a child)) s1)"
      using False by (auto elim!: set_dist_bindE)
    have s1_t: "s1 \<le> t"
      by (rule hash_outcome(1)[OF root_hash])
    have s1_u: "s1 \<le> u"
      using s1_t Cons.prems(2) by (meson hash_ext_trans)
    have child_root:
      "merkle_path_root_in_map u (len div 2) (idx - len div 2) leaf path =
        Some child"
      by (rule Cons.IH[OF child_check s1_u])
    have lookup_t:
      "fmlookup (HashMap t) (MerkleNode a child) = Some root"
      by (rule hash_outcome(2)[OF root_hash])
    have lookup_u:
      "fmlookup (HashMap u) (MerkleNode a child) = Some root"
      by (rule hash_extension_lookup[OF lookup_t Cons.prems(2)])
    show ?thesis
      using False child_root lookup_u by simp
  qed
qed

lemma merkle_path_root_same_index_eq_or_hash_collision:
  fixes root leaf leaf' :: 'f
    and s :: "('f, 'a) protocol_channel_scheme"
  assumes root1:
      "merkle_path_root_in_map s len idx leaf path = Some root"
    and root2:
      "merkle_path_root_in_map s len idx leaf' path' = Some root"
  shows "(leaf = leaf' \<and> path = path') \<or> hash_map_output_collision s"
  using root1 root2
proof (induction path arbitrary: len idx leaf path' leaf' root)
  case Nil
  show ?case
  proof (cases path')
    case Nil
    show ?thesis
    proof (cases "leaf = leaf'")
      case True
      then show ?thesis
        using Nil by simp
    next
      case False
      have lookup_leaf: "fmlookup (HashMap s) (MerkleLeaf leaf) = Some root"
        using Nil.prems(1) by simp
      have lookup_leaf':
        "fmlookup (HashMap s) (MerkleLeaf leaf') = Some root"
        using Nil.prems(2) unfolding Nil by simp
      have "hash_map_output_collision s"
        by (rule hash_map_output_collision_merkle_leafI
            [OF False lookup_leaf lookup_leaf'])
      then show ?thesis by simp
    qed
  next
    case (Cons a rest)
    have lookup_leaf: "fmlookup (HashMap s) (MerkleLeaf leaf) = Some root"
      using Nil.prems(1) by simp
    have "hash_map_output_collision s"
    proof (cases "idx < len div 2")
      case True
      from Nil.prems(2)[unfolded Cons] True obtain child where
        lookup_node: "fmlookup (HashMap s) (MerkleNode child a) = Some root"
        by (auto split: option.splits)
      show ?thesis
        by (rule hash_map_output_collision_merkle_leaf_nodeI
            [OF lookup_leaf lookup_node])
    next
      case False
      from Nil.prems(2)[unfolded Cons] False obtain child where
        lookup_node: "fmlookup (HashMap s) (MerkleNode a child) = Some root"
        by (auto split: option.splits)
      show ?thesis
        by (rule hash_map_output_collision_merkle_leaf_nodeI
            [OF lookup_leaf lookup_node])
    qed
    then show ?thesis by simp
  qed
next
  case (Cons a path)
  show ?case
  proof (cases path')
    case Nil
    have lookup_leaf': "fmlookup (HashMap s) (MerkleLeaf leaf') = Some root"
      using Cons.prems(2) unfolding Nil by simp
    have "hash_map_output_collision s"
    proof (cases "idx < len div 2")
      case True
      from Cons.prems(1) True obtain child where
        lookup_node: "fmlookup (HashMap s) (MerkleNode child a) = Some root"
        by (auto split: option.splits)
      show ?thesis
        by (rule hash_map_output_collisionI
            [of "MerkleNode child a" "MerkleLeaf leaf'" s root])
          (use lookup_node lookup_leaf' in simp_all)
    next
      case False
      from Cons.prems(1) False obtain child where
        lookup_node: "fmlookup (HashMap s) (MerkleNode a child) = Some root"
        by (auto split: option.splits)
      show ?thesis
        by (rule hash_map_output_collisionI
            [of "MerkleNode a child" "MerkleLeaf leaf'" s root])
          (use lookup_node lookup_leaf' in simp_all)
    qed
    then show ?thesis by simp
  next
    case (Cons b path'')
    show ?thesis
    proof (cases "idx < len div 2")
      case True
      from Cons.prems(1) obtain child where
        child1:
          "merkle_path_root_in_map s (len div 2) idx leaf path =
            Some child"
        and lookup1:
          "fmlookup (HashMap s) (MerkleNode child a) = Some root"
        using True by (auto split: option.splits)
      from Cons.prems(2)[unfolded Cons] obtain child' where
        child2:
          "merkle_path_root_in_map s (len div 2) idx leaf' path'' =
            Some child'"
        and lookup2:
          "fmlookup (HashMap s) (MerkleNode child' b) = Some root"
        using True by (auto split: option.splits)
      show ?thesis
      proof (cases "(child, a) = (child', b)")
        case False
        have "hash_map_output_collision s"
          by (rule hash_map_output_collision_merkle_nodeI
              [OF False lookup1 lookup2])
        then show ?thesis by simp
      next
        case pair_eq: True
        have child_eq: "child = child'" and a_eq: "a = b"
          using pair_eq by simp_all
        have rec:
          "(leaf = leaf' \<and> path = path'') \<or> hash_map_output_collision s"
          by (rule Cons.IH[OF child1 child2[unfolded child_eq[symmetric]]])
        then show ?thesis
          using a_eq Cons by auto
      qed
    next
      case False
      from Cons.prems(1) obtain child where
        child1:
          "merkle_path_root_in_map s (len div 2) (idx - len div 2)
            leaf path = Some child"
        and lookup1:
          "fmlookup (HashMap s) (MerkleNode a child) = Some root"
        using False by (auto split: option.splits)
      from Cons.prems(2)[unfolded Cons] obtain child' where
        child2:
          "merkle_path_root_in_map s (len div 2) (idx - len div 2)
            leaf' path'' = Some child'"
        and lookup2:
          "fmlookup (HashMap s) (MerkleNode b child') = Some root"
        using False by (auto split: option.splits)
      show ?thesis
      proof (cases "(a, child) = (b, child')")
        case False
        have "hash_map_output_collision s"
          by (rule hash_map_output_collision_merkle_nodeI
              [OF False lookup1 lookup2])
        then show ?thesis by simp
      next
        case pair_eq: True
        have child_eq: "child = child'" and a_eq: "a = b"
          using pair_eq by simp_all
        have rec:
          "(leaf = leaf' \<and> path = path'') \<or> hash_map_output_collision s"
          by (rule Cons.IH[OF child1 child2[unfolded child_eq[symmetric]]])
        then show ?thesis
      using a_eq Cons by auto
      qed
    qed
  qed
qed

lemma protocol_created_tree_singletonD:
  assumes "protocol_created_tree [x] t s"
  obtains h where
    "t = \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>"
    "fmlookup (HashMap s) (MerkleLeaf x) = Some h"
  using assms
  unfolding protocol_created_tree_def
  by (auto simp: protocol_merkle.created_tree.simps)

lemma protocol_created_tree_internalD:
  assumes created: "protocol_created_tree xs t s"
    and len: "2 \<le> length xs"
  obtains l h r i where
    "i = length xs div 2"
    "t = \<langle>l, h, r\<rangle>"
    "protocol_created_tree (take i xs) l s"
    "protocol_created_tree (drop i xs) r s"
    "fmlookup (HashMap s) (MerkleNode (value l) (value r)) = Some h"
proof -
  obtain a b cs where xs_eq: "xs = a # b # cs"
    using len by (cases xs; cases "tl xs") auto
  obtain l h r where
    t: "t = \<langle>l, h, r\<rangle>"
    and left:
      "protocol_merkle.created_tree
        (take (length xs div 2) (map MerkleLeaf xs)) l s"
    and right:
      "protocol_merkle.created_tree
        (drop (length xs div 2) (map MerkleLeaf xs)) r s"
    and root:
      "fmlookup (HashMap s) (MerkleNode (value l) (value r)) = Some h"
    using created len
    unfolding protocol_created_tree_def
    by (auto simp: xs_eq protocol_merkle.created_tree.simps Let_def)
  have left':
    "protocol_created_tree (take (length xs div 2) xs) l s"
    using left
    unfolding protocol_created_tree_def by (simp add: take_map)
  have right':
    "protocol_created_tree (drop (length xs div 2) xs) r s"
    using right
    unfolding protocol_created_tree_def by (simp add: drop_map)
  show ?thesis
    by (rule that[OF refl t left' right' root])
qed

lemma protocol_created_tree_path_root_in_map:
  assumes created: "protocol_created_tree xs tree s"
    and len_pow: "length xs = 2 ^ n"
    and i_bound: "i < length xs"
  shows
    "merkle_path_root_in_map s (length xs) i (xs ! i)
      (get_authentication_path (length xs) i tree) = Some (value tree)"
  using created len_pow i_bound
proof (induction n arbitrary: xs tree i)
  case 0
  then have len_xs: "length xs = 1"
    by simp
  then obtain x where xs_eq: "xs = [x]"
    by (cases xs) auto
  from protocol_created_tree_singletonD[OF "0.prems"(1)[unfolded xs_eq]]
  obtain h where tree_eq:
      "tree = \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>"
    and lookup: "fmlookup (HashMap s) (MerkleLeaf x) = Some h"
    by blast
  have i_eq: "i = 0"
    using "0.prems"(3) unfolding xs_eq by simp
  show ?case
    using lookup unfolding xs_eq tree_eq i_eq by simp
next
  case (Suc n)
  let ?mid = "length xs div 2"
  have len_xs: "length xs = 2 ^ Suc n"
    by (rule Suc.prems(2))
  have len_ge: "2 \<le> length xs"
    using len_xs by simp
  have len_not_one: "length xs \<noteq> 1"
    using len_ge by simp
  obtain l h r mid where mid_def: "mid = ?mid"
    and tree_eq: "tree = \<langle>l, h, r\<rangle>"
    and left: "protocol_created_tree (take mid xs) l s"
    and right: "protocol_created_tree (drop mid xs) r s"
    and root_lookup:
      "fmlookup (HashMap s) (MerkleNode (value l) (value r)) = Some h"
    by (rule protocol_created_tree_internalD[OF Suc.prems(1) len_ge])
  have mid_pow: "mid = 2 ^ n"
    using len_xs unfolding mid_def by simp
  have mid_pos: "0 < mid"
    using mid_pow by simp
  have mid_lt: "mid < length xs"
    using len_xs mid_pow by simp
  have take_len: "length (take mid xs) = 2 ^ n"
    using mid_lt mid_pow by simp
  have drop_len: "length (drop mid xs) = 2 ^ n"
    using len_xs mid_pow by simp
  show ?case
  proof (cases "i < mid")
    case True
    have idx_take: "i < length (take mid xs)"
      using True take_len mid_pow by simp
    have child:
      "merkle_path_root_in_map s (length (take mid xs)) i
        (take mid xs ! i)
        (get_authentication_path (length (take mid xs)) i l) =
        Some (value l)"
      by (rule Suc.IH[OF left take_len idx_take])
    have child_mid:
      "merkle_path_root_in_map s mid i (xs ! i)
        (get_authentication_path mid i l) = Some (value l)"
      using child True take_len mid_pow by simp
    show ?thesis
      using True child_mid root_lookup len_not_one
      unfolding tree_eq mid_def by simp
  next
    case False
    have idx_drop: "i - mid < length (drop mid xs)"
      using False Suc.prems(3) drop_len mid_pow mid_def by simp
    have child:
      "merkle_path_root_in_map s (length (drop mid xs)) (i - mid)
        (drop mid xs ! (i - mid))
        (get_authentication_path (length (drop mid xs)) (i - mid) r) =
        Some (value r)"
      by (rule Suc.IH[OF right drop_len idx_drop])
    have child_mid:
      "merkle_path_root_in_map s mid (i - mid) (xs ! i)
        (get_authentication_path mid (i - mid) r) = Some (value r)"
      using child False Suc.prems(3) drop_len mid_pow by simp
    show ?thesis
      using False child_mid root_lookup len_not_one
      unfolding tree_eq mid_def by simp
  qed
qed

lemma protocol_created_tree_merkle_mono:
  assumes created: "protocol_created_tree xs t s"
    and ext: "merkle_hash_extends s u"
  shows "protocol_created_tree xs t u"
  using created
proof (induction xs arbitrary: t rule: length_induct)
  case (1 xs)
  show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis
      using "1.prems"
      unfolding protocol_created_tree_def
      by (simp add: protocol_merkle.created_tree.simps)
  next
    case xs_nonempty: False
    show ?thesis
    proof (cases "length xs = 1")
      case True
      then obtain x where xs_eq: "xs = [x]"
        using xs_nonempty by (cases xs) auto
      from protocol_created_tree_singletonD[OF "1.prems"[unfolded xs_eq]]
      obtain h where
        t_eq: "t = \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>"
        and lookup_s: "fmlookup (HashMap s) (MerkleLeaf x) = Some h"
        by blast
      have lookup_u: "fmlookup (HashMap u) (MerkleLeaf x) = Some h"
        using ext lookup_s unfolding merkle_hash_extends_def by simp
      show ?thesis
        unfolding protocol_created_tree_def xs_eq t_eq
        using lookup_u by (simp add: protocol_merkle.created_tree.simps)
    next
      case not_singleton: False
      have len_ge: "2 \<le> length xs"
        using xs_nonempty not_singleton by (cases xs; cases "tl xs") auto
      obtain l h r i where
        i_def: "i = length xs div 2"
        and t_eq: "t = \<langle>l, h, r\<rangle>"
        and left_created: "protocol_created_tree (take i xs) l s"
        and right_created: "protocol_created_tree (drop i xs) r s"
        and root_lookup:
          "fmlookup (HashMap s) (MerkleNode (value l) (value r)) = Some h"
        by (rule protocol_created_tree_internalD[OF "1.prems" len_ge])
      have i_pos: "0 < i"
        using i_def len_ge by simp
      have i_lt: "i < length xs"
        using i_def len_ge by simp
      have take_less: "length (take i xs) < length xs"
        using i_lt by simp
      have drop_less: "length (drop i xs) < length xs"
        using i_pos i_lt by simp
      have left_u: "protocol_created_tree (take i xs) l u"
        by (rule "1.IH"[rule_format, OF take_less left_created])
      have right_u: "protocol_created_tree (drop i xs) r u"
        by (rule "1.IH"[rule_format, OF drop_less right_created])
      have root_lookup_u:
        "fmlookup (HashMap u) (MerkleNode (value l) (value r)) = Some h"
        using ext root_lookup unfolding merkle_hash_extends_def by simp
      obtain a b cs where xs_eq: "xs = a # b # cs"
        using len_ge by (cases xs; cases "tl xs") auto
      have take_leaf_eq:
        "MerkleLeaf a #
          take (length cs div 2) (MerkleLeaf b # map MerkleLeaf cs) =
        MerkleLeaf a #
          map MerkleLeaf (take (length cs div 2) (b # cs))"
        by (metis list.map(2) take_map)
      have drop_leaf_eq:
        "drop (length cs div 2) (MerkleLeaf b # map MerkleLeaf cs) =
        map MerkleLeaf (drop (length cs div 2) (b # cs))"
        by (metis list.map(2) drop_map)
      have left_u_raw:
        "protocol_merkle.created_tree
          (MerkleLeaf a #
            take (length cs div 2) (MerkleLeaf b # map MerkleLeaf cs))
          l u"
        using left_u
        unfolding protocol_created_tree_def i_def xs_eq
        by (simp add: take_leaf_eq)
      have right_u_raw:
        "protocol_merkle.created_tree
          (drop (length cs div 2) (MerkleLeaf b # map MerkleLeaf cs))
          r u"
        using right_u
        unfolding protocol_created_tree_def i_def xs_eq
        by (simp add: drop_leaf_eq)
      show ?thesis
        using left_u_raw right_u_raw root_lookup_u
        unfolding protocol_created_tree_def t_eq xs_eq
        by (auto simp: protocol_merkle.created_tree.simps Let_def)
    qed
  qed
qed

lemma created_tree_merkle_mono:
  assumes created: "created_tree xs t s"
    and ext: "merkle_hash_extends s u"
  shows "created_tree xs t u"
  using protocol_created_tree_merkle_mono
    [OF created[unfolded created_tree_def] ext]
  unfolding created_tree_def .

lemma merkle_root_binds_table_merkle_mono:
  assumes bind: "merkle_root_binds_table rt table s"
    and ext: "merkle_hash_extends s u"
  shows "merkle_root_binds_table rt table u"
proof -
  from bind obtain tree where
    created: "created_tree table tree s"
    and root: "rt = value tree"
    unfolding merkle_root_binds_table_def by blast
  have "created_tree table tree u"
    by (rule created_tree_merkle_mono[OF created ext])
  then show ?thesis
    unfolding merkle_root_binds_table_def
    using root by blast
qed

lemma protocol_created_tree_same_length_root_eq_or_hash_collision:
  assumes left_created: "protocol_created_tree xs tx s"
    and right_created: "protocol_created_tree ys ty s"
    and same_len: "length xs = length ys"
    and nonempty_xs: "xs \<noteq> []"
    and nonempty_ys: "ys \<noteq> []"
    and same_root: "value tx = value ty"
  shows "xs = ys \<or> hash_map_output_collision s"
  using assms
proof (induction xs arbitrary: ys tx ty rule: length_induct)
  case (1 xs)
  show ?case
  proof (cases "length xs = 1")
    case True
    then obtain x where xs_eq: "xs = [x]"
      using "1.prems"(4) by (cases xs) auto
    from True "1.prems"(3,5) obtain y where ys_eq: "ys = [y]"
      by (cases ys) auto
    from protocol_created_tree_singletonD[OF "1.prems"(1)[unfolded xs_eq]]
    obtain hx where tx: "tx = \<langle>\<langle>\<rangle>, hx, \<langle>\<rangle>\<rangle>"
      and hx_lookup: "fmlookup (HashMap s) (MerkleLeaf x) = Some hx"
      by blast
    from protocol_created_tree_singletonD[OF "1.prems"(2)[unfolded ys_eq]]
    obtain hy where ty: "ty = \<langle>\<langle>\<rangle>, hy, \<langle>\<rangle>\<rangle>"
      and hy_lookup: "fmlookup (HashMap s) (MerkleLeaf y) = Some hy"
      by blast
    have h_eq: "hx = hy"
      using "1.prems"(6) unfolding tx ty by simp
    show ?thesis
    proof (cases "x = y")
      case True
      then show ?thesis
        using xs_eq ys_eq by simp
    next
      case False
      have hy_lookup': "fmlookup (HashMap s) (MerkleLeaf y) = Some hx"
        using hy_lookup h_eq by simp
      then have "hash_map_output_collision s"
        by (rule hash_map_output_collision_merkle_leafI[OF False hx_lookup])
      then show ?thesis by simp
    qed
  next
    case False
    have "0 < length xs"
      using "1.prems"(4) by simp
    have len_ge: "2 \<le> length xs"
      using False \<open>0 < length xs\<close> by linarith
    have len_ge_y: "2 \<le> length ys"
      using len_ge "1.prems"(3) by simp
    obtain lx hx rx i where i_def: "i = length xs div 2"
      and tx: "tx = \<langle>lx, hx, rx\<rangle>"
      and lx_created: "protocol_created_tree (take i xs) lx s"
      and rx_created: "protocol_created_tree (drop i xs) rx s"
      and hx_lookup:
        "fmlookup (HashMap s) (MerkleNode (value lx) (value rx)) = Some hx"
      by (rule protocol_created_tree_internalD[OF "1.prems"(1) len_ge])
    obtain ly hy ry j where j_def: "j = length ys div 2"
      and ty: "ty = \<langle>ly, hy, ry\<rangle>"
      and ly_created: "protocol_created_tree (take j ys) ly s"
      and ry_created: "protocol_created_tree (drop j ys) ry s"
      and hy_lookup:
        "fmlookup (HashMap s) (MerkleNode (value ly) (value ry)) = Some hy"
      by (rule protocol_created_tree_internalD[OF "1.prems"(2) len_ge_y])
    have j_i: "j = i"
      using i_def j_def "1.prems"(3) by simp
    have ly_created_i: "protocol_created_tree (take i ys) ly s"
      using ly_created j_i by simp
    have ry_created_i: "protocol_created_tree (drop i ys) ry s"
      using ry_created j_i by simp
    have h_eq: "hx = hy"
      using "1.prems"(6) unfolding tx ty by simp
    show ?thesis
    proof (cases "(value lx, value rx) = (value ly, value ry)")
      case False
      have hy_lookup':
        "fmlookup (HashMap s) (MerkleNode (value ly) (value ry)) = Some hx"
        using hy_lookup h_eq by simp
      then have "hash_map_output_collision s"
        by (rule hash_map_output_collision_merkle_nodeI[OF False hx_lookup])
      then show ?thesis by simp
    next
      case True
      then have left_root: "value lx = value ly"
        and right_root: "value rx = value ry"
        by simp_all
      have i_pos: "0 < i"
        using i_def len_ge by simp
      have i_lt: "i < length xs"
        using i_def len_ge by simp
      have i_lt_y: "i < length ys"
        using i_lt "1.prems"(3) by simp
      have length_take_xs: "length (take i xs) = i"
        using i_lt by simp
      have length_take_ys: "length (take i ys) = i"
        using i_lt_y by simp
      have left_len: "length (take i xs) = length (take i ys)"
        using i_def j_i "1.prems"(3) by simp
      have right_len: "length (drop i xs) = length (drop i ys)"
        using i_def j_i "1.prems"(3) by simp
      have left_nonempty_xs: "take i xs \<noteq> []"
        using i_pos length_take_xs by auto
      have left_nonempty_ys: "take i ys \<noteq> []"
        using i_pos length_take_ys by auto
      have right_nonempty_xs: "drop i xs \<noteq> []"
        using i_lt by simp
      have right_nonempty_ys: "drop i ys \<noteq> []"
        using i_lt_y by simp
      have take_less: "length (take i xs) < length xs"
        using i_lt by simp
      have drop_less: "length (drop i xs) < length xs"
        using i_pos i_lt by simp
      show ?thesis
      proof (cases "take i xs = take i ys")
        case False
        have "take i xs = take i ys \<or> hash_map_output_collision s"
          by (rule "1.IH"[rule_format, OF take_less lx_created ly_created_i
                left_len left_nonempty_xs left_nonempty_ys left_root])
        then show ?thesis
          using False by simp
      next
        case left_eq: True
        show ?thesis
        proof (cases "drop i xs = drop i ys")
          case True
          then have "xs = ys"
            using left_eq i_def j_i "1.prems"(3)
            by (metis append_take_drop_id)
          then show ?thesis by simp
        next
          case False
          have "drop i xs = drop i ys \<or> hash_map_output_collision s"
            by (rule "1.IH"[rule_format, OF drop_less rx_created ry_created_i
                  right_len right_nonempty_xs right_nonempty_ys right_root])
          then show ?thesis
            using False by simp
        qed
      qed
    qed
  qed
qed

lemma merkle_root_binds_same_length_tables_collision_imp_hash_collision:
  assumes bind1: "merkle_root_binds_table rt table s"
    and bind2: "merkle_root_binds_table rt table' s"
    and same_len: "length table = length table'"
    and nonempty: "table \<noteq> []"
    and neq: "table \<noteq> table'"
  shows "hash_map_output_collision s"
proof -
  from bind1 obtain tree where tree:
    "created_tree table tree s" "rt = value tree"
    unfolding merkle_root_binds_table_def by blast
  from bind2 obtain tree' where tree':
    "created_tree table' tree' s" "rt = value tree'"
    unfolding merkle_root_binds_table_def by blast
  have nonempty': "table' \<noteq> []"
    using same_len nonempty by auto
  have same_root: "value tree = value tree'"
    using tree tree' by simp
  have "table = table' \<or> hash_map_output_collision s"
    by (rule protocol_created_tree_same_length_root_eq_or_hash_collision
        [OF tree(1)[unfolded created_tree_def]
            tree'(1)[unfolded created_tree_def]
            same_len nonempty nonempty' same_root])
  then show ?thesis
    using neq by simp
qed

lemma merkle_root_binds_same_length_tables_unique_if_no_hash_collision:
  assumes bind1: "merkle_root_binds_table rt table s"
    and bind2: "merkle_root_binds_table rt table' s"
    and same_len: "length table = length table'"
    and clean: "\<not> hash_map_output_collision s"
  shows "table = table'"
proof (cases "table = []")
  case True
  then show ?thesis
    using same_len by simp
next
  case False
  show ?thesis
  proof (rule ccontr)
    assume neq: "table \<noteq> table'"
    have "hash_map_output_collision s"
      by (rule merkle_root_binds_same_length_tables_collision_imp_hash_collision
          [OF bind1 bind2 same_len False neq])
    then show False
      using clean by contradiction
  qed
qed

lemma merkle_root_binds_same_length_tables_common_extension_collision:
  assumes bind1: "merkle_root_binds_table rt table s1"
    and bind2: "merkle_root_binds_table rt table' s2"
    and ext1: "s1 \<le> u"
    and ext2: "s2 \<le> u"
    and same_len: "length table = length table'"
    and nonempty: "table \<noteq> []"
    and neq: "table \<noteq> table'"
  shows "hash_map_output_collision u"
proof -
  have bind1_u: "merkle_root_binds_table rt table u"
    by (rule merkle_root_binds_table_mono[OF bind1 ext1])
  have bind2_u: "merkle_root_binds_table rt table' u"
    by (rule merkle_root_binds_table_mono[OF bind2 ext2])
  show ?thesis
    by (rule merkle_root_binds_same_length_tables_collision_imp_hash_collision
        [OF bind1_u bind2_u same_len nonempty neq])
qed

lemma merkle_root_binds_same_length_tables_common_extension_unique_if_clean:
  assumes clean: "\<not> hash_map_output_collision u"
    and bind1: "merkle_root_binds_table rt table s1"
    and bind2: "merkle_root_binds_table rt table' s2"
    and ext1: "s1 \<le> u"
    and ext2: "s2 \<le> u"
    and same_len: "length table = length table'"
    and nonempty: "table \<noteq> []"
  shows "table = table'"
proof (rule ccontr)
  assume "table \<noteq> table'"
  then have "hash_map_output_collision u"
    by (rule merkle_root_binds_same_length_tables_common_extension_collision
        [OF bind1 bind2 ext1 ext2 same_len nonempty])
  then show False
    using clean by contradiction
qed

lemma merkle_root_binds_same_length_tables_compatible_states_unique_if_clean_merge:
  assumes compatible: "hash_maps_compatible s1 s2"
    and clean: "\<not> hash_map_output_collision (hash_state_merge s1 s2)"
    and bind1: "merkle_root_binds_table rt table s1"
    and bind2: "merkle_root_binds_table rt table' s2"
    and same_len: "length table = length table'"
    and nonempty: "table \<noteq> []"
  shows "table = table'"
proof -
  have ext1: "s1 \<le> hash_state_merge s1 s2"
    by (rule hash_state_merge_extends_left_if_compatible[OF compatible])
  have ext2: "s2 \<le> hash_state_merge s1 s2"
    by (rule hash_state_merge_extends_right)
  show ?thesis
    by (rule merkle_root_binds_same_length_tables_common_extension_unique_if_clean
        [OF clean bind1 bind2 ext1 ext2 same_len nonempty])
qed

lemma merkle_root_binds_same_length_tables_merkle_compatible_unique_if_clean_merge:
  assumes compatible: "merkle_hash_maps_compatible s1 s2"
    and clean:
      "\<not> hash_map_output_collision (merkle_hash_state_merge s1 s2)"
    and bind1: "merkle_root_binds_table rt table s1"
    and bind2: "merkle_root_binds_table rt table' s2"
    and same_len: "length table = length table'"
    and nonempty: "table \<noteq> []"
  shows "table = table'"
proof (rule ccontr)
  let ?u = "merkle_hash_state_merge s1 s2"
  assume neq: "table \<noteq> table'"
  have ext1: "merkle_hash_extends s1 ?u"
    by (rule merkle_hash_state_merge_extends_left_if_compatible[OF compatible])
  have ext2: "merkle_hash_extends s2 ?u"
    by (rule merkle_hash_state_merge_extends_right)
  have bind1_u: "merkle_root_binds_table rt table ?u"
    by (rule merkle_root_binds_table_merkle_mono[OF bind1 ext1])
  have bind2_u: "merkle_root_binds_table rt table' ?u"
    by (rule merkle_root_binds_table_merkle_mono[OF bind2 ext2])
  have "hash_map_output_collision ?u"
    by (rule merkle_root_binds_same_length_tables_collision_imp_hash_collision
        [OF bind1_u bind2_u same_len nonempty neq])
  then show False
    using clean by contradiction
qed

definition state_after_query_chunks :: "'f \<Rightarrow> 'f list list \<Rightarrow> nat \<Rightarrow> 'f"
  where
    "state_after_query_chunks st chunks i =
      foldl (\<lambda>acc chunk. foldl concat acc chunk) st (take i chunks)"

lemma concat_append_eq_concat_same_chunk_lengths:
  assumes len: "length xs = length ys"
    and lens:
      "\<And>i. i < length xs \<Longrightarrow> length (xs ! i) = length (ys ! i)"
    and concat_eq: "List.concat xs @ trailing = List.concat ys"
  shows "xs = ys \<and> trailing = []"
  using len lens concat_eq
proof (induction xs arbitrary: ys trailing)
  case Nil
  then show ?case
    by (cases ys) simp_all
next
  case (Cons x xs)
  then obtain y ys' where ys_eq: "ys = y # ys'"
  proof (cases ys)
    case Nil
    then show ?thesis
      using Cons.prems(1) by simp
  next
    case (Cons y ys')
    then show ?thesis
      by (rule that)
  qed
  have head_len: "length x = length y"
    using Cons.prems(2)[of 0] unfolding ys_eq by simp
  have append_eq:
    "x @ (List.concat xs @ trailing) = y @ List.concat ys'"
    using Cons.prems(3) unfolding ys_eq by simp
  have head_eq: "x = y"
    using append_eq head_len
    by (metis append_eq_conv_conj)
  have tail_concat_eq:
    "List.concat xs @ trailing = List.concat ys'"
    using append_eq head_eq by simp
  have tail_len: "length xs = length ys'"
    using Cons.prems(1) unfolding ys_eq by simp
  have tail_lens:
    "\<And>i. i < length xs \<Longrightarrow> length (xs ! i) = length (ys' ! i)"
  proof -
    fix i
    assume i_bound: "i < length xs"
    then have "Suc i < length (x # xs)"
      by simp
    from Cons.prems(2)[OF this] show
      "length (xs ! i) = length (ys' ! i)"
      unfolding ys_eq by simp
  qed
  have "xs = ys' \<and> trailing = []"
    by (rule Cons.IH[OF tail_len tail_lens tail_concat_eq])
  then show ?case
    using head_eq unfolding ys_eq by simp
qed

fun fri_query_transcript_length :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "fri_query_transcript_length 0 len = 0"
  | "fri_query_transcript_length (Suc n) len =
      2 + 2 * floor_log len + fri_query_transcript_length n (len div 2)"

definition query_decommitment_transcript_length :: "nat \<Rightarrow> nat"
  where
    "query_decommitment_transcript_length idx =
      length (powers_scaled idx) * (1 + floor_log (clength * scale))"

definition query_leaf_path_chunk :: "nat \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "query_leaf_path_chunk len leaf path chunk \<longleftrightarrow>
      length path = floor_log len \<and>
      chunk = [leaf] @ path"

definition query_decommitment_transcript
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "query_decommitment_transcript idx leaves paths chunk \<longleftrightarrow>
      length leaves = length (powers_scaled idx) \<and>
      length paths = length (powers_scaled idx) \<and>
      chunk = List.concat
        (map (\<lambda>(leaf, path).
        [leaf] @ path) (zip leaves paths)) \<and>
      (\<forall>path \<in> set paths. length path = floor_log (clength * scale))"

lemma query_decommitment_transcript_length:
  assumes "query_decommitment_transcript idx leaves paths chunk"
  shows "length chunk = query_decommitment_transcript_length idx"
proof -
  have leaves_len: "length leaves = length (powers_scaled idx)"
    using assms unfolding query_decommitment_transcript_def by simp
  have paths_len: "length paths = length (powers_scaled idx)"
    using assms unfolding query_decommitment_transcript_def by simp
  have leaves_paths_len: "length leaves = length paths"
    using leaves_len paths_len by simp
  have map2_eq:
    "map2 (\<lambda>leaf path. [leaf] @ path) leaves paths =
      map2 (\<lambda>leaf path. leaf # path) leaves paths"
  proof (induction leaves arbitrary: paths)
    case Nil
    then show ?case
      by (cases paths) simp_all
  next
    case (Cons leaf leaves)
    then show ?case
      by (cases paths) simp_all
  qed
  have chunk_eq:
    "chunk =
      List.concat (map2 (\<lambda>leaf path. leaf # path) leaves paths)"
    using assms map2_eq unfolding query_decommitment_transcript_def
    by simp
  have path_lens:
    "\<And>path. path \<in> set paths \<Longrightarrow>
      length path = floor_log (clength * scale)"
    using assms unfolding query_decommitment_transcript_def by blast
  have concat_len:
    "length (List.concat (map2 (\<lambda>leaf path. leaf # path)
        leaves paths)) =
      length leaves * (1 + floor_log (clength * scale))"
    using leaves_paths_len path_lens
  proof (induction leaves arbitrary: paths)
    case Nil
    then show ?case
      by (cases paths) simp_all
  next
    case (Cons leaf leaves)
    then obtain path paths' where paths_eq: "paths = path # paths'"
      by (cases paths) auto
    have len_rest: "length leaves = length paths'"
      using Cons.prems(1) unfolding paths_eq by simp
    have path_len: "length path = floor_log (clength * scale)"
      using Cons.prems(2) unfolding paths_eq by simp
    have paths'_lens:
      "\<And>p. p \<in> set paths' \<Longrightarrow>
        length p = floor_log (clength * scale)"
      using Cons.prems(2) unfolding paths_eq by simp
    have rest:
      "length (List.concat (map2 (\<lambda>leaf path. leaf # path)
          leaves paths')) =
        length leaves * (1 + floor_log (clength * scale))"
      by (rule Cons.IH[OF len_rest paths'_lens])
    show ?case
      unfolding paths_eq using path_len rest by simp
  qed
  have "length chunk =
      length leaves * (1 + floor_log (clength * scale))"
    unfolding chunk_eq by (rule concat_len)
  also have "... =
      length (powers_scaled idx) * (1 + floor_log (clength * scale))"
    using leaves_len by simp
  finally show ?thesis
    unfolding query_decommitment_transcript_length_def .
qed

definition fri_layer_opening_chunk
  :: "nat \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "fri_layer_opening_chunk len xp xp_path xn xn_path chunk \<longleftrightarrow>
      length xp_path = floor_log len \<and>
      length xn_path = floor_log len \<and>
      chunk = [xp] @ xp_path @ [xn] @ xn_path"

lemma fri_layer_opening_chunk_length:
  assumes "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
  shows "length chunk = 2 + 2 * floor_log len"
  using assms unfolding fri_layer_opening_chunk_def by simp

fun fri_layers_transcript_length :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "fri_layers_transcript_length 0 len = 0"
  | "fri_layers_transcript_length (Suc n) len =
      2 + 2 * floor_log len + fri_layers_transcript_length n (len div 2)"

fun fri_layer_lengths :: "nat \<Rightarrow> nat \<Rightarrow> nat list"
  where
    "fri_layer_lengths 0 len = []"
  | "fri_layer_lengths (Suc n) len = len # fri_layer_lengths n (len div 2)"

fun fri_layer_indices :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
  where
    "fri_layer_indices 0 idx len = []"
  | "fri_layer_indices (Suc n) idx len =
      idx # fri_layer_indices n (idx mod (len div 2)) (len div 2)"

definition fri_sibling_index :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "fri_sibling_index len idx = (idx + len div 2) mod len"

definition fri_fold_denominator :: "'f \<Rightarrow> nat \<Rightarrow> 'f"
  where "fri_fold_denominator x pw = 2 * x ^ pw"

definition fri_fold_value :: "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f"
  where
    "fri_fold_value b xp xn denom =
      (xp + xn) div 2 + b * ((xp - xn) div denom)"

lemma length_fri_layer_lengths[simp]:
  "length (fri_layer_lengths n len) = n"
  by (induction n arbitrary: len) simp_all

lemma length_fri_layer_indices[simp]:
  "length (fri_layer_indices n idx len) = n"
  by (induction n arbitrary: idx len) simp_all

definition fri_layers_transcript
  :: "nat \<Rightarrow> nat \<Rightarrow> 'f list list \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "fri_layers_transcript n len layer_chunks chunk \<longleftrightarrow>
      length layer_chunks = n \<and>
      chunk = List.concat layer_chunks \<and>
      (\<forall>(layer_len, layer_chunk) \<in> set (zip (fri_layer_lengths n len) layer_chunks).
        \<exists>xp xp_path xn xn_path.
          fri_layer_opening_chunk layer_len xp xp_path xn xn_path layer_chunk)"

lemma fri_layers_transcript_length:
  assumes "fri_layers_transcript n len layer_chunks chunk"
  shows "length chunk = fri_layers_transcript_length n len"
  using assms
proof (induction n arbitrary: len layer_chunks chunk)
  case 0
  then show ?case
    unfolding fri_layers_transcript_def by simp
next
  case (Suc n)
  from Suc.prems have len_chunks:
    "length layer_chunks = Suc n"
    and chunk_eq: "chunk = List.concat layer_chunks"
    and openings:
      "\<forall>(layer_len, layer_chunk) \<in>
        set (zip (fri_layer_lengths (Suc n) len) layer_chunks).
        \<exists>xp xp_path xn xn_path.
          fri_layer_opening_chunk layer_len xp xp_path xn xn_path
            layer_chunk"
    unfolding fri_layers_transcript_def by simp_all
  obtain first rest where chunks_eq: "layer_chunks = first # rest"
    using len_chunks by (cases layer_chunks) auto
  from openings obtain xp xp_path xn xn_path where first_open:
    "fri_layer_opening_chunk len xp xp_path xn xn_path first"
    unfolding chunks_eq by auto
  have rest_layers:
    "fri_layers_transcript n (len div 2) rest (List.concat rest)"
    unfolding fri_layers_transcript_def
  proof (intro conjI)
    show "length rest = n"
      using len_chunks unfolding chunks_eq by simp
  next
    show "List.concat rest = List.concat rest"
      by simp
  next
    show "\<forall>(layer_len, layer_chunk) \<in>
        set (zip (fri_layer_lengths n (len div 2)) rest).
        \<exists>xp xp_path xn xn_path.
          fri_layer_opening_chunk layer_len xp xp_path xn xn_path
            layer_chunk"
      using openings unfolding chunks_eq by auto
  qed
  have "length chunk = length first + length (List.concat rest)"
    unfolding chunk_eq chunks_eq by simp
  also have "... =
      (2 + 2 * floor_log len) +
        fri_layers_transcript_length n (len div 2)"
    using fri_layer_opening_chunk_length[OF first_open]
      Suc.IH[OF rest_layers] by simp
  finally show ?case
    by simp
qed

lemma fri_layers_transcript_nth_opening:
  assumes layers: "fri_layers_transcript n len layer_chunks chunk"
    and j_bound: "j < n"
  obtains xp xp_path xn xn_path
  where "fri_layer_opening_chunk (fri_layer_lengths n len ! j)
    xp xp_path xn xn_path (layer_chunks ! j)"
proof -
  have len_chunks: "length layer_chunks = n"
    using layers unfolding fri_layers_transcript_def by simp
  have pair_in:
    "(fri_layer_lengths n len ! j, layer_chunks ! j) \<in>
      set (zip (fri_layer_lengths n len) layer_chunks)"
  proof -
    have j_zip:
      "j < length (zip (fri_layer_lengths n len) layer_chunks)"
      using j_bound len_chunks by simp
    have "zip (fri_layer_lengths n len) layer_chunks ! j =
        (fri_layer_lengths n len ! j, layer_chunks ! j)"
      using j_bound len_chunks by simp
    then show ?thesis
      using nth_mem[OF j_zip] by metis
  qed
  then obtain xp xp_path xn xn_path where
    "fri_layer_opening_chunk (fri_layer_lengths n len ! j)
      xp xp_path xn xn_path (layer_chunks ! j)"
    using layers unfolding fri_layers_transcript_def by blast
  then show ?thesis
    by (rule that)
qed

definition verifier_query_round_transcript_length
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat"
  where
    "verifier_query_round_transcript_length idx f_fri_roots composition_fri_roots =
      query_decommitment_transcript_length idx +
      fri_layers_transcript_length (length f_fri_roots) (clength * scale) +
      fri_layers_transcript_length (length composition_fri_roots) (clength * scale)"

definition verifier_query_round_chunk
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "verifier_query_round_chunk idx f_fri_roots composition_fri_roots chunk \<longleftrightarrow>
      (\<exists>query_chunk trace_fri_chunk composition_fri_chunk
          leaves paths trace_layer_chunks composition_layer_chunks.
        chunk = query_chunk @ trace_fri_chunk @ composition_fri_chunk \<and>
        query_decommitment_transcript idx leaves paths query_chunk \<and>
        fri_layers_transcript (length f_fri_roots) (clength * scale)
          trace_layer_chunks trace_fri_chunk \<and>
        fri_layers_transcript (length composition_fri_roots) (clength * scale)
          composition_layer_chunks composition_fri_chunk)"

lemma verifier_query_round_chunk_length:
  assumes "verifier_query_round_chunk idx f_fri_roots composition_fri_roots chunk"
  shows
    "length chunk =
      verifier_query_round_transcript_length idx f_fri_roots
        composition_fri_roots"
proof -
  from assms obtain query_chunk trace_fri_chunk composition_fri_chunk
      leaves paths trace_layer_chunks composition_layer_chunks where
    chunk_eq: "chunk = query_chunk @ trace_fri_chunk @ composition_fri_chunk"
    and query:
      "query_decommitment_transcript idx leaves paths query_chunk"
    and trace:
      "fri_layers_transcript (length f_fri_roots) (clength * scale)
        trace_layer_chunks trace_fri_chunk"
    and composition:
      "fri_layers_transcript (length composition_fri_roots) (clength * scale)
        composition_layer_chunks composition_fri_chunk"
    unfolding verifier_query_round_chunk_def by blast
  show ?thesis
    unfolding chunk_eq verifier_query_round_transcript_length_def
    using query_decommitment_transcript_length[OF query]
      fri_layers_transcript_length[OF trace]
      fri_layers_transcript_length[OF composition]
    by simp
qed

definition query_round_fri_layer_transcripts
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
      'f list list \<Rightarrow> 'f list list \<Rightarrow> bool"
  where
    "query_round_fri_layer_transcripts idx trace_roots composition_roots
      chunk trace_layer_chunks composition_layer_chunks \<longleftrightarrow>
      (\<exists>query_chunk trace_fri_chunk composition_fri_chunk leaves paths.
        chunk = query_chunk @ trace_fri_chunk @ composition_fri_chunk \<and>
        query_decommitment_transcript idx leaves paths query_chunk \<and>
        fri_layers_transcript (length trace_roots) (clength * scale)
          trace_layer_chunks trace_fri_chunk \<and>
        fri_layers_transcript (length composition_roots) (clength * scale)
          composition_layer_chunks composition_fri_chunk)"

lemma verifier_query_round_chunk_fri_layer_transcriptsE:
  assumes "verifier_query_round_chunk idx trace_roots composition_roots chunk"
  obtains trace_layer_chunks composition_layer_chunks
  where "query_round_fri_layer_transcripts idx trace_roots composition_roots
    chunk trace_layer_chunks composition_layer_chunks"
  using assms
  unfolding verifier_query_round_chunk_def query_round_fri_layer_transcripts_def
  by blast

definition verifier_query_indices_derived
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "verifier_query_indices_derived s out query_start_state rest
      f_fri_roots composition_fri_roots query_idxs \<longleftrightarrow>
      (\<exists>result final_state raw_idxs query_chunks trailing.
        out = Some (result, final_state) \<and>
        length raw_idxs = rounds \<and>
        query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
        length query_chunks = rounds \<and>
        List.concat query_chunks @ trailing = rest \<and>
        (\<forall>i < rounds.
          verifier_query_round_chunk (query_idxs ! i)
            f_fri_roots composition_fri_roots (query_chunks ! i)) \<and>
        (\<forall>i < rounds.
          fmlookup (HashMap final_state)
            (QueryIndexChallenge (PQueryCounter s + i)
              (state_after_query_chunks query_start_state query_chunks i)) =
            Some (raw_idxs ! i)) \<and>
        (\<forall>idx \<in> set query_idxs. idx < clength * scale))"

definition accepted_transcript_shape
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "accepted_transcript_shape s out alphas query_idxs \<longleftrightarrow>
      (\<exists>result final_state fr f_fri_roots f_final dg composition_fri_roots final rest.
        out = Some (result, final_state) \<and>
        verifier_header_transcript s fr f_fri_roots f_final alphas dg
          composition_fri_roots final rest \<and>
        verifier_query_indices_derived s out
          (verifier_header_state s fr f_fri_roots f_final alphas dg
            composition_fri_roots final)
          rest f_fri_roots composition_fri_roots query_idxs)"

lemma accepted_transcript_shape_query_chunksE:
  assumes shape: "accepted_transcript_shape s out alphas query_idxs"
  obtains result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest raw_idxs query_chunks trailing
  where
    "out = Some (result, final_state)"
    "verifier_header_transcript s fr f_fri_roots f_final alphas dg
      composition_fri_roots final rest"
    "length raw_idxs = rounds"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length query_chunks = rounds"
    "List.concat query_chunks @ trailing = rest"
    "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (query_idxs ! i)
        f_fri_roots composition_fri_roots (query_chunks ! i)"
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks
            (verifier_header_state s fr f_fri_roots f_final alphas dg
              composition_fri_roots final)
            query_chunks i)) =
        Some (raw_idxs ! i)"
    "\<forall>idx \<in> set query_idxs. idx < clength * scale"
proof -
  from shape obtain result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    out_eq: "out = Some (result, final_state)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final alphas dg
        composition_fri_roots final rest"
    and query:
      "verifier_query_indices_derived s out
        (verifier_header_state s fr f_fri_roots f_final alphas dg
          composition_fri_roots final)
        rest f_fri_roots composition_fri_roots query_idxs"
    unfolding accepted_transcript_shape_def by blast
  from query obtain result' final_state' raw_idxs query_chunks trailing where
    out_eq': "out = Some (result', final_state')"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and concat_chunks: "List.concat query_chunks @ trailing = rest"
    and chunk_shape:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          f_fri_roots composition_fri_roots (query_chunks ! i)"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks
              (verifier_header_state s fr f_fri_roots f_final alphas dg
                composition_fri_roots final)
              query_chunks i)) =
          Some (raw_idxs ! i)"
    and idx_bound:
      "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    unfolding verifier_query_indices_derived_def by blast
  have final_state_eq: "final_state' = final_state"
    using out_eq out_eq' by simp
  show ?thesis
    by (rule that[OF out_eq header len_raw query_idxs_eq len_chunks
          concat_chunks chunk_shape])
      (use lookup idx_bound final_state_eq in simp_all)
qed

lemma accepted_transcript_shape_query_chunk_lengthsE:
  assumes shape: "accepted_transcript_shape s out alphas query_idxs"
  obtains result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest raw_idxs query_chunks trailing
  where
    "out = Some (result, final_state)"
    "verifier_header_transcript s fr f_fri_roots f_final alphas dg
      composition_fri_roots final rest"
    "length raw_idxs = rounds"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length query_chunks = rounds"
    "List.concat query_chunks @ trailing = rest"
    "\<And>i. i < rounds \<Longrightarrow>
      length (query_chunks ! i) =
        verifier_query_round_transcript_length (query_idxs ! i)
          f_fri_roots composition_fri_roots"
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks
            (verifier_header_state s fr f_fri_roots f_final alphas dg
              composition_fri_roots final)
            query_chunks i)) =
        Some (raw_idxs ! i)"
    "\<forall>idx \<in> set query_idxs. idx < clength * scale"
proof -
  from accepted_transcript_shape_query_chunksE[OF shape]
  obtain result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest raw_idxs query_chunks trailing where
    out_eq: "out = Some (result, final_state)"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final alphas dg
        composition_fri_roots final rest"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and concat_chunks: "List.concat query_chunks @ trailing = rest"
    and chunk_shape:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          f_fri_roots composition_fri_roots (query_chunks ! i)"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks
              (verifier_header_state s fr f_fri_roots f_final alphas dg
                composition_fri_roots final)
              query_chunks i)) =
          Some (raw_idxs ! i)"
    and idx_bound:
      "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by blast
  have chunk_len:
    "\<And>i. i < rounds \<Longrightarrow>
      length (query_chunks ! i) =
        verifier_query_round_transcript_length (query_idxs ! i)
          f_fri_roots composition_fri_roots"
    using verifier_query_round_chunk_length[OF chunk_shape] by blast
  show ?thesis
    by (rule that[OF out_eq header len_raw query_idxs_eq len_chunks
          concat_chunks chunk_len lookup idx_bound])
qed

definition accepted_with_tables
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "accepted_with_tables s out trace_table composition_table alphas query_idxs \<longleftrightarrow>
      accepted_transcript_shape s out alphas query_idxs \<and>
        (\<forall>idx \<in> set query_idxs.
          query_consistent_at trace_table composition_table alphas idx) \<and>
      length trace_table = clength * scale \<and>
      length composition_table = clength * scale \<and>
      length alphas = length spec"

definition accepted_with_bound_tables
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "accepted_with_bound_tables s out trace_table composition_table alphas query_idxs \<longleftrightarrow>
      accepted_with_tables s out trace_table composition_table alphas query_idxs \<and>
      (\<exists>result final_state fr f_fri_roots f_final dg composition_fri_roots final rest.
        out = Some (result, final_state) \<and>
        verifier_header_transcript s fr f_fri_roots f_final alphas dg
          composition_fri_roots final rest \<and>
        merkle_root_binds_table fr trace_table final_state \<and>
        composition_fri_roots \<noteq> [] \<and>
        merkle_root_binds_table (hd composition_fri_roots) composition_table final_state)"

definition alpha_list_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list set \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "alpha_list_set_hit s B out \<longleftrightarrow>
      (\<exists>as query_idxs.
        accepted_transcript_shape s out as query_idxs \<and> as \<in> B)"

definition alpha_header_list_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "alpha_header_list_set_hit s B out \<longleftrightarrow>
      (\<exists>as query_idxs result final_state fr f_fri_roots f_final dg
          composition_fri_roots final rest.
        accepted_transcript_shape s out as query_idxs \<and>
        out = Some (result, final_state) \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest \<and>
        as \<in> B fr f_fri_roots f_final)"

end

end
