(*  Title:      Stark/Soundness_Oracle_Dynamic_Target.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Oracle_Dynamic_Target
  imports Soundness_Oracle_Budgets
begin

text \<open>
  State-dependent target-hit combinators.

  These lemmas are deliberately generic: the selected target set may depend on
  an intermediate oracle state, but all probability bounds are still discharged
  through the existing random-oracle target-budget interface.
\<close>

context soundness
begin

definition state_dependent_output_hit
  :: "(('f, 'a) protocol_channel_scheme \<Rightarrow> 'f set) \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "state_dependent_output_hit B s out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (y, _) \<Rightarrow> y \<in> B s)"

definition state_dependent_new_output_hit
  :: "(('f, 'a) protocol_channel_scheme \<Rightarrow> 'f set) \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('r \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "state_dependent_new_output_hit B s out \<longleftrightarrow>
      hash_new_output_hit_event (B s) s out"

definition state_dependent_prequeried_hash_hit
  :: "(('f, 'a) protocol_channel_scheme \<Rightarrow> 'f set) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "state_dependent_prequeried_hash_hit B x s \<longleftrightarrow>
      (\<exists>y. fmlookup (HashMap s) x = Some y \<and> y \<in> B s)"

lemma state_dependent_output_hit_None[simp]:
  "\<not> state_dependent_output_hit B s None"
  unfolding state_dependent_output_hit_def by simp

lemma state_dependent_new_output_hit_None[simp]:
  "\<not> state_dependent_new_output_hit B s None"
  unfolding state_dependent_new_output_hit_def hash_new_output_hit_event_def
  by simp

lemma state_dependent_prequeried_hash_hitI:
  assumes "fmlookup (HashMap s) x = Some y"
    and "y \<in> B s"
  shows "state_dependent_prequeried_hash_hit B x s"
  using assms unfolding state_dependent_prequeried_hash_hit_def by blast

lemma state_dependent_output_hit_mono:
  assumes subset: "\<And>s. B s \<subseteq> C s"
    and hit: "state_dependent_output_hit B s out"
  shows "state_dependent_output_hit C s out"
  using subset hit
  unfolding state_dependent_output_hit_def
  by (cases out) auto

lemma state_dependent_new_output_hit_mono:
  assumes subset: "\<And>s. B s \<subseteq> C s"
    and hit: "state_dependent_new_output_hit B s out"
  shows "state_dependent_new_output_hit C s out"
  using subset hit
  unfolding state_dependent_new_output_hit_def hash_new_output_hit_event_def
  by (cases out) (auto intro: hash_map_new_output_hit_subset)

lemma state_dependent_output_hit_union:
  "state_dependent_output_hit (\<lambda>s. B s \<union> C s) s out \<longleftrightarrow>
    state_dependent_output_hit B s out \<or>
    state_dependent_output_hit C s out"
  unfolding state_dependent_output_hit_def
  by (cases out) auto

lemma state_dependent_new_output_hit_union_imp:
  assumes hit: "state_dependent_new_output_hit (\<lambda>s. B s \<union> C s) s out"
  shows
    "state_dependent_new_output_hit B s out \<or>
      state_dependent_new_output_hit C s out"
proof (cases out)
  case None
  then show ?thesis
    using hit by simp
next
  case (Some rt)
  then obtain r t where rt: "rt = (r, t)"
    by (cases rt) simp
  obtain x y where
    none: "fmlookup (HashMap s) x = None"
    and some: "fmlookup (HashMap t) x = Some y"
    and y: "y \<in> B s \<union> C s"
    using hit Some rt
    unfolding state_dependent_new_output_hit_def hash_new_output_hit_event_def
      hash_map_new_output_hit_def
    by auto
  show ?thesis
  proof (cases "y \<in> B s")
    case True
    then show ?thesis
      using Some rt none some
      unfolding state_dependent_new_output_hit_def hash_new_output_hit_event_def
        hash_map_new_output_hit_def
      by auto
  next
    case False
    then have "y \<in> C s"
      using y by simp
    then show ?thesis
      using Some rt none some
      unfolding state_dependent_new_output_hit_def hash_new_output_hit_event_def
        hash_map_new_output_hit_def
      by auto
  qed
qed

lemma wp_event_state_dependent_output_union_bound:
  "wp_event m
      (state_dependent_output_hit (\<lambda>s. B s \<union> C s) s) s \<le>
    wp_event m (state_dependent_output_hit B s) s +
    wp_event m (state_dependent_output_hit C s) s"
  unfolding state_dependent_output_hit_union
  by (rule wp_event_union_bound)

lemma wp_event_state_dependent_new_output_union_bound:
  "wp_event m
      (state_dependent_new_output_hit (\<lambda>s. B s \<union> C s) s) s \<le>
    wp_event m (state_dependent_new_output_hit B s) s +
    wp_event m (state_dependent_new_output_hit C s) s"
proof -
  have "wp_event m
      (state_dependent_new_output_hit (\<lambda>s. B s \<union> C s) s) s \<le>
      wp_event m
        (\<lambda>out. state_dependent_new_output_hit B s out \<or>
          state_dependent_new_output_hit C s out) s"
    by (rule wp_event_mono) (rule state_dependent_new_output_hit_union_imp)
  also have "... \<le>
      wp_event m (state_dependent_new_output_hit B s) s +
      wp_event m (state_dependent_new_output_hit C s) s"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma wp_hash_state_dependent_new_output_hit:
  fixes x :: "'f protocol_hash_input"
  shows
    "wp_event (hash x) (state_dependent_new_output_hit B s) s =
      (if fmlookup (HashMap s) x = None
       then nnreal (card (B s)) / nnreal size
       else 0)"
  unfolding state_dependent_new_output_hit_def
  by (rule wp_hash_new_output_hit)

lemma wp_hash_state_dependent_new_output_hit_bound:
  fixes x :: "'f protocol_hash_input"
  shows
    "wp_event (hash x) (state_dependent_new_output_hit B s) s \<le>
      nnreal (card (B s)) / nnreal size"
  unfolding state_dependent_new_output_hit_def
  by (rule wp_hash_new_output_hit_bound)

lemma wp_hash_state_dependent_new_output_hit_bound_card:
  fixes x :: "'f protocol_hash_input"
  assumes card_bound: "card (B s) \<le> N"
  shows
    "wp_event (hash x) (state_dependent_new_output_hit B s) s \<le>
      nnreal N / nnreal size"
proof -
  have "wp_event (hash x) (state_dependent_new_output_hit B s) s \<le>
      nnreal (card (B s)) / nnreal size"
    by (rule wp_hash_state_dependent_new_output_hit_bound)
  also have "... \<le> nnreal N / nnreal size"
    by (rule nnreal_nat_divide_right_mono[OF card_bound])
  finally show ?thesis .
qed

lemma hash_state_dependent_output_hit_fresh_or_prequeried:
  fixes x :: "'f protocol_hash_input"
  assumes out: "out \<in> set_dist (execute (hash x) s)"
    and hit: "state_dependent_output_hit B s out"
  shows
    "state_dependent_new_output_hit B s out \<or>
      state_dependent_prequeried_hash_hit B x s"
proof (cases out)
  case None
  then show ?thesis
    using hit by simp
next
  case (Some ht)
  then obtain h t where ht: "ht = (h, t)"
    by (cases ht) simp
  have hash_out: "Some (h, t) \<in> set_dist (execute (hash x) s)"
    using out Some ht by simp
  have h_in: "h \<in> B s"
    using hit Some ht unfolding state_dependent_output_hit_def by simp
  have lookup_t: "fmlookup (HashMap t) x = Some h"
    using protocol_merkle.hash_outcome(2)[OF hash_out] .
  show ?thesis
  proof (cases "fmlookup (HashMap s) x")
    case None
    then have "hash_map_new_output_hit (B s) s t"
      unfolding hash_map_new_output_hit_def
      using lookup_t h_in by blast
    then show ?thesis
      using Some ht
      unfolding state_dependent_new_output_hit_def hash_new_output_hit_event_def
      by simp
  next
    case (Some y)
    then have "y = h"
      using lookup_t hash_extension_lookup[OF Some protocol_merkle.hash_outcome(1)[OF hash_out]]
      by simp
    then show ?thesis
      using Some h_in
      unfolding state_dependent_prequeried_hash_hit_def
      by blast
  qed
qed

lemma receive_alpha_challenge_state_dependent_hit_fresh_or_prequeried:
  assumes out: "Some (a, t) \<in> set_dist (execute receive_alpha_challenge s)"
    and hit: "a \<in> B s"
  shows
    "state_dependent_new_output_hit B s (Some (a, t)) \<or>
      state_dependent_prequeried_hash_hit B
        (AlphaChallenge (PAlphaCounter s) (PState s)) s"
proof -
  have recv:
    "s \<le> t \<and>
     fmlookup (HashMap t)
       (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using receive_alpha_challenge_outcome[OF out] by blast
  show ?thesis
  proof (cases
      "fmlookup (HashMap s)
        (AlphaChallenge (PAlphaCounter s) (PState s))")
    case None
    then have "hash_map_new_output_hit (B s) s t"
      unfolding hash_map_new_output_hit_def
      using recv hit by blast
    then show ?thesis
      unfolding state_dependent_new_output_hit_def
        hash_new_output_hit_event_def
      by simp
  next
    case (Some old_a)
    have old_lookup_t:
      "fmlookup (HashMap t)
        (AlphaChallenge (PAlphaCounter s) (PState s)) = Some old_a"
      by (rule hash_extension_lookup[OF Some conjunct1[OF recv]])
    then have "old_a = a"
      using recv by simp
    then show ?thesis
      using Some hit
      unfolding state_dependent_prequeried_hash_hit_def
      by blast
  qed
qed

lemma wp_receive_alpha_challenge_state_dependent_hit_split:
  "wp_event receive_alpha_challenge
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (a, _) \<Rightarrow> a \<in> B s) s \<le>
    wp_event receive_alpha_challenge
      (state_dependent_new_output_hit B s) s +
    (if state_dependent_prequeried_hash_hit B
          (AlphaChallenge (PAlphaCounter s) (PState s)) s
     then 1 else 0)"
proof -
  let ?bad =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (a, _) \<Rightarrow> a \<in> B s"
  let ?fresh = "state_dependent_new_output_hit B s"
  let ?pre =
    "state_dependent_prequeried_hash_hit B
      (AlphaChallenge (PAlphaCounter s) (PState s)) s"
  have "wp_event receive_alpha_challenge ?bad s \<le>
      wp_event receive_alpha_challenge
        (\<lambda>out. ?fresh out \<or> ?pre) s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute receive_alpha_challenge s)"
      and bad: "?bad out"
    show "?fresh out \<or> ?pre"
    proof (cases out)
      case None
      then show ?thesis
        using bad by simp
    next
      case (Some pair)
      then obtain a t where out_eq: "out = Some (a, t)"
        by (cases pair) auto
      have a_in: "a \<in> B s"
        using bad unfolding out_eq by simp
      show ?thesis
        unfolding out_eq
        by (rule
            receive_alpha_challenge_state_dependent_hit_fresh_or_prequeried
              [where B=B and s=s and a=a and t=t, OF _ a_in])
          (use support out_eq in simp)
    qed
  qed
  also have "... \<le>
      wp_event receive_alpha_challenge ?fresh s +
      wp_event receive_alpha_challenge (\<lambda>_. ?pre) s"
    by (rule wp_event_union_bound)
  also have "... \<le>
      wp_event receive_alpha_challenge ?fresh s +
      (if ?pre then 1 else 0)"
  proof (cases ?pre)
    case True
    have "wp_event receive_alpha_challenge (\<lambda>_. ?pre) s \<le> 1"
      by (rule wp_event_le_1)
    then show ?thesis
      using True by simp
  next
    case False
    then show ?thesis
      by (simp add: wp_event_def wp_def)
  qed
  finally show ?thesis .
qed

lemma wp_event_bind_state_dependent_output_bound_by_cont:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('f, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes none: "\<not> E None"
    and event_imp:
      "\<And>x t out. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        out \<in> set_dist (execute (k x) t) \<Longrightarrow>
        E out \<Longrightarrow> state_dependent_output_hit B t out"
    and cont_bound:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        wp_event (k x) (state_dependent_output_hit B t) t \<le> C"
  shows "wp_event (m \<bind> k) E s \<le> C"
proof (rule wp_event_bind_bound_by_cont
    [where Q=E and m=m and k=k and s=s and C=C])
  show "\<not> E None"
    by (rule none)
next
  fix x t
  assume head: "Some (x, t) \<in> set_dist (execute m s)"
  have "wp_event (k x) E t \<le>
      wp_event (k x) (state_dependent_output_hit B t) t"
    by (rule wp_event_mono_on_support)
      (use head event_imp in blast)
  also have "... \<le> C"
    by (rule cont_bound[OF head])
  finally show "wp_event (k x) E t \<le> C" .
qed

lemma wp_event_bind_state_dependent_new_output_bound_by_cont:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes none: "\<not> E None"
    and event_imp:
      "\<And>x t out. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        out \<in> set_dist (execute (k x) t) \<Longrightarrow>
        E out \<Longrightarrow> state_dependent_new_output_hit B t out"
    and cont_bound:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        wp_event (k x) (state_dependent_new_output_hit B t) t \<le> C"
  shows "wp_event (m \<bind> k) E s \<le> C"
proof (rule wp_event_bind_bound_by_cont
    [where Q=E and m=m and k=k and s=s and C=C])
  show "\<not> E None"
    by (rule none)
next
  fix x t
  assume head: "Some (x, t) \<in> set_dist (execute m s)"
  have "wp_event (k x) E t \<le>
      wp_event (k x) (state_dependent_new_output_hit B t) t"
    by (rule wp_event_mono_on_support)
      (use head event_imp in blast)
  also have "... \<le> C"
    by (rule cont_bound[OF head])
  finally show "wp_event (k x) E t \<le> C" .
qed

lemma wp_event_bind_state_dependent_new_output_bound_by_target_budget:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes none: "\<not> E None"
    and event_imp:
      "\<And>x t out. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        out \<in> set_dist (execute (k x) t) \<Longrightarrow>
        E out \<Longrightarrow> state_dependent_new_output_hit B t out"
    and budget:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_target_budget (B t) n (k x)"
    and value_bound:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_target_budget_value (B t) n \<le> C"
  shows
    "wp_event (m \<bind> k) E s \<le> C"
proof (rule wp_event_bind_state_dependent_new_output_bound_by_cont
    [where E=E and m=m and k=k and s=s and B=B and C=C])
  show "\<not> E None"
    by (rule none)
next
  show "\<And>x t out.
      Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
      out \<in> set_dist (execute (k x) t) \<Longrightarrow>
      E out \<Longrightarrow> state_dependent_new_output_hit B t out"
    by (rule event_imp)
next
  fix x t
  assume head: "Some (x, t) \<in> set_dist (execute m s)"
  have "wp_event (k x) (state_dependent_new_output_hit B t) t \<le>
      hash_target_budget_value (B t) n"
    using budget[OF head]
    unfolding hash_target_budget_def state_dependent_new_output_hit_def
    by blast
  also have "... \<le> C"
    by (rule value_bound[OF head])
  finally show
    "wp_event (k x) (state_dependent_new_output_hit B t) t \<le> C" .
qed

end

end
