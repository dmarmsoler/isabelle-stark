(*  Title:      Stark/Soundness_FRI_First_Root_RO_Bounded_State_Relation.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Bounded_State_Relation
  imports Soundness_FRI_First_Root_RO_State_Relation
begin

text \<open>
  Query-budget-bounded wrapper for the first-root absorbed query relation.
  The direct fiber keeps the exact query-agreement bound, while map-dependent
  transcript and Merkle drift is charged by the bounded oracle-map domain.
\<close>

context soundness
begin

definition first_root_absorbed_query_relation_bounded
  :: "nat \<Rightarrow>
      (('f protocol_hash_input, 'f) fmap \<Rightarrow>
        'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "first_root_absorbed_query_relation_bounded L M x y \<longleftrightarrow>
    card (fmdom' M) \<le> L \<and>
    first_root_absorbed_query_relation M x y"

lemma fmdom_fmupd[simp]:
  "fmdom' (fmupd x y M) = insert x (fmdom' M)"
  by (auto simp: fmdom'_notI fmlookup_dom'_iff)

lemma card_fmdom_fmupd_mono:
  "card (fmdom' M) \<le> card (fmdom' (fmupd x y M))"
  by (simp add: card_insert_if)


lemma hash_state_relation_budget_hash_fresh:
  assumes steps:
    "\<And>M x. fmlookup M x = None \<Longrightarrow>
      card {y.
        hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  shows
    "hash_state_relation_budget R b 1
      (hash x :: ('f, 'f protocol_channel) state_monad)"
  unfolding hash_state_relation_budget_def
proof
  fix s :: "'f protocol_channel"
  let ?T =
    "{y. hash_state_relation_transition R (HashMap s)
      (fmupd x y (HashMap s))}"
  have exact:
    "wp_event (hash x)
        (hash_state_relation_transition_event R (HashMap s)) s =
      (if fmlookup (HashMap s) x = None
       then nnreal (card ?T) / nnreal size
       else 0)"
    by (rule wp_hash_state_relation_transition)
  show
    "wp_event (hash x)
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      hash_relation_budget_value b 1"
  proof (cases "fmlookup (HashMap s) x")
    case None
    have card_le: "card ?T \<le> b"
      by (rule steps[OF None])
    have
      "wp_event (hash x)
          (hash_state_relation_transition_event R (HashMap s)) s =
        nnreal (card ?T) / nnreal size"
      using exact None by simp
    also have "... \<le> nnreal b / nnreal size"
      by (rule nnreal_nat_divide_right_mono[OF card_le])
    also have "... = hash_relation_budget_value b 1"
      unfolding hash_relation_budget_value_def by simp
    finally show ?thesis .
  next
    case (Some y)
    show ?thesis
      using exact Some
      unfolding hash_relation_budget_value_def by simp
  qed
qed

lemma controlled_ro_program_state_relation_fresh:
  assumes controlled: "controlled_ro_program q m"
    and steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  shows "hash_state_relation_budget R b q m"
  using controlled
proof (induction rule: controlled_ro_program.induct)
  case (Return x)
  show ?case
    by (rule hash_state_relation_budget_zero)
      (rule hash_map_preserving_return)
next
  case Fail
  show ?case
    by (rule hash_state_relation_budget_zero)
      (rule hash_map_preserving_throw)
next
  case (Sample d)
  show ?case
    by (rule hash_state_relation_budget_zero)
      (rule hash_map_preserving_state_independent_sample)
next
  case (Query q k x)
  have tail:
    "\<And>y. hash_state_relation_budget R b q (k y)"
    using Query.IH steps by blast
  have head:
    "hash_state_relation_budget R b 1
      (hash x :: ('f, 'f protocol_channel) state_monad)"
  proof (rule hash_state_relation_budget_hash_fresh)
    fix M :: "('f protocol_hash_input, 'f) fmap"
      and input :: "'f protocol_hash_input"
    assume "fmlookup M input = None"
    then show
      "card {y.
        hash_state_relation_transition R M (fmupd input y M)} \<le> b"
      by (rule steps)  qed
  have
    "hash_state_relation_budget R b (1 + q)
      ((hash x :: ('f, 'f protocol_channel) state_monad) \<bind> k)"
    by (rule hash_state_relation_budget_bind[OF head tail])  then show ?case by simp
next
  case (Bind q m r k)
  have tail:
    "\<And>x. hash_state_relation_budget R b r (k x)"
    using Bind.IH steps by blast
  show ?case
    by (rule hash_state_relation_budget_bind)
      (use Bind.IH steps in blast, rule tail)
next
  case (Weaken q m r)
  show ?case
    by (rule hash_state_relation_budget_mono[OF Weaken.hyps(2)])
      (use Weaken.IH steps in blast)
qed

lemma wp_controlled_ro_program_state_relation_fresh:
  assumes controlled: "controlled_ro_program q m"
    and steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  shows
    "wp_event m
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      nnreal (q * b) / nnreal size"
  using controlled_ro_program_state_relation_fresh[OF controlled steps]
  unfolding hash_state_relation_budget_def
    hash_relation_budget_value_def
  by blast


lemma first_root_bounded_direct_activation_subset:
  assumes fresh: "fmlookup M x = None"
  shows
    "{y.
      hash_state_relation_direct_activation
        (first_root_absorbed_query_relation_bounded L) M x y}
      \<subseteq>
    {y.
      hash_state_relation_direct_activation
        first_root_absorbed_query_relation M x y}"
proof
  fix y
  assume y:
    "y \<in> {y.
      hash_state_relation_direct_activation
        (first_root_absorbed_query_relation_bounded L) M x y}"
  have active_new:
    "hash_state_relation_active
      (first_root_absorbed_query_relation_bounded L)
      (fmupd x y M) x y"
    using y unfolding hash_state_relation_direct_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) x = Some y"
    and bounded_rel_new:
      "first_root_absorbed_query_relation_bounded L
        (fmupd x y M) x y"
    using active_new unfolding hash_state_relation_active_def by blast+
  have rel_new:
    "first_root_absorbed_query_relation (fmupd x y M) x y"
    using bounded_rel_new
    unfolding first_root_absorbed_query_relation_bounded_def by blast
  have original_new:
    "hash_state_relation_active first_root_absorbed_query_relation
      (fmupd x y M) x y"
    unfolding hash_state_relation_active_def
    using lookup_new rel_new by simp
  have original_old:
    "\<not> hash_state_relation_active first_root_absorbed_query_relation
      M x y"
    using fresh unfolding hash_state_relation_active_def by simp
  show
    "y \<in> {y.
      hash_state_relation_direct_activation
        first_root_absorbed_query_relation M x y}"
    unfolding hash_state_relation_direct_activation_def
    using original_new original_old by simp
qed

lemma first_root_bounded_direct_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_direct_activation
        (first_root_absorbed_query_relation_bounded L) M x y}
      \<le> rounds * query_raw_preimage_card_envelope clength"
proof -
  let ?A =
    "{y.
      hash_state_relation_direct_activation
        (first_root_absorbed_query_relation_bounded L) M x y}"
  let ?B =
    "{y.
      hash_state_relation_direct_activation
        first_root_absorbed_query_relation M x y}"
  have subset: "?A \<subseteq> ?B"
    by (rule first_root_bounded_direct_activation_subset[OF fresh])
  have finite_B: "finite ?B"
  proof -
    have "card ?B \<le>
      rounds * query_raw_preimage_card_envelope clength"
      by (rule
        first_root_absorbed_query_relation_direct_fiber_card_bound)
    then show ?thesis
      by simp
  qed
  have "card ?A \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  also have "... \<le>
      rounds * query_raw_preimage_card_envelope clength"
    by (rule
      first_root_absorbed_query_relation_direct_fiber_card_bound)
  finally show ?thesis .
qed

lemma first_root_bounded_drift_activation_subset:
  assumes fresh: "fmlookup M x = None"
  shows
    "{y.
      hash_state_relation_drift_activation
        (first_root_absorbed_query_relation_bounded L) M x y}
      \<subseteq>
    {y.
      hash_state_relation_drift_activation
        first_root_absorbed_query_relation M x y}"
proof
  fix y
  assume y:
    "y \<in> {y.
      hash_state_relation_drift_activation
        (first_root_absorbed_query_relation_bounded L) M x y}"
  then obtain k z where
    key_neq: "k \<noteq> x"
    and active_new:
      "hash_state_relation_active
        (first_root_absorbed_query_relation_bounded L)
        (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active
        (first_root_absorbed_query_relation_bounded L) M k z"
    unfolding hash_state_relation_drift_activation_def by blast
  have lookup_new: "fmlookup (fmupd x y M) k = Some z"
    and bounded_rel_new:
      "first_root_absorbed_query_relation_bounded L
        (fmupd x y M) k z"
    using active_new unfolding hash_state_relation_active_def by blast+
  have domain_new: "card (fmdom' (fmupd x y M)) \<le> L"
    and rel_new:
      "first_root_absorbed_query_relation (fmupd x y M) k z"
    using bounded_rel_new
    unfolding first_root_absorbed_query_relation_bounded_def by blast+
  have domain_old: "card (fmdom' M) \<le> L"
    using card_fmdom_fmupd_mono[of M x y] domain_new
    by linarith
  have original_new:
    "hash_state_relation_active first_root_absorbed_query_relation
      (fmupd x y M) k z"
    unfolding hash_state_relation_active_def
    using lookup_new rel_new by simp
  have original_old:
    "\<not> hash_state_relation_active first_root_absorbed_query_relation
      M k z"
  proof
    assume old:
      "hash_state_relation_active first_root_absorbed_query_relation
        M k z"
    have lookup_old: "fmlookup M k = Some z"
      and rel_old: "first_root_absorbed_query_relation M k z"
      using old unfolding hash_state_relation_active_def by blast+
    have bounded_old:
      "first_root_absorbed_query_relation_bounded L M k z"
      unfolding first_root_absorbed_query_relation_bounded_def
      using domain_old rel_old by simp
    have
      "hash_state_relation_active
        (first_root_absorbed_query_relation_bounded L) M k z"
      unfolding hash_state_relation_active_def
      using lookup_old bounded_old by simp
    then show False using inactive_old by contradiction
  qed
  show
    "y \<in> {y.
      hash_state_relation_drift_activation
        first_root_absorbed_query_relation M x y}"
    unfolding hash_state_relation_drift_activation_def
    using key_neq original_new original_old by blast
qed

lemma first_root_bounded_drift_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
    and domain: "card (fmdom' M) \<le> L"
  shows
    "card {y.
      hash_state_relation_drift_activation
        (first_root_absorbed_query_relation_bounded L) M x y}
      \<le> 5 * L + 2"
proof -
  let ?A =
    "{y.
      hash_state_relation_drift_activation
        (first_root_absorbed_query_relation_bounded L) M x y}"
  let ?B =
    "{y.
      hash_state_relation_drift_activation
        first_root_absorbed_query_relation M x y}"
  have subset: "?A \<subseteq> ?B"
    by (rule first_root_bounded_drift_activation_subset[OF fresh])
  have finite_B: "finite ?B"
  proof -
    have "card ?B \<le> 5 * card (fmdom' M) + 2"
      by (rule
        first_root_absorbed_query_relation_drift_fiber_card_bound[OF fresh])
    then show ?thesis
      by simp
  qed
  have "card ?A \<le> card ?B"
    by (rule card_mono[OF finite_B subset])
  also have "... \<le> 5 * card (fmdom' M) + 2"
    by (rule
      first_root_absorbed_query_relation_drift_fiber_card_bound[OF fresh])
  also have "... \<le> 5 * L + 2"
    using domain by simp
  finally show ?thesis .
qed

lemma first_root_bounded_transition_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
  shows
    "card {y.
      hash_state_relation_transition
        (first_root_absorbed_query_relation_bounded L)
        M (fmupd x y M)}
      \<le>
      rounds * query_raw_preimage_card_envelope clength +
        (5 * L + 2)"
proof (cases "card (fmdom' M) \<le> L")
  case True
  have direct:
    "card {y.
      hash_state_relation_direct_activation
        (first_root_absorbed_query_relation_bounded L) M x y}
      \<le> rounds * query_raw_preimage_card_envelope clength"
    by (rule first_root_bounded_direct_fiber_card_bound[OF fresh])
  have drift:
    "card {y.
      hash_state_relation_drift_activation
        (first_root_absorbed_query_relation_bounded L) M x y}
      \<le> 5 * L + 2"
    by (rule first_root_bounded_drift_fiber_card_bound[OF fresh True])
  show ?thesis
    by (rule hash_state_relation_transition_update_fiber_card_bound[
      OF direct drift])
next
  case False
  have no_active:
    "\<And>y k z.
      \<not> hash_state_relation_active
        (first_root_absorbed_query_relation_bounded L)
        (fmupd x y M) k z"
  proof
    fix y k z
    assume active_new:
      "hash_state_relation_active
        (first_root_absorbed_query_relation_bounded L)
        (fmupd x y M) k z"
    have domain_new: "card (fmdom' (fmupd x y M)) \<le> L"
      using active_new
      unfolding hash_state_relation_active_def
        first_root_absorbed_query_relation_bounded_def
      by blast
    have domain_old: "card (fmdom' M) \<le> L"
      using card_fmdom_fmupd_mono[of M x y] domain_new
      by linarith
    show False using False domain_old by contradiction
  qed
  have no_transition:
    "{y.
      hash_state_relation_transition
        (first_root_absorbed_query_relation_bounded L)
        M (fmupd x y M)} = {}"
    unfolding hash_state_relation_transition_def
    using no_active by auto
  show ?thesis using no_transition by simp
qed

end
end
