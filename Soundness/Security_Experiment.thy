(*  Title:      Stark/Security_Experiment.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Security_Experiment
  imports
    Soundness_Oracle
begin

type_synonym 'f semantic_adversary =
  "('f list, 'f protocol_channel) state_monad"

context soundness
begin

text \<open>
  A semantic adversary is an arbitrary probabilistic state-monad program that
  returns a complete proof transcript.  Admissibility states the random-oracle
  laws needed by the security proof: oracle consistency, bounded range growth,
  bounded collisions, and bounded hits on every fixed target set.

  This interface deliberately does not prescribe an attacker programming
  language.  A future capability-safe command language may expose only
  probabilistic computation and random-oracle queries, with a refinement
  theorem showing that every query-bounded command program satisfies
  \<^term>\<open>admissible_adversary\<close>.
\<close>

definition adversary_initial_state :: "'f protocol_channel"
  where
    "adversary_initial_state =
      \<lparr>HashMap = fmempty, PState = 0, PTranscript = [],
       PTraceFriCounter = 0, PCompositionFriCounter = 0,
       PAlphaCounter = 0, PQueryCounter = 0\<rparr>"

definition admissible_adversary
  :: "nat \<Rightarrow> 'f semantic_adversary \<Rightarrow> bool"
  where
    "admissible_adversary q A \<longleftrightarrow>
      hash_extension_preserving A \<and>
      hash_range_budget q A \<and>
      hash_collision_budget q A \<and>
      (\<forall>B. hash_target_program B q A)"

lemma adversary_initial_state_simps[simp]:
  "HashMap adversary_initial_state = fmempty"
  "PState adversary_initial_state = 0"
  "PTranscript adversary_initial_state = []"
  "PTraceFriCounter adversary_initial_state = 0"
  "PCompositionFriCounter adversary_initial_state = 0"
  "PAlphaCounter adversary_initial_state = 0"
  "PQueryCounter adversary_initial_state = 0"
  unfolding adversary_initial_state_def by simp_all

lemma adversary_initial_state_eq_verifier_initial_state:
  "adversary_initial_state = verifier_initial_state []"
  unfolding adversary_initial_state_def verifier_initial_state_def by simp

lemma admissible_adversary_extension:
  assumes "admissible_adversary q A"
  shows "hash_extension_preserving A"
  using assms unfolding admissible_adversary_def by simp

lemma admissible_adversary_range:
  assumes "admissible_adversary q A"
  shows "hash_range_budget q A"
  using assms unfolding admissible_adversary_def by simp

lemma admissible_adversary_collision:
  assumes "admissible_adversary q A"
  shows "hash_collision_budget q A"
  using assms unfolding admissible_adversary_def by simp

lemma admissible_adversary_target:
  assumes "admissible_adversary q A"
  shows "hash_target_program B q A"
  using assms unfolding admissible_adversary_def by simp

definition verifier_state_from_adversary
  :: "'f protocol_channel \<Rightarrow> 'f list \<Rightarrow> 'f protocol_channel"
  where
    "verifier_state_from_adversary s tr =
      \<lparr>HashMap = HashMap s, PState = 0, PTranscript = tr,
       PTraceFriCounter = 0, PCompositionFriCounter = 0,
       PAlphaCounter = 0, PQueryCounter = 0\<rparr>"

lemma verifier_state_from_adversary_simps[simp]:
  "HashMap (verifier_state_from_adversary s tr) = HashMap s"
  "PState (verifier_state_from_adversary s tr) = 0"
  "PTranscript (verifier_state_from_adversary s tr) = tr"
  "PTraceFriCounter (verifier_state_from_adversary s tr) = 0"
  "PCompositionFriCounter (verifier_state_from_adversary s tr) = 0"
  "PAlphaCounter (verifier_state_from_adversary s tr) = 0"
  "PQueryCounter (verifier_state_from_adversary s tr) = 0"
  unfolding verifier_state_from_adversary_def by simp_all

lemma verifier_state_from_adversary_empty:
  "verifier_state_from_adversary adversary_initial_state tr =
    verifier_initial_state tr"
  unfolding verifier_state_from_adversary_def adversary_initial_state_def
    verifier_initial_state_def
  by simp

lemma verifier_state_from_adversary_hash_extends:
  assumes "s \<le> t"
  shows "verifier_state_from_adversary s tr \<le>
    verifier_state_from_adversary t tr"
  using assms
  unfolding verifier_state_from_adversary_def less_eq_hash_ext_def
    less_eq_fmap_def
  by simp

definition verifier_state_transfer
  :: "'f list \<Rightarrow> (unit, 'f protocol_channel) state_monad"
  where
    "verifier_state_transfer tr =
      get \<bind> (\<lambda>s. put (verifier_state_from_adversary s tr))"

lemma verifier_state_transfer_outcomeE:
  assumes
    "Some ((), t) \<in> set_dist (execute (verifier_state_transfer tr) s)"
  shows "t = verifier_state_from_adversary s tr"
  using assms unfolding verifier_state_transfer_def
  by (auto elim!: set_dist_bindE)

lemma hash_map_preserving_verifier_state_transfer:
  "hash_map_preserving (verifier_state_transfer tr)"
  unfolding hash_map_preserving_def
  using verifier_state_transfer_outcomeE by fastforce

lemma hash_map_preserving_imp_hash_range_budget_zero_semantic:
  fixes m :: "('r, 'f protocol_channel) state_monad"
  assumes preserving: "hash_map_preserving m"
  shows "hash_range_budget 0 m"
  using preserving
  unfolding hash_range_budget_def hash_map_preserving_def
    hash_map_output_values_def
  by auto

lemma hash_map_preserving_imp_hash_collision_budget_zero_semantic:
  fixes m :: "('r, 'f protocol_channel) state_monad"
  assumes preserving: "hash_map_preserving m"
  shows "hash_collision_budget 0 m"
  unfolding hash_collision_budget_def
proof (intro allI impI)
  fix s :: "'f protocol_channel"
  assume clean: "\<not> hash_map_output_collision s"
  have no_event:
    "\<And>out. out \<in> set_dist (execute m s) \<Longrightarrow>
      \<not> hash_new_collision_event s out"
  proof -
    fix out
    assume support: "out \<in> set_dist (execute m s)"
    show "\<not> hash_new_collision_event s out"
    proof (cases out)
      case None
      then show ?thesis
        unfolding hash_new_collision_event_def by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) simp
      have same: "HashMap t = HashMap s"
        using preserving support Some xt
        unfolding hash_map_preserving_def by blast
      show ?thesis
        using clean same Some xt
        unfolding hash_new_collision_event_def
          hash_map_new_output_collision_def hash_map_output_collision_def
        by simp
    qed
  qed
  have no_event_dom:
    "\<And>out. out \<in> dom (dist (execute m s)) \<Longrightarrow>
      \<not> hash_new_collision_event s out"
    using no_event unfolding set_dist_def by blast
  have "wp_event m (hash_new_collision_event s) s = 0"
    unfolding wp_event_def wp_def dist_expect_def
    by (intro sum.neutral) (simp add: no_event_dom)
  then show
    "wp_event m (hash_new_collision_event s) s \<le>
      hash_collision_budget_value
        (card (hash_map_output_values s)) 0"
    unfolding hash_collision_budget_value_def by simp
qed

lemma hash_range_budget_verifier_state_transfer:
  "hash_range_budget 0 (verifier_state_transfer tr)"
  by (rule hash_map_preserving_imp_hash_range_budget_zero_semantic)
    (rule hash_map_preserving_verifier_state_transfer)

lemma hash_collision_budget_verifier_state_transfer:
  "hash_collision_budget 0 (verifier_state_transfer tr)"
  by (rule hash_map_preserving_imp_hash_collision_budget_zero_semantic)
    (rule hash_map_preserving_verifier_state_transfer)

lemma hash_range_budget_verifier_after_adversary:
  "hash_range_budget verifier_hash_query_budget
    (verifier_state_transfer tr \<bind> (\<lambda>_. verify_monad))"
proof -
  have range:
    "hash_range_budget (0 + verifier_hash_query_budget)
      (verifier_state_transfer tr \<bind> (\<lambda>_. verify_monad))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_verifier_state_transfer,
        rule hash_range_budget_verify_monad)
  then show ?thesis by simp
qed

lemma hash_collision_budget_verifier_after_adversary:
  "hash_collision_budget verifier_hash_query_budget
    (verifier_state_transfer tr \<bind> (\<lambda>_. verify_monad))"
proof -
  have collision:
    "hash_collision_budget (0 + verifier_hash_query_budget)
      (verifier_state_transfer tr \<bind> (\<lambda>_. verify_monad))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_verifier_state_transfer,
        rule hash_collision_budget_verifier_state_transfer,
        rule hash_range_budget_verify_monad,
        rule hash_collision_budget_verify_monad)
  then show ?thesis by simp
qed

definition security_experiment
  :: "'f semantic_adversary \<Rightarrow>
      (unit list, 'f protocol_channel) state_monad"
  where
    "security_experiment A =
      A \<bind> (\<lambda>tr.
        verifier_state_transfer tr \<bind> (\<lambda>_. verify_monad))"

definition adversary_acceptance_probability
  :: "'f semantic_adversary \<Rightarrow> prob"
  where
    "adversary_acceptance_probability A =
      wp_event (security_experiment A)
        (\<lambda>out. \<not> Option.is_none out) adversary_initial_state"

lemma security_experiment_outcomeE:
  assumes outcome:
    "Some (result, final_state) \<in>
      set_dist (execute (security_experiment A) initial_state)"
  obtains tr attacker_state where
    "Some (tr, attacker_state) \<in> set_dist (execute A initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state tr))"
  using outcome
  unfolding security_experiment_def verifier_state_transfer_def
  by (auto elim!: set_dist_bindE intro: that)

lemma accepted_security_experimentE:
  assumes outcome:
    "out \<in> set_dist
      (execute (security_experiment A) adversary_initial_state)"
    and accepted: "\<not> Option.is_none out"
  obtains result final_state tr attacker_state where
    "out = Some (result, final_state)"
    "Some (tr, attacker_state) \<in>
      set_dist (execute A adversary_initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state tr))"
proof -
  from accepted obtain result final_state where
    out: "out = Some (result, final_state)"
    by (cases out) auto
  from security_experiment_outcomeE[OF outcome[unfolded out]]
  obtain tr attacker_state where
    attacker:
      "Some (tr, attacker_state) \<in>
        set_dist (execute A adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state tr))"
    by blast
  show ?thesis
    by (rule that[OF out attacker verifier])
qed

lemma attacker_failure_not_accepted[simp]:
  "\<not> (\<not> Option.is_none
    (None :: (unit list \<times> 'f protocol_channel) option))"
  by simp

lemma security_experiment_success_requires_attacker_success:
  assumes no_success:
    "\<And>tr attacker_state.
      Some (tr, attacker_state) \<notin> set_dist (execute A initial_state)"
  shows
    "Some (result, final_state) \<notin>
      set_dist (execute (security_experiment A) initial_state)"
proof
  assume outcome:
    "Some (result, final_state) \<in>
      set_dist (execute (security_experiment A) initial_state)"
  from security_experiment_outcomeE[OF outcome]
  obtain tr attacker_state where
    "Some (tr, attacker_state) \<in> set_dist (execute A initial_state)"
    by blast
  then show False
    using no_success[of tr attacker_state] by blast
qed

lemma admissible_adversary_outcome_extends:
  assumes admissible: "admissible_adversary q A"
    and outcome:
      "Some (tr, attacker_state) \<in>
        set_dist (execute A adversary_initial_state)"
  shows "adversary_initial_state \<le> attacker_state"
  using admissible_adversary_extension[OF admissible] outcome
  unfolding hash_extension_preserving_def by blast

lemma hash_map_output_values_adversary_initial_state[simp]:
  "hash_map_output_values adversary_initial_state = {}"
  unfolding adversary_initial_state_eq_verifier_initial_state by simp

lemma adversary_initial_state_no_output_collision[simp]:
  "\<not> hash_map_output_collision adversary_initial_state"
  unfolding hash_map_output_collision_def by simp

lemma admissible_adversary_output_range_bound:
  assumes admissible: "admissible_adversary q A"
    and outcome:
      "Some (tr, attacker_state) \<in>
        set_dist (execute A adversary_initial_state)"
  shows "card (hash_map_output_values attacker_state) \<le> q"
proof -
  have
    "card (hash_map_output_values attacker_state) \<le>
      card (hash_map_output_values adversary_initial_state) + q"
    using admissible_adversary_range[OF admissible] outcome
    unfolding hash_range_budget_def by blast
  then show ?thesis by simp
qed

lemma admissible_adversary_collision_bound:
  assumes admissible: "admissible_adversary q A"
  shows
    "wp_event A (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le> hash_collision_budget_value 0 q"
proof -
  have collision_budget: "hash_collision_budget q A"
    by (rule admissible_adversary_collision[OF admissible])
  have
    "wp_event A (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
        hash_collision_budget_value
          (card (hash_map_output_values adversary_initial_state)) q"
    using collision_budget
      adversary_initial_state_no_output_collision
    unfolding hash_collision_budget_def by blast
  then show ?thesis by simp
qed

lemma admissible_adversary_target_bound:
  assumes admissible: "admissible_adversary q A"
  shows
    "wp_event A
      (hash_new_output_hit_event B adversary_initial_state)
      adversary_initial_state \<le> hash_target_budget_value B q"
proof -
  have "hash_target_budget B q A"
    by (rule hash_target_program_budget)
      (rule admissible_adversary_target[OF admissible])
  then show ?thesis
    unfolding hash_target_budget_def by blast
qed

lemma hash_range_budget_security_experiment:
  assumes admissible: "admissible_adversary q A"
  shows
    "hash_range_budget (q + verifier_hash_query_budget)
      (security_experiment A)"
  unfolding security_experiment_def
  by (rule hash_range_budget_bind)
    (rule admissible_adversary_range[OF admissible],
      rule hash_range_budget_verifier_after_adversary)

lemma hash_collision_budget_security_experiment:
  assumes admissible: "admissible_adversary q A"
  shows
    "hash_collision_budget (q + verifier_hash_query_budget)
      (security_experiment A)"
  unfolding security_experiment_def
  by (rule hash_collision_budget_bind)
    (rule admissible_adversary_range[OF admissible],
      rule admissible_adversary_collision[OF admissible],
      rule hash_range_budget_verifier_after_adversary,
      rule hash_collision_budget_verifier_after_adversary)

lemma security_experiment_hash_new_collision_bound:
  assumes admissible: "admissible_adversary q A"
  shows
    "wp_event (security_experiment A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (q + verifier_hash_query_budget)"
proof -
  have collision_budget:
    "hash_collision_budget (q + verifier_hash_query_budget)
      (security_experiment A)"
    by (rule hash_collision_budget_security_experiment[OF admissible])
  have
    "wp_event (security_experiment A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value
        (card (hash_map_output_values adversary_initial_state))
        (q + verifier_hash_query_budget)"
    using collision_budget adversary_initial_state_no_output_collision
    unfolding hash_collision_budget_def by blast
  then show ?thesis by simp
qed

lemma hash_map_output_collision_bad_imp_security_new_collision:
  assumes bad: "hash_map_output_collision_bad adversary_initial_state out"
  shows "hash_new_collision_event adversary_initial_state out"
proof -
  have new_bad: "hash_map_new_output_collision_bad adversary_initial_state out"
    by (rule hash_map_output_collision_bad_imp_new_collision_bad_if_initial_clean)
      (use bad in simp_all)
  show ?thesis
    by (rule hash_map_new_output_collision_bad_imp_hash_new_collision_event
        [OF new_bad])
qed

lemma security_experiment_hash_map_output_collision_bad_bound:
  assumes admissible: "admissible_adversary q A"
  shows
    "wp_event (security_experiment A)
      (hash_map_output_collision_bad adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (q + verifier_hash_query_budget)"
proof -
  have "wp_event (security_experiment A)
      (hash_map_output_collision_bad adversary_initial_state)
      adversary_initial_state \<le>
      wp_event (security_experiment A)
        (hash_new_collision_event adversary_initial_state)
        adversary_initial_state"
    by (rule wp_event_mono)
      (rule hash_map_output_collision_bad_imp_security_new_collision)
  also have "... \<le>
      hash_collision_budget_value 0 (q + verifier_hash_query_budget)"
    by (rule security_experiment_hash_new_collision_bound[OF admissible])
  finally show ?thesis .
qed

end

end
