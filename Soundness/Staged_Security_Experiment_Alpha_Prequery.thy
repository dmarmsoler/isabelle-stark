(*  Title:      Stark/Staged_Security_Experiment_Alpha_Prequery.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Alpha_Prequery
  imports
    Staged_Security_Experiment_Checked_Prefix
    Soundness_Oracle_Dynamic_Target
begin

section \<open>Staged Composition Accounting\<close>

text \<open>
  Alpha-key prequery support for staged soundness.

  This layer records deterministic facts about the alpha challenge key path.
  It is proof infrastructure for accounting adversarial prequeries to future
  alpha keys; it does not add assumptions or change the oracle model.
\<close>

context soundness
begin

definition alpha_challenge_key_at
  :: "'f protocol_channel \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow>
      'f protocol_hash_input"
  where
    "alpha_challenge_key_at s i as =
      AlphaChallenge (PAlphaCounter s + i)
        (foldl concat (PState s) (take i as))"

definition alpha_vector_key_relation
  :: "'f protocol_channel \<Rightarrow> 'f list set \<Rightarrow> nat \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "alpha_vector_key_relation s B n x y \<longleftrightarrow>
      (\<exists>as \<in> B. \<exists>i < n.
        i < length as \<and>
        x = alpha_challenge_key_at s i as \<and>
        y = as ! i)"

definition alpha_vector_prequery_hit_event
  :: "'f protocol_channel \<Rightarrow> 'f list set \<Rightarrow> nat \<Rightarrow>
      ('r \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "alpha_vector_prequery_hit_event s B n =
      hash_relation_hit_event (alpha_vector_key_relation s B n) s"

definition alpha_vector_prequeried_in_state
  :: "'f protocol_channel \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> bool"
  where
    "alpha_vector_prequeried_in_state s as n \<longleftrightarrow>
      (\<exists>i < n.
        i < length as \<and>
        fmlookup (HashMap s) (alpha_challenge_key_at s i as) =
          Some (as ! i))"

definition alpha_vector_path_fresh
  :: "'f protocol_channel \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> bool"
  where
    "alpha_vector_path_fresh s as n \<longleftrightarrow>
      (\<forall>i < n.
        i < length as \<longrightarrow>
        fmlookup (HashMap s) (alpha_challenge_key_at s i as) = None)"

lemma alpha_vector_key_relation_fiber_card_bound:
  assumes finite_B: "finite B"
  shows "card {y. alpha_vector_key_relation s B n x y} \<le> card B * n"
proof -
  let ?pairs = "B \<times> {..<n}"
  let ?values = "(\<lambda>(as, i). as ! i) ` ?pairs"
  have subset:
    "{y. alpha_vector_key_relation s B n x y} \<subseteq> ?values"
    unfolding alpha_vector_key_relation_def
    by force
  have finite_values: "finite ?values"
    using finite_B by simp
  have "card {y. alpha_vector_key_relation s B n x y} \<le> card ?values"
    by (rule card_mono[OF finite_values subset])
  also have "... \<le> card ?pairs"
    by (rule card_image_le) (use finite_B in simp)
  also have "... = card B * n"
    using finite_B by simp
  finally show ?thesis .
qed

lemma hash_relation_program_staged_alpha_prefix_alpha_vector_prequery:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
  shows
    "hash_relation_program (alpha_vector_key_relation s B n) (card B * n)
      (staged_alpha_search_queries budgets 0)
      (staged_alpha_prefix_program A)"
  by (rule hash_relation_program_staged_alpha_prefix_program
      [OF wf controlled])
    (rule alpha_vector_key_relation_fiber_card_bound[OF finite_B])

lemma staged_alpha_prefix_alpha_vector_prequery_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
  shows
    "wp_event (staged_alpha_prefix_program A)
      (alpha_vector_prequery_hit_event s B n) s \<le>
      hash_relation_budget_value (card B * n)
        (staged_alpha_search_queries budgets 0)"
proof -
  have program:
    "hash_relation_program (alpha_vector_key_relation s B n) (card B * n)
      (staged_alpha_search_queries budgets 0)
      (staged_alpha_prefix_program A)"
    by (rule hash_relation_program_staged_alpha_prefix_alpha_vector_prequery
        [OF wf controlled finite_B])
  then have budget:
    "hash_relation_budget (alpha_vector_key_relation s B n) (card B * n)
      (staged_alpha_search_queries budgets 0)
      (staged_alpha_prefix_program A)"
    unfolding hash_relation_program_def by simp
  show ?thesis
    using budget
    unfolding alpha_vector_prequery_hit_event_def
      hash_relation_budget_def by blast
qed

lemma staged_alpha_prefix_event_bound_from_hash_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
    and event_imp:
      "\<And>x t. Some (x, t) \<in>
          set_dist (execute (staged_alpha_prefix_program A) s) \<Longrightarrow>
        E (Some (x, t)) \<Longrightarrow> hash_relation_hit R s t"
    and none: "\<not> E None"
  shows
    "wp_event (staged_alpha_prefix_program A) E s \<le>
      hash_relation_budget_value b (staged_alpha_search_queries budgets 0)"
proof -
  have program:
    "hash_relation_program R b (staged_alpha_search_queries budgets 0)
      (staged_alpha_prefix_program A)"
    by (rule hash_relation_program_staged_alpha_prefix_program
        [OF wf controlled fibers])
  have
    "wp_event (staged_alpha_prefix_program A) E s \<le>
      wp_event (staged_alpha_prefix_program A)
        (hash_relation_hit_event R s) s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute (staged_alpha_prefix_program A) s)"
      and event: "E out"
    show "hash_relation_hit_event R s out"
    proof (cases out)
      case None
      then show ?thesis using none event by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) simp
      have "hash_relation_hit R s t"
        by (rule event_imp[of x t]) (use support event Some xt in simp_all)
      then show ?thesis
        unfolding Some xt hash_relation_hit_event_def by simp
    qed
  qed
  also have "... \<le>
      hash_relation_budget_value b (staged_alpha_search_queries budgets 0)"
    using program unfolding hash_relation_program_def hash_relation_budget_def
    by blast
  finally show ?thesis .
qed

lemma alpha_vector_path_fresh_Cons_tail:
  assumes fresh: "alpha_vector_path_fresh s (a # xs) (Suc n)"
    and recv:
      "Some (a, t) \<in> set_dist (execute receive_alpha_challenge s)"
    and record_out:
      "Some ((), u) \<in> set_dist (execute (record_staged_message a) t)"
  shows "alpha_vector_path_fresh u xs n"
proof -
  have recv_fields:
    "PAlphaCounter t = Suc (PAlphaCounter s)"
    "PState t = PState s"
    "fmlookup (HashMap t)
      (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using receive_alpha_challenge_outcome[OF recv]
      receive_alpha_challenge_counter_outcome[OF recv]
    by simp_all
  have u_eq:
    "u = t\<lparr>
      PState := concat (PState t) a,
      PTranscript := PTranscript t @ [a]\<rparr>"
    by (rule record_staged_message_outcome[OF record_out])
  show ?thesis
    unfolding alpha_vector_path_fresh_def
  proof (intro allI impI)
    fix i
    assume i_bound: "i < n"
      and i_len: "i < length xs"
    let ?tail_key = "alpha_challenge_key_at u i xs"
    let ?full_key = "alpha_challenge_key_at s (Suc i) (a # xs)"
    have key_eq: "?tail_key = ?full_key"
      unfolding alpha_challenge_key_at_def u_eq
      using recv_fields
      by simp
    have full_none:
      "fmlookup (HashMap s) ?full_key = None"
      using fresh i_bound i_len
      unfolding alpha_vector_path_fresh_def
      by simp
    have key_ne:
      "?full_key \<noteq> AlphaChallenge (PAlphaCounter s) (PState s)"
      unfolding alpha_challenge_key_at_def by simp
    have lookup_t:
      "fmlookup (HashMap t) ?full_key = None"
      using receive_alpha_challenge_preserves_other_lookup[OF recv key_ne]
        full_none
      by simp
    show "fmlookup (HashMap u) ?tail_key = None"
      using lookup_t key_eq unfolding u_eq by simp
  qed
qed

lemma wp_staged_alpha_program_exact_challenges_bound_from_path_fresh:
  assumes len: "length as = n"
    and fresh: "alpha_vector_path_fresh s as n"
  shows
    "wp_event (staged_alpha_program n)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as', _) \<Rightarrow> as' = as) s \<le>
      (1 / nnreal size) ^ n"
  using len fresh
proof (induction n arbitrary: as s)
  case 0
  then have as_empty: "as = []"
    by simp
  show ?case
    unfolding as_empty by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  obtain a as_tail where as_eq: "as = a # as_tail"
    using Suc.prems(1) by (cases as) auto
  have len_tail: "length as_tail = n"
    using Suc.prems(1) as_eq by simp
  let ?tail =
    "staged_alpha_program n ::
      ('f list, 'f protocol_channel) state_monad"
  let ?Q =
    "\<lambda>out :: ('f list \<times>
        'f protocol_channel) option.
      case out of None \<Rightarrow> False | Some (as', _) \<Rightarrow> as' = as"
  let ?Head =
    "\<lambda>out :: ('f \<times>
        'f protocol_channel) option.
      case out of None \<Rightarrow> False | Some (a0, _) \<Rightarrow> a0 \<in> {a}"
  have head_fresh:
    "fmlookup (HashMap s)
      (AlphaChallenge (PAlphaCounter s) (PState s)) = None"
  proof -
    have "fmlookup (HashMap s)
        (alpha_challenge_key_at s 0 (a # as_tail)) = None"
      using Suc.prems(2)
      unfolding as_eq alpha_vector_path_fresh_def by simp
    then show ?thesis
      unfolding alpha_challenge_key_at_def by simp
  qed
  have head_bound:
    "wp_event receive_alpha_challenge ?Head s \<le> 1 / nnreal size"
  proof -
    have "wp_event receive_alpha_challenge ?Head s =
        nnreal (card ({a} :: 'f set)) / nnreal size"
      by (rule wp_receive_alpha_challenge_fresh_set[OF head_fresh])
    then show ?thesis by simp
  qed
  have bind_bound:
    "wp_event
      (receive_alpha_challenge \<bind>
        (\<lambda>a0. record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind>
            (\<lambda>as'. return (a0 # as')))))
      ?Q s \<le>
      wp_event receive_alpha_challenge ?Head s *
        (1 / nnreal size) ^ n"
  proof (rule wp_event_bind_bound_by_head_and_cont[where P = ?Head])
    show "\<not> ?Q None"
      by simp
  next
    fix a0 t
    assume recv:
      "Some (a0, t) \<in> set_dist (execute receive_alpha_challenge s)"
      and not_head: "\<not> ?Head (Some (a0, t))"
    have a0_ne: "a0 \<noteq> a"
      using not_head by simp
    have cont_false:
      "wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t \<le>
       wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        (\<lambda>_ :: ('f list \<times> 'f protocol_channel) option. False) t"
      by (rule wp_event_mono_on_support)
        (use a0_ne as_eq in
          \<open>auto simp: wpsimps elim!: set_dist_bindE
              split: option.splits prod.splits\<close>)
    also have "... = 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
    finally have le_zero:
      "wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t \<le> 0" .
    show
      "wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t = 0"
      by (rule antisym[OF le_zero]) simp
  next
    fix a0 t
    assume recv:
      "Some (a0, t) \<in> set_dist (execute receive_alpha_challenge s)"
      and head: "?Head (Some (a0, t))"
    have a0_eq: "a0 = a"
      using head by simp
    have record_cont_bound:
      "wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t \<le> (1 / nnreal size) ^ n"
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?Q None"
        by simp
    next
      fix uu u
      assume record_out:
        "Some (uu, u) \<in>
          set_dist (execute (record_staged_message a0) t)"
      have record_unit:
        "Some ((), u) \<in>
          set_dist (execute (record_staged_message a0) t)"
        using record_out by (cases uu) simp
      have tail_fresh: "alpha_vector_path_fresh u as_tail n"
      proof -
        have fresh_cons:
          "alpha_vector_path_fresh s (a # as_tail) (Suc n)"
          using Suc.prems(2) unfolding as_eq .
        have recv_a:
          "Some (a, t) \<in> set_dist (execute receive_alpha_challenge s)"
          using recv a0_eq by simp
        have record_a:
          "Some ((), u) \<in> set_dist (execute (record_staged_message a) t)"
          using record_unit a0_eq by simp
        show ?thesis
          by (rule alpha_vector_path_fresh_Cons_tail
              [OF fresh_cons recv_a record_a])
      qed
      have tail_bound:
        "wp_event ?tail
          (\<lambda>out. case out of None \<Rightarrow> False
            | Some (as', _) \<Rightarrow> as' = as_tail) u
          \<le> (1 / nnreal size) ^ n"
        by (rule Suc.IH[OF len_tail tail_fresh])
      have cont_eq:
        "wp_event
          (?tail \<bind> (\<lambda>as'. return (a0 # as'))) ?Q u =
         wp_event ?tail
          (\<lambda>out. case out of None \<Rightarrow> False
            | Some (as', _) \<Rightarrow> as' = as_tail) u"
        by (simp add: wp_event_bind_return_map a0_eq as_eq
            split: option.splits prod.splits)
      show
        "wp_event (?tail \<bind> (\<lambda>as'. return (a0 # as'))) ?Q u
          \<le> (1 / nnreal size) ^ n"
        unfolding cont_eq by (rule tail_bound)
    qed
    show
      "wp_event
        (record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t \<le> (1 / nnreal size) ^ n"
      by (rule record_cont_bound)
  qed
  have "wp_event (staged_alpha_program (Suc n)) ?Q s
      \<le> wp_event receive_alpha_challenge ?Head s *
        (1 / nnreal size) ^ n"
    unfolding staged_alpha_program.simps by (rule bind_bound)
  also have "... \<le> (1 / nnreal size) * (1 / nnreal size) ^ n"
    by (rule mult_right_mono[OF head_bound]) simp
  also have "... = (1 / nnreal size) ^ Suc n"
    by simp
  finally show ?case .
qed

lemma wp_staged_alpha_program_finite_set_bound_from_path_fresh:
  assumes finite_B: "finite B"
    and lengths: "\<And>as. as \<in> B \<Longrightarrow> length as = n"
    and fresh: "\<And>as. as \<in> B \<Longrightarrow> alpha_vector_path_fresh s as n"
  shows
    "wp_event (staged_alpha_program n)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le>
      nnreal (card B) / (nnreal size) ^ n"
proof -
  let ?P =
    "\<lambda>a out. case out of None \<Rightarrow> False
      | Some (as', _) \<Rightarrow> as' = a"
  have event_mono:
    "wp_event (staged_alpha_program n)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le>
      wp_event (staged_alpha_program n)
        (\<lambda>out. \<exists>as\<in>B. ?P as out) s"
    by (rule wp_event_mono) (auto split: option.splits prod.splits)
  also have "... \<le>
      (\<Sum>a\<in>B. wp_event (staged_alpha_program n) (?P a) s)"
    by (rule wp_event_finite_UN_bound[where A = B and P = ?P])
      (use finite_B in simp_all)
  also have "... \<le> (\<Sum>as\<in>B. (1 / nnreal size) ^ n)"
  proof (rule sum_mono)
    fix as
    assume as_in: "as \<in> B"
    show
      "wp_event (staged_alpha_program n) (?P as) s \<le>
        (1 / nnreal size) ^ n"
      by (rule wp_staged_alpha_program_exact_challenges_bound_from_path_fresh
          [OF lengths[OF as_in] fresh[OF as_in]])
  qed
  also have "... = nnreal (card B) * ((1 / nnreal size) ^ n)"
    using finite_B by simp
  also have "... = nnreal (card B) / (nnreal size) ^ n"
    using size_card by transfer (simp add: power_divide)
  finally show ?thesis .
qed

lemma alpha_vector_prequeried_in_state_imp_hash_relation_hit:
  assumes prequeried: "alpha_vector_prequeried_in_state s as n"
    and member: "as \<in> B"
    and initial_absent:
      "\<And>i. i < n \<Longrightarrow> i < length as \<Longrightarrow>
        fmlookup (HashMap initial) (alpha_challenge_key_at s i as) = None"
  shows "hash_relation_hit (alpha_vector_key_relation s B n) initial s"
proof -
  from prequeried obtain i where
    i_n: "i < n"
    and i_len: "i < length as"
    and lookup:
      "fmlookup (HashMap s) (alpha_challenge_key_at s i as) =
        Some (as ! i)"
    unfolding alpha_vector_prequeried_in_state_def by blast
  have relation:
    "alpha_vector_key_relation s B n (alpha_challenge_key_at s i as)
      (as ! i)"
    unfolding alpha_vector_key_relation_def
    using member i_n i_len by blast
  show ?thesis
    unfolding hash_relation_hit_def
    using initial_absent[OF i_n i_len] lookup relation by blast
qed

lemma alpha_vector_prequeried_in_state_imp_hash_relation_hit_empty_initial:
  assumes prequeried: "alpha_vector_prequeried_in_state s as n"
    and member: "as \<in> B"
    and empty: "HashMap initial = fmempty"
  shows "hash_relation_hit (alpha_vector_key_relation s B n) initial s"
  by (rule alpha_vector_prequeried_in_state_imp_hash_relation_hit
      [OF prequeried member])
    (simp add: empty)

lemma staged_alpha_program_outcome_lookup:
  assumes outcome:
    "Some (as, t) \<in> set_dist (execute (staged_alpha_program n) s)"
    and i_bound: "i < n"
  shows
    "fmlookup (HashMap t)
      (AlphaChallenge (PAlphaCounter s + i)
        (foldl concat (PState s) (take i as))) = Some (as ! i)"
  using outcome i_bound
proof (induction n arbitrary: as s t i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from staged_alpha_program_Suc_outcomeE[OF Suc.prems(1)]
  obtain a as' s1 s2 where
    challenge_out:
      "Some (a, s1) \<in> set_dist (execute receive_alpha_challenge s)"
    and record_out:
      "Some ((), s2) \<in> set_dist (execute (record_staged_message a) s1)"
    and rest_out:
      "Some (as', t) \<in>
        set_dist (execute (staged_alpha_program n) s2)"
    and as_eq: "as = a # as'"
    .
  have challenge_lookup:
    "fmlookup (HashMap s1)
      (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using receive_alpha_challenge_outcome[OF challenge_out] by blast
  have challenge_counter:
    "PAlphaCounter s1 = Suc (PAlphaCounter s)"
    using receive_alpha_challenge_counter_outcome[OF challenge_out] by simp
  have record_eq:
    "s2 = s1\<lparr>
      PState := concat (PState s1) a,
      PTranscript := PTranscript s1 @ [a]\<rparr>"
    by (rule record_staged_message_outcome[OF record_out])
  have s2_fields:
    "HashMap s2 = HashMap s1"
    "PState s2 = concat (PState s) a"
    "PAlphaCounter s2 = Suc (PAlphaCounter s)"
    unfolding record_eq
    using receive_alpha_challenge_outcome[OF challenge_out]
      challenge_counter
    by simp_all
  have rest_ext: "s2 \<le> t"
  proof -
    have "hash_target_program {} n (staged_alpha_program n)"
      by (rule hash_target_program_staged_alpha_program)
    then show ?thesis
      using rest_out
      unfolding hash_target_program_def hash_extension_preserving_def
      by blast
  qed
  show ?case
  proof (cases i)
    case 0
    have lookup_s2:
      "fmlookup (HashMap s2)
        (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
      using challenge_lookup unfolding s2_fields by simp
    have lookup_t:
      "fmlookup (HashMap t)
        (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
      by (rule hash_extension_lookup[OF lookup_s2 rest_ext])
    then show ?thesis
      using 0 as_eq by simp
  next
    case (Suc j)
    then have j_bound: "j < n"
      using Suc.prems(2) by simp
    have rest_lookup:
      "fmlookup (HashMap t)
        (AlphaChallenge (PAlphaCounter s2 + j)
          (foldl concat (PState s2) (take j as'))) = Some (as' ! j)"
      by (rule Suc.IH[OF rest_out j_bound])
    show ?thesis
      using rest_lookup
      unfolding Suc as_eq s2_fields
      by simp
  qed
qed

lemma staged_alpha_program_outcome_not_path_fresh_imp_prequeried:
  assumes outcome:
    "Some (as, t) \<in> set_dist (execute (staged_alpha_program n) s)"
    and not_fresh: "\<not> alpha_vector_path_fresh s as n"
  shows "alpha_vector_prequeried_in_state s as n"
proof -
  from not_fresh obtain i old where
    i_bound: "i < n"
    and i_len: "i < length as"
    and lookup_s:
      "fmlookup (HashMap s) (alpha_challenge_key_at s i as) = Some old"
    unfolding alpha_vector_path_fresh_def
    by (metis option.exhaust)
  have lookup_t:
    "fmlookup (HashMap t) (alpha_challenge_key_at s i as) =
      Some (as ! i)"
    using staged_alpha_program_outcome_lookup[OF outcome i_bound]
    unfolding alpha_challenge_key_at_def .
  have ext: "s \<le> t"
  proof -
    have "hash_target_program {} n (staged_alpha_program n)"
      by (rule hash_target_program_staged_alpha_program)
    then show ?thesis
      using outcome
      unfolding hash_target_program_def hash_extension_preserving_def
      by blast
  qed
  have lookup_t_old:
    "fmlookup (HashMap t) (alpha_challenge_key_at s i as) = Some old"
    by (rule hash_extension_lookup[OF lookup_s ext])
  have old_eq: "old = as ! i"
    using lookup_t lookup_t_old by simp
  show ?thesis
    unfolding alpha_vector_prequeried_in_state_def
    using i_bound i_len lookup_s old_eq by blast
qed

lemma wp_staged_alpha_program_set_bound_from_path_fresh_or_prequery:
  assumes subset: "B \<subseteq> alpha_space"
  shows
    "wp_event (staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le>
      nnreal (card B) / nnreal (CARD('f) ^ length spec) +
      (if \<exists>as\<in>B.
          alpha_vector_prequeried_in_state s as (length spec)
       then 1 else 0)"
proof (cases "\<exists>as\<in>B.
    alpha_vector_prequeried_in_state s as (length spec)")
  case True
  have "wp_event (staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le> 1"
    by (rule wp_event_le_1)
  also have "... \<le>
      nnreal (card B) / nnreal (CARD('f) ^ length spec) + 1"
    by simp
  finally show ?thesis
    using True by simp
next
  case False
  let ?BF =
    "{as \<in> B. alpha_vector_path_fresh s as (length spec)}"
  have finite_B: "finite B"
    by (rule finite_subset[OF subset])
      (simp add: alpha_space_def finite_length_lists_UNIV)
  have finite_BF: "finite ?BF"
    using finite_B by simp
  have lengths:
    "\<And>as. as \<in> ?BF \<Longrightarrow> length as = length spec"
    using subset unfolding alpha_space_def by auto
  have fresh:
    "\<And>as. as \<in> ?BF \<Longrightarrow>
      alpha_vector_path_fresh s as (length spec)"
    by simp
  have event_mono:
    "wp_event (staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le>
      wp_event (staged_alpha_program (length spec))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some (as, _) \<Rightarrow> as \<in> ?BF) s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist
        (execute (staged_alpha_program (length spec)) s)"
      and hit:
        "(case out of None \<Rightarrow> False
          | Some (as, _) \<Rightarrow> as \<in> B)"
    show
      "(case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> ?BF)"
    proof (cases out)
      case None
      then show ?thesis using hit by simp
    next
      case (Some result)
      then obtain as t where out_eq: "out = Some (as, t)"
        by (cases result) simp
      have as_in: "as \<in> B"
        using hit unfolding out_eq by simp
      have outcome:
        "Some (as, t) \<in>
          set_dist (execute (staged_alpha_program (length spec)) s)"
        using support unfolding out_eq .
      have path_fresh:
        "alpha_vector_path_fresh s as (length spec)"
      proof (rule ccontr)
        assume "\<not> alpha_vector_path_fresh s as (length spec)"
        then have "alpha_vector_prequeried_in_state s as (length spec)"
          by (rule
              staged_alpha_program_outcome_not_path_fresh_imp_prequeried
              [OF outcome])
        then show False
          using False as_in by blast
      qed
      show ?thesis
        unfolding out_eq using as_in path_fresh by simp
    qed
  qed
  also have "... \<le>
      nnreal (card ?BF) / (nnreal size) ^ length spec"
    by (rule wp_staged_alpha_program_finite_set_bound_from_path_fresh
        [OF finite_BF lengths fresh])
  also have "... \<le> nnreal (card B) / (nnreal size) ^ length spec"
  proof -
    have "card ?BF \<le> card B"
      by (rule card_mono[OF finite_B]) blast
    then show ?thesis
      apply (subst nn2real_le_iff[symmetric])
      by (simp add: divide_right_mono)
  qed
  also have "... =
      nnreal (card B) / nnreal (CARD('f) ^ length spec)"
    using size_card by simp
  finally show ?thesis
    using False by simp
qed

lemma wp_staged_alpha_program_set_bound_excluding_prequeried:
  assumes subset: "B \<subseteq> alpha_space"
  shows
    "wp_event (staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow>
            as \<in> B \<and>
            \<not> alpha_vector_prequeried_in_state s as (length spec))
      s \<le> nnreal (card B) / nnreal (CARD('f) ^ length spec)"
proof -
  let ?BF =
    "{as \<in> B. alpha_vector_path_fresh s as (length spec)}"
  have finite_B: "finite B"
    by (rule finite_subset[OF subset])
      (simp add: alpha_space_def finite_length_lists_UNIV)
  have finite_BF: "finite ?BF"
    using finite_B by simp
  have lengths:
    "\<And>as. as \<in> ?BF \<Longrightarrow> length as = length spec"
    using subset unfolding alpha_space_def by auto
  have fresh:
    "\<And>as. as \<in> ?BF \<Longrightarrow>
      alpha_vector_path_fresh s as (length spec)"
    by simp
  have event_mono:
    "wp_event (staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow>
            as \<in> B \<and>
            \<not> alpha_vector_prequeried_in_state s as (length spec))
      s \<le>
      wp_event (staged_alpha_program (length spec))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some (as, _) \<Rightarrow> as \<in> ?BF) s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist
        (execute (staged_alpha_program (length spec)) s)"
      and hit:
        "(case out of None \<Rightarrow> False
          | Some (as, _) \<Rightarrow>
              as \<in> B \<and>
              \<not> alpha_vector_prequeried_in_state s as (length spec))"
    show
      "(case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> ?BF)"
    proof (cases out)
      case None
      then show ?thesis using hit by simp
    next
      case (Some result)
      then obtain as t where out_eq: "out = Some (as, t)"
        by (cases result) simp
      have as_in: "as \<in> B"
        and not_prequeried:
          "\<not> alpha_vector_prequeried_in_state s as (length spec)"
        using hit unfolding out_eq by simp_all
      have outcome:
        "Some (as, t) \<in>
          set_dist (execute (staged_alpha_program (length spec)) s)"
        using support unfolding out_eq .
      have path_fresh:
        "alpha_vector_path_fresh s as (length spec)"
      proof (rule ccontr)
        assume "\<not> alpha_vector_path_fresh s as (length spec)"
        then have "alpha_vector_prequeried_in_state s as (length spec)"
          by (rule
              staged_alpha_program_outcome_not_path_fresh_imp_prequeried
              [OF outcome])
        then show False using not_prequeried by contradiction
      qed
      show ?thesis
        unfolding out_eq using as_in path_fresh by simp
    qed
  qed
  also have "... \<le>
      nnreal (card ?BF) / (nnreal size) ^ length spec"
    by (rule wp_staged_alpha_program_finite_set_bound_from_path_fresh
        [OF finite_BF lengths fresh])
  also have "... \<le> nnreal (card B) / (nnreal size) ^ length spec"
  proof -
    have "card ?BF \<le> card B"
      by (rule card_mono[OF finite_B]) blast
    then show ?thesis
      apply (subst nn2real_le_iff[symmetric])
      by (simp add: divide_right_mono)
  qed
  also have "... =
      nnreal (card B) / nnreal (CARD('f) ^ length spec)"
    using size_card by simp
  finally show ?thesis .
qed

lemma staged_after_alpha_prefix_program_alpha_list_bound_from_path_fresh_or_prequery:
  assumes subset: "B \<subseteq> alpha_space"
  shows
    "wp_event
      (staged_after_alpha_prefix_program A
        (fr, trace_roots, trace_bs, trace_final))
      (staged_transcript_alpha_list_hit B) s \<le>
      nnreal (card B) / nnreal (CARD('f) ^ length spec) +
      (if \<exists>as\<in>B.
          alpha_vector_prequeried_in_state s as (length spec)
       then 1 else 0)"
proof -
  have alpha_bound:
    "wp_event (staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le>
      nnreal (card B) / nnreal (CARD('f) ^ length spec) +
      (if \<exists>as\<in>B.
          alpha_vector_prequeried_in_state s as (length spec)
       then 1 else 0)"
    by (rule wp_staged_alpha_program_set_bound_from_path_fresh_or_prequery
        [OF subset])
  show ?thesis
    by (rule staged_after_alpha_prefix_program_alpha_list_bound_from_alpha_program
        [OF alpha_bound])
qed

end

end
