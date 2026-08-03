(*  Title:      Stark/Soundness_FRI_Prequery_Core.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Prequery_Core
  imports
    Soundness_FRI_Obligation_Normalization
    Staged_Security_Experiment_Composition_Branch
begin
text \<open>
  Verifier-local FRI challenge prequery accounting.

  The concrete FRI challenge-list bounds require freshness of future
  Trace/Composition FRI challenge keys.  In the staged adversary experiment the
  verifier receives the adversary's final oracle map, so freshness is not
  automatic.  This layer defines the exact verifier-header key paths and proves
  deterministic fresh/prequeried splits.  It does not add assumptions or change
  the oracle model.
\<close>

context soundness
begin

definition trace_fri_challenge_key_at
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      nat \<Rightarrow> 'f protocol_hash_input"
  where
    "trace_fri_challenge_key_at s fr roots i =
      TraceFriChallenge (PTraceFriCounter s + i)
        (foldl concat (concat (PState s) fr) (take (Suc i) roots))"

definition composition_fri_challenge_key_at
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f protocol_hash_input"
  where
    "composition_fri_challenge_key_at s fr trace_roots trace_final as dg
        composition_roots i =
      CompositionFriChallenge (PCompositionFriCounter s + i)
        (foldl concat
          (concat
            (foldl concat
              (concat
                (foldl concat (concat (PState s) fr) trace_roots)
                trace_final)
              as)
            dg)
          (take (Suc i) composition_roots))"

definition trace_fri_challenge_path_fresh
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      nat \<Rightarrow> bool"
  where
    "trace_fri_challenge_path_fresh s fr roots n \<longleftrightarrow>
      (\<forall>i < n.
        i < length roots \<longrightarrow>
        fmlookup (HashMap s) (trace_fri_challenge_key_at s fr roots i) =
          None)"

definition trace_fri_challenge_path_prequeried
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      nat \<Rightarrow> bool"
  where
    "trace_fri_challenge_path_prequeried s fr roots n \<longleftrightarrow>
      (\<exists>i < n.
        i < length roots \<and>
        fmlookup (HashMap s) (trace_fri_challenge_key_at s fr roots i)
          \<noteq> None)"

definition composition_fri_challenge_path_fresh
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> bool"
  where
    "composition_fri_challenge_path_fresh s fr trace_roots trace_final as dg
        composition_roots n \<longleftrightarrow>
      (\<forall>i < n.
        i < length composition_roots \<longrightarrow>
        fmlookup (HashMap s)
          (composition_fri_challenge_key_at s fr trace_roots trace_final
            as dg composition_roots i) = None)"

definition composition_fri_challenge_path_prequeried
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> bool"
  where
    "composition_fri_challenge_path_prequeried s fr trace_roots trace_final as dg
        composition_roots n \<longleftrightarrow>
      (\<exists>i < n.
        i < length composition_roots \<and>
        fmlookup (HashMap s)
          (composition_fri_challenge_key_at s fr trace_roots trace_final
            as dg composition_roots i) \<noteq> None)"

definition trace_fri_challenge_list_fresh_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list set \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_challenge_list_fresh_hit s B out \<longleftrightarrow>
      (\<exists>trace_bs dg comp_bs fr trace_roots trace_final as
          composition_roots final rest.
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        verifier_header_transcript s fr trace_roots trace_final as dg
          composition_roots final rest \<and>
        trace_bs \<in> B \<and>
        trace_fri_challenge_path_fresh s fr trace_roots
          (length trace_roots))"

definition trace_fri_challenge_list_prequery_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list set \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_challenge_list_prequery_hit s B out \<longleftrightarrow>
      (\<exists>trace_bs dg comp_bs fr trace_roots trace_final as
          composition_roots final rest.
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        verifier_header_transcript s fr trace_roots trace_final as dg
          composition_roots final rest \<and>
        trace_bs \<in> B \<and>
        trace_fri_challenge_path_prequeried s fr trace_roots
          (length trace_roots))"

definition composition_fri_challenge_list_fresh_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> ('f \<Rightarrow> 'f list set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_fri_challenge_list_fresh_hit s B out \<longleftrightarrow>
      (\<exists>trace_bs dg comp_bs fr trace_roots trace_final as
          composition_roots final rest.
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        verifier_header_transcript s fr trace_roots trace_final as dg
          composition_roots final rest \<and>
        comp_bs \<in> B dg \<and>
        composition_fri_challenge_path_fresh s fr trace_roots trace_final
          as dg composition_roots (length composition_roots))"

definition composition_fri_challenge_list_prequery_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> ('f \<Rightarrow> 'f list set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_fri_challenge_list_prequery_hit s B out \<longleftrightarrow>
      (\<exists>trace_bs dg comp_bs fr trace_roots trace_final as
          composition_roots final rest.
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        verifier_header_transcript s fr trace_roots trace_final as dg
          composition_roots final rest \<and>
        comp_bs \<in> B dg \<and>
        composition_fri_challenge_path_prequeried s fr trace_roots
          trace_final as dg composition_roots (length composition_roots))"

definition trace_fri_challenge_key_relation
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list set \<Rightarrow> nat \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "trace_fri_challenge_key_relation s B n x y \<longleftrightarrow>
      (\<exists>bs \<in> B. \<exists>fr roots i.
        i < n \<and>
        i < length bs \<and>
        i < length roots \<and>
        x = trace_fri_challenge_key_at s fr roots i \<and>
        y = bs ! i)"

definition composition_fri_challenge_key_relation
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> ('f \<Rightarrow> 'f list set) \<Rightarrow>
      nat \<Rightarrow> 'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "composition_fri_challenge_key_relation s B n x y \<longleftrightarrow>
      (\<exists>dg. \<exists>bs \<in> B dg. \<exists>fr trace_roots trace_final as
          composition_roots i.
        i < n \<and>
        i < length bs \<and>
        i < length composition_roots \<and>
        x = composition_fri_challenge_key_at s fr trace_roots trace_final
          as dg composition_roots i \<and>
        y = bs ! i)"

definition checked_staged_trace_fri_prequery_hit
  :: "'f list set \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_trace_fri_prequery_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, attacker_state) \<Rightarrow>
          let s = verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)
          in staged_trace_fri_challenges data \<in> B \<and>
             trace_fri_challenge_path_prequeried s
               (staged_trace_root data)
               (staged_trace_fri_roots data)
               (length (staged_trace_fri_roots data)))"

definition checked_staged_composition_fri_prequery_hit
  :: "('f \<Rightarrow> 'f list set) \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_composition_fri_prequery_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, attacker_state) \<Rightarrow>
          let s = verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)
          in staged_composition_fri_challenges data \<in>
               B (staged_degree data) \<and>
             composition_fri_challenge_path_prequeried s
               (staged_trace_root data)
               (staged_trace_fri_roots data)
               (staged_trace_final data)
               (staged_alphas data)
               (staged_degree data)
               (staged_composition_fri_roots data)
               (length (staged_composition_fri_roots data)))"

definition checked_staged_trace_fri_prequery_relation
  :: "'f staged_adversary \<Rightarrow> 'f list set \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "checked_staged_trace_fri_prequery_relation A B x y \<longleftrightarrow>
      (\<exists>data attacker_state i.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<and>
        staged_trace_fri_challenges data \<in> B \<and>
        i < ceil_log clength \<and>
        i < length (staged_trace_fri_challenges data) \<and>
        i < length (staged_trace_fri_roots data) \<and>
        x = trace_fri_challenge_key_at
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data) (staged_trace_fri_roots data) i \<and>
        y = staged_trace_fri_challenges data ! i)"

definition checked_staged_composition_fri_prequery_relation
  :: "'f staged_adversary \<Rightarrow> ('f \<Rightarrow> 'f list set) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "checked_staged_composition_fri_prequery_relation A B x y \<longleftrightarrow>
      (\<exists>data attacker_state i.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<and>
        staged_composition_fri_challenges data \<in> B (staged_degree data) \<and>
        i < ceil_log (maxDegree + 1) \<and>
        i < length (staged_composition_fri_challenges data) \<and>
        i < length (staged_composition_fri_roots data) \<and>
        x = composition_fri_challenge_key_at
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data) (staged_trace_fri_roots data)
          (staged_trace_final data) (staged_alphas data)
          (staged_degree data) (staged_composition_fri_roots data) i \<and>
        y = staged_composition_fri_challenges data ! i)"

definition checked_staged_trace_fri_verifier_prequery_relation
  :: "'f staged_adversary \<Rightarrow> 'f list set \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "checked_staged_trace_fri_verifier_prequery_relation A B x y \<longleftrightarrow>
      (\<exists>data attacker_state bs fr roots i.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<and>
        bs \<in> B \<and>
        i < ceil_log clength \<and>
        i < length bs \<and>
        i < length roots \<and>
        x = trace_fri_challenge_key_at
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          fr roots i \<and>
        y = bs ! i)"

definition checked_staged_composition_fri_verifier_prequery_relation
  :: "'f staged_adversary \<Rightarrow> ('f \<Rightarrow> 'f list set) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "checked_staged_composition_fri_verifier_prequery_relation A B x y
      \<longleftrightarrow>
      (\<exists>data attacker_state dg bs fr trace_roots trace_final as
          composition_roots i.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<and>
        bs \<in> B dg \<and>
        i < ceil_log (maxDegree + 1) \<and>
        i < length bs \<and>
        i < length composition_roots \<and>
        x = composition_fri_challenge_key_at
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          fr trace_roots trace_final as dg composition_roots i \<and>
        y = bs ! i)"

lemma trace_fri_challenge_key_relation_fiber_card_bound:
  assumes finite_B: "finite B"
  shows
    "card {y. trace_fri_challenge_key_relation s B n x y} \<le> card B * n"
proof -
  let ?pairs = "B \<times> {..<n}"
  let ?values = "(\<lambda>(bs, i). bs ! i) ` ?pairs"
  have subset:
    "{y. trace_fri_challenge_key_relation s B n x y} \<subseteq> ?values"
    unfolding trace_fri_challenge_key_relation_def
    by force
  have finite_values: "finite ?values"
    using finite_B by simp
  have "card {y. trace_fri_challenge_key_relation s B n x y} \<le>
      card ?values"
    by (rule card_mono[OF finite_values subset])
  also have "... \<le> card ?pairs"
    by (rule card_image_le) (use finite_B in simp)
  also have "... = card B * n"
    using finite_B by simp
  finally show ?thesis .
qed

lemma composition_fri_challenge_key_relation_fiber_card_bound:
  assumes finite_B: "\<And>dg. finite (B dg)"
  shows
    "card {y. composition_fri_challenge_key_relation s B n x y} \<le>
      (\<Sum>dg \<in> (UNIV :: 'f set). card (B dg) * n)"
proof -
  let ?pairs = "(SIGMA dg:(UNIV :: 'f set). B dg \<times> {..<n})"
  let ?values = "(\<lambda>(dg, bs, i). bs ! i) ` ?pairs"
  have subset:
    "{y. composition_fri_challenge_key_relation s B n x y} \<subseteq> ?values"
    unfolding composition_fri_challenge_key_relation_def
    by force
  have finite_values: "finite ?values"
    using finite_B by simp
  have "card {y. composition_fri_challenge_key_relation s B n x y} \<le>
      card ?values"
    by (rule card_mono[OF finite_values subset])
  also have "... \<le> card ?pairs"
    by (rule card_image_le) (use finite_B in simp)
  also have "... =
      (\<Sum>dg \<in> (UNIV :: 'f set). card (B dg \<times> {..<n}))"
    using finite_B by (simp add: card_SigmaI)
  also have "... = (\<Sum>dg \<in> (UNIV :: 'f set). card (B dg) * n)"
    using finite_B by simp
  finally show ?thesis .
qed

lemma hash_relation_program_checked_staged_transcript_trace_fri_prequery:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
  shows
    "hash_relation_program (trace_fri_challenge_key_relation s B n)
      (card B * n)
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
  by (rule hash_relation_program_checked_staged_transcript_program
      [OF wf controlled])
    (rule trace_fri_challenge_key_relation_fiber_card_bound[OF finite_B])

lemma checked_staged_transcript_trace_fri_prequery_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
  shows
    "wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event (trace_fri_challenge_key_relation s B n)
        adversary_initial_state)
      adversary_initial_state \<le>
      hash_relation_budget_value (card B * n)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have program:
    "hash_relation_program (trace_fri_challenge_key_relation s B n)
      (card B * n)
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
    by (rule hash_relation_program_checked_staged_transcript_trace_fri_prequery
        [OF wf controlled finite_B])
  show ?thesis
    using program
    unfolding hash_relation_program_def hash_relation_budget_def by blast
qed

lemma hash_relation_program_checked_staged_transcript_composition_fri_prequery:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
  shows
    "hash_relation_program (composition_fri_challenge_key_relation s B n)
      (\<Sum>dg \<in> (UNIV :: 'f set). card (B dg) * n)
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
  by (rule hash_relation_program_checked_staged_transcript_program
      [OF wf controlled])
    (rule composition_fri_challenge_key_relation_fiber_card_bound
      [OF finite_B])

lemma checked_staged_transcript_composition_fri_prequery_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
  shows
    "wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event
        (composition_fri_challenge_key_relation s B n)
        adversary_initial_state)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set). card (B dg) * n)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have program:
    "hash_relation_program (composition_fri_challenge_key_relation s B n)
      (\<Sum>dg \<in> (UNIV :: 'f set). card (B dg) * n)
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
    by (rule
        hash_relation_program_checked_staged_transcript_composition_fri_prequery
        [OF wf controlled finite_B])
  show ?thesis
    using program
    unfolding hash_relation_program_def hash_relation_budget_def by blast
qed

end

context soundness
begin

lemma checked_staged_trace_fri_prequery_relation_fiber_card_bound:
  assumes finite_B: "finite B"
  shows
    "card {y. checked_staged_trace_fri_prequery_relation A B x y} \<le>
      card B * ceil_log clength"
proof -
  let ?pairs = "B \<times> {..<ceil_log clength}"
  let ?values = "(\<lambda>(bs, i). bs ! i) ` ?pairs"
  have subset:
    "{y. checked_staged_trace_fri_prequery_relation A B x y} \<subseteq>
      ?values"
    unfolding checked_staged_trace_fri_prequery_relation_def
    by force
  have finite_values: "finite ?values"
    using finite_B by simp
  have "card {y. checked_staged_trace_fri_prequery_relation A B x y} \<le>
      card ?values"
    by (rule card_mono[OF finite_values subset])
  also have "... \<le> card ?pairs"
    by (rule card_image_le) (use finite_B in simp)
  also have "... = card B * ceil_log clength"
    using finite_B by simp
  finally show ?thesis .
qed

lemma checked_staged_composition_fri_prequery_relation_fiber_card_bound:
  assumes finite_B: "\<And>dg. finite (B dg)"
  shows
    "card {y. checked_staged_composition_fri_prequery_relation A B x y}
      \<le> (\<Sum>dg \<in> (UNIV :: 'f set).
        card (B dg) * ceil_log (maxDegree + 1))"
proof -
  let ?pairs =
    "(SIGMA dg:(UNIV :: 'f set). B dg \<times> {..<ceil_log (maxDegree + 1)})"
  let ?values = "(\<lambda>(dg, bs, i). bs ! i) ` ?pairs"
  have subset:
    "{y. checked_staged_composition_fri_prequery_relation A B x y}
      \<subseteq> ?values"
    unfolding checked_staged_composition_fri_prequery_relation_def
    by force
  have finite_values: "finite ?values"
    using finite_B by simp
  have "card {y. checked_staged_composition_fri_prequery_relation A B x y}
      \<le> card ?values"
    by (rule card_mono[OF finite_values subset])
  also have "... \<le> card ?pairs"
    by (rule card_image_le) (use finite_B in simp)
  also have "... =
      (\<Sum>dg \<in> (UNIV :: 'f set).
        card (B dg \<times> {..<ceil_log (maxDegree + 1)}))"
    using finite_B by (simp add: card_SigmaI)
  also have "... =
      (\<Sum>dg \<in> (UNIV :: 'f set).
        card (B dg) * ceil_log (maxDegree + 1))"
    using finite_B by simp
  finally show ?thesis .
qed

lemma checked_staged_trace_fri_verifier_prequery_relation_fiber_card_bound:
  assumes finite_B: "finite B"
  shows
    "card {y. checked_staged_trace_fri_verifier_prequery_relation A B x y}
      \<le> card B * ceil_log clength"
proof -
  let ?pairs = "B \<times> {..<ceil_log clength}"
  let ?values = "(\<lambda>(bs, i). bs ! i) ` ?pairs"
  have subset:
    "{y. checked_staged_trace_fri_verifier_prequery_relation A B x y}
      \<subseteq> ?values"
    unfolding checked_staged_trace_fri_verifier_prequery_relation_def
    by auto
  have "card {y. checked_staged_trace_fri_verifier_prequery_relation A B x y}
      \<le> card ?values"
    by (rule card_mono[OF finite_imageI[OF finite_cartesian_product
          [OF finite_B finite_lessThan]] subset])
  also have "... \<le> card ?pairs"
    by (rule card_image_le) (use finite_B in simp)
  also have "... = card B * ceil_log clength"
    using finite_B by simp
  finally show ?thesis .
qed

lemma
  checked_staged_composition_fri_verifier_prequery_relation_fiber_card_bound:
  assumes finite_B: "\<And>dg. finite (B dg)"
  shows
    "card
      {y. checked_staged_composition_fri_verifier_prequery_relation A B x y}
      \<le> (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))"
proof -
  let ?pairs =
    "SIGMA dg:(UNIV :: 'f set). B dg \<times> {..<ceil_log (maxDegree + 1)}"
  let ?values = "(\<lambda>(dg, bs, i). bs ! i) ` ?pairs"
  have subset:
    "{y. checked_staged_composition_fri_verifier_prequery_relation A B x y}
      \<subseteq> ?values"
    unfolding checked_staged_composition_fri_verifier_prequery_relation_def
    by force
  have finite_pairs: "finite ?pairs"
    using finite_B by simp
  have "card
      {y. checked_staged_composition_fri_verifier_prequery_relation A B x y}
      \<le> card ?values"
    by (rule card_mono[OF finite_imageI[OF finite_pairs] subset])
  also have "... \<le> card ?pairs"
    by (rule card_image_le) (rule finite_pairs)
  also have "... =
      (\<Sum>dg \<in> (UNIV :: 'f set).
        card (B dg) * ceil_log (maxDegree + 1))"
    using finite_B by (simp add: card_SigmaI)
  finally show ?thesis .
qed

lemma checked_staged_transcript_trace_fri_verifier_prequery_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
  shows
    "wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event
        (checked_staged_trace_fri_verifier_prequery_relation A B)
        adversary_initial_state)
      adversary_initial_state \<le>
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have program:
    "hash_relation_program
      (checked_staged_trace_fri_verifier_prequery_relation A B)
      (card B * ceil_log clength)
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
    by (rule hash_relation_program_checked_staged_transcript_program
        [OF wf controlled])
      (rule checked_staged_trace_fri_verifier_prequery_relation_fiber_card_bound
        [OF finite_B])
  then show ?thesis
    unfolding hash_relation_program_def hash_relation_budget_def by blast
qed

lemma
  checked_staged_transcript_composition_fri_verifier_prequery_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
  shows
    "wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event
        (checked_staged_composition_fri_verifier_prequery_relation A B)
        adversary_initial_state)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have program:
    "hash_relation_program
      (checked_staged_composition_fri_verifier_prequery_relation A B)
      (\<Sum>dg \<in> (UNIV :: 'f set).
        card (B dg) * ceil_log (maxDegree + 1))
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
    by (rule hash_relation_program_checked_staged_transcript_program
        [OF wf controlled])
      (rule
        checked_staged_composition_fri_verifier_prequery_relation_fiber_card_bound
        [OF finite_B])
  then show ?thesis
    unfolding hash_relation_program_def hash_relation_budget_def by blast
qed

end

context soundness
begin

lemma checked_staged_trace_fri_verifier_prequery_hit_imp_relation_hit:
  assumes builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and hit:
      "trace_fri_challenge_list_prequery_hit
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        B (Some (result, final_state))"
  shows
    "hash_relation_hit
      (checked_staged_trace_fri_verifier_prequery_relation A B)
      adversary_initial_state attacker_state"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from hit obtain trace_bs dg comp_bs fr roots trace_final as
      composition_roots final rest where
    challenges:
      "accepted_fri_challenges ?s (Some (result, final_state))
        trace_bs dg comp_bs"
    and header:
      "verifier_header_transcript ?s fr roots trace_final as dg
        composition_roots final rest"
    and trace_bs_B: "trace_bs \<in> B"
    and prequeried:
      "trace_fri_challenge_path_prequeried ?s fr roots (length roots)"
    unfolding trace_fri_challenge_list_prequery_hit_def by blast
  from prequeried obtain i y where
    i_len: "i < length roots"
    and lookup_s:
      "fmlookup (HashMap ?s) (trace_fri_challenge_key_at ?s fr roots i) =
        Some y"
    unfolding trace_fri_challenge_path_prequeried_def
    by (auto split: option.splits)
  have lookup_info:
    "i < length trace_bs \<and> y = trace_bs ! i"
    by (rule verify_monad_trace_fri_prequery_lookup
        [OF verifier challenges header i_len])
      (use lookup_s in \<open>simp add: trace_fri_challenge_key_at_def\<close>)
  have i_round: "i < ceil_log clength"
  proof -
    have "trace_bs \<in> fri_challenge_space (ceil_log clength)"
      by (rule accepted_fri_challenges_trace_space[OF challenges])
    then have "length trace_bs = ceil_log clength"
      unfolding fri_challenge_space_def by simp
    then show ?thesis
      using lookup_info by simp
  qed
  have relation:
    "checked_staged_trace_fri_verifier_prequery_relation A B
      (trace_fri_challenge_key_at ?s fr roots i) y"
    unfolding checked_staged_trace_fri_verifier_prequery_relation_def
    apply (rule exI[where x = data])
    apply (rule exI[where x = attacker_state])
    apply (rule exI[where x = trace_bs])
    apply (rule exI[where x = fr])
    apply (rule exI[where x = roots])
    apply (rule exI[where x = i])
    using builder trace_bs_B i_round i_len lookup_info by simp
  have initial_absent:
    "fmlookup (HashMap adversary_initial_state)
      (trace_fri_challenge_key_at ?s fr roots i) = None"
    unfolding adversary_initial_state_def by simp
  have attacker_lookup:
    "fmlookup (HashMap attacker_state)
      (trace_fri_challenge_key_at ?s fr roots i) = Some y"
    using lookup_s unfolding verifier_state_from_adversary_def by simp
  show ?thesis
    unfolding hash_relation_hit_def
    using initial_absent attacker_lookup relation by blast
qed

lemma checked_staged_composition_fri_verifier_prequery_hit_imp_relation_hit:
  assumes builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and hit:
      "composition_fri_challenge_list_prequery_hit
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        B (Some (result, final_state))"
  shows
    "hash_relation_hit
      (checked_staged_composition_fri_verifier_prequery_relation A B)
      adversary_initial_state attacker_state"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from hit obtain trace_bs dg comp_bs fr trace_roots trace_final as
      composition_roots final rest where
    challenges:
      "accepted_fri_challenges ?s (Some (result, final_state))
        trace_bs dg comp_bs"
    and header:
      "verifier_header_transcript ?s fr trace_roots trace_final as dg
        composition_roots final rest"
    and comp_bs_B: "comp_bs \<in> B dg"
    and prequeried:
      "composition_fri_challenge_path_prequeried ?s fr trace_roots
        trace_final as dg composition_roots (length composition_roots)"
    unfolding composition_fri_challenge_list_prequery_hit_def by blast
  from prequeried obtain i y where
    i_len: "i < length composition_roots"
    and lookup_s:
      "fmlookup (HashMap ?s)
        (composition_fri_challenge_key_at ?s fr trace_roots trace_final as
          dg composition_roots i) =
        Some y"
    unfolding composition_fri_challenge_path_prequeried_def
    by (auto split: option.splits)
  have lookup_info:
    "i < length comp_bs \<and> y = comp_bs ! i"
    by (rule verify_monad_composition_fri_prequery_lookup
        [OF verifier challenges header i_len])
      (use lookup_s in
        \<open>simp add: composition_fri_challenge_key_at_def\<close>)
  have i_round: "i < ceil_log (maxDegree + 1)"
  proof -
    have "comp_bs \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
      by (rule accepted_fri_challenges_composition_space[OF challenges])
    then have len_comp: "length comp_bs = ceil_log (to_nat dg + 1)"
      unfolding fri_challenge_space_def by simp
    have dg_bound: "to_nat dg \<le> maxDegree"
      by (rule verify_monad_accepted_fri_challenges_degree_bound
          [OF verifier challenges])
    have "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
      by (rule ceil_log_to_nat_degree_bound[OF dg_bound])
    then show ?thesis
      using lookup_info len_comp by simp
  qed
  have relation:
    "checked_staged_composition_fri_verifier_prequery_relation A B
      (composition_fri_challenge_key_at ?s fr trace_roots trace_final as dg
        composition_roots i) y"
    unfolding checked_staged_composition_fri_verifier_prequery_relation_def
    apply (rule exI[where x = data])
    apply (rule exI[where x = attacker_state])
    apply (rule exI[where x = dg])
    apply (rule exI[where x = comp_bs])
    apply (rule exI[where x = fr])
    apply (rule exI[where x = trace_roots])
    apply (rule exI[where x = trace_final])
    apply (rule exI[where x = as])
    apply (rule exI[where x = composition_roots])
    apply (rule exI[where x = i])
    using builder comp_bs_B i_round i_len lookup_info by simp
  have initial_absent:
    "fmlookup (HashMap adversary_initial_state)
      (composition_fri_challenge_key_at ?s fr trace_roots trace_final as dg
        composition_roots i) = None"
    unfolding adversary_initial_state_def by simp
  have attacker_lookup:
    "fmlookup (HashMap attacker_state)
      (composition_fri_challenge_key_at ?s fr trace_roots trace_final as dg
        composition_roots i) = Some y"
    using lookup_s unfolding verifier_state_from_adversary_def by simp
  show ?thesis
    unfolding hash_relation_hit_def
    using initial_absent attacker_lookup relation by blast
qed

lemma checked_staged_security_trace_fri_verifier_prequery_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_prequery_hit s B))
      adversary_initial_state \<le>
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  unfolding checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_head_event)
  show "wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event
        (checked_staged_trace_fri_verifier_prequery_relation A B)
        adversary_initial_state)
      adversary_initial_state
      \<le> hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule checked_staged_transcript_trace_fri_verifier_prequery_relation_bound
        [OF wf controlled finite_B])
next
  show "staged_security_with_data_state_verifier_event
      (\<lambda>s. trace_fri_challenge_list_prequery_hit s B) None \<Longrightarrow>
    hash_relation_hit_event
      (checked_staged_trace_fri_verifier_prequery_relation A B)
      adversary_initial_state None"
    unfolding staged_security_with_data_state_verifier_event_def by simp
next
  fix data attacker_state out
  assume builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>s. put
                (verifier_state_from_adversary s
                  (staged_proof_transcript data)) \<bind>
                (\<lambda>_. verify_monad \<bind>
                  (\<lambda>result. return ((data, s), result)))))
            attacker_state)"
    and hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_prequery_hit s B) out"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from cont hit obtain result final_state where
    verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and prequery:
      "trace_fri_challenge_list_prequery_hit ?s B
        (Some (result, final_state))"
    unfolding staged_security_with_data_state_verifier_event_def
    by (auto elim!: set_dist_bindE split: option.splits prod.splits)
  have relation_hit:
    "hash_relation_hit
      (checked_staged_trace_fri_verifier_prequery_relation A B)
      adversary_initial_state attacker_state"
    by (rule checked_staged_trace_fri_verifier_prequery_hit_imp_relation_hit
        [OF builder verifier prequery])
  then show
    "hash_relation_hit_event
      (checked_staged_trace_fri_verifier_prequery_relation A B)
      adversary_initial_state (Some (data, attacker_state))"
    unfolding hash_relation_hit_event_def by simp
qed

lemma checked_staged_security_composition_fri_verifier_prequery_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_prequery_hit s B))
      adversary_initial_state \<le>
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  unfolding checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_head_event)
  show "wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event
        (checked_staged_composition_fri_verifier_prequery_relation A B)
        adversary_initial_state)
      adversary_initial_state
      \<le> hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule
        checked_staged_transcript_composition_fri_verifier_prequery_relation_bound
        [OF wf controlled finite_B])
next
  show "staged_security_with_data_state_verifier_event
      (\<lambda>s. composition_fri_challenge_list_prequery_hit s B) None \<Longrightarrow>
    hash_relation_hit_event
      (checked_staged_composition_fri_verifier_prequery_relation A B)
      adversary_initial_state None"
    unfolding staged_security_with_data_state_verifier_event_def by simp
next
  fix data attacker_state out
  assume builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>s. put
                (verifier_state_from_adversary s
                  (staged_proof_transcript data)) \<bind>
                (\<lambda>_. verify_monad \<bind>
                  (\<lambda>result. return ((data, s), result)))))
            attacker_state)"
    and hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_prequery_hit s B) out"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from cont hit obtain result final_state where
    verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and prequery:
      "composition_fri_challenge_list_prequery_hit ?s B
        (Some (result, final_state))"
    unfolding staged_security_with_data_state_verifier_event_def
    by (auto elim!: set_dist_bindE split: option.splits prod.splits)
  have relation_hit:
    "hash_relation_hit
      (checked_staged_composition_fri_verifier_prequery_relation A B)
      adversary_initial_state attacker_state"
    by (rule
        checked_staged_composition_fri_verifier_prequery_hit_imp_relation_hit
        [OF builder verifier prequery])
  then show
    "hash_relation_hit_event
      (checked_staged_composition_fri_verifier_prequery_relation A B)
      adversary_initial_state (Some (data, attacker_state))"
    unfolding hash_relation_hit_event_def by simp
qed

lemma checked_staged_trace_fri_prequery_hit_imp_fixed_relation_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and hit:
      "checked_staged_trace_fri_prequery_hit B
        (Some (data, attacker_state))"
  shows
    "hash_relation_hit
      (checked_staged_trace_fri_prequery_relation A B)
      adversary_initial_state attacker_state"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have member: "staged_trace_fri_challenges data \<in> B"
    using hit unfolding checked_staged_trace_fri_prequery_hit_def by simp
  have prequeried:
    "trace_fri_challenge_path_prequeried ?s
      (staged_trace_root data) (staged_trace_fri_roots data)
      (length (staged_trace_fri_roots data))"
    using hit unfolding checked_staged_trace_fri_prequery_hit_def by simp
  from prequeried obtain i where
    i_len: "i < length (staged_trace_fri_roots data)"
    and lookup_s:
      "fmlookup (HashMap ?s)
        (trace_fri_challenge_key_at ?s (staged_trace_root data)
          (staged_trace_fri_roots data) i) \<noteq> None"
    unfolding trace_fri_challenge_path_prequeried_def by blast
  have shape:
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     ceil_log (to_nat (staged_degree data) + 1) \<le>
       ceil_log (maxDegree + 1) \<and>
     length (staged_query_chunks data) = rounds"
    by (rule checked_staged_transcript_program_outcome_shape
        [OF wf controlled outcome])
  have unchecked_out:
    "Some (data, attacker_state) \<in>
      set_dist (execute (staged_transcript_program A)
        adversary_initial_state)"
    by (rule checked_staged_transcript_program_outcome_imp_staged_transcript_program
        [OF outcome])
  have staged_lookup:
    "fmlookup (HashMap attacker_state)
      (TraceFriChallenge i
        (foldl concat (staged_trace_fri_start_hash data)
          (take (Suc i) (staged_trace_fri_roots data)))) =
      Some (staged_trace_fri_challenges data ! i)"
    by (rule staged_transcript_program_outcome_trace_challenge_lookup
        [OF wf controlled unchecked_out])
      (use i_len shape in simp)
  have key_eq:
    "trace_fri_challenge_key_at ?s (staged_trace_root data)
      (staged_trace_fri_roots data) i =
      TraceFriChallenge i
        (foldl concat (staged_trace_fri_start_hash data)
          (take (Suc i) (staged_trace_fri_roots data)))"
    unfolding trace_fri_challenge_key_at_def staged_trace_fri_start_hash_def
    by simp
  have relation:
    "checked_staged_trace_fri_prequery_relation A B
      (trace_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) i)
      (staged_trace_fri_challenges data ! i)"
    unfolding checked_staged_trace_fri_prequery_relation_def
    by (intro exI[of _ data] exI[of _ attacker_state] exI[of _ i])
      (use outcome member i_len shape in simp_all)
  have initial_absent:
    "fmlookup (HashMap adversary_initial_state)
      (trace_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) i) = None"
    unfolding adversary_initial_state_def by simp
  have staged_lookup_key:
    "fmlookup (HashMap attacker_state)
      (trace_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) i) =
      Some (staged_trace_fri_challenges data ! i)"
    using staged_lookup key_eq by simp
  show ?thesis
    unfolding hash_relation_hit_def
    using initial_absent staged_lookup_key relation by blast
qed

lemma checked_staged_composition_fri_prequery_hit_imp_fixed_relation_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and hit:
      "checked_staged_composition_fri_prequery_hit B
        (Some (data, attacker_state))"
  shows
    "hash_relation_hit
      (checked_staged_composition_fri_prequery_relation A B)
      adversary_initial_state attacker_state"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have member:
    "staged_composition_fri_challenges data \<in> B (staged_degree data)"
    using hit unfolding checked_staged_composition_fri_prequery_hit_def
    by simp
  have prequeried:
    "composition_fri_challenge_path_prequeried ?s
      (staged_trace_root data) (staged_trace_fri_roots data)
      (staged_trace_final data) (staged_alphas data) (staged_degree data)
      (staged_composition_fri_roots data)
      (length (staged_composition_fri_roots data))"
    using hit unfolding checked_staged_composition_fri_prequery_hit_def
    by simp
  from prequeried obtain i where
    i_len: "i < length (staged_composition_fri_roots data)"
    and lookup_s:
      "fmlookup (HashMap ?s)
        (composition_fri_challenge_key_at ?s (staged_trace_root data)
          (staged_trace_fri_roots data) (staged_trace_final data)
          (staged_alphas data) (staged_degree data)
          (staged_composition_fri_roots data) i) \<noteq> None"
    unfolding composition_fri_challenge_path_prequeried_def by blast
  have shape:
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     ceil_log (to_nat (staged_degree data) + 1) \<le>
       ceil_log (maxDegree + 1) \<and>
     length (staged_query_chunks data) = rounds"
    by (rule checked_staged_transcript_program_outcome_shape
        [OF wf controlled outcome])
  have unchecked_out:
    "Some (data, attacker_state) \<in>
      set_dist (execute (staged_transcript_program A)
        adversary_initial_state)"
    by (rule checked_staged_transcript_program_outcome_imp_staged_transcript_program
        [OF outcome])
  have staged_lookup:
    "fmlookup (HashMap attacker_state)
      (CompositionFriChallenge i
        (foldl concat (staged_composition_fri_start_hash data)
          (take (Suc i) (staged_composition_fri_roots data)))) =
      Some (staged_composition_fri_challenges data ! i)"
    by (rule staged_transcript_program_outcome_composition_challenge_lookup
        [OF wf controlled unchecked_out])
      (use i_len shape in simp)
  have key_eq:
    "composition_fri_challenge_key_at ?s (staged_trace_root data)
      (staged_trace_fri_roots data) (staged_trace_final data)
      (staged_alphas data) (staged_degree data)
      (staged_composition_fri_roots data) i =
      CompositionFriChallenge i
        (foldl concat (staged_composition_fri_start_hash data)
          (take (Suc i) (staged_composition_fri_roots data)))"
    unfolding composition_fri_challenge_key_at_def
      staged_composition_fri_start_hash_def staged_trace_fri_start_hash_def
    by simp
  have relation:
    "checked_staged_composition_fri_prequery_relation A B
      (composition_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) (staged_trace_final data)
        (staged_alphas data) (staged_degree data)
        (staged_composition_fri_roots data) i)
      (staged_composition_fri_challenges data ! i)"
    unfolding checked_staged_composition_fri_prequery_relation_def
    by (intro exI[of _ data] exI[of _ attacker_state] exI[of _ i])
      (use outcome member i_len shape in simp_all)
  have initial_absent:
    "fmlookup (HashMap adversary_initial_state)
      (composition_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) (staged_trace_final data)
        (staged_alphas data) (staged_degree data)
        (staged_composition_fri_roots data) i) = None"
    unfolding adversary_initial_state_def by simp
  have staged_lookup_key:
    "fmlookup (HashMap attacker_state)
      (composition_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) (staged_trace_final data)
        (staged_alphas data) (staged_degree data)
        (staged_composition_fri_roots data) i) =
      Some (staged_composition_fri_challenges data ! i)"
    using staged_lookup key_eq by simp
  show ?thesis
    unfolding hash_relation_hit_def
    using initial_absent staged_lookup_key relation by blast
qed

lemma checked_staged_transcript_trace_fri_prequery_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
  shows
    "wp_event (checked_staged_transcript_program A)
      (checked_staged_trace_fri_prequery_hit B)
      adversary_initial_state \<le>
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have prehit_le_relation:
    "wp_event (checked_staged_transcript_program A)
      (checked_staged_trace_fri_prequery_hit B)
      adversary_initial_state \<le>
     wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event
        (checked_staged_trace_fri_prequery_relation A B)
        adversary_initial_state)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
      and hit: "checked_staged_trace_fri_prequery_hit B out"
    show
      "hash_relation_hit_event
        (checked_staged_trace_fri_prequery_relation A B)
        adversary_initial_state out"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding checked_staged_trace_fri_prequery_hit_def by simp
    next
      case (Some result)
      then obtain data attacker_state where out_eq:
        "out = Some (data, attacker_state)"
        by (cases result) simp
      have relation_hit:
        "hash_relation_hit
          (checked_staged_trace_fri_prequery_relation A B)
          adversary_initial_state attacker_state"
        by (rule checked_staged_trace_fri_prequery_hit_imp_fixed_relation_hit
            [OF wf controlled _ _])
          (use support hit out_eq in simp_all)
      then show ?thesis
        unfolding out_eq hash_relation_hit_event_def by simp
    qed
  qed
  also have "... \<le>
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  proof -
    have program:
      "hash_relation_program
        (checked_staged_trace_fri_prequery_relation A B)
        (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)
        (checked_staged_transcript_program A)"
      by (rule hash_relation_program_checked_staged_transcript_program
          [OF wf controlled])
        (rule checked_staged_trace_fri_prequery_relation_fiber_card_bound
          [OF finite_B])
    show ?thesis
      using program
      unfolding hash_relation_program_def hash_relation_budget_def by blast
  qed
  finally show ?thesis .
qed

lemma checked_staged_transcript_composition_fri_prequery_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
  shows
    "wp_event (checked_staged_transcript_program A)
      (checked_staged_composition_fri_prequery_hit B)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have prehit_le_relation:
    "wp_event (checked_staged_transcript_program A)
      (checked_staged_composition_fri_prequery_hit B)
      adversary_initial_state \<le>
     wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event
        (checked_staged_composition_fri_prequery_relation A B)
        adversary_initial_state)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in> set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
      and hit: "checked_staged_composition_fri_prequery_hit B out"
    show
      "hash_relation_hit_event
        (checked_staged_composition_fri_prequery_relation A B)
        adversary_initial_state out"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding checked_staged_composition_fri_prequery_hit_def
        by simp
    next
      case (Some result)
      then obtain data attacker_state where out_eq:
        "out = Some (data, attacker_state)"
        by (cases result) simp
      have relation_hit:
        "hash_relation_hit
          (checked_staged_composition_fri_prequery_relation A B)
          adversary_initial_state attacker_state"
        by (rule
            checked_staged_composition_fri_prequery_hit_imp_fixed_relation_hit
            [OF wf controlled _ _])
          (use support hit out_eq in simp_all)
      then show ?thesis
        unfolding out_eq hash_relation_hit_event_def by simp
    qed
  qed
  also have "... \<le>
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  proof -
    have program:
      "hash_relation_program
        (checked_staged_composition_fri_prequery_relation A B)
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)
        (checked_staged_transcript_program A)"
      by (rule hash_relation_program_checked_staged_transcript_program
          [OF wf controlled])
        (rule
          checked_staged_composition_fri_prequery_relation_fiber_card_bound
          [OF finite_B])
    show ?thesis
      using program
      unfolding hash_relation_program_def hash_relation_budget_def by blast
  qed
  finally show ?thesis .
qed

end

context soundness
begin

lemma checked_staged_trace_fri_prequery_hit_imp_relation_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and hit:
      "checked_staged_trace_fri_prequery_hit B
        (Some (data, attacker_state))"
  shows
    "hash_relation_hit
      (trace_fri_challenge_key_relation
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        B (length (staged_trace_fri_roots data)))
      adversary_initial_state attacker_state"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have member: "staged_trace_fri_challenges data \<in> B"
    using hit unfolding checked_staged_trace_fri_prequery_hit_def by simp
  have prequeried:
    "trace_fri_challenge_path_prequeried ?s
      (staged_trace_root data) (staged_trace_fri_roots data)
      (length (staged_trace_fri_roots data))"
    using hit unfolding checked_staged_trace_fri_prequery_hit_def by simp
  from prequeried obtain i where
    i_len: "i < length (staged_trace_fri_roots data)"
    and lookup_s:
      "fmlookup (HashMap ?s)
        (trace_fri_challenge_key_at ?s (staged_trace_root data)
          (staged_trace_fri_roots data) i) \<noteq> None"
    unfolding trace_fri_challenge_path_prequeried_def by blast
  have shape:
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     ceil_log (to_nat (staged_degree data) + 1) \<le>
       ceil_log (maxDegree + 1) \<and>
     length (staged_query_chunks data) = rounds"
    by (rule checked_staged_transcript_program_outcome_shape
        [OF wf controlled outcome])
  have unchecked_out:
    "Some (data, attacker_state) \<in>
      set_dist (execute (staged_transcript_program A)
        adversary_initial_state)"
    by (rule checked_staged_transcript_program_outcome_imp_staged_transcript_program
        [OF outcome])
  have staged_lookup:
    "fmlookup (HashMap attacker_state)
      (TraceFriChallenge i
        (foldl concat (staged_trace_fri_start_hash data)
          (take (Suc i) (staged_trace_fri_roots data)))) =
      Some (staged_trace_fri_challenges data ! i)"
    by (rule staged_transcript_program_outcome_trace_challenge_lookup
        [OF wf controlled unchecked_out])
      (use i_len shape in simp)
  have key_eq:
    "trace_fri_challenge_key_at ?s (staged_trace_root data)
      (staged_trace_fri_roots data) i =
      TraceFriChallenge i
        (foldl concat (staged_trace_fri_start_hash data)
          (take (Suc i) (staged_trace_fri_roots data)))"
    unfolding trace_fri_challenge_key_at_def staged_trace_fri_start_hash_def
    by simp
  have relation:
    "trace_fri_challenge_key_relation ?s B
      (length (staged_trace_fri_roots data))
      (trace_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) i)
      (staged_trace_fri_challenges data ! i)"
  proof -
    have i_challenges: "i < length (staged_trace_fri_challenges data)"
      using i_len shape by simp
    show ?thesis
      unfolding trace_fri_challenge_key_relation_def
      by (intro bexI[of _ "staged_trace_fri_challenges data"]
          exI[of _ "staged_trace_root data"]
          exI[of _ "staged_trace_fri_roots data"]
          exI[of _ i])
        (use member i_len i_challenges in simp_all)
  qed
  have initial_absent:
    "fmlookup (HashMap adversary_initial_state)
      (trace_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) i) = None"
    unfolding adversary_initial_state_def by simp
  have staged_lookup_key:
    "fmlookup (HashMap attacker_state)
      (trace_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) i) =
      Some (staged_trace_fri_challenges data ! i)"
    using staged_lookup key_eq by simp
  show ?thesis
    unfolding hash_relation_hit_def
    using initial_absent staged_lookup_key relation by blast
qed

lemma checked_staged_composition_fri_prequery_hit_imp_relation_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and hit:
      "checked_staged_composition_fri_prequery_hit B
        (Some (data, attacker_state))"
  shows
    "hash_relation_hit
      (composition_fri_challenge_key_relation
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        B (length (staged_composition_fri_roots data)))
      adversary_initial_state attacker_state"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have member:
    "staged_composition_fri_challenges data \<in> B (staged_degree data)"
    using hit unfolding checked_staged_composition_fri_prequery_hit_def
    by simp
  have prequeried:
    "composition_fri_challenge_path_prequeried ?s
      (staged_trace_root data) (staged_trace_fri_roots data)
      (staged_trace_final data) (staged_alphas data) (staged_degree data)
      (staged_composition_fri_roots data)
      (length (staged_composition_fri_roots data))"
    using hit unfolding checked_staged_composition_fri_prequery_hit_def
    by simp
  from prequeried obtain i where
    i_len: "i < length (staged_composition_fri_roots data)"
    and lookup_s:
      "fmlookup (HashMap ?s)
        (composition_fri_challenge_key_at ?s (staged_trace_root data)
          (staged_trace_fri_roots data) (staged_trace_final data)
          (staged_alphas data) (staged_degree data)
          (staged_composition_fri_roots data) i) \<noteq> None"
    unfolding composition_fri_challenge_path_prequeried_def by blast
  have shape:
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     length (staged_composition_fri_challenges data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     ceil_log (to_nat (staged_degree data) + 1) \<le>
       ceil_log (maxDegree + 1) \<and>
     length (staged_query_chunks data) = rounds"
    by (rule checked_staged_transcript_program_outcome_shape
        [OF wf controlled outcome])
  have unchecked_out:
    "Some (data, attacker_state) \<in>
      set_dist (execute (staged_transcript_program A)
        adversary_initial_state)"
    by (rule checked_staged_transcript_program_outcome_imp_staged_transcript_program
        [OF outcome])
  have staged_lookup:
    "fmlookup (HashMap attacker_state)
      (CompositionFriChallenge i
        (foldl concat (staged_composition_fri_start_hash data)
          (take (Suc i) (staged_composition_fri_roots data)))) =
      Some (staged_composition_fri_challenges data ! i)"
    by (rule staged_transcript_program_outcome_composition_challenge_lookup
        [OF wf controlled unchecked_out])
      (use i_len shape in simp)
  have key_eq:
    "composition_fri_challenge_key_at ?s (staged_trace_root data)
      (staged_trace_fri_roots data) (staged_trace_final data)
      (staged_alphas data) (staged_degree data)
      (staged_composition_fri_roots data) i =
      CompositionFriChallenge i
        (foldl concat (staged_composition_fri_start_hash data)
          (take (Suc i) (staged_composition_fri_roots data)))"
    unfolding composition_fri_challenge_key_at_def
      staged_composition_fri_start_hash_def staged_trace_fri_start_hash_def
    by simp
  have relation:
    "composition_fri_challenge_key_relation ?s B
      (length (staged_composition_fri_roots data))
      (composition_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) (staged_trace_final data)
        (staged_alphas data) (staged_degree data)
        (staged_composition_fri_roots data) i)
      (staged_composition_fri_challenges data ! i)"
  proof -
    have i_challenges: "i < length (staged_composition_fri_challenges data)"
      using i_len shape by simp
    show ?thesis
      unfolding composition_fri_challenge_key_relation_def
      by (intro exI[of _ "staged_degree data"]
          bexI[of _ "staged_composition_fri_challenges data"]
          exI[of _ "staged_trace_root data"]
          exI[of _ "staged_trace_fri_roots data"]
          exI[of _ "staged_trace_final data"]
          exI[of _ "staged_alphas data"]
          exI[of _ "staged_composition_fri_roots data"]
          exI[of _ i])
        (use member i_len i_challenges in simp_all)
  qed
  have initial_absent:
    "fmlookup (HashMap adversary_initial_state)
      (composition_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) (staged_trace_final data)
        (staged_alphas data) (staged_degree data)
        (staged_composition_fri_roots data) i) = None"
    unfolding adversary_initial_state_def by simp
  have staged_lookup_key:
    "fmlookup (HashMap attacker_state)
      (composition_fri_challenge_key_at ?s (staged_trace_root data)
        (staged_trace_fri_roots data) (staged_trace_final data)
        (staged_alphas data) (staged_degree data)
        (staged_composition_fri_roots data) i) =
      Some (staged_composition_fri_challenges data ! i)"
    using staged_lookup key_eq by simp
  show ?thesis
    unfolding hash_relation_hit_def
    using initial_absent staged_lookup_key relation by blast
qed

end

end
