theory Soundness_FRI_Correlated_Agreement_Adaptive_Charging
  imports
    Soundness_FRI_Correlated_Agreement_Challenge_Outcomes
    Soundness_FRI_First_Root_RO_Adaptive_Query_Budget
begin

section \<open>Auxiliary adaptive-oracle charges for correlated agreement\<close>
text \<open>
  The full existing staged transcript query budget covers direct and drift
  activation, including opening-stage queries. The final events are joint
  clean-and-bad events, not probabilities conditional on cleanliness.
  Composition retains the exact decoded-degree guard. No public acceptance bound
  or concrete security profile is changed.
\<close>

context soundness
begin

lemma mca_conditioned_trace_fri_bounded_transition_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and trace_rate: "4*fri_padded_degree_bound (clength - 1) \<le> clength*scale"
  shows
    "card {y.
      hash_state_relation_transition
        (conditioned_fri_relation_bounded L
          (mca_conditioned_trace_fri_bad_challenge_relation))
        M (fmupd x y M)}
      \<le> fri_mca_direct_cap +
        (7 * L + 2)"
proof (rule conditioned_fri_bounded_transition_fiber_card_bound[
    OF fresh])
  assume "card (fmdom' M) \<le> L"
  show
    "card {y.
      hash_state_relation_direct_activation
        (mca_conditioned_trace_fri_bad_challenge_relation) M x y}
      \<le> fri_mca_direct_cap"
    by (rule
      mca_conditioned_trace_fri_bad_challenge_relation_direct_fiber_card_bound[
        OF eval_power trace_rounds_fit trace_rate])
next
  assume domain: "card (fmdom' M) \<le> L"
  have
    "card {y.
      hash_state_relation_drift_activation
        (mca_conditioned_trace_fri_bad_challenge_relation) M x y}
      \<le> 7 * card (fmdom' M) + 2"
    by (rule
      mca_conditioned_trace_fri_bad_challenge_relation_drift_fiber_card_bound[
        OF fresh])
  also have "... \<le> 7 * L + 2"
    by (rule add_le_mono[OF mult_left_mono[OF domain] order_refl], simp)
  finally show
    "card {y.
      hash_state_relation_drift_activation
        (mca_conditioned_trace_fri_bad_challenge_relation) M x y}
      \<le> 7 * L + 2"
    .
qed


lemma
  wp_ro_checked_staged_transcript_with_query_witnesses_mca_conditioned_trace_fri_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and trace_rate: "4*fri_padded_degree_bound (clength - 1) \<le> clength*scale"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded q
          (mca_conditioned_trace_fri_bad_challenge_relation))
        (HashMap adversary_initial_state))
      adversary_initial_state
      \<le> nnreal
          (q *
            (fri_mca_direct_cap +
              (7 * q + 2))) /
        nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B =
    "fri_mca_direct_cap +
      (7 * ?Q + 2)"
  have steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition
            (conditioned_fri_relation_bounded ?Q
              (mca_conditioned_trace_fri_bad_challenge_relation))
            M (fmupd x y M)}
          \<le> ?B"
    by (rule
      mca_conditioned_trace_fri_bounded_transition_fiber_card_bound[
        OF _ eval_power trace_rounds_fit trace_rate])
  have bound:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (conditioned_fri_relation_bounded ?Q
            (mca_conditioned_trace_fri_bad_challenge_relation))
          (HashMap adversary_initial_state))
        adversary_initial_state
        \<le> nnreal (?Q * ?B) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound_all_rounds[
        OF wf controlled steps])
  show ?thesis
    using bound unfolding q_def by simp
qed



lemma mca_conditioned_composition_fri_bounded_transition_fiber_card_bound:
  assumes fresh: "fmlookup M x = None"
    and eval_power: "clength * scale = 2 ^ N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and composition_rate: "4*fri_padded_degree_bound maxDegree \<le> clength*scale"
  shows
    "card {y.
      hash_state_relation_transition
        (conditioned_fri_relation_bounded L
          (mca_conditioned_composition_fri_bad_challenge_relation))
        M (fmupd x y M)}
      \<le> fri_mca_direct_cap +
        (7 * L + 2)"
proof (rule conditioned_fri_bounded_transition_fiber_card_bound[
    OF fresh])
  assume "card (fmdom' M) \<le> L"
  show
    "card {y.
      hash_state_relation_direct_activation
        (mca_conditioned_composition_fri_bad_challenge_relation)
        M x y}
      \<le> fri_mca_direct_cap"
    by (rule
      mca_conditioned_composition_fri_bad_challenge_relation_direct_fiber_card_bound[
        OF eval_power composition_rounds_fit composition_rate])
next
  assume domain: "card (fmdom' M) \<le> L"
  have
    "card {y.
      hash_state_relation_drift_activation
        (mca_conditioned_composition_fri_bad_challenge_relation) M x y}
      \<le> 7 * card (fmdom' M) + 2"
    by (rule
      mca_conditioned_composition_fri_bad_challenge_relation_drift_fiber_card_bound[
        OF fresh])
  also have "... \<le> 7 * L + 2"
    by (rule add_le_mono[OF mult_left_mono[OF domain] order_refl], simp)
  finally show
    "card {y.
      hash_state_relation_drift_activation
        (mca_conditioned_composition_fri_bad_challenge_relation) M x y}
      \<le> 7 * L + 2"
    .
qed


lemma
  wp_ro_checked_staged_transcript_with_query_witnesses_mca_conditioned_composition_fri_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and composition_rate: "4*fri_padded_degree_bound maxDegree \<le> clength*scale"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (hash_state_relation_transition_event
        (conditioned_fri_relation_bounded q
          (mca_conditioned_composition_fri_bad_challenge_relation))
        (HashMap adversary_initial_state))
      adversary_initial_state
      \<le> nnreal
          (q *
            (fri_mca_direct_cap +
              (7 * q + 2))) /
        nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B =
    "fri_mca_direct_cap +
      (7 * ?Q + 2)"
  have steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition
            (conditioned_fri_relation_bounded ?Q
              (mca_conditioned_composition_fri_bad_challenge_relation))
            M (fmupd x y M)}
          \<le> ?B"
    by (rule
      mca_conditioned_composition_fri_bounded_transition_fiber_card_bound[
        OF _ eval_power composition_rounds_fit composition_rate])
  have bound:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (conditioned_fri_relation_bounded ?Q
            (mca_conditioned_composition_fri_bad_challenge_relation))
          (HashMap adversary_initial_state))
        adversary_initial_state
        \<le> nnreal (?Q * ?B) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound_all_rounds[
        OF wf controlled steps])
  show ?thesis
    using bound unfolding q_def by simp
qed

definition fri_mca_trace_builder_bad ::
  "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> bool"
where "fri_mca_trace_builder_bad data state \<longleftrightarrow>
  \<not> hash_map_output_collision state \<and>
  PState adversary_initial_state \<notin> hash_map_output_values state \<and>
  fri_mca_chain_bad_event (clength - 1) fri_mca_quarter_radii
    (staged_trace_fri_roots data) (staged_trace_fri_challenges data) state"

definition fri_mca_composition_builder_bad ::
  "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> bool"
where "fri_mca_composition_builder_bad data state \<longleftrightarrow>
  \<not> hash_map_output_collision state \<and>
  PState adversary_initial_state \<notin> hash_map_output_values state \<and>
  to_nat (staged_degree data) \<le> maxDegree \<and>
  fri_mca_chain_bad_event (to_nat (staged_degree data)) fri_mca_quarter_radii
    (staged_composition_fri_roots data) (staged_composition_fri_challenges data) state"

lemma wp_ro_checked_staged_transcript_trace_mca_bad:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and ep: "clength * scale = 2 ^ N"
    and fit: "Suc (ceil_log clength) \<le> N"
    and rate: "4 * fri_padded_degree_bound (clength - 1) \<le> clength * scale"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows "wp_event
    (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
    (\<lambda>out. case out of None \<Rightarrow> False
      | Some ((prefix_with_state, data, query_start, raws, query_states), state) \<Rightarrow>
        fri_mca_trace_builder_bad data state)
    adversary_initial_state \<le>
      nnreal (q * (fri_mca_direct_cap + (7*q+2))) / nnreal size"
proof -
  let ?m = "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?R = "conditioned_fri_relation_bounded q
    mca_conditioned_trace_fri_bad_challenge_relation"
  let ?E = "\<lambda>out. case out of None \<Rightarrow> False
    | Some ((prefix_with_state, data, query_start, raws, query_states), state) \<Rightarrow>
      fri_mca_trace_builder_bad data state"
  have mono: "wp_event ?m ?E adversary_initial_state \<le>
    wp_event ?m (hash_state_relation_transition_event ?R
      (HashMap adversary_initial_state)) adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?m adversary_initial_state)"
      and event: "?E out"
    obtain prefix prefix_state data query_start raws query_states state where
      out: "out = Some (((prefix, prefix_state), data, query_start, raws, query_states), state)"
      and bad: "fri_mca_trace_builder_bad data state"
      using event by (cases out) auto
    have hit: "\<exists>j < length (staged_trace_fri_roots data).
      staged_trace_fri_challenges data ! j \<in>
        fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j
          state (staged_trace_fri_roots data ! j)"
      using bad unfolding fri_mca_trace_builder_bad_def fri_mca_chain_bad_event_def by auto
    have "hash_state_relation_transition ?R (HashMap adversary_initial_state) (HashMap state)"
      unfolding q_def
      by (rule checked_builder_trace_mca_online_bad_imp_bounded_relation_transition[
        OF wf controlled support[unfolded out] _ _ hit])
        (use bad in \<open>auto simp: fri_mca_trace_builder_bad_def\<close>)
    then show "hash_state_relation_transition_event ?R (HashMap adversary_initial_state) out"
      unfolding out hash_state_relation_transition_event_def by simp
  qed
  also have "wp_event ?m (hash_state_relation_transition_event ?R
      (HashMap adversary_initial_state)) adversary_initial_state \<le>
    nnreal (q * (fri_mca_direct_cap + (7*q+2))) / nnreal size"
    unfolding q_def by (rule
      wp_ro_checked_staged_transcript_with_query_witnesses_mca_conditioned_trace_fri_relation[
        OF wf controlled ep fit rate])
  finally show ?thesis .
qed

lemma wp_ro_checked_staged_transcript_composition_mca_bad:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and ep: "clength * scale = 2 ^ N"
    and fit: "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and rate: "4 * fri_padded_degree_bound maxDegree \<le> clength * scale"
  defines "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows "wp_event
    (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
    (\<lambda>out. case out of None \<Rightarrow> False
      | Some ((prefix_with_state, data, query_start, raws, query_states), state) \<Rightarrow>
        fri_mca_composition_builder_bad data state)
    adversary_initial_state \<le>
      nnreal (q * (fri_mca_direct_cap + (7*q+2))) / nnreal size"
proof -
  let ?m = "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?R = "conditioned_fri_relation_bounded q
    mca_conditioned_composition_fri_bad_challenge_relation"
  let ?E = "\<lambda>out. case out of None \<Rightarrow> False
    | Some ((prefix_with_state, data, query_start, raws, query_states), state) \<Rightarrow>
      fri_mca_composition_builder_bad data state"
  have mono: "wp_event ?m ?E adversary_initial_state \<le>
    wp_event ?m (hash_state_relation_transition_event ?R
      (HashMap adversary_initial_state)) adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?m adversary_initial_state)"
      and event: "?E out"
    obtain prefix prefix_state data query_start raws query_states state where
      out: "out = Some (((prefix, prefix_state), data, query_start, raws, query_states), state)"
      and bad: "fri_mca_composition_builder_bad data state"
      using event by (cases out) auto
    have hit: "\<exists>j < length (staged_composition_fri_roots data).
      staged_composition_fri_challenges data ! j \<in>
        fri_mca_online_bad_challenges (to_nat (staged_degree data)) (fri_mca_quarter_radii j) j
          state (staged_composition_fri_roots data ! j)"
      using bad unfolding fri_mca_composition_builder_bad_def fri_mca_chain_bad_event_def by auto
    have "hash_state_relation_transition ?R (HashMap adversary_initial_state) (HashMap state)"
      unfolding q_def
      by (rule checked_builder_composition_mca_online_bad_imp_bounded_relation_transition[
        OF wf controlled support[unfolded out] _ _ _ hit])
        (use bad in \<open>auto simp: fri_mca_composition_builder_bad_def\<close>)
    then show "hash_state_relation_transition_event ?R (HashMap adversary_initial_state) out"
      unfolding out hash_state_relation_transition_event_def by simp
  qed
  also have "wp_event ?m (hash_state_relation_transition_event ?R
      (HashMap adversary_initial_state)) adversary_initial_state \<le>
    nnreal (q * (fri_mca_direct_cap + (7*q+2))) / nnreal size"
    unfolding q_def by (rule
      wp_ro_checked_staged_transcript_with_query_witnesses_mca_conditioned_composition_fri_relation[
        OF wf controlled ep fit rate])
  finally show ?thesis .
qed

lemma fri_mca_scale64_direct_cap:
  assumes ep: "clength*scale = 2^16"
  shows "fri_mca_direct_cap = 16384"
  unfolding fri_mca_direct_cap_def fri_mca_quarter_radii_def
    fri_canonical_domain_at_length ep by simp

end
end
