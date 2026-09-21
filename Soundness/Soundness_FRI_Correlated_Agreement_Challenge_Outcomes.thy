theory Soundness_FRI_Correlated_Agreement_Challenge_Outcomes
  imports
    Soundness_FRI_Correlated_Agreement_Challenge_Fibers
    Soundness_FRI_Conditioned_Challenge_Outcome_Bridge
begin

section \<open>Actual builder outcomes activate the auxiliary relations\<close>
text \<open>
  The existing all-round checked transcript experiment supplies the absorption
  prefixes and challenge lookups. No new execution, freshness, authentication,
  or initial-distance premise is hidden in these outcome bridges.
\<close>

context soundness
begin

lemma checked_builder_trace_mca_online_bad_imp_conditioned_relation_active:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision t"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values t"
    and hit:
      "\<exists>j < length (staged_trace_fri_roots data).
        staged_trace_fri_challenges data ! j \<in>
          fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j t
            (staged_trace_fri_roots data ! j)"
  shows
    "\<exists>x y.
      hash_state_relation_active
        (mca_conditioned_trace_fri_bad_challenge_relation)
        (HashMap t) x y"
proof -
  from hit obtain j where
    j_bound: "j < length (staged_trace_fri_roots data)"
    and bad:
      "staged_trace_fri_challenges data ! j \<in>
        fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j t
          (staged_trace_fri_roots data ! j)"
    by blast
  have prefixes:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength \<and>
       (\<forall>j < length (staged_trace_fri_roots data). \<exists>final.
         ro_absorb_lookup_chain t (PState adversary_initial_state)
           (staged_trace_root data #
             take (Suc j) (staged_trace_fri_roots data)) final \<and>
         fmlookup (HashMap t) (TraceFriChallenge j final) =
           Some (staged_trace_fri_challenges data ! j))"
    using ro_checked_staged_transcript_program_conditioned_challenge_prefixes[
      OF wf controlled outcome]
    by blast
  from prefixes j_bound obtain final where
    chain:
      "ro_absorb_lookup_chain t (PState adversary_initial_state)
        (staged_trace_root data #
          take (Suc j) (staged_trace_fri_roots data)) final"
    and lookup:
      "fmlookup (HashMap t) (TraceFriChallenge j final) =
        Some (staged_trace_fri_challenges data ! j)"
    by blast
  have final_map:
      "HashMap (channel_for_hash_map (HashMap t)) = HashMap t"
    unfolding channel_for_hash_map_def adversary_initial_state_def by simp
  have chain_map:
      "ro_absorb_lookup_chain (channel_for_hash_map (HashMap t))
        (PState adversary_initial_state)
        (staged_trace_root data #
          take (Suc j) (staged_trace_fri_roots data)) final"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule chain)
  have clean_map:
      "\<not> hash_map_output_collision (channel_for_hash_map (HashMap t))"
    using clean final_map unfolding hash_map_output_collision_def by simp
  have no_initial_map:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (HashMap t))"
    using no_initial final_map unfolding hash_map_output_values_def by simp
  have tables:
      "conceptual_table (channel_for_hash_map (HashMap t)) =
        conceptual_table t"
    by (rule ext)+
      (rule conceptual_table_cong_hash_map[OF final_map])
  have family_eq:
      "fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j
          (channel_for_hash_map (HashMap t))
          (staged_trace_fri_roots data ! j) =
        fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j t
          (staged_trace_fri_roots data ! j)"
    unfolding fri_mca_online_bad_challenges_def tables by simp
  have bad_map:
      "staged_trace_fri_challenges data ! j \<in>
        fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j
          (channel_for_hash_map (HashMap t))
          (staged_trace_fri_roots data ! j)"
    using bad family_eq by simp
  have rel:
      "mca_conditioned_trace_fri_bad_challenge_relation
        (HashMap t)
        (TraceFriChallenge j final)
        (staged_trace_fri_challenges data ! j)"
    unfolding mca_conditioned_trace_fri_bad_challenge_relation_def Let_def
    apply (intro conjI)
     apply (rule clean_map)
     apply (rule no_initial_map)
    apply (rule exI[where x="staged_trace_root data"])
    apply (rule exI[where x="staged_trace_fri_roots data"])
    apply (rule exI[where x=final])
    apply (rule exI[where x=j])
    using prefixes j_bound chain_map bad_map
    by simp
  have active:
      "hash_state_relation_active
        (mca_conditioned_trace_fri_bad_challenge_relation)
        (HashMap t)
        (TraceFriChallenge j final)
        (staged_trace_fri_challenges data ! j)"
    unfolding hash_state_relation_active_def using lookup rel by blast
  show ?thesis
    using active by blast
qed



lemma checked_builder_composition_mca_online_bad_imp_conditioned_relation_active:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision t"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values t"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and hit:
      "\<exists>j < length (staged_composition_fri_roots data).
        staged_composition_fri_challenges data ! j \<in>
          fri_mca_online_bad_challenges (to_nat (staged_degree data)) (fri_mca_quarter_radii j) j t
            (staged_composition_fri_roots data ! j)"
  shows
    "\<exists>x y.
      hash_state_relation_active
        (mca_conditioned_composition_fri_bad_challenge_relation)
        (HashMap t) x y"
proof -
  from hit obtain j where
    j_bound: "j < length (staged_composition_fri_roots data)"
    and bad:
      "staged_composition_fri_challenges data ! j \<in>
        fri_mca_online_bad_challenges (to_nat (staged_degree data)) (fri_mca_quarter_radii j) j t
          (staged_composition_fri_roots data ! j)"
    by blast
  have prefixes:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_alphas data) = length spec \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (Suc (to_nat (staged_degree data))) \<and>
       (\<forall>j < length (staged_composition_fri_roots data). \<exists>final.
         ro_absorb_lookup_chain t (PState adversary_initial_state)
           (composition_fri_challenge_prefix_messages
             (staged_trace_root data)
             (staged_trace_fri_roots data)
             (staged_trace_final data)
             (staged_alphas data)
             (staged_degree data)
             (staged_composition_fri_roots data) j) final \<and>
         fmlookup (HashMap t) (CompositionFriChallenge j final) =
           Some (staged_composition_fri_challenges data ! j))"
    using ro_checked_staged_transcript_program_conditioned_challenge_prefixes[
      OF wf controlled outcome]
    by blast
  from prefixes j_bound obtain final where
    chain:
      "ro_absorb_lookup_chain t (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data) j) final"
    and lookup:
      "fmlookup (HashMap t) (CompositionFriChallenge j final) =
        Some (staged_composition_fri_challenges data ! j)"
    by blast
  have final_map:
      "HashMap (channel_for_hash_map (HashMap t)) = HashMap t"
    unfolding channel_for_hash_map_def adversary_initial_state_def by simp
  have chain_map:
      "ro_absorb_lookup_chain (channel_for_hash_map (HashMap t))
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data) j) final"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule chain)
  have clean_map:
      "\<not> hash_map_output_collision (channel_for_hash_map (HashMap t))"
    using clean final_map unfolding hash_map_output_collision_def by simp
  have no_initial_map:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (HashMap t))"
    using no_initial final_map unfolding hash_map_output_values_def by simp
  have tables:
      "conceptual_table (channel_for_hash_map (HashMap t)) =
        conceptual_table t"
    by (rule ext)+
      (rule conceptual_table_cong_hash_map[OF final_map])
  have family_eq:
      "fri_mca_online_bad_challenges (to_nat (staged_degree data)) (fri_mca_quarter_radii j) j
          (channel_for_hash_map (HashMap t))
          (staged_composition_fri_roots data ! j) =
        fri_mca_online_bad_challenges (to_nat (staged_degree data)) (fri_mca_quarter_radii j) j t
          (staged_composition_fri_roots data ! j)"
    unfolding fri_mca_online_bad_challenges_def tables by simp
  have bad_map:
      "staged_composition_fri_challenges data ! j \<in>
        fri_mca_online_bad_challenges (to_nat (staged_degree data)) (fri_mca_quarter_radii j) j
          (channel_for_hash_map (HashMap t))
          (staged_composition_fri_roots data ! j)"
    using bad family_eq by simp
  have rel:
      "mca_conditioned_composition_fri_bad_challenge_relation
        (HashMap t)
        (CompositionFriChallenge j final)
        (staged_composition_fri_challenges data ! j)"
    unfolding
      mca_conditioned_composition_fri_bad_challenge_relation_def Let_def
    apply (intro conjI)
     apply (rule clean_map)
     apply (rule no_initial_map)
    apply (rule exI[where x="staged_trace_root data"])
    apply (rule exI[where x="staged_trace_fri_roots data"])
    apply (rule exI[where x="staged_trace_final data"])
    apply (rule exI[where x="staged_alphas data"])
    apply (rule exI[where x="staged_degree data"])
    apply (rule exI[where x="staged_composition_fri_roots data"])
    apply (rule exI[where x=final])
    apply (rule exI[where x=j])
    using prefixes degree_bound j_bound chain_map bad_map
    by simp
  have active:
      "hash_state_relation_active
        (mca_conditioned_composition_fri_bad_challenge_relation)
        (HashMap t)
        (CompositionFriChallenge j final)
        (staged_composition_fri_challenges data ! j)"
    unfolding hash_state_relation_active_def using lookup rel by blast
  show ?thesis
    using active by blast
qed



lemma checked_builder_trace_mca_online_bad_imp_bounded_relation_transition:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values attacker_state"
    and hit:
      "\<exists>j < length (staged_trace_fri_roots data).
        staged_trace_fri_challenges data ! j \<in>
          fri_mca_online_bad_challenges (clength - 1) (fri_mca_quarter_radii j) j
            attacker_state (staged_trace_fri_roots data ! j)"
  shows
    "hash_state_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (mca_conditioned_trace_fri_bad_challenge_relation))
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have active:
      "\<exists>x y.
        hash_state_relation_active
          (mca_conditioned_trace_fri_bad_challenge_relation)
          (HashMap attacker_state) x y"
    by (rule
      checked_builder_trace_mca_online_bad_imp_conditioned_relation_active[
        OF wf controlled original_out clean no_initial hit])
  have domain:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds[
        OF wf controlled outcome clean])
  show ?thesis
    by (rule conditioned_relation_active_imp_bounded_initial_transition[
      OF active domain])
qed

lemma checked_builder_composition_mca_online_bad_imp_bounded_relation_transition:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values attacker_state"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and hit:
      "\<exists>j < length (staged_composition_fri_roots data).
        staged_composition_fri_challenges data ! j \<in>
          fri_mca_online_bad_challenges (to_nat (staged_degree data)) (fri_mca_quarter_radii j) j
            attacker_state
            (staged_composition_fri_roots data ! j)"
  shows
    "hash_state_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (mca_conditioned_composition_fri_bad_challenge_relation))
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have active:
      "\<exists>x y.
        hash_state_relation_active
          (mca_conditioned_composition_fri_bad_challenge_relation)
          (HashMap attacker_state) x y"
    by (rule
      checked_builder_composition_mca_online_bad_imp_conditioned_relation_active[
        OF wf controlled original_out clean no_initial degree_bound hit])
  have domain:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound_all_rounds[
        OF wf controlled outcome clean])
  show ?thesis
    by (rule conditioned_relation_active_imp_bounded_initial_transition[
      OF active domain])
qed

end
end
