(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Canonical.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Canonical
  imports Staged_Security_Experiment_Composition_Query_Classification
begin

text \<open>
  Canonical-index projections for the header-authenticated composition query
  bridge.  These lemmas do not bound the broad existential event by themselves;
  they expose the canonical query-index cover that a later Merkle/candidate
  binding argument has to control.

  In particular, the projection from the actual-alpha-prefix event to a
  query-prefix hit is support-level evidence.  It is not by itself a probability
  reduction to the separately sampled query-prefix program: the authenticated
  opening witness is still selected existentially from verifier-reachable
  evidence.  A sound probability bound needs either a cover fixed before the
  query challenge is sampled, or a Merkle/collision/partial-opening side event
  accounting for failure to select such a witness.
\<close>

context soundness
begin

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_canonical_query_indexE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
  obtains i trace_openings composition_openings query_prefix query_prefix_state
      raw raw_state where
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    "i < rounds"
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((query_prefix, query_prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "index (to_nat raw) \<in>
      query_header_supported_partial_opening_canonical_query_indices
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_query_prefixE
      [OF hit])
  fix i trace_openings composition_openings query_prefix query_prefix_state
      raw raw_state
  assume witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
    and i_bound: "i < rounds"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((query_prefix, query_prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i)
        (Some (((query_prefix, query_prefix_state), raw), raw_state))"
  have header_hit:
    "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i
      (Some (((((query_prefix, query_prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    by (rule
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hitI_from_dynamic_hit
        [OF witness target_hit])
  have canonical:
    "index (to_nat raw) \<in>
      query_header_supported_partial_opening_canonical_query_indices
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    by (rule
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_canonical_query_indexD
        [OF i_bound header_hit])
  show ?thesis
    by (rule that[OF witness i_bound builder prefix_receive canonical])
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_coverE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    and cover:
      "query_header_supported_partial_opening_canonical_query_indices
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data) \<subseteq> B"
  obtains i query_prefix query_prefix_state raw raw_state where
    "i < rounds"
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    "Some (((query_prefix, query_prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "checked_staged_query_prefix_dynamic_index_hit
      (\<lambda>_ _. B)
      (Some (((query_prefix, query_prefix_state), raw), raw_state))"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix_canonical_query_indexE
      [OF hit])
  fix i trace_openings composition_openings query_prefix query_prefix_state raw
      raw_state
  assume i_bound: "i < rounds"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix_receive:
      "Some (((query_prefix, query_prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and canonical:
      "index (to_nat raw) \<in>
        query_header_supported_partial_opening_canonical_query_indices
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
  have hit_B:
    "checked_staged_query_prefix_dynamic_index_hit
      (\<lambda>_ _. B)
      (Some (((query_prefix, query_prefix_state), raw), raw_state))"
    using canonical cover
    unfolding checked_staged_query_prefix_dynamic_index_hit_def
    by auto
  show ?thesis
    by (rule that[OF i_bound builder prefix_receive hit_B])
qed

lemma checked_staged_query_prefix_constant_index_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit (\<lambda>_ _. B))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit (\<lambda>_ _. B))
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit (\<lambda>_ _. B))
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    show
      "(\<lambda>_ _. B) prefix prefix_state \<subseteq> query_sample_space \<and>
       nnreal
         (query_raw_preimage_card_envelope
           (card ((\<lambda>_ _. B) prefix prefix_state))) /
        nnreal size \<le> query_error_bound"
      using subset frac by simp
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit (\<lambda>_ _. B))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
  proof (rule
      checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
    show "HashMap adversary_initial_state = fmempty"
      by (simp add: adversary_initial_state_def)
    show "hash_relation_program
        (checked_staged_query_prefix_dynamic_index_prehit_relation A i
          adversary_initial_state (\<lambda>_ _. B))
        size (staged_query_search_queries budgets i + 1)
        (checked_staged_query_prefix_receive_with_state A i)"
      by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
          [OF wf controlled])
        (use i_bound in simp_all,
          rule checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
  qed
  show ?thesis
    by (rule order_trans[OF hit_bound])
      (intro add_mono prehit_bound order_refl)
qed

lemma checked_staged_security_with_query_prefix_constant_index_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
        (\<lambda>_ _. B))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
  by (rule checked_staged_security_with_query_prefix_dynamic_index_hit_bound,
      rule checked_staged_query_prefix_constant_index_hit_bound_from_budgets
        [OF wf controlled i_bound subset frac])

end

end
