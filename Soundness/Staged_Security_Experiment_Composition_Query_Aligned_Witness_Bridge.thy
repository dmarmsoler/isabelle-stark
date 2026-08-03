(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Aligned_Witness_Bridge.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Aligned_Witness_Bridge
  imports
    Staged_Security_Experiment_Composition_Query_Current_Alignment
    Staged_Security_Experiment_Composition_Query_Single_Round_Witness_Bridge
begin

text \<open>
  Same-run bridge from actual-alpha support to the fixed query-prefix
  candidate-pair witness-gap event.

  This layer avoids the broad diagnostic event: the sampled query index, prefix
  state, verifier output, and witness side facts all live on the same
  query-prefix data-state output.
\<close>

context soundness
begin

lemma checked_staged_security_with_query_prefix_data_state_accepted_shape_query_index:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and shape:
      "accepted_transcript_shape
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) as query_idxs"
  shows "index (to_nat raw) = query_idxs ! i"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_imp_data_state_support
        [OF i_bound support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain verifier where verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled data_support shape]
  obtain raw_idxs where len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup_final:
      "\<forall>j<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data) (staged_query_chunks data) j)) =
        Some (raw_idxs ! j)"
    by blast
  from support obtain t where prefix_receive:
      "Some (((prefix, prefix_state), raw), t) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and t_eq: "t = raw_state"
    and cont:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive_with_verifier A i
              ((prefix, prefix_state), raw))
            raw_state)"
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have data_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive A i
            ((prefix, prefix_state), raw))
          raw_state)"
    by (rule checked_staged_after_query_prefix_receive_with_verifier_outcome(1)
        [OF cont])
  have prefix_support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
    by (rule checked_staged_query_prefix_receive_with_state_prefix_support)
      (use prefix_receive t_eq in simp)
  have recv:
    "Some (raw, raw_state) \<in>
      set_dist (execute receive_query_index_challenge prefix_state)"
    by (rule checked_staged_query_prefix_receive_with_state_receive_support)
      (use prefix_receive t_eq in simp)
  from checked_staged_query_prefix_with_state_alignment
      [OF wf controlled i_bound prefix_support]
  have prefix_counter: "PQueryCounter prefix_state = i"
    and prefix_state_hash:
      "PState prefix_state =
        state_after_query_chunks
          (staged_query_prefix_start_hash prefix)
          (sqp_query_chunks prefix) i"
    and prefix_len: "length (sqp_query_chunks prefix) = i"
    by blast+
  from data_out obtain chunk chunk_state record_state suffix_chunks where
    chunk_out:
      "Some (chunk, chunk_state) \<in>
        set_dist (execute (query_opening_stage A i raw) raw_state)"
    and record_out:
      "Some ((), record_state) \<in>
        set_dist (execute (record_staged_messages chunk) chunk_state)"
    and suffix_out:
      "Some (suffix_chunks, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A
              (sqp_trace_fri_roots prefix)
              (sqp_composition_fri_roots prefix)
              (Suc i) (rounds - Suc i))
            record_state)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = sqp_trace_root prefix,
         staged_trace_fri_roots = sqp_trace_fri_roots prefix,
         staged_trace_fri_challenges = sqp_trace_fri_challenges prefix,
         staged_trace_final = sqp_trace_final prefix,
         staged_alphas = sqp_alphas prefix,
         staged_degree = sqp_degree prefix,
         staged_composition_fri_roots = sqp_composition_fri_roots prefix,
         staged_composition_fri_challenges =
            sqp_composition_fri_challenges prefix,
         staged_composition_final = sqp_composition_final prefix,
         staged_query_chunks =
            sqp_query_chunks prefix @ chunk # suffix_chunks\<rparr>"
    unfolding checked_staged_after_query_prefix_receive_def Let_def
    by (auto elim!: set_dist_bindE simp: assert_def throw_no_outcome
        split: if_splits)
  have match: "staged_query_prefix_matches_data i prefix data"
    unfolding staged_query_prefix_matches_data_def data_eq
    using prefix_len by simp
  have start_hash:
    "staged_query_start_hash data = staged_query_prefix_start_hash prefix"
    by (rule staged_query_start_hash_of_prefix_completion[OF match])
  have prefix_key_state:
    "PState prefix_state =
      state_after_query_chunks
        (staged_query_start_hash data) (staged_query_chunks data) i"
    using prefix_state_hash prefix_len start_hash
    unfolding data_eq
    by (simp add: state_after_query_chunks_append_prefix)
  have receive_lookup:
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    using receive_query_index_challenge_outcome[OF recv]
      prefix_counter prefix_key_state
    by simp
  have raw_ext_attacker: "raw_state \<le> attacker_state"
    by (rule checked_staged_after_query_prefix_receive_extends
        [OF wf controlled i_bound data_out])
  have attacker_ext_s: "attacker_state \<le> ?s"
  proof -
    have "attacker_state \<le> attacker_state"
      unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    then show ?thesis
      by (rule hash_extends_verifier_state_from_adversary_right)
  qed
  have s_ext_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have raw_ext_final: "raw_state \<le> final_state"
    by (rule hash_ext_trans[OF raw_ext_attacker])
      (rule hash_ext_trans[OF attacker_ext_s s_ext_final])
  have lookup_final_raw:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule hash_extension_lookup[OF receive_lookup raw_ext_final])
  have raw_eq: "raw_idxs ! i = raw"
    using lookup_final[rule_format, OF i_bound] lookup_final_raw by simp
  show ?thesis
    using query_idxs_eq len_raw i_bound raw_eq by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_aligned_transcript_query_bad_imp_header_authenticated_candidate_opening_query_hit_from_prefix_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and bad:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        query_bad_with_aligned_transcript_partial_candidates
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
      A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  from bad obtain fr f_fri_roots f_final as dg composition_fri_roots
      final query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent
        ?s (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      query_bad_with_aligned_transcript_partial_candidates_def
    by auto
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as
      query_idxs"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_shape
        [OF partial])
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled data_support shape]
  obtain raw_idxs where as_eq: "as = staged_alphas data"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<forall>i<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    by blast
  have aligned0:
    "accepted_with_partial_initial_openings_aligned ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
        [OF aligned])
  from accepted_with_partial_initial_openings_aligned_shapes[OF aligned0]
  obtain rest where header:
    "verifier_header_transcript ?s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    by blast
  have comp_nonempty: "composition_fri_roots \<noteq> []"
    using accepted_with_partial_initial_openings_aligned_shapes(1)
      [OF aligned0] .
  have trace_partial:
    "accepted_with_partial_trace_openings ?s
      (Some (result, final_state)) fr query_idxs trace_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(3)
      [OF aligned0] .
  have comp_partial:
    "accepted_with_partial_composition_openings ?s
      (Some (result, final_state)) (hd composition_fri_roots) query_idxs
      composition_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(4)
      [OF aligned0] .
  have header_eq:
    "fr = staged_trace_root data \<and>
     f_fri_roots = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     composition_fri_roots = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  let ?i = 0
  have i_bound: "?i < rounds"
    using rounds_positive by simp
  have round_consistent:
    "partial_query_round_consistent trace_openings composition_openings as
      ?i (query_idxs ! ?i)"
    using aligned i_bound
    unfolding accepted_with_partial_initial_openings_aligned_consistent_def
    by simp
  have opening_consistent:
    "partial_query_openings_consistent (trace_openings ! ?i)
      (composition_openings ! ?i) (staged_alphas data)
      (index (to_nat (raw_idxs ! ?i)))"
    using round_consistent query_idxs_eq len_raw i_bound header_eq
    unfolding partial_query_round_consistent_def
      partial_query_openings_consistent_def
    by simp
  have trace_table_auth:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! ?i) final_state"
    using trace_partial i_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  have comp_table_auth:
    "partial_authenticated_table (hd composition_fri_roots)
      (scale * clength) (composition_openings ! ?i) final_state"
    using comp_partial i_bound
    unfolding accepted_with_partial_composition_openings_def by blast
  have witness_header:
    "(trace_openings ! ?i, composition_openings ! ?i) \<in>
      query_header_supported_partial_opening_witnesses ?s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_opening_witnesses_def
    using comp_nonempty verifier trace_table_auth comp_table_auth header
    by blast
  have witness:
    "(trace_openings ! ?i, composition_openings ! ?i) \<in>
      query_header_supported_partial_opening_witnesses ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    using witness_header header_eq by simp
  have lookup0:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge ?i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) ?i)) =
      Some (raw_idxs ! ?i)"
    using lookup i_bound by simp
  from checked_staged_transcript_program_query_prefix_receive_final_lookup_support_with_alphas
      [OF wf controlled i_bound builder verifier lookup0]
  obtain prefix prefix_state raw_state where prefix_receive:
      "Some (((prefix, prefix_state), raw_idxs ! ?i), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A ?i)
            adversary_initial_state)"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    by blast
  have component:
    "checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefix A
      ((replicate rounds []) [?i := trace_openings ! ?i])
      ((replicate rounds []) [?i := composition_openings ! ?i])
      ?i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_opening_query_hit_from_prefixI_from_prefix_receive
        [OF i_bound builder prefix_receive alphas_eq opening_consistent])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefixI
        [OF witness component])
qed

lemma checked_staged_security_with_actual_alpha_prefix_aligned_transcript_query_bad_imp_single_round_header_target_or_gap_witness_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and bad:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        query_bad_with_aligned_transcript_partial_candidates
        (Some (((((alpha_prefix, alpha_prefix_state), data),
          attacker_state), result), final_state))"
  shows
    "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
      0 A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state)) \<or>
     checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
      0 A
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  from bad obtain fr f_fri_roots f_final as dg composition_fri_roots
      final query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent
        ?s (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
    unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      query_bad_with_aligned_transcript_partial_candidates_def
    by auto
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as
      query_idxs"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_shape
        [OF partial])
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled data_support shape]
  obtain raw_idxs where as_eq: "as = staged_alphas data"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<forall>i<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    by blast
  have aligned0:
    "accepted_with_partial_initial_openings_aligned ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
        [OF aligned])
  from accepted_with_partial_initial_openings_aligned_shapes[OF aligned0]
  obtain rest where header:
    "verifier_header_transcript ?s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    by blast
  have comp_nonempty: "composition_fri_roots \<noteq> []"
    using accepted_with_partial_initial_openings_aligned_shapes(1)
      [OF aligned0] .
  have trace_partial:
    "accepted_with_partial_trace_openings ?s
      (Some (result, final_state)) fr query_idxs trace_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(3)
      [OF aligned0] .
  have comp_partial:
    "accepted_with_partial_composition_openings ?s
      (Some (result, final_state)) (hd composition_fri_roots) query_idxs
      composition_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(4)
      [OF aligned0] .
  have header_eq:
    "fr = staged_trace_root data \<and>
     f_fri_roots = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     composition_fri_roots = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  let ?i = 0
  have i_bound: "?i < rounds"
    using rounds_positive by simp
  have round_consistent:
    "partial_query_round_consistent trace_openings composition_openings as
      ?i (query_idxs ! ?i)"
    using aligned i_bound
    unfolding accepted_with_partial_initial_openings_aligned_consistent_def
    by simp
  have opening_consistent:
    "partial_query_openings_consistent (trace_openings ! ?i)
      (composition_openings ! ?i) (staged_alphas data)
      (index (to_nat (raw_idxs ! ?i)))"
    using round_consistent query_idxs_eq len_raw i_bound header_eq
    unfolding partial_query_round_consistent_def
      partial_query_openings_consistent_def
    by simp
  have trace_table_auth:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! ?i) final_state"
    using trace_partial i_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  have comp_table_auth:
    "partial_authenticated_table (hd composition_fri_roots)
      (scale * clength) (composition_openings ! ?i) final_state"
    using comp_partial i_bound
    unfolding accepted_with_partial_composition_openings_def by blast
  have witness_header:
    "(trace_openings ! ?i, composition_openings ! ?i) \<in>
      query_header_supported_partial_opening_witnesses ?s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_opening_witnesses_def
    using comp_nonempty verifier trace_table_auth comp_table_auth header
    by blast
  have witness:
    "(trace_openings ! ?i, composition_openings ! ?i) \<in>
      query_header_supported_partial_opening_witnesses ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    using witness_header header_eq by simp
  have lookup0:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge ?i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) ?i)) =
      Some (raw_idxs ! ?i)"
    using lookup i_bound by simp
  from checked_staged_transcript_program_query_prefix_receive_final_lookup_support_with_alphas
      [OF wf controlled i_bound builder verifier lookup0]
  obtain prefix prefix_state raw_state where prefix_receive:
      "Some (((prefix, prefix_state), raw_idxs ! ?i), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A ?i)
            adversary_initial_state)"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    by blast
  have trace_candidate_single:
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [?i := trace_openings ! ?i])"
    by (rule partial_trace_table_candidate_single_round_from_all_rounds
        [OF trace_candidate i_bound])
  have comp_candidate_single:
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [?i := composition_openings ! ?i])"
    by (rule partial_composition_table_candidate_single_round_from_all_rounds
        [OF comp_candidate i_bound])
  have opening_target:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [?i := trace_openings ! ?i])
        ((replicate rounds []) [?i := composition_openings ! ?i])
        ?i)
      (Some (((prefix, prefix_state), raw_idxs ! ?i), raw_state))"
    by (rule checked_staged_query_prefix_candidate_opening_target_from_prefix_single_round_hitI
        [OF i_bound])
      (use opening_consistent alphas_eq in simp)
  have not_all_prefix:
    "\<not> all_queries_consistent trace_table composition_table
      (sqp_alphas prefix)"
    using not_all header_eq alphas_eq by simp
  have opening_subset:
    "staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [?i := trace_openings ! ?i])
        ((replicate rounds []) [?i := composition_openings ! ?i])
        ?i prefix prefix_state \<subseteq>
      staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
        composition_table prefix prefix_state"
    by (rule
        staged_query_prefix_candidate_opening_query_target_from_prefix_subset_candidate_pair_from_prefix
        [OF trace_candidate_single comp_candidate_single trace_low comp_low
          not_all_prefix])
  have pair_target:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
        composition_table)
      (Some (((prefix, prefix_state), raw_idxs ! ?i), raw_state))"
    using opening_target opening_subset
    unfolding checked_staged_query_prefix_dynamic_index_hit_def by auto
  have pair_hit:
    "checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix
      A trace_table composition_table ?i
      (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
        result), final_state))"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefixI
        [OF i_bound builder prefix_receive pair_target])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_candidate_pair_query_hit_from_prefix_with_witness_imp_single_round_header_target_or_gap_witness
        [OF pair_hit witness trace_candidate_single comp_candidate_single])
qed

definition checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_exists_at
where
  "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_exists_at
      i out \<longleftrightarrow>
    (\<exists>trace_openings composition_openings trace_table composition_table.
      checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_at
        trace_openings composition_openings trace_table composition_table i out)"

definition checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_current_exists_at
where
  "checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_current_exists_at
      i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i out \<and>
    checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_exists_at
      i out"

definition checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_at
where
  "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_at
      i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i out \<and>
    checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
      i out"

lemma checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_current_exists_bound_from_current:
  assumes current_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i)
      adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_current_exists_at
        i)
      adversary_initial_state \<le> C"
  by (rule order_trans[OF _ current_bound],
      rule wp_event_mono)
    (simp add:
      checked_staged_security_with_query_prefix_single_round_candidate_binding_gap_witness_current_exists_at_def)

lemma checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_bound_from_current:
  assumes current_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i)
      adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_at
        i)
      adversary_initial_state \<le> C"
  by (rule order_trans[OF _ current_bound],
      rule wp_event_mono)
    (simp add:
      checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_at_def)

lemma checked_staged_security_with_query_prefix_data_state_aligned_transcript_query_bad_imp_single_round_components_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A 0)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates
        (Some (((data, attacker_state), result), final_state))"
  shows
    "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_at
      0
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
      0
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  let ?i = 0
  have i_bound: "?i < rounds"
    using rounds_positive by simp
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_imp_data_state_support
        [OF i_bound support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  from bad obtain fr f_fri_roots f_final as dg composition_fri_roots
      final query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent
        ?s (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
    unfolding staged_security_with_data_state_verifier_event_def
      query_bad_with_aligned_transcript_partial_candidates_def
    by auto
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as
      query_idxs"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_shape
        [OF partial])
  have index_eq: "index (to_nat raw) = query_idxs ! ?i"
    by (rule
        checked_staged_security_with_query_prefix_data_state_accepted_shape_query_index
        [OF wf controlled i_bound support shape])
  have aligned0:
    "accepted_with_partial_initial_openings_aligned ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
        [OF aligned])
  from accepted_with_partial_initial_openings_aligned_shapes[OF aligned0]
  obtain rest where header:
    "verifier_header_transcript ?s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    by blast
  have comp_nonempty: "composition_fri_roots \<noteq> []"
    using accepted_with_partial_initial_openings_aligned_shapes(1)
      [OF aligned0] .
  have trace_partial:
    "accepted_with_partial_trace_openings ?s
      (Some (result, final_state)) fr query_idxs trace_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(3)
      [OF aligned0] .
  have comp_partial:
    "accepted_with_partial_composition_openings ?s
      (Some (result, final_state)) (hd composition_fri_roots) query_idxs
      composition_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(4)
      [OF aligned0] .
  have header_eq:
    "fr = staged_trace_root data \<and>
     f_fri_roots = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     composition_fri_roots = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  have alphas_eq: "staged_alphas data = sqp_alphas prefix"
    by (rule checked_staged_security_with_query_prefix_data_state_alphas_eq)
      (rule support)
  have round_consistent:
    "partial_query_round_consistent trace_openings composition_openings as
      ?i (query_idxs ! ?i)"
    using aligned i_bound
    unfolding accepted_with_partial_initial_openings_aligned_consistent_def
    by simp
  have opening_consistent:
    "partial_query_openings_consistent (trace_openings ! ?i)
      (composition_openings ! ?i) (sqp_alphas prefix)
      (index (to_nat raw))"
    using round_consistent index_eq header_eq alphas_eq
    unfolding partial_query_round_consistent_def
      partial_query_openings_consistent_def
    by simp
  have trace_table_auth:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! ?i) final_state"
    using trace_partial i_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  have comp_table_auth:
    "partial_authenticated_table (hd composition_fri_roots)
      (scale * clength) (composition_openings ! ?i) final_state"
    using comp_partial i_bound
    unfolding accepted_with_partial_composition_openings_def by blast
  have witness_header:
    "(trace_openings ! ?i, composition_openings ! ?i) \<in>
      query_header_supported_partial_opening_witnesses ?s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_opening_witnesses_def
    using comp_nonempty verifier trace_table_auth comp_table_auth header
    by blast
  have witness:
    "(trace_openings ! ?i, composition_openings ! ?i) \<in>
      query_header_supported_partial_opening_witnesses ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    using witness_header header_eq by simp
  have trace_candidate_single:
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [?i := trace_openings ! ?i])"
    by (rule partial_trace_table_candidate_single_round_from_all_rounds
        [OF trace_candidate i_bound])
  have comp_candidate_single:
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [?i := composition_openings ! ?i])"
    by (rule partial_composition_table_candidate_single_round_from_all_rounds
        [OF comp_candidate i_bound])
  have opening_target:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [?i := trace_openings ! ?i])
        ((replicate rounds []) [?i := composition_openings ! ?i])
        ?i)
      (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule checked_staged_query_prefix_candidate_opening_target_from_prefix_single_round_hitI
        [OF i_bound opening_consistent])
  have not_all_prefix:
    "\<not> all_queries_consistent trace_table composition_table
      (sqp_alphas prefix)"
    using not_all header_eq alphas_eq by simp
  have opening_subset:
    "staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [?i := trace_openings ! ?i])
        ((replicate rounds []) [?i := composition_openings ! ?i])
        ?i prefix prefix_state \<subseteq>
      staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
        composition_table prefix prefix_state"
    by (rule
        staged_query_prefix_candidate_opening_query_target_from_prefix_subset_candidate_pair_from_prefix
        [OF trace_candidate_single comp_candidate_single trace_low comp_low
          not_all_prefix])
  have pair_target:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
        composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
    using opening_target opening_subset
    unfolding checked_staged_query_prefix_dynamic_index_hit_def by auto
  have auth_hit:
    "checked_staged_security_with_query_prefix_authenticated_opening_hit
      (trace_openings ! ?i) (composition_openings ! ?i) ?i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    unfolding
      checked_staged_security_with_query_prefix_authenticated_opening_hit_def
    using comp_nonempty trace_table_auth comp_table_auth opening_consistent
      header_eq alphas_eq
    by simp
  show ?thesis
  proof (cases
      "(trace_table, composition_table) \<in>
        query_header_supported_single_round_partial_table_candidates
          prefix_state
          (sqp_trace_root prefix)
          (sqp_trace_fri_roots prefix)
          (sqp_trace_final prefix)
          (sqp_alphas prefix)
          (sqp_degree prefix)
          (sqp_composition_fri_roots prefix)
          (sqp_composition_final prefix)
          ?i")
    case True
    have target_hit:
      "checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_single_round_header_supported_query_target ?i)
        (Some (((prefix, prefix_state), raw), raw_state))"
      by (rule
          checked_staged_query_prefix_candidate_pair_hit_imp_single_round_header_target_hit
          [OF True pair_target])
    have
      "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_at
        ?i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_at_def
        checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at_def
      using target_hit
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_atI
          [OF auth_hit]
      by simp
    then show ?thesis by simp
  next
    case False
    have success_prefix:
      "index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (sqp_alphas prefix)"
      using pair_target
      unfolding
        checked_staged_query_prefix_dynamic_index_hit_def
        staged_query_prefix_candidate_pair_query_target_from_prefix_def
      by simp
    have gap_witness:
      "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
        (trace_openings ! ?i) (composition_openings ! ?i)
        trace_table composition_table ?i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      by (rule
          checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_atI
          [OF success_prefix witness trace_candidate_single
            comp_candidate_single False])
    have gap_exists:
      "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
        ?i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      by (rule
          checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_atI
          [OF gap_witness])
    then show ?thesis
      using gap_exists by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_data_state_aligned_transcript_query_bad_extract_round0_authenticated_opening_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A 0)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates
        (Some (((data, attacker_state), result), final_state))"
  obtains trace_opening composition_opening trace_table composition_table where
    "checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_opening composition_opening 0
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    "(trace_opening, composition_opening) \<in>
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
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [0 := trace_opening])"
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [0 := composition_opening])"
    "trace_table_low_degree trace_table"
    "composition_table_low_degree maxDegree composition_table"
    "\<not> all_queries_consistent trace_table composition_table
      (sqp_alphas prefix)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  let ?i = 0
  have i_bound: "?i < rounds"
    using rounds_positive by simp
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_imp_data_state_support
        [OF i_bound support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  from bad obtain fr f_fri_roots f_final as dg composition_fri_roots
      final query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent
        ?s (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
    unfolding staged_security_with_data_state_verifier_event_def
      query_bad_with_aligned_transcript_partial_candidates_def
    by auto
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  have aligned0:
    "accepted_with_partial_initial_openings_aligned ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
        [OF aligned])
  from accepted_with_partial_initial_openings_aligned_shapes[OF aligned0]
  obtain rest where header:
    "verifier_header_transcript ?s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    by blast
  have comp_nonempty: "composition_fri_roots \<noteq> []"
    using accepted_with_partial_initial_openings_aligned_shapes(1)
      [OF aligned0] .
  have trace_partial:
    "accepted_with_partial_trace_openings ?s
      (Some (result, final_state)) fr query_idxs trace_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(3)
      [OF aligned0] .
  have comp_partial:
    "accepted_with_partial_composition_openings ?s
      (Some (result, final_state)) (hd composition_fri_roots) query_idxs
      composition_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(4)
      [OF aligned0] .
  have header_eq:
    "fr = staged_trace_root data \<and>
     f_fri_roots = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     composition_fri_roots = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  have alphas_eq: "staged_alphas data = sqp_alphas prefix"
    by (rule checked_staged_security_with_query_prefix_data_state_alphas_eq)
      (rule support)
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as
      query_idxs"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_shape
        [OF partial])
  have index_eq: "index (to_nat raw) = query_idxs ! ?i"
    by (rule
        checked_staged_security_with_query_prefix_data_state_accepted_shape_query_index
        [OF wf controlled i_bound support shape])
  have round_consistent:
    "partial_query_round_consistent trace_openings composition_openings as
      ?i (query_idxs ! ?i)"
    using aligned i_bound
    unfolding accepted_with_partial_initial_openings_aligned_consistent_def
    by simp
  have opening_consistent:
    "partial_query_openings_consistent (trace_openings ! ?i)
      (composition_openings ! ?i) (sqp_alphas prefix)
      (index (to_nat raw))"
    using round_consistent index_eq header_eq alphas_eq
    unfolding partial_query_round_consistent_def
      partial_query_openings_consistent_def
    by simp
  have trace_table_auth:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! ?i) final_state"
    using trace_partial i_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  have comp_table_auth:
    "partial_authenticated_table (hd composition_fri_roots)
      (scale * clength) (composition_openings ! ?i) final_state"
    using comp_partial i_bound
    unfolding accepted_with_partial_composition_openings_def by blast
  have witness_header:
    "(trace_openings ! ?i, composition_openings ! ?i) \<in>
      query_header_supported_partial_opening_witnesses ?s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_opening_witnesses_def
    using comp_nonempty verifier trace_table_auth comp_table_auth header
    by blast
  have witness:
    "(trace_openings ! ?i, composition_openings ! ?i) \<in>
      query_header_supported_partial_opening_witnesses ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    using witness_header header_eq by simp
  have trace_candidate_single:
    "partial_trace_table_candidate trace_table
      ((replicate rounds []) [?i := trace_openings ! ?i])"
    by (rule partial_trace_table_candidate_single_round_from_all_rounds
        [OF trace_candidate i_bound])
  have comp_candidate_single:
    "partial_composition_table_candidate composition_table
      ((replicate rounds []) [?i := composition_openings ! ?i])"
    by (rule partial_composition_table_candidate_single_round_from_all_rounds
        [OF comp_candidate i_bound])
  have auth_hit:
    "checked_staged_security_with_query_prefix_authenticated_opening_hit
      (trace_openings ! ?i) (composition_openings ! ?i) ?i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    unfolding
      checked_staged_security_with_query_prefix_authenticated_opening_hit_def
    using comp_nonempty trace_table_auth comp_table_auth opening_consistent
      header_eq alphas_eq
    by simp
  have not_all_prefix:
    "\<not> all_queries_consistent trace_table composition_table
      (sqp_alphas prefix)"
    using not_all header_eq alphas_eq by simp
  show ?thesis
    by (rule that[OF auth_hit witness trace_candidate_single
          comp_candidate_single trace_low comp_low not_all_prefix])
qed

lemma checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_query_prefix_single_round_components:
  fixes T Gap :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and target_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A 0)
        (checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_at
          0)
        adversary_initial_state \<le> T"
    and gap_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A 0)
        (checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
          0)
        adversary_initial_state \<le> Gap"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> T + Gap"
proof -
  let ?i = 0
  let ?m =
    "checked_staged_security_experiment_with_query_prefix_data_state A ?i"
  let ?query =
    "staged_security_with_data_state_verifier_event
      query_bad_with_aligned_transcript_partial_candidates"
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow> ?query None
    | Some (packed, t) \<Rightarrow> ?query (Some (snd packed, t))"
  let ?target =
    "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_at
      ?i"
  let ?gap =
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
      ?i"
  have i_bound: "?i < rounds"
    using rounds_positive by simp
  have projection:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      ?query adversary_initial_state =
     wp_event ?m ?projected adversary_initial_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound])
  have event_le:
    "wp_event ?m ?projected adversary_initial_state \<le>
     wp_event ?m (\<lambda>out. ?target out \<or> ?gap out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?m adversary_initial_state)"
      and projected: "?projected out"
    show "?target out \<or> ?gap out"
    proof (cases out)
      case None
      then show ?thesis
        using projected
        unfolding staged_security_with_data_state_verifier_event_def by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state
          result final_state where out_eq:
        "out =
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      have bad:
        "staged_security_with_data_state_verifier_event
          query_bad_with_aligned_transcript_partial_candidates
          (Some (((data, attacker_state), result), final_state))"
        using projected unfolding out_eq by simp
      show ?thesis
        unfolding out_eq
        by (rule
            checked_staged_security_with_query_prefix_data_state_aligned_transcript_query_bad_imp_single_round_components_on_support
            [OF wf controlled])
          (use support bad out_eq in simp_all)
    qed
  qed
  have union_bound:
    "wp_event ?m (\<lambda>out. ?target out \<or> ?gap out)
      adversary_initial_state \<le>
     wp_event ?m ?target adversary_initial_state +
     wp_event ?m ?gap adversary_initial_state"
    by (rule wp_event_union_bound)
  have sum_bound:
    "wp_event ?m ?target adversary_initial_state +
     wp_event ?m ?gap adversary_initial_state \<le> T + Gap"
    by (rule add_mono[OF target_bound gap_bound])
  show ?thesis
    unfolding projection
    by (rule order_trans[OF event_le order_trans[OF union_bound sum_bound]])
qed

lemma checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_query_prefix_single_round_target_and_gap_components:
  fixes T Gap :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and target_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A 0)
        (checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_at
          0)
        adversary_initial_state \<le> T"
    and gap_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A 0)
        (checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
          0)
        adversary_initial_state \<le> Gap"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> T + Gap"
  by (rule
      checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_query_prefix_single_round_components
      [OF wf controlled target_bound gap_bound])

lemma checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_query_prefix_single_round_target_and_transcript_gap:
  fixes T P Q :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and target_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A 0)
        (checked_staged_security_with_query_prefix_single_round_header_supported_query_target_current_hit_at
          0)
        adversary_initial_state \<le> T"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> T + (P + Q)"
proof -
  have i_bound: "0 < rounds"
    using rounds_positive by simp
  have gap_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A 0)
      (checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at
        0)
      adversary_initial_state \<le> P + Q"
    by (rule
        checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_exists_at_bound_from_data_pre_and_new
        [OF i_bound data_pre_bound new_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_query_prefix_single_round_target_and_gap_components
        [OF wf controlled target_bound gap_bound])
qed

lemma checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_header_authenticated_candidate_opening_query_hit_from_prefix:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and header_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
          A)
        adversary_initial_state \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> Q"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  let ?query =
    "staged_security_with_data_state_verifier_event
      query_bad_with_aligned_transcript_partial_candidates"
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (packed, t) \<Rightarrow> ?query (Some (?project packed, t))"
  have projection:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      ?query adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?projected adversary_initial_state"
  proof -
    have
      "wp_event (checked_staged_security_experiment_with_data_state A)
        ?query adversary_initial_state =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
          \<bind> (\<lambda>x. return (?project x)))
        ?query adversary_initial_state"
      using
        checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
        [of A]
      by simp
    also have "... =
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        ?projected adversary_initial_state"
      by (subst wp_event_bind_return_map)
        (simp add: staged_security_with_data_state_verifier_event_def)
    finally show ?thesis
      by simp
  qed
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?projected adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
        A)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
                A)
              adversary_initial_state)"
      and projected: "?projected out"
    show
      "checked_staged_security_with_actual_alpha_prefix_header_authenticated_candidate_opening_query_hit_from_prefix
        A out"
    proof (cases out)
      case None
      then show ?thesis
        using projected by simp
    next
      case (Some packed)
      then obtain alpha_prefix alpha_prefix_state data attacker_state
          result final_state where out_eq:
          "out =
            Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      have bad:
        "checked_staged_security_with_actual_alpha_prefix_verifier_event
          query_bad_with_aligned_transcript_partial_candidates out"
        using projected unfolding out_eq
        by (simp add:
            checked_staged_security_with_actual_alpha_prefix_verifier_event_def
            staged_security_with_data_state_verifier_event_def Let_def)
      show ?thesis
        unfolding out_eq
        by (rule
            checked_staged_security_with_actual_alpha_prefix_aligned_transcript_query_bad_imp_header_authenticated_candidate_opening_query_hit_from_prefix_on_support
            [OF wf controlled])
          (use support bad out_eq in simp_all)
    qed
  qed
  show ?thesis
    unfolding projection
    by (rule order_trans[OF event_le header_bound])
qed

lemma checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_single_round_components:
  fixes T Gap :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and target_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
          0 A)
        adversary_initial_state \<le> T"
    and gap_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
          0 A)
        adversary_initial_state \<le> Gap"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> T + Gap"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  let ?query =
    "staged_security_with_data_state_verifier_event
      query_bad_with_aligned_transcript_partial_candidates"
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (packed, t) \<Rightarrow> ?query (Some (?project packed, t))"
  let ?target =
    "checked_staged_security_with_actual_alpha_prefix_single_round_header_supported_query_target_hit_at
      0 A"
  let ?gap =
    "checked_staged_security_with_actual_alpha_prefix_query_prefix_single_round_candidate_binding_gap_witness_at
      0 A"
  have projection:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      ?query adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?projected adversary_initial_state"
  proof -
    have
      "wp_event (checked_staged_security_experiment_with_data_state A)
        ?query adversary_initial_state =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
          \<bind> (\<lambda>x. return (?project x)))
        ?query adversary_initial_state"
      using
        checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
        [of A]
      by simp
    also have "... =
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        ?projected adversary_initial_state"
      by (subst wp_event_bind_return_map)
        (simp add: staged_security_with_data_state_verifier_event_def)
    finally show ?thesis
      by simp
  qed
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?projected adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. ?target out \<or> ?gap out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
                A)
              adversary_initial_state)"
      and projected: "?projected out"
    show "?target out \<or> ?gap out"
    proof (cases out)
      case None
      then show ?thesis
        using projected by simp
    next
      case (Some packed)
      then obtain alpha_prefix alpha_prefix_state data attacker_state
          result final_state where out_eq:
          "out =
            Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      have bad:
        "checked_staged_security_with_actual_alpha_prefix_verifier_event
          query_bad_with_aligned_transcript_partial_candidates out"
        using projected unfolding out_eq
        by (simp add:
            checked_staged_security_with_actual_alpha_prefix_verifier_event_def
            staged_security_with_data_state_verifier_event_def Let_def)
      show ?thesis
        unfolding out_eq
        by (rule
            checked_staged_security_with_actual_alpha_prefix_aligned_transcript_query_bad_imp_single_round_header_target_or_gap_witness_on_support
            [OF wf controlled])
          (use support bad out_eq in simp_all)
    qed
  qed
  have union_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. ?target out \<or> ?gap out)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?target adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?gap adversary_initial_state"
    by (rule wp_event_union_bound)
  have sum_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?target adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?gap adversary_initial_state \<le> T + Gap"
    by (rule add_mono[OF target_bound gap_bound])
  show ?thesis
    unfolding projection
    by (rule order_trans[OF event_le order_trans[OF union_bound sum_bound]])
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_success_witness_gapE:
  assumes i_bound: "i < rounds"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and success:
      "\<And>prefix prefix_state raw raw_state.
        Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        sqp_alphas prefix = staged_alphas data \<Longrightarrow>
        index (to_nat raw) \<in>
          query_sampling_success_space trace_table composition_table
            (staged_alphas data)"
    and witness:
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
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and notin:
      "\<And>prefix prefix_state raw raw_state.
        Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        sqp_alphas prefix = staged_alphas data \<Longrightarrow>
        (trace_table, composition_table) \<notin>
          query_header_supported_single_round_partial_table_candidates
            prefix_state
            (sqp_trace_root prefix)
            (sqp_trace_fri_roots prefix)
            (sqp_trace_final prefix)
            (sqp_alphas prefix)
            (sqp_degree prefix)
            (sqp_composition_fri_roots prefix)
            (sqp_composition_final prefix)
            i"
  obtains prefix prefix_state raw raw_state where
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  from checked_staged_security_with_actual_alpha_prefix_support_query_prefix_data_state_alphasE
      [OF i_bound support]
  obtain prefix prefix_state raw raw_state where qsupport:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    by blast
  have success_prefix:
    "index (to_nat raw) \<in>
      query_sampling_success_space trace_table composition_table
        (sqp_alphas prefix)"
    using success[OF qsupport alphas_eq] alphas_eq by simp
  have notin_prefix:
    "(trace_table, composition_table) \<notin>
      query_header_supported_single_round_partial_table_candidates
        prefix_state
        (sqp_trace_root prefix)
        (sqp_trace_fri_roots prefix)
        (sqp_trace_final prefix)
        (sqp_alphas prefix)
        (sqp_degree prefix)
        (sqp_composition_fri_roots prefix)
        (sqp_composition_final prefix)
        i"
    by (rule notin[OF qsupport alphas_eq])
  have fixed_gap:
    "checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_at
      trace_openings composition_openings trace_table composition_table i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    by (rule checked_staged_security_with_query_prefix_single_round_candidate_pair_witness_gap_atI
        [OF success_prefix witness trace_candidate comp_candidate notin_prefix])
  show ?thesis
    by (rule that[OF qsupport fixed_gap])
qed

lemma checked_staged_security_with_actual_alpha_prefix_candidate_pair_success_header_targetE:
  assumes i_bound: "i < rounds"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and success:
      "\<And>prefix prefix_state raw raw_state.
        Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        sqp_alphas prefix = staged_alphas data \<Longrightarrow>
        index (to_nat raw) \<in>
          query_sampling_success_space trace_table composition_table
            (staged_alphas data)"
    and supported:
      "\<And>prefix prefix_state raw raw_state.
        Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state
                A i)
              adversary_initial_state) \<Longrightarrow>
        sqp_alphas prefix = staged_alphas data \<Longrightarrow>
        (trace_table, composition_table) \<in>
          query_header_supported_single_round_partial_table_candidates
            prefix_state
            (sqp_trace_root prefix)
            (sqp_trace_fri_roots prefix)
            (sqp_trace_final prefix)
            (sqp_alphas prefix)
            (sqp_degree prefix)
            (sqp_composition_fri_roots prefix)
            (sqp_composition_final prefix)
            i"
  obtains prefix prefix_state raw raw_state where
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  from checked_staged_security_with_actual_alpha_prefix_support_query_prefix_data_state_alphasE
      [OF i_bound support]
  obtain prefix prefix_state raw raw_state where qsupport:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    by blast
  have success_prefix:
    "index (to_nat raw) \<in>
      query_sampling_success_space trace_table composition_table
        (sqp_alphas prefix)"
    using success[OF qsupport alphas_eq] alphas_eq by simp
  have pair_target_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_candidate_pair_query_target_from_prefix
        trace_table composition_table)
      (Some (((prefix, prefix_state), raw), raw_state))"
    using success_prefix
    unfolding
      checked_staged_query_prefix_dynamic_index_hit_def
      staged_query_prefix_candidate_pair_query_target_from_prefix_def
    by simp
  have supported_prefix:
    "(trace_table, composition_table) \<in>
      query_header_supported_single_round_partial_table_candidates
        prefix_state
        (sqp_trace_root prefix)
        (sqp_trace_fri_roots prefix)
        (sqp_trace_final prefix)
        (sqp_alphas prefix)
        (sqp_degree prefix)
        (sqp_composition_fri_roots prefix)
        (sqp_composition_final prefix)
        i"
    by (rule supported[OF qsupport alphas_eq])
  have target_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_single_round_header_supported_query_target i)
      (Some (((prefix, prefix_state), raw), raw_state))"
    by (rule
        checked_staged_query_prefix_candidate_pair_hit_imp_single_round_header_target_hit
        [OF supported_prefix pair_target_hit])
  have query_prefix_hit:
    "checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    unfolding
      checked_staged_security_with_query_prefix_single_round_header_supported_query_target_hit_at_def
    using target_hit by simp
  show ?thesis
    by (rule that[OF qsupport query_prefix_hit])
qed

end

end
