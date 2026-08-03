(*  Title:      Stark/Soundness_Conceptual_Query_Empty_Current.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Conceptual_Query_Empty_Current
  imports
    Soundness_Query_Opening_Consistency
    Soundness_Conceptual_Query_Current
    Staged_Security_Experiment_Composition_Query_Current_Path
    Soundness_Staged_Bounds
begin

text \<open>
  Empty-composition current-query projection.

  This layer connects the verifier-local empty-composition query extraction to
  the prefix-fixed conceptual empty query target infrastructure.  It is kept
  separate from the non-empty current-query layer to avoid growing the already
  size-sensitive staged/query theories.
\<close>

context soundness
begin

definition staged_security_with_data_state_current_empty_query_opening_hit_at
  :: "nat \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "staged_security_with_data_state_current_empty_query_opening_hit_at i out
    \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), result), final_state) \<Rightarrow>
          (let s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in
            (\<exists>raw trace_openings rest.
              i < rounds \<and>
              fmlookup (HashMap final_state)
                (QueryIndexChallenge i
                  (state_after_query_chunks
                    (staged_query_start_hash data)
                    (staged_query_chunks data) i)) =
                Some raw \<and>
              staged_composition_fri_roots data = [] \<and>
              Some (result, final_state) \<in>
                set_dist (execute verify_monad s) \<and>
              partial_authenticated_table (staged_trace_root data)
                (scale * clength) trace_openings final_state \<and>
              verifier_header_transcript s
                (staged_trace_root data)
                (staged_trace_fri_roots data)
                (staged_trace_final data)
                (staged_alphas data)
                (staged_degree data)
                []
                (staged_composition_final data)
                rest \<and>
              map opening_index trace_openings =
                powers_scaled (index (to_nat raw)) \<and>
              cp_eval (staged_alphas data) (map opening_value trace_openings)
                (h ^ index (to_nat raw) * shift) =
                staged_composition_final data)))"

definition staged_security_with_data_state_current_empty_query_opening_hit
  :: "((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "staged_security_with_data_state_current_empty_query_opening_hit out
    \<longleftrightarrow>
      (\<exists>i < rounds.
        staged_security_with_data_state_current_empty_query_opening_hit_at
          i out)"

lemma staged_security_with_data_state_current_empty_query_opening_hitI:
  assumes "i < rounds"
    and "staged_security_with_data_state_current_empty_query_opening_hit_at
      i out"
  shows "staged_security_with_data_state_current_empty_query_opening_hit out"
  using assms
  unfolding staged_security_with_data_state_current_empty_query_opening_hit_def
  by blast

lemma staged_security_with_data_state_current_empty_query_opening_hit_atI:
  assumes i_bound: "i < rounds"
    and lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
        Some raw"
    and comp_empty: "staged_composition_fri_roots data = []"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and header:
      "verifier_header_transcript
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        []
        (staged_composition_final data)
        rest"
    and trace_indices:
      "map opening_index trace_openings =
        powers_scaled (index (to_nat raw))"
    and consistent:
      "cp_eval (staged_alphas data) (map opening_value trace_openings)
        (h ^ index (to_nat raw) * shift) =
        staged_composition_final data"
  shows
    "staged_security_with_data_state_current_empty_query_opening_hit_at i
      (Some (((data, attacker_state), result), final_state))"
  unfolding staged_security_with_data_state_current_empty_query_opening_hit_at_def
    Let_def
  apply simp
  by (intro exI[of _ raw] exI[of _ trace_openings] exI[of _ rest] conjI)
    (use assms in simp_all)

lemma empty_query_bad_header_alignment_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates
        (Some (((data, attacker_state), result), final_state))"
  obtains fr f_fri_roots f_final as dg final rest where
    "verifier_header_transcript
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      fr f_fri_roots f_final as dg [] final rest"
    "fr = staged_trace_root data"
    "f_fri_roots = staged_trace_fri_roots data"
    "f_final = staged_trace_final data"
    "as = staged_alphas data"
    "dg = staged_degree data"
    "staged_composition_fri_roots data = []"
    "final = staged_composition_final data"
    "rest = List.concat (staged_query_chunks data)"
    "verifier_header_state
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      fr f_fri_roots f_final as dg [] final =
      staged_query_start_hash data"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support]
  obtain builder where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
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
  have bad_verifier:
    "query_bad_with_empty_composition_header_candidates ?s
      (Some (result, final_state))"
    using bad
    unfolding staged_security_with_data_state_verifier_event_def
    by simp
  from bad_verifier obtain fr f_fri_roots f_final as dg final
      trace_query_idxs trace_openings trace_table composition_table
    where partial:
      "accepted_with_empty_composition_header_candidates ?s
        (Some (result, final_state)) fr f_fri_roots f_final as dg final
        trace_query_idxs trace_openings trace_table composition_table"
    unfolding query_bad_with_empty_composition_header_candidates_def
    by blast
  from partial obtain rest where header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg []
        final rest"
    unfolding accepted_with_empty_composition_header_candidates_def
    by blast
  have header_eq:
    "fr = staged_trace_root data \<and>
     f_fri_roots = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     [] = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  have header_state:
    "verifier_header_state ?s fr f_fri_roots f_final as dg [] final =
      staged_query_start_hash data"
    using header_eq
    unfolding verifier_header_state_def verifier_header_messages_def
      staged_query_start_hash_def staged_composition_fri_start_hash_def
      staged_trace_fri_start_hash_def
    by simp
  show ?thesis
    by (rule that[OF header])
      (use header_eq header_state in simp_all)
qed

lemma empty_query_bad_query_rounds_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates
        (Some (((data, attacker_state), result), final_state))"
  obtains f_fl query_state where
    "PState query_state = staged_query_start_hash data"
    "PQueryCounter query_state = 0"
    "Some (result, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program
              (staged_trace_root data)
              f_fl
              (staged_trace_final data)
              (staged_alphas data)
              []
              (staged_composition_final data))
            rounds)
          query_state)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support]
  have verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  from empty_query_bad_header_alignment_on_support
      [OF wf controlled support bad]
  obtain fr f_fri_roots f_final as dg final rest where header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg []
        final rest"
    and fr_eq: "fr = staged_trace_root data"
    and f_final_eq: "f_final = staged_trace_final data"
    and as_eq: "as = staged_alphas data"
    and final_eq: "final = staged_composition_final data"
    and header_state:
      "verifier_header_state ?s fr f_fri_roots f_final as dg [] final =
        staged_query_start_hash data"
    by blast
  from verify_monad_supplied_empty_header_query_rounds[OF verifier header]
  obtain f_fl query_state where
    query_state_state:
      "PState query_state =
        verifier_header_state ?s fr f_fri_roots f_final as dg [] final"
    and query_counter: "PQueryCounter query_state = PQueryCounter ?s"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as [] final)
              rounds)
            query_state)"
    by blast
  show ?thesis
    by (rule that[of query_state f_fl])
      (use query_state_state query_counter query_out header_state fr_eq
        f_final_eq as_eq final_eq in simp_all)
qed

lemma staged_security_with_data_state_current_empty_query_opening_hit_at_imp_query_prefix_current_on_support:
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
    and hit:
      "staged_security_with_data_state_current_empty_query_opening_hit_at i
        (Some (((data, attacker_state), result), final_state))"
  shows
    "checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have hit':
    "\<exists>raw' trace_openings rest.
      i < rounds \<and>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some raw' \<and>
      staged_composition_fri_roots data = [] \<and>
      Some (result, final_state) \<in> set_dist (execute verify_monad ?s) \<and>
      partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state \<and>
      verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        []
        (staged_composition_final data)
        rest \<and>
      map opening_index trace_openings =
        powers_scaled (index (to_nat raw')) \<and>
      cp_eval (staged_alphas data) (map opening_value trace_openings)
        (h ^ index (to_nat raw') * shift) =
        staged_composition_final data"
    using hit
    unfolding
      staged_security_with_data_state_current_empty_query_opening_hit_at_def
      Let_def
    by simp
  from hit' obtain raw' trace_openings rest where
    final_lookup':
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some raw'"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and trace_indices:
      "map opening_index trace_openings =
        powers_scaled (index (to_nat raw'))"
    and consistent:
      "cp_eval (staged_alphas data) (map opening_value trace_openings)
        (h ^ index (to_nat raw') * shift) =
        staged_composition_final data"
    by blast
  have final_lookup:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_raw_final_lookup
        [OF wf controlled i_bound support])
  have raw_eq: "raw' = raw"
    using final_lookup' final_lookup by simp
  from support obtain chunk chunk_state assert_state record_state suffix_chunks
    where data_eq:
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
         staged_query_chunks = sqp_query_chunks prefix @ chunk # suffix_chunks\<rparr>"
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
      checked_staged_after_query_prefix_receive_with_verifier_def
      checked_staged_after_query_prefix_receive_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have current:
    "checked_staged_security_with_query_prefix_empty_authenticated_opening_hit
      trace_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    unfolding
      checked_staged_security_with_query_prefix_empty_authenticated_opening_hit_def
    using trace_auth trace_indices consistent raw_eq data_eq by simp
  show ?thesis
    unfolding
      checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at_def
    using current by blast
qed

lemma checked_staged_security_with_data_state_current_empty_query_opening_hit_at_le_query_prefix_current:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_empty_query_opening_hit_at i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at i)
      adversary_initial_state"
proof -
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow>
        staged_security_with_data_state_current_empty_query_opening_hit_at
          i None
    | Some (packed, t) \<Rightarrow>
        staged_security_with_data_state_current_empty_query_opening_hit_at
          i (Some (snd packed, t))"
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_empty_query_opening_hit_at i)
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      ?projected
      adversary_initial_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound])
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      ?projected
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at i)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state A i)
              adversary_initial_state)"
      and hit: "?projected out"
    show
      "checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at
        i out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          staged_security_with_data_state_current_empty_query_opening_hit_at_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
          "out =
            Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      show ?thesis
        unfolding out_eq
        by (rule
            staged_security_with_data_state_current_empty_query_opening_hit_at_imp_query_prefix_current_on_support
            [OF wf controlled i_bound])
          (use support hit out_eq in simp_all)
    qed
  qed
  show ?thesis
    unfolding projection
    by (rule event_le)
qed

lemma empty_query_bad_imp_current_empty_opening_hit_at_zero_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates
        (Some (((data, attacker_state), result), final_state))"
  shows
    "staged_security_with_data_state_current_empty_query_opening_hit_at 0
      (Some (((data, attacker_state), result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support]
  have verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  from empty_query_bad_header_alignment_on_support
      [OF wf controlled support bad]
  obtain rest where header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        []
        (staged_composition_final data)
        rest"
    and comp_empty:
      "staged_composition_fri_roots data = []"
    by blast
  from empty_query_bad_query_rounds_on_support
      [OF wf controlled support bad]
  obtain f_fl query_state where query_state_state:
      "PState query_state = staged_query_start_hash data"
    and query_counter:
      "PQueryCounter query_state = 0"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program
                (staged_trace_root data)
                f_fl
                (staged_trace_final data)
                (staged_alphas data)
                []
                (staged_composition_final data))
              rounds)
            query_state)"
    by blast
  from ntimes_verifier_query_rounds_empty_composition_first_consistent
      [OF refl query_out]
  obtain raw trace_openings where trace_indices:
      "map opening_index trace_openings =
        powers_scaled (index (to_nat raw))"
    and trace_table:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and consistent:
      "cp_eval (staged_alphas data) (map opening_value trace_openings)
        (h ^ index (to_nat raw) * shift) =
      staged_composition_final data"
    and lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter query_state) (PState query_state)) =
      Some raw"
    by blast
  have zero_bound: "0 < rounds"
    using rounds_positive by simp
  have lookup0:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge 0
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) 0)) =
      Some raw"
    using lookup query_state_state query_counter
    unfolding state_after_query_chunks_def by simp
  show ?thesis
    by (rule
        staged_security_with_data_state_current_empty_query_opening_hit_atI
        [OF zero_bound lookup0 comp_empty verifier trace_table header
          trace_indices consistent])
qed

lemma checked_staged_security_with_data_state_empty_query_bad_le_current_empty_opening_hit_at_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
      adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates out"
  show
    "staged_security_with_data_state_current_empty_query_opening_hit_at 0 out"
  proof (cases out)
    case None
    then show ?thesis
      using bad
      unfolding staged_security_with_data_state_verifier_event_def
        query_bad_with_empty_composition_header_candidates_def
      by simp
  next
    case (Some packed)
    then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
      by (cases packed) (auto split: prod.splits)
    show ?thesis
      unfolding out_eq
      by (rule empty_query_bad_imp_current_empty_opening_hit_at_zero_on_support
          [OF wf controlled])
        (use support bad out_eq in simp_all)
  qed
qed

lemma checked_staged_security_with_data_state_current_empty_query_opening_hit_at_bound_from_prefix_and_path:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
          i)
        adversary_initial_state \<le> P"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at
          i)
        adversary_initial_state \<le> T"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_empty_query_opening_hit_at i)
      adversary_initial_state \<le> P + T"
proof -
  have current_le_prefix:
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_empty_query_opening_hit_at i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at i)
      adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_current_empty_query_opening_hit_at_le_query_prefix_current
        [OF wf controlled i_bound])
  have prefix_bound':
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at i)
      adversary_initial_state \<le> P + T"
    by (rule
        checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at_bound_from_prefix_and_path
        [OF wf controlled i_bound prefix_bound path_bound])
  show ?thesis
    by (rule order_trans[OF current_le_prefix prefix_bound'])
qed

lemma checked_staged_security_with_data_state_current_empty_query_opening_hit_at_bound_from_conceptual_empty_residual_and_path:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and residual_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
          i)
        adversary_initial_state \<le> R"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at
          i)
        adversary_initial_state \<le> T"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_empty_query_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R + T"
proof -
  have prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
        i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R"
    by (rule
        checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at_bound_from_conceptual_empty_residual
        [OF wf controlled i_bound residual_bound])
  have current_bound:
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_empty_query_opening_hit_at i)
      adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R) + T"
    by (rule
        checked_staged_security_with_data_state_current_empty_query_opening_hit_at_bound_from_prefix_and_path
        [OF wf controlled i_bound prefix_bound path_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at_bound_from_transcript:
  assumes i_bound: "i < rounds"
    and pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at
        i)
      adversary_initial_state \<le> P + R"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at
        i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      checked_staged_security_with_query_prefix_transcript_hit
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state A i)
              adversary_initial_state)"
      and hit:
        "checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at
          i out"
    show "checked_staged_security_with_query_prefix_transcript_hit out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at_def
          checked_staged_security_with_query_prefix_empty_trace_path_output_hit_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
          "out =
            Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      have mapped_support:
        "Some (((data, attacker_state), result), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state A i \<bind>
                (\<lambda>packed. return (snd packed)))
              adversary_initial_state)"
        unfolding out_eq
        by (rule set_dist_bindI[OF support[unfolded out_eq]]) simp
      have projection:
        "checked_staged_security_experiment_with_query_prefix_data_state A i \<bind>
            (\<lambda>packed. return (snd packed)) =
          checked_staged_security_experiment_with_data_state A"
        by (rule checked_staged_security_experiment_with_query_prefix_data_state_projection
            [OF i_bound])
      have data_support:
        "Some (((data, attacker_state), result), final_state) \<in>
          set_dist
            (execute (checked_staged_security_experiment_with_data_state A)
              adversary_initial_state)"
        using mapped_support unfolding projection .
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from checked_staged_security_experiment_with_data_state_outcomeE
          [OF data_support]
      have verifier:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        by blast
      have transcript_split:
        "hash_map_output_values ?s \<inter> set (staged_proof_transcript data)
            \<noteq> {} \<or>
         hash_map_new_output_hit (set (staged_proof_transcript data))
            ?s final_state"
        by (rule verify_monad_trace_root_target_preexisting_or_new[OF verifier])
          simp
      show ?thesis
        unfolding out_eq
          checked_staged_security_with_query_prefix_transcript_hit_def
        using transcript_split by simp
    qed
  qed
  have transcript_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      checked_staged_security_with_query_prefix_transcript_hit
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_query_prefix_transcript_hit_bound_from_data_state
        [OF i_bound pre_bound new_bound])
  show ?thesis
    by (rule order_trans[OF event_le transcript_bound])
qed

lemma checked_staged_security_with_data_state_current_empty_query_opening_hit_at_bound_from_conceptual_empty_residual_and_transcript:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and residual_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
          i)
        adversary_initial_state \<le> E"
    and pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_empty_query_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + E + (P + R)"
proof -
  have path_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at
        i)
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at_bound_from_transcript
        [OF i_bound pre_bound new_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_current_empty_query_opening_hit_at_bound_from_conceptual_empty_residual_and_path
        [OF wf controlled i_bound residual_bound path_bound])
qed

lemma checked_staged_security_with_data_state_empty_header_bad_event_bound_from_prefix_drift_trace_fri_and_current_empty_query:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error"
proof -
  have query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> empty_query_error"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_empty_query_bad_le_current_empty_opening_hit_at_zero[
          OF wf controlled] current_empty_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_prefix_drift_trace_fri_and_query
        [OF false_statement wf controlled prefix_bound drift_bound
          trace_fri_bound query_bound])
qed

end

end
