(*  Title:      Stark/Staged_Security_Experiment_Alpha_Header_Binding.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Alpha_Header_Binding
  imports
    Staged_Security_Experiment_Composition_Query_Residual
    Soundness_Alpha_Header_Cross_Candidate
begin

text \<open>
  Staged wrapper for the alpha-header candidate-binding diagnostic.

  This does not bound the event.  It isolates the remaining proof obligation:
  a partial-header alpha hit that is not already a prefix-fixed alpha hit must
  use a header-supported partial trace candidate that is not bound by the
  prefix Merkle evidence.
\<close>

context soundness
begin

definition checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
      bad_sets out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, final_state) \<Rightarrow>
        (let packed = fst (fst x);
             prefix = fst (fst packed);
             prefix_state = snd (fst packed);
             data = snd packed;
             attacker_state = snd (fst x);
             result = snd x;
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>as query_idxs fr f_fri_roots f_final dg composition_fri_roots
              final rest.
              accepted_transcript_shape s (Some (result, final_state))
                as query_idxs \<and>
              verifier_header_transcript s fr f_fri_roots f_final as dg
                composition_fri_roots final rest \<and>
              as \<in>
                alpha_header_supported_partial_union_bad_sets s bad_sets fr
                  f_fri_roots f_final \<and>
              as \<notin> alpha_prefix_union_bad_sets prefix_state bad_sets fr \<and>
              alpha_header_partial_candidate_not_prefix_bound prefix_state s
                fr f_fri_roots f_final))"

lemma checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_boundI:
  assumes s_eq:
      "s =
        verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
    and shape:
      "accepted_transcript_shape s (Some (result, final_state))
        as query_idxs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and hit:
      "as \<in>
        alpha_header_supported_partial_union_bad_sets s bad_sets fr
          f_fri_roots f_final"
    and not_prefix:
      "as \<notin> alpha_prefix_union_bad_sets prefix_state bad_sets fr"
    and not_bound:
      "alpha_header_partial_candidate_not_prefix_bound prefix_state s fr
        f_fri_roots f_final"
  shows
    "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
      bad_sets
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have shape':
    "accepted_transcript_shape ?s (Some (result, final_state))
      as query_idxs"
    using shape by (simp add: s_eq)
  have header':
    "verifier_header_transcript ?s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    using header by (simp add: s_eq)
  have hit':
    "as \<in>
      alpha_header_supported_partial_union_bad_sets ?s bad_sets fr
        f_fri_roots f_final"
    using hit by (simp add: s_eq)
  have not_bound':
    "alpha_header_partial_candidate_not_prefix_bound prefix_state ?s fr
      f_fri_roots f_final"
    using not_bound by (simp add: s_eq)
  show ?thesis
  unfolding
    checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound_def
    Let_def
  apply simp
  apply (rule exI[where x=as])
  apply (intro conjI)
   apply (rule exI[where x=query_idxs])
   apply (rule shape')
  apply (rule exI[where x=fr])
  apply (rule exI[where x=f_fri_roots])
  apply (rule exI[where x=f_final])
  apply (intro conjI)
     apply (rule exI[where x=dg])
     apply (rule exI[where x=composition_fri_roots])
     apply (rule exI[where x=final])
     apply (rule exI[where x=rest])
     apply (rule header')
    apply (rule hit')
   apply (rule not_prefix)
  apply (rule not_bound')
  done
qed

lemma checked_staged_security_with_actual_alpha_prefix_support_prefix_extends_verifier_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
  shows
    "prefix_state \<le>
      verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
proof -
  from support obtain trans_out where trans_out:
      "Some (((prefix, prefix_state), data), attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_with_alpha_prefix_program A)
            adversary_initial_state)"
    unfolding
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  from checked_staged_transcript_with_alpha_prefix_program_support
      [OF wf controlled trans_out]
  have prefix_ext: "prefix_state \<le> attacker_state"
    by blast
  show ?thesis
    by (rule
        alpha_prefix_hash_extends_verifier_state_from_adversary_right
        [OF prefix_ext])
qed

lemma checked_staged_security_with_actual_alpha_prefix_support_prefix_extends_verifier_final:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and verifier_out:
      "Some (result', witness_final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
  shows "prefix_state \<le> witness_final_state"
proof -
  have prefix_s:
    "prefix_state \<le>
      verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_prefix_extends_verifier_state
        [OF wf controlled support])
  have s_final:
    "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data) \<le>
      witness_final_state"
    by (rule verify_monad_hash_extends[OF verifier_out])
  show ?thesis
    by (rule hash_ext_trans[OF prefix_s s_final])
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_obtain_witness_final_ext:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and bound:
      "alpha_header_partial_candidate_not_prefix_bound prefix_state
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        fr f_fri_roots f_final"
  obtains trace_table witness_final_state trace_openings where
    "alpha_header_supported_partial_trace_table_candidate_witness
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      fr f_fri_roots f_final trace_table witness_final_state
      trace_openings"
    "trace_table \<notin> alpha_prefix_trace_table_candidates prefix_state fr"
    "prefix_state \<le> witness_final_state"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from alpha_header_partial_candidate_not_prefix_bound_obtain_witness
      [OF bound]
  obtain trace_table witness_final_state trace_openings where witness:
      "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
        f_fri_roots f_final trace_table witness_final_state
        trace_openings"
    and not_prefix:
      "trace_table \<notin> alpha_prefix_trace_table_candidates prefix_state fr"
    by blast
  from witness obtain witness_result query_idxs as dg composition_fri_roots
      final rest where verifier_out:
      "Some (witness_result, witness_final_state) \<in>
        set_dist (execute verify_monad ?s)"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  have prefix_final: "prefix_state \<le> witness_final_state"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_prefix_extends_verifier_final
        [OF wf controlled support verifier_out])
  show ?thesis
    by (rule that[OF witness not_prefix prefix_final])
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_decompose:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and bound:
      "alpha_header_partial_candidate_not_prefix_bound prefix_state
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        fr f_fri_roots f_final"
  shows
    "hash_map_output_collision prefix_state \<or>
     (\<exists>trace_table witness_final_state trace_openings.
        alpha_header_supported_partial_trace_table_candidate_witness
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          fr f_fri_roots f_final trace_table witness_final_state
          trace_openings \<and>
        trace_table \<notin>
          alpha_prefix_trace_table_candidates prefix_state fr \<and>
        prefix_state \<le> witness_final_state \<and>
        ((\<exists>j < scale * clength.
            \<forall>i opn. i < rounds \<longrightarrow>
              opn \<in> set (trace_openings ! i) \<longrightarrow>
              opening_index opn \<noteq> j) \<or>
         alpha_prefix_trace_table_candidates prefix_state fr = {} \<or>
         (\<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
            hash_map_new_output_hit
              (merkle_path_target_roots witness_final_state fr
                (scale * clength) (opening_index opn)
                (opening_value opn) (opening_path opn))
              prefix_state witness_final_state)))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_obtain_witness_final_ext
      [OF wf controlled support bound]
  obtain trace_table witness_final_state trace_openings where witness:
      "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
        f_fri_roots f_final trace_table witness_final_state
        trace_openings"
    and not_prefix:
      "trace_table \<notin>
        alpha_prefix_trace_table_candidates prefix_state fr"
    and prefix_final: "prefix_state \<le> witness_final_state"
    by blast
  show ?thesis
  proof (cases "hash_map_output_collision prefix_state")
    case True
    then show ?thesis by simp
  next
    case clean_prefix: False
    show ?thesis
    proof (cases
        "\<forall>j < scale * clength.
          \<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
            opening_index opn = j")
      case False
      then have uncovered:
        "\<exists>j < scale * clength.
          \<forall>i opn. i < rounds \<longrightarrow>
            opn \<in> set (trace_openings ! i) \<longrightarrow>
            opening_index opn \<noteq> j"
        by blast
      show ?thesis
        using witness not_prefix prefix_final uncovered by blast
    next
      case True
      have pullback_or_new:
        "(\<forall>i < rounds.
            partial_authenticated_table fr (scale * clength)
              (trace_openings ! i) prefix_state) \<or>
         (\<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
            hash_map_new_output_hit
              (merkle_path_target_roots witness_final_state fr
                (scale * clength) (opening_index opn)
                (opening_value opn) (opening_path opn))
              prefix_state witness_final_state)"
        by (rule alpha_header_witness_openings_pullback_or_new_output_hit
            [OF prefix_final witness])
      from pullback_or_new show ?thesis
      proof
        assume pullback_all:
          "\<forall>i < rounds.
            partial_authenticated_table fr (scale * clength)
              (trace_openings ! i) prefix_state"
        have no_prefix_candidate:
          "alpha_prefix_trace_table_candidates prefix_state fr = {}"
        proof (rule
            alpha_header_not_prefix_witness_imp_no_prefix_candidate_or_pullback_gap
            [OF not_prefix witness clean_prefix])
          fix i
          assume "i < rounds"
          then show
            "partial_authenticated_table fr (scale * clength)
              (trace_openings ! i) prefix_state"
            using pullback_all by blast
        next
          fix j
          assume "j < scale * clength"
          then show
            "\<exists>i<rounds. \<exists>opn\<in>set (trace_openings ! i).
              opening_index opn = j"
            using True by blast
        qed
        show ?thesis
          using witness not_prefix prefix_final no_prefix_candidate by blast
      next
        assume
          "\<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
            hash_map_new_output_hit
              (merkle_path_target_roots witness_final_state fr
                (scale * clength) (opening_index opn)
                (opening_value opn) (opening_path opn))
              prefix_state witness_final_state"
        then show ?thesis
          using witness not_prefix prefix_final by blast
      qed
    qed
  qed
qed

definition checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_not_prefix_collision out
    \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             prefix_state = snd (fst packed)
         in hash_map_output_collision prefix_state))"

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_collision_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (staged_alpha_search_queries budgets 0)"
proof -
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
      adversary_initial_state \<le>
     wp_event
      (checked_staged_transcript_with_alpha_prefix_program A)
      checked_staged_transcript_actual_alpha_prefix_collision_hit
      adversary_initial_state"
    unfolding
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
  proof (rule wp_event_bind_bound_by_head_event)
    show
      "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
        checked_staged_transcript_actual_alpha_prefix_collision_hit
        adversary_initial_state \<le>
       wp_event (checked_staged_transcript_with_alpha_prefix_program A)
        checked_staged_transcript_actual_alpha_prefix_collision_hit
        adversary_initial_state"
      by simp
  next
    show
      "checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
        None \<Longrightarrow>
       checked_staged_transcript_actual_alpha_prefix_collision_hit None"
      unfolding
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision_def
        checked_staged_transcript_actual_alpha_prefix_collision_hit_def
      by simp
  next
    fix packed attacker_state out
    assume cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>s. put
                (verifier_state_from_adversary s
                  (staged_proof_transcript (snd packed))) \<bind>
                (\<lambda>_. verify_monad \<bind>
                  (\<lambda>result. return ((packed, s), result)))))
            attacker_state)"
      and hit:
      "checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
        out"
    obtain prefix prefix_state data where packed_eq:
      "packed = ((prefix, prefix_state), data)"
      by (cases packed, auto split: prod.splits)
    have "hash_map_output_collision prefix_state"
      using cont hit
      unfolding
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision_def
        packed_eq
      by (auto elim!: set_dist_bindE split: option.splits prod.splits)
    then show
      "checked_staged_transcript_actual_alpha_prefix_collision_hit
        (Some (packed, attacker_state))"
      unfolding checked_staged_transcript_actual_alpha_prefix_collision_hit_def
        packed_eq
      by simp
  qed
  have transcript_bound:
    "wp_event
      (checked_staged_transcript_with_alpha_prefix_program A)
      checked_staged_transcript_actual_alpha_prefix_collision_hit
      adversary_initial_state \<le>
     wp_event (staged_alpha_prefix_program A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state"
    by (rule checked_staged_transcript_with_alpha_prefix_collision_bound)
  have collision_budget:
    "hash_collision_budget (staged_alpha_search_queries budgets 0)
      (staged_alpha_prefix_program A)"
    by (rule hash_collision_budget_staged_alpha_prefix_program
        [OF wf controlled])
  have collision_bound:
    "wp_event (staged_alpha_prefix_program A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (staged_alpha_search_queries budgets 0)"
  proof -
    have
      "wp_event (staged_alpha_prefix_program A)
        (hash_new_collision_event adversary_initial_state)
        adversary_initial_state \<le>
        hash_collision_budget_value
          (card (hash_map_output_values adversary_initial_state))
          (staged_alpha_search_queries budgets 0)"
      using collision_budget adversary_initial_state_no_output_collision
      unfolding hash_collision_budget_def by blast
    also have "... =
        hash_collision_budget_value 0 (staged_alpha_search_queries budgets 0)"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
    by (rule order_trans[OF projection])
      (rule order_trans[OF transcript_bound collision_bound])
qed

definition checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             prefix_state = snd (fst packed);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>fr f_fri_roots f_final trace_table witness_final_state
              trace_openings.
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table witness_final_state
                trace_openings \<and>
              trace_table \<notin>
                alpha_prefix_trace_table_candidates prefix_state fr \<and>
              prefix_state \<le> witness_final_state \<and>
              (\<exists>j < scale * clength.
                \<forall>i opn. i < rounds \<longrightarrow>
                  opn \<in> set (trace_openings ! i) \<longrightarrow>
                  opening_index opn \<noteq> j)))"

definition checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             prefix_state = snd (fst packed);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>fr f_fri_roots f_final trace_table witness_final_state
              trace_openings.
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table witness_final_state
                trace_openings \<and>
              trace_table \<notin>
                alpha_prefix_trace_table_candidates prefix_state fr \<and>
              prefix_state \<le> witness_final_state \<and>
              alpha_prefix_trace_table_candidates prefix_state fr = {}))"

definition checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             prefix_state = snd (fst packed);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>fr f_fri_roots f_final trace_table witness_final_state
              trace_openings.
              alpha_header_supported_partial_trace_table_candidate_witness
                s fr f_fri_roots f_final trace_table witness_final_state
                trace_openings \<and>
              trace_table \<notin>
                alpha_prefix_trace_table_candidates prefix_state fr \<and>
              prefix_state \<le> witness_final_state \<and>
              (\<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
                hash_map_new_output_hit
                  (merkle_path_target_roots witness_final_state fr
                    (scale * clength) (opening_index opn)
                    (opening_value opn) (opening_path opn))
                  prefix_state witness_final_state)))"

definition checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
              s))"

definition checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>witness_result witness_state.
              Some (witness_result, witness_state) \<in>
                set_dist (execute verify_monad s) \<and>
              (hash_map_output_values s \<inter>
                set (staged_proof_transcript data) \<noteq> {} \<or>
               hash_map_new_output_hit (set (staged_proof_transcript data))
                s witness_state)))"

definition checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in hash_map_output_values s \<inter>
              set (staged_proof_transcript data) \<noteq> {}))"

definition checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, _) \<Rightarrow>
        (let packed = fst (fst x);
             data = snd packed;
             attacker_state = snd (fst x);
             s =
              verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)
         in \<exists>witness_result witness_state.
              Some (witness_result, witness_state) \<in>
                set_dist (execute verify_monad s) \<and>
              hash_map_new_output_hit (set (staged_proof_transcript data))
                s witness_state))"

lemma checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_imp_pre_or_new:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      out \<or>
     checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
      out"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_def
    checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_def
    checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit_def
  by (auto split: option.splits prod.splits)

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_imp_witness_transcript_hit:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using assms
    unfolding
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_def
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from assms obtain fr f_fri_roots f_final trace_table witness_final_state
      trace_openings where witness:
      "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
        f_fri_roots f_final trace_table witness_final_state trace_openings"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_def
      Let_def
    by (auto split: option.splits prod.splits)
  from witness obtain witness_result query_idxs as dg composition_fri_roots
      final rest where outcome:
      "Some (witness_result, witness_final_state) \<in>
        set_dist (execute verify_monad ?s)"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  have tr_eq: "PTranscript ?s = staged_proof_transcript data"
    by simp
  have transcript_hit:
    "hash_map_output_values ?s \<inter> set (staged_proof_transcript data)
        \<noteq> {} \<or>
     hash_map_new_output_hit (set (staged_proof_transcript data))
        ?s witness_final_state"
    by (rule verify_monad_trace_root_target_preexisting_or_new
        [OF outcome tr_eq])
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_def
      Let_def
    using outcome transcript_hit
    by (auto split: option.splits prod.splits)
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_le_witness_transcript_hit:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
    adversary_initial_state"
  by (rule wp_event_mono)
    (rule
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_imp_witness_transcript_hit)

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_imp_witness_transcript_hit:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using assms
    unfolding
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_def
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from assms obtain fr f_fri_roots f_final trace_table witness_final_state
      trace_openings where witness:
      "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
        f_fri_roots f_final trace_table witness_final_state trace_openings"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_def
      Let_def
    by (auto split: option.splits prod.splits)
  from witness obtain witness_result query_idxs as dg composition_fri_roots
      final rest where outcome:
      "Some (witness_result, witness_final_state) \<in>
        set_dist (execute verify_monad ?s)"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  have tr_eq: "PTranscript ?s = staged_proof_transcript data"
    by simp
  have transcript_hit:
    "hash_map_output_values ?s \<inter> set (staged_proof_transcript data)
        \<noteq> {} \<or>
     hash_map_new_output_hit (set (staged_proof_transcript data))
        ?s witness_final_state"
    by (rule verify_monad_trace_root_target_preexisting_or_new
        [OF outcome tr_eq])
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_def
      Let_def
    using outcome transcript_hit
    by (auto split: option.splits prod.splits)
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_le_witness_transcript_hit:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
    adversary_initial_state"
  by (rule wp_event_mono)
    (rule
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_imp_witness_transcript_hit)

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_imp_witnessed_cross_or_merkle_bad:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
      out"
proof (cases out)
  case None
  then show ?thesis
    using assms
    unfolding
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from assms obtain fr f_fri_roots f_final trace_table witness_final_state
      trace_openings j where witness:
      "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
        f_fri_roots f_final trace_table witness_final_state trace_openings"
    and j_bound: "j < scale * clength"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow>
        opn \<in> set (trace_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_def
      Let_def
    by (auto split: option.splits prod.splits)
  from witness obtain result' query_idxs as dg composition_fri_roots final rest
    where outcome:
      "Some (result', witness_final_state) \<in> set_dist (execute verify_monad ?s)"
    and partial:
      "accepted_with_partial_trace_openings ?s
        (Some (result', witness_final_state)) fr query_idxs trace_openings"
    and candidate: "partial_trace_table_candidate trace_table trace_openings"
    and header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  have not_singleton:
    "\<not> (\<exists>trace_table0.
      alpha_header_supported_partial_trace_table_candidates ?s fr f_fri_roots
        f_final \<subseteq> {trace_table0})"
    by (rule
        alpha_header_supported_partial_trace_table_candidates_not_singleton_if_trace_unopened
        [OF outcome partial candidate header j_bound unopened])
  have not_singleton_witnessed:
    "\<not> (\<exists>trace_table0.
      alpha_header_supported_witnessed_partial_trace_table_candidates ?s fr
        f_fri_roots f_final \<subseteq> {trace_table0})"
    using not_singleton
    by (simp add: alpha_header_supported_witnessed_candidates_eq_candidates)
  have
    "alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
      ?s fr f_fri_roots f_final"
    by (rule
        alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad_if_not_singleton
        [OF not_singleton_witnessed])
  then have
    "alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad ?s"
    unfolding alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad_def
    by blast
  then show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad_def
      Let_def
    by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_witnessed_cross_or_merkle_bad:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
    adversary_initial_state"
  by (rule wp_event_mono)
    (rule
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_imp_witnessed_cross_or_merkle_bad)

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_imp_decomposition_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        bad_sets out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_not_prefix_collision out \<or>
     checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
        out \<or>
     checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        out \<or>
     checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
        out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have hit_body:
    "\<exists>as query_idxs fr f_fri_roots f_final dg composition_fri_roots
        final rest.
        accepted_transcript_shape ?s (Some (result, final_state))
          as query_idxs \<and>
        verifier_header_transcript ?s fr f_fri_roots f_final as dg
          composition_fri_roots final rest \<and>
        as \<in>
          alpha_header_supported_partial_union_bad_sets ?s bad_sets fr
            f_fri_roots f_final \<and>
        as \<notin> alpha_prefix_union_bad_sets prefix_state bad_sets fr \<and>
        alpha_header_partial_candidate_not_prefix_bound prefix_state ?s fr
          f_fri_roots f_final"
    using hit
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound_def
      Let_def
    by simp
  from hit_body obtain as query_idxs fr f_fri_roots f_final dg
      composition_fri_roots final rest where bound:
      "alpha_header_partial_candidate_not_prefix_bound prefix_state ?s fr
        f_fri_roots f_final"
    by blast
  have support_some:
    "Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
    using support out_eq by simp
  from
    checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_decompose
      [OF wf controlled support_some bound]
  show ?thesis
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have
      "checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
        out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision_def
        Let_def
      using collision by simp
    then show ?thesis by simp
  next
    assume witness_cases:
      "\<exists>trace_table witness_final_state trace_openings.
        alpha_header_supported_partial_trace_table_candidate_witness ?s fr
          f_fri_roots f_final trace_table witness_final_state
          trace_openings \<and>
        trace_table \<notin>
          alpha_prefix_trace_table_candidates prefix_state fr \<and>
        prefix_state \<le> witness_final_state \<and>
        ((\<exists>j<scale * clength.
            \<forall>i opn.
              i < rounds \<longrightarrow>
              opn \<in> set (trace_openings ! i) \<longrightarrow>
              opening_index opn \<noteq> j) \<or>
         alpha_prefix_trace_table_candidates prefix_state fr = {} \<or>
         (\<exists>i<rounds. \<exists>opn\<in>set (trace_openings ! i).
            hash_map_new_output_hit
              (merkle_path_target_roots witness_final_state fr
                (scale * clength) (opening_index opn)
                (opening_value opn) (opening_path opn))
              prefix_state witness_final_state))"
    from witness_cases obtain trace_table witness_final_state trace_openings
      where witness:
        "alpha_header_supported_partial_trace_table_candidate_witness ?s fr
          f_fri_roots f_final trace_table witness_final_state
          trace_openings"
      and not_prefix:
        "trace_table \<notin>
          alpha_prefix_trace_table_candidates prefix_state fr"
      and ext: "prefix_state \<le> witness_final_state"
      and cases:
        "(\<exists>j<scale * clength.
            \<forall>i opn.
              i < rounds \<longrightarrow>
              opn \<in> set (trace_openings ! i) \<longrightarrow>
              opening_index opn \<noteq> j) \<or>
         alpha_prefix_trace_table_candidates prefix_state fr = {} \<or>
         (\<exists>i<rounds. \<exists>opn\<in>set (trace_openings ! i).
            hash_map_new_output_hit
              (merkle_path_target_roots witness_final_state fr
                (scale * clength) (opening_index opn)
                (opening_value opn) (opening_path opn))
              prefix_state witness_final_state)"
      by blast
    from cases show ?thesis
    proof
      assume uncovered:
        "\<exists>j<scale * clength.
          \<forall>i opn.
            i < rounds \<longrightarrow>
            opn \<in> set (trace_openings ! i) \<longrightarrow>
            opening_index opn \<noteq> j"
      have body:
        "\<exists>fr' f_fri_roots' f_final' trace_table'
            witness_final_state' trace_openings'.
          alpha_header_supported_partial_trace_table_candidate_witness ?s
            fr' f_fri_roots' f_final' trace_table'
            witness_final_state' trace_openings' \<and>
          trace_table' \<notin>
            alpha_prefix_trace_table_candidates prefix_state fr' \<and>
          prefix_state \<le> witness_final_state' \<and>
          (\<exists>j < scale * clength.
            \<forall>i opn. i < rounds \<longrightarrow>
              opn \<in> set (trace_openings' ! i) \<longrightarrow>
              opening_index opn \<noteq> j)"
        using witness not_prefix ext uncovered by blast
      have
        "checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
          out"
        unfolding out_eq
          checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_def
          Let_def
        using body by (simp split: prod.splits)
      then show ?thesis by simp
    next
      assume rest:
        "alpha_prefix_trace_table_candidates prefix_state fr = {} \<or>
         (\<exists>i<rounds. \<exists>opn\<in>set (trace_openings ! i).
            hash_map_new_output_hit
              (merkle_path_target_roots witness_final_state fr
                (scale * clength) (opening_index opn)
                (opening_value opn) (opening_path opn))
              prefix_state witness_final_state)"
      then show ?thesis
      proof
        assume no_prefix:
          "alpha_prefix_trace_table_candidates prefix_state fr = {}"
        have body:
          "\<exists>fr' f_fri_roots' f_final' trace_table'
              witness_final_state' trace_openings'.
            alpha_header_supported_partial_trace_table_candidate_witness ?s
              fr' f_fri_roots' f_final' trace_table'
              witness_final_state' trace_openings' \<and>
            trace_table' \<notin>
              alpha_prefix_trace_table_candidates prefix_state fr' \<and>
            prefix_state \<le> witness_final_state' \<and>
            alpha_prefix_trace_table_candidates prefix_state fr' = {}"
          using witness not_prefix ext no_prefix by blast
        have
          "checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
            out"
          unfolding out_eq
            checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_def
            Let_def
          using body by (simp split: prod.splits)
        then show ?thesis by simp
      next
        assume path:
          "\<exists>i<rounds. \<exists>opn\<in>set (trace_openings ! i).
            hash_map_new_output_hit
              (merkle_path_target_roots witness_final_state fr
                (scale * clength) (opening_index opn)
                (opening_value opn) (opening_path opn))
              prefix_state witness_final_state"
        have body:
          "\<exists>fr' f_fri_roots' f_final' trace_table'
              witness_final_state' trace_openings'.
            alpha_header_supported_partial_trace_table_candidate_witness ?s
              fr' f_fri_roots' f_final' trace_table'
              witness_final_state' trace_openings' \<and>
            trace_table' \<notin>
              alpha_prefix_trace_table_candidates prefix_state fr' \<and>
            prefix_state \<le> witness_final_state' \<and>
            (\<exists>i < rounds. \<exists>opn \<in> set (trace_openings' ! i).
              hash_map_new_output_hit
                (merkle_path_target_roots witness_final_state' fr'
                  (scale * clength) (opening_index opn)
                  (opening_value opn) (opening_path opn))
                prefix_state witness_final_state')"
          using witness not_prefix ext path by blast
        have
          "checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
            out"
          unfolding out_eq
            checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_def
            Let_def
          using body by (simp split: prod.splits)
        then show ?thesis by simp
      qed
    qed
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound:
  fixes C U N P :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and collision_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
        adversary_initial_state \<le> C"
    and uncovered_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
        adversary_initial_state \<le> U"
    and no_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        adversary_initial_state \<le> N"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
        adversary_initial_state \<le> P"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        bad_sets)
      adversary_initial_state \<le> C + U + N + P"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?B =
    "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
      bad_sets"
  let ?C = checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
  let ?U =
    checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
  let ?N =
    checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
  let ?P = checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
  have "wp_event ?M ?B adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?C out \<or> ?U out \<or> ?N out \<or> ?P out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_imp_decomposition_on_support
        [OF wf controlled])
  also have "... \<le>
      wp_event ?M ?C adversary_initial_state +
      wp_event ?M ?U adversary_initial_state +
      wp_event ?M ?N adversary_initial_state +
      wp_event ?M ?P adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le> C + U + N + P"
    by (intro add_mono collision_bound uncovered_bound no_prefix_bound
        path_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_imp_not_prefix_bound_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and drift:
      "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
        bad_sets out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
      bad_sets out"
proof (cases out)
  case None
  then show ?thesis
    using drift
    unfolding
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_def
      checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit_def
      checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_def
    by simp
next
  case (Some packed_out)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state), result),
          final_state)"
    by (cases packed_out, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have partial_hit:
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      bad_sets out"
    using drift
    unfolding
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_def
      checked_staged_security_with_actual_alpha_prefix_partial_header_fresh_hit_def
    by simp
  have not_prefix_event:
    "\<not> checked_staged_security_with_actual_alpha_prefix_bad_set_hit
      bad_sets out"
    using drift
    unfolding
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_def
    by simp
  have builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  proof -
    have data_support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
          [OF support[unfolded out_eq]])
    from checked_staged_security_experiment_with_data_state_outcomeE
        [OF data_support]
    show ?thesis
      by blast
  qed
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
  have prefix_root_eq: "staged_trace_root data = fst prefix"
    using support out_eq
    unfolding checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
      checked_staged_transcript_with_alpha_prefix_program_def
      checked_staged_after_alpha_prefix_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have alpha_header_hit:
    "alpha_header_list_set_hit ?s
      (alpha_header_supported_partial_union_bad_sets ?s bad_sets)
      (Some (result, final_state))"
    using partial_hit unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_def
    by (simp add: Let_def)
  from alpha_header_hit obtain as query_idxs fr f_fri_roots f_final dg
      composition_fri_roots final rest where shape:
      "accepted_transcript_shape ?s (Some (result, final_state)) as query_idxs"
    and header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and hit:
    "as \<in>
      alpha_header_supported_partial_union_bad_sets ?s bad_sets fr
        f_fri_roots f_final"
    unfolding alpha_header_list_set_hit_def by blast
  have as_eq: "as = staged_alphas data"
    using verifier_header_transcript_unique[OF staged_header header]
    by simp
  have fr_eq: "fr = staged_trace_root data"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  have not_prefix:
    "as \<notin> alpha_prefix_union_bad_sets prefix_state bad_sets fr"
  proof
    assume as_prefix:
      "as \<in> alpha_prefix_union_bad_sets prefix_state bad_sets fr"
    have
      "staged_alphas data \<in>
        alpha_prefix_union_bad_sets prefix_state bad_sets (fst prefix)"
      using as_prefix as_eq fr_eq prefix_root_eq by simp
    then show False
      using not_prefix_event unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_def
      by simp
  qed
  have not_bound:
    "alpha_header_partial_candidate_not_prefix_bound prefix_state ?s fr
      f_fri_roots f_final"
    by (rule alpha_header_partial_union_hit_not_prefix_hit_imp_not_prefix_bound
        [OF hit not_prefix])
  show ?thesis
    unfolding out_eq
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_boundI
        [OF refl shape header hit not_prefix not_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_le_not_prefix_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
        bad_sets)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        bad_sets)
      adversary_initial_state"
  by (rule wp_event_mono_on_support)
    (rule
      checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_imp_not_prefix_bound_on_support
      [OF wf controlled])

lemma checked_staged_security_with_data_state_composition_bad_bound_from_candidate_not_prefix_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> D"
  proof -
    have "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le>
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift_le_not_prefix_bound
          [OF wf controlled])
    also have "... \<le> D"
      by (rule not_prefix_bound)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_partial_header_candidate_drift_and_budgets
        [OF wf controlled drift_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_not_prefix_components_and_budgets:
  fixes C U N P :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and collision_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
        adversary_initial_state \<le> C"
    and uncovered_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
        adversary_initial_state \<le> U"
    and no_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        adversary_initial_state \<le> N"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
        adversary_initial_state \<le> P"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (C + U + N + P) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have not_prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> C + U + N + P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_bound_union_bound
        [OF wf controlled collision_bound uncovered_bound no_prefix_bound
          path_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_candidate_not_prefix_and_budgets
        [OF wf controlled not_prefix_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_not_prefix_noncollision_components_and_budgets:
  fixes U N P :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and uncovered_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
        adversary_initial_state \<le> U"
    and no_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        adversary_initial_state \<le> N"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
        adversary_initial_state \<le> P"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + U + N + P) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof (rule
    checked_staged_security_with_data_state_composition_bad_bound_from_not_prefix_components_and_budgets
    [OF wf controlled _ uncovered_bound no_prefix_bound path_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_collision
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_not_prefix_collision_bound
        [OF wf controlled])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_cross_no_prefix_path_components_and_budgets:
  fixes X N P :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and no_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        adversary_initial_state \<le> N"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
        adversary_initial_state \<le> P"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + N + P) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof (rule
    checked_staged_security_with_data_state_composition_bad_bound_from_not_prefix_noncollision_components_and_budgets
    [OF wf controlled _ no_prefix_bound path_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index
      adversary_initial_state \<le> X"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_uncovered_index_le_witnessed_cross_or_merkle_bad
          cross_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_cross_no_prefix_transcript_components_and_budgets:
  fixes X N T :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and no_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        adversary_initial_state \<le> N"
    and transcript_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
        adversary_initial_state \<le> T"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + N + T) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof (rule
    checked_staged_security_with_data_state_composition_bad_bound_from_cross_no_prefix_path_components_and_budgets
    [OF wf controlled cross_bound no_prefix_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le> T"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_le_witness_transcript_hit
          transcript_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new:
  assumes pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      adversary_initial_state \<le> P + Q"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (\<lambda>out.
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
          out \<or>
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
          out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_imp_pre_or_new)
  have union_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (\<lambda>out.
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
          out \<or>
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
          out)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
      adversary_initial_state"
    by (rule wp_event_union_bound)
  have sum_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
      adversary_initial_state \<le> P + Q"
    by (intro add_mono pre_bound new_bound)
  show ?thesis
    by (rule order_trans[OF event_le])
      (rule order_trans[OF union_bound sum_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_imp_data_state_pre_hit:
  assumes
    "checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
  shows
    "staged_security_with_data_state_transcript_pre_hit
      (Some (((data, attacker_state), result), final_state))"
  using assms
  unfolding
    checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_def
    staged_security_with_data_state_transcript_pre_hit_def
  by simp

lemma checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_bound_from_data_state_pre_hit:
  assumes pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      adversary_initial_state \<le> P"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have projection:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_pre_hit
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. case out of
        None \<Rightarrow> staged_security_with_data_state_transcript_pre_hit None
      | Some (packed, t) \<Rightarrow>
          staged_security_with_data_state_transcript_pre_hit
            (Some (?project packed, t)))
      adversary_initial_state"
  proof -
    have
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
          \<bind> (\<lambda>x. return (?project x)))
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state"
      using
        checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
        [of A]
      by simp
    also have "... =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        (\<lambda>out. case out of
          None \<Rightarrow> staged_security_with_data_state_transcript_pre_hit None
        | Some (packed, t) \<Rightarrow>
            staged_security_with_data_state_transcript_pre_hit
              (Some (?project packed, t)))
        adversary_initial_state"
      by (rule wp_event_bind_return_map)
    finally show ?thesis .
  qed
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. case out of
        None \<Rightarrow> staged_security_with_data_state_transcript_pre_hit None
      | Some (packed, t) \<Rightarrow>
          staged_security_with_data_state_transcript_pre_hit
            (Some (?project packed, t)))
      adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume hit:
      "checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
        out"
    show
      "(case out of
        None \<Rightarrow> staged_security_with_data_state_transcript_pre_hit None
      | Some (packed, t) \<Rightarrow>
          staged_security_with_data_state_transcript_pre_hit
            (Some (?project packed, t)))"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state data attacker_state result final_state
        where out_eq:
          "out =
            Some (((((prefix, prefix_state), data), attacker_state), result),
              final_state)"
        by (cases packed) (auto split: prod.splits)
      show ?thesis
        using
          checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_imp_data_state_pre_hit
            [OF hit[unfolded out_eq]]
        unfolding out_eq by simp
    qed
  qed
  show ?thesis
    by (rule order_trans[OF event_le])
      (use pre_bound projection in simp)
qed

definition checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<Rightarrow>
        staged_security_with_data_state_transcript_pre_hit
          (Some (((data, attacker_state), result), final_state)) \<or>
        staged_security_with_data_state_transcript_new_hit
          (Some (((data, attacker_state), result), final_state)))"

lemma checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit_bound_from_data_state:
  assumes pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
      adversary_initial_state \<le> P + R"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  let ?E =
    "\<lambda>out.
      staged_security_with_data_state_transcript_pre_hit out \<or>
      staged_security_with_data_state_transcript_new_hit out"
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow> ?E None
    | Some (packed, t) \<Rightarrow> ?E (Some (?project packed, t))"
  have projected_eq:
    "?projected =
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit"
    unfolding
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit_def
      staged_security_with_data_state_transcript_pre_hit_def
      staged_security_with_data_state_transcript_new_hit_def
    by (rule ext) (auto split: option.splits prod.splits)
  have projection:
    "wp_event (checked_staged_security_experiment_with_data_state A) ?E
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
      adversary_initial_state"
  proof -
    have
      "wp_event (checked_staged_security_experiment_with_data_state A) ?E
        adversary_initial_state =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
          \<bind> (\<lambda>x. return (?project x)))
        ?E adversary_initial_state"
      using
        checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
        [of A]
      by simp
    also have "... =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        ?projected adversary_initial_state"
      by (rule wp_event_bind_return_map)
    finally show ?thesis
      unfolding projected_eq .
  qed
  have union_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A) ?E
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_pre_hit
      adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state"
    by (rule wp_event_union_bound)
  have
    "wp_event (checked_staged_security_experiment_with_data_state A) ?E
      adversary_initial_state \<le> P + R"
    by (rule order_trans[OF union_bound])
      (intro add_mono pre_bound new_bound)
  then show ?thesis
    unfolding projection .
qed

lemma checked_staged_security_with_actual_alpha_prefix_some_support_imp_sampled_transcript_hit:
  assumes support:
      "Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
  shows
    "checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
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
    unfolding
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit_def
      staged_security_with_data_state_transcript_pre_hit_def
      staged_security_with_data_state_transcript_new_hit_def
    using transcript_split by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_bound_from_sampled_transcript:
  assumes pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le> P + R"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
              adversary_initial_state)"
      and hit:
        "checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
          out"
    show
      "checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
        out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state data attacker_state result final_state
        where out_eq:
          "out =
            Some (((((prefix, prefix_state), data), attacker_state), result),
              final_state)"
        by (cases packed) (auto split: prod.splits)
      show ?thesis
        unfolding out_eq
        by (rule
            checked_staged_security_with_actual_alpha_prefix_some_support_imp_sampled_transcript_hit)
          (rule support[unfolded out_eq])
    qed
  qed
  have transcript_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit_bound_from_data_state
        [OF pre_bound new_bound])
  show ?thesis
    by (rule order_trans[OF event_le transcript_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_bound_from_sampled_transcript:
  assumes pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_new_hit
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le> P + R"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
              adversary_initial_state)"
      and hit:
        "checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output
          out"
    show
      "checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
        out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_actual_alpha_prefix_not_prefix_path_output_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state data attacker_state result final_state
        where out_eq:
          "out =
            Some (((((prefix, prefix_state), data), attacker_state), result),
              final_state)"
        by (cases packed) (auto split: prod.splits)
      show ?thesis
        unfolding out_eq
        by (rule
            checked_staged_security_with_actual_alpha_prefix_some_support_imp_sampled_transcript_hit)
          (rule support[unfolded out_eq])
    qed
  qed
  have transcript_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit
      adversary_initial_state \<le> P + R"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_sampled_transcript_hit_bound_from_data_state
        [OF pre_bound new_bound])
  show ?thesis
    by (rule order_trans[OF event_le transcript_bound])
qed

lemma checked_staged_security_with_data_state_transcript_new_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
proof -
  let ?Builder = "checked_staged_transcript_program A"
  let ?Tail =
    "\<lambda>data s.
      wp_event verify_monad
        (hash_new_output_hit_event (set (staged_proof_transcript data))
          (verifier_state_from_adversary s (staged_proof_transcript data)))
        (verifier_state_from_adversary s (staged_proof_transcript data))"
  have new_none[simp]: "\<not> staged_security_with_data_state_transcript_new_hit None"
    unfolding staged_security_with_data_state_transcript_new_hit_def by simp
  have return_eq:
    "wp (return ((data, s), result))
      (\<lambda>out.
        if staged_security_with_data_state_transcript_new_hit out then 1
        else 0)
      final_state =
     (if hash_map_new_output_hit (set (staged_proof_transcript data))
        (verifier_state_from_adversary s (staged_proof_transcript data))
        final_state then 1 else 0)"
    for data s result final_state
    unfolding staged_security_with_data_state_transcript_new_hit_def
    by (simp add: wpsimps)
  have verify_post_eq:
    "(\<lambda>r. case r of
        None \<Rightarrow> 0
      | Some (result, final_state) \<Rightarrow>
          wp (return ((data, s), result))
            (\<lambda>out.
              if staged_security_with_data_state_transcript_new_hit out
              then 1 else 0)
            final_state) =
     (\<lambda>r.
        if hash_new_output_hit_event (set (staged_proof_transcript data))
          (verifier_state_from_adversary s (staged_proof_transcript data)) r
        then 1 else 0)"
    for data s
  proof (rule ext)
    fix r
    show "(case r of
        None \<Rightarrow> 0
      | Some (result, final_state) \<Rightarrow>
          wp (return ((data, s), result))
            (\<lambda>out.
              if staged_security_with_data_state_transcript_new_hit out
              then 1 else 0)
            final_state) =
     (if hash_new_output_hit_event (set (staged_proof_transcript data))
        (verifier_state_from_adversary s (staged_proof_transcript data)) r
      then 1 else 0)"
    proof (cases r)
      case None
      then show ?thesis
        unfolding hash_new_output_hit_event_def by simp
    next
      case (Some packed)
      then obtain result final_state where
        packed_eq: "packed = (result, final_state)"
        by (cases packed) simp
      show ?thesis
        using return_eq[of data s result final_state]
        unfolding Some packed_eq hash_new_output_hit_event_def
        by simp
    qed
  qed
  have tail_eq:
    "wp
      (get \<bind> (\<lambda>s.
        put (verifier_state_from_adversary s
          (staged_proof_transcript data)) \<bind>
        (\<lambda>_. verify_monad \<bind>
          (\<lambda>result. return ((data, s), result)))))
      (\<lambda>out.
        if staged_security_with_data_state_transcript_new_hit out then 1
        else 0)
      s =
     ?Tail data s"
    for data s
    unfolding wp_event_def
    by (simp add: wpsimps verify_post_eq)
  have post_eq:
    "(\<lambda>out. case out of
        None \<Rightarrow> 0
      | Some (x, y) \<Rightarrow>
          wp
            (get \<bind> (\<lambda>s.
              put (verifier_state_from_adversary s
                (staged_proof_transcript x)) \<bind>
              (\<lambda>_. verify_monad \<bind>
                (\<lambda>result. return ((x, s), result)))))
            (\<lambda>out.
              if staged_security_with_data_state_transcript_new_hit out
              then 1 else 0)
            y) =
     (\<lambda>out. case out of
        None \<Rightarrow> 0
      | Some (data, s) \<Rightarrow> ?Tail data s)"
    by (rule ext) (simp add: tail_eq split: option.splits prod.splits)
  have post_tail_unfold:
    "(\<lambda>out. case out of
        None \<Rightarrow> 0
      | Some (data, s) \<Rightarrow> ?Tail data s) =
     (\<lambda>out. case out of
        None \<Rightarrow> 0
      | Some (data, s) \<Rightarrow>
          wp verify_monad
            (\<lambda>x. if hash_new_output_hit_event
              (set (staged_proof_transcript data))
              (verifier_state_from_adversary s
                (staged_proof_transcript data))
              x then 1 else 0)
            (verifier_state_from_adversary s
              (staged_proof_transcript data)))"
    by (rule ext) (simp add: wp_event_def split: option.splits prod.splits)
  have event_eq:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state =
     wp ?Builder
      (\<lambda>out. case out of
        None \<Rightarrow> 0
      | Some (data, s) \<Rightarrow> ?Tail data s)
      adversary_initial_state"
    unfolding checked_staged_security_experiment_with_data_state_def
      wp_event_def
    by (simp add: wpsimps post_eq post_tail_unfold
        split: prod.splits option.splits)
  have tail_bound:
    "\<And>out. out \<in> set_dist (execute ?Builder adversary_initial_state) \<Longrightarrow>
      (case out of None \<Rightarrow> 0 | Some (data, s) \<Rightarrow> ?Tail data s)
      \<le> staged_concrete_transcript_target_error_bound"
  proof -
    fix out
    assume support:
      "out \<in> set_dist (execute ?Builder adversary_initial_state)"
    show "(case out of None \<Rightarrow> 0 | Some (data, s) \<Rightarrow> ?Tail data s)
      \<le> staged_concrete_transcript_target_error_bound"
    proof (cases out)
      case None
      then show ?thesis
        unfolding staged_concrete_transcript_target_error_bound_def by simp
    next
      case (Some packed)
      then obtain data s where packed_eq: "packed = (data, s)"
        by (cases packed) simp
      have outcome:
        "Some (data, s) \<in>
          set_dist (execute ?Builder adversary_initial_state)"
        using support Some packed_eq by simp
      have verifier_bound:
        "?Tail data s \<le>
          concrete_transcript_target_error (staged_proof_transcript data)"
        using wp_verify_monad_hash_new_output_hit_bound
          [of "set (staged_proof_transcript data)"
            "verifier_state_from_adversary s
              (staged_proof_transcript data)"]
        unfolding concrete_transcript_target_error_def
          hash_target_budget_value_def
        by (simp add: mult.commute)
      have target_bound:
        "concrete_transcript_target_error (staged_proof_transcript data)
          \<le> staged_concrete_transcript_target_error_bound"
      proof -
        have len:
          "length (staged_proof_transcript data) \<le>
            staged_proof_transcript_length_bound"
          by (rule
              checked_staged_transcript_program_staged_proof_transcript_length_bound
              [OF wf controlled outcome])
        show ?thesis
          unfolding staged_concrete_transcript_target_error_bound_def
          by (rule concrete_transcript_target_error_bound_from_length[OF len])
      qed
      show ?thesis
        using Some packed_eq order_trans[OF verifier_bound target_bound]
        by simp
    qed
  qed
  show ?thesis
    unfolding event_eq
    by (rule wp_le_const_on_support[OF tail_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_cross_no_prefix_transcript_split_components_and_budgets:
  fixes X N P Q :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and no_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        adversary_initial_state \<le> N"
    and pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
        adversary_initial_state \<le> P"
    and new_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_new_hit
        adversary_initial_state \<le> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + N + (P + Q)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof (rule
    checked_staged_security_with_data_state_composition_bad_bound_from_cross_no_prefix_transcript_components_and_budgets
    [OF wf controlled cross_bound no_prefix_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      adversary_initial_state \<le> P + Q"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new
        [OF pre_bound new_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_cross_no_prefix_data_pre_and_witness_new_components_and_budgets:
  fixes X N P Q :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and no_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
        adversary_initial_state \<le> N"
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
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + N + (P + Q)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof (rule
    checked_staged_security_with_data_state_composition_bad_bound_from_cross_no_prefix_transcript_split_components_and_budgets
    [OF wf controlled cross_bound no_prefix_bound _ new_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
      adversary_initial_state \<le> P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_bound_from_data_state_pre_hit
        [OF data_pre_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_cross_and_transcript_components_and_budgets:
  fixes X T :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
    and transcript_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
        adversary_initial_state \<le> T"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + T + T) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof (rule
    checked_staged_security_with_data_state_composition_bad_bound_from_cross_no_prefix_transcript_components_and_budgets
    [OF wf controlled cross_bound _ transcript_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate
      adversary_initial_state \<le> T"
    by (rule order_trans
        [OF
          checked_staged_security_with_actual_alpha_prefix_not_prefix_no_prefix_candidate_le_witness_transcript_hit
          transcript_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_cross_data_pre_and_witness_new_components_and_budgets:
  fixes X P Q :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cross_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witnessed_cross_or_merkle_bad
        adversary_initial_state \<le> X"
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
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) + X + (P + Q) + (P + Q)) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof (rule
    checked_staged_security_with_data_state_composition_bad_bound_from_cross_and_transcript_components_and_budgets
    [OF wf controlled cross_bound])
  show
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit
      adversary_initial_state \<le> P + Q"
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_witness_transcript_hit_bound_from_pre_and_new
      [OF _ new_bound])
    show
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit
        adversary_initial_state \<le> P"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_witness_transcript_pre_hit_bound_from_data_state_pre_hit
          [OF data_pre_bound])
  qed
qed

end

end
