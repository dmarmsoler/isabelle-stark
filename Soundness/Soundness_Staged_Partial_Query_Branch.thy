(*  Title:      Stark/Soundness_Staged_Partial_Query_Branch.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Partial_Query_Branch
  imports Soundness_Staged_Partial_Query
begin

text \<open>
  Branch-specific probability bridges for the partial-opening query layer.
  This keeps branch/tree-output integration material out of the size-sensitive
  base partial-query theory.
\<close>

context soundness
begin

definition checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (x, t) \<Rightarrow>
        staged_security_with_data_state_query_partial_opening_hit
          (Some (((snd (fst (fst x)), snd (fst x)), snd x), t)))"

lemma checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hitE:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
  obtains i raw trace_openings composition_openings where
    "i < rounds"
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some raw"
    "index (to_nat raw) \<in> query_sample_space"
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
    "partial_query_openings_consistent trace_openings composition_openings
      (staged_alphas data) (index (to_nat raw))"
proof -
  have data_hit:
    "staged_security_with_data_state_query_partial_opening_hit
      (Some (((data, attacker_state), result), final_state))"
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit_def
    by simp
  then obtain i where i_bound: "i < rounds"
    and hit_at:
      "staged_security_with_data_state_query_partial_opening_hit_at i
        (Some (((data, attacker_state), result), final_state))"
    unfolding staged_security_with_data_state_query_partial_opening_hit_def
    by blast
  from staged_security_with_data_state_query_partial_opening_hit_atE
      [OF hit_at]
  obtain raw where lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
        Some raw"
    and raw_hit:
      "index (to_nat raw) \<in>
        query_header_supported_partial_opening_success_indices_at
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)
          i"
    by blast
  from query_header_supported_partial_opening_success_indices_atE
      [OF raw_hit]
  obtain trace_openings composition_openings where idx_sample:
      "index (to_nat raw) \<in> query_sample_space"
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
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
    by blast
  show ?thesis
    by (rule that[OF i_bound lookup idx_sample witness consistent])
qed

lemma checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit_projection:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
    adversary_initial_state =
   wp_event (checked_staged_security_experiment_with_data_state A)
    staged_security_with_data_state_query_partial_opening_hit
    adversary_initial_state"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
        \<bind> (\<lambda>x. return (?project x)))
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state"
    using
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
      [of A]
    by simp
  also have "... =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. case out of
        None \<Rightarrow> staged_security_with_data_state_query_partial_opening_hit None
      | Some (x, t) \<Rightarrow>
          staged_security_with_data_state_query_partial_opening_hit
            (Some (?project x, t)))
      adversary_initial_state"
    by (rule wp_event_bind_return_map)
  also have "... =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      adversary_initial_state"
    unfolding
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit_def
      staged_security_with_data_state_query_partial_opening_hit_def
      staged_security_with_data_state_query_partial_opening_hit_at_def
    by (rule arg_cong[where
        f="\<lambda>Q. wp_event
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
          Q adversary_initial_state"])
      (rule ext, simp split: option.splits prod.splits)
  finally show ?thesis
    by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit_bound_from_fixed_query_error_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
    "\<And>data attacker_state i.
      i < rounds \<Longrightarrow>
      query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<subseteq> B"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
proof -
  have data_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
    by (rule
        checked_staged_security_with_data_state_partial_opening_hit_bound_from_fixed_query_error_cover
        [OF wf controlled cover raw_bound subset frac])
  show ?thesis
    unfolding
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit_projection
    by (rule data_bound)
qed

lemma checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support_branch:
  assumes support:
    "Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
  shows
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have projected:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A \<bind> (\<lambda>x. return (?project x)))
          adversary_initial_state)"
    apply (rule set_dist_bindI[OF support])
    apply simp
    done
  show ?thesis
    using projected
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
      [of A]
    by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_bound_tables_all_queries_imp_query_partial_opening_hit_on_support:
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
      "accepted_with_bound_tables
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) trace_table composition_table as
        query_idxs"
    and header:
      "verifier_header_transcript
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data) (staged_trace_fri_roots data)
        (staged_trace_final data) as dg composition_fri_roots final rest"
    and all_queries:
      "all_queries_consistent trace_table composition_table as"
  shows
    "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      (Some (((((prefix, prefix_state), data), attacker_state), result),
        final_state))"
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
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support_branch
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder where builder:
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
  have header_eq:
    "as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     composition_fri_roots = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF staged_header header]
    by simp
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as query_idxs"
    using bound
    unfolding accepted_with_bound_tables_def accepted_with_tables_def
    by simp
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled data_support shape]
  obtain raw_idxs where
    as_eq: "as = staged_alphas data"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    by blast
  have bound_staged:
    "accepted_with_bound_tables ?s (Some (result, final_state))
      trace_table composition_table (staged_alphas data) query_idxs"
    using bound as_eq by simp
  have all_queries_staged:
    "all_queries_consistent trace_table composition_table
      (staged_alphas data)"
    using all_queries as_eq by simp
  have i_bound: "0 < rounds"
    by (rule rounds_positive)
  have idx_sample:
    "query_idxs ! 0 \<in> query_sample_space"
  proof -
    have len_query_idxs: "length query_idxs = rounds"
      by (rule accepted_with_bound_tables_shapes(4)[OF bound_staged])
    have "query_idxs ! 0 \<in> set query_idxs"
      by (rule nth_mem) (use i_bound len_query_idxs in simp)
    then show ?thesis
      by (rule accepted_with_bound_tables_query_sample_space
          [OF bound_staged])
  qed
  show ?thesis
  proof (rule accepted_with_bound_tables_partial_opening_witnesses_Some
      [OF bound_staged])
    fix fr f_fri_roots f_final dg' composition_fri_roots' final'
        rest' trace_openings composition_openings
    assume header':
      "verifier_header_transcript ?s fr f_fri_roots f_final
        (staged_alphas data) dg' composition_fri_roots' final' rest'"
      and comp_nonempty: "composition_fri_roots' \<noteq> []"
      and trace_partial:
      "accepted_with_partial_trace_openings ?s
        (Some (result, final_state)) fr query_idxs trace_openings"
      and comp_partial:
      "accepted_with_partial_composition_openings ?s
        (Some (result, final_state)) (hd composition_fri_roots')
        query_idxs composition_openings"
      and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
      and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    have header_eq':
      "fr = staged_trace_root data \<and>
       f_fri_roots = staged_trace_fri_roots data \<and>
       f_final = staged_trace_final data \<and>
       dg' = staged_degree data \<and>
       composition_fri_roots' = staged_composition_fri_roots data \<and>
       final' = staged_composition_final data \<and>
       rest' = List.concat (staged_query_chunks data)"
      using verifier_header_transcript_unique[OF staged_header header']
      by simp
    have idx_in:
      "query_idxs ! 0 \<in>
        query_header_supported_partial_opening_success_indices_at ?s fr
          f_fri_roots f_final (staged_alphas data) dg'
          composition_fri_roots' final' 0"
      by (rule
          query_header_supported_partial_opening_success_indices_atI_from_partials_consistent
          [OF verifier trace_partial comp_partial trace_candidate
            comp_candidate header' comp_nonempty refl i_bound idx_sample
            all_queries_staged])
    have idx_in_staged:
      "query_idxs ! 0 \<in>
        query_header_supported_partial_opening_success_indices_at ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)
          0"
      using idx_in header_eq' by simp
    have raw_idx:
      "index (to_nat (raw_idxs ! 0)) = query_idxs ! 0"
      using query_idxs_eq len_raw i_bound by simp
    have hit_at:
      "staged_security_with_data_state_query_partial_opening_hit_at 0
        (Some (((data, attacker_state), result), final_state))"
      unfolding staged_security_with_data_state_query_partial_opening_hit_at_def
      using i_bound lookup[OF i_bound] idx_in_staged raw_idx
      by (simp add: Let_def)
    have hit:
      "staged_security_with_data_state_query_partial_opening_hit
        (Some (((data, attacker_state), result), final_state))"
      by (rule staged_security_with_data_state_query_partial_opening_hitI
          [OF i_bound hit_at])
    show ?thesis
      unfolding
        checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit_def
      using hit by simp
  qed
qed

definition checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), data), attacker_state),
        result), final_state) \<Rightarrow>
        (let s =
          verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)
         in \<exists>as dg composition_fri_roots final rest trace_table
              composition_table query_idxs trace_openings composition_openings.
          accepted_with_bound_tables s (Some (result, final_state))
            trace_table composition_table as query_idxs \<and>
          verifier_header_transcript s
            (staged_trace_root data) (staged_trace_fri_roots data)
            (staged_trace_final data) as dg composition_fri_roots final rest \<and>
          (trace_openings, composition_openings) \<in>
            query_header_supported_partial_opening_witnesses s
              (staged_trace_root data) (staged_trace_fri_roots data)
              (staged_trace_final data) as dg composition_fri_roots final \<and>
          all_queries_consistent trace_table composition_table as))"

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit_imp_query_hit_on_support:
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
      "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state result final_state where
    out_eq:
      "out = Some (((((prefix, prefix_state), data), attacker_state),
        result), final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have support_some:
    "Some (((((prefix, prefix_state), data), attacker_state),
        result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
    using support unfolding out_eq .
  from hit obtain as dg composition_fri_roots final rest trace_table
      composition_table query_idxs trace_openings composition_openings where
    bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root data) (staged_trace_fri_roots data)
        (staged_trace_final data) as dg composition_fri_roots final rest"
    and all_queries:
      "all_queries_consistent trace_table composition_table as"
    unfolding out_eq
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit_def
      Let_def
    by auto
  show ?thesis
    unfolding out_eq
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bound_tables_all_queries_imp_query_partial_opening_hit_on_support
        [OF wf controlled support_some bound header all_queries])
qed

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit_bound_from_query_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
      adversary_initial_state \<le> Q"
proof -
  have
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit_imp_query_hit_on_support
        [OF wf controlled])
  then show ?thesis
    by (rule order_trans[OF _ query_bound])
qed

definition checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit
      out \<longleftrightarrow>
    checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      out \<and>
    checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      out"

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit_imp_query_hit:
  assumes
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit
      out"
  shows "checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
    out"
  using assms
  unfolding
    checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit_def
  by simp

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit_bound_from_query_hit:
  assumes query_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit
      adversary_initial_state \<le> Q"
  by (rule order.trans[OF _ query_bound])
    (rule wp_event_mono,
      rule
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit_imp_query_hit)

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit_bound_from_fixed_query_error_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
    "\<And>data attacker_state i.
      i < rounds \<Longrightarrow>
      query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<subseteq> B"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
proof -
  have query_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit_bound_from_fixed_query_error_cover
        [OF wf controlled cover raw_bound subset frac])
  show ?thesis
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit_bound_from_query_hit
        [OF query_bound])
qed

definition checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_query_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_query_hit
      out \<longleftrightarrow>
    checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      out \<and>
    \<not> checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
      out"

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit_imp_query_or_without_query:
  assumes
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      out"
  shows
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit
      out \<or>
     checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_query_hit
      out"
  using assms
  unfolding
    checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit_def
    checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_query_hit_def
  by blast

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit_bound_from_query_and_without_query:
  assumes query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit
        adversary_initial_state \<le> Q"
    and without_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_query_hit
        adversary_initial_state \<le> W"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      adversary_initial_state \<le> Q + W"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Witness =
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit"
  let ?Query =
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit"
  let ?Without =
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_query_hit"
  have "wp_event ?M ?Witness adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?Query out \<or> ?Without out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit_imp_query_or_without_query)
  also have "... \<le>
      wp_event ?M ?Query adversary_initial_state +
      wp_event ?M ?Without adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> Q + W"
    by (intro add_mono query_bound without_bound)
  finally show ?thesis .
qed

lemma checked_actual_alpha_prefix_branch_subtree_verifier_output_hit_bound_from_partial_opening_witness_hit:
  assumes witness_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      adversary_initial_state \<le> W"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
      adversary_initial_state \<le> W"
proof -
  have
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
      adversary_initial_state \<le>
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_imp_partial_opening_witness_hit_on_support)
  also have "... \<le> W"
    by (rule witness_bound)
  finally show ?thesis .
qed

definition checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit
      out \<longleftrightarrow>
    checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      out \<and>
    \<not> checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
      out"

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit_imp_all_queries_or_without_all_queries:
  assumes
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      out"
  shows
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
      out \<or>
     checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit
      out"
  using assms
  unfolding
    checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit_def
  by blast

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit_bound_from_all_queries_and_without_all_queries:
  assumes all_queries_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
        adversary_initial_state \<le> Q"
    and without_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit
        adversary_initial_state \<le> W"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      adversary_initial_state \<le> Q + W"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Witness =
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit"
  let ?All =
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit"
  let ?Without =
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit"
  have "wp_event ?M ?Witness adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?All out \<or> ?Without out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit_imp_all_queries_or_without_all_queries)
  also have "... \<le>
      wp_event ?M ?All adversary_initial_state +
      wp_event ?M ?Without adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> Q + W"
    by (intro add_mono all_queries_bound without_bound)
  finally show ?thesis .
qed

lemma checked_actual_alpha_prefix_branch_subtree_verifier_output_hit_bound_from_all_queries_and_without_all_queries:
  assumes all_queries_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
        adversary_initial_state \<le> Q"
    and without_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit
        adversary_initial_state \<le> W"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
      adversary_initial_state \<le> Q + W"
proof -
  have witness_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      adversary_initial_state \<le> Q + W"
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit_bound_from_all_queries_and_without_all_queries
        [OF all_queries_bound without_bound])
  show ?thesis
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_output_hit_bound_from_partial_opening_witness_hit
        [OF witness_bound])
qed

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit_imp_fri_or_query_bad_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      trace_fri_bad_with_partial_openings out \<or>
     checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_fri_bad_with_partial_openings out \<or>
     checked_staged_security_with_actual_alpha_prefix_verifier_event
      query_bad out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit_def
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state result final_state where
    out_eq:
      "out = Some (((((prefix, prefix_state), data), attacker_state),
        result), final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have support_some:
    "Some (((((prefix, prefix_state), data), attacker_state),
        result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
    using support unfolding out_eq .
  have witness_hit:
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      out"
    using hit
    unfolding
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit_def
    by simp
  have not_all_hit:
    "\<not>
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
        out"
    using hit
    unfolding
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit_def
    by simp
  from witness_hit obtain as dg composition_fri_roots final rest trace_table
      composition_table query_idxs trace_openings composition_openings where
    bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root data) (staged_trace_fri_roots data)
        (staged_trace_final data) as dg composition_fri_roots final rest"
    and witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses ?s
          (staged_trace_root data) (staged_trace_fri_roots data)
          (staged_trace_final data) as dg composition_fri_roots final"
    unfolding out_eq
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit_def
      Let_def
    by auto
  have not_all_queries:
    "\<not> all_queries_consistent trace_table composition_table as"
  proof
    assume all_queries:
      "all_queries_consistent trace_table composition_table as"
    have
      "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
        out"
      unfolding out_eq
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit_def
        Let_def
      apply simp
      apply (rule exI[where x=as])
      apply (rule exI[where x=dg])
      apply (rule exI[where x=composition_fri_roots])
      apply (rule exI[where x=final])
      apply (rule exI[where x=rest])
      apply (rule exI[where x=trace_table])
      apply (rule exI[where x=composition_table])
      apply (intro conjI)
         apply (rule exI[where x=query_idxs])
         apply (rule bound)
        apply (rule header)
       apply (rule exI[where x=trace_openings])
       apply (rule exI[where x=composition_openings])
       apply (rule witness)
      apply (rule all_queries)
      done
    then show False
      using not_all_hit by contradiction
  qed
  show ?thesis
  proof (cases "trace_table_low_degree trace_table")
    case False
    obtain fr f_fri_roots f_final dg' composition_fri_roots' final'
        rest' trace_openings' composition_openings' where
      trace_partial:
      "accepted_with_partial_trace_openings ?s
        (Some (result, final_state)) fr query_idxs trace_openings'"
      by (rule accepted_with_bound_tables_partial_opening_witnesses_Some
          [OF bound]) blast
    have trace_bad:
      "trace_fri_bad_with_partial_openings ?s
        (Some (result, final_state))"
      unfolding trace_fri_bad_with_partial_openings_def trace_fri_bad_def
      using bound False trace_partial by blast
    then show ?thesis
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        Let_def
      by simp
  next
    case trace_low: True
    show ?thesis
    proof (cases
        "composition_table_low_degree maxDegree composition_table")
      case False
      obtain fr f_fri_roots f_final dg' composition_fri_roots' final'
          rest' trace_openings' composition_openings' where
        trace_partial:
        "accepted_with_partial_trace_openings ?s
          (Some (result, final_state)) fr query_idxs trace_openings'"
        by (rule accepted_with_bound_tables_partial_opening_witnesses_Some
            [OF bound]) blast
      have comp_bad:
        "composition_fri_bad_with_partial_openings ?s
          (Some (result, final_state))"
        unfolding composition_fri_bad_with_partial_openings_def
          composition_fri_bad_def
        using bound trace_low False trace_partial by blast
      then show ?thesis
        unfolding out_eq
          checked_staged_security_with_actual_alpha_prefix_verifier_event_def
          Let_def
        by simp
    next
      case composition_low: True
      have query_bad:
        "query_bad ?s (Some (result, final_state))"
        unfolding query_bad_def
        using bound trace_low composition_low not_all_queries by blast
      then show ?thesis
        unfolding out_eq
          checked_staged_security_with_actual_alpha_prefix_verifier_event_def
          Let_def
        by simp
    qed
  qed
qed

lemma checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit_bound_from_partial_fri_and_query:
  assumes trace_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          trace_fri_bad_with_partial_openings)
        adversary_initial_state \<le> T"
    and composition_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_fri_bad_with_partial_openings)
        adversary_initial_state \<le> C"
    and query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          query_bad)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit
      adversary_initial_state \<le> T + C + Q"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Without =
    "checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit"
  let ?Trace =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      trace_fri_bad_with_partial_openings"
  let ?Composition =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_fri_bad_with_partial_openings"
  let ?Query =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event query_bad"
  have "wp_event ?M ?Without adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?Trace out \<or> (?Composition out \<or> ?Query out))
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit_imp_fri_or_query_bad_on_support)
  also have "... \<le>
      wp_event ?M ?Trace adversary_initial_state +
      wp_event ?M (\<lambda>out. ?Composition out \<or> ?Query out)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      wp_event ?M ?Trace adversary_initial_state +
      (wp_event ?M ?Composition adversary_initial_state +
       wp_event ?M ?Query adversary_initial_state)"
    by (intro add_mono order_refl wp_event_union_bound)
  also have "... \<le> T + (C + Q)"
    by (intro add_mono trace_bound composition_bound query_bound)
  also have "... = T + C + Q"
    by (simp add: add.assoc)
  finally show ?thesis .
qed

lemma checked_actual_alpha_prefix_branch_subtree_verifier_output_hit_bound_from_query_hit_partial_fri_and_query:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and query_hit_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
        adversary_initial_state \<le> QH"
    and trace_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          trace_fri_bad_with_partial_openings)
        adversary_initial_state \<le> T"
    and composition_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_fri_bad_with_partial_openings)
        adversary_initial_state \<le> C"
    and query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          query_bad)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
      adversary_initial_state \<le> QH + (T + C + Q)"
proof -
  have all_queries_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit
      adversary_initial_state \<le> QH"
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_all_queries_hit_bound_from_query_hit
        [OF wf controlled query_hit_bound])
  have without_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit
      adversary_initial_state \<le> T + C + Q"
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_all_queries_hit_bound_from_partial_fri_and_query
        [OF trace_bound composition_bound query_bound])
  show ?thesis
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_output_hit_bound_from_all_queries_and_without_all_queries
        [OF all_queries_bound without_bound])
qed

lemma checked_actual_alpha_prefix_branch_subtree_verifier_output_hit_bound_from_partial_opening_witness_query_and_without_query:
  assumes query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit
        adversary_initial_state \<le> Q"
    and without_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_query_hit
        adversary_initial_state \<le> W"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
      adversary_initial_state \<le> Q + W"
proof -
  have witness_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
      adversary_initial_state \<le> Q + W"
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit_bound_from_query_and_without_query
        [OF query_bound without_bound])
  show ?thesis
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_output_hit_bound_from_partial_opening_witness_hit
        [OF witness_bound])
qed

lemma checked_actual_alpha_prefix_branch_subtree_verifier_output_hit_bound_from_partial_opening_fixed_query_cover_and_without_query:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
    "\<And>data attacker_state i.
      i < rounds \<Longrightarrow>
      query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<subseteq> B"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
    and without_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_without_query_hit
        adversary_initial_state \<le> W"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound + W"
proof -
  have query_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_query_hit_bound_from_fixed_query_error_cover
        [OF wf controlled cover raw_bound subset frac])
  show ?thesis
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_output_hit_bound_from_partial_opening_witness_query_and_without_query
        [OF query_bound without_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_branch_split_witness_and_transcript_budget:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and root_pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
        adversary_initial_state \<le> RP"
    and subtree_pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit
        adversary_initial_state \<le> SP"
    and subtree_verifier_witness_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_actual_alpha_prefix_branch_subtree_verifier_partial_opening_witness_hit
        adversary_initial_state \<le> WV"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (RP + staged_concrete_transcript_target_error_bound + SP + WV)"
proof -
  have subtree_verifier_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
      adversary_initial_state \<le> WV"
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_output_hit_bound_from_partial_opening_witness_hit
        [OF subtree_verifier_witness_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_branch_split_side_events_and_transcript_budget
        [OF wf controlled root_pre_bound subtree_pre_bound
          subtree_verifier_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_branch_split_query_hit_partial_fri_and_query_no_root_pre:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subtree_pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit
        adversary_initial_state \<le> SP"
    and query_hit_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_query_partial_opening_hit
        adversary_initial_state \<le> QH"
    and trace_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          trace_fri_bad_with_partial_openings)
        adversary_initial_state \<le> T"
    and composition_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          composition_fri_bad_with_partial_openings)
        adversary_initial_state \<le> C"
    and query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_verifier_event
          query_bad)
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
      (staged_phase_relation_error size
        (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
       staged_concrete_transcript_target_error_bound + SP +
       (QH + (T + C + Q)))"
proof -
  have subtree_verifier_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
      adversary_initial_state \<le> QH + (T + C + Q)"
    by (rule
        checked_actual_alpha_prefix_branch_subtree_verifier_output_hit_bound_from_query_hit_partial_fri_and_query
        [OF wf controlled query_hit_bound trace_bound composition_bound
          query_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_branch_split_side_events_and_transcript_budget_no_root_pre
        [OF wf controlled subtree_pre_bound subtree_verifier_bound])
qed

end

end
